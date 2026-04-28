open Base
open System4_lsp
module Lsp = Linol_lsp.Lsp

let test_project_dir = Stdlib.Filename.concat (Stdlib.Sys.getcwd ()) "testdata"
let testdir_path = List.fold ~init:test_project_dir ~f:Stdlib.Filename.concat

let initialize_project ?(pje = "default.pje") () =
  let proj = Project.create ~read_file:Stdio.In_channel.read_all in
  let pjePath = testdir_path [ pje ] in
  let options = { Types.InitializationOptions.default with pjePath } in
  Project.initialize proj options;
  Project.initial_scan proj;
  proj

let string_of_kind (k : Lsp.Types.CompletionItemKind.t) =
  match k with
  | Variable -> "Variable"
  | Constant -> "Constant"
  | Function -> "Function"
  | Method -> "Method"
  | Field -> "Field"
  | Class -> "Class"
  | Interface -> "Interface"
  | Module -> "Module"
  | Keyword -> "Keyword"
  | _ -> "Other"

let print_completion_items (cl : Lsp.Types.CompletionList.t) =
  let items =
    List.sort cl.items ~compare:(fun (a : Lsp.Types.CompletionItem.t) b ->
        String.compare a.label b.label)
  in
  List.iter items ~f:(fun (it : Lsp.Types.CompletionItem.t) ->
      let kind = Option.value_map it.kind ~default:"?" ~f:string_of_kind in
      Stdio.printf "  %s [%s]" it.label kind;
      Option.iter it.detail ~f:(fun d -> Stdio.printf " %s" d);
      Stdio.print_endline "")

let completion_at proj path text pos =
  List.iter (Project.update_document proj ~path text) ~f:(fun _ -> ());
  match Project.get_completion proj ~path pos with
  | Some (`CompletionList cl) -> print_completion_items cl
  | Some (`List items) ->
      print_completion_items
        (Lsp.Types.CompletionList.create ~isIncomplete:false ~items ())
  | None -> Stdio.print_endline "(none)"

let initialize_completion_project () =
  initialize_project ~pje:"completion.pje" ()

let%expect_test "get_completion_globals" =
  let proj = initialize_completion_project () in
  let path = testdir_path [ "src"; "completion.jaf" ] in
  (* Partial identifier in function body; file cannot parse cleanly, but the
     completion must still surface globals from other .jaf files. *)
  let text = "void completion_test(void) {\n\tg\n}\n" in
  let pos = Lsp.Types.Position.create ~line:1 ~character:2 in
  completion_at proj path text pos;
  [%expect
    {|
    GCONST [Constant] int
    MyLib [Module]
    NULL [Keyword]
    SType [Class]
    TestCls [Class]
    completion_test [Function] void completion_test();
    dtype [Interface]
    false [Constant] bool
    ftype [Interface]
    gfunc [Function] void gfunc(int x);
    gstr [Variable] string
    gvar [Variable] int
    system [Keyword]
    true [Constant] bool
    |}]

let%expect_test "get_completion_after_dot_unresolved_returns_none" =
  let proj = initialize_completion_project () in
  let path = testdir_path [ "src"; "completion.jaf" ] in
  (* Broken parse with no usable last_good_toplevel for [s], so the receiver
     cannot be type-resolved and member completion returns nothing. *)
  let text = "void completion_test(void) {\n\tSType s;\n\ts.\n}\n" in
  let pos = Lsp.Types.Position.create ~line:2 ~character:3 in
  completion_at proj path text pos;
  [%expect {| (none) |}]

let%expect_test "get_completion_non_ascii_prefix" =
  let proj = initialize_completion_project () in
  let path = testdir_path [ "src"; "completion.jaf" ] in
  (* Multibyte identifier prefix is detected as member mode, but [変数]
     is undefined so we return no completions. *)
  let text = "void completion_test(void) {\n\t変数.\n}\n" in
  (* "\t変数." -> 1 tab + 3 UTF-16 chars = cursor column 4 *)
  let pos = Lsp.Types.Position.create ~line:1 ~character:4 in
  completion_at proj path text pos;
  [%expect {| (none) |}]

(* Locals/params and enclosing class scope. *)

(* Filter output to highlight scope-specific items, since the global list
   is voluminous and tested separately. *)
let print_scope_items (cl : Lsp.Types.CompletionList.t) ~include_kinds =
  let items =
    List.filter cl.items ~f:(fun (it : Lsp.Types.CompletionItem.t) ->
        match it.kind with
        | Some k -> List.mem include_kinds k ~equal:Poly.equal
        | None -> false)
    |> List.sort ~compare:(fun (a : Lsp.Types.CompletionItem.t) b ->
        String.compare a.label b.label)
  in
  List.iter items ~f:(fun (it : Lsp.Types.CompletionItem.t) ->
      let kind = Option.value_map it.kind ~default:"?" ~f:string_of_kind in
      Stdio.printf "  %s [%s]" it.label kind;
      Option.iter it.detail ~f:(fun d -> Stdio.printf " %s" d);
      Stdio.print_endline "")

let completion_scope_at proj path text pos ~include_kinds =
  List.iter (Project.update_document proj ~path text) ~f:(fun _ -> ());
  match Project.get_completion proj ~path pos with
  | Some (`CompletionList cl) -> print_scope_items cl ~include_kinds
  | Some (`List items) ->
      print_scope_items
        (Lsp.Types.CompletionList.create ~isIncomplete:false ~items ())
        ~include_kinds
  | None -> Stdio.print_endline "(none)"

let%expect_test "get_completion_locals_and_params" =
  let proj = initialize_completion_project () in
  let path = testdir_path [ "src"; "completion.jaf" ] in
  let text = "void test_locals(int a, int b) {\n\tint c;\n\t\n}\n" in
  (* Cursor on the empty line inside the block. *)
  let pos = Lsp.Types.Position.create ~line:2 ~character:1 in
  completion_scope_at proj path text pos
    ~include_kinds:[ Lsp.Types.CompletionItemKind.Variable ];
  [%expect
    {|
    a [Variable] int
    b [Variable] int
    c [Variable] int
    gstr [Variable] string
    gvar [Variable] int
    |}]

let%expect_test "get_completion_locals_limited_by_scope" =
  let proj = initialize_completion_project () in
  let path = testdir_path [ "src"; "completion.jaf" ] in
  (* `d` is declared in an inner block that does not contain the cursor. *)
  let text =
    "void test_scope(void) {\n\tint a;\n\t{\n\t\tint d;\n\t}\n\tint b;\n\t\n}\n"
  in
  let pos = Lsp.Types.Position.create ~line:6 ~character:1 in
  completion_scope_at proj path text pos
    ~include_kinds:[ Lsp.Types.CompletionItemKind.Variable ];
  [%expect
    {|
    a [Variable] int
    b [Variable] int
    gstr [Variable] string
    gvar [Variable] int
    |}]

let%expect_test "get_completion_locals_inside_while_body" =
  let proj = initialize_completion_project () in
  let path = testdir_path [ "src"; "completion.jaf" ] in
  (* Regression: locals declared inside a while/if/do-while/switch body must
     be visible. The scope_collector previously snapshotted at the enclosing
     statement level, missing variables introduced in the nested body. *)
  let text =
    "void test_while_locals(void) {\n\
     \twhile (true) {\n\
     \t\tarray@int array_int;\n\
     \t\t\n\
     \t}\n\
     }\n"
  in
  let pos = Lsp.Types.Position.create ~line:3 ~character:2 in
  completion_scope_at proj path text pos
    ~include_kinds:[ Lsp.Types.CompletionItemKind.Variable ];
  [%expect
    {|
    array_int [Variable] array@int
    gstr [Variable] string
    gvar [Variable] int
    |}]

let%expect_test "get_completion_member_for_local_inside_while_body" =
  let proj = initialize_completion_project () in
  let path = testdir_path [ "src"; "completion.jaf" ] in
  (* Member completion needs the local's type, so the same scope-collection
     bug would also break `array_int.` inside a while body. *)
  let text =
    "void test_while_member(void) {\n\
     \twhile (true) {\n\
     \t\tarray@int array_int;\n\
     \t\tarray_int.PushBack(0);\n\
     \t}\n\
     }\n"
  in
  let pos = Lsp.Types.Position.create ~line:3 ~character:12 in
  completion_at proj path text pos;
  [%expect
    {|
    Alloc [Method] void Alloc(int );
    Copy [Method] int Copy(int , ref array@int , int , int );
    Empty [Method] int Empty();
    Erase [Method] int Erase(int );
    Fill [Method] int Fill(int , int , int );
    Find [Method] int Find(int , int , int , bool(int, int)  = &NULL);
    Free [Method] void Free();
    Insert [Method] void Insert(int , int );
    Numof [Method] int Numof(int  = 1);
    PopBack [Method] void PopBack();
    PushBack [Method] void PushBack(int );
    Realloc [Method] void Realloc(int );
    Reverse [Method] void Reverse();
    Sort [Method] void Sort(int(int, int)  = &NULL);
    |}]

let%expect_test "get_completion_class_members_in_method" =
  let proj = initialize_completion_project () in
  let path = testdir_path [ "src"; "completion.jaf" ] in
  let text = "int TestCls::tc_method() {\n\t\n}\n" in
  let pos = Lsp.Types.Position.create ~line:1 ~character:1 in
  completion_scope_at proj path text pos
    ~include_kinds:
      [
        Lsp.Types.CompletionItemKind.Field; Lsp.Types.CompletionItemKind.Method;
      ];
  (* Inside the class, privates are visible; ctors/dtors never appear. *)
  [%expect
    {|
    tc_member [Field] int
    tc_method [Method] int tc_method();
    tc_priv_field [Field] int
    tc_priv_method [Method] int tc_priv_method();
    |}]

let%expect_test "get_completion_keywords_in_method" =
  let proj = initialize_completion_project () in
  let path = testdir_path [ "src"; "completion.jaf" ] in
  let text = "int TestCls::tc_method() {\n\t\n}\n" in
  let pos = Lsp.Types.Position.create ~line:1 ~character:1 in
  completion_scope_at proj path text pos
    ~include_kinds:[ Lsp.Types.CompletionItemKind.Keyword ];
  [%expect {|
    NULL [Keyword]
    system [Keyword]
    this [Keyword]
    |}]

let%expect_test "get_completion_falls_back_to_last_good" =
  let proj = initialize_completion_project () in
  let path = testdir_path [ "src"; "completion.jaf" ] in
  (* First update with a clean parse so last_good_toplevel is populated.
     The good and broken layouts share the same line count so that the
     cursor position remains valid against last_good_lexbuf. *)
  let good = "void test_fallback(int a, int b) {\n\tint c;\n\tint d;\n}\n" in
  List.iter (Project.update_document proj ~path good) ~f:(fun _ -> ());
  (* Then an edit that breaks the parse (line 2 becomes "\tc"). *)
  let broken = "void test_fallback(int a, int b) {\n\tint c;\n\tc\n}\n" in
  let pos = Lsp.Types.Position.create ~line:2 ~character:2 in
  completion_scope_at proj path broken pos
    ~include_kinds:[ Lsp.Types.CompletionItemKind.Variable ];
  [%expect
    {|
    a [Variable] int
    b [Variable] int
    c [Variable] int
    d [Variable] int
    gstr [Variable] string
    gvar [Variable] int
    |}]

(* Member completion after '.'. *)

let%expect_test "get_completion_struct_field" =
  let proj = initialize_completion_project () in
  let path = testdir_path [ "src"; "completion.jaf" ] in
  (* Clean parse so the receiver [s] is type-resolved as SType. Cursor sits
     between the dot and [x] in `s.x`. *)
  let text = "void completion_test(void) {\n\tSType s;\n\tint i = s.x;\n}\n" in
  let pos = Lsp.Types.Position.create ~line:2 ~character:11 in
  completion_at proj path text pos;
  [%expect {| x [Field] int |}]

let%expect_test "get_completion_this_in_method" =
  let proj = initialize_completion_project () in
  let path = testdir_path [ "src"; "completion.jaf" ] in
  let text =
    "int TestCls::tc_method() {\n\tint x = this.tc_member;\n\treturn x;\n}\n"
  in
  (* Cursor right after the dot in `this.tc_member`. *)
  let pos = Lsp.Types.Position.create ~line:1 ~character:14 in
  completion_at proj path text pos;
  (* `this.` from inside the class shows privates; ctors/dtors are filtered. *)
  [%expect
    {|
    tc_member [Field] int
    tc_method [Method] int tc_method();
    tc_priv_field [Field] int
    tc_priv_method [Method] int tc_priv_method();
    |}]

let%expect_test "get_completion_struct_member_outside_class" =
  let proj = initialize_completion_project () in
  let path = testdir_path [ "src"; "completion.jaf" ] in
  (* From a non-method function, `obj.` must hide private members and the
     constructor/destructor of TestCls. *)
  let text =
    "void completion_test(void) {\n\
     \tTestCls obj;\n\
     \tint x = obj.tc_member;\n\
     }\n"
  in
  let pos = Lsp.Types.Position.create ~line:2 ~character:13 in
  completion_at proj path text pos;
  [%expect
    {|
    tc_member [Field] int
    tc_method [Method] int tc_method();
    |}]

let%expect_test "get_completion_system" =
  let proj = initialize_completion_project () in
  let path = testdir_path [ "src"; "completion.jaf" ] in
  let text = "void completion_test(void) {\n\tsystem.Exit(0);\n}\n" in
  (* Cursor right after `system.`. *)
  let pos = Lsp.Types.Position.create ~line:1 ~character:8 in
  completion_at proj path text pos;
  [%expect
    {|
    CopySaveFile [Function] int CopySaveFile(string , string );
    DeleteSaveFile [Function] int DeleteSaveFile(string );
    Error [Function] string Error(string );
    ExistFile [Function] int ExistFile(string );
    ExistFunc [Function] bool ExistFunc(string );
    ExistSaveFile [Function] int ExistSaveFile(string );
    Exit [Function] void Exit(int );
    GetFuncStackName [Function] string GetFuncStackName(int );
    GetGameName [Function] string GetGameName();
    GetSaveFolderName [Function] string GetSaveFolderName();
    GetTime [Function] int GetTime();
    GlobalLoad [Function] int GlobalLoad(string , string );
    GlobalSave [Function] int GlobalSave(string , string );
    GroupLoad [Function] int GroupLoad(string , string , string , ref int );
    GroupSave [Function] int GroupSave(string , string , string , ref int );
    IsDebugMode [Function] int IsDebugMode();
    LockPeek [Function] int LockPeek();
    MsgBox [Function] string MsgBox(string );
    MsgBoxOkCancel [Function] int MsgBoxOkCancel(string );
    OpenWeb [Function] void OpenWeb(string );
    Output [Function] string Output(string );
    Peek [Function] void Peek();
    Reset [Function] void Reset();
    ResumeLoad [Function] void ResumeLoad(string , string );
    ResumeReadComment [Function] bool ResumeReadComment(string , string , ref array@string );
    ResumeSave [Function] int ResumeSave(string , string , ref int );
    ResumeWriteComment [Function] bool ResumeWriteComment(string , string , ref array@string );
    Sleep [Function] void Sleep(int );
    UnlockPeek [Function] int UnlockPeek();
    |}]

let%expect_test "get_completion_string_builtin" =
  let proj = initialize_completion_project () in
  let path = testdir_path [ "src"; "completion.jaf" ] in
  let text = "void completion_test(void) {\n\tint i = \"abc\".Length();\n}\n" in
  (* Cursor right after the dot in `"abc".Length()`. *)
  let pos = Lsp.Types.Position.create ~line:1 ~character:15 in
  completion_at proj path text pos;
  [%expect
    {|
    Empty [Method] int Empty();
    Erase [Method] void Erase(int );
    Find [Method] int Find(string );
    GetPart [Method] string GetPart(int , int );
    Int [Method] int Int();
    Length [Method] int Length();
    LengthByte [Method] int LengthByte();
    PopBack [Method] void PopBack();
    PushBack [Method] void PushBack(int );
    |}]

let%expect_test "get_completion_array_builtin" =
  let proj = initialize_completion_project () in
  let path = testdir_path [ "src"; "completion.jaf" ] in
  let text =
    "void completion_test(void) {\n\tarray@int arr;\n\tarr.PushBack(0);\n}\n"
  in
  (* Cursor right after `arr.`. *)
  let pos = Lsp.Types.Position.create ~line:2 ~character:5 in
  completion_at proj path text pos;
  [%expect
    {|
    Alloc [Method] void Alloc(int );
    Copy [Method] int Copy(int , ref array@int , int , int );
    Empty [Method] int Empty();
    Erase [Method] int Erase(int );
    Fill [Method] int Fill(int , int , int );
    Find [Method] int Find(int , int , int , bool(int, int)  = &NULL);
    Free [Method] void Free();
    Insert [Method] void Insert(int , int );
    Numof [Method] int Numof(int  = 1);
    PopBack [Method] void PopBack();
    PushBack [Method] void PushBack(int );
    Realloc [Method] void Realloc(int );
    Reverse [Method] void Reverse();
    Sort [Method] void Sort(int(int, int)  = &NULL);
    |}]

let%expect_test "get_completion_hll_library" =
  let proj = initialize_completion_project () in
  let path = testdir_path [ "src"; "completion.jaf" ] in
  let text = "void completion_test(void) {\n\tMyLib.Add(1, 2);\n}\n" in
  (* Cursor right after `MyLib.`. *)
  let pos = Lsp.Types.Position.create ~line:1 ~character:7 in
  completion_at proj path text pos;
  [%expect
    {|
    Add [Function] int Add(int a, int b);
    Compute [Function] float Compute(float x, float y);
    Greet [Function] void Greet(string name);
    |}]

let%expect_test "get_completion_sort_text" =
  let proj = initialize_completion_project () in
  let path = testdir_path [ "src"; "completion.jaf" ] in
  (* Inside a method body so all three sort buckets are populated:
     locals (`local_x`), class members (TestCls's fields/methods), and
     globals (gvar/gfunc/etc.). *)
  let text = "int TestCls::tc_method() {\n\tint local_x;\n\t\n}\n" in
  let pos = Lsp.Types.Position.create ~line:2 ~character:1 in
  List.iter (Project.update_document proj ~path text) ~f:(fun _ -> ());
  (match Project.get_completion proj ~path pos with
  | Some (`CompletionList cl) ->
      let interesting =
        [
          "local_x";
          "tc_member";
          "tc_method";
          "tc_priv_field";
          "gvar";
          "gfunc";
          "TestCls";
        ]
      in
      List.iter interesting ~f:(fun name ->
          match
            List.find cl.items ~f:(fun (it : Lsp.Types.CompletionItem.t) ->
                String.equal it.label name)
          with
          | Some it ->
              Stdio.printf "  %s -> %s\n" name
                (Option.value it.sortText ~default:"(none)")
          | None -> Stdio.printf "  %s -> (missing)\n" name)
  | _ -> Stdio.print_endline "(none)");
  [%expect
    {|
    local_x -> 0_local_x
    tc_member -> 1_tc_member
    tc_method -> 1_tc_method
    tc_priv_field -> 1_tc_priv_field
    gvar -> 2_gvar
    gfunc -> 2_gfunc
    TestCls -> 2_TestCls
    |}]

(* Member completion (after `.`) does not get a sortText prefix; items are
   sorted alphabetically by the client. *)
let%expect_test "get_completion_member_no_sort_text" =
  let proj = initialize_completion_project () in
  let path = testdir_path [ "src"; "completion.jaf" ] in
  let text = "void completion_test(void) {\n\tSType s;\n\tint i = s.x;\n}\n" in
  let pos = Lsp.Types.Position.create ~line:2 ~character:11 in
  List.iter (Project.update_document proj ~path text) ~f:(fun _ -> ());
  (match Project.get_completion proj ~path pos with
  | Some (`CompletionList cl) ->
      List.iter cl.items ~f:(fun (it : Lsp.Types.CompletionItem.t) ->
          Stdio.printf "  %s -> %s\n" it.label
            (Option.value it.sortText ~default:"(none)"))
  | _ -> Stdio.print_endline "(none)");
  [%expect {| x -> (none) |}]

(* Signature help: global functions. *)

let print_signature_help (sh : Lsp.Types.SignatureHelp.t) =
  let active =
    match sh.activeParameter with
    | Some (Some i) -> Int.to_string i
    | _ -> "(none)"
  in
  Stdio.printf "active: %s\n" active;
  List.iter sh.signatures ~f:(fun (s : Lsp.Types.SignatureInformation.t) ->
      Stdio.printf "  %s\n" s.label;
      Option.iter s.parameters ~f:(fun ps ->
          List.iter ps ~f:(fun (p : Lsp.Types.ParameterInformation.t) ->
              match p.label with
              | `String s -> Stdio.printf "    param: %s\n" s
              | `Offset (a, b) -> Stdio.printf "    param: [%d, %d)\n" a b)))

let signature_help_at proj path text pos =
  List.iter (Project.update_document proj ~path text) ~f:(fun _ -> ());
  match Project.get_signature_help proj ~path pos with
  | Some sh -> print_signature_help sh
  | None -> Stdio.print_endline "(none)"

let initialize_signature_help_project () =
  initialize_project ~pje:"signature_help.pje" ()

let%expect_test "get_signature_help_global_function" =
  let proj = initialize_signature_help_project () in
  let path = testdir_path [ "src"; "signature_help.jaf" ] in
  let text = "void signature_help_test(void) {\n\tgfunc(\n}\n" in
  let pos = Lsp.Types.Position.create ~line:1 ~character:7 in
  signature_help_at proj path text pos;
  [%expect
    {|
    active: 0
      void gfunc(int x);
        param: [11, 16)
    |}]

let%expect_test "get_signature_help_active_parameter_after_comma" =
  let proj = initialize_signature_help_project () in
  let path = testdir_path [ "src"; "signature_help.jaf" ] in
  (* Two-arg call: cursor is after the first comma so activeParameter = 1. *)
  let text = "void signature_help_test(void) {\n\tgfunc2(1, \n}\n" in
  let pos = Lsp.Types.Position.create ~line:1 ~character:11 in
  signature_help_at proj path text pos;
  [%expect
    {|
    active: 1
      void gfunc2(int a, int b);
        param: [12, 17)
        param: [19, 24)
    |}]

let%expect_test "get_signature_help_no_call_site" =
  let proj = initialize_signature_help_project () in
  let path = testdir_path [ "src"; "signature_help.jaf" ] in
  let text = "void signature_help_test(void) {\n\tint x = \n}\n" in
  let pos = Lsp.Types.Position.create ~line:1 ~character:9 in
  signature_help_at proj path text pos;
  [%expect {| (none) |}]

let%expect_test "get_signature_help_string_literal_with_paren" =
  let proj = initialize_signature_help_project () in
  let path = testdir_path [ "src"; "signature_help.jaf" ] in
  (* The "(" inside the string literal must not be misread as the call site. *)
  let text = "void signature_help_test(void) {\n\tgfunc2(\"(\", \n}\n" in
  let pos = Lsp.Types.Position.create ~line:1 ~character:12 in
  signature_help_at proj path text pos;
  [%expect
    {|
    active: 1
      void gfunc2(int a, int b);
        param: [12, 17)
        param: [19, 24)
    |}]

let%expect_test "get_signature_help_nested_call" =
  let proj = initialize_signature_help_project () in
  let path = testdir_path [ "src"; "signature_help.jaf" ] in
  (* Outer call's signature should win when the cursor is in its arg list,
     past the inner call. *)
  let text = "void signature_help_test(void) {\n\tgfunc2(gfunc(1), \n}\n" in
  let pos = Lsp.Types.Position.create ~line:1 ~character:17 in
  signature_help_at proj path text pos;
  [%expect
    {|
    active: 1
      void gfunc2(int a, int b);
        param: [12, 17)
        param: [19, 24)
    |}]

let%expect_test "get_signature_help_after_close_paren" =
  let proj = initialize_signature_help_project () in
  let path = testdir_path [ "src"; "signature_help.jaf" ] in
  let text = "void signature_help_test(void) {\n\tgfunc(1)\n}\n" in
  let pos = Lsp.Types.Position.create ~line:1 ~character:9 in
  signature_help_at proj path text pos;
  [%expect {| (none) |}]

let%expect_test "get_signature_help_multiline_args" =
  let proj = initialize_signature_help_project () in
  let path = testdir_path [ "src"; "signature_help.jaf" ] in
  let text = "void signature_help_test(void) {\n\tgfunc(\n\t\t\n}\n" in
  let pos = Lsp.Types.Position.create ~line:2 ~character:2 in
  signature_help_at proj path text pos;
  [%expect
    {|
    active: 0
      void gfunc(int x);
        param: [11, 16)
    |}]

(* Signature help: methods, syscalls, HLL, builtins, functypes. *)

let%expect_test "get_signature_help_method_on_object" =
  let proj = initialize_signature_help_project () in
  let path = testdir_path [ "src"; "signature_help.jaf" ] in
  let text = "void signature_help_test(void) {\n\tsh_obj.sh_method(1, \n}\n" in
  let pos = Lsp.Types.Position.create ~line:1 ~character:21 in
  signature_help_at proj path text pos;
  [%expect
    {|
    active: 1
      int sh_method(int x, int y);
        param: [14, 19)
        param: [21, 26)
    |}]

let%expect_test "get_signature_help_method_this" =
  let proj = initialize_signature_help_project () in
  let path = testdir_path [ "src"; "signature_help.jaf" ] in
  (* Layout matches the initial fixture: signature_help_test body on
     lines 0-1, blank line 2, sh_test_method body on lines 3-5. The
     cursor lies inside the method body so scope lookup against
     [last_good_toplevel] finds the enclosing class. *)
  let text =
    "void signature_help_test(void) {\n\
     }\n\n\
     int SHCls::sh_test_method(int n) {\n\
     \treturn this.sh_method2(\n\
     }\n"
  in
  let pos = Lsp.Types.Position.create ~line:4 ~character:24 in
  signature_help_at proj path text pos;
  [%expect
    {|
    active: 0
      int sh_method2(string s);
        param: [15, 23)
    |}]

let%expect_test "get_signature_help_method_implicit" =
  let proj = initialize_signature_help_project () in
  let path = testdir_path [ "src"; "signature_help.jaf" ] in
  let text =
    "void signature_help_test(void) {\n\
     }\n\n\
     int SHCls::sh_test_method(int n) {\n\
     \treturn sh_method2(\n\
     }\n"
  in
  let pos = Lsp.Types.Position.create ~line:4 ~character:19 in
  signature_help_at proj path text pos;
  [%expect
    {|
    active: 0
      int sh_method2(string s);
        param: [15, 23)
    |}]

let%expect_test "get_signature_help_syscall" =
  let proj = initialize_signature_help_project () in
  let path = testdir_path [ "src"; "signature_help.jaf" ] in
  let text = "void signature_help_test(void) {\n\tsystem.Output(\n}\n" in
  let pos = Lsp.Types.Position.create ~line:1 ~character:15 in
  signature_help_at proj path text pos;
  [%expect
    {|
    active: 0
      string Output(string );
        param: [14, 21)
    |}]

let%expect_test "get_signature_help_hll" =
  let proj = initialize_signature_help_project () in
  let path = testdir_path [ "src"; "signature_help.jaf" ] in
  let text = "void signature_help_test(void) {\n\tSHLib.Add(1, \n}\n" in
  let pos = Lsp.Types.Position.create ~line:1 ~character:13 in
  signature_help_at proj path text pos;
  [%expect
    {|
    active: 1
      int Add(int a, int b);
        param: [8, 13)
        param: [15, 20)
    |}]

let%expect_test "get_signature_help_builtin_array" =
  let proj = initialize_signature_help_project () in
  let path = testdir_path [ "src"; "signature_help.jaf" ] in
  (* sh_arr is a global array@int defined in signature_help_globals.jaf. *)
  let text = "void signature_help_test(void) {\n\tsh_arr.PushBack(\n}\n" in
  let pos = Lsp.Types.Position.create ~line:1 ~character:17 in
  signature_help_at proj path text pos;
  [%expect
    {|
    active: 0
      void PushBack(int );
        param: [14, 18)
    |}]

let%expect_test "get_signature_help_builtin_string" =
  let proj = initialize_signature_help_project () in
  let path = testdir_path [ "src"; "signature_help.jaf" ] in
  let text = "void signature_help_test(void) {\n\tsh_str.Find(\n}\n" in
  let pos = Lsp.Types.Position.create ~line:1 ~character:13 in
  signature_help_at proj path text pos;
  [%expect
    {|
    active: 0
      int Find(string );
        param: [9, 16)
    |}]

let%expect_test "get_signature_help_functype_var" =
  let proj = initialize_signature_help_project () in
  let path = testdir_path [ "src"; "signature_help.jaf" ] in
  let text = "void signature_help_test(void) {\n\tsh_ft_var(\n}\n" in
  let pos = Lsp.Types.Position.create ~line:1 ~character:11 in
  signature_help_at proj path text pos;
  [%expect
    {|
    active: 0
      int sh_ft(int n);
        param: [10, 15)
    |}]

let%expect_test "get_signature_help_delegate_var" =
  let proj = initialize_signature_help_project () in
  let path = testdir_path [ "src"; "signature_help.jaf" ] in
  let text = "void signature_help_test(void) {\n\tsh_dg_var(\n}\n" in
  let pos = Lsp.Types.Position.create ~line:1 ~character:11 in
  signature_help_at proj path text pos;
  [%expect
    {|
    active: 0
      void sh_dg(string s);
        param: [11, 19)
    |}]

let%expect_test "get_signature_help_utf16_offsets" =
  let proj = initialize_signature_help_project () in
  let path = testdir_path [ "src"; "signature_help.jaf" ] in
  (* Multibyte parameter names exercise the UTF-8 -> UTF-16 counter:
     each CJK char is 3 UTF-8 bytes but 1 UTF-16 code unit. *)
  let text = "void signature_help_test(void) {\n\tsh_unicode(\n}\n" in
  let pos = Lsp.Types.Position.create ~line:1 ~character:12 in
  signature_help_at proj path text pos;
  [%expect
    {|
    active: 0
      void sh_unicode(int あ, int い);
        param: [16, 21)
        param: [23, 28)
    |}]

let%expect_test "get_signature_help_assert" =
  let proj = initialize_signature_help_project () in
  let path = testdir_path [ "src"; "signature_help.jaf" ] in
  (* `assert` is a JAF keyword, so it can't be parsed as an expression;
     signature help is synthesized directly. Only the user-visible
     condition argument is shown - the file / line / stringified
     expression are auto-supplied by the parser. *)
  let text = "void signature_help_test(void) {\n\tassert(\n}\n" in
  let pos = Lsp.Types.Position.create ~line:1 ~character:8 in
  signature_help_at proj path text pos;
  [%expect
    {|
    active: 0
      void assert(int condition);
        param: [12, 25)
    |}]

(* Signature help: '//' comment skipping. *)

let%expect_test "get_signature_help_line_comment_only" =
  let proj = initialize_signature_help_project () in
  let path = testdir_path [ "src"; "signature_help.jaf" ] in
  (* The '(' lives entirely inside a '//' comment, so no call site is found. *)
  let text = "void signature_help_test(void) {\n\t// gfunc(\n}\n" in
  let pos = Lsp.Types.Position.create ~line:1 ~character:10 in
  signature_help_at proj path text pos;
  [%expect {| (none) |}]

let%expect_test "get_signature_help_comment_in_args" =
  let proj = initialize_signature_help_project () in
  let path = testdir_path [ "src"; "signature_help.jaf" ] in
  (* Commas and a paren inside a trailing '//' comment must be ignored:
     the comment '(' is masked so it isn't picked as the call site, and
     the three commas in '// ,,,(' don't bump activeParameter. *)
  let text =
    "void signature_help_test(void) {\n\tgfunc2(1, // ,,,(\n\t\t\n}\n"
  in
  let pos = Lsp.Types.Position.create ~line:2 ~character:2 in
  signature_help_at proj path text pos;
  [%expect
    {|
    active: 1
      void gfunc2(int a, int b);
        param: [12, 17)
        param: [19, 24)
    |}]
