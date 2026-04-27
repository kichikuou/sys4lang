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

let load_jaf proj path =
  let jaf_text = Stdio.In_channel.read_all path in
  List.iter (Project.update_document proj ~path jaf_text) ~f:(fun d ->
      Stdio.printf "(%d, %d) - (%d, %d) " d.range.start.line
        d.range.start.character d.range.end_.line d.range.end_.character;
      match d.message with
      | `String message -> Stdio.print_endline message
      | _ -> Stdio.print_endline "?");
  jaf_text

let%expect_test "get_hover" =
  let proj = initialize_project () in
  let path = testdir_path [ "src"; "hover.jaf" ] in
  let jaf_text = load_jaf proj path in
  let lines = String.split_lines jaf_text in
  List.iteri lines ~f:(fun i line ->
      match String.substr_index line ~pattern:"^hover" with
      | Some col -> (
          let pos = Lsp.Types.Position.create ~line:(i - 1) ~character:col in
          Stdio.printf "%d:%d: " pos.line pos.character;
          let hover = Project.get_hover proj ~path pos in
          match hover with
          | Some { contents = `MarkupContent { value; _ }; _ } ->
              Stdio.print_endline value
          | _ -> Stdio.print_endline "No hover info")
      | None -> ());
  [%expect
    {|
    1:11: int
    6:11: string
    11:7: int Copy(int , ref array@string , int , int );
    |}]

let definition_test
    (getdef :
      Project.t ->
      path:string ->
      Lsp.Types.Position.t ->
      Lsp.Types.Locations.t option) pattern ~load_classes_after_def =
  let proj = initialize_project () in
  let path = testdir_path [ "src"; "definition.jaf" ] in
  let jaf_text = load_jaf proj path in
  if load_classes_after_def then
    load_jaf proj (testdir_path [ "src"; "classes.jaf" ]) |> ignore;
  let lines = String.split_lines jaf_text in
  List.iteri lines ~f:(fun i line ->
      match String.substr_index line ~pattern with
      | Some col -> (
          let pos = Lsp.Types.Position.create ~line:(i - 1) ~character:col in
          Stdio.printf "%d:%d: " pos.line pos.character;
          let locs = getdef proj ~path pos in
          match locs with
          | Some (`Location [ loc ]) ->
              let def_path = Lsp.Uri.to_path loc.uri in
              let def_text = Stdio.In_channel.read_all def_path in
              let def_lines = String.split_lines def_text in
              let start_line = List.nth_exn def_lines loc.range.start.line in
              let text =
                String.sub start_line ~pos:loc.range.start.character
                  ~len:(loc.range.end_.character - loc.range.start.character)
              in
              Stdio.printf "%s:%d:%d-%d \"%s\"\n"
                (Stdlib.Filename.basename def_path)
                loc.range.start.line loc.range.start.character
                loc.range.end_.character text
          | _ -> Stdio.print_endline "No definition found")
      | None -> ())

let%expect_test "get_definition" =
  let test ~load_classes_after_def =
    definition_test Project.get_definition "^definition" ~load_classes_after_def;
    [%expect
      {|
      1:11: definition.jaf:0:21-26 "int x"
      6:11: globals.jaf:0:4-14 "global_int"
      13:5: definition.jaf:10:0-17 "void foo(void) {}"
      15:6: definition.jaf:29:0-18 "int C::method() {}"
      |}]
  in
  test ~load_classes_after_def:false;
  test ~load_classes_after_def:true

let%expect_test "get_references" =
  let proj = initialize_project () in
  let path = testdir_path [ "src"; "references.jaf" ] in
  let jaf_text = load_jaf proj path in
  let lines = String.split_lines jaf_text in
  List.iteri lines ~f:(fun i line ->
      match String.substr_index line ~pattern:"^ref" with
      | Some col -> (
          let pos = Lsp.Types.Position.create ~line:(i - 1) ~character:col in
          Stdio.printf "%d:%d:\n" pos.line pos.character;
          match
            Project.get_references proj ~path pos ~include_declaration:true
          with
          | None -> Stdio.print_endline "  (none)"
          | Some locs ->
              let sorted =
                List.sort locs ~compare:(fun (a : Lsp.Types.Location.t) b ->
                    let cmp =
                      String.compare (Lsp.Uri.to_path a.uri)
                        (Lsp.Uri.to_path b.uri)
                    in
                    if cmp <> 0 then cmp
                    else
                      let cmp =
                        Int.compare a.range.start.line b.range.start.line
                      in
                      if cmp <> 0 then cmp
                      else
                        Int.compare a.range.start.character
                          b.range.start.character)
              in
              List.iter sorted ~f:(fun (loc : Lsp.Types.Location.t) ->
                  let fname =
                    Stdlib.Filename.basename (Lsp.Uri.to_path loc.uri)
                  in
                  Stdio.printf "  %s:%d:%d-%d:%d\n" fname loc.range.start.line
                    loc.range.start.character loc.range.end_.line
                    loc.range.end_.character))
      | None -> ());
  [%expect
    {|
    0:4:
      references.jaf:0:0-8:1
    2:12:
      references.jaf:0:15-0:20
      references.jaf:2:12-2:13
      references.jaf:4:12-4:13
    4:4:
      references.jaf:2:8-2:17
      references.jaf:4:4-4:5
      references.jaf:4:8-4:9
      references.jaf:6:11-6:12
    6:11:
      references.jaf:2:8-2:17
      references.jaf:4:4-4:5
      references.jaf:4:8-4:9
      references.jaf:6:11-6:12
    11:16:
      definition.jaf:6:11-6:21
      globals.jaf:0:4-0:14
      references.jaf:11:12-11:22
      references.jaf:13:4-13:14
      references.jaf:15:11-15:21
    13:8:
      definition.jaf:6:11-6:21
      globals.jaf:0:4-0:14
      references.jaf:11:12-11:22
      references.jaf:13:4-13:14
      references.jaf:15:11-15:21
    15:15:
      definition.jaf:6:11-6:21
      globals.jaf:0:4-0:14
      references.jaf:11:12-11:22
      references.jaf:13:4-13:14
      references.jaf:15:11-15:21
    19:9:
      references.jaf:19:0-19:34
      references.jaf:23:4-23:24
      references.jaf:25:4-25:24
    23:10:
      references.jaf:19:0-19:34
      references.jaf:23:4-23:24
      references.jaf:25:4-25:24
    25:10:
      references.jaf:19:0-19:34
      references.jaf:23:4-23:24
      references.jaf:25:4-25:24
    30:4:
      references.jaf:29:16-29:19
      references.jaf:30:4-30:5
      references.jaf:32:11-32:12
    32:13:
      classes.jaf:0:15-0:16
      definition.jaf:20:11-20:14
      references.jaf:30:4-30:7
      references.jaf:32:11-32:14
    |}]

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

(* Phase 2: locals/params and enclosing class scope. *)

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

(* Phase 3: member completion after '.'. *)

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

let%expect_test "get_type_definition" =
  let test ~load_classes_after_def =
    definition_test Project.get_type_definition "^type_definition"
      ~load_classes_after_def;
    [%expect
      {|
      20:11: classes.jaf:0:0-20 "struct S { int x; };"
      25:4: classes.jaf:2:0-23 "functype void ft(void);"
      |}]
  in
  test ~load_classes_after_def:false;
  test ~load_classes_after_def:true
