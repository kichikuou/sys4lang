(* Copyright (C) 2026 kichikuou <KichikuouChrome@gmail.com>
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, see <http://gnu.org/licenses/>.
 *)

(* Declaration compatibility, type resolution and entry tables. *)

open Common
open Compiler
open Base
open PatchTestSupport

(* Existing declaration compatibility. *)

let%expect_test "registration and validation retain input IDs and AIN" =
  let ain =
    base
      {|
    struct First { int x; };
    struct Second { ref int value; int tail; };
    int old_global = 12;
    int used_global = 13;
    int unused() { return 0; }
    int target(ref int old_arg, Second value) { return old_arg; }
  |}
  in
  let before = raw ain in
  with_program
    {|
    struct Second { ref int value; int tail; };
    struct First { int x; };
    int used_global = 999;
    int old_global = 12;
    int unused() { return 0; }
    int target(ref int old_arg, Second value) { return old_arg; }
  |}
    "int target(ref int renamed, Second value) { return renamed + used_global; \
     }" (fun program ->
      let t = PatchDeclarations.create ain program in
      let ctx = PatchDeclarations.context t in
      let f = Hashtbl.find_exn ctx.functions "target" in
      let g = Hashtbl.find_exn ctx.globals "used_global" in
      let original = Option.value_exn (Ain.get_function ain "target") in
      Stdio.printf "function ID retained: %b, parameter: %s\n"
        (Option.value_exn f.index = original.index)
        (List.hd_exn f.params).name;
      Stdio.printf "global ID retained: %b\n"
        (Option.value_exn g.index
       = (Option.value_exn (Ain.get_global ain "used_global")).index);
      let structure = Hashtbl.find_exn ctx.structs "Second" in
      Stdio.printf "structure ID: %d, ref member: %d, following member: %d\n"
        structure.index
        (Option.value_exn (Hashtbl.find_exn structure.members "value").index)
        (Option.value_exn (Hashtbl.find_exn structure.members "tail").index);
      Stdio.printf "AIN unchanged: %b\n" (String.equal before (raw ain)));
  [%expect
    {|
    function ID retained: true, parameter: renamed
    global ID retained: true
    structure ID: 1, ref member: 0, following member: 2
    AIN unchanged: true
    |}]

let%expect_test
    "replacement signature mismatch includes ref slot and array shape" =
  List.iter
    [
      "float target(ref int value) { return 0.0; }";
      "int target(int value) { return value; }";
      "int target(ref int value, int extra) { return value; }";
      "int target(array@int value) { return 0; }";
    ] ~f:(fun patch ->
      let ain = base "int target(ref int value) { return value; }" in
      print_error (fun () ->
          with_program "" patch (fun p ->
              ignore (PatchDeclarations.create ain p))));
  [%expect
    {|
    Patch function signature mismatch: target
    Patch function signature mismatch: target
    Patch function signature mismatch: target
    Patch function signature mismatch: target
    |}]

let%expect_test "recursive type references resolve without recursive validation"
    =
  let declarations =
    {|
    struct Node { ref Node next; };
    struct Left { ref Right right; };
    struct Right { ref Left left; };
    struct Handler { Callback callback; };
    functype void Callback(ref Handler handler);
  |}
  in
  let ain = base (declarations ^ "void target() {}") in
  with_program declarations "void target() {}" (fun p ->
      ignore (Patch.compile_sources ain p);
      Stdio.print_endline "resolved and validated");
  [%expect {| resolved and validated |}]

(* New types and their dependencies. *)

let%expect_test
    "all four type kinds resolve recursive references by name or source" =
  let source =
    {|
      class NewClass { public: ref NewClass next; ref NewStruct other; Callback callback; };
      struct NewStruct { ref NewClass object; EventHandler event; };
      functype NewStruct Callback(ref NewClass value, EventHandler event);
      delegate void EventHandler(ref NewStruct value, Callback callback);
    |}
  in
  let original =
    "struct Old { int x; }; functype int OldCallback(int x); delegate void \
     OldEvent(); int old; void unchanged() {}"
  in
  let expected = base (original ^ source) in
  List.iter [ false; true ] ~f:(fun by_source ->
      let ain = base original in
      let code = Ain.get_code ain in
      let run program =
        let result = Patch.compile_sources ain program in
        print_result result;
        let same = ref true in
        Ain.struct_iter ain ~f:(fun s ->
            same :=
              !same
              && Poly.equal s
                   (Option.value_exn (Ain.get_struct expected s.name)));
        Ain.functype_iter ain ~f:(fun f ->
            same :=
              !same
              && Poly.equal f
                   (Option.value_exn (Ain.get_functype expected f.name)));
        Ain.delegate_iter ain ~f:(fun f ->
            same :=
              !same
              && Poly.equal f
                   (Option.value_exn (Ain.get_delegate expected f.name)));
        Stdio.printf
          "tables match ordinary compilation: %b; CODE retained: %b\n" !same
          (Bytes.equal code (Ain.get_code ain))
      in
      if by_source then with_program "" source run
      else
        with_project
          ~targets:
            [ "EventHandler"; "Callback"; "NewStruct"; "NewClass"; "Callback" ]
          source run);
  [%expect
    {|
    Added class: NewClass
    Added struct: NewStruct
    Added functype: Callback
    Added delegate: EventHandler
    functions:
    tables match ordinary compilation: true; CODE retained: true
    Added class: NewClass
    Added struct: NewStruct
    Added functype: Callback
    Added delegate: EventHandler
    functions:
    tables match ordinary compilation: true; CODE retained: true
  |}]

let%expect_test "new classes and their bodies must both be selected" =
  let source = "class C { public: int method(int x) { return x + 1; } };" in
  List.iter [ [ "C" ]; [ "C::method" ] ] ~f:(fun targets ->
      print_error (fun () ->
          with_project ~targets source (fun program ->
              ignore (Patch.compile_sources (base "") program))));
  List.iter [ false; true ] ~f:(fun by_source ->
      let ain = base "" in
      let run program = print_result (Patch.compile_sources ain program) in
      if by_source then with_program "" source run
      else with_project ~targets:[ "C"; "C::method" ] source run);
  [%expect
    {|
    Patch function is absent from output: C@method
    New type C is not selected; select C or pass its source with --source.
    Added class: C
    functions: C@method
    Added class: C
    functions: C@method
  |}]

let%expect_test
    "new types are usable in signatures, locals, globals and members" =
  let ain = base "struct Existing { int old; }; int old = 1;" in
  with_program "int old = 1;"
    {|
      struct Node { int value; };
      functype int Callback(int value);
      delegate void Handler(ref Node value);
      struct Existing { int old; Node appended; Callback callback; Handler event; };
      Node global_node;
      Callback global_callback;
      Handler global_event;
      Node identity(Node argument, Callback callback, Handler event) {
        Node local;
        local.value = argument.value;
        return local;
      }
    |}
    (fun program ->
      print_result (Patch.compile_sources ain program);
      let s = Option.value_exn (Ain.get_struct ain "Existing") in
      Stdio.printf "old structure ID: %d; appended members: %d; globals: %d\n"
        s.index
        (List.length s.members - 1)
        (Ain.nr_globals ain);
      let f = Option.value_exn (Ain.get_function ain "identity") in
      Stdio.printf "return: %s; variables: %s\n"
        (Ain.Type.to_string f.return_type)
        (String.concat ~sep:", "
           (List.map f.vars ~f:(fun v -> Ain.Type.to_string v.value_type))));
  [%expect
    {|
    Added struct: Node
    Added functype: Callback
    Added delegate: Handler
    functions: identity
    old structure ID: 0; appended members: 3; globals: 4
    return: struct<1>; variables: struct<1>, functype<0>, delegate<0>, struct<1>
    |}]

let%expect_test "type dependencies must be selected and defined" =
  with_project ~targets:[ "Container" ]
    "struct Item { int value; }; struct Container { Item item; };"
    (fun program ->
      print_error (fun () -> ignore (Patch.compile_sources (base "") program)));
  with_project ~targets:[ "Container" ] "struct Container { Missing item; };"
    (fun program ->
      print_error (fun () -> ignore (Patch.compile_sources (base "") program)));
  [%expect
    {|
    New type Item is not selected; select Item or pass its source with --source.
    Patch undefined source type: Missing
  |}]

let%expect_test "duplicate and cross-kind type names are rejected" =
  List.iter
    [
      "class C { int x; }; struct C { int x; };";
      "struct C { int x; }; functype void C();";
    ] ~f:(fun source ->
      print_error (fun () ->
          with_program "" source (fun program ->
              ignore (Patch.compile_sources (base "") program))));
  print_error (fun () ->
      with_program "" "functype void C();" (fun program ->
          ignore (Patch.compile_sources (base "struct C { int x; };") program)));
  [%expect
    {|
    Patch duplicate source type declaration: C
    Patch type name collision (struct and functype): C
    Patch type name collision (source functype, input struct/class): C
    |}]

let%expect_test
    "existing function types allow parameter renaming and reject signature \
     changes" =
  let ain =
    base
      "functype int Callback(ref int original); delegate int Handler(ref int \
       original);"
  in
  let before = raw ain in
  with_project ~targets:[ "Callback"; "Handler" ]
    "functype int Callback(ref int renamed); delegate int Handler(ref int \
     renamed);" (fun program ->
      print_result (Patch.compile_sources ain program));
  Stdio.printf "AIN unchanged: %b\n" (String.equal before (raw ain));
  List.iter
    [
      "functype int Callback(int value);";
      "delegate float Handler(ref int value);";
    ] ~f:(fun source ->
      let ain =
        base
          "functype int Callback(ref int original); delegate int Handler(ref \
           int original);"
      in
      print_error (fun () ->
          with_program "" source (fun program ->
              ignore (Patch.compile_sources ain program))));
  [%expect
    {|
    functions:
    AIN unchanged: true
    Patch function type signature mismatch: Callback
    Patch function type signature mismatch: Handler
  |}]

(* Global groups and HLL imports. *)

let%expect_test "global groups append with stable IDs" =
  let ain = base ~version:5 "globalgroup Old { int old; } int ungrouped;" in
  with_project ~targets:[ "New" ]
    "globalgroup Empty; globalgroup Old { int old; } int ungrouped; \
     globalgroup New { int added; }" (fun program ->
      print_entries (Patch.compile_sources ain program);
      List.iter [ "Old"; "Empty"; "New" ] ~f:(fun name ->
          Stdio.printf "%s group ID: %d\n" name
            (Option.value_exn (Ain.find_global_group_index ain name)));
      List.init (Ain.nr_globals ain) ~f:(Ain.get_global_by_index ain)
      |> List.iter ~f:(fun (v : Ain.Variable.t) ->
          Stdio.printf "%s: ID %d, group %d\n" v.name v.index
            (Ain.get_global_group_index ain v.index));
      print_entries (Patch.compile_sources ain program));
  [%expect
    {|
    Added globalgroup: Empty
    Added globalgroup: New
    Old group ID: 0
    Empty group ID: 1
    New group ID: 2
    old: ID 0, group 0
    ungrouped: ID 1, group -1
    added: ID 2, group 2
    |}]

let%expect_test "global group mismatches and unsupported versions are rejected"
    =
  List.iter
    [
      (5, "globalgroup Old { int old; }", "globalgroup New { int old; }");
      (4, "", "globalgroup New { int added; }");
    ]
    ~f:(fun (version, original, source) ->
      print_error (fun () ->
          with_program "" source (fun program ->
              ignore (Patch.compile_sources (base ~version original) program))));
  [%expect
    {|
    Patch global group mismatch: old
    Patch global groups require AIN v5 or later: New
    |}]

let%expect_test "HLL imports reuse IDs and validate every source declaration" =
  List.iter
    [
      ("int Unused(int x); int Read(intp renamed);", "Read");
      ("string Unused(string x); int Read(intp renamed);", "Read");
      ("int Unused(int x); int Read(string renamed);", "Read");
      ("int Unused(int x); int Missing(intp x);", "Missing");
    ]
    ~f:(fun (declarations, called) ->
      let ctx = Jaf.context_from_ain (Ain.create 4 0) in
      Compile.compile ctx
        [ Pje.Hll ("api.hll", "Original"); Pje.Jaf "base.jaf" ]
        (DebugInfo.create ())
        (function
          | "api.hll" -> "int Unused(int x); int Read(intp x);"
          | _ -> "int target(ref int x) { return Original.Read(x); }");
      let ain = ctx.ain in
      let original = Ain.get_library_by_index ain 0 in
      with_files
        [
          ("project.pje", {|Source = { "api.hll", "API", }|});
          ("api.hll", declarations);
          ( "patch.jaf",
            "int target(ref int renamed) { return API." ^ called
            ^ "(renamed); }" );
        ]
        (fun root ->
          let p =
            PatchSources.load
              ~patch_files:[ Stdlib.Filename.concat root "patch.jaf" ]
              (Stdlib.Filename.concat root "project.pje")
          in
          let start = Ain.code_size ain in
          print_error (fun () ->
              ignore (Patch.compile_sources ain p);
              print_new_code ain start;
              Stdio.printf "HLL retained: %b\n"
                (Poly.equal original (Ain.get_library_by_index ain 0)))));
  [%expect
    {|
    FUNC target
    PUSHLOCALPAGE
    PUSH 0
    REFREF
    CALLHLL library(0), library_function(1)
    RETURN
    PUSH 0
    RETURN
    ENDFUNC target
    EOF <patch>
    HLL retained: true
    Patch HLL function signature mismatch: API.Unused
    Patch HLL function signature mismatch: API.Read
    Patch HLL function is absent from input AIN: Missing
    |}]

let%expect_test "HLL additions require selection" =
  List.iter
    [ ("api", "int Old(); int Added();"); ("new", "int Added();") ]
    ~f:(fun (name, source) ->
      with_files
        [
          ( "project.pje",
            "Source = { \"" ^ name ^ ".hll\", \"API\", \"target.jaf\", }" );
          (name ^ ".hll", source);
          ("target.jaf", "void target() {}");
        ]
        (fun root ->
          let ain =
            base ~version:5 ~hlls:[ ("api", "int Old();") ] "void target() {}"
          in
          print_error (fun () ->
              let program =
                PatchSources.load ~targets:[ "target" ]
                  (Stdlib.Filename.concat root "project.pje")
              in
              ignore (Patch.compile_sources ain program))));
  [%expect
    {|
    Patch HLL function is absent from input AIN: Added
    Patch HLL is absent from input AIN: new
    |}]
