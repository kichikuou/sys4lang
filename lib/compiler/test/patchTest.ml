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

(* Patch code generation, initialization and file output. *)

open Common
open Compiler
open Base
open PatchTestSupport

let filenames ain =
  let rec collect index files =
    match Ain.get_file ain index with
    | Some file -> collect (index + 1) (file :: files)
    | None -> List.rev files
  in
  collect 0 []

(* Function replacement and body validation. *)

let%expect_test "patch stores a relative source filename in the AIN" =
  let ain = base "int target() { return 0; }" in
  with_program "int target() { return 0; }" "int target() { return 1; }"
    (fun program ->
      ignore (Patch.compile_sources ain program);
      List.filter (filenames ain) ~f:(Fn.non String.is_empty)
      |> List.iter ~f:Stdio.print_endline);
  [%expect {|
    base.jaf
    patch.jaf
    |}]

let%expect_test "ordinary replacement appends code and reuses function ID" =
  let ain =
    base
      "int g = 1; int helper(int x) { return x; } int target(int x) { return \
       x; } int caller() { return target(1); }"
  in
  let old_code = Ain.get_code ain in
  let before = Option.value_exn (Ain.get_function ain "target") in
  let caller = Option.value_exn (Ain.get_function ain "caller") in
  let null = Option.value_exn (Ain.get_function ain "NULL") in
  with_program "int g = 999; int helper(int x) { return unknown_body; }"
    "int target(int renamed) { int local = helper(renamed); return local + g; }"
    (fun p ->
      let names = function_names (Patch.compile_sources ain p) in
      let after = Option.value_exn (Ain.get_function ain "target") in
      Stdio.printf "replaced: %s\n" (String.concat ~sep:", " names);
      Stdio.printf "old CODE retained: %b\n"
        (Bytes.equal old_code
           (Bytes.sub (Ain.get_code ain) ~pos:0 ~len:(Bytes.length old_code)));
      Stdio.printf "ID retained: %b, address appended: %b, CRC changed: %b\n"
        (before.index = after.index)
        (after.address = Bytes.length old_code + 6)
        (not (Int32.equal before.crc after.crc));
      Stdio.printf "caller retained: %b, NULL retained: %b\n"
        (Poly.equal caller (Option.value_exn (Ain.get_function ain "caller")))
        (Poly.equal null (Option.value_exn (Ain.get_function ain "NULL")));
      Stdio.printf "variables: %s\n"
        (String.concat ~sep:", " (List.map after.vars ~f:(fun v -> v.name)));
      print_new_code ain (Bytes.length old_code));
  [%expect
    {|
    replaced: target
    old CODE retained: true
    ID retained: true, address appended: true, CRC changed: true
    caller retained: true, NULL retained: true
    variables: renamed, local
    FUNC target
    PUSHLOCALPAGE
    PUSH 1
    SH_LOCALREF renamed
    CALLFUNC helper
    ASSIGN
    POP
    SH_LOCALREF local
    SH_GLOBALREF global(0)
    ADD
    RETURN
    PUSH 0
    RETURN
    ENDFUNC target
    EOF <patch>
    |}]

let%expect_test "all declarations are checked before the selected body" =
  List.iter
    [
      ( "int g; int helper(int x) { return x; }",
        "int target() { int g = 3; return g; }" );
      ( "string g; int helper(int x) { return x; }",
        "int target() { int g = 3; return g; }" );
      ( "int g; string helper(string x) { return x; }",
        "int target() { return 0; }" );
      ( "int g; int helper(int x) { return x; } void missing() {}",
        "int target() { return 0; }" );
      ("Unknown new_global;", "int target() { return 0; }");
      ("struct NewType { int x; };", "int target() { return 0; }");
    ]
    ~f:(fun (reference, patch) ->
      let ain =
        base "int g; int helper(int x) { return x; } int target() { return 0; }"
      in
      with_program reference patch (fun p ->
          print_error (fun () ->
              ignore (Patch.compile_sources ain p);
              Stdio.print_endline "ok")));
  [%expect
    {|
    ok
    Patch global type mismatch: g
    Patch function signature mismatch: helper
    Patch function is absent from output: missing
    Patch undefined source type: Unknown
    New type NewType is not selected; select NewType or pass its source with --source.
    |}]

let%expect_test
    "all constants and defaults are checked before the selected body" =
  List.iter
    [
      "const int BAD = missing; int helper(int x) { return x; }";
      "int helper(int x = missing) { return x; }";
    ] ~f:(fun reference ->
      let ain =
        base "int helper(int x) { return x; } int target() { return 0; }"
      in
      with_program reference "int target() { return 1; }" (fun p ->
          print_error (fun () -> ignore (Patch.compile_sources ain p))));
  [%expect
    {|
    Undefined variable: missing
    Undefined variable: missing
    |}]

let%expect_test "unsupported and invalid target bodies are rejected" =
  List.iter
    [
      "void NULL() {}";
      "void target() { (() => int { return 1; }); }";
      "void target() { jump scene; }";
      "void target() { int x = \"bad\"; }";
    ] ~f:(fun patch ->
      let ain = base "void target() {}" in
      print_error (fun () ->
          with_program "" patch (fun p -> ignore (Patch.compile_sources ain p))));
  [%expect
    {|
    Syntax error
    Patch does not yet support lambdas in target bodies
    scene is not a scenario function
    Type error: expected int; got string
    |}]

let%expect_test "scenario replacement, addition and jumps in AIN v2 through v7"
    =
  let reference =
    {|#scene() { jumps "scene"; }
      #untouched() { jump scene; }
      void target() {}|}
  in
  List.iter (List.range 2 8) ~f:(fun version ->
      let ain = base ~version reference in
      let scene = Option.value_exn (Ain.get_function ain "scene") in
      let untouched = Option.value_exn (Ain.get_function ain "untouched") in
      let count = Ain.nr_functions ain in
      let start = Ain.code_size ain in
      with_program reference
        {|void target() { jump new_scene; }
          #scene() { jump new_scene; }
          #new_scene() { jumps "untouched"; }|}
        (fun program ->
          let result = Patch.compile_sources ain program in
          let replacement = Option.value_exn (Ain.get_function ain "scene") in
          let added = Option.value_exn (Ain.get_function ain "new_scene") in
          Stdio.printf
            "v%d: ID retained: %b, address appended: %b, new trailing ID: %b, \
             labels: %b, reference retained: %b\n"
            version
            (replacement.index = scene.index)
            (replacement.address > start)
            (added.index = count && Ain.nr_functions ain = count + 1)
            (replacement.is_label && added.is_label)
            (Poly.equal untouched
               (Option.value_exn (Ain.get_function ain "untouched")));
          if version = 4 then (
            print_result result;
            print_new_code ain start)));
  [%expect
    {|
    v2: ID retained: true, address appended: true, new trailing ID: true, labels: true, reference retained: true
    v3: ID retained: true, address appended: true, new trailing ID: true, labels: true, reference retained: true
    v4: ID retained: true, address appended: true, new trailing ID: true, labels: true, reference retained: true
    functions: target, scene, new_scene
    FUNC target
    S_PUSH "new_scene"
    CALLONJUMP
    SJUMP
    RETURN
    ENDFUNC target
    FUNC scene
    S_PUSH "new_scene"
    CALLONJUMP
    SJUMP
    ENDFUNC scene
    FUNC new_scene
    S_PUSH "untouched"
    CALLONJUMP
    SJUMP
    ENDFUNC new_scene
    EOF <patch>
    v5: ID retained: true, address appended: true, new trailing ID: true, labels: true, reference retained: true
    v6: ID retained: true, address appended: true, new trailing ID: true, labels: true, reference retained: true
    v7: ID retained: true, address appended: true, new trailing ID: true, labels: true, reference retained: true
    |}]

let%expect_test "scenario version and function-kind restrictions" =
  List.iter
    [
      (1, "void target() {}", "#scene() { jumps \"scene\"; }");
      (1, "void target() {}", "void target() { jumps \"scene\"; }");
      (4, "void target() {}", "#target() { jumps \"target\"; }");
      (4, "#target() { jumps \"target\"; }", "void target() {}");
    ]
    ~f:(fun (version, source, patch) ->
      let ain = base ~version source in
      print_error (fun () ->
          with_program "" patch (fun program ->
              ignore (Patch.compile_sources ain program))));
  [%expect
    {|
    Patch does not yet support special function scene
    Patch does not yet support scenario jumps
    Patch function signature mismatch: target
    Patch function signature mismatch: target
    |}]

let%expect_test
    "method replacement inherits defaults and privacy without renaming \
     parameters" =
  let reference =
    {|
    const int GLOBAL = 4;
    int untouched = 12;
    class C {
      const int FACTOR = GLOBAL + 2;
      int value;
      int helper(int original = FACTOR);
    public:
      int run(ref int input);
    };
    int C::helper(int original) { return original; }
    int C::run(ref int input) { return helper(input); }
    int target(C object) { int value = 0; return object.run(value); }
  |}
  in
  let ain =
    base (String.substr_replace_all reference ~pattern:"= FACTOR" ~with_:"= 6")
  in
  let start = Ain.code_size ain in
  let structure = Ain.get_struct ain "C" in
  let global = Ain.get_global ain "untouched" in
  with_program
    (String.substr_replace_all reference ~pattern:"= 12" ~with_:"= 999")
    {|
      int C::helper(int renamed) { return renamed + value; }
      int C::run(ref int changed) {
        int GLOBAL = 100;
        changed = helper();
        return changed + FACTOR;
      }
    |}
    (fun p ->
      Stdio.print_endline
        (String.concat ~sep:", " (function_names (Patch.compile_sources ain p)));
      Stdio.printf "STRT retained: %b, global retained: %b\n"
        (Poly.equal structure (Ain.get_struct ain "C"))
        (Poly.equal global (Ain.get_global ain "untouched"));
      print_new_code ain start);
  [%expect
    {|
    C@helper, C@run
    STRT retained: true, global retained: true
    FUNC C@helper
    SH_LOCALREF renamed
    SH_STRUCTREF 0
    ADD
    RETURN
    PUSH 0
    RETURN
    FUNC C@run
    SH_LOCALASSIGN GLOBAL, 100
    PUSHLOCALPAGE
    PUSH 0
    REFREF
    PUSHSTRUCTPAGE
    PUSH 6
    CALLMETHOD C@helper
    ASSIGN
    POP
    PUSHLOCALPAGE
    PUSH 0
    REFREF
    REF
    PUSH 6
    ADD
    RETURN
    PUSH 0
    RETURN
    EOF <patch>
    |}]

(* New functions and HLL calls. *)

let%expect_test "new functions reserve trailing IDs for cross-file mutual calls"
    =
  let ain = base "int existing(int x) { return x; }" in
  let count = Ain.nr_functions ain in
  let old_code = Ain.get_code ain in
  let start = Bytes.length old_code in
  with_files
    [
      ("project.pje", {|Source = { "reference.jaf", }|});
      ("reference.jaf", "int existing(int x) { return x; }");
      ( "first.jaf",
        "int existing(int x) { return first(x); } int first(int x) { if (x) \
         return second(x - 1); return 1; }" );
      ( "second.jaf",
        "int second(int x) { if (x) return first(x - 1); return existing(0); }"
      );
    ]
    (fun root ->
      let file = Stdlib.Filename.concat root in
      let p =
        PatchSources.load
          ~patch_files:[ file "first.jaf"; file "second.jaf" ]
          (file "project.pje")
      in
      Stdio.print_endline
        (String.concat ~sep:", " (function_names (Patch.compile_sources ain p)));
      Stdio.printf "trailing IDs: %b\n"
        ((Option.value_exn (Ain.get_function ain "first")).index = count
        && (Option.value_exn (Ain.get_function ain "second")).index = count + 1
        );
      Stdio.printf "old CODE retained: %b\n"
        (Bytes.equal old_code (Bytes.sub (Ain.get_code ain) ~pos:0 ~len:start));
      let dasm = Dasm.create ain in
      Dasm.jump dasm start;
      while not (Dasm.eof dasm) do
        (if
           Poly.equal
             (Bytecode.opcode_of_int (Dasm.opcode dasm))
             Bytecode.CALLFUNC
         then
           let caller =
             Ain.get_function_by_index ain
               (Option.value_exn (Dasm.current_func dasm))
           in
           let callee =
             Ain.get_function_by_index ain (Int32.to_int_exn (Dasm.arg dasm 0))
           in
           Stdio.printf "%s -> %s\n" caller.name callee.name);
        Dasm.next dasm
      done);
  [%expect
    {|
    existing, first, second
    trailing IDs: true
    old CODE retained: true
    existing -> first
    first -> second
    second -> first
    second -> existing
  |}]

let%expect_test "inline new method and new caller share the allocated method ID"
    =
  let ain = base "class C { int value; };" in
  let start = Ain.code_size ain in
  with_program ""
    "class C { int value; public: int added(int x) { return value + x; } }; \
     int caller(C object) { return object.added(4); }" (fun p ->
      ignore (Patch.compile_sources ain p);
      print_new_code ain start);
  [%expect
    {|
    FUNC C@added
    SH_STRUCTREF 0
    SH_LOCALREF x
    ADD
    RETURN
    PUSH 0
    RETURN
    FUNC caller
    SH_LOCALREF object
    PUSH 4
    CALLMETHOD C@added
    RETURN
    PUSH 0
    RETURN
    ENDFUNC caller
    EOF <patch>
    |}]

let%expect_test
    "HLL additions retain existing IDs and bind calls by import name" =
  let ain =
    base ~version:5
      ~hlls:[ ("api", "int First(int x); int Read(intp x); int Omitted();") ]
      "int target(ref int x) { return x; }"
  in
  let library = Ain.get_library_by_index ain 0 in
  with_files
    [
      ( "project.pje",
        {|Source = { "api.hll", "API", "extra.hll", "Extra", "patch.jaf", }|} );
      ( "api.hll",
        "int Read(intp renamed); int Appended(intp value); int First(int \
         renamed);" );
      ("extra.hll", "int Run(int value);");
      ( "patch.jaf",
        "int target(ref int value) { return API.Appended(value) + \
         Extra.Run(API.Read(value)); }" );
    ]
    (fun root ->
      let program =
        PatchSources.load
          ~targets:[ "target"; "Extra"; "API" ]
          (Stdlib.Filename.concat root "project.pje")
      in
      let start = Ain.code_size ain in
      print_entries (Patch.compile_sources ain program);
      print_new_code ain start;
      Stdio.printf "original HLL entries retained: %b\n"
        (Poly.equal library.functions
           (Array.sub (Ain.get_library_by_index ain 0).functions ~pos:0
              ~len:(Array.length library.functions))));
  [%expect
    {|
    Added HLL function: api.Appended
    Added HLL: extra
    Added HLL function: extra.Run
    FUNC target
    PUSHLOCALPAGE
    PUSH 0
    REFREF
    CALLHLL library(0), library_function(3)
    PUSHLOCALPAGE
    PUSH 0
    REFREF
    CALLHLL library(0), library_function(1)
    CALLHLL library(1), library_function(0)
    ADD
    RETURN
    PUSH 0
    RETURN
    ENDFUNC target
    EOF <patch>
    original HLL entries retained: true
    |}]

(* Global and member initialization. *)

let print_global_initval ain name =
  let value =
    match (Option.value_exn (Ain.get_global ain name)).initval with
    | None -> "none"
    | Some Ain.Variable.Void -> "void"
    | Some (Ain.Variable.Int value) -> Int32.to_string value
    | Some (Ain.Variable.Float value) -> Float.to_string value
    | Some (Ain.Variable.String value) -> Printf.sprintf "%S" value
  in
  Stdio.printf "%s=%s\n" name value

let%expect_test
    "constructor and destructor compilation retains IDs on replacement" =
  let ain = base "class C { public: int value; };" in
  let old_code = Ain.get_code ain in
  let before = Option.value_exn (Ain.get_struct ain "C") in
  let run () =
    with_program "class C { public: int value; C(); ~C(); };"
      "C::C() { value = 1; } C::~C() { value = 0; }" (fun program ->
        function_names (Patch.compile_sources ain program))
  in
  let names = run () in
  let ids () =
    List.map names ~f:(fun name ->
        (Option.value_exn (Ain.get_function ain name)).index)
  in
  let first_ids = ids () in
  List.iter2_exn names first_ids ~f:(fun name id ->
      Stdio.printf "%s: %d\n" name id);
  let after = Option.value_exn (Ain.get_struct ain "C") in
  Stdio.printf
    "constructor=%d destructor=%d; layout retained=%b; old code retained=%b\n"
    after.constructor after.destructor
    (Poly.equal before
       {
         after with
         constructor = before.constructor;
         destructor = before.destructor;
       })
    (Bytes.equal old_code
       (Bytes.sub (Ain.get_code ain) ~pos:0 ~len:(Bytes.length old_code)));
  let count = Ain.nr_functions ain in
  ignore (run ());
  Stdio.printf "IDs reused: %b; function count retained: %b\n"
    (Poly.equal first_ids (ids ()))
    (Ain.nr_functions ain = count);
  [%expect
    {|
    C@0: 1
    C@1: 2
    C@2: 3
    constructor=1 destructor=2; layout retained=true; old code retained=true
    IDs reused: true; function count retained: true
  |}]

let%expect_test "regenerate class and global arrays from declarations" =
  let open Common in
  let ain =
    base
      "class C { private: array@int a[4]; public: C() {} }; array@int g[8]; \
       int unchanged = 7;"
  in
  let old_code = Ain.get_code ain in
  let ctor = Option.value_exn (Ain.get_function ain "C@0") in
  let structure = Option.value_exn (Ain.get_struct ain "C") in
  with_project ~targets:[ "C"; "unchanged" ]
    "const int N = 3; class C { private: const int SIZE = N + 2; array@int \
     a[SIZE]; public: C(); }; array@int g[N]; int unchanged = 999;"
    (fun program ->
      let names = function_names (Patch.compile_sources ain program) in
      Stdio.printf "output: %s\n" (String.concat ~sep:", " names);
      print_new_code ain (Bytes.length old_code);
      Stdio.printf "GSET rebuilt: %b\n"
        (match Ain.get_global ain "unchanged" with
        | Some { initval = Some (Ain.Variable.Int value); _ } ->
            Int32.equal value 999l
        | _ -> false);
      Stdio.printf
        "CODE retained: %b; constructor retained: %b; STRT retained: %b\n"
        (Bytes.equal old_code
           (Bytes.sub (Ain.get_code ain) ~pos:0 ~len:(Bytes.length old_code)))
        (Poly.equal ctor (Option.value_exn (Ain.get_function ain "C@0")))
        (Poly.equal structure (Option.value_exn (Ain.get_struct ain "C"))));
  [%expect
    {|
    output: C@2, 0
    FUNC C@2
    PUSHSTRUCTPAGE
    PUSH 0
    PUSH 5
    PUSH 1
    A_ALLOC
    RETURN
    ENDFUNC C@2
    FUNC 0
    PUSHGLOBALPAGE
    PUSH 0
    PUSH 3
    PUSH 1
    A_ALLOC
    RETURN
    ENDFUNC 0
    EOF <patch>
    GSET rebuilt: true
    CODE retained: true; constructor retained: true; STRT retained: true
    |}]

let%expect_test
    "rebuild all global initial values and remove stale GSET entries" =
  let ain =
    base
      {|
        int integer = 1;
        float real = 1.5;
        string text = "old";
        int removed = 4;
        array@int values[2];
        ref array@int alias = values;
      |}
  in
  with_project ~targets:[ "integer" ]
    {|
      const int OFFSET = 2;
      int integer = 40 + OFFSET;
      float real = 2.5;
      string text = "new";
      int removed;
      array@int values[3];
      ref array@int alias = values;
    |}
    (fun program ->
      Stdio.printf "outputs: %s\n"
        (String.concat ~sep:", "
           (function_names (Patch.compile_sources ain program))));
  List.iter
    [ "integer"; "real"; "text"; "removed"; "alias" ]
    ~f:(print_global_initval ain);
  [%expect
    {|
    outputs: 0
    integer=42
    real=2.5
    text="new"
    removed=none
    alias=4
    |}]

let%expect_test "append global suffix and rebuild all initializers" =
  let open Common in
  let ain = base "int old = 1;" in
  let old = Option.value_exn (Ain.get_global ain "old") in
  let start = Ain.code_size ain in
  with_project ~targets:[ "added" ]
    "int old = 2; int added = 3; array@int values[4];" (fun program ->
      Stdio.printf "outputs: %s\n"
        (String.concat ~sep:", "
           (function_names (Patch.compile_sources ain program))));
  Stdio.printf "globals=%d; old ID=%d; added ID=%d; values ID=%d\n"
    (Ain.nr_globals ain) (Option.value_exn (Ain.get_global ain "old")).index
    (Option.value_exn (Ain.get_global ain "added")).index
    (Option.value_exn (Ain.get_global ain "values")).index;
  Stdio.printf "old declaration retained: %b\n"
    (Poly.equal
       { old with initval = None }
       { (Option.value_exn (Ain.get_global ain "old")) with initval = None });
  print_global_initval ain "old";
  print_global_initval ain "added";
  print_new_code ain start;
  [%expect
    {|
    outputs: 0
    globals=3; old ID=0; added ID=1; values ID=2
    old declaration retained: true
    old=2
    added=3
    FUNC 0
    PUSHGLOBALPAGE
    PUSH 2
    PUSH 4
    PUSH 1
    A_ALLOC
    RETURN
    ENDFUNC 0
    EOF <patch>
    |}]

let%expect_test "append physical member suffix including ref padding" =
  let open Common in
  let ain = base "class C { public: int old; };" in
  let old = List.hd_exn (Option.value_exn (Ain.get_struct ain "C")).members in
  let start = Ain.code_size ain in
  with_project ~targets:[ "C" ]
    "class C { public: int old; ref int added; array@int values[3]; };"
    (fun program ->
      Stdio.printf "outputs: %s\n"
        (String.concat ~sep:", "
           (function_names (Patch.compile_sources ain program))));
  let structure = Option.value_exn (Ain.get_struct ain "C") in
  List.iter structure.members ~f:(fun v ->
      Stdio.printf "%d:%s:%s\n" v.index v.name (Ain.Type.to_string v.value_type));
  Stdio.printf "old member retained: %b\n"
    (Poly.equal old (List.hd_exn structure.members));
  print_new_code ain start;
  [%expect
    {|
    outputs: C@0
    0:old:int
    1:added:ref<int>
    2:<void>:void
    3:values:array<int>
    old member retained: true
    FUNC C@0
    PUSHSTRUCTPAGE
    PUSH 3
    PUSH 3
    PUSH 1
    A_ALLOC
    RETURN
    EOF <patch>
    |}]

let%expect_test "new automatic initializer and removal preserve IDs" =
  let open Common in
  let ain = base "class C { array@int@2 a; array@int b; };" in
  with_project ~targets:[ "C" ]
    "class C { array@int@2 a[2][3]; array@int b[4]; };" (fun program ->
      let start = Ain.code_size ain in
      ignore (Patch.compile_sources ain program);
      print_new_code ain start);
  let first = Option.value_exn (Ain.get_function ain "C@0") in
  let start = Ain.code_size ain in
  with_project ~targets:[ "C" ] "class C { array@int@2 a; array@int b; };"
    (fun program ->
      ignore (Patch.compile_sources ain program);
      print_new_code ain start);
  Stdio.printf "ID and registration retained: %b\n"
    (first.index = (Option.value_exn (Ain.get_function ain "C@0")).index
    && first.index = (Option.value_exn (Ain.get_struct ain "C")).constructor);
  [%expect
    {|
    FUNC C@0
    PUSHSTRUCTPAGE
    PUSH 0
    PUSH 2
    PUSH 3
    PUSH 2
    A_ALLOC
    PUSHSTRUCTPAGE
    PUSH 1
    PUSH 4
    PUSH 1
    A_ALLOC
    RETURN
    EOF <patch>
    FUNC C@0
    RETURN
    EOF <patch>
    ID and registration retained: true
    |}]

let%expect_test "constructor patch splits automatic initializer like full build"
    =
  let open Common in
  let ain = base "class C { public: array@int a[16]; int used; };" in
  let original = Option.value_exn (Ain.get_function ain "C@0") in
  let strt = Ain.get_struct ain "C" in
  let start = Ain.code_size ain in
  with_program "class C { public: array@int a[32]; int used; C(); };"
    "C::C() { used = 1; }" (fun program ->
      Stdio.printf "%s\n"
        (String.concat ~sep:", "
           (function_names (Patch.compile_sources ain program))));
  print_new_code ain start;
  Stdio.printf "constructor ID retained: %b; STRT retained: %b\n"
    (original.index = (Option.value_exn (Ain.get_function ain "C@0")).index)
    (Poly.equal strt (Ain.get_struct ain "C"));
  let ctor = Ain.get_function ain "C@0" in
  with_project ~targets:[ "C" ]
    "class C { public: array@int a[64]; int used; C(); };" (fun program ->
      ignore (Patch.compile_sources ain program));
  Stdio.printf "initializer-only patch preserves constructor: %b\n"
    (Poly.equal ctor (Ain.get_function ain "C@0"));
  [%expect
    {|
    C@0, C@2
    FUNC C@0
    PUSHSTRUCTPAGE
    CALLMETHOD C@2
    PUSHSTRUCTPAGE
    PUSH 1
    PUSH 1
    ASSIGN
    POP
    RETURN
    EOF <patch>
    FUNC C@2
    PUSHSTRUCTPAGE
    PUSH 0
    PUSH 32
    PUSH 1
    A_ALLOC
    RETURN
    ENDFUNC C@2
    EOF <patch>
    constructor ID retained: true; STRT retained: true
    initializer-only patch preserves constructor: true
    |}]

let%expect_test
    "new class member arrays generate constructors and internal initializers" =
  let source =
    {|
      class Auto { public: array@int values[3]; };
      class Explicit { public: array@int values[4]; Explicit() {} ~Explicit() {} };
    |}
  in
  let ain = base "" in
  let start = Ain.code_size ain in
  with_program "" source (fun program ->
      print_result (Patch.compile_sources ain program));
  print_new_code ain start;
  List.iter [ "Auto"; "Explicit" ] ~f:(fun name ->
      let s = Option.value_exn (Ain.get_struct ain name) in
      Stdio.printf "%s constructor registered: %b; destructor registered: %b\n"
        name
        (s.constructor
       = (Option.value_exn (Ain.get_function ain (name ^ "@0"))).index)
        (match Ain.get_function ain (name ^ "@1") with
        | Some f -> s.destructor = f.index
        | None -> s.destructor = -1));
  [%expect
    {|
    Added class: Auto
    Added class: Explicit
    functions: Explicit@0, Explicit@1, Auto@0, Explicit@2
    FUNC Explicit@0
    PUSHSTRUCTPAGE
    CALLMETHOD Explicit@2
    RETURN
    FUNC Explicit@1
    RETURN
    EOF <patch>
    FUNC Auto@0
    PUSHSTRUCTPAGE
    PUSH 0
    PUSH 3
    PUSH 1
    A_ALLOC
    RETURN
    FUNC Explicit@2
    PUSHSTRUCTPAGE
    PUSH 0
    PUSH 4
    PUSH 1
    A_ALLOC
    RETURN
    ENDFUNC Explicit@2
    EOF <patch>
    Auto constructor registered: true; destructor registered: true
    Explicit constructor registered: true; destructor registered: true
    |}]

(* File output and serialization. *)

let%expect_test
    "file results include type-only additions and survive serialization" =
  with_files
    [
      ("project.pje", {| Source = { "types.jaf", } |});
      ( "types.jaf",
        "class C { public: int x; }; struct S { ref C c; }; functype S \
         Callback(ref C c); delegate void Handler(ref S s);" );
    ]
    (fun root ->
      let path = Stdlib.Filename.concat root in
      Ain.write_file
        (base "struct Old { int x; }; void old() {}")
        (path "base.ain");
      let run base_file =
        let result =
          Patch.compile ~base:(path base_file) ~output:(path "output.ain")
            ~targets:[ "Handler"; "S"; "C"; "Callback" ]
            ~sources:[] ~write_debug_info:false (path "project.pje")
        in
        List.iter result.added_types ~f:(fun (kind, name) ->
            Stdio.printf "Added %s: %s\n" kind name);
        Stdio.printf "added/replaced functions: %d/%d\n"
          (List.length result.added)
          (List.length result.replaced)
      in
      run "base.ain";
      let output = Ain.load (path "output.ain") in
      Stdio.printf "serialized counts: %d, %d, %d; CODE unchanged: %b\n"
        (Ain.nr_structs output) (Ain.nr_functypes output)
        (Ain.nr_delegates output)
        (Bytes.equal (Ain.get_code output)
           (Ain.get_code (Ain.load (path "base.ain"))));
      let before = Stdio.In_channel.read_all (path "output.ain") in
      run "output.ain";
      Stdio.printf "serialized reapplication unchanged: %b\n"
        (String.equal before (Stdio.In_channel.read_all (path "output.ain"))));
  [%expect
    {|
    Added class: C
    Added struct: S
    Added functype: Callback
    Added delegate: Handler
    added/replaced functions: 0/0
    serialized counts: 3, 1, 1; CODE unchanged: true
    added/replaced functions: 0/0
    serialized reapplication unchanged: true
    |}]

let%expect_test "debug information must belong to the base AIN" =
  with_files
    [
      ("project.pje", {| Source = { "game.jaf", } |});
      ("game.jaf", "int f() { return 1; }");
    ]
    (fun root ->
      let path = Stdlib.Filename.concat root in
      let ctx = Jaf.context_from_ain (Ain.create 4 0) in
      let debug_info = DebugInfo.create () in
      Compile.compile ctx [ Pje.Jaf "game.jaf" ] debug_info (fun _ ->
          Stdio.In_channel.read_all (path "game.jaf"));
      Ain.write_file ctx.ain (path "base.ain");
      DebugInfo.write_to_file debug_info (path "debug_info.json");
      let run () =
        try
          let result =
            Patch.compile ~base:(path "base.ain") ~output:(path "output.ain")
              ~targets:[ "f" ] ~sources:[] (path "project.pje")
          in
          List.iter result.replaced ~f:(Stdio.printf "Replaced: %s\n")
        with Sys_error message ->
          String.substr_replace_all message ~pattern:root ~with_:"<root>"
          |> String.tr ~target:'\\' ~replacement:'/'
          |> Stdio.print_endline
      in
      run ();
      run ());
  [%expect
    {|
    Replaced: f
    <root>/debug_info.json: debug information does not match base AIN <root>/base.ain
    |}]
