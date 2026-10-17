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

open Common
open Base
open Compiler

let printf = Stdio.printf
let sprintf = Printf.sprintf
let is_hll name = String.is_suffix name ~suffix:".hll"
let import_name name = Stdlib.Filename.chop_extension name

let build ?(version = (4, 0)) ?debug_info files =
  let major, minor = version in
  let ctx = Jaf.create_context (Ain.create major minor) in
  let sources =
    List.map files ~f:(fun (name, _) ->
        if is_hll name then Pje.Hll (name, import_name name) else Pje.Jaf name)
  in
  let debug_info = Option.value debug_info ~default:(DebugInfo.create ()) in
  Compile.compile ctx sources debug_info (fun name ->
      List.Assoc.find_exn files ~equal:String.equal name);
  ctx.ain

let print_code ain ~from =
  let dasm = Dasm.create ain in
  while not (Dasm.eof dasm) do
    (if Dasm.addr dasm >= from then
       let opcode = Bytecode.opcode_of_int (Dasm.opcode dasm) in
       let args =
         List.map2_exn (Dasm.argument_types dasm) (Dasm.arguments dasm)
           ~f:(CompileTest.arg_to_string dasm ain)
       in
       printf "%03d: %s %s\n" (Dasm.addr dasm)
         (Bytecode.string_of_opcode opcode)
         (String.concat ~sep:", " args));
    Dasm.next dasm
  done

let patch ?(targets = []) ?(globals = false) ?(keep_crc = false)
    ?(selected = []) ?(extras = []) ?debug_info ?minor_version ?(quiet = false)
    base project =
  let pje = Pje.default_pje "test.pje" Pje.UTF8 in
  pje.ain_version <- Ain.version base;
  pje.ain_minor_version <-
    Option.value minor_version ~default:(Ain.minor_version base);
  let source origin (name, _) =
    Patch.
      {
        path = name;
        debug_path = name;
        origin;
        kind = (if is_hll name then `Hll (import_name name) else `Jaf);
      }
  in
  let sources =
    List.map project ~f:(fun f ->
        source
          (if List.mem selected (fst f) ~equal:String.equal then
             `Project_selected
           else `Project)
          f)
    @ List.map extras ~f:(source `Extra)
  in
  let files = project @ extras in
  let start = Ain.code_size base in
  try
    Patch.apply ~base ~pje ~sources ~targets ~globals ~keep_crc
      ~read_file:(fun s ->
        List.Assoc.find_exn files ~equal:String.equal s.Patch.path)
      ~debug_info;
    if not quiet then print_code base ~from:start
  with CompileError.Compile_error e ->
    CompileError.print_error e (List.Assoc.find files ~equal:String.equal)

let type_to_string ain (t : Ain.Type.t) =
  match t with
  | Struct i -> (Ain.get_struct_by_index ain i).name
  | _ -> Ain.Type.to_string t

let vars_to_string ain (vars : Ain.Variable.t list) =
  String.concat ~sep:", "
    (List.map vars ~f:(fun v -> type_to_string ain v.value_type ^ " " ^ v.name))

let print_function ain name =
  match Ain.get_function ain name with
  | None -> printf "%s: none\n" name
  | Some f ->
      printf "%d %s: address=%d nr_args=%d vars=[%s]\n" f.index f.name f.address
        f.nr_args
        (vars_to_string ain f.vars)

let print_struct ain name =
  match Ain.get_struct ain name with
  | None -> printf "%s: none\n" name
  | Some s ->
      let fname i =
        if i < 0 then "-" else (Ain.get_function_by_index ain i).name
      in
      printf "%d %s: members=[%s] constructor=%s destructor=%s\n" s.index s.name
        (vars_to_string ain s.members)
        (fname s.constructor) (fname s.destructor)

let print_globals ain =
  Ain.global_iter ain ~f:(fun g ->
      let initval =
        match g.variable.initval with
        | None -> ""
        | Some (Int i) -> sprintf " = %ld" i
        | Some (Float f) -> sprintf " = %f" f
        | Some (String s) -> sprintf " = \"%s\"" s
        | Some Void -> " = void"
      in
      let group =
        if Ain.version ain >= 5 && g.group_index >= 0 then
          Ain.get_global_group_name ain g.group_index ^ "."
        else ""
      in
      printf "%d %s%s %s%s\n" g.variable.index group
        (type_to_string ain g.variable.value_type)
        g.variable.name initval)

let base_src =
  {|
int g_score = 1;

int calc(int value) {
    return value * 2;
}

class Counter {
public:
    int value;
    Counter();
    int scaled(int factor);
};

Counter::Counter() {
    value = 1;
}

int Counter::scaled(int factor) {
    return value * factor;
}

int main() {
    return calc(g_score);
}
|}

let base () = build [ ("base.jaf", base_src) ]
let edit ~pattern ~with_ = String.substr_replace_first base_src ~pattern ~with_

let%expect_test "replace a function by name" =
  let ain = base () in
  let nr_functions = Ain.nr_functions ain in
  let project =
    [
      ("base.jaf", edit ~pattern:"return value * 2;" ~with_:"return value * 3;");
    ]
  in
  patch ain project ~targets:[ "calc" ];
  print_function ain "calc";
  printf "functions: %d -> %d\n" nr_functions (Ain.nr_functions ain);
  [%expect
    {|
    166: FUNC calc
    172: SH_LOCALREF value
    178: PUSH 3
    184: MUL
    186: RETURN
    188: PUSH 0
    194: RETURN
    196: ENDFUNC calc
    1 calc: address=172 nr_args=1 vars=[int value]
    functions: 6 -> 6
    |}]

let%expect_test "add a function and rename parameters with --source" =
  let ain = base () in
  let fixes =
    {|
int calc(int renamed) {
    return adjust(renamed);
}

int adjust(int value) {
    return value * 2;
}
|}
  in
  patch ain [ ("base.jaf", base_src) ] ~extras:[ ("fixes.jaf", fixes) ];
  print_function ain "calc";
  print_function ain "adjust";
  [%expect
    {|
    166: FUNC calc
    172: SH_LOCALREF renamed
    178: CALLFUNC adjust
    184: RETURN
    186: PUSH 0
    192: RETURN
    194: ENDFUNC calc
    200: FUNC adjust
    206: SH_LOCALREF value
    212: PUSH 2
    218: MUL
    220: RETURN
    222: PUSH 0
    228: RETURN
    230: ENDFUNC adjust
    1 calc: address=172 nr_args=1 vars=[int renamed]
    6 adjust: address=206 nr_args=1 vars=[int value]
    |}]

let%expect_test "--keep-crc keeps the CRC of replaced functions" =
  let crc ain name = (Option.value_exn (Ain.get_function ain name)).crc in
  let project =
    [
      ("base.jaf", edit ~pattern:"return value * 2;" ~with_:"return value - 2;");
    ]
  in
  let ain = base () in
  let original = crc ain "calc" in
  patch ain project ~targets:[ "calc" ] ~quiet:true;
  printf "default: %b\n" (Int32.equal original (crc ain "calc"));
  let ain = base () in
  patch ain project ~targets:[ "calc" ] ~keep_crc:true ~quiet:true;
  printf "keep_crc: %b\n" (Int32.equal original (crc ain "calc"));
  [%expect {|
    default: false
    keep_crc: true
    |}]

let%expect_test "signature mismatch" =
  let ain = base () in
  let fixes = {|
float calc(int value) {
    return 1.0;
}
|} in
  patch ain [ ("base.jaf", base_src) ] ~extras:[ ("fixes.jaf", fixes) ];
  [%expect
    {|
    fixes.jaf:2:1-4:2: Signature of calc does not match the base AIN
        2 | float calc(int value) {
        3 |     return 1.0;
        4 | }
    |}]

let%expect_test "--source bodies take priority over the project" =
  let ain = base () in
  let project =
    [ ("base.jaf", edit ~pattern:"return value * 2;" ~with_:"return 100;") ]
  in
  let fixes = {|
int calc(int value) {
    return 200;
}
|} in
  patch ain project ~targets:[ "calc" ] ~extras:[ ("fixes.jaf", fixes) ];
  [%expect
    {|
    166: FUNC calc
    172: PUSH 200
    178: RETURN
    180: PUSH 0
    186: RETURN
    188: ENDFUNC calc
    |}]

let%expect_test "same function in two --source files" =
  let ain = base () in
  let fix = {|
int calc(int value) {
    return 200;
}
|} in
  patch ain
    [ ("base.jaf", base_src) ]
    ~extras:[ ("a.jaf", fix); ("b.jaf", fix) ];
  [%expect {| Function calc is defined in both a.jaf and b.jaf |}]

let%expect_test "same function in two project files" =
  let ain = base () in
  let dup = {|
int calc(int value) {
    return 200;
}
|} in
  patch ain [ ("base.jaf", base_src); ("dup.jaf", dup) ] ~targets:[ "main" ];
  [%expect {| Function calc is defined in both base.jaf and dup.jaf |}]

let%expect_test "--source replaces a method defined in the class" =
  let ain = base () in
  let project =
    [
      ( "base.jaf",
        edit ~pattern:"int scaled(int factor);"
          ~with_:"int scaled(int factor) { return 0; }"
        |> String.substr_replace_first
             ~pattern:
               "int Counter::scaled(int factor) {\n\
               \    return value * factor;\n\
                }"
             ~with_:"" );
    ]
  in
  let fixes = {|
int Counter::scaled(int factor) {
    return factor;
}
|} in
  patch ain project ~extras:[ ("fixes.jaf", fixes) ];
  [%expect
    {|
    166: FUNC Counter@scaled
    172: SH_LOCALREF factor
    178: RETURN
    180: PUSH 0
    186: RETURN
    |}]

let%expect_test "project file selected with --source" =
  let ain = base () in
  let project =
    [
      ("base.jaf", base_src);
      ("extra.jaf", {|
int calc2(int value) {
    return calc(value) + 1;
}
|});
    ]
  in
  patch ain project ~selected:[ "extra.jaf" ];
  print_function ain "calc2";
  [%expect
    {|
    166: FUNC calc2
    172: SH_LOCALREF value
    178: CALLFUNC calc
    184: PUSH 1
    190: ADD
    192: RETURN
    194: PUSH 0
    200: RETURN
    202: ENDFUNC calc2
    6 calc2: address=172 nr_args=1 vars=[int value]
    |}]

let%expect_test "replace a class with --source" =
  let ain = base () in
  let fixes =
    {|
class Counter {
public:
    int value;
    int step;
    Counter();
    int scaled(int factor);
    void advance();
};

void Counter::advance()
{
    value += step;
}

int g_score = 10;
|}
  in
  patch ain [ ("base.jaf", base_src) ] ~extras:[ ("fixes.jaf", fixes) ];
  print_struct ain "Counter";
  print_function ain "Counter@advance";
  print_globals ain;
  [%expect
    {|
    166: FUNC Counter@advance
    172: PUSHSTRUCTPAGE
    174: PUSH 0
    180: SH_STRUCTREF 1
    186: PLUSA
    188: POP
    190: RETURN
    192: FUNC Counter@2
    198: RETURN
    200: ENDFUNC Counter@2
    0 Counter: members=[int value, int step] constructor=Counter@0 destructor=-
    6 Counter@advance: address=172 nr_args=0 vars=[]
    0 int g_score = 10
    |}]

let%expect_test "replaced class must keep base members and constructor" =
  let ain = base () in
  patch ain
    [ ("base.jaf", base_src) ]
    ~extras:
      [
        ( "fixes.jaf",
          {|
class Counter {
public:
    int step;
    Counter();
};
|} );
      ];
  let ain = base () in
  patch ain
    [ ("base.jaf", base_src) ]
    ~extras:
      [
        ( "fixes.jaf",
          {|
class Counter {
public:
    int value;
    int scaled(int factor);
};
|}
        );
      ];
  [%expect
    {|
    fixes.jaf:2:1-6:3: Existing members of Counter must keep their name, type, and order
        2 | class Counter {
        3 | public:
        4 |     int step;
        5 |     Counter();
        6 | };
    fixes.jaf:2:1-6:3: Constructor of Counter cannot be removed
        2 | class Counter {
        3 | public:
        4 |     int value;
        5 |     int scaled(int factor);
        6 | };
    |}]

let%expect_test "project definitions of methods missing from a replaced class" =
  let ain = base () in
  let fixes = {|
class Counter {
public:
    int value;
    Counter();
};
|} in
  patch ain [ ("base.jaf", base_src) ] ~extras:[ ("fixes.jaf", fixes) ];
  [%expect
    {|
    166: FUNC Counter@2
    172: RETURN
    174: ENDFUNC Counter@2
    |}];
  let ain = base () in
  patch ain
    [ ("base.jaf", base_src) ]
    ~targets:[ "Counter::scaled" ]
    ~extras:[ ("fixes.jaf", fixes) ];
  [%expect
    {|
    base.jaf:19:1-21:2: scaled is not declared in class Counter
       19 | int Counter::scaled(int factor) {
       20 |     return value * factor;
       21 | }
    |}]

let%expect_test "select a project method of a replaced class" =
  let ain = base () in
  let fixes =
    {|
class Counter {
public:
    int value;
    Counter();
    int scaled(int factor);
};
|}
  in
  patch ain
    [ ("base.jaf", base_src) ]
    ~targets:[ "Counter::scaled" ]
    ~extras:[ ("fixes.jaf", fixes) ]
    ~quiet:true;
  print_function ain "Counter@scaled";
  [%expect {| 3 Counter@scaled: address=172 nr_args=1 vars=[int factor] |}]

let%expect_test "replace globals with --source" =
  let src =
    {|
int a, b;
globalgroup G { int c = 1; }
int main() { return a + b + c; }
|}
  in
  let ain = build ~version:(6, 0) [ ("base.jaf", src) ] in
  patch ain [ ("base.jaf", src) ] ~extras:[ ("fixes.jaf", "int b = 5;") ];
  print_globals ain;
  [%expect {|
    0 int a
    1 int b = 5
    2 G.int c = 1
    |}];
  patch ain [ ("base.jaf", src) ] ~extras:[ ("fixes.jaf", "int c = 2;") ];
  [%expect
    {|
    fixes.jaf:1:5-10: Global c must be declared in the same group as in the project
        1 | int c = 2;
                ^^^^^
    |}]

let%expect_test "duplicate declarations in --source files" =
  let src = {|
int a;
class C { int x; };
int main() { return a; }
|} in
  let ain = build [ ("base.jaf", src) ] in
  patch ain
    [ ("base.jaf", src) ]
    ~extras:[ ("fix1.jaf", "int a = 1;"); ("fix2.jaf", "int a = 2;") ];
  patch ain
    [ ("base.jaf", src) ]
    ~extras:
      [
        ("fix1.jaf", "class C { int x; };"); ("fix2.jaf", "class C { int x; };");
      ];
  [%expect
    {|
    fix2.jaf:1:5-10: duplicate global definition
        1 | int a = 2;
                ^^^^^
    fix2.jaf:1:1-20: duplicate struct definition
        1 | class C { int x; };
            ^^^^^^^^^^^^^^^^^^^
    |}]

let%expect_test "methods" =
  let ain = base () in
  let project =
    [
      ( "base.jaf",
        edit ~pattern:"return value * factor;" ~with_:"return value + factor;"
        ^ {|
void Counter::reset() {
    value = 0;
}
|} );
    ]
  in
  patch ain project ~targets:[ "Counter::scaled" ] ~quiet:true;
  print_function ain "Counter@scaled";
  patch ain project ~targets:[ "Counter::reset" ];
  [%expect
    {|
    3 Counter@scaled: address=172 nr_args=1 vars=[int factor]
    base.jaf:27:1-29:2: reset is not declared in class Counter
       27 | void Counter::reset() {
       28 |     value = 0;
       29 | }
    |}]

let%expect_test "add a constructor and a destructor" =
  let src = {|
class Buffer {
public:
    array@int values[16];
};
|} in
  let ain = build [ ("base.jaf", src) ] in
  print_struct ain "Buffer";
  let project =
    [
      ( "base.jaf",
        {|
class Buffer {
public:
    array@int values[16];
    int size;
    Buffer();
    ~Buffer();
};
Buffer::Buffer() { size = 16; }
Buffer::~Buffer() { size = 0; }
|}
      );
    ]
  in
  patch ain project ~targets:[ "Buffer::Buffer" ];
  let ctor_only =
    [
      ( "base.jaf",
        {|
class Buffer {
public:
    array@int values[16];
    Buffer();
};
Buffer::Buffer() {}
|}
      );
    ]
  in
  patch ain ctor_only ~targets:[ "Buffer::Buffer" ];
  patch ain project ~targets:[ "Buffer"; "Buffer::Buffer"; "Buffer::~Buffer" ];
  print_struct ain "Buffer";
  [%expect
    {|
    0 Buffer: members=[array<int> values] constructor=Buffer@0 destructor=-
    base.jaf:2:1-8:3: New members of Buffer require selecting Buffer
        2 | class Buffer {
        3 | public:
        4 |     array@int values[16];
        5 |     int size;
        6 |     Buffer();
        7 |     ~Buffer();
        8 | };
    base.jaf:2:1-6:3: Buffer and Buffer::Buffer must be selected together
        2 | class Buffer {
        3 | public:
        4 |     array@int values[16];
        5 |     Buffer();
        6 | };
    048: FUNC Buffer@0
    054: PUSHSTRUCTPAGE
    056: CALLMETHOD Buffer@2
    062: PUSHSTRUCTPAGE
    064: PUSH 1
    070: PUSH 16
    076: ASSIGN
    078: POP
    080: RETURN
    082: FUNC Buffer@1
    088: PUSHSTRUCTPAGE
    090: PUSH 1
    096: PUSH 0
    102: ASSIGN
    104: POP
    106: RETURN
    108: FUNC Buffer@2
    114: PUSHSTRUCTPAGE
    116: PUSH 0
    122: PUSH 16
    128: PUSH 1
    134: A_ALLOC
    136: RETURN
    138: ENDFUNC Buffer@2
    0 Buffer: members=[array<int> values, int size] constructor=Buffer@0 destructor=Buffer@1
    |}]

let%expect_test "add types" =
  let ain = base () in
  let types =
    {|
struct Item {
    int value;
};

struct Container {
    Item item;
};

functype int Callback(ref Item item);
|}
  in
  patch ain [ ("base.jaf", base_src); ("types.jaf", types) ];
  patch ain
    [ ("base.jaf", base_src); ("types.jaf", types) ]
    ~targets:[ "Item"; "Container"; "Callback" ];
  print_struct ain "Item";
  print_struct ain "Container";
  [%expect
    {|
    No patch targets specified
    1 Item: members=[int value] constructor=- destructor=-
    2 Container: members=[Item item] constructor=- destructor=-
    |}];
  let ain = base () in
  patch ain
    [ ("base.jaf", base_src); ("types.jaf", types) ]
    ~targets:[ "Item"; "Callback" ];
  [%expect
    {|
    types.jaf:6:1-8:3: New struct Container must be selected
        6 | struct Container {
        7 |     Item item;
        8 | };
    |}]

let%expect_test "add a delegate" =
  let src = {|
int main() { return 0; }
|} in
  let ain = build ~version:(6, 10) [ ("base.jaf", src) ] in
  patch ain
    [ ("base.jaf", src) ]
    ~extras:[ ("fixes.jaf", "delegate void Handler(int x);") ];
  printf "%s\n" (Ain.get_delegate_by_index ain 0).name;
  [%expect {| Handler |}]

let%expect_test "add members and change array sizes" =
  let src = {|
class Buffer {
public:
    array@int values[16];
};
|} in
  let ain = build [ ("base.jaf", src) ] in
  let project =
    [
      ( "base.jaf",
        {|
class Buffer {
public:
    array@int values[32];
    int size;
};
|}
      );
    ]
  in
  patch ain project ~targets:[ "Buffer" ];
  print_struct ain "Buffer";
  [%expect
    {|
    048: FUNC Buffer@0
    054: PUSHSTRUCTPAGE
    056: PUSH 0
    062: PUSH 32
    068: PUSH 1
    074: A_ALLOC
    076: RETURN
    0 Buffer: members=[array<int> values, int size] constructor=Buffer@0 destructor=-
    |}];
  let project =
    [
      ( "base.jaf",
        {|
class Buffer {
public:
    int size;
    array@int values[16];
};
|}
      );
    ]
  in
  patch ain project ~targets:[ "Buffer" ];
  [%expect
    {|
    base.jaf:2:1-6:3: Existing members of Buffer must keep their name, type, and order
        2 | class Buffer {
        3 | public:
        4 |     int size;
        5 |     array@int values[16];
        6 | };
    |}]

let%expect_test "add globals" =
  let src = {|
int a = 1;
array@int arr[3];
|} in
  let ain = build ~version:(5, 0) [ ("base.jaf", src) ] in
  let project =
    [
      ( "base.jaf",
        {|
int a = 2;
array@int arr[4];
globalgroup G { string s = "x"; }
float f;
|}
      );
    ]
  in
  patch ain project ~globals:true;
  print_globals ain;
  [%expect
    {|
    054: FUNC 0
    060: PUSHGLOBALPAGE
    062: PUSH 1
    068: PUSH 4
    074: PUSH 1
    080: A_ALLOC
    082: RETURN
    084: ENDFUNC 0
    0 int a = 2
    1 array<int> arr
    2 G.string s = "x"
    3 float f
    |}];
  patch ain [ ("base.jaf", "int a; float f;") ] ~globals:true;
  patch ain [ ("base.jaf", src) ] ~targets:[ "a" ];
  [%expect
    {|
    base.jaf:1:14-15: Global f does not match the base AIN
        1 | int a; float f;
                         ^
    Globals cannot be selected by name; use --globals: a
    |}];
  let ain = build [ ("base.jaf", src) ] in
  patch ain [ ("base.jaf", src ^ "globalgroup G { int b; }") ] ~globals:true;
  [%expect
    {|
    base.jaf:4:1-25: Global groups require AIN version 5 or later
        4 | globalgroup G { int b; }
            ^^^^^^^^^^^^^^^^^^^^^^^^
    |}]

let%expect_test "references to declarations not in the base AIN" =
  let ain = base () in
  let project =
    [
      ( "base.jaf",
        edit ~pattern:"return value * 2;" ~with_:"return helper(value);"
        ^ {|
int helper(int x) { return x; }
|} );
    ]
  in
  patch ain project ~targets:[ "calc" ];
  [%expect
    {|
    base.jaf:5:12-18: Undefined variable: helper
    helper is declared in the project but is not in the base AIN. Select it to add it.
        5 |     return helper(value);
                       ^^^^^^
    |}]

let%expect_test "unselected changes to globals and members" =
  let ain = base () in
  let project =
    [
      ( "base.jaf",
        edit ~pattern:"return value * 2;" ~with_:"return value;"
        ^ "int g_new;\n" );
    ]
  in
  patch ain project ~targets:[ "calc" ];
  let project =
    [
      ( "base.jaf",
        edit ~pattern:"    int value;" ~with_:"    int value;\n    int extra;"
      );
    ]
  in
  patch ain project ~targets:[ "calc" ];
  let src = "int a;\nvoid f() {}\n" in
  let ain = build ~version:(5, 0) [ ("base.jaf", src) ] in
  patch ain [ ("base.jaf", src ^ "globalgroup G {}\n") ] ~targets:[ "f" ];
  patch ain [ ("base.jaf", "int b;\nvoid f() {}\n") ] ~targets:[ "f" ];
  patch ain [ ("base.jaf", "void f() {}\n") ] ~targets:[ "f" ];
  [%expect
    {|
    base.jaf:26:5-10: New global g_new requires --globals
       26 | int g_new;
                ^^^^^
    base.jaf:8:1-14:3: New members of Counter require selecting Counter
        8 | class Counter {
        9 | public:
       10 |     int value;
       11 |     int extra;
       12 |     Counter();
       13 |     int scaled(int factor);
       14 | };
    base.jaf:3:1-17: New global group G requires --globals
        3 | globalgroup G {}
            ^^^^^^^^^^^^^^^^
    base.jaf:1:5-6: Global b does not match the base AIN
        1 | int b;
                ^
    Existing globals must keep their name, type, order, and group
    |}]

let%expect_test "ain v8 builtin HLL functions" =
  let hll = {|
int Twice(ref int self);
|} in
  let src = {|
int main() { int i = 2; return i.Twice(); }
|} in
  let ain = build ~version:(8, 0) [ ("Int.hll", hll); ("base.jaf", src) ] in
  patch ain [ ("Int.hll", hll); ("base.jaf", src) ] ~targets:[ "main" ];
  patch ain
    [ ("Int.hll", "int Twice(int self);"); ("base.jaf", src) ]
    ~targets:[ "main" ];
  [%expect
    {|
    076: FUNC main
    082: PUSHLOCALPAGE
    084: PUSH 0
    090: PUSH 2
    096: ASSIGN
    098: POP
    100: PUSHLOCALPAGE
    102: PUSH 0
    108: CALLHLL library(0), library_function(0)
    118: RETURN
    120: PUSH 0
    126: RETURN
    128: ENDFUNC main
    Int.hll:1:11-19: first parameter must be of type ref int
        1 | int Twice(int self);
                      ^^^^^^^^
    |}]

let%expect_test "ain v8 default arguments" =
  let src =
    {|
int f(int a, int b = 2) { return a + b; }
class C {
public:
    int g(int x = 3);
};
int C::g(int x) { return x; }
int main() { C c; return f(1) + c.g(); }
|}
  in
  let ain = build ~version:(8, 0) [ ("base.jaf", src) ] in
  patch ain
    [ ("base.jaf", src) ]
    ~extras:
      [
        ( "fixes.jaf",
          {|
int f(int a, int b = 5) { return a * b; }
int C::g(int x) { return x * 2; }
|}
        );
      ]
    ~quiet:true;
  CompileTest.print_default_args ain;
  patch ain
    [ ("base.jaf", src) ]
    ~extras:[ ("fixes.jaf", "int f(int a, int b) { return a - b; }") ]
    ~quiet:true;
  CompileTest.print_default_args ain;
  [%expect {|
    f b = 5
    C@g x = 3
    C@g x = 3
    |}]

let%expect_test "ain v1 scenario labels" =
  let src =
    {|
void f() {}
#label() { f(); }
int main() { jump label; return 0; }
|}
  in
  let ain = build ~version:(1, 0) [ ("base.jaf", src) ] in
  patch ain [ ("base.jaf", src) ] ~targets:[ "f" ] ~quiet:true;
  patch ain [ ("base.jaf", src) ] ~targets:[ "label" ];
  patch ain [ ("base.jaf", src) ] ~targets:[ "main" ];
  [%expect
    {|
    base.jaf:3:1-18: Scenario labels cannot be patched in AIN version 1
        3 | #label() { f(); }
            ^^^^^^^^^^^^^^^^^
    base.jaf:4:14-25: Scenario labels cannot be patched in AIN version 1
        4 | int main() { jump label; return 0; }
                         ^^^^^^^^^^^
    |}]

let%expect_test "lambdas are always added" =
  let src =
    {|
delegate int D(int x);
int f() {
    D d = (int x) => int { return x + 1; };
    return d(1);
}
|}
  in
  let ain = build ~version:(6, 10) [ ("base.jaf", src) ] in
  let nr_functions = Ain.nr_functions ain in
  patch ain [ ("base.jaf", src) ] ~targets:[ "f" ] ~quiet:true;
  printf "functions: %d -> %d\n" nr_functions (Ain.nr_functions ain);
  [%expect {| functions: 3 -> 4 |}]

let%expect_test "strings reuse base numbers" =
  let src = {|
string f() { return "hello"; }
|} in
  let ain = build [ ("base.jaf", src) ] in
  let project =
    [ ("base.jaf", {|
string f() { return "hello" + "world"; }
|}) ]
  in
  patch ain project ~targets:[ "f" ];
  [%expect
    {|
    046: FUNC f
    052: S_PUSH "hello"
    058: S_PUSH "world"
    064: S_ADD
    066: RETURN
    068: S_PUSH ""
    074: RETURN
    076: ENDFUNC f
    |}];
  printf "%s\n" (Option.value_exn (Ain.get_string ain 1));
  [%expect {| hello |}]

let%expect_test "patch twice" =
  let ain = base () in
  let fixes =
    {|
int calc(int value) {
    return adjust(value);
}

int adjust(int value) {
    return value * 2;
}
|}
  in
  patch ain
    [ ("base.jaf", base_src) ]
    ~extras:[ ("fixes.jaf", fixes) ]
    ~quiet:true;
  let second = {|
int adjust(int value) {
    return value * 4;
}
|} in
  patch ain [ ("base.jaf", base_src) ] ~extras:[ ("second.jaf", second) ];
  print_function ain "adjust";
  [%expect
    {|
    236: FUNC adjust
    242: SH_LOCALREF value
    248: PUSH 4
    254: MUL
    256: RETURN
    258: PUSH 0
    264: RETURN
    266: ENDFUNC adjust
    6 adjust: address=242 nr_args=1 vars=[int value]
    |}]

let%expect_test "debug information" =
  let debug_info = DebugInfo.create () in
  let ain = build ~debug_info [ ("base.jaf", base_src) ] in
  let project =
    [
      ("base.jaf", edit ~pattern:"return value * 2;" ~with_:"return value * 3;");
    ]
  in
  let fixes = {|
int main() {
    return 0;
}
|} in
  patch ain project ~targets:[ "calc" ]
    ~extras:[ ("fixes.jaf", fixes) ]
    ~debug_info ~quiet:true;
  Stdio.print_endline (Yojson.Basic.to_string (DebugInfo.to_json debug_info));
  let ain = base () in
  patch ain project ~targets:[ "calc" ] ~debug_info;
  [%expect
    {|
    {"version":"alpha-1","sources":["base.jaf","base.jaf","fixes.jaf"],"mappings":[[6,0,5],[50,0,16],[76,0,20],[106,0,24],[172,1,5],[208,2,3]]}
    debug_info.json has mappings past the end of the base AIN code
    |}]

let%expect_test "errors" =
  let ain = base () in
  patch ain [ ("base.jaf", base_src) ] ~targets:[ "nothing" ];
  patch ain [ ("base.jaf", base_src) ] ~targets:[ "Counter::scaled2" ];
  patch ain
    [
      ( "base.jaf",
        base_src ^ "class C { public: const int MAX = 1; void f(); };" );
    ]
    ~targets:[ "C::MAX" ];
  patch ain
    [ ("base.jaf", base_src ^ "class C { public: void f(); };") ]
    ~targets:[ "C::f" ];
  patch (build ~version:(9, 0) []) [] ~globals:true;
  [%expect
    {|
    Unknown patch target: nothing
    Unknown patch target: Counter::scaled2
    Constants cannot be patch targets: C::MAX
    No definition of C::f found
    AIN version 9 is not supported
    |}]

let%expect_test "AIN minor version" =
  let src = {|
int main() { return 0; }
|} in
  let ain = build ~version:(6, 10) [ ("base.jaf", src) ] in
  patch ain [ ("base.jaf", src) ] ~targets:[ "main" ] ~minor_version:0;
  patch ain
    [ ("base.jaf", src) ]
    ~targets:[ "main" ] ~minor_version:20 ~quiet:true;
  printf "%d.%d\n" (Ain.version ain) (Ain.minor_version ain);
  [%expect
    {|
    _AINMINORVERSION 0 is lower than the base AIN version 6.10
    6.20
    |}]
