open Base
open Sys4cLib

let parse_jaf input =
  let lexbuf = Lexing.from_string input in
  try Parser.jaf Lexer.token lexbuf
  with Lexer.Error | Parser.Error -> CompileError.syntax_error lexbuf

let compile_jaf input =
  let ctx = Jaf.{ ain = Ain.create 4 0; const_vars = [] } in
  try
    let jaf = parse_jaf input in
    Declarations.register_type_declarations ctx jaf;
    Declarations.resolve_types ctx jaf false;
    Declarations.define_types ctx jaf;
    TypeAnalysis.check_types ctx jaf;
    ConstEval.evaluate_constant_expressions ctx jaf;
    VariableAlloc.allocate_variables ctx jaf;
    SanityCheck.check_invariants ctx jaf;
    Compiler.compile ctx jaf;
    Stdio.print_endline "ok"
  with e -> CompileError.print_error e

let%expect_test "empty jaf" =
  compile_jaf {||};
  [%expect {| ok |}]

let%expect_test "empty function" =
  compile_jaf {|
    void f() {}
  |};
  [%expect {| ok |}]

let%expect_test "syntax error" =
  compile_jaf {|
    int c = ;
  |};
  [%expect {| :2:13-14: Syntax error |}]

let%expect_test "undefined variable" =
  compile_jaf {|
    int c = foo;
  |};
  [%expect {| :2:13-16: Undefined variable: foo |}]

let%expect_test "arity error" =
  compile_jaf {|
    int c = system.Exit();
  |};
  [%expect
    {|
      :2:13-26: wrong number of arguments to function Exit (expected 1; got 0)
      	in: system.Exit() |}]

let%expect_test "not lvalue error" =
  compile_jaf {|
    ref int c = 3;
  |};
  [%expect {|
    :2:13-18: not an lvalue: 3
    	in: ref int c = 3; |}]

let%expect_test "undefined type error" =
  compile_jaf {|
    undef_t c;
  |};
  [%expect
    {|
    :2:13-14: Undefined type: undef_t
    	in: Unresolved<undef_t> c; |}]

let%expect_test "type error" =
  compile_jaf {|
    void f() {
      int x = "s";
      return 1;
    }
  |};
  [%expect
    {|
      :3:11-18: Type error: expected int; got string
      	at: "s"
      	in: int x = "s";
      :4:7-16: Type error: expected void; got int
      	at: 1
      	in: return 1; |}]
