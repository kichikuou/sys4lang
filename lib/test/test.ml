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

let%expect_test "empty function" =
  compile_jaf {|
    void f() {}
  |};
  [%expect {| ok |}]

let%expect_test "syntax error" =
  compile_jaf {|int c = ;|};
  [%expect {| :1:9-10: Syntax error |}]

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
