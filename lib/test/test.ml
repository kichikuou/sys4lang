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

let%expect_test "RefAssign operator" =
  compile_jaf
    {|
      struct S { int f; ref int rf; };
      ref int ref_val() { return NULL; }
      ref S ref_S() { return NULL; }
      void S::f(ref S other) {
        int a = 1, b = 2;
        ref int ra = a, rb = b;
        S s;
        ra <- rb;         // ok
        ra <- a;          // ok
        a <- ra;          // error: lhs is not a reference
        NULL <- ra;       // error: lhs can't be the NULL keyword
        ra <- NULL;       // ok
        ra <- ref_val();  // ok
        ra <- ref_S();    // error: referenced type mismatch
        ra <- 3;          // error: rhs is not a lvalue
        ref_val() <- ra;  // error: lhs is not a variable
        s.rf <- ra;       // ok
        s.f <- ra;        // error: lhs is not a reference
        other <- this;    // ok
        this <- other;    // error: lhs is not a reference
      }
    |};
  [%expect
    {|
      :11:9-17: Type error: expected ref int; got int
      	at: a
      	in: a <- ra;
      :12:9-20: Type error: expected ref int; got null
      	at: NULL
      	in: NULL <- ra;
      :15:9-23: Type error: expected int; got ref
      	at: ref_S()
      	in: ra <- ref_S();
      :16:9-17: not an lvalue: 3
      	in: ra <- 3;
      :17:9-25: Type error: expected ref int; got ref int
      	at: ref_val()
      	in: ref_val() <- ra;
      :19:9-19: Type error: expected ref int; got int
      	at: s.f
      	in: s.f <- ra;
      :21:9-23: Type error: expected ref S; got
      	at: this
      	in: this <- other; |}]

let%expect_test "RefEqual operator" =
  compile_jaf
    {|
      struct S { int f; ref int rf; };
      ref int ref_int() { return NULL; }
      ref S ref_S() { return NULL; }
      void S::f(ref S other) {
        int a = 1, b = 2;
        ref int ra = a, rb = b;
        S s;
        ra === rb;         // ok
        ra === a;          // ok
        a === ra;          // error: lhs is not a reference
        NULL === ra;       // error: lhs can't be the NULL keyword
        ra === NULL;       // ok
        ra === ref_int();  // ok
        ra === ref_S();    // error: referenced type mismatch
        ref_S() === ra;    // error: referenced type mismatch
        ra === 3;          // error: rhs is not a lvalue
        ref_int() === ra;  // ok
        s.rf === ra;       // ok
        s.f === ra;        // error: lhs is not a reference
        other === this;    // ok
        this === other;    // error: lhs is not a reference
        ref_S() === this;  // ok
      }
    |};
  [%expect
    {|
      :11:9-17: Type error: expected ref int; got int
      	at: a
      	in: a === ra
      :12:9-20: Type error: expected null; got ref int
      	at: ra
      	in: NULL === ra
      :15:9-23: Type error: expected int; got ref
      	at: ref_S()
      	in: ra === ref_S()
      :16:9-23: Type error: expected ref ; got ref int
      	at: ra
      	in: ref_S() === ra
      :17:9-17: not an lvalue: 3
      	in: ra === 3
      :20:9-19: Type error: expected ref int; got int
      	at: s.f
      	in: s.f === ra
      :22:9-23: not an lvalue: this
      	in: this === other |}]
