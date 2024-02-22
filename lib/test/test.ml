open Base
open Sys4cLib

let parse_jaf input =
  let lexbuf = Lexing.from_string input in
  try Parser.jaf Lexer.token lexbuf
  with Lexer.Error | Parser.Error -> CompileError.syntax_error lexbuf

let compile_jaf input =
  let ctx = Jaf.context_from_ain (Ain.create 4 0) in
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
  with CompileError.CompileError e -> CompileError.print_error e

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
    :2:5-12: Undefined type: undef_t
    	in: Unresolved<undef_t> |}]

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

let%expect_test "function call" =
  compile_jaf
    {|
      functype void func(int x);
      void f_int(int x) {}
      void f_float(float x) {}
      void f_ref_int(ref int x) {}
      void f_ref_float(ref float x) {}
      void f_func(func x) {}

      void test() {
        int i;
        ref int ri;
        f_int(3);         // ok
        f_int(3.0);       // ok
        f_int(ri);        // ok
        f_float(3);       // ok
        f_float(3.0);     // ok
        f_float(ri);      // ok
        f_ref_int(NULL);  // ok
        f_ref_int(3);     // error
        f_ref_int(i);     // ok;
        f_ref_int(ri);    // ok
        f_ref_float(3);   // error
        f_ref_float(i);   // error
        f_ref_float(ri);  // error
        f_func(&f_int);   // ok
        f_func(&f_float); // error
        f_func(NULL);     // ok
      }
    |};
  [%expect
    {|
      :19:19-20: not an lvalue: 3
      	in: 3
      :22:21-22: not an lvalue: 3
      	in: 3
      :23:21-22: Type error: expected ref float; got int
      	at: i
      	in: i
      :24:21-23: Type error: expected ref float; got ref int
      	at: ri
      	in: ri
      :26:16-24: Type error: expected func; got ref typeof(f_float)
      	at: &f_float
      	in: &f_float |}]

let%expect_test "return statement" =
  compile_jaf
    {|
      functype void func();
      void f_void() {
        return;    // ok
        return 3;  // error
      }
      int f_int() {
        return;      // error
        return 3;    // ok
        return 3.0;  // ok
        return "s";  // error
      }
      ref int f_ref_int() {
        int i;
        ref int ri;
        ref float rf;
        return NULL;  // ok
        return i;     // ok
        return ri;    // ok
        return rf;    // error
      }
      func f_func() {
        return NULL;     // ok
        return &f_void;  // ok
        return &f_int;   // error
      }
    |};
  [%expect
    {|
      :5:9-18: Type error: expected void; got int
      	at: 3
      	in: return 3;
      :8:9-16: Type error: expected int; got void
      	in: return;
      :11:9-20: Type error: expected int; got string
      	at: "s"
      	in: return "s";
      :20:9-19: Type error: expected ref int; got ref float
      	at: rf
      	in: return rf;
      :25:9-23: Type error: expected func; got ref typeof(f_int)
      	at: &f_int
      	in: return &f_int; |}]

let%expect_test "variable declarations" =
  compile_jaf
    {|
      void f() {
        ref int ri = NULL;       // ok
      }
    |};
  [%expect {| ok |}]

let%expect_test "class declarations" =
  compile_jaf {|
      class C {
        C(void);
        ~C();
      };
    |};
  [%expect {| ok |}]

let%expect_test "RefAssign operator" =
  compile_jaf
    {|
      const int false = 0;
      struct S { int f; ref int rf; };
      ref int ref_val() { return NULL; }
      ref S ref_S() { return NULL; }
      int g_i;
      ref int g_ri;
      void S::f(ref S other) {
        int a = 1, b = 2;
        ref int ra = a;
        S s;
        ra <- ra;         // ok
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
        g_ri <- ra;       // ok
        g_i <- ra;        // error: lhs is not a reference
        false <- NULL;    // error: lhs is not a reference
        undefined <- ra;  // error: undefined is not defined
      }
    |};
  [%expect
    {|
      :14:9-17: Type error: expected ref int; got int
      	at: a
      	in: a <- ra;
      :15:9-20: Type error: expected ref int; got null
      	at: NULL
      	in: NULL <- ra;
      :18:9-23: Type error: expected ref int; got ref S
      	at: ref_S()
      	in: ra <- ref_S();
      :19:9-17: not an lvalue: 3
      	in: ra <- 3;
      :20:9-25: Type error: expected ref int; got ref int
      	at: ref_val()
      	in: ref_val() <- ra;
      :22:9-19: Type error: expected ref int; got int
      	at: s.f
      	in: s.f <- ra;
      :24:9-23: Type error: expected ref S; got S
      	at: this
      	in: this <- other;
      :26:9-19: Type error: expected ref int; got int
      	at: g_i
      	in: g_i <- ra;
      :27:9-23: Type error: expected ref null; got int
      	at: false
      	in: false <- NULL;
      :28:9-18: Undefined variable: undefined |}]

let%expect_test "RefEqual operator" =
  compile_jaf
    {|
      const int false = 0;
      struct S { int f; ref int rf; };
      ref int ref_int() { return NULL; }
      ref S ref_S() { return NULL; }
      int g_i;
      ref int g_ri;
      void S::f(ref S other) {
        int a = 1, b = 2;
        ref int ra = a;
        S s;
        ra === ra;         // ok
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
        ref_S() === NULL;  // ok
        g_ri === ra;       // ok
        g_i === ra;        // error: lhs is not a reference
        false === NULL;    // error: lhs is not a reference
        undefined === ra;  // error: undefined is not defined
      }
    |};
  [%expect
    {|
      :14:9-17: Type error: expected ref int; got int
      	at: a
      	in: a === ra
      :15:9-20: not an lvalue: NULL
      	in: NULL === ra
      :18:9-23: Type error: expected ref int; got ref S
      	at: ref_S()
      	in: ra === ref_S()
      :19:9-23: Type error: expected ref S; got ref int
      	at: ra
      	in: ref_S() === ra
      :20:9-17: not an lvalue: 3
      	in: ra === 3
      :23:9-19: Type error: expected ref int; got int
      	at: s.f
      	in: s.f === ra
      :25:9-23: not an lvalue: this
      	in: this === other
      :29:9-19: Type error: expected ref int; got int
      	at: g_i
      	in: g_i === ra
      :30:9-23: Type error: expected ref null; got int
      	at: false
      	in: false === NULL
      :31:9-18: Undefined variable: undefined |}]

let%expect_test "label_is_a_statement" =
  compile_jaf
    {|
      void f() {
        switch (1) {
          case 1:
          default:
        }
        if (1)
          label1:
        else
          label2:
      }
    |};
  [%expect {| ok |}]
