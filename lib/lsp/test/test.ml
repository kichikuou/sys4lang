open Base
open Common
open System4_lsp

let analyze source =
  let doc =
    Document.create
      (Jaf.context_from_ain (Ain.create 4 0))
      ~fname:"test.jaf" source
  in
  if List.is_empty doc.errors then Stdio.print_endline "ok"
  else
    List.iter doc.errors ~f:(fun (range, message) ->
        Stdio.printf "(%d, %d) - (%d, %d) %s\n" range.start.line
          range.start.character range.end_.line range.end_.character message)

let%expect_test "empty doc" =
  analyze {||};
  [%expect {| ok |}]

let%expect_test "empty function" =
  analyze {|
    void f() {}
  |};
  [%expect {| ok |}]

let%expect_test "syntax error" =
  analyze {|
    int c = ;
  |};
  [%expect {| (1, 12) - (1, 13) Syntax error. |}]

let%expect_test "undefined variable" =
  analyze {|
    int c = foo;
  |};
  [%expect {| (1, 12) - (1, 15) Undefined variable: foo |}]

let%expect_test "arity error" =
  analyze {|
    int c = system.Exit();
  |};
  [%expect
    {| (1, 12) - (1, 25) Wrong number of arguments to function Exit (expected 1; got 0) |}]

let%expect_test "not lvalue error" =
  analyze {|
    ref int c = 3;
  |};
  [%expect {| (1, 12) - (1, 17) Not an lvalue: 3 |}]

let%expect_test "undefined type error" =
  analyze {|
    undef_t c;
  |};
  [%expect {| (1, 4) - (1, 11) Undefined type: undef_t |}]

let%expect_test "type error" =
  analyze {|
    void f() { int x = "s"; }
  |};
  [%expect {| (1, 23) - (1, 26) Type error: expected int; got string |}]

let%expect_test "function call" =
  analyze
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
    (18, 18) - (18, 19) Not an lvalue: 3
    (21, 20) - (21, 21) Not an lvalue: 3
    (22, 20) - (22, 21) Type error: expected ref float; got int
    (23, 20) - (23, 22) Type error: expected ref float; got ref int
    (25, 15) - (25, 23) Type error: expected func; got void(float)
    |}]

let%expect_test "return statement" =
  analyze
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
    (4, 15) - (4, 16) Type error: expected void; got int
    (7, 8) - (7, 15) Type error: expected int; got void
    (10, 15) - (10, 18) Type error: expected int; got string
    (19, 15) - (19, 17) Type error: expected ref int; got ref float
    (24, 15) - (24, 21) Type error: expected func; got int()
    |}]

let%expect_test "variable declarations" =
  analyze {|
      ref int ri = NULL;       // ok
    |};
  [%expect {| ok |}]

let%expect_test "class declarations" =
  analyze {|
      class C {
        C(void);
        ~C();
      };
    |};
  [%expect {| ok |}]

let%expect_test "RefAssign operator" =
  analyze
    {|
      struct S { int i; ref int ri; void f(ref S other); };
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
        s.ri <- ra;       // ok
        s.i <- ra;        // error: lhs is not a reference
        other <- this;    // ok
        this <- other;    // error: lhs is not a reference
        g_ri <- ra;       // ok
        g_i <- ra;        // error: lhs is not a reference
        3 <- NULL;    // error: lhs is not a reference
        undefined <- ra;  // error: undefined is not defined
      }
    |};
  [%expect
    {|
    (12, 8) - (12, 9) Type error: expected ref int; got int
    (13, 8) - (13, 12) Type error: expected ref int; got null
    (16, 14) - (16, 21) Type error: expected ref int; got ref S
    (17, 8) - (17, 16) Not an lvalue: 3
    (18, 8) - (18, 17) Type error: expected ref int; got ref int
    (20, 8) - (20, 11) Type error: expected ref int; got int
    (22, 8) - (22, 12) Type error: expected ref S; got S
    (24, 8) - (24, 11) Type error: expected ref int; got int
    (25, 8) - (25, 9) Type error: expected ref null; got int
    (26, 8) - (26, 17) Undefined variable: undefined
    |}]

let%expect_test "RefEqual operator" =
  analyze
    {|
      struct S { int i; ref int ri; void f(ref S other); };
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
        s.ri === ra;       // ok
        s.i === ra;        // error: lhs is not a reference
        other === this;    // ok
        this === other;    // error: lhs is not a reference
        ref_S() === this;  // ok
        ref_S() === NULL;  // ok
        g_ri === ra;       // ok
        g_i === ra;        // error: lhs is not a reference
        3 === NULL;    // error: lhs is not a reference
        undefined === ra;  // error: undefined is not defined
      }
    |};
  [%expect
    {|
    (12, 8) - (12, 9) Type error: expected ref int; got int
    (13, 8) - (13, 19) Not an lvalue: NULL
    (16, 15) - (16, 22) Type error: expected ref int; got ref S
    (17, 20) - (17, 22) Type error: expected ref S; got ref int
    (18, 8) - (18, 16) Not an lvalue: 3
    (21, 8) - (21, 11) Type error: expected ref int; got int
    (23, 8) - (23, 22) Not an lvalue: this
    (27, 8) - (27, 11) Type error: expected ref int; got int
    (28, 8) - (28, 18) Not an lvalue: 3
    (29, 8) - (29, 17) Undefined variable: undefined
    |}]

let%expect_test "label_is_a_statement" =
  analyze
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
