(* Copyright (C) 2024 kichikuou <KichikuouChrome@gmail.com>
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
open Compiler

let type_test input =
  let ctx = Jaf.context_from_ain (Ain.create 4 0) in
  let debug_info = DebugInfo.create () in
  try
    Compile.compile ctx [ Pje.Jaf "-" ] debug_info (fun _ -> input);
    Stdio.print_endline "ok"
  with CompileError.Compile_error e ->
    CompileError.print_error e (fun _ -> Some input)

let%expect_test "empty jaf" =
  type_test {||};
  [%expect {| ok |}]

let%expect_test "empty function" =
  type_test {|
    void f() {}
  |};
  [%expect {| ok |}]

let%expect_test "syntax error" =
  type_test {|
    int c = ;
  |};
  [%expect
    {|
    -:2:13-14: Syntax error
        2 |     int c = ;
                        ^ |}]

let%expect_test "undefined variable" =
  type_test {|
    int c = foo;
  |};
  [%expect
    {|
    -:2:13-16: Undefined variable: foo
        2 |     int c = foo;
                        ^^^ |}]

let%expect_test "multiline error" =
  type_test {|
      void f(int x) {
        f(3,
          4);
      }
    |};
  [%expect
    {|
    -:3:9-4:13: Wrong number of arguments to function f (expected 1; got 2)
        3 |         f(3,
        4 |           4); |}]

let%expect_test "not lvalue error" =
  type_test {|
    ref int c = 3;
  |};
  [%expect
    {|
    -:2:13-18: Not an lvalue: 3
        2 |     ref int c = 3;
                        ^^^^^ |}]

let%expect_test "undefined type error" =
  type_test {|
    undef_t c;
  |};
  [%expect
    {|
    -:2:5-12: Undefined type: undef_t
        2 |     undef_t c;
                ^^^^^^^ |}]

let%expect_test "type error" =
  type_test {|
    void f() {
      int x = "s";
      return 1;
    }
  |};
  [%expect
    {|
      -:3:15-18: Type error: expected int; got string
          3 |       int x = "s";
                            ^^^
      -:4:14-15: Type error: expected void; got int
          4 |       return 1;
                           ^ |}]

let%expect_test "uninitialized constant" =
  type_test {|
    const int c;    // ok
    const string s; // error
  |};
  [%expect
    {|
      -:3:18-19: Const variable lacks initializer
          3 |     const string s; // error
                               ^
    |}]

let%expect_test "function call" =
  type_test
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
    -:19:19-20: Not an lvalue: 3
       19 |         f_ref_int(3);     // error
                              ^
    -:22:21-22: Not an lvalue: 3
       22 |         f_ref_float(3);   // error
                                ^
    -:23:21-22: Type error: expected ref float; got int
       23 |         f_ref_float(i);   // error
                                ^
    -:24:21-23: Type error: expected ref float; got ref int
       24 |         f_ref_float(ri);  // error
                                ^^
    -:26:16-24: Type error: expected func; got void(float)
       26 |         f_func(&f_float); // error
                           ^^^^^^^^
    |}]

let%expect_test "default parameter" =
  type_test
    {|
      int g;
      void f(int required, int optional = 0) {}
      void err(int x = "") {}
      void test() {
        f();  // arity error
        f(3);
        f(1, 2);
        f(3,);
        f(, 2);  // missing argument
        f(1, 2, 3);  // arity error
        f(1, 2,);  // arity error
        array@int a1;
        array@int@2 a2;
        a1.Numof();  // ok
        a2.Numof();  // arity error
      }
    |};
  [%expect
    {|
      -:4:24-26: Type error: expected int; got string
          4 |       void err(int x = "") {}
                                     ^^
      -:6:9-12: Wrong number of arguments to function f (expected 2; got 0)
          6 |         f();  // arity error
                      ^^^
      -:10:9-15: Missing argument #0
         10 |         f(, 2);  // missing argument
                      ^^^^^^
      -:11:9-19: Wrong number of arguments to function f (expected 2; got 3)
         11 |         f(1, 2, 3);  // arity error
                      ^^^^^^^^^^
      -:12:9-17: Wrong number of arguments to function f (expected 2; got 3)
         12 |         f(1, 2,);  // arity error
                      ^^^^^^^^
      -:16:9-19: Wrong number of arguments to function Numof (expected 1; got 0)
         16 |         a2.Numof();  // arity error
                      ^^^^^^^^^^ |}]

let%expect_test "non-constant default parameter" =
  type_test
    {|
      int g;
      class C {
        void f(int x = g);
      };
      void C::f(int x) {}
    |};
  [%expect
    {|
    -:4:16-25: Value of const variable is not constant
        4 |         void f(int x = g);
                           ^^^^^^^^^ |}]

let%expect_test "return statement" =
  type_test
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
    -:5:16-17: Type error: expected void; got int
        5 |         return 3;  // error
                           ^
    -:8:9-16: Type error: expected int; got void
        8 |         return;      // error
                    ^^^^^^^
    -:11:16-19: Type error: expected int; got string
       11 |         return "s";  // error
                           ^^^
    -:20:16-18: Type error: expected ref int; got ref float
       20 |         return rf;    // error
                           ^^
    -:25:16-22: Type error: expected func; got int()
       25 |         return &f_int;   // error
                           ^^^^^^
    |}]

let%expect_test "variable declarations" =
  type_test
    {|
      void f() {
        ref int ri = NULL;       // ok
      }
    |};
  [%expect {| ok |}]

let%expect_test "class declarations" =
  type_test
    {|
      class C {
        C(void);
        ~C();
      };
      C::C(void) {}
      C::~C() {}
    |};
  [%expect {| ok |}]

let%expect_test "undefined method" =
  type_test {|
      class C {
        int f();
      };
    |};
  [%expect
    {|
    -:3:9-17: No definition of C::f found
        3 |         int f();
                    ^^^^^^^^ |}]

let%expect_test "private members" =
  type_test
    {|
      class C {
        int priv_func() {}
        int priv_memb;
      public:
        int pub_func() {}
        int pub_memb;
      };
      void test() {
        C c;
        c.pub_func();
        c.priv_func();  // error
        c.pub_memb;
        c.priv_memb;    // error
      }
    |};
  [%expect
    {|
    -:12:9-20: C::priv_func is not public
       12 |         c.priv_func();  // error
                    ^^^^^^^^^^^
    -:14:9-20: C::priv_memb is not public
       14 |         c.priv_memb;    // error
                    ^^^^^^^^^^^ |}]

let%expect_test "Member access for temporary object" =
  type_test
    {|
      class C {
      public:
        int n;
        void f() {}
      };
      C get_C() { C c; return c; }
      void test() {
        get_C().n;
        get_C().f();
      }
    |};
  [%expect
    {|
      -:9:9-18: Member access not allowed for temporary object
          9 |         get_C().n;
                      ^^^^^^^^^
      -:10:9-18: Member access not allowed for temporary object
         10 |         get_C().f();
                      ^^^^^^^^^ |}]

let%expect_test "RefAssign operator" =
  type_test
    {|
      const int false = 0;
      struct S {
        int f;
        ref int rf;
        void f(ref S other);
      };
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
        ref S rs = new S; // ok
      }
    |};
  [%expect
    {|
      -:18:9-10: Type error: expected ref int; got int
         18 |         a <- ra;          // error: lhs is not a reference
                      ^
      -:19:9-13: Type error: expected ref int; got null
         19 |         NULL <- ra;       // error: lhs can't be the NULL keyword
                      ^^^^
      -:22:15-22: Type error: expected ref int; got ref S
         22 |         ra <- ref_S();    // error: referenced type mismatch
                            ^^^^^^^
      -:23:9-17: Not an lvalue: 3
         23 |         ra <- 3;          // error: rhs is not a lvalue
                      ^^^^^^^^
      -:24:9-18: Type error: expected ref int; got ref int
         24 |         ref_val() <- ra;  // error: lhs is not a variable
                      ^^^^^^^^^
      -:26:9-12: Type error: expected ref int; got int
         26 |         s.f <- ra;        // error: lhs is not a reference
                      ^^^
      -:28:9-13: Type error: expected ref S; got S
         28 |         this <- other;    // error: lhs is not a reference
                      ^^^^
      -:30:9-12: Type error: expected ref int; got int
         30 |         g_i <- ra;        // error: lhs is not a reference
                      ^^^
      -:31:9-14: Type error: expected ref null; got int
         31 |         false <- NULL;    // error: lhs is not a reference
                      ^^^^^
      -:32:9-18: Undefined variable: undefined
         32 |         undefined <- ra;  // error: undefined is not defined
                      ^^^^^^^^^ |}]

let%expect_test "RefEqual operator" =
  type_test
    {|
      const int false = 0;
      struct S {
        int f;
        ref int rf;
        void f(ref S other);
      };
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
      -:18:9-10: Type error: expected ref int; got int
         18 |         a === ra;          // error: lhs is not a reference
                      ^
      -:19:9-20: Not an lvalue: NULL
         19 |         NULL === ra;       // error: lhs can't be the NULL keyword
                      ^^^^^^^^^^^
      -:22:16-23: Type error: expected ref int; got ref S
         22 |         ra === ref_S();    // error: referenced type mismatch
                             ^^^^^^^
      -:23:21-23: Type error: expected ref S; got ref int
         23 |         ref_S() === ra;    // error: referenced type mismatch
                                  ^^
      -:24:9-17: Not an lvalue: 3
         24 |         ra === 3;          // error: rhs is not a lvalue
                      ^^^^^^^^
      -:27:9-12: Type error: expected ref int; got int
         27 |         s.f === ra;        // error: lhs is not a reference
                      ^^^
      -:29:9-23: Not an lvalue: this
         29 |         this === other;    // error: lhs is not a reference
                      ^^^^^^^^^^^^^^
      -:33:9-12: Type error: expected ref int; got int
         33 |         g_i === ra;        // error: lhs is not a reference
                      ^^^
      -:34:9-14: Type error: expected ref null; got int
         34 |         false === NULL;    // error: lhs is not a reference
                      ^^^^^
      -:35:9-18: Undefined variable: undefined
         35 |         undefined === ra;  // error: undefined is not defined
                      ^^^^^^^^^ |}]

let%expect_test "implicit dereference" =
  type_test
    {|
      int f() {
        ref int r;
        for (r = 10; r; r--) {
          switch (r) {
            case 1:
              r + r || r;
          }
        }
        return r;
      }
    |};
  [%expect {| ok |}]

let%expect_test "label_is_a_statement" =
  type_test
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

let%expect_test "jump statement" =
  type_test
    {|
      void f() {
        jump sf;  // ok
        jump f;   // error : f is not a scenario function
        jumps sf; // error: jumps expects a string
      }
      #sf() {
        return;   // error: return from a scenario function
      }
    |};
  [%expect
    {|
    -:4:9-16: f is not a scenario function
        4 |         jump f;   // error : f is not a scenario function
                    ^^^^^^^
    -:5:15-17: Type error: expected string; got void()
        5 |         jumps sf; // error: jumps expects a string
                          ^^
    -:8:9-16: cannot return from scenario function
        8 |         return;   // error: return from a scenario function
                    ^^^^^^^
    |}]

let%expect_test "functype assignment" =
  type_test
    {|
      functype void ft(void);
      functype void ft2(void);
      functype void ft3(int);
      void f(ft f) {
        ft2 f2 = f;  // ok
        ft3 f3 = f;  // error
      }
    |};
  [%expect
    {|
      -:7:18-19: Type error: expected ft3; got ft
          7 |         ft3 f3 = f;  // error
                               ^ |}]

let%expect_test "boolean ops" =
  type_test
    {|
      void f(bool b1, bool b2) {
        b1 = b2;         // ok
        b1 == b2;        // ok
        b1 != b2;        // ok
        b1 + b2;         // error
        b1 || b2 && b1;  // ok
        b1 & b2 ^ b1;    // ok
        b1 < b2;         // error
      }
    |};
  [%expect
    {|
      -:6:9-16: invalid operation on boolean type
          6 |         b1 + b2;         // error
                      ^^^^^^^
      -:9:9-16: invalid operation on boolean type
          9 |         b1 < b2;         // error
                      ^^^^^^^ |}]

let%expect_test "method declaration mismatch" =
  type_test
    {|
      class C {
        void f(int x);
      };
      void C::f() {}
    |};
  [%expect
    {|
      -:5:7-21: Function signature mismatch
          5 |       void C::f() {}
                    ^^^^^^^^^^^^^^ |}]

let%expect_test "duplicated function definition" =
  type_test
    {|
      class C {
        void f() {}
      };
      void C::f() {}
    |};
  [%expect
    {|
      -:5:7-21: Duplicate function definition
          5 |       void C::f() {}
                    ^^^^^^^^^^^^^^ |}]

let%expect_test "undeclared method" =
  type_test {|
      class C {};
      void C::f() {}
    |};
  [%expect
    {|
      -:3:7-21: f is not declared in class C
          3 |       void C::f() {}
                    ^^^^^^^^^^^^^^ |}]

let%expect_test "wrong constructor name" =
  type_test {|
      class C {
        X();
      };
    |};
  [%expect
    {|
      -:3:9-13: constructor name doesn't match struct name
          3 |         X();
                      ^^^^ |}]

let%expect_test "forbidden array expressions" =
  type_test
    {|
      void f(ref array@int ra) {
        array@int a;
        a;
        for (;; a) {}
        ra, 1;
      }
    |};
  [%expect
    {|
    -:4:9-10: array expression not allowed here
        4 |         a;
                    ^
    -:5:17-18: array expression not allowed here
        5 |         for (;; a) {}
                            ^
    -:6:9-11: array expression not allowed here
        6 |         ra, 1;
                    ^^
    |}]

let%expect_test "Array.Sort() callback" =
  type_test
    {|
      struct S {};
      int int_compare(int a, int b) { return 0; }
      int S_compare(ref S a, ref S b) { return 0; }
      void f() {
        array@int ai;
        ai.Sort();  // ok
        ai.Sort(&int_compare);  // ok
        ai.Sort(&S_compare);  // error
        array@S as;
        as.Sort();  // error
        as.Sort(&S_compare);  // ok
        as.Sort(&int_compare);  // error
        array@bool ab;
        ab.Sort();  // error
      }
    |};
  [%expect
    {|
    -:9:17-27: Type error: expected int(int, int); got int(ref S, ref S)
        9 |         ai.Sort(&S_compare);  // error
                            ^^^^^^^^^^
    -:11:9-18: Wrong number of arguments to function Sort (expected 1; got 0)
       11 |         as.Sort();  // error
                    ^^^^^^^^^
    -:13:17-29: Type error: expected int(ref S, ref S); got int(int, int)
       13 |         as.Sort(&int_compare);  // error
                            ^^^^^^^^^^^^
    -:15:9-18: Sort() is not supported for array@bool
       15 |         ab.Sort();  // error
                    ^^^^^^^^^
    |}]

let%expect_test "Array.SortBy()" =
  type_test
    {|
      struct S {
        int i;
        lint li;
        string s;
        ref S rs;
      };
      struct T {
        int i;
      };
      void f() {
        array@S a;
        a.SortBy(&S::i);  // ok
        a.SortBy(&S::li);  // ok
        a.SortBy(&S::s);  // ok
        a.SortBy(&S::rs);  // error
        a.SortBy(&T::i);  // error
        array@int ai;
        ai.SortBy(&S::i);  // error
      }
    |};
  [%expect
    {|
    -:16:18-24: Type error: expected S::(int | string); got S::ref S
       16 |         a.SortBy(&S::rs);  // error
                             ^^^^^^
    -:17:18-23: Type error: expected S::(int | string); got T::int
       17 |         a.SortBy(&T::i);  // error
                             ^^^^^
    -:19:9-25: SortBy() is not supported for array@int
       19 |         ai.SortBy(&S::i);  // error
                    ^^^^^^^^^^^^^^^^
    |}]

let%expect_test "switch type error" =
  type_test
    {|
      void f() {
        switch (1) {
          case "a":
            break;
        }
      }
    |};
  [%expect
    {|
      -:4:11-20: string case in int switch
          4 |           case "a":
                        ^^^^^^^^^ |}]

let%expect_test "stray case" =
  type_test
    {|
      void f() {
        switch (1) {
          if (1) {
            case 1:  // this is OK
              break;
          }
        }
        case 2:
      }
    |};
  [%expect
    {|
    -:9:9-16: switch case outside of switch statement
        9 |         case 2:
                    ^^^^^^^ |}]
