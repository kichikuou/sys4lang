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

open Base
open Sys4cLib

let sprintf = Printf.sprintf

let arg_to_string dasm ain (argtype : Bytecode.argtype) arg =
  match argtype with
  | Int -> Int32.to_string arg
  | Float -> Int32.float_of_bits arg |> Float.to_string
  | Address -> Int32.to_string arg
  | Function -> (Ain.get_function_by_index ain (Int32.to_int_exn arg)).name
  | String ->
      sprintf "\"%s\""
        (Ain.get_string ain (Int32.to_int_exn arg) |> Option.value_exn)
  | Message ->
      sprintf "\'%s\'"
        (Ain.get_message ain (Int32.to_int_exn arg) |> Option.value_exn)
  | Local ->
      let f =
        Ain.get_function_by_index ain
          (Option.value_exn (Dasm.current_func dasm))
      in
      (List.nth_exn f.vars (Int32.to_int_exn arg)).name
  | Global -> sprintf "global(%ld)" arg
  | Struct -> sprintf "struct(%ld)" arg
  | Syscall ->
      Bytecode.string_of_syscall
        (Bytecode.syscall_of_int (Int32.to_int_exn arg))
  | Library -> sprintf "library(%ld)" arg
  | LibraryFunction -> sprintf "library_function(%ld)" arg
  | File -> Ain.get_file ain (Int32.to_int_exn arg) |> Option.value_exn
  | Delegate -> sprintf "delegate(%ld)" arg
  | Switch -> sprintf "switch(%ld)" arg

let print_disassemble ain =
  let dasm = Dasm.create ain in
  while not (Dasm.eof dasm) do
    let opcode = Bytecode.opcode_of_int (Dasm.opcode dasm) in
    let argtypes = Dasm.argument_types dasm in
    let args = Dasm.arguments dasm in
    Stdio.printf "%03d: %s %s\n" (Dasm.addr dasm)
      (Bytecode.string_of_opcode opcode)
      (String.concat ~sep:", "
         (List.map2_exn ~f:(arg_to_string dasm ain) argtypes args));
    Dasm.next dasm
  done

let compile_test input =
  let ctx = Jaf.context_from_ain (Ain.create 4 0) in
  let debug_info = DebugInfo.create () in
  try
    Compiler.compile ctx [ Pje.Jaf "test.jaf" ] debug_info (fun _ -> input);
    print_disassemble ctx.ain
  with CompileError.Compile_error e ->
    CompileError.print_error e (fun _ -> Some input)

let%expect_test "empty function" =
  compile_test {|
    void f() {}
  |};
  [%expect
    {|
      000: FUNC f
      006: RETURN
      008: ENDFUNC f
      014: EOF test.jaf
      020: FUNC NULL
      026: EOF
    |}]

let%expect_test "return" =
  compile_test {|
    int f() {
      return 42;
    }
  |};
  [%expect
    {|
      000: FUNC f
      006: PUSH 42
      012: RETURN
      014: PUSH 0
      020: RETURN
      022: ENDFUNC f
      028: EOF test.jaf
      034: FUNC NULL
      040: EOF
    |}]

let%expect_test "lint inc" =
  compile_test {|
    void f() {
      lint i;
      i++;
    }
  |};
  [%expect
    {|
      000: FUNC f
      006: SH_LOCALASSIGN i, 0
      016: PUSHLOCALPAGE
      018: PUSH 0
      024: DUP2
      026: REF
      028: DUP_X2
      030: POP
      032: LI_INC
      034: POP
      036: RETURN
      038: ENDFUNC f
      044: EOF test.jaf
      050: FUNC NULL
      056: EOF |}]

let%expect_test "compare lint and int" =
  compile_test {|
    void f(lint a) {
      a == 0;
      1 < a;
    }
  |};
  [%expect
    {|
      000: FUNC f
      006: SH_LOCALREF a
      012: PUSH 0
      018: EQUALE
      020: POP
      022: PUSH 1
      028: SH_LOCALREF a
      034: LT
      036: POP
      038: RETURN
      040: ENDFUNC f
      046: EOF test.jaf
      052: FUNC NULL
      058: EOF
    |}]

let%expect_test "local ref int" =
  compile_test {|
    void f() {
      ref int r;
    }
  |};
  [%expect
    {|
      000: FUNC f
      006: CALLSYS LockPeek
      012: POP
      014: PUSHLOCALPAGE
      016: PUSH 0
      022: DUP2
      024: REFREF
      026: POP
      028: DELETE
      030: PUSH -1
      036: PUSH 0
      042: R_ASSIGN
      044: POP
      046: POP
      048: CALLSYS UnlockPeek
      054: POP
      056: RETURN
      058: ENDFUNC f
      064: EOF test.jaf
      070: FUNC NULL
      076: EOF
    |}]

let%expect_test "local ref string" =
  compile_test {|
    void f() {
      ref string r;
    }
  |};
  [%expect
    {|
      000: FUNC f
      006: CALLSYS LockPeek
      012: POP
      014: PUSHLOCALPAGE
      016: PUSH 0
      022: DUP2
      024: REF
      026: DELETE
      028: PUSH -1
      034: ASSIGN
      036: POP
      038: CALLSYS UnlockPeek
      044: POP
      046: RETURN
      048: ENDFUNC f
      054: EOF test.jaf
      060: FUNC NULL
      066: EOF
  |}]

let%expect_test "jump statement" =
  compile_test
    {|
    #sfunc(void) {
      jumps "foo";
      jump sfunc;
    }
  |};
  [%expect
    {|
      000: FUNC sfunc
      006: S_PUSH "foo"
      012: CALLONJUMP
      014: SJUMP
      016: S_PUSH "sfunc"
      022: CALLONJUMP
      024: SJUMP
      026: ENDFUNC sfunc
      032: EOF test.jaf
      038: FUNC NULL
      044: EOF
  |}]

let%expect_test "new" =
  compile_test {|
      struct S {};
      ref S f(int i) { return new S; }
  |};
  [%expect
    {|
      000: FUNC f
      006: PUSHLOCALPAGE
      008: PUSH 1
      014: PUSH 0
      020: CALLSYS LockPeek
      026: POP
      028: NEW
      030: ASSIGN
      032: CALLSYS UnlockPeek
      038: POP
      040: DUP
      042: SP_INC
      044: RETURN
      046: PUSH -1
      052: RETURN
      054: ENDFUNC f
      060: EOF test.jaf
      066: FUNC NULL
      072: EOF
  |}]

let%expect_test "function returning ref" =
  compile_test {|
      struct S {};
      ref S f() { return f(); }
  |};
  [%expect
    {|
      000: FUNC f
      006: PUSHLOCALPAGE
      008: PUSH 0
      014: CALLFUNC f
      020: ASSIGN
      022: DUP
      024: SP_INC
      026: RETURN
      028: PUSH -1
      034: RETURN
      036: ENDFUNC f
      042: EOF test.jaf
      048: FUNC NULL
      054: EOF
  |}]

let%expect_test "bool ? ref int : int" =
  compile_test
    {|
      int f(int a, ref int ra) {
        return a == 0 ? ra : a;
      }
  |};
  [%expect
    {|
      000: FUNC f
      006: SH_LOCALREF a
      012: PUSH 0
      018: EQUALE
      020: IFZ 44
      026: PUSHLOCALPAGE
      028: PUSH 1
      034: REFREF
      036: REF
      038: JUMP 50
      044: SH_LOCALREF a
      050: RETURN
      052: PUSH 0
      058: RETURN
      060: ENDFUNC f
      066: EOF test.jaf
      072: FUNC NULL
      078: EOF
    |}]

let%expect_test "assign this" =
  compile_test
    {|
      struct S {
        void f();
      };

      void S::f() {
        S s2;
        s2 = this;
      }
    |};
  [%expect
    {|
      000: FUNC S@f
      006: SH_LOCALDELETE s2
      012: SH_LOCALCREATE s2, struct(0)
      022: SH_LOCALREF s2
      028: PUSHSTRUCTPAGE
      030: SR_REF2 struct(0)
      036: PUSH 0
      042: SR_ASSIGN
      044: SR_POP
      046: RETURN
      048: EOF test.jaf
      054: FUNC NULL
      060: EOF
    |}]

let%expect_test "deref struct assign" =
  compile_test
    {|
      struct S {};
      ref S ref_s(ref S rs) {
        S s;
        s = ref_s(rs);
        return rs;
      }
    |};
  [%expect
    {|
      000: FUNC ref_s
      006: SH_LOCALDELETE s
      012: SH_LOCALCREATE s, struct(0)
      022: SH_LOCALREF s
      028: PUSHLOCALPAGE
      030: PUSH 2
      036: SH_LOCALREF rs
      042: CALLFUNC ref_s
      048: ASSIGN
      050: PUSH 0
      056: SR_ASSIGN
      058: POP
      060: SH_LOCALREF rs
      066: DUP
      068: SP_INC
      070: RETURN
      072: PUSH -1
      078: RETURN
      080: ENDFUNC ref_s
      086: EOF test.jaf
      092: FUNC NULL
      098: EOF
    |}]

let%expect_test "ref struct assign" =
  compile_test
    {|
      struct S {};
      ref S f() {
        ref S r = f();
        return r;
      }
    |};
  [%expect
    {|
      000: FUNC f
      006: CALLSYS LockPeek
      012: POP
      014: PUSHLOCALPAGE
      016: PUSH 0
      022: DUP2
      024: REF
      026: DELETE
      028: DUP2
      030: PUSHLOCALPAGE
      032: PUSH 1
      038: CALLFUNC f
      044: ASSIGN
      046: ASSIGN
      048: DUP_X2
      050: POP
      052: REF
      054: SP_INC
      056: POP
      058: CALLSYS UnlockPeek
      064: POP
      066: SH_LOCALREF r
      072: DUP
      074: SP_INC
      076: RETURN
      078: PUSH -1
      084: RETURN
      086: ENDFUNC f
      092: EOF test.jaf
      098: FUNC NULL
      104: EOF
  |}]

let%expect_test "ref int assign" =
  compile_test
    {|
      ref int f() {
        ref int r = f();
        return r;
      }
    |};
  [%expect
    {|
      000: FUNC f
      006: CALLSYS LockPeek
      012: POP
      014: PUSHLOCALPAGE
      016: PUSH 0
      022: DUP2
      024: REFREF
      026: POP
      028: DELETE
      030: DUP2
      032: PUSHLOCALPAGE
      034: PUSH 2
      040: CALLFUNC f
      046: R_ASSIGN
      048: R_ASSIGN
      050: POP
      052: POP
      054: REF
      056: SP_INC
      058: CALLSYS UnlockPeek
      064: POP
      066: PUSHLOCALPAGE
      068: PUSH 0
      074: REFREF
      076: DUP_U2
      078: SP_INC
      080: RETURN
      082: PUSH -1
      088: PUSH 0
      094: RETURN
      096: ENDFUNC f
      102: EOF test.jaf
      108: FUNC NULL
      114: EOF
  |}]

let%expect_test "syscall" =
  compile_test {|
      void f() { system.Exit(42); }
  |};
  [%expect
    {|
      000: FUNC f
      006: PUSH 42
      012: CALLSYS Exit
      018: RETURN
      020: ENDFUNC f
      026: EOF test.jaf
      032: FUNC NULL
      038: EOF
  |}]

let%expect_test "global array initializer" =
  compile_test {|
      array@int a[10];
      void f() {}
  |};
  [%expect
    {|
      000: FUNC f
      006: RETURN
      008: ENDFUNC f
      014: EOF test.jaf
      020: FUNC 0
      026: PUSHGLOBALPAGE
      028: PUSH 0
      034: PUSH 10
      040: PUSH 1
      046: A_ALLOC
      048: RETURN
      050: ENDFUNC 0
      056: FUNC NULL
      062: EOF
    |}]

let%expect_test "if" =
  compile_test
    {|
      void f() {
        int i = 1;
        if (i) {
          i = 2;
        }
      }
  |};
  [%expect
    {|
      000: FUNC f
      006: SH_LOCALASSIGN i, 1
      016: SH_LOCALREF i
      022: IFZ 44
      028: SH_LOCALASSIGN i, 2
      038: JUMP 44
      044: RETURN
      046: ENDFUNC f
      052: EOF test.jaf
      058: FUNC NULL
      064: EOF
    |}]

let%expect_test "if-else" =
  compile_test
    {|
      void f() {
        int i = 1;
        if (i) {
          i = 2;
        } else {
          i = 3;
        }
      }
  |};
  [%expect
    {|
      000: FUNC f
      006: SH_LOCALASSIGN i, 1
      016: SH_LOCALREF i
      022: IFZ 44
      028: SH_LOCALASSIGN i, 2
      038: JUMP 54
      044: SH_LOCALASSIGN i, 3
      054: RETURN
      056: ENDFUNC f
      062: EOF test.jaf
      068: FUNC NULL
      074: EOF
    |}]

let%expect_test "for-loop" =
  compile_test
    {|
      void f() {
        int i;
        for (i = 0; i < 10; i++) {
          continue;
          break;
        }
      }
  |};
  [%expect
    {|
      000: FUNC f
      006: SH_LOCALASSIGN i, 0
      016: SH_LOCALASSIGN i, 0
      026: SH_LOCALREF i
      032: PUSH 10
      038: LT
      040: IFZ 82
      046: JUMP 64
      052: SH_LOCALINC i
      058: JUMP 26
      064: JUMP 52
      070: JUMP 82
      076: JUMP 52
      082: RETURN
      084: ENDFUNC f
      090: EOF test.jaf
      096: FUNC NULL
      102: EOF
    |}]

let%expect_test "for-inconly" =
  compile_test
    {|
      void f() {
        int i;
        for (;; i++) {
          continue;
          break;
        }
      }
  |};
  [%expect
    {|
      000: FUNC f
      006: SH_LOCALASSIGN i, 0
      016: JUMP 34
      022: SH_LOCALINC i
      028: JUMP 16
      034: JUMP 22
      040: JUMP 52
      046: JUMP 22
      052: RETURN
      054: ENDFUNC f
      060: EOF test.jaf
      066: FUNC NULL
      072: EOF
    |}]

let%expect_test "forever" =
  compile_test
    {|
      void f() {
        for (;;) {
          continue;
          break;
        }
      }
  |};
  [%expect
    {|
      000: FUNC f
      006: JUMP 6
      012: JUMP 24
      018: JUMP 6
      024: RETURN
      026: ENDFUNC f
      032: EOF test.jaf
      038: FUNC NULL
      044: EOF
    |}]

let%expect_test "logical-not" =
  compile_test {|
      void f() {
        bool b;
        b = !b;
      }
  |};
  [%expect
    {|
      000: FUNC f
      006: SH_LOCALASSIGN b, 0
      016: PUSHLOCALPAGE
      018: PUSH 0
      024: SH_LOCALREF b
      030: NOT
      032: ITOB
      034: ASSIGN
      036: POP
      038: RETURN
      040: ENDFUNC f
      046: EOF test.jaf
      052: FUNC NULL
      058: EOF
    |}]

let%expect_test "self reference in initval" =
  compile_test {|
      void f() {
        string s = s = "a";
      }
  |};
  [%expect
    {|
      000: FUNC f
      006: SH_LOCALREF s
      012: SH_LOCALREF s
      018: S_PUSH "a"
      024: S_ASSIGN
      026: S_ASSIGN
      028: S_POP
      030: RETURN
      032: ENDFUNC f
      038: EOF test.jaf
      044: FUNC NULL
      050: EOF
    |}]

let%expect_test "functype with string initval" =
  compile_test
    {|
        functype void funcptr(void);
        void f() {
          funcptr fp = "f";
        }
    |};
  [%expect
    {|
      000: FUNC f
      006: PUSHLOCALPAGE
      008: PUSH 0
      014: S_PUSH "f"
      020: PUSH 0
      026: FT_ASSIGNS
      028: S_POP
      030: RETURN
      032: ENDFUNC f
      038: EOF test.jaf
      044: FUNC NULL
      050: EOF |}]

let%expect_test "local delete" =
  compile_test
    {|
        struct S {};
        void f() {
          for (;;) {
            ref int r;
            array@int a;
            S s;
          }
        }
    |};
  [%expect
    {|
        000: FUNC f
        006: CALLSYS LockPeek
        012: POP
        014: PUSHLOCALPAGE
        016: PUSH 0
        022: DUP2
        024: REFREF
        026: POP
        028: DELETE
        030: PUSH -1
        036: PUSH 0
        042: R_ASSIGN
        044: POP
        046: POP
        048: CALLSYS UnlockPeek
        054: POP
        056: PUSHLOCALPAGE
        058: PUSH 2
        064: A_FREE
        066: SH_LOCALDELETE s
        072: SH_LOCALCREATE s, struct(0)
        082: SH_LOCALDELETE s
        088: PUSHLOCALPAGE
        090: PUSH 2
        096: A_FREE
        098: SH_LOCALDELETE r
        104: JUMP 6
        110: RETURN
        112: ENDFUNC f
        118: EOF test.jaf
        124: FUNC NULL
        130: EOF |}]

let%expect_test "local delete with goto" =
  compile_test
    {|
      struct S {};
      void f() {
        S s1;
        for (;;) {
          S s2;
          goto skip;
        }
        skip:
      }
    |};
  [%expect
    {|
      000: FUNC f
      006: SH_LOCALDELETE s1
      012: SH_LOCALCREATE s1, struct(0)
      022: SH_LOCALDELETE s2
      028: SH_LOCALCREATE s2, struct(0)
      038: SH_LOCALDELETE s2
      044: JUMP 62
      050: SH_LOCALDELETE s2
      056: JUMP 22
      062: RETURN
      064: ENDFUNC f
      070: EOF test.jaf
      076: FUNC NULL
      082: EOF
    |}]

let%expect_test "member pointer" =
  compile_test
    {|
      struct S {
        int a;
        int b;
      };
      void f(array@S as) {
        as.SortBy(&S::b);
      }
    |};
  [%expect
    {|
      000: FUNC f
      006: PUSHLOCALPAGE
      008: PUSH 0
      014: PUSH 1
      020: A_SORT_MEM
      022: RETURN
      024: ENDFUNC f
      030: EOF test.jaf
      036: FUNC NULL
      042: EOF
    |}]

let%expect_test "dg_return_null" =
  compile_test
    {|
      delegate void dg();
      dg f() {
        return NULL;
      }
    |};
  [%expect
    {|
    000: FUNC f
    006: DG_NEW
    008: RETURN
    010: PUSH -1
    016: RETURN
    018: ENDFUNC f
    024: EOF test.jaf
    030: FUNC NULL
    036: EOF
    |}]

let%expect_test "dg_add" =
  compile_test
    {|
      delegate void dg();
      void f() {
        dg d = &f;
      }
    |};
  [%expect
    {|
      000: FUNC f
      006: PUSHLOCALPAGE
      008: PUSH 0
      014: REF
      016: PUSH 1
      022: PUSH -1
      028: SWAP
      030: DG_SET
      032: RETURN
      034: ENDFUNC f
      040: EOF test.jaf
      046: FUNC NULL
      052: EOF
    |}]

let%expect_test "dg_set_string" =
  compile_test
    {|
      delegate void dg();
      void f() {
        dg d = "f";
        d = "f";
      }
    |};
  [%expect
    {|
    000: FUNC f
    006: PUSHLOCALPAGE
    008: PUSH 0
    014: REF
    016: S_PUSH "f"
    022: PUSH -1
    028: SWAP
    030: PUSH 0
    036: DG_STR_TO_METHOD
    038: DG_SET
    040: PUSHLOCALPAGE
    042: PUSH 0
    048: REF
    050: S_PUSH "f"
    056: PUSH -1
    062: SWAP
    064: PUSH 0
    070: DG_STR_TO_METHOD
    072: DG_SET
    074: RETURN
    076: ENDFUNC f
    082: EOF test.jaf
    088: FUNC NULL
    094: EOF
    |}]

let%expect_test "dg_erase" =
  compile_test
    {|
      delegate void dg();
      void f() {
        dg d;
        d.Erase(&f);
      }
    |};
  [%expect
    {|
    000: FUNC f
    006: PUSHLOCALPAGE
    008: PUSH 0
    014: REF
    016: DG_CLEAR
    018: PUSHLOCALPAGE
    020: PUSH 0
    026: REF
    028: PUSH 1
    034: PUSH -1
    040: SWAP
    042: DG_ERASE
    044: RETURN
    046: ENDFUNC f
    052: EOF test.jaf
    058: FUNC NULL
    064: EOF
    |}]
