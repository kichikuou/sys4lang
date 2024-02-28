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

let parse_jaf input =
  let lexbuf = Lexing.from_string input in
  Lexing.set_filename lexbuf "-";
  try Parser.jaf Lexer.token lexbuf
  with Lexer.Error | Parser.Error -> CompileError.syntax_error lexbuf

let arg_to_string ain (argtype : Bytecode.argtype) arg =
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
  | Local -> sprintf "local(%ld)" arg
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
         (List.map2_exn ~f:(arg_to_string ain) argtypes args));
    Dasm.next dasm
  done

let compile_test input =
  let ctx = Jaf.context_from_ain (Ain.create 4 0) in
  try
    let jaf = parse_jaf input in
    Declarations.register_type_declarations ctx jaf;
    Declarations.resolve_types ctx jaf false;
    Declarations.define_types ctx jaf;
    let array_init = new ArrayInit.visitor ctx in
    List.iter ~f:array_init#visit_declaration jaf;
    let jaf = jaf @ array_init#generate_initializers () in
    TypeAnalysis.check_types ctx jaf;
    ConstEval.evaluate_constant_expressions ctx jaf;
    VariableAlloc.allocate_variables ctx jaf;
    SanityCheck.check_invariants ctx jaf;
    Compiler.compile ctx "test.jaf" jaf;
    print_disassemble ctx.ain
  with CompileError.CompileError e -> CompileError.print_error e

let%expect_test "empty function" =
  compile_test {|
    void f() {}
  |};
  [%expect
    {|
      000: FUNC f
      006: RETURN
      008: ENDFUNC f
      014: FUNC NULL
      020: EOF test.jaf
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
      028: FUNC NULL
      034: EOF test.jaf
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
      024: REF
      026: DELETE
      028: PUSH -1
      034: PUSH 0
      040: R_ASSIGN
      042: POP
      044: POP
      046: CALLSYS UnlockPeek
      052: POP
      054: RETURN
      056: ENDFUNC f
      062: FUNC NULL
      068: EOF test.jaf
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
      054: FUNC NULL
      060: EOF test.jaf
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
      032: FUNC NULL
      038: EOF test.jaf
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
      060: FUNC NULL
      066: EOF test.jaf
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
      042: FUNC NULL
      048: EOF test.jaf
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
      066: PUSHLOCALPAGE
      068: PUSH 0
      074: REF
      076: DUP
      078: SP_INC
      080: RETURN
      082: PUSH -1
      088: RETURN
      090: ENDFUNC f
      096: FUNC NULL
      102: EOF test.jaf
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
      024: REF
      026: DELETE
      028: DUP2
      030: PUSHLOCALPAGE
      032: PUSH 2
      038: CALLFUNC f
      044: R_ASSIGN
      046: R_ASSIGN
      048: POP
      050: POP
      052: REF
      054: SP_INC
      056: CALLSYS UnlockPeek
      062: POP
      064: PUSHLOCALPAGE
      066: PUSH 0
      072: REFREF
      074: DUP_U2
      076: SP_INC
      078: RETURN
      080: PUSH -1
      086: PUSH 0
      092: RETURN
      094: ENDFUNC f
      100: FUNC NULL
      106: EOF test.jaf
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
      026: FUNC NULL
      032: EOF test.jaf
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
      014: FUNC 0
      020: PUSHGLOBALPAGE
      022: PUSH 0
      028: PUSH 10
      034: PUSH 1
      040: A_ALLOC
      042: RETURN
      044: ENDFUNC 0
      050: FUNC NULL
      056: EOF test.jaf
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
      006: PUSHLOCALPAGE
      008: PUSH 0
      014: PUSH 1
      020: ASSIGN
      022: POP
      024: PUSHLOCALPAGE
      026: PUSH 0
      032: REF
      034: IFZ 64
      040: PUSHLOCALPAGE
      042: PUSH 0
      048: PUSH 2
      054: ASSIGN
      056: POP
      058: JUMP 64
      064: RETURN
      066: ENDFUNC f
      072: FUNC NULL
      078: EOF test.jaf
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
      006: PUSHLOCALPAGE
      008: PUSH 0
      014: PUSH 1
      020: ASSIGN
      022: POP
      024: PUSHLOCALPAGE
      026: PUSH 0
      032: REF
      034: IFZ 64
      040: PUSHLOCALPAGE
      042: PUSH 0
      048: PUSH 2
      054: ASSIGN
      056: POP
      058: JUMP 82
      064: PUSHLOCALPAGE
      066: PUSH 0
      072: PUSH 3
      078: ASSIGN
      080: POP
      082: RETURN
      084: ENDFUNC f
      090: FUNC NULL
      096: EOF test.jaf
    |}]
