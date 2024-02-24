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
  | File -> sprintf "file(%ld)" arg
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
    TypeAnalysis.check_types ctx jaf;
    ConstEval.evaluate_constant_expressions ctx jaf;
    VariableAlloc.allocate_variables ctx jaf;
    SanityCheck.check_invariants ctx jaf;
    Compiler.compile ctx jaf;
    print_disassemble ctx.ain
  with CompileError.CompileError e -> CompileError.print_error e

let%expect_test "empty function" =
  compile_test {|
    void f() {}
  |};
  [%expect {|
      000: FUNC f
      006: RETURN
      008: ENDFUNC f
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
      026: RETURN
      028: ENDFUNC sfunc
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
  |}]
