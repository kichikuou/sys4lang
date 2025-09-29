open Common
open Base

type instruction = {
  op_i : int;
  opcode : Bytecode.opcode;
  args : Bytecode.argtype list;
}

type t = {
  ain : Ain.t;
  mutable addr : int;
  mutable instruction : instruction option;
  mutable current_func : int option;
}

let create ain = { ain; addr = 0; instruction = None; current_func = None }

let arg dasm i =
  Stdlib.Bytes.get_int32_le (Ain.get_code dasm.ain) (dasm.addr + (2 + (i * 4)))

let get_instruction dasm =
  match dasm.instruction with
  | Some instruction -> instruction
  | None ->
      let op_i = Stdlib.Bytes.get_int16_le (Ain.get_code dasm.ain) dasm.addr in
      let opcode = Bytecode.opcode_of_int op_i in
      let args = Bytecode.args_of_opcode opcode in
      let instr = { op_i; opcode; args } in
      (match opcode with
      | Bytecode.FUNC ->
          dasm.current_func <- Some (Int32.to_int_exn (arg dasm 0))
      | Bytecode.ENDFUNC -> dasm.current_func <- None
      | _ -> ());
      dasm.instruction <- Some instr;
      instr

let instruction_size instr = 2 + (List.length instr.args * 4)
let eof dasm = dasm.addr >= Bytes.length (Ain.get_code dasm.ain)
let addr dasm = dasm.addr
let current_func dasm = dasm.current_func

let jump dasm pos =
  dasm.addr <- pos;
  dasm.instruction <- None

let next dasm =
  let size = instruction_size (get_instruction dasm) in
  dasm.addr <- dasm.addr + size;
  dasm.instruction <- None

let peek dasm =
  let size = instruction_size (get_instruction dasm) in
  if dasm.addr + size >= Bytes.length (Ain.get_code dasm.ain) then None
  else
    Some
      (Bytecode.opcode_of_int
         (Stdlib.Bytes.get_int16_le (Ain.get_code dasm.ain) (dasm.addr + size)))

let opcode dasm = (get_instruction dasm).op_i
let nr_args dasm = List.length (get_instruction dasm).args
let arg_type dasm i = List.nth_exn (get_instruction dasm).args i

let arguments dasm =
  List.map (List.init (nr_args dasm) ~f:Stdlib.( ~+ )) ~f:(arg dasm)

let argument_types dasm = (get_instruction dasm).args
