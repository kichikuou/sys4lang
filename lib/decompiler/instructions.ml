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
open Loc
open Type
module BR = BytesReader

type instruction =
  | PUSH of int32
  | POP
  | REF
  | REFREF
  | PUSHGLOBALPAGE
  | PUSHLOCALPAGE
  | INV
  | NOT
  | COMPL
  | ADD
  | SUB
  | MUL
  | DIV
  | MOD
  | AND
  | OR
  | XOR
  | LSHIFT
  | RSHIFT
  | LT
  | GT
  | LTE
  | GTE
  | NOTE
  | EQUALE
  | ASSIGN
  | PLUSA
  | MINUSA
  | MULA
  | DIVA
  | MODA
  | ANDA
  | ORA
  | XORA
  | LSHIFTA
  | RSHIFTA
  | F_ASSIGN
  | F_PLUSA
  | F_MINUSA
  | F_MULA
  | F_DIVA
  | DUP2
  | DUP_X2
  (* CMP            = 0x2b, *)
  | JUMP of int
  | IFZ of int
  | IFNZ of int
  | RETURN
  | CALLFUNC of int
  | INC
  | DEC
  | FTOI
  | ITOF
  | F_INV
  | F_ADD
  | F_SUB
  | F_MUL
  | F_DIV
  | F_LT
  | F_GT
  | F_LTE
  | F_GTE
  | F_NOTE
  | F_EQUALE
  | F_PUSH of float
  | S_PUSH of int
  | S_POP
  | S_ADD
  | S_ASSIGN
  | S_PLUSA
  | S_REF
  (* S_REFREF       = 0x47, *)
  | S_NOTE
  | S_EQUALE
  (* SF_CREATE      = 0x4A, *)
  (* SF_CREATEPIXEL = 0x4B, *)
  (* SF_CREATEALPHA = 0x4C, *)
  | SR_POP
  | SR_ASSIGN
  | SR_REF of int
  (* SR_REFREF      = 0x50, *)
  | A_ALLOC
  | A_REALLOC
  | A_FREE
  | A_NUMOF
  | A_COPY
  | A_FILL
  | C_REF
  | C_ASSIGN
  | MSG of int
  | CALLHLL of int * int * ain_type (* lib, func, type *)
  | PUSHSTRUCTPAGE
  | CALLMETHOD of int
  | SH_GLOBALREF of int
  | SH_LOCALREF of int
  | SWITCH of int
  | STRSWITCH of int
  | FUNC of int
  | EOF of int
  | CALLSYS of int
  | SJUMP
  | CALLONJUMP
  | SWAP
  | SH_STRUCTREF of int
  | S_LENGTH
  | S_LENGTHBYTE
  | I_STRING
  | CALLFUNC2
  | DUP2_X1
  | R_ASSIGN
  | FT_ASSIGNS
  | ASSERT
  | S_LT
  | S_GT
  | S_LTE
  | S_GTE
  | S_LENGTH2
  (* S_LENGTHBYTE2  = 0x75, *)
  | NEW of int * int (* struc, func *)
  | DELETE
  | CHECKUDO
  | A_REF
  | DUP
  | DUP_U2
  | SP_INC
  (* SP_DEC         = 0x7d, *)
  | ENDFUNC of int
  | R_EQUALE
  | R_NOTE
  | SH_LOCALCREATE of int * int
  | SH_LOCALDELETE of int
  | STOI
  | A_PUSHBACK
  | A_POPBACK
  | S_EMPTY
  | A_EMPTY
  | A_ERASE
  | A_INSERT
  | SH_LOCALINC of int
  | SH_LOCALDEC of int
  | SH_LOCALASSIGN of int * int32
  | ITOB
  | S_FIND
  | S_GETPART
  | A_SORT
  (* S_PUSHBACK     = 0x91, *)
  (* S_POPBACK      = 0x92, *)
  | FTOS
  | S_MOD of int
  | S_PLUSA2
  | OBJSWAP of int (* type *)
  (* S_ERASE        = 0x97, *)
  | SR_REF2 of int
  | S_ERASE2
  | S_PUSHBACK2
  | S_POPBACK2
  | ITOLI
  | LI_ADD
  | LI_SUB
  | LI_MUL
  | LI_DIV
  | LI_MOD
  | LI_ASSIGN
  | LI_PLUSA
  | LI_MINUSA
  | LI_MULA
  | LI_DIVA
  | LI_MODA
  | LI_ANDA
  | LI_ORA
  | LI_XORA
  | LI_LSHIFTA
  | LI_RSHIFTA
  | LI_INC
  | LI_DEC
  | A_FIND
  | A_REVERSE
  | SH_SR_ASSIGN
  | SH_MEM_ASSIGN_LOCAL of int * int
  | A_NUMOF_GLOB_1 of int
  | A_NUMOF_STRUCT_1 of int
  | SH_MEM_ASSIGN_IMM of int * int32
  | SH_LOCALREFREF of int
  | SH_LOCALASSIGN_SUB_IMM of int * int32
  | SH_IF_LOC_LT_IMM of int * int32 * int
  | SH_IF_LOC_GE_IMM of int * int32 * int
  | SH_LOCREF_ASSIGN_MEM of int * int
  | PAGE_REF of int32
  | SH_GLOBAL_ASSIGN_LOCAL of int * int
  | SH_STRUCTREF_GT_IMM of int * int32
  | SH_STRUCT_ASSIGN_LOCALREF_ITOB of int * int
  | SH_LOCAL_ASSIGN_STRUCTREF of int * int
  | SH_IF_STRUCTREF_NE_LOCALREF of int * int * int
  | SH_IF_STRUCTREF_GT_IMM of int * int32 * int
  | SH_STRUCTREF_CALLMETHOD_NO_PARAM of int * int
  | SH_STRUCTREF2 of int * int32
  | SH_REF_STRUCTREF2 of int32 * int32
  | SH_STRUCTREF3 of int * int32 * int32
  | SH_STRUCTREF2_CALLMETHOD_NO_PARAM of int * int32 * int
  | SH_IF_STRUCTREF_Z of int * int
  | SH_IF_STRUCT_A_NOT_EMPTY of int * int
  | SH_IF_LOC_GT_IMM of int * int32 * int
  | SH_IF_STRUCTREF_NE_IMM of int * int32 * int
  | THISCALLMETHOD_NOPARAM of int
  | SH_IF_LOC_NE_IMM of int * int32 * int
  | SH_IF_STRUCTREF_EQ_IMM of int * int32 * int
  | SH_GLOBAL_ASSIGN_IMM of int * int32
  | SH_LOCALSTRUCT_ASSIGN_IMM of int * int32 * int32
  | SH_STRUCT_A_PUSHBACK_LOCAL_STRUCT of int * int
  | SH_GLOBAL_A_PUSHBACK_LOCAL_STRUCT of int * int
  | SH_LOCAL_A_PUSHBACK_LOCAL_STRUCT of int * int
  | SH_IF_SREF_NE_STR0 of int * int
  | SH_S_ASSIGN_REF
  | SH_A_FIND_SREF
  | SH_SREF_EMPTY
  | SH_STRUCTSREF_EQ_LOCALSREF of int * int
  | SH_LOCALSREF_EQ_STR0 of int * int
  | SH_STRUCTSREF_NE_LOCALSREF of int * int
  | SH_LOCALSREF_NE_STR0 of int * int
  | SH_STRUCT_SR_REF of int * int
  | SH_STRUCT_S_REF of int
  | S_REF2 of int32
  (* SH_REF_LOCAL_ASSIGN_STRUCTREF2, *)
  | SH_GLOBAL_S_REF of int
  | SH_LOCAL_S_REF of int
  | SH_LOCALREF_SASSIGN_LOCALSREF of int * int
  | SH_LOCAL_APUSHBACK_LOCALSREF of int * int
  | SH_S_ASSIGN_CALLSYS19
  | SH_S_ASSIGN_STR0 of int
  | SH_SASSIGN_LOCALSREF of int
  | SH_STRUCTREF_SASSIGN_LOCALSREF of int * int
  | SH_LOCALSREF_EMPTY of int
  | SH_GLOBAL_APUSHBACK_LOCALSREF of int * int
  | SH_STRUCT_APUSHBACK_LOCALSREF of int * int
  | SH_STRUCTSREF_EMPTY of int
  | SH_GLOBALSREF_EMPTY of int
  | SH_SASSIGN_STRUCTSREF of int
  | SH_SASSIGN_GLOBALSREF of int
  | SH_STRUCTSREF_NE_STR0 of int * int
  | SH_GLOBALSREF_NE_STR0 of int * int
  | SH_LOC_LT_IMM_OR_LOC_GE_IMM of int * int32 * int32
  (* instruction names are known, exact order of them are guesses after this point *)
  | A_SORT_MEM
  | DG_SET
  | DG_ADD
  | DG_CALL of int * int (* dg_type, addr *)
  | DG_NUMOF
  | DG_EXIST
  | DG_ERASE
  | DG_CLEAR
  | DG_COPY
  | DG_ASSIGN
  | DG_PLUSA
  | DG_POP
  | DG_NEW_FROM_METHOD
  | DG_MINUSA
  | DG_CALLBEGIN of int (* dg_type *)
  | DG_NEW
  | DG_STR_TO_METHOD of int (* dg_type *)
  (*instruction names are not known *)
  (* OP_0X102 = 0x102, *)
  | X_GETENV
  | X_SET
  | X_ICAST of int (* struct *)
  (* X_OP_SET = 0x106, // some kind of set operation on option types *)
  (* OP_0X107 = 0x107, // unused *)
  (* OP_0X108 = 0x108, // unused *)
  (* OP_0X109 = 0x109, // unused *)
  (* X_DUP    = 0x10A, // DUP, but it can copy multiple values *)
  (* X_MOV    = 0x10B, // moves values from the top of the stack to another position *)
  (* X_REF    = 0x10C, // REF, buf it can ref multiple values *)
  (* X_ASSIGN = 0x10D, // ASSIGN, but it can assign multiple values *)
  (* X_A_INIT = 0x10E, // some kind of array intialization operation *)
  (* X_A_SIZE = 0x10F, // gets the size of an array *)
  (* X_TO_STR = 0x110, // converts various types to string *)
  | PSEUDO_LOGAND
  | PSEUDO_LOGOR
  | PSEUDO_COMMA
  | PSEUDO_REF_ASSIGN
  | PSEUDO_FT_ASSIGNS of int
  | PSEUDO_DG_CALL of int (* dg_type *)
  | PSEUDO_A_NUMOF1
  | PSEUDO_NULL_COALESCE
  | PSEUDO_ARRAY_ASSIGN
[@@deriving show { with_path = false }]

let width = function
  | JUMP _ -> 6
  | op ->
      Printf.failwithf "width: not implemented for %s" (show_instruction op) ()

let decode code_bytes =
  let br = BR.create code_bytes () in
  let is = ref [] in
  let push i = is := i :: !is in
  while not (BR.eof br) do
    let addr = BR.get_pos br in
    let insn =
      match BR.u16 br with
      | 0x00 -> PUSH (BR.i32 br)
      | 0x01 -> POP
      | 0x02 -> REF
      | 0x03 -> REFREF
      | 0x04 -> PUSHGLOBALPAGE
      | 0x05 -> PUSHLOCALPAGE
      | 0x06 -> INV
      | 0x07 -> NOT
      | 0x08 -> COMPL
      | 0x09 -> ADD
      | 0x0a -> SUB
      | 0x0b -> MUL
      | 0x0c -> DIV
      | 0x0d -> MOD
      | 0x0e -> AND
      | 0x0f -> OR
      | 0x10 -> XOR
      | 0x11 -> LSHIFT
      | 0x12 -> RSHIFT
      | 0x13 -> LT
      | 0x14 -> GT
      | 0x15 -> LTE
      | 0x16 -> GTE
      | 0x17 -> NOTE
      | 0x18 -> EQUALE
      | 0x19 -> ASSIGN
      | 0x1a -> PLUSA
      | 0x1b -> MINUSA
      | 0x1c -> MULA
      | 0x1d -> DIVA
      | 0x1e -> MODA
      | 0x1f -> ANDA
      | 0x20 -> ORA
      | 0x21 -> XORA
      | 0x22 -> LSHIFTA
      | 0x23 -> RSHIFTA
      | 0x24 -> F_ASSIGN
      | 0x25 -> F_PLUSA
      | 0x26 -> F_MINUSA
      | 0x27 -> F_MULA
      | 0x28 -> F_DIVA
      | 0x29 -> DUP2
      | 0x2a -> DUP_X2
      (* | Opcode.CMP -> CMP *)
      | 0x2c -> JUMP (BR.int br)
      | 0x2d -> IFZ (BR.int br)
      | 0x2e -> IFNZ (BR.int br)
      | 0x2f -> RETURN
      | 0x30 -> CALLFUNC (BR.int br)
      | 0x31 -> INC
      | 0x32 -> DEC
      | 0x33 -> FTOI
      | 0x34 -> ITOF
      | 0x35 -> F_INV
      | 0x36 -> F_ADD
      | 0x37 -> F_SUB
      | 0x38 -> F_MUL
      | 0x39 -> F_DIV
      | 0x3a -> F_LT
      | 0x3b -> F_GT
      | 0x3c -> F_LTE
      | 0x3D -> F_GTE
      | 0x3E -> F_NOTE
      | 0x3f -> F_EQUALE
      | 0x40 -> F_PUSH (BR.f32 br)
      | 0x41 -> S_PUSH (BR.int br)
      | 0x42 -> S_POP
      | 0x43 -> S_ADD
      | 0x44 -> S_ASSIGN
      | 0x45 -> S_PLUSA
      | 0x46 -> S_REF
      (* | Opcode.S_REFREF -> S_REFREF *)
      | 0x48 -> S_NOTE
      | 0x49 -> S_EQUALE
      (* | Opcode.SF_CREATE -> SF_CREATE *)
      (* | Opcode.SF_CREATEPIXEL -> SF_CREATEPIXEL *)
      (* | Opcode.SF_CREATEALPHA -> SF_CREATEALPHA *)
      | 0x4d -> SR_POP
      | 0x4e -> SR_ASSIGN
      | 0x4f -> SR_REF (BR.int br)
      (* | Opcode.SR_REFREF -> SR_REFREF *)
      | 0x51 -> A_ALLOC
      | 0x52 -> A_REALLOC
      | 0x53 -> A_FREE
      | 0x54 -> A_NUMOF
      | 0x55 -> A_COPY
      | 0x56 -> A_FILL
      | 0x57 -> C_REF
      | 0x58 -> C_ASSIGN
      | 0x59 -> MSG (BR.int br)
      | 0x5a ->
          let lib = BR.int br in
          let func = BR.int br in
          let tid = if Ain.ain.vers > 8 then BR.int br else -1 in
          let type_ =
            if tid = -1 then Any else Type.create tid ~struc:0 ~rank:1
          in
          CALLHLL (lib, func, type_)
      | 0x5b -> PUSHSTRUCTPAGE
      | 0x5c -> CALLMETHOD (BR.int br)
      | 0x5d -> SH_GLOBALREF (BR.int br)
      | 0x5e -> SH_LOCALREF (BR.int br)
      | 0x5f -> SWITCH (BR.int br)
      | 0x60 -> STRSWITCH (BR.int br)
      | 0x61 -> FUNC (BR.int br)
      | 0x62 ->
          if Ain.ain.vers = 0 then SH_STRUCTREF (BR.int br) else EOF (BR.int br)
      | 0x63 -> CALLSYS (BR.int br)
      | 0x64 -> SJUMP
      | 0x65 -> CALLONJUMP
      | 0x66 -> SWAP
      | 0x67 -> SH_STRUCTREF (BR.int br)
      | 0x68 -> S_LENGTH
      | 0x69 -> S_LENGTHBYTE
      | 0x6a -> I_STRING
      | 0x6b -> CALLFUNC2
      | 0x6c -> DUP2_X1
      | 0x6d -> R_ASSIGN
      | 0x6e -> FT_ASSIGNS
      | 0x6f -> ASSERT
      | 0x70 -> S_LT
      | 0x71 -> S_GT
      | 0x72 -> S_LTE
      | 0x73 -> S_GTE
      | 0x74 -> S_LENGTH2
      (* | Opcode.S_LENGTHBYTE2 -> S_LENGTHBYTE2 *)
      | 0x76 ->
          if Ain.ain.vers > 8 then
            let struc = BR.int br in
            let func = BR.int br in
            NEW (struc, func)
          else NEW (-1, -1)
      | 0x77 -> DELETE
      | 0x78 -> CHECKUDO
      | 0x79 -> A_REF
      | 0x7a -> DUP
      | 0x7b -> DUP_U2
      | 0x7c -> SP_INC
      (* | Opcode.SP_DEC -> SP_DEC *)
      | 0x7e -> ENDFUNC (BR.int br)
      | 0x7f -> R_EQUALE
      | 0x80 -> R_NOTE
      | 0x81 ->
          let slot = BR.int br in
          SH_LOCALCREATE (slot, BR.int br)
      | 0x82 -> SH_LOCALDELETE (BR.int br)
      | 0x83 -> STOI
      | 0x84 -> A_PUSHBACK
      | 0x85 -> A_POPBACK
      | 0x86 -> S_EMPTY
      | 0x87 -> A_EMPTY
      | 0x88 -> A_ERASE
      | 0x89 -> A_INSERT
      | 0x8a -> SH_LOCALINC (BR.int br)
      | 0x8b -> SH_LOCALDEC (BR.int br)
      | 0x8c ->
          let slot = BR.int br in
          SH_LOCALASSIGN (slot, BR.i32 br)
      | 0x8d -> ITOB
      | 0x8e -> S_FIND
      | 0x8f -> S_GETPART
      | 0x90 -> A_SORT
      (* | Opcode.S_PUSHBACK -> S_PUSHBACK *)
      (* | Opcode.S_POPBACK -> S_POPBACK *)
      | 0x93 -> FTOS
      | 0x94 -> S_MOD (if Ain.ain.vers > 8 then BR.int br else -1)
      | 0x95 -> S_PLUSA2
      | 0x96 -> OBJSWAP (if Ain.ain.vers > 8 then BR.int br else -1)
      (* | Opcode.S_ERASE -> S_ERASE *)
      | 0x98 -> SR_REF2 (BR.int br)
      | 0x99 -> S_ERASE2
      | 0x9A -> S_PUSHBACK2
      | 0x9B -> S_POPBACK2
      | 0x9c -> ITOLI
      | 0x9d -> LI_ADD
      | 0x9e -> LI_SUB
      | 0x9f -> LI_MUL
      | 0xa0 -> LI_DIV
      | 0xa1 -> LI_MOD
      | 0xa2 -> LI_ASSIGN
      | 0xa3 -> LI_PLUSA
      | 0xa4 -> LI_MINUSA
      | 0xa5 -> LI_MULA
      | 0xa6 -> LI_DIVA
      | 0xa7 -> LI_MODA
      | 0xa8 -> LI_ANDA
      | 0xa9 -> LI_ORA
      | 0xaa -> LI_XORA
      | 0xab -> LI_LSHIFTA
      | 0xac -> LI_RSHIFTA
      | 0xad -> LI_INC
      | 0xae -> LI_DEC
      | 0xaf -> A_FIND
      | 0xb0 -> A_REVERSE
      | 0xb1 -> SH_SR_ASSIGN
      | 0xb2 ->
          let memb = BR.int br in
          let local = BR.int br in
          SH_MEM_ASSIGN_LOCAL (memb, local)
      | 0xb3 -> A_NUMOF_GLOB_1 (BR.int br)
      | 0xb4 -> A_NUMOF_STRUCT_1 (BR.int br)
      | 0xb5 ->
          let slot = BR.int br in
          SH_MEM_ASSIGN_IMM (slot, BR.i32 br)
      | 0xb6 -> SH_LOCALREFREF (BR.int br)
      | 0xb7 ->
          let local = BR.int br in
          let imm = BR.i32 br in
          SH_LOCALASSIGN_SUB_IMM (local, imm)
      | 0xb8 ->
          let local = BR.int br in
          let imm = BR.i32 br in
          let addr = BR.int br in
          SH_IF_LOC_LT_IMM (local, imm, addr)
      | 0xb9 ->
          let local = BR.int br in
          let imm = BR.i32 br in
          let addr = BR.int br in
          SH_IF_LOC_GE_IMM (local, imm, addr)
      | 0xba ->
          let local = BR.int br in
          let memb = BR.int br in
          SH_LOCREF_ASSIGN_MEM (local, memb)
      | 0xbb -> PAGE_REF (BR.i32 br)
      | 0xbc ->
          let glob = BR.int br in
          let local = BR.int br in
          SH_GLOBAL_ASSIGN_LOCAL (glob, local)
      | 0xbd ->
          let memb = BR.int br in
          let imm = BR.i32 br in
          SH_STRUCTREF_GT_IMM (memb, imm)
      | 0xbe ->
          let memb = BR.int br in
          let local = BR.int br in
          SH_STRUCT_ASSIGN_LOCALREF_ITOB (memb, local)
      | 0xbf ->
          let local = BR.int br in
          let memb = BR.int br in
          SH_LOCAL_ASSIGN_STRUCTREF (local, memb)
      | 0xc0 ->
          let memb = BR.int br in
          let local = BR.int br in
          let addr = BR.int br in
          SH_IF_STRUCTREF_NE_LOCALREF (memb, local, addr)
      | 0xc1 ->
          let memb = BR.int br in
          let imm = BR.i32 br in
          let addr = BR.int br in
          SH_IF_STRUCTREF_GT_IMM (memb, imm, addr)
      | 0xc2 ->
          let memb = BR.int br in
          let func = BR.int br in
          SH_STRUCTREF_CALLMETHOD_NO_PARAM (memb, func)
      | 0xc3 ->
          let memb = BR.int br in
          let slot = BR.i32 br in
          SH_STRUCTREF2 (memb, slot)
      | 0xc4 ->
          let slot1 = BR.i32 br in
          let slot2 = BR.i32 br in
          SH_REF_STRUCTREF2 (slot1, slot2)
      | 0xc5 ->
          let memb = BR.int br in
          let slot1 = BR.i32 br in
          let slot2 = BR.i32 br in
          SH_STRUCTREF3 (memb, slot1, slot2)
      | 0xc6 ->
          let memb = BR.int br in
          let slot = BR.i32 br in
          let func = BR.int br in
          SH_STRUCTREF2_CALLMETHOD_NO_PARAM (memb, slot, func)
      | 0xc7 ->
          let memb = BR.int br in
          let addr = BR.int br in
          SH_IF_STRUCTREF_Z (memb, addr)
      | 0xc8 ->
          let memb = BR.int br in
          let addr = BR.int br in
          SH_IF_STRUCT_A_NOT_EMPTY (memb, addr)
      | 0xc9 ->
          let local = BR.int br in
          let imm = BR.i32 br in
          let addr = BR.int br in
          SH_IF_LOC_GT_IMM (local, imm, addr)
      | 0xca ->
          let memb = BR.int br in
          let imm = BR.i32 br in
          let addr = BR.int br in
          SH_IF_STRUCTREF_NE_IMM (memb, imm, addr)
      | 0xcb -> THISCALLMETHOD_NOPARAM (BR.int br)
      | 0xcc ->
          let local = BR.int br in
          let imm = BR.i32 br in
          let addr = BR.int br in
          SH_IF_LOC_NE_IMM (local, imm, addr)
      | 0xcd ->
          let memb = BR.int br in
          let imm = BR.i32 br in
          let addr = BR.int br in
          SH_IF_STRUCTREF_EQ_IMM (memb, imm, addr)
      | 0xce ->
          let var = BR.int br in
          SH_GLOBAL_ASSIGN_IMM (var, BR.i32 br)
      | 0xcf ->
          let local = BR.int br in
          let slot = BR.i32 br in
          let imm = BR.i32 br in
          SH_LOCALSTRUCT_ASSIGN_IMM (local, slot, imm)
      | 0xd0 ->
          let memb = BR.int br in
          let local = BR.int br in
          SH_STRUCT_A_PUSHBACK_LOCAL_STRUCT (memb, local)
      | 0xd1 ->
          let glob = BR.int br in
          let local = BR.int br in
          SH_GLOBAL_A_PUSHBACK_LOCAL_STRUCT (glob, local)
      | 0xd2 ->
          let arrayvar = BR.int br in
          let structvar = BR.int br in
          SH_LOCAL_A_PUSHBACK_LOCAL_STRUCT (arrayvar, structvar)
      | 0xd3 ->
          let strno = BR.int br in
          let addr = BR.int br in
          SH_IF_SREF_NE_STR0 (strno, addr)
      | 0xd4 -> SH_S_ASSIGN_REF
      | 0xd5 -> SH_A_FIND_SREF
      | 0xd6 -> SH_SREF_EMPTY
      | 0xd7 ->
          let memb = BR.int br in
          let local = BR.int br in
          SH_STRUCTSREF_EQ_LOCALSREF (memb, local)
      | 0xd8 ->
          let local = BR.int br in
          let strno = BR.int br in
          SH_LOCALSREF_EQ_STR0 (local, strno)
      | 0xd9 ->
          let memb = BR.int br in
          let local = BR.int br in
          SH_STRUCTSREF_NE_LOCALSREF (memb, local)
      | 0xda ->
          let local = BR.int br in
          let strno = BR.int br in
          SH_LOCALSREF_NE_STR0 (local, strno)
      | 0xdb ->
          let memb = BR.int br in
          let struc = BR.int br in
          SH_STRUCT_SR_REF (memb, struc)
      | 0xdc -> SH_STRUCT_S_REF (BR.int br)
      | 0xdd -> S_REF2 (BR.i32 br)
      | 0xdf -> SH_GLOBAL_S_REF (BR.int br)
      | 0xe0 -> SH_LOCAL_S_REF (BR.int br)
      | 0xe1 ->
          let lvar = BR.int br in
          let rvar = BR.int br in
          SH_LOCALREF_SASSIGN_LOCALSREF (lvar, rvar)
      | 0xe2 ->
          let arrayvar = BR.int br in
          let strvar = BR.int br in
          SH_LOCAL_APUSHBACK_LOCALSREF (arrayvar, strvar)
      | 0xe3 -> SH_S_ASSIGN_CALLSYS19
      | 0xe4 -> SH_S_ASSIGN_STR0 (BR.int br)
      | 0xe5 -> SH_SASSIGN_LOCALSREF (BR.int br)
      | 0xe6 ->
          let memb = BR.int br in
          let local = BR.int br in
          SH_STRUCTREF_SASSIGN_LOCALSREF (memb, local)
      | 0xe7 -> SH_LOCALSREF_EMPTY (BR.int br)
      | 0xe8 ->
          let glob = BR.int br in
          let local = BR.int br in
          SH_GLOBAL_APUSHBACK_LOCALSREF (glob, local)
      | 0xe9 ->
          let memb = BR.int br in
          let local = BR.int br in
          SH_STRUCT_APUSHBACK_LOCALSREF (memb, local)
      | 0xea -> SH_STRUCTSREF_EMPTY (BR.int br)
      | 0xeb -> SH_GLOBALSREF_EMPTY (BR.int br)
      | 0xec -> SH_SASSIGN_STRUCTSREF (BR.int br)
      | 0xed -> SH_SASSIGN_GLOBALSREF (BR.int br)
      | 0xee ->
          let memb = BR.int br in
          let strno = BR.int br in
          SH_STRUCTSREF_NE_STR0 (memb, strno)
      | 0xef ->
          let glob = BR.int br in
          let strno = BR.int br in
          SH_GLOBALSREF_NE_STR0 (glob, strno)
      | 0xf0 ->
          let local = BR.int br in
          let imm1 = BR.i32 br in
          let imm2 = BR.i32 br in
          SH_LOC_LT_IMM_OR_LOC_GE_IMM (local, imm1, imm2)
      | 0xf1 -> A_SORT_MEM
      | 0xf2 -> DG_SET
      | 0xf3 -> DG_ADD
      | 0xf4 ->
          let dg_type = BR.int br in
          let addr = BR.int br in
          DG_CALL (dg_type, addr)
      | 0xf5 -> DG_NUMOF
      | 0xf6 -> DG_EXIST
      | 0xf7 -> DG_ERASE
      | 0xf8 -> DG_CLEAR
      | 0xf9 -> DG_COPY
      | 0xfa -> DG_ASSIGN
      | 0xfb -> DG_PLUSA
      | 0xfc -> DG_POP
      | 0xfd -> DG_NEW_FROM_METHOD
      | 0xfe -> DG_MINUSA
      | 0xff -> DG_CALLBEGIN (BR.int br)
      | 0x100 -> DG_NEW
      | 0x101 -> DG_STR_TO_METHOD (if Ain.ain.vers > 8 then BR.int br else -1)
      | 0x103 -> X_GETENV
      | 0x104 -> X_SET
      | 0x105 -> X_ICAST (BR.int br)
      | code ->
          Printf.failwithf "unknown instruction 0x%x at 0x%x" code
            (BR.get_pos br - 2)
            ()
    in
    push { addr; end_addr = BR.get_pos br; txt = insn }
  done;
  List.rev !is

let detect_ifthen_optimization code =
  let trivial_jumps = ref 0 and total_jumps = ref 0 in
  List.iter code ~f:(function
    | { addr; txt = JUMP target as op; _ } ->
        Int.incr total_jumps;
        if addr + width op = target then Int.incr trivial_jumps
    | _ -> ());
  !trivial_jumps * 10 < !total_jumps

let builtin_method_name = function
  | S_EMPTY | A_EMPTY -> "Empty"
  | S_FIND | A_FIND -> "Find"
  | S_GETPART -> "GetPart"
  | S_LENGTH | S_LENGTH2 -> "Length"
  | S_LENGTHBYTE -> "LengthByte"
  | S_ERASE2 | A_ERASE | DG_ERASE -> "Erase"
  | S_PUSHBACK2 | A_PUSHBACK -> "PushBack"
  | S_POPBACK2 | A_POPBACK -> "PopBack"
  | A_NUMOF | DG_NUMOF | PSEUDO_A_NUMOF1 -> "Numof"
  | A_ALLOC -> "Alloc"
  | A_REALLOC -> "Realloc"
  | A_FREE -> "Free"
  | A_COPY -> "Copy"
  | A_FILL -> "Fill"
  | A_INSERT -> "Insert"
  | A_SORT -> "Sort"
  | A_SORT_MEM -> "SortBy"
  | A_REVERSE -> "Reverse"
  | X_SET -> "Set"
  | DG_CLEAR -> "Clear"
  | DG_EXIST -> "Exist"
  | FTOS -> "String"
  | insn -> failwith ("no builtin for " ^ show_instruction insn)

type syscall = {
  name : string;
  return_type : ain_type;
  arg_types : ain_type list;
}

let syscalls =
  let syscall name return_type arg_types = { name; return_type; arg_types } in
  [|
    syscall "system.Exit" Void [ Int ];
    syscall "system.GlobalSave" Int [ String; String ];
    syscall "system.GlobalLoad" Int [ String; String ];
    syscall "system.LockPeek" Int [];
    syscall "system.UnlockPeek" Int [];
    syscall "system.Reset" Void [];
    syscall "system.Output" String [ String ];
    syscall "system.MsgBox" String [ String ];
    syscall "system.ResumeSave" Int [ String; String; Ref Int; Void ];
    syscall "system.ResumeLoad" Void [ String; String ];
    syscall "system.ExistFile" Int [ String ];
    syscall "system.OpenWeb" Void [ String ];
    syscall "system.GetSaveFolderName" String [];
    syscall "system.GetTime" Int [];
    syscall "system.GetGameName" String [];
    syscall "system.Error" String [ String ];
    syscall "system.ExistSaveFile" Int [ String ];
    syscall "system.IsDebugMode" Int [];
    syscall "system.MsgBoxOkCancel" Int [ String ];
    syscall "system.GetFuncStackName" String [ Int ];
    syscall "system.Peek" Void [];
    syscall "system.Sleep" Void [ Int ];
    syscall "system.ResumeWriteComment" Bool
      [ String; String; Ref (Array String) ];
    syscall "system.ResumeReadComment" Bool
      [ String; String; Ref (Array String) ];
    syscall "system.GroupSave" Int [ String; String; String; Ref Int; Void ];
    syscall "system.GroupLoad" Int [ String; String; String; Ref Int; Void ];
    syscall "system.DeleteSaveFile" Int [ String ];
    syscall "system.ExistFunc" Bool [ String ];
    syscall "system.CopySaveFile" Int [ String; String ];
  |]
