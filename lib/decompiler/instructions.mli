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
  | CALLHLL of int * int * Type.ain_type (* lib, func, type *)
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
[@@deriving show { with_path = false }]

val width : instruction -> int
val decode : bytes -> instruction loc list
val detect_ifthen_optimization : instruction loc list -> bool
val builtin_method_name : instruction -> string

type syscall = {
  name : string;
  return_type : Ain.type_t;
  arg_types : Ain.type_t list;
}

val syscalls : syscall array
