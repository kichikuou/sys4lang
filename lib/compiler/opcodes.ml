(* Copyright (C) 2021 Nunuhara Cabbage <nunuhara@haniwa.technology>
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
open Jaf
open Bytecode

(* Selection of instructions by operator and operand type. *)

let incdec (op : unary_op) (ty : jaf_type) =
  match (op, ty) with
  | (PreInc | PostInc), LongInt -> Some LI_INC
  | (PreDec | PostDec), LongInt -> Some LI_DEC
  | (PreInc | PostInc), _ -> Some INC
  | (PreDec | PostDec), _ -> Some DEC
  | _ -> None

let negate (ty : jaf_type) = match ty with Float -> F_INV | _ -> INV

(* The instruction for a binary operator that takes two values of the type of
   the left operand from the stack. *)
let binary (ty : jaf_type) (op : binary_op) =
  match (ty, op) with
  | (Int | LongInt | Bool), Equal -> Some EQUALE
  | (Int | LongInt | Bool), NEqual -> Some NOTE
  | Int, Plus -> Some ADD
  | Int, Minus -> Some SUB
  | Int, Times -> Some MUL
  | Int, Divide -> Some DIV
  | Int, Modulo -> Some MOD
  | (Int | LongInt), LT -> Some LT
  | (Int | LongInt), GT -> Some GT
  | (Int | LongInt), LTE -> Some LTE
  | (Int | LongInt), GTE -> Some GTE
  | (Int | Bool), BitOr -> Some OR
  | (Int | Bool), BitXor -> Some XOR
  | (Int | Bool), BitAnd -> Some AND
  | (Int | Bool), LShift -> Some LSHIFT
  | (Int | Bool), RShift -> Some RSHIFT
  | LongInt, Plus -> Some LI_ADD
  | LongInt, Minus -> Some LI_SUB
  | LongInt, Times -> Some LI_MUL
  | LongInt, Divide -> Some LI_DIV
  | LongInt, Modulo -> Some LI_MOD
  | Float, Plus -> Some F_ADD
  | Float, Minus -> Some F_SUB
  | Float, Times -> Some F_MUL
  | Float, Divide -> Some F_DIV
  | Float, Equal -> Some F_EQUALE
  | Float, NEqual -> Some F_NOTE
  | Float, LT -> Some F_LT
  | Float, GT -> Some F_GT
  | Float, LTE -> Some F_LTE
  | Float, GTE -> Some F_GTE
  | String, Plus -> Some S_ADD
  | String, Equal -> Some S_EQUALE
  | String, NEqual -> Some S_NOTE
  | String, LT -> Some S_LT
  | String, GT -> Some S_GT
  | String, LTE -> Some S_LTE
  | String, GTE -> Some S_GTE
  | Ref t, RefEqual -> Some (if is_numeric t then R_EQUALE else EQUALE)
  | Ref t, RefNEqual -> Some (if is_numeric t then R_NOTE else NOTE)
  | FuncType _, Equal -> Some EQUALE
  | FuncType _, NEqual -> Some NOTE
  | _ -> None

(* The instruction for an assignment of a number of type [ty]. *)
let assign (op : assign_op) (ty : jaf_type) =
  match (op, ty) with
  | EqAssign, (Int | Bool | TyFunction _ | FuncType _) -> Some ASSIGN
  | PlusAssign, (Int | Bool) -> Some PLUSA
  | MinusAssign, (Int | Bool) -> Some MINUSA
  | TimesAssign, (Int | Bool) -> Some MULA
  | DivideAssign, (Int | Bool) -> Some DIVA
  | ModuloAssign, (Int | Bool) -> Some MODA
  | OrAssign, (Int | Bool) -> Some ORA
  | XorAssign, (Int | Bool) -> Some XORA
  | AndAssign, (Int | Bool) -> Some ANDA
  | LShiftAssign, (Int | Bool) -> Some LSHIFTA
  | RShiftAssign, (Int | Bool) -> Some RSHIFTA
  | CharAssign, Int -> Some C_ASSIGN
  | EqAssign, LongInt -> Some LI_ASSIGN
  | PlusAssign, LongInt -> Some LI_PLUSA
  | MinusAssign, LongInt -> Some LI_MINUSA
  | TimesAssign, LongInt -> Some LI_MULA
  | DivideAssign, LongInt -> Some LI_DIVA
  | ModuloAssign, LongInt -> Some LI_MODA
  | AndAssign, LongInt -> Some LI_ANDA
  | OrAssign, LongInt -> Some LI_ORA
  | XorAssign, LongInt -> Some LI_XORA
  | LShiftAssign, LongInt -> Some LI_LSHIFTA
  | RShiftAssign, LongInt -> Some LI_RSHIFTA
  | EqAssign, Float -> Some F_ASSIGN
  | PlusAssign, Float -> Some F_PLUSA
  | MinusAssign, Float -> Some F_MINUSA
  | TimesAssign, Float -> Some F_MULA
  | DivideAssign, Float -> Some F_DIVA
  | _ -> None

(* The operand of S_MOD for a value of type [ty]. *)
let string_format_type (ty : jaf_type) =
  match ty with
  | Int -> Some 2
  | Float -> Some 3
  | String -> Some 4
  | Bool -> Some 48
  | LongInt -> Some 56
  | _ -> None
