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

module TypeVar : sig
  type 'a value = Var | Type of 'a | Id of int * 'a [@@deriving show]
  type 'a t [@@deriving show]

  val create : 'a value -> 'a t
  val get_value : 'a t -> 'a value
  val set_id : ('a -> 'a -> bool) -> 'a t -> int -> 'a -> (unit, 'a * 'a) result
  val set_type : ('a -> 'a -> bool) -> 'a t -> 'a -> (unit, 'a * 'a) result
  val unify : ('a -> 'a -> bool) -> 'a t -> 'a t -> unit
end

type ain_type =
  | Any
  | Void
  | Int
  | Float
  | Char
  | String
  | Bool
  | LongInt
  | IMainSystem
  | Struct of int
  | Array of ain_type
  | Ref of ain_type
  | VarRef of ain_type
  | FuncType of func_type TypeVar.t
  | StructMember of int
  | Delegate of func_type TypeVar.t
  | HllParam
  | Option of ain_type
  | IFace of int
  | Enum2 of int
  | Enum of int
  | HllFunc
[@@deriving show]

and func_type = { return_type : ain_type; arg_types : ain_type list }

val func_type_unify : func_type -> func_type -> bool
val create : int -> struc:int -> rank:int -> ain_type

(** [delegate n] returns the type variable of a delegate type with the delegate
    number [n], or -1 if the type has no number. *)
val create_ain11 :
  int ->
  struc:int ->
  subtype:ain_type option ->
  delegate:(int -> func_type TypeVar.t) ->
  ain_type

val is_scalar : ain_type -> bool
val is_fat : ain_type -> bool
val is_fat_reference : ain_type -> bool
val array_base_and_rank : ain_type -> ain_type * int
val replace_hll_param : ain_type -> ain_type -> ain_type
