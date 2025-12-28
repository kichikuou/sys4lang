(* Copyright (C) 2025 kichikuou <KichikuouChrome@gmail.com>
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

type function_owner = Struct of Ain.Struct.t | Enum of int

type function_t = {
  func : Ain.Function.t;
  name : string; (* without struct name *)
  owner : function_owner option;
  end_addr : int;
  code : Instructions.instruction Loc.loc list;
  mutable parent : function_t option;
}

type t = {
  files : (string * function_t list) list;
  lambdas : (int, function_t) Base.Hashtbl.t;
}

(* Transforms the code section of Ain v0 into a format accepted by group_by_source_file. *)
val preprocess_ain_v0 :
  Instructions.instruction Loc.loc list -> Instructions.instruction Loc.loc list

(* Splits the code section by source file, and then splits each source file
   into functions. *)
val parse : Instructions.instruction Loc.loc list -> t

(* A code section may contain multiple functions with the same ID, and the last
   one is the effective one. This function removes ineffective functions.
   When [move_to_original_file] is true, the effective definition is moved to
   the location where the function was first defined. *)
val remove_overridden_functions : move_to_original_file:bool -> t -> t
val fix_or_remove_known_broken_functions : t -> t
