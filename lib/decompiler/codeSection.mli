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

type function_t = {
  func : Ain.Function.t;
  name : string; (* without struct name *)
  struc : Ain.Struct.t option;
  end_addr : int;
  code : Instructions.instruction Loc.loc list;
  lambdas : function_t list;
  parent : Ain.Function.t option;
}

val is_overridden_function : function_t -> bool

(* Transforms the code section of Ain v0 into a format accepted by group_by_source_file. *)
val preprocess_ain_v0 :
  Instructions.instruction Loc.loc list -> Instructions.instruction Loc.loc list

(* Splits the code section by source file. *)
val group_by_source_file :
  Instructions.instruction Loc.loc list ->
  (string * Instructions.instruction Loc.loc list) list

(* Splits the code within a source file into functions. *)
val parse_functions : Instructions.instruction Loc.loc list -> function_t list
