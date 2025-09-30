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

open Loc

type variable = { v : Ain.Variable.t; dims : Ast.expr list }

type function_t = {
  func : Ain.Function.t;
  struc : Ain.Struct.t option;
  name : string;
  body : Ast.statement loc;
}

type struct_t = {
  struc : Ain.Struct.t;
  mutable members : variable list;
  mutable methods : function_t list;
}

type project_t = { name : string }
type debug_info

val create_debug_info : unit -> debug_info

type printer

val create_printer : out_channel -> string -> printer
val print_newline : printer -> unit

val print_function :
  print_addr:bool -> printer -> debug_info -> function_t -> unit

val print_struct_decl : printer -> struct_t -> unit
val print_functype_decl : printer -> string -> Ain.FuncType.t -> unit
val print_globals : printer -> variable list -> unit
val print_constants : printer -> unit
val print_hll_function : printer -> Ain.HLL.function_t -> unit
val print_hll_inc : printer -> unit
val print_inc : printer -> string list -> unit
val print_pje : printer -> project_t -> unit
val print_debug_info : printer -> debug_info -> unit
