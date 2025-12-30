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

type variable = {
  v : Ain.Variable.t;
  dims : Ast.expr list;
  initval : Ast.expr option;
}

val from_ain_variable : Ain.Variable.t -> variable

type function_t = {
  func : Ain.Function.t;
  struc : Ain.Struct.t option;
  name : string;
  body : Ast.statement loc;
  lambdas : function_t list;
}

type struct_t = {
  struc : Ain.Struct.t;
  mutable members : variable list;
  mutable methods : function_t list;
  mutable initval_lambdas : function_t list;
}

type debug_info

val create_debug_info : unit -> debug_info

type enum_t = { name : string; mutable values : (string * int32) list }
type project_t = { name : string; output_dir : string; ain_minor_version : int }

class code_printer :
  ?print_addr:bool ->
  ?dbginfo:debug_info ->
  ?enums:enum_t array ->
  string ->
object
  method get_buffer : Buffer.t
  method print_newline : unit
  method print_function : ?as_lambda:bool -> function_t -> unit
  method print_struct_decl : struct_t -> unit
  method print_enum_decl : enum_t -> unit
  method print_functype_decl : string -> Ain.FuncType.t -> unit
  method print_globals : variable list -> function_t list -> unit
  method print_constants : unit
  method print_hll : Ain.HLL.function_t array -> unit
  method print_hll_inc : unit
  method print_inc : string list -> unit
  method print_pje : project_t -> unit
  method print_debug_info : unit
end
