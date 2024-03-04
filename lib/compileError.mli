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

type compile_error =
  | Error of string * Jaf.location
  | ErrorList of compile_error list

exception Compile_error of compile_error

val raise : string -> Jaf.location -> 'a
val raise_list : compile_error list -> 'a
val syntax_error : Lexing.lexbuf -> 'a
val type_error : Jaf.jaf_type -> Jaf.expression option -> Jaf.ast_node -> 'a
val undefined_variable_error : string -> Jaf.ast_node -> 'a
val arity_error : string -> int -> 'a list -> Jaf.ast_node -> 'b
val not_an_lvalue_error : Jaf.expression -> Jaf.ast_node -> 'a
val const_error : Jaf.variable -> 'a
val compile_error : string -> Jaf.ast_node -> 'a
val compiler_bug : string -> Jaf.ast_node option -> 'a
val print_error : compile_error -> (string -> string option) -> unit
