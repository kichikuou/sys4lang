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

open Core
open Jaf
open Printf

exception Syntax_error of Lexing.position * Lexing.position
exception Type_error of jaf_type * expression option * ast_node
exception Undefined_variable of string * ast_node
exception Arity_error of Ain.Function.t * expression list * ast_node
exception Not_lvalue_error of expression * ast_node
exception Const_error of variable
exception CompileError of string * ast_node
exception CompilerBug of string * ast_node option
exception LinkError of string
exception LinkerBug of string

let syntax_error lexbuf =
  raise
    (Syntax_error (Lexing.lexeme_start_p lexbuf, Lexing.lexeme_end_p lexbuf))

let type_error ty expr parent = raise (Type_error (ty, expr, parent))

let undefined_variable_error name parent =
  raise (Undefined_variable (name, parent))

let arity_error t args parent = raise (Arity_error (t, args, parent))
let not_an_lvalue_error expr parent = raise (Not_lvalue_error (expr, parent))
let const_error v = raise (Const_error v)
let compile_error str node = raise (CompileError (str, node))
let compiler_bug str node = raise (CompilerBug (str, node))
let link_error str = raise (LinkError str)
let linker_bug str = raise (LinkerBug str)

let format_location (s, e) =
  Lexing.(
    let scol = s.pos_cnum - s.pos_bol + 1 in
    let ecol = e.pos_cnum - e.pos_bol + 1 in
    if s.pos_lnum = e.pos_lnum then
      sprintf "%s:%d:%d-%d" s.pos_fname s.pos_lnum scol ecol
    else sprintf "%s:%d:%d-%d:%d" s.pos_fname s.pos_lnum scol e.pos_lnum ecol)

let format_node_location node = format_location (ast_node_pos node)

let print_error = function
  | Syntax_error (s, e) -> printf "%s: Syntax error\n" (format_location (s, e))
  | Type_error (expected, actual, parent) ->
      let s_expected = jaf_type_to_string expected in
      let s_actual =
        match actual with
        | None -> "void"
        | Some expr -> jaf_type_to_string expr.ty
      in
      printf "%s: Type error: expected %s; got %s\n"
        (format_node_location parent)
        s_expected s_actual;
      Option.iter actual ~f:(fun e -> printf "\tat: %s\n" (expr_to_string e));
      printf "\tin: %s\n" (ast_to_string parent)
  | Undefined_variable (name, node) ->
      printf "%s: Undefined variable: %s\n" (format_node_location node) name
  | Arity_error (f, args, parent) ->
      printf
        "%s: wrong number of arguments to function %s (expected %d; got %d)\n"
        (format_node_location parent)
        f.name f.nr_args (List.length args);
      printf "\tin: %s\n" (ast_to_string parent)
  | Not_lvalue_error (expr, parent) ->
      printf "%s: not an lvalue: %s\n"
        (format_node_location parent)
        (expr_to_string expr);
      printf "\tin: %s\n" (ast_to_string parent)
  | Const_error var ->
      printf "%s: %s\n"
        (format_location var.location)
        (match var.initval with
        | Some _ -> "value of const variable is not constant"
        | None -> "const variable lacks initializer");
      printf "\tin: %s\n" (var_to_string var)
  | CompileError (msg, node) ->
      printf "%s: %s\n" (format_node_location node) msg;
      printf "\tin: %s\n" (ast_to_string node)
  | LinkError msg -> printf "Error: %s\n" msg
  | CompilerBug (msg, node) ->
      (match node with
      | Some n ->
          printf "%s: %s\n\tin: %s\n" (format_node_location n) msg
            (ast_to_string n)
      | None -> printf "Error: %s\n" msg);
      printf "(This is a compiler bug!)"
  | LinkerBug msg ->
      printf "Error: %s\n" msg;
      printf "(This is a linker bug!)"
  | e -> raise e
