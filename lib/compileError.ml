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

open Base
open Jaf
open Printf

let printf = Stdio.printf

type compile_error =
  | Error of string * location
  | ErrorList of compile_error list

exception Compile_error of compile_error

let raise msg loc = Base.raise (Compile_error (Error (msg, loc)))
let raise_list es = Base.raise (Compile_error (ErrorList es))

let syntax_error lexbuf =
  raise "Syntax error" (Lexing.lexeme_start_p lexbuf, Lexing.lexeme_end_p lexbuf)

let type_error expected actual parent =
  let s_expected = jaf_type_to_string expected in
  let s_actual =
    match actual with None -> "void" | Some expr -> jaf_type_to_string expr.ty
  in
  raise
    (sprintf "Type error: expected %s; got %s" s_expected s_actual)
    (ast_node_pos
       (match actual with Some e -> ASTExpression e | None -> parent))

let undefined_variable_error name parent =
  raise ("Undefined variable: " ^ name) (ast_node_pos parent)

let arity_error name nr_params args parent =
  raise
    (sprintf "Wrong number of arguments to function %s (expected %d; got %d)"
       name nr_params (List.length args))
    (ast_node_pos parent)

let not_an_lvalue_error expr parent =
  raise ("Not an lvalue: " ^ expr_to_string expr) (ast_node_pos parent)

let const_error v =
  raise
    (match v.initval with
    | Some _ -> "Value of const variable is not constant"
    | None -> "Const variable lacks initializer")
    v.location

let compile_error str node = raise str (ast_node_pos node)

let compiler_bug str node =
  raise
    (str ^ " (This is a compiler bug!)")
    (match node with Some n -> ast_node_pos n | None -> dummy_location)

let format_location (s, e) =
  Lexing.(
    let scol = s.pos_cnum - s.pos_bol + 1 in
    let ecol = e.pos_cnum - e.pos_bol + 1 in
    if s.pos_lnum = e.pos_lnum then
      sprintf "%s:%d:%d-%d" s.pos_fname s.pos_lnum scol ecol
    else sprintf "%s:%d:%d-%d:%d" s.pos_fname s.pos_lnum scol e.pos_lnum ecol)

let detab = String.substr_replace_all ~pattern:"\t" ~with_:"    "

let print_underline c s =
  let len = String.length (Sjis.from_utf8 (detab s)) in
  Stdio.print_string (String.make len c)

let rec print_error err get_source_text =
  match err with
  | ErrorList es -> List.iter es ~f:(fun e -> print_error e get_source_text)
  | Error (msg, (s, e)) -> (
      printf "%s: %s\n" (format_location (s, e)) msg;
      match get_source_text s.pos_fname with
      | None -> ()
      | Some src ->
          let lines = String.split_lines src in
          if s.pos_lnum = e.pos_lnum then (
            let line = List.nth_exn lines (s.pos_lnum - 1) in
            printf "%5d | %s\n        " s.pos_lnum (detab line);
            print_underline ' '
              (String.sub line ~pos:0 ~len:(s.pos_cnum - s.pos_bol));
            print_underline '^'
              (String.sub line ~pos:(s.pos_cnum - s.pos_bol)
                 ~len:(e.pos_cnum - s.pos_cnum));
            Stdio.print_endline "")
          else
            let error_lines =
              List.sub lines ~pos:(s.pos_lnum - 1)
                ~len:(e.pos_lnum - s.pos_lnum + 1)
            in
            List.iteri error_lines ~f:(fun i line ->
                printf "%5d | %s\n" (i + s.pos_lnum) line))
