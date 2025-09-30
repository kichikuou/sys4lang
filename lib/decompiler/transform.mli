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

open Ast
open Loc

type ast_transform = statement loc -> statement loc

(* Assigns sequential numbers to labels, and removes unnecessary labels. *)
val rename_labels : ast_transform

(* Moves an assignment statement followed by a for statement into the init
   clause of the for statement. *)
val recover_loop_initializer : ast_transform

(* Removes a return at the end of a void function, or a return added by the
   compiler after a return statement in the source program. *)
val remove_redundant_return : ast_transform
val remove_implicit_array_free : ast_transform
val remove_array_free_for_dead_arrays : ast_transform

(* Removes `this.2();` call inserted at the beginning of constructors. *)
val remove_array_initializer_call : ast_transform
val remove_generated_lockpeek : ast_transform
val remove_dummy_variable_assignment : ast_transform
val remove_vardecl_default_rhs : ast_transform
val fold_newline_func_to_msg : ast_transform
val remove_optional_arguments : ast_transform
val simplify_boolean_expr : ast_transform
