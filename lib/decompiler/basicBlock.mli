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

type terminator =
  | Seq
  | Jump of int (* addr *)
  | Branch of int * Ast.expr (* (addr, cond) - jumps if cond == 0 *)
  | Switch0 of int * Ast.expr
  | DoWhile0 of int (* addr of branching basic block *)
[@@deriving show { with_path = false }]

val seq_terminator : terminator loc

(* A piece of code held in a basic block. It consists of a sequence of
   statements followed by a terminator instruction. *)
type fragment = terminator loc * Ast.statement loc list
[@@deriving show { with_path = false }]

type 'a basic_block = {
  addr : int;
  end_addr : int;
  labels : Ast.label loc list;
  code : 'a;
  mutable nr_jump_srcs : int;
}
[@@deriving show { with_path = false }]

type t = fragment basic_block [@@deriving show { with_path = false }]

val create : CodeSection.function_t -> t list

(* Replace the first occurence of each local variable with the variable declaration. *)
val generate_var_decls : Ain.Function.t -> t list -> t list
