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

open Base
open Loc

class analyzer : Ain.Function.t -> Ain.Struct.t option -> object
  method analyze_expr : Ain.type_t -> Ast.expr -> Ast.expr * Ain.type_t
  method analyze_lvalue : Ast.lvalue -> Ast.lvalue * Ain.type_t
  method analyze_statement : Ast.statement loc -> Ast.statement loc
end
