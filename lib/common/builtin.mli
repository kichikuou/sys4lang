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

val fundecl_of_syscall : Bytecode.syscall -> Jaf.fundecl

val fundecl_of_builtin :
  Jaf.context ->
  Bytecode.builtin ->
  Jaf.jaf_type ->
  Jaf.ast_node option ->
  Jaf.fundecl

val function_of_syscall : Bytecode.syscall -> Ain.Function.t

val function_of_builtin :
  Jaf.context -> Bytecode.builtin -> Jaf.jaf_type -> Ain.Function.t
