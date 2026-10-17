(* Copyright (C) 2026 kichikuou <KichikuouChrome@gmail.com>
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

open Common

(** A source file of the patch. [path] is the name used to read the file and in
    error messages. [debug_path] is the name recorded in the debug information.
    A [`Project_selected] file is a project file that is also given as a patch
    file. *)
type source = {
  path : string;
  debug_path : string;
  origin : [ `Project | `Project_selected | `Extra ];
  kind : [ `Jaf | `Hll of string ];
}

(** Compiles the selected declarations of [sources] and appends them to [base].
    [sources] must list the project files first, in project order. Raises
    [CompileError.Compile_error] on error; [base] is then in an undefined state.
*)
val apply :
  base:Ain.t ->
  pje:Pje.t ->
  sources:source list ->
  targets:string list ->
  globals:bool ->
  keep_crc:bool ->
  read_file:(source -> string) ->
  debug_info:DebugInfo.t option ->
  unit
