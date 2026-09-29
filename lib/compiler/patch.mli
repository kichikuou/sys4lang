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

type result = {
  replaced : string list;
  added : string list;
  added_types : (string * string) list;
  added_entries : (string * string) list;
}

(** [base] and [output] default to the project's AIN path. Debug information is
    updated only when its file exists. *)
val compile :
  ?base:string ->
  ?output:string ->
  ?write_debug_info:bool ->
  targets:string list ->
  sources:string list ->
  string ->
  result

(* Exposed for testing *)
type sources_result = {
  functions : string list;
  added_types : (string * string) list;
  added_entries : (string * string) list;
}

(* Exposed for testing *)
val compile_sources :
  ?debug_info:DebugInfo.t -> Common.Ain.t -> PatchSources.t -> sources_result
