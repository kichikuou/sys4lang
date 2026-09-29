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

(** Collect explicit and generated bodies once per AIN function name. *)
type output =
  | Body of PatchSources.definition
  | Initializer of PatchInitializers.target

val name : output -> string
val outputs : PatchSources.t -> PatchInitializers.target list -> output list

(** Modify the AIN to register outputs, reusing existing IDs or allocating
    trailing IDs. Set the AIN IDs of source-defined functions and update
    constructor/destructor registrations. *)
val register : Common.Ain.t -> output list -> (output * int) list

type result = {
  functions : string list;
  added_types : (string * string) list;
  added_entries : (string * string) list;
}

(** Compile selected bodies and array initializers into [ain]. On failure,
    discard [ain]: changes are not rolled back. *)
val compile :
  ?debug_info:DebugInfo.t -> Common.Ain.t -> PatchSources.t -> result

type file_result = {
  replaced : string list;
  added : string list;
  added_types : (string * string) list;
  added_entries : (string * string) list;
  warnings : string list;
}

(** Compile selected targets and write the resulting AIN. [base] and [output]
    default to the project's AIN path. When [write_debug_info] is true (the
    default), existing debug information is updated when available. *)
val compile_file :
  project:string ->
  ?base:string ->
  targets:string list ->
  sources:string list ->
  ?output:string ->
  ?write_debug_info:bool ->
  unit ->
  file_result
