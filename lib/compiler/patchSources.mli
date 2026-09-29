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

type role = Reference | Target

type jaf_source = {
  filename : string;
  role : role;
  declarations : Jaf.declaration list;
}

type source =
  | Jaf of jaf_source
  | Hll of {
      filename : string;
      name : string;
      import_name : string;
      declarations : Jaf.declaration list;
    }

type definition = {
  source : jaf_source;
  name : string;
  class_name : string option;
  declaration : Jaf.fundecl;
}

type selection =
  | FuncType of Jaf.fundecl
  | Delegate of Jaf.fundecl
  | Function of definition
  | Class of Common.Jaf.structdecl
  | GlobalGroup of Jaf.global_group
  | Library of string
  | Global of Common.Jaf.variable

(** [sources] lists project sources followed by external patches. [globals]
    includes constants. The ASTs are not type checked. *)
type t = private {
  project : Pje.t;
  sources : source list;
  structures : Jaf.structdecl list;
  global_groups : Jaf.global_group list;
  globals : (string option * Jaf.variable) list;
  selections : selection list;
  output_definitions : definition list;
  definitions : (string, definition) Base.Hashtbl.t;
}

(** [read_file] returns raw bytes. An external HLL file uses its filename stem
    as its import name. *)
val load :
  ?read_file:(string -> string) ->
  ?patch_files:string list ->
  ?targets:string list ->
  string ->
  t

val find_definition : t -> string -> definition option
val global_variables : t -> Jaf.variable list
val selected_classes : t -> Jaf.structdecl list

(** Includes delegate types. *)
val selected_function_types : t -> Jaf.fundecl list

(** Import names. *)
val selected_libraries : t -> string list

(** Whether a global or global group is selected. *)
val rebuild_globals : t -> bool
