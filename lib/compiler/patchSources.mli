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

(** A parsed patch project. [sources] contains project sources followed by
    external patches. [targets] begins with external JAF patches in the order
    supplied to [load]. ASTs are shared between these collections and
    [definitions], and have not been type checked. *)
type t = private {
  project : Pje.t;
  sources : source list;
  targets : jaf_source list;
  selections : selection list;
  output_definitions : definition list;
  definitions : (string, definition) Base.Hashtbl.t;
}

(** [load project_file] parses the sources and patch targets for a project.
    [read_file] returns raw bytes. [patch_files] accepts JAF and HLL files;
    external HLL files use their filename stem as their import name. *)
val load :
  ?read_file:(string -> string) ->
  ?patch_files:string list ->
  ?targets:string list ->
  string ->
  t

val find_definition : t -> string -> definition option

(** Non-const and const global declarations in project source order. *)
val global_variables : t -> Jaf.variable list

(** Whether any selected global or group requests whole-global reconstruction.
*)
val rebuild_globals : t -> bool
