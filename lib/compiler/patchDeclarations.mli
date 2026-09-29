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

type t

(** Classify and validate source type names against the base AIN, then reserve
    trailing IDs for all selected new types and bind source declarations. *)
val prepare : Ain.t -> PatchSources.t -> t

val context : t -> Jaf.context

(** Added (kind, name) types in source declaration order. *)
val added_types : t -> (string * string) list

(** Added global groups, HLL libraries and HLL functions in application order.
*)
val added_entries : t -> (string * string) list

(** Resolve every source type name to an existing or reserved AIN ID. *)
val resolve : t -> PatchSources.t -> unit

(** Define new function/delegate type signatures, validate selected structure
    and global layouts, and append their source suffixes and new global groups.
    Append new libraries/functions from selected HLL declarations, validating
    existing signatures. *)
val apply_additions : t -> PatchSources.t -> unit

(** Validate and bind every source declaration against the updated AIN and
    explicitly selected function bodies. *)
val validate : t -> PatchSources.t -> unit

val resolve_type : t -> Jaf.type_specifier -> unit

(** Bind the compiler-generated array initializer called by a constructor. *)
val bind_initializer_reference : t -> Jaf.fundecl -> unit
