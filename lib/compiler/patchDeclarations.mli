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

(** Add the selected declarations to the AIN and bind all source declarations to
    it. *)
val create : Ain.t -> PatchSources.t -> t

val context : t -> Jaf.context
val added_types : t -> (string * string) list

(** Added global groups, HLL libraries and HLL functions. *)
val added_entries : t -> (string * string) list

val resolve_type : t -> Jaf.type_specifier -> unit

(** Bind the compiler-generated array initializer called by a constructor. *)
val bind_initializer_reference : t -> Jaf.fundecl -> unit
