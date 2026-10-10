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

type kind = GlobalArrays | MemberArrays | DefaultConstructor

type target = {
  kind : kind;
  name : string;
  owner : Common.Jaf.structdecl option;
  index : int option;
}

val select : Common.Ain.t -> PatchSources.t -> target list

(** Build the array initializer function for the selected target. *)
val generate :
  PatchDeclarations.t -> PatchSources.t -> target -> int -> Common.Jaf.fundecl
