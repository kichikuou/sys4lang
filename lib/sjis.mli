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

(** [from_utf8 str] converts the UTF-8 encoded string [str] to Shift_JIS
    encoding. *)
val from_utf8 : string -> string

(** [to_utf8 str] converts the Shift_JIS encoded string [str] to UTF-8 encoding.
*)
val to_utf8 : string -> string

(** [is_valid n] checks if the integer [n] is a valid Shift_JIS code point. *)
val is_valid : int -> bool

(** [from_uchar_le u] converts the Unicode character [u] to a Shift_JIS code, in
    little-endian order. *)
val from_uchar_le : Uchar.t -> int option
