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

(* The parameter and return types of HLL functions in the source.

   In AIN v11+, an array type of an HLL function has no element type. In HLL
   Array, the arrays have the element type hll_param, but ShallowCopy returns
   an array of references to the elements. For the other libraries, an
   element type comes from the first call that shows it. *)

(** The element types that the calls have shown. *)
type t

val create : unit -> t

(** [params t lib func] returns the parameters of the function [func] of the
    library [lib]. *)
val params : t -> string -> Ain.HLL.function_t -> Ain.Variable.t list

val param_types : t -> string -> Ain.HLL.function_t -> Ain.type_t list
val return_type : t -> string -> Ain.HLL.function_t -> Ain.type_t

(** [infer_param t lib func i arg_type] records the element type of the array
    parameter [i] from the type of an argument. *)
val infer_param : t -> string -> Ain.HLL.function_t -> int -> Ain.type_t -> unit

(** [infer_return t lib func expected] records the element type of the array
    that [func] returns from the type that the caller expects. *)
val infer_return : t -> string -> Ain.HLL.function_t -> Ain.type_t -> unit
