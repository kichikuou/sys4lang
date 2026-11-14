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
   an array of references to the elements. *)

(** [params lib func] returns the parameters of the function [func] of the
    library [lib]. *)
val params : string -> Ain.HLL.function_t -> Ain.Variable.t list

val param_types : string -> Ain.HLL.function_t -> Ain.type_t list
val return_type : string -> Ain.HLL.function_t -> Ain.type_t
