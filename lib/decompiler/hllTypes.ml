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

open Base
open Type

let is_array_lib lib = Ain.ain.vers >= 11 && String.equal lib "Array"

let rec with_hll_param_elements = function
  | Array Any -> Array HllParam
  | Ref t -> Ref (with_hll_param_elements t)
  | t -> t

let params lib (func : Ain.HLL.function_t) =
  let params = Ain.HLL.args func in
  if is_array_lib lib then
    List.map params ~f:(fun v ->
        { v with Ain.Variable.type_ = with_hll_param_elements v.type_ })
  else params

let param_types lib func =
  List.map (params lib func) ~f:(fun (v : Ain.Variable.t) -> v.type_)

let return_type lib (func : Ain.HLL.function_t) =
  if is_array_lib lib then
    match (func.name, func.return_type) with
    | "ShallowCopy", Array Any -> Array (Ref HllParam)
    | _, t -> with_hll_param_elements t
  else func.return_type
