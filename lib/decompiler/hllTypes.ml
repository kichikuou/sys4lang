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

let source_params lib (func : Ain.HLL.function_t) =
  let params = Ain.HLL.args func in
  if is_array_lib lib then
    List.map params ~f:(fun v ->
        { v with Ain.Variable.type_ = with_hll_param_elements v.type_ })
  else params

let source_return_type lib (func : Ain.HLL.function_t) =
  if is_array_lib lib then
    match (func.name, func.return_type) with
    | "ShallowCopy", Array Any -> Array (Ref HllParam)
    | _, t -> with_hll_param_elements t
  else func.return_type

type entry = {
  func : Ain.HLL.function_t;
  params : Ain.Variable.t array;
  mutable return_type : ain_type;
}

(* The entries of the functions whose types a call has shown, by library. *)
type t = (string, entry list) Hashtbl.t

let create () = Hashtbl.create (module String)

let find t lib func =
  List.find (Hashtbl.find_multi t lib) ~f:(fun e -> phys_equal e.func func)

let entry t lib func =
  match find t lib func with
  | Some e -> e
  | None ->
      let e =
        {
          func;
          params = Array.of_list (source_params lib func);
          return_type = source_return_type lib func;
        }
      in
      Hashtbl.add_multi t ~key:lib ~data:e;
      e

let params t lib func =
  match find t lib func with
  | Some e -> Array.to_list e.params
  | None -> source_params lib func

let param_types t lib func =
  List.map (params t lib func) ~f:(fun (v : Ain.Variable.t) -> v.type_)

let return_type t lib func =
  match find t lib func with
  | Some e -> e.return_type
  | None -> source_return_type lib func

let known_element = function
  | Array t | Ref (Array t) -> ( match t with Any -> None | t -> Some t)
  | _ -> None

let infer_param t lib func i arg_type =
  if Ain.ain.vers >= 11 && not (is_array_lib lib) then
    match known_element arg_type with
    | None -> ()
    | Some elem -> (
        let e = entry t lib func in
        (* [i] counts the parameters that are not void. *)
        let indices =
          Array.filter_mapi e.params ~f:(fun j (v : Ain.Variable.t) ->
              match v.type_ with Void -> None | _ -> Some j)
        in
        let j = indices.(i) in
        let v = e.params.(j) in
        match v.type_ with
        | Array Any -> e.params.(j) <- { v with type_ = Array elem }
        | Ref (Array Any) -> e.params.(j) <- { v with type_ = Ref (Array elem) }
        | _ -> ())

let infer_return t lib func expected =
  if Ain.ain.vers >= 11 && not (is_array_lib lib) then
    match (known_element expected, source_return_type lib func) with
    | Some elem, Array Any -> (
        let e = entry t lib func in
        match e.return_type with
        | Array Any -> e.return_type <- Array elem
        | _ -> ())
    | _ -> ()
