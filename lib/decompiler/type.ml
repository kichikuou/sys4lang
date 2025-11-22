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

open Base
module BR = BytesReader

module TypeVar = struct
  type 'a value = Var | Type of 'a | Id of int * 'a [@@deriving show]

  type 'a t = 'a node ref

  and 'a node =
    | Root of int * 'a value ref (* height of the tree, index to Ain.fnct *)
    | Link of 'a t
  [@@deriving show]

  let create value = ref (Root (1, ref value))

  let rec root node =
    match !node with
    | Root _ -> node
    | Link parent ->
        let root = root parent in
        node := Link root;
        root

  let get_value node =
    match !(root node) with Root (_, v) -> !v | _ -> failwith "cannot happen"

  let set_id node n ft =
    match !(root node) with
    | Root (_, id) -> (
        match !id with
        | Var -> id := Id (n, ft)
        | Type ft' ->
            if Poly.(ft = ft') then id := Id (n, ft)
            else failwith "type var conflict"
        | Id (_, ft') -> if Poly.(ft <> ft') then failwith "type var conflict")
    | _ -> failwith "cannot happen"

  let set_type node ft =
    match !(root node) with
    | Root (_, id) -> (
        match !id with
        | Var -> id := Type ft
        | Type ft' -> if Poly.(ft <> ft') then failwith "type var conflict"
        | Id (_, ft') -> if Poly.(ft <> ft') then failwith "type var conflict")
    | _ -> failwith "cannot happen"

  let unify_value fr fr' =
    match (!fr, !fr') with
    | Var, Var -> ()
    | Var, x -> fr := x
    | x, Var -> fr' := x
    | Type t, Type t' -> if Poly.(t <> t') then failwith "type mismatch"
    | Type t, Id (_, t') ->
        if Poly.(t = t') then fr := !fr' else failwith "type mismatch"
    | Id (_, t), Type t' ->
        if Poly.(t = t') then fr' := !fr else failwith "type mismatch"
    | Id (n, _), Id (n', _) -> if n <> n' then failwith "oops"

  let unify node node' =
    let r = root node in
    let r' = root node' in
    match (!r, !r') with
    | Root (hr, fr), Root (hr', fr') ->
        unify_value fr fr';
        if not (phys_equal r r') then
          if hr < hr' then r := Link r'
          else (
            r' := Link r;
            if hr = hr' then r := Root (hr + 1, fr))
    | _ -> failwith "cannot happen"
end

type ain_type =
  | Any
  | Void
  | Int
  | Float
  | Char
  | String
  | Bool
  | LongInt
  | IMainSystem
  | Struct of int
  | Array of ain_type
  | Ref of ain_type
  | FuncType of func_type TypeVar.t
  | StructMember of int
  | Delegate of func_type TypeVar.t
  | HllFunc2
  | HllParam
  | Option of ain_type
  | IFace of int
  | Enum2 of int
  | Enum of int
  | HllFunc
[@@deriving show]

and func_type = { return_type : ain_type; arg_types : ain_type list }

let size_in_stack = function
  | Ref (Int | LongInt | Bool | Float) | HllFunc2 -> 2
  | _ -> 1

let rec make_array base = function
  | 0 -> base
  | rank -> Array (make_array base (rank - 1))

let create enum ~struc ~rank =
  match enum with
  | 0 -> Void
  | 10 -> Int
  | 11 -> Float
  | 12 -> String
  | 13 -> Struct struc
  | 14 -> make_array Int rank
  | 15 -> make_array Float rank
  | 16 -> make_array String rank
  | 17 -> make_array (Struct struc) rank
  | 18 -> Ref Int
  | 19 -> Ref Float
  | 20 -> Ref String
  | 21 -> Ref (Struct struc)
  | 22 -> Ref (make_array Int rank)
  | 23 -> Ref (make_array Float rank)
  | 24 -> Ref (make_array String rank)
  | 25 -> Ref (make_array (Struct struc) rank)
  | 26 -> IMainSystem
  | 27 -> FuncType (TypeVar.create Var)
  | 30 -> make_array (FuncType (TypeVar.create Var)) rank
  | 31 -> Ref (FuncType (TypeVar.create Var))
  | 32 -> Ref (make_array (FuncType (TypeVar.create Var)) rank)
  | 47 -> Bool
  | 50 -> make_array Bool rank
  | 51 -> Ref Bool
  | 52 -> Ref (make_array Bool rank)
  | 55 -> LongInt
  | 58 -> make_array LongInt rank
  | 59 -> Ref LongInt
  | 60 -> Ref (make_array LongInt rank)
  | 63 -> Delegate (TypeVar.create Var)
  | 66 -> make_array (Delegate (TypeVar.create Var)) rank
  | 67 -> Ref (Delegate (TypeVar.create Var))
  | 69 -> Ref (make_array (Delegate (TypeVar.create Var)) rank)
  | 71 -> HllFunc2
  | 74 -> HllParam
  | 75 -> Ref HllParam
  | 79 -> make_array Any rank
  | 80 -> Ref (make_array Any rank)
  | 89 -> IFace struc
  | 92 -> Enum struc
  | 95 -> HllFunc
  | _ as tag -> Printf.failwithf "unknown type enum %d" tag ()

let create_ain11 enum ~struc ~subtype =
  match enum with
  | 0 -> Void
  | 10 -> Int
  | 11 -> Float
  | 12 -> String
  | 13 -> Struct struc
  | 18 -> Ref Int
  | 19 -> Ref Float
  | 20 -> Ref String
  | 21 -> Ref (Struct struc)
  | 47 -> Bool
  | 51 -> Ref Bool
  | 63 -> Delegate (TypeVar.create Var)
  | 67 -> Ref (Delegate (TypeVar.create Var))
  | 79 -> Array (Option.value_exn subtype)
  | 80 -> Ref (Array (Option.value_exn subtype))
  | 82 -> Ref (Option.value_exn subtype)
  | 86 -> Option (Option.value_exn subtype)
  | 89 -> IFace struc
  | 91 -> Enum2 struc
  | 92 -> Enum struc
  | 93 -> Ref (Enum struc)
  | _ ->
      Printf.failwithf "unknown ain11 type enum %d (struc=%d, subtype=%s)" enum
        struc
        ([%show: ain_type option] subtype)
        ()

let rec array_base_and_rank = function
  | Array t ->
      let base, rank = array_base_and_rank t in
      (base, 1 + rank)
  | t -> (t, 0)

let replace_hll_param t param_type =
  let rec aux = function
    | HllParam -> param_type
    | Array t -> Array (aux t)
    | Ref t -> Ref (aux t)
    | t -> t
  in
  aux t
