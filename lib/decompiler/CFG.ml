(* Copyright (C) 2025 kichikuou <KichikuouChrome@gmail.com>
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
open BasicBlock

module Dll = struct
  type 'a elt = {
    mutable value : 'a;
    mutable prev : 'a elt option;
    mutable next : 'a elt option;
  }

  and 'a t = { mutable first : 'a elt option; mutable last : 'a elt option }

  let create () = { first = None; last = None }
  let value elt = elt.value
  let set elt v = elt.value <- v
  let equal = phys_equal
  let first_elt t = t.first
  let last_elt t = t.last
  let next elt = elt.next
  let prev elt = elt.prev

  let insert_before list before_elt value =
    let new_elt = { value; prev = None; next = None } in
    (match before_elt.prev with
    | Some p ->
        p.next <- Some new_elt;
        new_elt.prev <- Some p
    | None -> list.first <- Some new_elt);
    before_elt.prev <- Some new_elt;
    new_elt.next <- Some before_elt;
    new_elt

  let insert_last list value =
    let new_elt = { value; prev = list.last; next = None } in
    (match list.last with
    | Some l -> l.next <- Some new_elt
    | None -> list.first <- Some new_elt);
    list.last <- Some new_elt;
    new_elt

  let remove list elt =
    (match elt.prev with
    | Some p -> p.next <- elt.next
    | None -> list.first <- elt.next);
    (match elt.next with
    | Some n -> n.prev <- elt.prev
    | None -> list.last <- elt.prev);
    elt.prev <- None;
    elt.next <- None

  let of_list values =
    let list = create () in
    (match values with
    | [] -> ()
    | v :: vs ->
        let first_elt = { value = v; prev = None; next = None } in
        list.first <- Some first_elt;
        let last_elt =
          List.fold vs ~init:first_elt ~f:(fun prev_elt value ->
              let new_elt = { value; prev = Some prev_elt; next = None } in
              prev_elt.next <- Some new_elt;
              new_elt)
        in
        list.last <- Some last_elt);
    list

  let splice list begin_node end_node =
    if Option.equal phys_equal begin_node end_node then create ()
    else
      let b_elt = Option.value_exn begin_node in
      let last_spliced_node =
        match end_node with Some e_elt -> e_elt.prev | None -> list.last
      in
      let l_elt = Option.value_exn last_spliced_node in

      (* Link list's remaining parts *)
      let prev_of_begin = b_elt.prev in
      (match prev_of_begin with
      | Some p -> p.next <- end_node
      | None -> list.first <- end_node);
      (match end_node with
      | Some e -> e.prev <- prev_of_begin
      | None -> list.last <- prev_of_begin);

      (* Isolate the spliced part *)
      b_elt.prev <- None;
      l_elt.next <- None;

      (* Create new list from the spliced part *)
      { first = begin_node; last = last_spliced_node }

  let to_list list =
    let rec loop acc = function
      | None -> List.rev acc
      | Some elt -> loop (elt.value :: acc) elt.next
    in
    loop [] list.first
end

type node = fragment basic_block Dll.elt
type t = fragment basic_block Dll.t

let of_list = Dll.of_list
let to_list = Dll.to_list
let value = Option.map ~f:Dll.value
let value_exn node = Dll.value (Option.value_exn node)

let next = function
  | None -> raise (Invalid_argument "next Null")
  | Some elt -> Dll.next elt

let prev = function
  | None -> raise (Invalid_argument "prev Null")
  | Some elt -> Dll.prev elt

let first = Dll.first_elt
let last = Dll.last_elt
let is_end = Option.is_none
let node_equal = Option.equal Dll.equal

let insert_before cfg node value =
  Some (Dll.insert_before cfg (Option.value_exn node) value)

let insert_last cfg value = Some (Dll.insert_last cfg value)
let remove cfg node = Dll.remove cfg (Option.value_exn node)
let set node value = Dll.set (Option.value_exn node) value

let rec iterate cfg node end_node f =
  if node_equal node end_node then ()
  else (
    f (value_exn node);
    iterate cfg (next node) end_node f)

let rec find cfg node ~next ~f =
  match value node with
  | None -> None
  | Some v -> if f v then node else find cfg (next node) ~next ~f

let find_forward cfg node ~f = find cfg node ~next ~f
let find_backward cfg node ~f = find cfg node ~next:prev ~f
let by_address addr bb = bb.addr = addr

let by_jump_target addr = function
  | { code = { Loc.txt = Jump target; _ }, _; _ } -> target = addr
  | _ -> false

let splice cfg begin_node end_node = Dll.splice cfg begin_node end_node
