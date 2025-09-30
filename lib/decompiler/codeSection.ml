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
open Loc
open Instructions

type function_t = {
  func : Ain.Function.t;
  name : string; (* without struct name *)
  struc : Ain.Struct.t option;
  end_addr : int;
  code : instruction loc list;
  lambdas : function_t list;
  parent : Ain.Function.t option;
}

let is_overridden_function (f : function_t) =
  f.func.address
  <> match List.hd f.code with Some insn -> insn.addr | None -> f.end_addr

(* In Ain v0, when a Function.t is a method, its name field contains the class
   name (the method name is not recorded anywhere). To simplify the
   decompilation process, rename them to align with the Ain v1+ naming
   convention. *)
let rename_ain_v0_methods () =
  if Ain.ain.vers = 0 then
    Array.iteri Ain.ain.func ~f:(fun i func ->
        match
          Array.find Ain.ain.strt ~f:(fun s -> String.equal s.name func.name)
        with
        | Some s when s.constructor = i ->
            func.name <- Printf.sprintf "%s@0" func.name
        | Some s when s.destructor = i ->
            func.name <- Printf.sprintf "%s@1" func.name
        | Some _ -> func.name <- Printf.sprintf "%s@method%d" func.name i
        | None -> ())

(* Ain v0 doesn't have FUNC/EOF instructions, so insert them *)
let rec insert_func acc next_fno = function
  | ({ addr; _ } as hd) :: tl
    when next_fno < Array.length Ain.ain.func
         && addr = Ain.ain.func.(next_fno).address ->
      insert_func
        (hd :: { addr; end_addr = addr; txt = FUNC next_fno } :: acc)
        (next_fno + 1) tl
  | hd :: tl -> insert_func (hd :: acc) next_fno tl
  | [] -> List.rev ({ addr = -1; end_addr = -1; txt = EOF 0 } :: acc)

let preprocess_ain_v0 code =
  if Ain.ain.vers = 0 then (
    rename_ain_v0_methods ();
    Ain.ain.fnam <- [| "all.jaf" |];
    insert_func [] 0 code)
  else code

let group_by_source_file code =
  let rec aux acc curr = function
    | [] ->
        if List.is_empty curr then List.rev acc
        else
          (* ain file patched by AinDecompiler *)
          let eof = { addr = -1; end_addr = -1; txt = EOF (-1) } in
          aux (("remaining.jaf", List.rev (eof :: curr)) :: acc) [] []
    | ({ txt = EOF n; _ } as hd) :: tl ->
        aux ((Ain.ain.fnam.(n), List.rev (hd :: curr)) :: acc) [] tl
    | hd :: tl -> aux acc (hd :: curr) tl
  in
  aux [] [] code

let parse_method_name s =
  match String.lsplit2 s ~on:'@' with
  | None -> (None, s)
  | Some (left, name) -> (Hashtbl.find Ain.ain.struct_by_name left, name)

let rec parse_function func_id parent code =
  let lambdas = ref [] in
  let rec aux acc = function
    | { addr = end_addr; txt = ENDFUNC n; _ } :: tl ->
        if n <> func_id then
          Printf.failwithf "Unexpected ENDFUNC %d at 0x%x (ENDFUNC %d expected)"
            n end_addr func_id ()
        else
          let func = Ain.ain.func.(func_id) in
          let struc, name = parse_method_name func.name in
          ( {
              func;
              name;
              struc;
              end_addr;
              code = List.rev acc;
              lambdas = List.rev !lambdas;
              parent;
            },
            tl )
    | { txt = FUNC n; _ } :: tl when Ain.ain.func.(n).is_lambda -> (
        let lambda, code = parse_function n (Some Ain.ain.func.(func_id)) tl in
        lambdas := lambda :: !lambdas;
        (* Remove JUMP over the lambda *)
        match (acc, code) with
        | ( { addr = addr1; txt = JUMP addr2; _ } :: acc_tl,
            { addr = addr2'; end_addr; txt = insn } :: code_tl )
          when addr2 = addr2' ->
            aux acc_tl ({ addr = addr1; end_addr; txt = insn } :: code_tl)
        | _, _ -> Printf.failwithf "No JUMP that skips %s" lambda.func.name ())
    | { addr = end_addr; txt = FUNC _ | EOF _; _ } :: _ as code ->
        (* constructors are missing ENDFUNCs. *)
        let func = Ain.ain.func.(func_id) in
        let struc, name = parse_method_name func.name in
        ( {
            func;
            name;
            struc;
            end_addr;
            code = List.rev acc;
            lambdas = List.rev !lambdas;
            parent;
          },
          code )
    | hd :: tl -> aux (hd :: acc) tl
    | [] -> failwith "unexpected end of code section"
  in
  aux [] code

let parse_functions code =
  let rec aux acc = function
    | { txt = FUNC func_id; _ } :: tl ->
        let parsed, code = parse_function func_id None tl in
        aux (parsed :: acc) code
    | [ { txt = EOF _; _ } ] -> List.rev acc
    | _ :: tl -> aux acc tl (* Junk code after EOF, ignore *)
    | [] -> failwith "unexpected end of code section"
  in
  aux [] code
