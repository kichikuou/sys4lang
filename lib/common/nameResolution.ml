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
open Jaf

(* What a name refers to. *)

type resolved_member =
  | MemberVar of variable
  | MemberFunctions of fundecl list (* the overloads; not empty *)

type resolved_name =
  | ResolvedLocal of variable
  | ResolvedGlobal of variable
  | ResolvedFunction of fundecl
  | ResolvedMember of jaf_struct * resolved_member
  | ResolvedLibrary of library
  | ResolvedSystem
  | ResolvedBuiltin of Bytecode.builtin
  | UnresolvedName

(* The member [name] of the class [s]. *)
let find_member ctx (s : jaf_struct) name =
  match Hashtbl.find s.members name with
  | Some (MemberVariable v) -> Some (MemberVar v)
  | Some MemberMethod -> (
      match find_functions ctx (method_mangled_name s.name name) with
      | [] -> None
      | fs -> Some (MemberFunctions fs))
  | None -> None

let resolve_global ctx name =
  match Hashtbl.find ctx.globals name with
  | Some g -> ResolvedGlobal g
  | None -> (
      match find_function ctx name with
      | Some f -> ResolvedFunction f
      | None -> (
          match Hashtbl.find ctx.libraries name with
          | Some l -> ResolvedLibrary l
          | None -> UnresolvedName))

(* The meaning of the identifier [name] in the environment [env]. *)
let resolve ctx (env : environment) name =
  match name with
  | "system" -> ResolvedSystem
  | "assert" ->
      ResolvedBuiltin
        (Option.value_exn (Bytecode.builtin_function_of_string "assert"))
  | _ -> (
      match env#get_local name with
      | Some v -> ResolvedLocal v
      | None -> (
          let member =
            match env#current_class with
            | Some (Struct (s_name, _)) ->
                let s = Hashtbl.find_exn ctx.structs s_name in
                Option.map (find_member ctx s name) ~f:(fun m -> (s, m))
            | _ -> None
          in
          match member with
          | Some (s, m) -> ResolvedMember (s, m)
          | None -> resolve_global ctx name))
