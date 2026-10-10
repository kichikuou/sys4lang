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

open Common
open Base

type kind = GlobalArrays | MemberArrays | DefaultConstructor

type target = {
  kind : kind;
  name : string;
  owner : Jaf.structdecl option;
  index : int option;
}

let select ain (program : PatchSources.t) =
  let target ?owner kind name =
    {
      kind;
      name;
      owner;
      index = Option.map (Ain.get_function ain name) ~f:(fun f -> f.index);
    }
  in
  let global_variables = PatchSources.global_variables program in
  let globals = PatchSources.rebuild_globals program in
  let class_target name =
    let s =
      List.find_exn program.structures ~f:(fun s ->
          String.equal s.Jaf.name name)
    in
    let has_constructor =
      List.exists s.decls ~f:(function Jaf.Constructor _ -> true | _ -> false)
    in
    let init_name = name ^ "@2" in
    if has_constructor || Option.is_some (Ain.get_function ain init_name) then (
      if
        Option.is_none (Ain.get_function ain init_name)
        && not
             (List.exists program.output_definitions ~f:(fun d ->
                  Jaf.is_constructor d.declaration
                  && Option.equal String.equal d.class_name (Some name)))
      then
        CompileError.raise
          ("Initializer requires a selected constructor body: " ^ name)
          s.loc;
      target ~owner:s MemberArrays init_name)
    else target ~owner:s DefaultConstructor (name ^ "@0")
  in
  let classes =
    List.map (PatchSources.selected_classes program) ~f:(fun s -> s.name)
    @ List.filter_map program.output_definitions ~f:(fun d ->
        match d.class_name with
        | Some owner
          when Jaf.is_constructor d.declaration
               && Option.is_none (Ain.get_function ain (owner ^ "@2")) ->
            Some owner
        | _ -> None)
    |> List.stable_dedup ~compare:String.compare
  in
  let has_allocation variables =
    List.exists variables ~f:(fun v ->
        (not v.Jaf.is_const) && not (List.is_empty v.array_dim))
  in
  let targets =
    List.map classes ~f:class_target
    @ if globals then [ target GlobalArrays "0" ] else []
  in
  List.filter targets ~f:(fun t ->
      Option.is_some t.index
      || Poly.equal t.kind MemberArrays
      ||
      match t.owner with
      | None -> has_allocation global_variables
      | Some s ->
          List.exists s.decls ~f:(function
            | Jaf.MemberDecl ds -> has_allocation ds.vars
            | _ -> false))

let generate declarations (program : PatchSources.t) (target : target) index =
  let open Jaf in
  let ctx = PatchDeclarations.context declarations in
  let variables, class_name, class_index, name, loc =
    match target.owner with
    | Some s ->
        ( List.concat_map s.decls ~f:(function
            | MemberDecl ds -> ds.vars
            | _ -> []),
          Some s.name,
          Ain.get_struct_index ctx.ain s.name,
          (match target.kind with MemberArrays -> "2" | _ -> "0"),
          s.loc )
    | None ->
        let variables = PatchSources.global_variables program in
        (* Validation has already retained the input type and ID of size-less
           arrays as well as arrays with explicit dimensions. *)
        (variables, None, None, "0", dummy_location)
  in
  let body =
    List.filter_map variables ~f:(fun v ->
        if v.is_const || List.is_empty v.array_dim then None
        else Some (ArrayInit.array_alloc_stmt v))
  in
  {
    name;
    loc;
    return = { ty = Void; location = loc };
    params = [];
    body = Some body;
    is_label = false;
    is_lambda = false;
    is_private = false;
    index = Some index;
    class_name;
    class_index;
  }
