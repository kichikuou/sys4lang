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

open Common
open Base
open Jaf

let make_stmt node = { node; delete_vars = []; loc = dummy_location }

let array_alloc_stmt (v : variable) =
  let var = make_expr (Ident (v.name, UnresolvedIdent)) in
  let func = make_expr (Member (var, "Alloc", UnresolvedMember)) in
  let call =
    make_expr
      (Call
         ( func,
           List.map ~f:Option.some v.array_dim,
           BuiltinCall Bytecode.ArrayAlloc ))
  in
  make_stmt (Expression call)

type patch_init = {
  is_struct_selected : string -> bool;
  rebuild_globals : bool;
  find_base_function : string -> int option;
}

let make_initializer ?class_name ?class_index name index body =
  {
    name;
    loc = dummy_location;
    return = { ty = Void; location = dummy_location };
    params = [];
    body = Some body;
    is_label = false;
    is_lambda = false;
    is_private = false;
    index = Some index;
    class_name;
    class_index;
  }

class visitor ?allocator ?(generate = `All) ctx =
  let allocator =
    match allocator with
    | Some a -> a
    | None -> Declarations.build_allocator ctx.ain
  in
  object (self)
    inherit ivisitor ctx as _super
    val mutable initializer_funcs : declaration list = []
    val mutable global_init_stmts : statement list = []

    method insert_array_initializer_call (fdecl : fundecl) =
      (* insert `2();` at the beginning of constructor body *)
      let func = make_expr (Ident ("2", UnresolvedIdent)) in
      let call = make_expr (Call (func, [], UnresolvedCall)) in
      fdecl.body <-
        Some (make_stmt (Expression call) :: Option.value_exn fdecl.body)

    method visit_struct_decl s =
      let initialize_stmts = ref [] in
      let has_ctor = ref false in
      List.iter s.decls ~f:(function
        | MemberDecl ds ->
            List.iter ds.vars ~f:(function
              | { array_dim = _ :: _; is_const = false; _ } as m ->
                  initialize_stmts := array_alloc_stmt m :: !initialize_stmts
              | _ -> ())
        | Constructor fdecl ->
            has_ctor := true;
            if Option.is_some fdecl.body then
              self#insert_array_initializer_call fdecl
        | _ -> ());
      let name = if !has_ctor then "2" else "0" in
      let full_name = s.name ^ "@" ^ name in
      let class_index = (Hashtbl.find_exn ctx.structs s.name).index in
      let needed = (not (List.is_empty !initialize_stmts)) || !has_ctor in
      let emit =
        match generate with
        | `All -> needed
        | `Patch p ->
            p.is_struct_selected s.name
            && (needed || Option.is_some (p.find_base_function full_name))
      in
      if emit then (
        let f_index = allocator#generated_function_index full_name in
        let fdecl =
          make_initializer ~class_name:s.name ~class_index name f_index
            (List.rev !initialize_stmts)
        in
        Hashtbl.add_exn ctx.functions ~key:full_name ~data:fdecl;
        initializer_funcs <- Function fdecl :: initializer_funcs;
        if not !has_ctor then
          (* register the generated constructor in ain *)
          let ain_s = Ain.get_struct_by_index ctx.ain class_index in
          Ain.write_struct ctx.ain { ain_s with constructor = f_index })
      else
        match generate with
        | `Patch p when !has_ctor ->
            Option.iter (p.find_base_function full_name) ~f:(fun index ->
                Hashtbl.set ctx.functions ~key:full_name
                  ~data:
                    (make_initializer ~class_name:s.name ~class_index name index
                       []))
        | _ -> ()

    method! visit_declaration decl =
      let visit_global = function
        | { array_dim = _ :: _; is_const = false; _ } as g ->
            global_init_stmts <- array_alloc_stmt g :: global_init_stmts
        | _ -> ()
      in
      match decl with
      | Global ds -> List.iter ds.vars ~f:visit_global
      | GlobalGroup { vardecls = dss; _ } ->
          List.iter dss ~f:(function ds -> List.iter ds.vars ~f:visit_global)
      | StructDef s -> self#visit_struct_decl s
      | Function fdecl when is_constructor fdecl ->
          self#insert_array_initializer_call fdecl
      | _ -> ()

    method generate_initializers () =
      let funcs = List.rev initializer_funcs in
      let generate_global_init, funcs =
        match generate with
        | `All ->
            let null_func = Function (make_initializer "NULL" 0 []) in
            (not (List.is_empty global_init_stmts), funcs @ [ null_func ])
        | `Patch p ->
            ( p.rebuild_globals
              && ((not (List.is_empty global_init_stmts))
                 || Option.is_some (p.find_base_function "0")),
              funcs )
      in
      if not generate_global_init then funcs
      else
        let global_init =
          Function
            (make_initializer "0"
               (allocator#generated_function_index "0")
               (List.rev global_init_stmts))
        in
        global_init :: funcs
  end
