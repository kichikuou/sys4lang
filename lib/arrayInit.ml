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
open Jaf

let make_expr node = { ty = Untyped; node; loc = dummy_location }
let make_stmt node = { node; delete_vars = []; loc = dummy_location }

let array_alloc_stmt (v : variable) =
  let var = make_expr (Ident (v.name, UnresolvedIdent)) in
  let func = make_expr (Member (var, "Alloc", UnresolvedMember)) in
  let call =
    make_expr (Call (func, v.array_dim, BuiltinCall Bytecode.ArrayAlloc))
  in
  make_stmt (Expression call)

class visitor ctx =
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
      if (not (List.is_empty !initialize_stmts)) || !has_ctor then (
        (* generate array initializer for the class *)
        let name = if !has_ctor then "2" else "0" in
        let full_name = s.name ^ "@" ^ name in
        let f_index = (Ain.add_function ctx.ain full_name).index in
        let fdecl =
          {
            name;
            loc = dummy_location;
            return = { ty = Void; location = dummy_location };
            params = [];
            body = Some (List.rev !initialize_stmts);
            is_label = false;
            index = Some f_index;
            class_name = Some s.name;
            class_index =
              Some (Ain.get_struct ctx.ain s.name |> Option.value_exn).index;
          }
        in
        Hashtbl.add_exn ctx.functions ~key:full_name ~data:fdecl;
        initializer_funcs <- Function fdecl :: initializer_funcs;
        if not !has_ctor then
          (* register the generated constructor in ain *)
          let ain_s = Option.value_exn (Ain.get_struct ctx.ain s.name) in
          Ain.write_struct ctx.ain { ain_s with constructor = f_index })

    method! visit_declaration decl =
      match decl with
      | Global ds ->
          List.iter ds.vars ~f:(function
            | { array_dim = _ :: _; is_const = false; _ } as g ->
                global_init_stmts <- array_alloc_stmt g :: global_init_stmts
            | _ -> ())
      | StructDef s -> self#visit_struct_decl s
      | Function fdecl when is_constructor fdecl ->
          self#insert_array_initializer_call fdecl
      | _ -> ()

    method generate_initializers () =
      let null_func =
        Function
          {
            name = "NULL";
            loc = dummy_location;
            return = { ty = Void; location = dummy_location };
            params = [];
            body = Some [];
            (* not to generate default return *)
            is_label = true;
            index = Some 0;
            class_name = None;
            class_index = None;
          }
      in
      let funcs = List.rev (null_func :: initializer_funcs) in
      if List.is_empty global_init_stmts then funcs
      else
        let global_init =
          Function
            {
              name = "0";
              loc = dummy_location;
              return = { ty = Void; location = dummy_location };
              params = [];
              body = Some (List.rev global_init_stmts);
              is_label = false;
              index = Some (Ain.add_function ctx.ain "0").index;
              class_name = None;
              class_index = None;
            }
        in
        global_init :: funcs
  end
