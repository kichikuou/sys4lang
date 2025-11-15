(* Copyright (C) 2021 Nunuhara Cabbage <nunuhara@haniwa.technology>
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
open CompileError

(*
 * AST pass over top-level declarations register names in the .ain file.
 *)
class type_declare_visitor ctx =
  object (self)
    inherit ivisitor ctx
    val mutable gg_index = -1

    method declare_function (decl : fundecl) =
      decl.index <- Some (-1);
      let name = mangled_name decl in
      Hashtbl.set ctx.functions ~key:name ~data:decl

    method! visit_declaration decl =
      match decl with
      | Global ds ->
          List.iter ds.vars ~f:(fun g ->
              Hashtbl.set ctx.globals ~key:g.name ~data:g;
              if not g.is_const then g.index <- Some (-1))
      | GlobalGroup gg ->
          gg_index <- Ain.add_global_group ctx.ain gg.name;
          List.iter gg.vardecls ~f:(fun ds ->
              self#visit_declaration (Global ds));
          gg_index <- -1
      | Function f ->
          (match parse_qualified_name f.name with
          | None, _ -> ()
          | Some qual, name ->
              if Hashtbl.mem ctx.structs qual then (
                f.name <- name;
                f.class_name <- Some qual;
                if not (Hashtbl.mem ctx.functions (mangled_name f)) then
                  compile_error
                    (f.name ^ " is not declared in class " ^ qual)
                    (ASTDeclaration decl)));
          self#declare_function f
      | FuncTypeDef f ->
          Hashtbl.set ctx.functypes ~key:f.name
            ~data:{ f with index = Some (-1) }
      | DelegateDef f ->
          Hashtbl.set ctx.delegates ~key:f.name
            ~data:{ f with index = Some (-1) }
      | StructDef s ->
          let unqualified_struct_name = snd (parse_qualified_name s.name) in
          let ain_s =
            Option.value_or_thunk (Ain.get_struct ctx.ain s.name)
              ~default:(fun () -> Ain.add_struct ctx.ain s.name)
          in
          let jaf_s = new_jaf_struct s.name s.loc ain_s.index in
          let next_index = ref 0 in
          let in_private = ref s.is_class in
          let visit_decl = function
            | AccessSpecifier Public -> in_private := false
            | AccessSpecifier Private -> in_private := true
            | Constructor f ->
                if not (String.equal f.name unqualified_struct_name) then
                  compile_error "constructor name doesn't match struct name"
                    (ASTDeclaration (Function f));
                f.class_name <- Some s.name;
                f.class_index <- Some ain_s.index;
                f.is_private <- !in_private;
                self#declare_function f
            | Destructor f ->
                if not (String.equal f.name ("~" ^ unqualified_struct_name))
                then
                  compile_error "destructor name doesn't match struct name"
                    (ASTDeclaration (Function f));
                f.class_name <- Some s.name;
                f.class_index <- Some ain_s.index;
                f.is_private <- !in_private;
                self#declare_function f
            | Method f ->
                f.class_name <- Some s.name;
                f.class_index <- Some ain_s.index;
                f.is_private <- !in_private;
                self#declare_function f
            | MemberDecl ds ->
                List.iter ds.vars ~f:(fun v ->
                    v.is_private <- !in_private;
                    if not v.is_const then (
                      v.index <- Some !next_index;
                      next_index :=
                        !next_index
                        + if is_ref_scalar v.type_spec.ty then 2 else 1);
                    match Hashtbl.add jaf_s.members ~key:v.name ~data:v with
                    | `Duplicate ->
                        compile_error "duplicate member variable declaration"
                          (ASTVariable v)
                    | `Ok -> ())
          in
          List.iter s.decls ~f:visit_decl;
          Hashtbl.set ctx.structs ~key:s.name ~data:jaf_s
      | Enum _ ->
          compile_error "enum types not yet supported" (ASTDeclaration decl)
  end

let register_type_declarations ctx decls =
  (new type_declare_visitor ctx)#visit_toplevel decls

(*
 * AST pass to resolve HLL-specific type aliases.
 *)
class hll_type_resolve_visitor ctx =
  object
    inherit ivisitor ctx

    method! visit_type_specifier ts =
      match ts.ty with
      | Unresolved "intp" -> ts.ty <- Ref Int
      | Unresolved "floatp" -> ts.ty <- Ref Float
      | Unresolved "stringp" -> ts.ty <- Ref String
      | Unresolved "boolp" -> ts.ty <- Ref Bool
      | _ -> ()
  end

let resolve_hll_types ctx decls =
  (new hll_type_resolve_visitor ctx)#visit_toplevel decls

(*
 * AST pass to resolve user-defined types (struct/enum/function types).
 *)
class type_resolve_visitor ctx decl_only =
  object (self)
    inherit ivisitor ctx as super

    method resolve_type name node =
      match Hashtbl.find ctx.structs name with
      | Some s -> Struct (name, s.index)
      | None -> (
          match Hashtbl.find ctx.functypes name with
          | Some _ -> FuncType (Some (name, -1))
          | None -> (
              match Hashtbl.find ctx.delegates name with
              | Some _ -> Delegate (Some (name, -1))
              | None -> (
                  match name with
                  | "IMainSystem" -> IMainSystem
                  | _ -> compile_error ("Undefined type: " ^ name) node)))

    method! visit_type_specifier ts =
      let rec resolve t =
        match t with
        | Unresolved t -> self#resolve_type t (ASTType ts)
        | Ref t -> Ref (resolve t)
        | Array t -> Array (resolve t)
        | Wrap t -> Wrap (resolve t)
        | _ -> t
      in
      ts.ty <- resolve ts.ty

    method! visit_declaration decl =
      (match decl with
      | Function f -> (
          match f.class_name with
          | Some name ->
              f.class_index <- Some (Hashtbl.find_exn ctx.structs name).index
          | _ -> ())
      | FuncTypeDef _ | DelegateDef _ | Global _ | GlobalGroup _ | StructDef _
        ->
          ()
      | Enum _ ->
          compile_error "enum types not yet supported" (ASTDeclaration decl));
      if not decl_only then super#visit_declaration decl
  end

let resolve_types ctx decls decl_only =
  (new type_resolve_visitor ctx decl_only)#visit_toplevel decls

let define_library ctx decls hll_name import_name =
  let is_struct_def decl = match decl with StructDef _ -> true | _ -> false in
  let struct_defs, fun_decls = List.partition_tf decls ~f:is_struct_def in
  (* handle struct definitions *)
  register_type_declarations ctx struct_defs;
  resolve_types ctx struct_defs true;
  (* define library *)
  let functions =
    List.map fun_decls ~f:(function
      | Function f -> f
      | decl ->
          compiler_bug "unexpected declaration in .hll file"
            (Some (ASTDeclaration decl)))
  in
  Ain.write_library ctx.ain
    {
      (Ain.add_library ctx.ain hll_name) with
      functions = List.map ~f:jaf_to_ain_hll_function functions;
    };
  let functions =
    Hashtbl.of_alist_exn
      (module String)
      (List.map ~f:(fun d -> (d.name, d)) functions)
  in
  Hashtbl.add_exn ctx.libraries ~key:import_name ~data:{ hll_name; functions }
