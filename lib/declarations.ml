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

    method declare_function decl =
      let name = mangled_name decl in
      if Option.is_some decl.body then
        decl.index <- Some (Ain.add_function ctx.ain name).index;
      Hashtbl.update ctx.functions name ~f:(function
        | Some prev_decl ->
            if not (fundecl_compatible decl prev_decl) then
              compile_error "Function signature mismatch"
                (ASTDeclaration (Function decl))
            else if Option.is_some prev_decl.body then
              compile_error "Duplicate function definition"
                (ASTDeclaration (Function decl))
            else if Option.is_none decl.body then (
              (* Duplicate method declaration. Ignore the later one. *)
              decl.index <- Some (-1);
              prev_decl)
            else (
              prev_decl.index <- decl.index;
              (* Make sure the declaration has the default parameters specified
                 in the method declaration (default values cannot be specified
                 in method definition) *)
              if Option.is_some decl.body then decl.params <- prev_decl.params;
              decl)
        | None -> decl)

    method! visit_declaration decl =
      match decl with
      | Global ds ->
          List.iter ds.vars ~f:(fun g ->
              match Hashtbl.add ctx.globals ~key:g.name ~data:g with
              | `Duplicate ->
                  compile_error "duplicate global definition"
                    (ASTDeclaration decl)
              | `Ok ->
                  if not g.is_const then
                    g.index <- Some (Ain.add_global ctx.ain g.name gg_index))
      | GlobalGroup gg ->
          gg_index <- Ain.add_global_group ctx.ain gg.name;
          List.iter gg.vardecls ~f:(fun ds ->
              self#visit_declaration (Global ds));
          gg_index <- -1
      | Function f ->
          (match f.class_name with
          | Some name ->
              if not (Hashtbl.mem ctx.structs name) then
                compile_error
                  ("undefined class name " ^ name)
                  (ASTDeclaration decl)
              else if not (Hashtbl.mem ctx.functions (mangled_name f)) then
                compile_error
                  (f.name ^ " is not declared in class " ^ name)
                  (ASTDeclaration decl)
          | None -> ());
          self#declare_function f
      | FuncTypeDef f -> (
          match Hashtbl.add ctx.functypes ~key:f.name ~data:f with
          | `Duplicate ->
              compile_error "duplicate functype definition"
                (ASTDeclaration decl)
          | `Ok -> f.index <- Some (Ain.add_functype ctx.ain f.name).index)
      | DelegateDef f -> (
          match Hashtbl.add ctx.delegates ~key:f.name ~data:f with
          | `Duplicate ->
              compile_error "duplicate delegate definition"
                (ASTDeclaration decl)
          | `Ok -> f.index <- Some (Ain.add_delegate ctx.ain f.name).index)
      | StructDef s -> (
          let ain_s = Ain.add_struct ctx.ain s.name in
          let jaf_s = new_jaf_struct s.name ain_s.index in
          let next_index = ref 0 in
          let in_private = ref s.is_class in
          let visit_decl = function
            | AccessSpecifier Public -> in_private := false
            | AccessSpecifier Private -> in_private := true
            | Constructor f ->
                if not (String.equal f.name s.name) then
                  compile_error "constructor name doesn't match struct name"
                    (ASTDeclaration (Function f));
                f.class_name <- Some s.name;
                f.class_index <- Some ain_s.index;
                f.is_private <- !in_private;
                self#declare_function f
            | Destructor f ->
                if not (String.equal f.name ("~" ^ s.name)) then
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
          match Hashtbl.add ctx.structs ~key:s.name ~data:jaf_s with
          | `Duplicate ->
              compile_error "duplicate struct definition" (ASTDeclaration decl)
          | `Ok -> ())
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
          | Some ft -> FuncType (Some (name, Option.value_exn ft.index))
          | None -> (
              match Hashtbl.find ctx.delegates name with
              | Some dg ->
                  Delegate
                    (Some
                       (name, Option.value_exn dg.index, tymethod_of_fundecl dg))
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

(*
 * AST pass over top-level declarations to define function/struct types.
 *)
class type_define_visitor ctx =
  object (self)
    inherit ivisitor ctx

    method! visit_declaration decl =
      match decl with
      | Global ds ->
          List.iter ds.vars ~f:(fun g ->
              if not g.is_const then
                Ain.set_global_type ctx.ain g.name
                  (jaf_to_ain_type g.type_spec.ty))
      | GlobalGroup gg ->
          List.iter gg.vardecls ~f:(fun ds ->
              self#visit_declaration (Global ds))
      | Function f ->
          let obj =
            Ain.get_function_by_index ctx.ain (Option.value_exn f.index)
          in
          obj |> jaf_to_ain_function f |> Ain.write_function ctx.ain
      | FuncTypeDef f -> jaf_to_ain_functype f |> Ain.write_functype ctx.ain
      | DelegateDef f -> jaf_to_ain_functype f |> Ain.write_delegate ctx.ain
      | StructDef s -> (
          (* check for undefined methods *)
          List.iter s.decls ~f:(function
            | Method f | Constructor f | Destructor f ->
                if Option.is_none f.index then
                  compile_error
                    (Printf.sprintf "No definition of %s::%s found" s.name
                       f.name)
                    (ASTDeclaration (Function f))
            | _ -> ());
          match Ain.get_struct ctx.ain s.name with
          | Some obj -> obj |> jaf_to_ain_struct s |> Ain.write_struct ctx.ain
          | None -> compiler_bug "undefined struct" (Some (ASTDeclaration decl))
          )
      | Enum _ ->
          compile_error "Enum types not yet supported" (ASTDeclaration decl)
  end

let define_types ctx decls = (new type_define_visitor ctx)#visit_toplevel decls

let define_library ctx decls hll_name import_name =
  let is_struct_def decl = match decl with StructDef _ -> true | _ -> false in
  let struct_defs, fun_decls = List.partition_tf decls ~f:is_struct_def in
  (* handle struct definitions *)
  register_type_declarations ctx struct_defs;
  resolve_types ctx struct_defs true;
  define_types ctx struct_defs;
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
