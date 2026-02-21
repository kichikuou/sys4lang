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
    inherit ivisitor ctx as super
    val mutable gg_index = -1

    (* LSP uses function-local lambda names to prevent ctx.functions from growing indefinitely. *)
    val mutable lambda_index = 0

    method! visit_fundecl (decl : fundecl) =
      if decl.is_lambda then (
        lambda_index <- lambda_index + 1;
        let parent = Option.value_exn self#env#current_function in
        decl.name <- Printf.sprintf "%s::<lambda : %d>" parent.name lambda_index;
        decl.class_name <- parent.class_name);
      decl.index <- Some (-1);
      let name = mangled_name decl in
      Hashtbl.update ctx.functions name ~f:(function
        | Some prev_decl
          when Option.is_some decl.body && Option.is_none prev_decl.body ->
            (* Make sure the declaration has the default parameters specified
                in the method declaration (default values cannot be specified
                in method definition) *)
            decl.params <- prev_decl.params;
            decl
        | Some prev_decl
          when Option.is_none decl.body && Option.is_some prev_decl.body ->
            prev_decl.params <- decl.params;
            prev_decl
        | _ -> decl);
      let prev_lambda_index = lambda_index in
      lambda_index <- 0;
      super#visit_fundecl decl;
      lambda_index <- prev_lambda_index

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
          (match Util.parse_qualified_name f.name with
          | None, _ -> ()
          | Some qual, name ->
              if Hashtbl.mem ctx.structs qual then (
                f.name <- name;
                f.class_name <- Some qual;
                if not (Hashtbl.mem ctx.functions (mangled_name f)) then
                  compile_error
                    (f.name ^ " is not declared in class " ^ qual)
                    (ASTDeclaration decl)));
          self#visit_fundecl f
      | FuncTypeDef f ->
          Hashtbl.set ctx.functypes ~key:f.name
            ~data:{ f with index = Some (-1) }
      | DelegateDef f ->
          Hashtbl.set ctx.delegates ~key:f.name
            ~data:{ f with index = Some (-1) }
      | StructDef s ->
          let unqualified_struct_name =
            snd (Util.parse_qualified_name s.name)
          in
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
                self#visit_fundecl f
            | Destructor f ->
                if not (String.equal f.name ("~" ^ unqualified_struct_name))
                then
                  compile_error "destructor name doesn't match struct name"
                    (ASTDeclaration (Function f));
                f.class_name <- Some s.name;
                f.class_index <- Some ain_s.index;
                f.is_private <- !in_private;
                self#visit_fundecl f
            | Method f ->
                f.class_name <- Some s.name;
                f.class_index <- Some ain_s.index;
                f.is_private <- !in_private;
                self#visit_fundecl f
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
class type_resolve_visitor ctx ~decl_only =
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

    method! visit_fundecl decl =
      (if decl.is_lambda then
         match self#env#current_class with
         | Some (Struct (name, index)) ->
             decl.class_name <- Some name;
             decl.class_index <- Some index
         | _ -> ());
      if decl_only then super#visit_fundecl { decl with body = None }
      else super#visit_fundecl decl

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
      super#visit_declaration decl
  end

let resolve_types ?(decl_only = false) ctx decls =
  (new type_resolve_visitor ctx ~decl_only)#visit_toplevel decls

let check_builtin_library builtin_type =
  (* All functions in HLL for a built-in type T must have a first argument of
     type ref T. *)
  List.iter ~f:(fun func ->
      match func.params with
      | [] ->
          compile_error "builtin HLL function must have at least one parameter"
            (ASTDeclaration (Function func))
      | param :: _ ->
          if not (Poly.equal param.type_spec.ty (Ref builtin_type)) then
            compile_error
              (Printf.sprintf "first parameter must be of type ref %s"
                 (jaf_type_to_string builtin_type))
              (ASTVariable param))

let define_library ctx decls hll_name import_name =
  let functions =
    List.map decls ~f:(function
      | Function f -> f
      | decl ->
          compiler_bug "unexpected declaration in .hll file"
            (Some (ASTDeclaration decl)))
  in
  (if ctx.version >= 800 then
     match import_name with
     | "Int" -> check_builtin_library Int functions
     | "Float" -> check_builtin_library Float functions
     | "String" -> check_builtin_library String functions
     | "Array" -> check_builtin_library (Array HLLParam) functions
     | "Delegate" -> check_builtin_library (Delegate None) functions
     | _ -> ());
  let lib =
    match Ain.get_library_index ctx.ain hll_name with
    | Some i -> Ain.get_library_by_index ctx.ain i
    | None -> Ain.add_library ctx.ain hll_name
  in
  Ain.write_library ctx.ain
    { lib with functions = List.map ~f:jaf_to_ain_hll_function functions };
  let functions =
    Hashtbl.create_with_key_exn
      (module String)
      ~get_key:(fun (d : fundecl) -> d.name)
      functions
  in
  Hashtbl.set ctx.libraries ~key:import_name ~data:{ hll_name; functions }
