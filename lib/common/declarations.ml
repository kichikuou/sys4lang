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

(* Registration puts the names of declarations in the tables of the context,
   and gives numbers to types. It does not read function bodies. *)

(* The type as it is written in the source. The declarations of a function are
   compared in this form, because registration can precede or follow the
   resolution of the other declaration. *)
let rec source_type = function
  | Struct (name, _) | FuncType (Some (name, _)) | Delegate (Some (name, _)) ->
      Unresolved name
  | IMainSystem -> Unresolved "IMainSystem"
  | Ref t -> Ref (source_type t)
  | Array t -> Array (source_type t)
  | Wrap t -> Wrap (source_type t)
  | t -> t

let same_signature (a : fundecl) (b : fundecl) =
  let source_ft f =
    let params, return = ft_of_fundecl f in
    (List.map params ~f:source_type, source_type return)
  in
  ft_compatible (source_ft a) (source_ft b)

(* Default argument values and access modifiers are specified in the
   declaration. The definition gets them from the declaration. *)
let inherit_declaration (decl : fundecl) (def : fundecl) =
  List.iter2_exn def.params decl.params ~f:(fun p d -> p.initval <- d.initval);
  def.is_private <- decl.is_private

let register_function ctx (f : fundecl) =
  let name = mangled_name f in
  let node = ASTDeclaration (Function f) in
  let entries = Hashtbl.find_multi ctx.functions name in
  let entry =
    List.find entries ~f:(fun e -> same_signature f (entry_fundecl e))
  in
  match (entry, f.body) with
  | None, _ ->
      if not (List.is_empty entries) then
        compile_error "Function signature mismatch" node;
      Hashtbl.set ctx.functions ~key:name ~data:[ new_function_entry f ]
  | Some { def = Some _; _ }, Some _ ->
      compile_error "Duplicate function definition" node
  | Some ({ def = None; decl } as entry), Some _ ->
      Option.iter decl ~f:(fun d ->
          List.iter f.params ~f:(fun p ->
              if Option.is_some p.initval then
                compile_error
                  "Default argument values must be specified in the declaration"
                  (ASTVariable p));
          inherit_declaration d f);
      entry.def <- Some f
  | Some { decl = Some _; _ }, None ->
      (* A repeated declaration adds nothing. *)
      ()
  | Some ({ decl = None; def } as entry), None ->
      Option.iter def ~f:(inherit_declaration f);
      entry.decl <- Some f

let register_global ctx decl (g : variable) =
  match Hashtbl.add ctx.globals ~key:g.name ~data:g with
  | `Duplicate ->
      compile_error "duplicate global definition" (ASTDeclaration decl)
  | `Ok -> ()

(* A member variable hides a method of the same name. *)
let add_method_member (s : jaf_struct) name =
  Hashtbl.add s.members ~key:name ~data:MemberMethod |> ignore

let register_struct ctx (s : structdecl) =
  if Hashtbl.mem ctx.structs s.name then
    compile_error "duplicate struct definition" (ASTDeclaration (StructDef s));
  let unqualified_name = snd (Util.parse_qualified_name s.name) in
  let index = number_of_name ctx.struct_numbers s.name in
  let jaf_s = new_jaf_struct s.name s.loc index in
  Hashtbl.add_exn ctx.structs ~key:s.name ~data:jaf_s;
  let in_private = ref s.is_class in
  let register_method (f : fundecl) =
    f.class_name <- Some s.name;
    f.class_index <- Some index;
    f.is_private <- !in_private;
    register_function ctx f
  in
  let register_variable (v : variable) =
    v.is_private <- !in_private;
    match Hashtbl.find jaf_s.members v.name with
    | Some (MemberVariable _) ->
        compile_error "duplicate member variable declaration" (ASTVariable v)
    | Some MemberMethod | None ->
        Hashtbl.set jaf_s.members ~key:v.name ~data:(MemberVariable v)
  in
  List.iter s.decls ~f:(function
    | AccessSpecifier Public -> in_private := false
    | AccessSpecifier Private -> in_private := true
    | Constructor f ->
        if not (String.equal f.name unqualified_name) then
          compile_error "constructor name doesn't match struct name"
            (ASTDeclaration (Function f));
        register_method f
    | Destructor f ->
        if not (String.equal f.name ("~" ^ unqualified_name)) then
          compile_error "destructor name doesn't match struct name"
            (ASTDeclaration (Function f));
        register_method f
    | Method f ->
        add_method_member jaf_s f.name;
        register_method f
    | MemberDecl ds -> List.iter ds.vars ~f:register_variable)

let register_declaration ctx decl =
  match decl with
  | Global ds -> List.iter ds.vars ~f:(register_global ctx decl)
  | GlobalGroup gg ->
      if ctx.version < 500 then
        compile_error "Global groups require AIN version 5 or later"
          (ASTDeclaration decl);
      List.iter gg.vardecls ~f:(fun ds ->
          List.iter ds.vars ~f:(register_global ctx (Global ds)))
  | Function ({ class_name = Some class_name; _ } as f) ->
      (* A generated method. *)
      Option.iter (Hashtbl.find ctx.structs class_name) ~f:(fun s ->
          add_method_member s f.name);
      register_function ctx f
  | Function f ->
      (* An out-of-class definition of a method. *)
      (match Util.parse_qualified_name f.name with
      | None, _ -> ()
      | Some qual, name -> (
          match Hashtbl.find ctx.structs qual with
          | None -> ()
          | Some s ->
              f.name <- name;
              f.class_name <- Some qual;
              f.class_index <- Some s.index;
              if not (Hashtbl.mem ctx.functions (mangled_name f)) then
                compile_error
                  (f.name ^ " is not declared in class " ^ qual)
                  (ASTDeclaration decl)));
      register_function ctx f
  | FuncTypeDef f -> (
      match Hashtbl.add ctx.functypes ~key:f.name ~data:f with
      | `Duplicate ->
          compile_error "duplicate functype definition" (ASTDeclaration decl)
      | `Ok -> f.index <- Some (number_of_name ctx.functype_numbers f.name))
  | DelegateDef f -> (
      match Hashtbl.add ctx.delegates ~key:f.name ~data:f with
      | `Duplicate ->
          compile_error "duplicate delegate definition" (ASTDeclaration decl)
      | `Ok -> f.index <- Some (number_of_name ctx.delegate_numbers f.name))
  | StructDef s -> register_struct ctx s
  | Enum _ -> compile_error "enum types not yet supported" (ASTDeclaration decl)

let register ctx decls = List.iter decls ~f:(register_declaration ctx)

(* Unregistration removes what the registration of a declaration put in the
   tables. The numbers of types stay. The other declaration of a function stays
   in its entry. *)

let remove_if_same table name value =
  match Hashtbl.find table name with
  | Some v when phys_equal v value -> Hashtbl.remove table name
  | _ -> ()

let unregister_function ctx (f : fundecl) =
  Hashtbl.change ctx.functions (mangled_name f) ~f:(fun entries ->
      let remove = function Some d when phys_equal d f -> None | d -> d in
      let entries =
        List.filter (Option.value entries ~default:[]) ~f:(fun e ->
            e.decl <- remove e.decl;
            e.def <- remove e.def;
            Option.is_some e.decl || Option.is_some e.def)
      in
      if List.is_empty entries then None else Some entries)

let unregister_declaration ctx decl =
  let unregister_globals (ds : vardecls) =
    List.iter ds.vars ~f:(fun g -> remove_if_same ctx.globals g.name g)
  in
  match decl with
  | Global ds -> unregister_globals ds
  | GlobalGroup gg -> List.iter gg.vardecls ~f:unregister_globals
  | Function f -> unregister_function ctx f
  | FuncTypeDef f -> remove_if_same ctx.functypes f.name f
  | DelegateDef f -> remove_if_same ctx.delegates f.name f
  | StructDef s ->
      (match Hashtbl.find ctx.structs s.name with
      | Some jaf_s when phys_equal jaf_s.loc s.loc ->
          Hashtbl.remove ctx.structs s.name
      | _ -> ());
      List.iter s.decls ~f:(function
        | Constructor f | Destructor f | Method f -> unregister_function ctx f
        | AccessSpecifier _ | MemberDecl _ -> ())
  | Enum _ -> ()

let unregister ctx decls = List.iter decls ~f:(unregister_declaration ctx)

(*
 * AST pass to resolve HLL-specific type aliases.
 *)
class hll_type_resolve_visitor =
  object
    inherit ivisitor

    method! visit_type_specifier ts =
      match ts.ty with
      | Unresolved "intp" -> ts.ty <- Ref Int
      | Unresolved "floatp" -> ts.ty <- Ref Float
      | Unresolved "stringp" -> ts.ty <- Ref String
      | Unresolved "boolp" -> ts.ty <- Ref Bool
      | _ -> ()
  end

(*
 * AST pass to resolve user-defined types (struct/enum/function types).
 *)
class type_resolve_visitor ctx =
  object (self)
    inherit ivisitor as super

    method resolve_type name node =
      match Hashtbl.find ctx.structs name with
      | Some s -> Struct (name, s.index)
      | None -> (
          match Hashtbl.find ctx.functypes name with
          | Some ft -> FuncType (Some (name, Option.value_exn ft.index))
          | None -> (
              match Hashtbl.find ctx.delegates name with
              | Some dg -> Delegate (Some (name, Option.value_exn dg.index))
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

    (* A lambda belongs to the class of the enclosing function. *)
    method! visit_fundecl decl =
      (if decl.is_lambda then
         match self#env#current_function with
         | Some parent ->
             decl.class_name <- parent.class_name;
             decl.class_index <- parent.class_index
         | None -> ());
      super#visit_fundecl decl

    method! visit_declaration decl =
      (match decl with
      | Enum _ ->
          compile_error "enum types not yet supported" (ASTDeclaration decl)
      | _ -> ());
      super#visit_declaration decl
  end

(* Resolves the type specifiers in [decls]. All types that [decls] refer to
   must be registered. *)
let resolve ctx decls = (new type_resolve_visitor ctx)#visit_toplevel decls

let resolve_hll ctx decls =
  (new hll_type_resolve_visitor)#visit_toplevel decls;
  resolve ctx decls

let check_builtin_params builtin_type =
  (* All functions in HLL for a built-in type T must have a first argument of
     type ref T. *)
  List.iter ~f:(fun func ->
      match func.params with
      | [] ->
          compile_error "builtin HLL function must have at least one parameter"
            (ASTDeclaration (Function func))
      | param :: _ ->
          if not (jaf_type_equal param.type_spec.ty (Ref builtin_type)) then
            compile_error
              (Printf.sprintf "first parameter must be of type ref %s"
                 (jaf_type_to_string builtin_type))
              (ASTVariable param))

let check_library ctx import_name (functions : fundecl list) =
  (match
     List.find_a_dup functions ~compare:(fun a b ->
         String.compare a.name b.name)
   with
  | Some f ->
      compile_error
        ("Duplicate HLL function: " ^ f.name)
        (ASTDeclaration (Function f))
  | None -> ());
  if ctx.version >= 800 then
    match import_name with
    | "Int" -> check_builtin_params Int functions
    | "Float" -> check_builtin_params Float functions
    | "String" -> check_builtin_params String functions
    | "Array" -> check_builtin_params (Array HLLParam) functions
    | "Delegate" -> check_builtin_params (Delegate None) functions
    | _ -> ()

(* Registers the library that the resolved declarations of a .hll file make,
   and returns it. *)
let register_library ctx decls ~hll_name ~import_name =
  let functions =
    List.map decls ~f:(function
      | Function f -> f
      | decl ->
          compiler_bug "unexpected declaration in .hll file"
            (Some (ASTDeclaration decl)))
  in
  check_library ctx import_name functions;
  let lib = new_library hll_name None functions in
  (match Hashtbl.add ctx.libraries ~key:import_name ~data:lib with
  | `Duplicate -> raise_message ("Duplicate HLL import name: " ^ import_name)
  | `Ok -> ());
  lib

let unregister_library ctx ~import_name (lib : library) =
  remove_if_same ctx.libraries import_name lib
