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
open Jaf

type t = {
  context : context;
  structures : (string, structdecl) Hashtbl.t;
  function_declarations : (string, fundecl list) Hashtbl.t;
  methods : (string, fundecl) Hashtbl.t;
  new_functions : string Hash_set.t;
  selected_structures : string Hash_set.t;
  added_types : (string * string) list;
  new_types : string Hash_set.t;
  selected_libraries : string Hash_set.t;
  mutable added_entries_rev : (string * string) list;
}

let context t = t.context
let added_types t = t.added_types
let added_entries t = List.rev t.added_entries_rev

let record_addition t kind name =
  t.added_entries_rev <- (kind, name) :: t.added_entries_rev

let error kind name loc = CompileError.raise ("Patch " ^ kind ^ ": " ^ name) loc

let variable_types vars =
  List.map vars ~f:(fun (v : Ain.Variable.t) -> v.value_type)

let find_type t name loc =
  let ctx = t.context in
  if Hashtbl.mem t.structures name then
    match Hashtbl.find ctx.structs name with
    | Some s -> Struct (name, s.index)
    | None -> error "type is absent from input AIN" name loc
  else
    match Hashtbl.find ctx.functypes name with
    | Some { index = Some index; _ } -> FuncType (Some (name, index))
    | Some _ -> error "type is absent from input AIN" name loc
    | None -> (
        match Hashtbl.find ctx.delegates name with
        | Some { index = Some index; _ } -> Delegate (Some (name, index))
        | Some _ -> error "type is absent from input AIN" name loc
        | None ->
            if String.equal name "IMainSystem" then IMainSystem
            else error "undefined source type" name loc)

let resolve_type t (ts : type_specifier) =
  let rec resolve = function
    | Unresolved name -> find_type t name ts.location
    | Ref ty -> Ref (resolve ty)
    | Array ty -> Array (resolve ty)
    | Wrap ty -> Wrap (resolve ty)
    | ty -> ty
  in
  ts.ty <- resolve ts.ty

let resolve_signature t f =
  resolve_type t f.return;
  List.iter f.params ~f:(fun p -> resolve_type t p.type_spec);
  Option.iter f.class_name ~f:(fun name ->
      match find_type t name f.loc with
      | Struct (_, index) -> f.class_index <- Some index
      | _ -> error "method owner is not a structure" name f.loc)

let check_source_function t f =
  let name = mangled_name f in
  Option.iter f.class_name ~f:(fun _ ->
      match Hashtbl.find t.methods name with
      | None -> error "method is not declared in class" name f.loc
      | Some declaration -> f.is_private <- declaration.is_private);
  List.iter (Hashtbl.find_multi t.function_declarations name) ~f:(fun decl ->
      if not (Poly.equal (ft_of_fundecl f) (ft_of_fundecl decl)) then
        error "source function signature mismatch" name f.loc);
  (* Copy defaults by position, keeping the definition's parameter records and
     names. The selected body takes precedence over reference bodies. *)
  List.iter (Hashtbl.find_multi t.function_declarations name) ~f:(fun decl ->
      f.params <-
        List.map2_exn f.params decl.params ~f:(fun param source ->
            if Option.is_some param.initval then param
            else { param with initval = source.initval }))

let check_function t f base =
  check_source_function t f;
  let vars = jaf_to_ain_variables f.params in
  if
    (not
       (Poly.equal (jaf_to_ain_type f.return.ty) base.Ain.Function.return_type))
    || List.length vars <> base.nr_args
    || (not
          (Poly.equal (variable_types vars)
             (variable_types (List.take base.vars base.nr_args))))
    || Bool.(f.is_label <> base.is_label || f.is_lambda <> base.is_lambda)
  then error "function signature mismatch" base.name f.loc;
  f.index <- Some base.index

let validate_function t name loc =
  let f =
    match Hashtbl.find t.context.functions name with
    | Some f -> f
    | None -> error "undefined source function" name loc
  in
  (if Hash_set.mem t.new_functions name then check_source_function t f
   else
     match Ain.get_function t.context.ain name with
     | Some base -> check_function t f base
     | None -> error "function is absent from output" name loc);
  f

let validate_global t (v : variable) =
  if not v.is_const then (
    let base =
      match Ain.get_global t.context.ain v.name with
      | Some v -> v
      | None -> error "global is absent from input AIN" v.name v.location
    in
    if not (Poly.equal (jaf_to_ain_type v.type_spec.ty) base.value_type) then
      error "global type mismatch" v.name v.location;
    v.index <- Some base.index)

let validate_hll_function t import_name (f : fundecl) =
  let ctx = t.context in
  let lib = Hashtbl.find_exn ctx.libraries import_name in
  let lib_no =
    match Ain.get_library_index ctx.ain lib.hll_name with
    | Some i -> i
    | None -> error "HLL is absent from input AIN" lib.hll_name f.loc
  in
  let index =
    match Ain.get_library_function_index ctx.ain lib_no f.name with
    | Some i -> i
    | None -> error "HLL function is absent from input AIN" f.name f.loc
  in
  let base = (Ain.get_library_by_index ctx.ain lib_no).functions.(index) in
  let source = jaf_to_ain_hll_function f in
  let types args =
    List.map args ~f:(fun (a : Ain.Library.Argument.t) -> a.value_type)
  in
  if
    (not (Poly.equal source.return_type base.return_type))
    || not (Poly.equal (types source.arguments) (types base.arguments))
  then
    error "HLL function signature mismatch" (import_name ^ "." ^ f.name) f.loc

let source_members (s : structdecl) =
  List.concat_map s.decls ~f:(function
    | MemberDecl ds when not ds.is_const_decls -> ds.vars
    | _ -> [])

let layout vars =
  List.map vars ~f:(fun (v : Ain.Variable.t) ->
      (* Names of ref-scalar padding slots are not source names. *)
      ( (if Poly.equal v.value_type Ain.Type.Void then "" else v.name),
        v.value_type ))

let validate_structure t ~allow_suffix (s : structdecl) =
  let base =
    match Ain.get_struct t.context.ain s.name with
    | Some s -> s
    | None -> error "type is absent from input AIN" s.name s.loc
  in
  let source_members = source_members s in
  let members = jaf_to_ain_variables source_members in
  let source_layout = layout members in
  let base_layout = layout base.members in
  let compatible =
    if allow_suffix then
      List.length source_layout >= List.length base_layout
      && Poly.equal
           (List.take source_layout (List.length base_layout))
           base_layout
    else Poly.equal source_layout base_layout
  in
  if not compatible then error "structure layout mismatch" s.name s.loc;
  let index = ref 0 in
  List.iter source_members ~f:(fun v ->
      v.index <- Some !index;
      index := !index + if is_ref_scalar v.type_spec.ty then 2 else 1);
  if allow_suffix && List.length members > List.length base.members then
    Ain.write_struct t.context.ain
      {
        base with
        members = base.members @ List.drop members (List.length base.members);
      }

let validate_function_type t get (f : fundecl) =
  let base =
    match get t.context.ain f.name with
    | Some ft -> ft
    | None -> error "type is absent from input AIN" f.name f.loc
  in
  let vars = jaf_to_ain_variables f.params in
  if
    (not
       (Poly.equal
          (jaf_to_ain_type f.return.ty)
          base.Ain.FunctionType.return_type))
    || List.length vars <> base.nr_arguments
    || not (Poly.equal (variable_types vars) (variable_types base.variables))
  then error "function type signature mismatch" f.name f.loc

type type_kind = StructKind | FuncTypeKind | DelegateKind

let base_type_name = function
  | StructKind -> "struct/class"
  | FuncTypeKind -> "functype"
  | DelegateKind -> "delegate"

let exists_in_base ain name = function
  | StructKind -> Option.is_some (Ain.get_struct_index ain name)
  | FuncTypeKind -> Option.is_some (Ain.get_functype_index ain name)
  | DelegateKind -> Option.is_some (Ain.get_delegate_index ain name)

let prepare ain (program : PatchSources.t) =
  let type_declarations =
    List.concat_map program.sources ~f:(function
      | PatchSources.Jaf source ->
          List.filter_map source.declarations ~f:(function
            | StructDef s ->
                Some
                  ( StructKind,
                    (if s.is_class then "class" else "struct"),
                    s.name,
                    s.loc )
            | FuncTypeDef f -> Some (FuncTypeKind, "functype", f.name, f.loc)
            | DelegateDef f -> Some (DelegateKind, "delegate", f.name, f.loc)
            | _ -> None)
      | Hll _ -> [])
  in
  let selected_classes =
    List.map (PatchSources.selected_classes program) ~f:(fun s -> s.name)
  in
  let selected_types =
    Hash_set.of_list
      (module String)
      (selected_classes
      @ List.map (PatchSources.selected_function_types program) ~f:(fun f ->
          f.name))
  in
  let source_types = Hashtbl.create (module String) in
  let added_types =
    List.filter_map type_declarations ~f:(fun (kind, label, name, loc) ->
        (match Hashtbl.add source_types ~key:name ~data:(kind, label) with
        | `Ok -> ()
        | `Duplicate ->
            let previous_kind, previous_label =
              Hashtbl.find_exn source_types name
            in
            if Poly.equal previous_kind kind then
              error "duplicate source type declaration" name loc
            else
              error
                ("type name collision (" ^ previous_label ^ " and " ^ label
               ^ ")")
                name loc);
        let base_kinds =
          List.filter
            [ StructKind; FuncTypeKind; DelegateKind ]
            ~f:(exists_in_base ain name)
        in
        List.iter base_kinds ~f:(fun base_kind ->
            if not (Poly.equal kind base_kind) then
              error
                ("type name collision (source " ^ label ^ ", input "
               ^ base_type_name base_kind ^ ")")
                name loc);
        if List.is_empty base_kinds then (
          if not (Hash_set.mem selected_types name) then
            CompileError.raise
              ("New type " ^ name ^ " is not selected; select " ^ name
             ^ " or pass its source with --source.")
              loc;
          Some (label, name))
        else None)
  in
  let table () = Hashtbl.create (module String) in
  let context =
    {
      ain;
      version = (Ain.version ain * 100) + Ain.minor_version ain;
      globals = table ();
      structs = table ();
      functions = table ();
      functypes = table ();
      delegates = table ();
      libraries = table ();
    }
  in
  let t =
    {
      context;
      added_entries_rev = [];
      selected_libraries =
        Hash_set.of_list
          (module String)
          (PatchSources.selected_libraries program);
      added_types;
      new_types = Hash_set.of_list (module String) (List.map added_types ~f:snd);
      structures = table ();
      function_declarations = table ();
      methods = table ();
      new_functions =
        Hash_set.of_list
          (module String)
          (List.filter_map program.output_definitions ~f:(fun d ->
               if Option.is_none (Ain.get_function ain d.name) then Some d.name
               else None));
      selected_structures = Hash_set.of_list (module String) selected_classes;
    }
  in
  let add table name value loc =
    match Hashtbl.add table ~key:name ~data:value with
    | `Ok -> ()
    | `Duplicate -> error "duplicate source declaration" name loc
  in
  let register_function ?class_name (f : fundecl) =
    let owner, name =
      match class_name with
      | Some _ -> (class_name, f.name)
      | None -> Util.parse_qualified_name f.name
    in
    f.class_name <- owner;
    f.name <- name;
    let key = mangled_name f in
    Hashtbl.add_multi t.function_declarations ~key ~data:f;
    Option.iter class_name ~f:(fun _ ->
        if not (Hashtbl.mem t.methods key) then
          Hashtbl.set t.methods ~key ~data:f);
    f.index <- Option.map (Ain.get_function ain key) ~f:(fun f -> f.index);
    if not (Hashtbl.mem context.functions key) then
      Hashtbl.set context.functions ~key ~data:f
  in
  let register_globals (ds : vardecls) =
    List.iter ds.vars ~f:(fun v ->
        v.index <-
          (if v.is_const then None
           else Option.map (Ain.get_global ain v.name) ~f:(fun g -> g.index));
        add context.globals v.name v v.location)
  in
  let register = function
    | Function f -> register_function f
    | Global ds -> register_globals ds
    | GlobalGroup gg -> List.iter gg.vardecls ~f:register_globals
    | StructDef s ->
        add t.structures s.name s s.loc;
        let members = table () in
        let private_access = ref s.is_class in
        List.iter s.decls ~f:(function
          | MemberDecl ds ->
              List.iter ds.vars ~f:(fun v ->
                  v.is_private <- !private_access;
                  add members v.name v v.location)
          | Method f | Constructor f | Destructor f ->
              f.is_private <- !private_access;
              register_function ~class_name:s.name f
          | AccessSpecifier Public -> private_access := false
          | AccessSpecifier Private -> private_access := true);
        List.iter s.decls ~f:(function
          | Method f when Hashtbl.mem members f.name ->
              error "method conflicts with data member" (mangled_name f) f.loc
          | _ -> ());
        let index =
          match Ain.get_struct_index ain s.name with
          | Some index -> index
          | None -> (Ain.add_struct ain s.name).index
        in
        Hashtbl.set context.structs ~key:s.name
          ~data:{ name = s.name; loc = s.loc; index; members }
    | FuncTypeDef f ->
        f.index <-
          Some
            (match Ain.get_functype_index ain f.name with
            | Some index -> index
            | None -> (Ain.add_functype ain f.name).index);
        add context.functypes f.name f f.loc
    | DelegateDef f ->
        f.index <-
          Some
            (match Ain.get_delegate_index ain f.name with
            | Some index -> index
            | None -> (Ain.add_delegate ain f.name).index);
        add context.delegates f.name f f.loc
    | Enum _ -> ()
  in
  List.iter program.sources ~f:(function
    | PatchSources.Jaf s -> List.iter s.declarations ~f:register
    | Hll s ->
        let functions = table () in
        List.iter s.declarations ~f:(function
          | Function f -> add functions f.name f f.loc
          | _ -> error "invalid HLL declaration" s.name dummy_location);
        add context.libraries s.import_name
          { hll_name = s.name; functions }
          dummy_location);
  (* Body precedence was established while loading; retain declarations even
     when their bodies were superseded. All new type IDs are now reserved,
     but their layouts and signatures have not yet been resolved. *)
  List.iter (Hashtbl.keys context.functions) ~f:(fun key ->
      Option.iter (PatchSources.find_definition program key) ~f:(fun d ->
          Hashtbl.set context.functions ~key ~data:d.declaration));
  t

let resolve t (program : PatchSources.t) =
  let resolve_variables (ds : vardecls) =
    List.iter ds.vars ~f:(fun v -> resolve_type t v.type_spec)
  in
  let resolve_declaration = function
    | Function f -> resolve_signature t f
    | Global ds -> resolve_variables ds
    | GlobalGroup gg -> List.iter gg.vardecls ~f:resolve_variables
    | StructDef s ->
        List.iter s.decls ~f:(function
          | Method f | Constructor f | Destructor f -> resolve_signature t f
          | MemberDecl ds -> resolve_variables ds
          | AccessSpecifier _ -> ())
    | FuncTypeDef f | DelegateDef f -> resolve_signature t f
    | Enum _ -> ()
  in
  List.iter program.sources ~f:(function
    | PatchSources.Jaf source ->
        List.iter source.declarations ~f:resolve_declaration
    | Hll source ->
        Declarations.resolve_hll_types t.context source.declarations;
        List.iter source.declarations ~f:(function
          | Function f -> resolve_signature t f
          | _ -> assert false))

let apply_additions t (program : PatchSources.t) =
  List.iter program.sources ~f:(function
    | PatchSources.Jaf source ->
        List.iter source.declarations ~f:(function
          | FuncTypeDef f when Hash_set.mem t.new_types f.name ->
              Ain.write_functype t.context.ain (jaf_to_ain_functype f)
          | DelegateDef f when Hash_set.mem t.new_types f.name ->
              Ain.write_delegate t.context.ain (jaf_to_ain_functype f)
          | _ -> ())
    | Hll source when Hash_set.mem t.selected_libraries source.import_name ->
        let ain = t.context.ain in
        let library =
          match Ain.get_library_index ain source.name with
          | Some index -> Ain.get_library_by_index ain index
          | None ->
              record_addition t "HLL" source.name;
              Ain.add_library ain source.name
        in
        let additions =
          List.filter_map source.declarations ~f:(function
            | Function f -> (
                match
                  Ain.get_library_function_index ain library.index f.name
                with
                | Some _ -> None
                | None ->
                    record_addition t "HLL function" (source.name ^ "." ^ f.name);
                    Some (jaf_to_ain_hll_function f))
            | _ -> assert false)
        in
        if not (List.is_empty additions) then
          Ain.write_library ain
            {
              library with
              functions =
                Array.append library.functions (Array.of_list additions);
            }
    | Hll _ -> ());
  Hash_set.iter t.selected_structures ~f:(fun name ->
      let s = Hashtbl.find_exn t.structures name in
      validate_structure t ~allow_suffix:true s);
  if PatchSources.rebuild_globals program then (
    List.iter program.global_groups ~f:(fun gg ->
        if Option.is_none (Ain.find_global_group_index t.context.ain gg.name)
        then (
          if Ain.version t.context.ain < 5 then
            error "global groups require AIN v5 or later" gg.name gg.loc;
          ignore (Ain.add_global_group t.context.ain gg.name);
          record_addition t "globalgroup" gg.name));
    let globals =
      List.filter program.globals ~f:(fun (_, v) -> not v.is_const)
    in
    let group_index group v =
      match group with
      | None -> if Ain.version t.context.ain < 5 then 0 else -1
      | Some name -> (
          match Ain.find_global_group_index t.context.ain name with
          | Some index -> index
          | None ->
              error "global group is absent from input AIN" name v.location)
    in
    let existing = Ain.nr_globals t.context.ain in
    List.iteri globals ~f:(fun index (group, v) ->
        let value_type = jaf_to_ain_type v.type_spec.ty in
        let source_group = group_index group v in
        if index < existing then (
          let base = Ain.get_global_by_index t.context.ain index in
          if not (String.equal v.name base.name) then
            error "global declaration order mismatch" v.name v.location;
          if not (Poly.equal value_type base.value_type) then
            error "global type mismatch" v.name v.location;
          if
            Ain.version t.context.ain >= 5
            && source_group <> Ain.get_global_group_index t.context.ain index
          then error "global group mismatch" v.name v.location)
        else
          ignore
            (Ain.write_new_global ~group_index:source_group t.context.ain
               (Ain.Variable.make v.name value_type));
        v.index <- Some index);
    if List.length globals < existing then
      let missing =
        Ain.get_global_by_index t.context.ain (List.length globals)
      in
      error "missing global declaration" missing.name dummy_location)

let validate t (program : PatchSources.t) =
  let validated_functions = Hash_set.create (module String) in
  let validate_function_once f =
    let name = mangled_name f in
    if Hash_set.strict_add validated_functions name |> Result.is_ok then
      ignore (validate_function t name f.loc)
  in
  let validate_globals (ds : vardecls) =
    List.iter ds.vars ~f:(validate_global t)
  in
  let validate_declaration = function
    | Function f -> validate_function_once f
    | Global ds -> validate_globals ds
    | GlobalGroup gg -> List.iter gg.vardecls ~f:validate_globals
    | StructDef s ->
        validate_structure t ~allow_suffix:false s;
        List.iter s.decls ~f:(function
          | Method f | Constructor f | Destructor f -> validate_function_once f
          | MemberDecl _ -> ()
          | AccessSpecifier _ -> ())
    | FuncTypeDef f -> validate_function_type t Ain.get_functype f
    | DelegateDef f -> validate_function_type t Ain.get_delegate f
    | Enum _ -> ()
  in
  List.iter program.sources ~f:(function
    | PatchSources.Jaf source ->
        List.iter source.declarations ~f:validate_declaration
    | Hll source ->
        List.iter source.declarations ~f:(function
          | Function f -> validate_hll_function t source.import_name f
          | _ -> assert false))

let create ain program =
  let t = prepare ain program in
  resolve t program;
  apply_additions t program;
  validate t program;
  t

let bind_initializer_reference t (constructor : fundecl) =
  let owner = Option.value_exn constructor.class_name in
  let name = owner ^ "@2" in
  let f =
    {
      constructor with
      name = "2";
      params = [];
      body = None;
      return = { ty = Void; location = constructor.loc };
      is_private = false;
      index =
        Some (Option.value_exn (Ain.get_function t.context.ain name)).index;
    }
  in
  Hashtbl.set t.context.functions ~key:name ~data:f;
  Hashtbl.set t.methods ~key:name ~data:f;
  (* This internal declaration follows ArrayInit's generation convention. *)
  Hash_set.add t.new_functions name
