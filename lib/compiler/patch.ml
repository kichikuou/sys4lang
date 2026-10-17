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
open CompileError

(* A patch does not change the existing bytecode or table entries of the base
   AIN. It appends new code to the end of the CODE section, and appends new
   entries to the end of each table. A replaced function keeps its FUNC index,
   and only its address, variables, and CRC change. Thus the existing
   CALLFUNC and CALLMETHOD instructions, function pointer values, and struct
   constructors and destructors call the new body.

   The appended code has no EOF instruction and no FNAM entry. sys4dc
   (CodeSection.remove_overridden_functions) uses the last code of each
   function, and decompiles the code after the last EOF to remaining.jaf.

   The base AIN gives the indices and types of the existing entries. The project
   and the --source files give the declarations that the selected code uses.
   Declarations are bound to the base AIN entries by name. The bodies that are
   not selected are removed before registration, so the usual passes run on
   all declarations but check and compile only the selected bodies. *)

type source = {
  path : string;
  debug_path : string;
  origin : [ `Project | `Project_selected | `Extra ];
  kind : [ `Jaf | `Hll of string ];
}

let sprintf = Printf.sprintf

(* [src_no] is the index of [src] in the source list, and [ord] is the position
   of [decl] in that source. *)
type entry = { decl : declaration; src : source; src_no : int; ord : int }

let is_selected_source src =
  match src.origin with `Extra | `Project_selected -> true | `Project -> false

let method_mangled_name class_name name =
  let _, s = Util.parse_qualified_name class_name in
  if String.equal name s then class_name ^ "@0"
  else if String.equal name ("~" ^ s) then class_name ^ "@1"
  else class_name ^ "@" ^ name

let function_mangled_name struct_names (fd : fundecl) =
  match Util.parse_qualified_name fd.name with
  | Some qual, name when Hash_set.mem struct_names qual ->
      method_mangled_name qual name
  | _ -> fd.name

let collect_struct_names entries =
  let names = Hash_set.create (module String) in
  List.iter entries ~f:(fun e ->
      match e.decl with StructDef s -> Hash_set.add names s.name | _ -> ());
  names

(* Calls [f] for every function and method declaration in [entries], with its
   mangled name and the name to show in messages. *)
let iter_fundecls struct_names entries ~f =
  List.iter entries ~f:(fun e ->
      match e.decl with
      | Function fd -> f e (function_mangled_name struct_names fd) fd.name fd
      | StructDef s ->
          List.iter s.decls ~f:(function
            | Constructor fd | Destructor fd | Method fd ->
                f e
                  (method_mangled_name s.name fd.name)
                  (s.name ^ "::" ^ fd.name)
                  fd
            | AccessSpecifier _ | MemberDecl _ -> ())
      | _ -> ())

let is_out_of_class_method struct_names (fd : fundecl) =
  match Util.parse_qualified_name fd.name with
  | Some qual, _ -> Hash_set.mem struct_names qual
  | None, _ -> false

let global_vars_with_group decl =
  match decl with
  | Global ds -> List.map ds.vars ~f:(fun v -> (v, None))
  | GlobalGroup gg ->
      List.concat_map gg.vardecls ~f:(fun ds ->
          List.map ds.vars ~f:(fun v -> (v, Some gg.name)))
  | _ -> []

(* Replaces each declaration in [project] with the declaration of the same kind
   and name in [extras], and returns [project] followed by the remaining
   [extras]. Functions match by mangled name, and globals match by variable.
   Declarations in [extras] do not replace other declarations in [extras]. *)
let replace_declarations project extras =
  let struct_names = collect_struct_names (project @ extras) in
  (* Collect the declarations in [extras] by kind and name. *)
  let ext_structs = Hashtbl.create (module String) in
  let ext_funcs = Hash_set.create (module String) in
  let ext_functypes = Hash_set.create (module String) in
  let ext_delegates = Hash_set.create (module String) in
  let ext_globals = Hashtbl.create (module String) in
  List.iter extras ~f:(fun e ->
      match e.decl with
      | StructDef s -> (
          match Hashtbl.add ext_structs ~key:s.name ~data:e with
          | `Duplicate ->
              compile_error "duplicate struct definition"
                (ASTDeclaration e.decl)
          | `Ok -> ())
      | Function fd ->
          Hash_set.add ext_funcs (function_mangled_name struct_names fd)
      | FuncTypeDef fd -> Hash_set.add ext_functypes fd.name
      | DelegateDef fd -> Hash_set.add ext_delegates fd.name
      | Global _ | GlobalGroup _ ->
          List.iter (global_vars_with_group e.decl) ~f:(fun (v, group) ->
              match Hashtbl.add ext_globals ~key:v.name ~data:(v, group) with
              | `Duplicate ->
                  compile_error "duplicate global definition" (ASTVariable v)
              | `Ok -> ())
      | Enum _ -> ());
  (* Remove the project declarations that [extras] replace. Replacement structs
     and globals go to the position of the project declaration, because
     out-of-class method definitions must come after their class, and global
     indices follow the declaration order. *)
  let project_struct_names = Hash_set.create (module String) in
  let moved_globals = Hash_set.create (module String) in
  let replace_vars group (ds : vardecls) =
    let vars =
      List.map ds.vars ~f:(fun v ->
          match Hashtbl.find ext_globals v.name with
          | None -> v
          | Some (ext_v, ext_group) ->
              if not (Option.equal String.equal group ext_group) then
                compile_error
                  (sprintf
                     "Global %s must be declared in the same group as in the \
                      project"
                     v.name)
                  (ASTVariable ext_v);
              Hash_set.add moved_globals v.name;
              ext_v)
    in
    { ds with vars }
  in
  let project =
    List.filter_map project ~f:(fun e ->
        match e.decl with
        | StructDef s -> (
            Hash_set.add project_struct_names s.name;
            match Hashtbl.find ext_structs s.name with
            | Some ext -> Some ext
            | None -> Some e)
        | Function fd ->
            if Hash_set.mem ext_funcs (function_mangled_name struct_names fd)
            then None
            else Some e
        | FuncTypeDef fd ->
            if Hash_set.mem ext_functypes fd.name then None else Some e
        | DelegateDef fd ->
            if Hash_set.mem ext_delegates fd.name then None else Some e
        | Global ds -> Some { e with decl = Global (replace_vars None ds) }
        | GlobalGroup gg ->
            Some
              {
                e with
                decl =
                  GlobalGroup
                    {
                      gg with
                      vardecls =
                        List.map gg.vardecls ~f:(replace_vars (Some gg.name));
                    };
              }
        | Enum _ -> Some e)
  in
  (* Remove the structs and globals that moved into [project]. *)
  let remove_moved_vars (ds : vardecls) =
    {
      ds with
      vars =
        List.filter ds.vars ~f:(fun v ->
            not (Hash_set.mem moved_globals v.name));
    }
  in
  let extras =
    List.filter_map extras ~f:(fun e ->
        match e.decl with
        | StructDef s when Hash_set.mem project_struct_names s.name -> None
        | Global ds -> Some { e with decl = Global (remove_moved_vars ds) }
        | GlobalGroup gg ->
            Some
              {
                e with
                decl =
                  GlobalGroup
                    {
                      gg with
                      vardecls = List.map gg.vardecls ~f:remove_moved_vars;
                    };
              }
        | _ -> Some e)
  in
  project @ extras

(* The declarations that the patch compiles or adds. [functions] maps mangled
   names to the declarations whose bodies are compiled. *)
type selection = {
  functions : (string, fundecl * source) Hashtbl.t;
  structs : string Hash_set.t;
  functypes : string Hash_set.t;
  delegates : string Hash_set.t;
  rebuild_globals : bool;
}

let declares_globals decl =
  match decl with
  | GlobalGroup _ -> true
  | Global ds -> List.exists ds.vars ~f:(fun v -> not v.is_const)
  | _ -> false

let defined_twice display (a : source) (b : source) =
  raise_message
    (sprintf "Function %s is defined in both %s and %s" display a.path b.path)

let select_function (sel : selection) mangled display (fd : fundecl) src =
  match Hashtbl.find sel.functions mangled with
  | Some (_, prev_src) -> defined_twice display prev_src src
  | None -> Hashtbl.set sel.functions ~key:mangled ~data:(fd, src)

let select_from_sources (sel : selection) struct_names entries =
  iter_fundecls struct_names entries ~f:(fun e mangled display fd ->
      if is_selected_source e.src && Option.is_some fd.body then
        select_function sel mangled display fd e.src);
  List.iter entries ~f:(fun e ->
      if is_selected_source e.src then
        match e.decl with
        | StructDef s -> Hash_set.add sel.structs s.name
        | FuncTypeDef fd -> Hash_set.add sel.functypes fd.name
        | DelegateDef fd -> Hash_set.add sel.delegates fd.name
        | _ -> ())

(* The names of all declarations, used to resolve target names. A [funcs] value
   is [None] if no declaration of the function has a body. *)
type name_index = {
  funcs : (string, (fundecl * source) option) Hashtbl.t;
  struct_decls : (string, structdecl) Hashtbl.t;
  functype_names : string Hash_set.t;
  delegate_names : string Hash_set.t;
  global_names : string Hash_set.t;
  class_consts : string Hash_set.t;
  enum_names : string Hash_set.t;
}

let build_name_index (sel : selection) struct_names entries =
  let idx =
    {
      funcs = Hashtbl.create (module String);
      struct_decls = Hashtbl.create (module String);
      functype_names = Hash_set.create (module String);
      delegate_names = Hash_set.create (module String);
      global_names = Hash_set.create (module String);
      class_consts = Hash_set.create (module String);
      enum_names = Hash_set.create (module String);
    }
  in
  (* A function can have only one body, but a body in a selected source
     overrides the other bodies. *)
  iter_fundecls struct_names entries ~f:(fun e mangled display fd ->
      Hashtbl.update idx.funcs mangled ~f:(fun prev ->
          match (Option.join prev, fd.body) with
          | Some (_, src), Some _ when not (Hashtbl.mem sel.functions mangled)
            ->
              defined_twice display src e.src
          | None, Some _ -> Some (fd, e.src)
          | def, _ -> def));
  List.iter entries ~f:(fun e ->
      match e.decl with
      | StructDef s ->
          Hashtbl.set idx.struct_decls ~key:s.name ~data:s;
          List.iter s.decls ~f:(function
            | MemberDecl ds when ds.is_const_decls ->
                List.iter ds.vars ~f:(fun v ->
                    Hash_set.add idx.class_consts (s.name ^ "::" ^ v.name))
            | _ -> ())
      | FuncTypeDef fd -> Hash_set.add idx.functype_names fd.name
      | DelegateDef fd -> Hash_set.add idx.delegate_names fd.name
      | Global _ -> ()
      | GlobalGroup gg -> Hash_set.add idx.global_names gg.name
      | Enum { name = Some name; _ } -> Hash_set.add idx.enum_names name
      | Enum { name = None; _ } | Function _ -> ());
  List.iter entries ~f:(fun e ->
      List.iter (global_vars_with_group e.decl) ~f:(fun (v, _) ->
          Hash_set.add idx.global_names v.name));
  idx

let select_target (sel : selection) idx target =
  let select_function_by_name mangled =
    if Hashtbl.mem sel.functions mangled then `Selected
    else
      match Hashtbl.find idx.funcs mangled with
      | None -> `Unknown
      | Some None -> `No_definition
      | Some (Some (fd, src)) ->
          Hashtbl.set sel.functions ~key:mangled ~data:(fd, src);
          `Selected
  in
  let no_definition () =
    raise_message (sprintf "No definition of %s found" target)
  in
  let unknown () =
    if Hash_set.mem idx.global_names target then
      raise_message
        (sprintf "Globals cannot be selected by name; use --globals: %s" target)
    else if Hash_set.mem idx.class_consts target then
      raise_message (sprintf "Constants cannot be patch targets: %s" target)
    else if Hash_set.mem idx.enum_names target then
      raise_message "Enum types are not supported"
    else raise_message (sprintf "Unknown patch target: %s" target)
  in
  match Util.parse_qualified_name target with
  | Some qual, name when Hashtbl.mem idx.struct_decls qual -> (
      match select_function_by_name (method_mangled_name qual name) with
      | `Selected -> ()
      | `No_definition -> no_definition ()
      | `Unknown -> unknown ())
  | _ -> (
      let func = select_function_by_name target in
      let others =
        List.filter_map
          [
            (Hashtbl.mem idx.struct_decls target, sel.structs);
            (Hash_set.mem idx.functype_names target, sel.functypes);
            (Hash_set.mem idx.delegate_names target, sel.delegates);
          ]
          ~f:(fun (found, set) -> if found then Some set else None)
      in
      List.iter others ~f:(fun set -> Hash_set.add set target);
      match func with
      | `Selected -> ()
      | `No_definition when List.is_empty others -> no_definition ()
      | `Unknown when List.is_empty others -> unknown ()
      | `No_definition | `Unknown -> ())

let strip_bodies (sel : selection) struct_names entries =
  iter_fundecls struct_names entries ~f:(fun _ mangled _ fd ->
      if Option.is_some fd.body then
        match Hashtbl.find sel.functions mangled with
        | Some (selected, _) when phys_equal selected fd -> ()
        | _ -> fd.body <- None);
  (* Remove the out-of-class method definitions that have no body. Such a
     definition only repeats the in-class declaration, and causes an error if a
     replacement class does not declare the method. *)
  List.filter entries ~f:(fun e ->
      match e.decl with
      | Function fd ->
          Option.is_some fd.body || not (is_out_of_class_method struct_names fd)
      | _ -> true)

class jump_check_visitor ctx =
  object
    inherit ivisitor ctx as super

    method! visit_statement stmt =
      (match stmt.node with
      | Jump _ | Jumps _ ->
          compile_error "Scenario labels cannot be patched in AIN version 1"
            (ASTStatement stmt)
      | _ -> ());
      super#visit_statement stmt
  end

(* In AIN version 1, scenario labels are in SLBL instead of FUNC, and jump uses
   the SLBL address. Appended code cannot change these addresses. *)
let check_v1_restrictions (ctx : context) (sel : selection) =
  Hashtbl.iter sel.functions ~f:(fun (fd, _) ->
      if fd.is_label then
        compile_error "Scenario labels cannot be patched in AIN version 1"
          (ASTDeclaration (Function fd));
      (new jump_check_visitor ctx)#visit_fundecl fd)

(* The number of entries in each table of the base AIN before the patch. An
   index below this number refers to an existing entry, and other indices refer
   to entries that the patch adds. *)
type base_info = {
  nr_functions : int;
  nr_globals : int;
  nr_structs : int;
  nr_functypes : int;
  nr_delegates : int;
}

let base_info ain =
  {
    nr_functions = Ain.nr_functions ain;
    nr_globals = Ain.nr_globals ain;
    nr_structs = Ain.nr_structs ain;
    nr_functypes = Ain.nr_functypes ain;
    nr_delegates = Ain.nr_delegates ain;
  }

let in_base nr i = Option.filter i ~f:(fun i -> i < nr)

let find_base_function ain (base : base_info) name =
  Ain.get_function ain name
  |> Option.map ~f:(fun (f : Ain.Function.t) -> f.index)
  |> in_base base.nr_functions

(* Binds declarations to the base AIN entries of the same name, and adds new
   entries only for selected declarations. *)
let patch_allocator ain (base : base_info) (sel : selection) :
    Declarations.allocator =
  let next_global = ref 0 in
  let added = Hashtbl.create (module String) in
  let memoize name f =
    match Hashtbl.find added name with
    | Some i -> i
    | None ->
        let i = f () in
        Hashtbl.set added ~key:name ~data:i;
        i
  in
  let type_index kind base_index selected name node add =
    match base_index with
    | Some i -> i
    | None ->
        if selected then add ()
        else compile_error (sprintf "New %s %s must be selected" kind name) node
  in
  object
    method function_index _ name =
      match find_base_function ain base name with
      | Some i -> Some i
      | None ->
          if Hashtbl.mem sel.functions name then
            Some (memoize name (fun () -> (Ain.add_function ain name).index))
          else None

    (* Lambda names are sequence numbers, so a base AIN function with the same
       name is a different function. *)
    method lambda_index name = (Ain.add_function ain name).index

    method generated_function_index name =
      match find_base_function ain base name with
      | Some i -> i
      | None -> memoize name (fun () -> (Ain.add_function ain name).index)

    (* Globals are bound by declaration order. define_globals checks the
       names. *)
    method global_index (g : variable) ~group =
      let i = !next_global in
      Int.incr next_global;
      if i < base.nr_globals then i
      else if sel.rebuild_globals then Ain.add_global ain g.name group
      else
        compile_error
          (sprintf "New global %s requires --globals" g.name)
          (ASTVariable g)

    method global_group_index (gg : global_group) =
      let rec find i =
        if i >= Ain.nr_global_groups ain then None
        else if String.equal (Ain.get_global_group_name ain i) gg.name then
          Some i
        else find (i + 1)
      in
      match find 0 with
      | Some i -> i
      | None ->
          if sel.rebuild_globals then Ain.add_global_group ain gg.name
          else
            compile_error
              (sprintf "New global group %s requires --globals" gg.name)
              (ASTDeclaration (GlobalGroup gg))

    method struct_index (s : structdecl) =
      type_index "struct"
        (in_base base.nr_structs (Ain.get_struct_index ain s.name))
        (Hash_set.mem sel.structs s.name)
        s.name (ASTDeclaration (StructDef s))
        (fun () -> (Ain.add_struct ain s.name).index)

    method functype_index (f : fundecl) =
      type_index "functype"
        (in_base base.nr_functypes (Ain.get_functype_index ain f.name))
        (Hash_set.mem sel.functypes f.name)
        f.name (ASTDeclaration (FuncTypeDef f))
        (fun () -> (Ain.add_functype ain f.name).index)

    method delegate_index (f : fundecl) =
      type_index "delegate"
        (in_base base.nr_delegates (Ain.get_delegate_index ain f.name))
        (Hash_set.mem sel.delegates f.name)
        f.name (ASTDeclaration (DelegateDef f))
        (fun () -> (Ain.add_delegate ain f.name).index)
  end

(* Removes the functions that have no index, and records in [unavailable] the
   hints that [add_hints] adds to errors about them. The functions are also
   removed from [decls], so that type analysis does not check their default
   argument values. *)
let remove_unbound (ctx : context) unavailable decls =
  Hashtbl.filter_inplace ctx.functions ~f:(fun (f : fundecl) ->
      match f.index with
      | Some _ -> true
      | None ->
          let display, keys =
            match f.class_name with
            | Some c -> (c ^ "::" ^ f.name, [ c ^ "." ^ f.name; f.name ])
            | None -> (f.name, [ f.name ])
          in
          let message =
            sprintf
              "%s is declared in the project but is not in the base AIN. \
               Select it to add it."
              display
          in
          List.iter keys ~f:(fun key ->
              Hashtbl.set unavailable ~key ~data:message);
          false);
  List.filter decls ~f:(function
    | Function { index = None | Some -1; _ } -> false
    | _ -> true)

let rec add_hints unavailable = function
  | Error (msg, loc) -> (
      match String.chop_prefix msg ~prefix:"Undefined variable: " with
      | Some name -> (
          match Hashtbl.find unavailable name with
          | Some hint -> Error (msg ^ "\n" ^ hint, loc)
          | None -> Error (msg, loc))
      | None -> Error (msg, loc))
  | Message msg -> Message msg
  | ErrorList es -> ErrorList (List.map es ~f:(add_hints unavailable))

let bind_library (ctx : context) decls hll_name import_name =
  let functions =
    List.map decls ~f:(function
      | Function f -> f
      | decl ->
          compiler_bug "unexpected declaration in .hll file"
            (Some (ASTDeclaration decl)))
  in
  Declarations.check_builtin_library ctx import_name functions;
  let lib_no =
    match Ain.get_library_index ctx.ain hll_name with
    | Some i -> i
    | None -> raise_message ("HLL libraries cannot be added: " ^ hll_name)
  in
  let lib = Ain.get_library_by_index ctx.ain lib_no in
  let version = Ain.version ctx.ain in
  let data_type t = Ain.Type.int_of_data_type version t in
  List.iter functions ~f:(fun f ->
      let display = hll_name ^ "." ^ f.name in
      match
        Array.find lib.functions ~f:(fun (bf : Ain.Library.Function.t) ->
            String.equal bf.name f.name)
      with
      | None -> raise_message ("HLL functions cannot be added: " ^ display)
      | Some bf ->
          let pf = jaf_to_ain_hll_function f in
          let same_types =
            data_type pf.return_type = data_type bf.return_type
            && List.equal
                 (fun (a : Ain.Library.Argument.t) (b : Ain.Library.Argument.t)
                    -> data_type a.value_type = data_type b.value_type)
                 pf.arguments bf.arguments
          in
          if not same_types then
            compile_error
              (sprintf "Signature of %s does not match the base AIN" display)
              (ASTDeclaration (Function f)));
  let functions =
    Hashtbl.create_with_key_exn
      (module String)
      ~get_key:(fun (d : fundecl) -> d.name)
      functions
  in
  Hashtbl.add_exn ctx.libraries ~key:import_name ~data:{ hll_name; functions }

(* The base AIN can record a function type or delegate type without its
   index. Such a type matches any function type or delegate type. *)
let rec type_matches ~(base : Ain.Type.t) (t : Ain.Type.t) =
  match (base, t) with
  | FuncType -1, FuncType _ | Delegate -1, Delegate _ -> true
  | Ref b, Ref t | Array b, Array t | Wrap b, Wrap t -> type_matches ~base:b t
  | _ -> Poly.equal base t

let types_match ~(base : Ain.Variable.t list) (vars : Ain.Variable.t list) =
  List.equal
    (fun (b : Ain.Variable.t) (v : Ain.Variable.t) ->
      type_matches ~base:b.value_type v.value_type)
    base vars

(* Checks also the functions that are not selected, because the code for calls
   uses the project declarations. Default argument values are not compared,
   because the existing code passes all arguments. *)
let verify_functions (ctx : context) (base : base_info) struct_names entries =
  iter_fundecls struct_names entries ~f:(fun _ _ display fd ->
      match fd.index with
      | Some i when i >= 0 && i < base.nr_functions ->
          let b = Ain.get_function_by_index ctx.ain i in
          let p = jaf_to_ain_function fd b in
          if
            not
              (type_matches ~base:b.return_type p.return_type
              && p.nr_args = b.nr_args
              && types_match ~base:(List.take b.vars b.nr_args) p.vars
              && Bool.equal p.is_label b.is_label)
          then
            compile_error
              (sprintf "Signature of %s does not match the base AIN" display)
              (ASTDeclaration (Function fd))
      | _ -> ())

let define_functypes (ctx : context) (base : base_info) decls =
  let define get nr write (f : fundecl) node =
    let p = jaf_to_ain_functype f in
    if p.index < nr then (
      let b : Ain.FunctionType.t = get ctx.ain p.index in
      if
        not
          (type_matches ~base:b.return_type p.return_type
          && p.nr_arguments = b.nr_arguments
          && types_match ~base:b.variables p.variables)
      then
        compile_error
          (sprintf "Signature of %s does not match the base AIN" f.name)
          node)
    else write ctx.ain p
  in
  List.iter decls ~f:(function
    | FuncTypeDef f as d ->
        define Ain.get_functype_by_index base.nr_functypes Ain.write_functype f
          (ASTDeclaration d)
    | DelegateDef f as d ->
        define Ain.get_delegate_by_index base.nr_delegates Ain.write_delegate f
          (ASTDeclaration d)
    | _ -> ())

let define_structs (ctx : context) (base : base_info) (sel : selection) decls =
  let selected_function name =
    Option.map (Hashtbl.find sel.functions name) ~f:(fun (fd, _) ->
        Option.value_exn fd.index)
  in
  List.iter decls ~f:(function
    | StructDef s ->
        let index = (Hashtbl.find_exn ctx.structs s.name).index in
        let b = Ain.get_struct_by_index ctx.ain index in
        let has_ctor =
          List.exists s.decls ~f:(function Constructor _ -> true | _ -> false)
        in
        let ctor_selected = Hashtbl.mem sel.functions (s.name ^ "@0") in
        let struct_selected = Hash_set.mem sel.structs s.name in
        (if index >= base.nr_structs then (
           List.iter s.decls ~f:(function
             | Method f | Constructor f | Destructor f ->
                 if Option.is_none f.index then
                   compile_error
                     (sprintf "No definition of %s::%s found" s.name f.name)
                     (ASTDeclaration (Function f))
             | _ -> ());
           jaf_to_ain_struct s b |> Ain.write_struct ctx.ain)
         else
           let project_members =
             List.concat_map s.decls ~f:(function
               | MemberDecl ds when not ds.is_const_decls -> ds.vars
               | _ -> [])
             |> jaf_to_ain_variables
           in
           let nb = List.length b.members in
           let keeps_base_members =
             List.length project_members >= nb
             && List.for_all2_exn (List.take project_members nb) b.members
                  ~f:(fun (x : Ain.Variable.t) y ->
                    String.equal x.name y.name
                    && type_matches ~base:y.value_type x.value_type)
           in
           if not keeps_base_members then
             compile_error
               (sprintf
                  "Existing members of %s must keep their name, type, and order"
                  s.name)
               (ASTDeclaration (StructDef s));
           if List.length project_members > nb && not struct_selected then
             compile_error
               (sprintf "New members of %s require selecting %s" s.name s.name)
               (ASTDeclaration (StructDef s));
           let members = b.members @ List.drop project_members nb in
           (* AIN version 1 has no S@2. The constructor body allocates the
              member arrays. *)
           if
             Ain.version ctx.ain >= 2
             && Option.is_some (find_base_function ctx.ain base (s.name ^ "@2"))
             && not has_ctor
           then
             compile_error
               (sprintf "Constructor of %s cannot be removed" s.name)
               (ASTDeclaration (StructDef s));
           let constructor =
             Option.value
               (selected_function (s.name ^ "@0"))
               ~default:b.constructor
           in
           let destructor =
             Option.value
               (selected_function (s.name ^ "@1"))
               ~default:b.destructor
           in
           Ain.write_struct ctx.ain { b with members; constructor; destructor });
        (* Without S@2 in the base AIN, the new S@2 and the call to it in the
           constructor must be compiled together. *)
        if
          has_ctor
          && Option.is_none (find_base_function ctx.ain base (s.name ^ "@2"))
          && not (Bool.equal struct_selected ctor_selected)
        then
          let _, name = Util.parse_qualified_name s.name in
          compile_error
            (sprintf "%s and %s::%s must be selected together" s.name s.name
               name)
            (ASTDeclaration (StructDef s))
    | _ -> ())

let base_group_name ain (g : Ain.Global.t) =
  if Ain.version ain < 5 || g.group_index < 0 then None
  else Some (Ain.get_global_group_name ain g.group_index)

let define_globals (ctx : context) (base : base_info) (sel : selection) decls =
  let project_globals =
    List.concat_map decls ~f:global_vars_with_group
    |> List.filter ~f:(fun ((v : variable), _) -> not v.is_const)
  in
  List.iter project_globals ~f:(fun (v, group) ->
      let i = Option.value_exn v.index in
      if i < base.nr_globals then
        let b = Ain.get_global_entry ctx.ain i in
        if
          not
            (String.equal v.name b.variable.name
            && type_matches ~base:b.variable.value_type
                 (jaf_to_ain_type v.type_spec.ty)
            && Option.equal String.equal group (base_group_name ctx.ain b))
        then
          compile_error
            (sprintf "Global %s does not match the base AIN" v.name)
            (ASTVariable v));
  if List.length project_globals < base.nr_globals then
    raise_message
      "Existing globals must keep their name, type, order, and group";
  if sel.rebuild_globals then
    List.iter project_globals ~f:(fun (v, _) ->
        let i = Option.value_exn v.index in
        if i >= base.nr_globals then
          let g = Ain.get_global_entry ctx.ain i in
          Ain.write_global ctx.ain
            {
              g with
              variable =
                { g.variable with value_type = jaf_to_ain_type v.type_spec.ty };
            })

(* The code generator selects instructions by the minor version, and the base
   AIN gives only its lower limit. *)
let set_minor_version base (pje : Pje.t) =
  if pje.ain_version <> Ain.version base then
    raise_message
      (sprintf "_AINVERSION %d does not match the base AIN version %d"
         pje.ain_version (Ain.version base));
  if pje.ain_minor_version < Ain.minor_version base then
    raise_message
      (sprintf "_AINMINORVERSION %d is lower than the base AIN version %d.%d"
         pje.ain_minor_version (Ain.version base) (Ain.minor_version base));
  Ain.set_minor_version base pje.ain_minor_version

let parse_source read_file src =
  let parser =
    match src.kind with `Jaf -> Parser.jaf | `Hll _ -> Parser.hll
  in
  Compile.parse_file Lexer.token parser src.path (fun _ -> read_file src)

(* Groups the function bodies by source, in source order. *)
let selected_bodies entries =
  List.concat_map entries ~f:(fun e ->
      match e.decl with
      | Function fd when Option.is_some fd.body -> [ (e, fd) ]
      | StructDef s ->
          List.filter_map s.decls ~f:(function
            | (Constructor fd | Destructor fd | Method fd)
              when Option.is_some fd.body ->
                Some (e, fd)
            | _ -> None)
      | _ -> [])
  |> List.stable_sort ~compare:(fun (a, _) (b, _) ->
      Poly.compare (a.src_no, a.ord) (b.src_no, b.ord))
  |> List.group ~break:(fun (a, _) (b, _) -> a.src_no <> b.src_no)
  |> List.map ~f:(fun group ->
      let e, _ = List.hd_exn group in
      (e.src, List.map group ~f:(fun (_, fd) -> Function fd)))

let apply ~base ~pje ~sources ~targets ~globals ~keep_crc ~read_file ~debug_info
    =
  (* Validate the base AIN and the options. *)
  let version = Ain.version base in
  if version < 1 || version > 8 then
    raise_message (sprintf "AIN version %d is not supported" version);
  if
    List.is_empty targets && (not globals)
    && not (List.exists sources ~f:is_selected_source)
  then raise_message "No patch targets specified";
  set_minor_version base pje;
  Option.iter debug_info ~f:(fun di ->
      match DebugInfo.last_address di with
      | Some addr when addr >= Ain.code_size base ->
          raise_message
            "debug_info.json has mappings past the end of the base AIN code"
      | _ -> ());
  let ctx = create_context base in
  let base_info = base_info base in
  (* Parse the sources. *)
  let jafs, hlls =
    List.partition_map
      (List.mapi sources ~f:(fun src_no src ->
           (src_no, src, parse_source read_file src)))
      ~f:(fun (src_no, src, decls) ->
        match src.kind with
        | `Jaf ->
            First
              (List.mapi decls ~f:(fun ord decl -> { decl; src; src_no; ord }))
        | `Hll import_name ->
            let hll_name =
              Stdlib.Filename.(chop_extension (basename src.path))
            in
            Second (hll_name, import_name, decls))
  in
  let project, extras =
    List.partition_tf (List.concat jafs) ~f:(fun e ->
        match e.src.origin with
        | `Project | `Project_selected -> true
        | `Extra -> false)
  in
  (* Replace the project declarations with the --source declarations. *)
  let entries = replace_declarations project extras in
  (* Select the patch targets. *)
  let sel =
    {
      functions = Hashtbl.create (module String);
      structs = Hash_set.create (module String);
      functypes = Hash_set.create (module String);
      delegates = Hash_set.create (module String);
      rebuild_globals =
        globals
        || List.exists (project @ extras) ~f:(fun e ->
            is_selected_source e.src && declares_globals e.decl);
    }
  in
  let struct_names = collect_struct_names entries in
  select_from_sources sel struct_names entries;
  let idx = build_name_index sel struct_names entries in
  List.iter targets ~f:(select_target sel idx);
  (* Remove the bodies that are not selected. *)
  let entries = strip_bodies sel struct_names entries in
  if version = 1 then check_v1_restrictions ctx sel;
  (* Bind the declarations to the base AIN entries. *)
  let unavailable = Hashtbl.create (module String) in
  let allocator = patch_allocator base base_info sel in
  Declarations.register_type_declarations ~allocator ctx
    (List.map entries ~f:(fun e -> e.decl));
  let decls =
    remove_unbound ctx unavailable (List.map entries ~f:(fun e -> e.decl))
  in
  Declarations.resolve_types ctx decls;
  (* Verify the declarations against the base AIN and write the new entries. *)
  List.iter hlls ~f:(fun (hll_name, import_name, hll) ->
      Declarations.resolve_hll_types ctx hll;
      Declarations.resolve_types ctx hll;
      bind_library ctx hll hll_name import_name);
  verify_functions ctx base_info struct_names entries;
  define_functypes ctx base_info decls;
  define_structs ctx base_info sel decls;
  define_globals ctx base_info sel decls;
  (* Generate the initializers and analyze the declarations. *)
  let array_init =
    new ArrayInit.visitor
      ~allocator
      ~generate:
        (`Patch
           ArrayInit.
             {
               is_struct_selected = Hash_set.mem sel.structs;
               rebuild_globals = sel.rebuild_globals;
               find_base_function = find_base_function base base_info;
             })
      ctx
  in
  List.iter decls ~f:array_init#visit_declaration;
  let initializers = array_init#generate_initializers () in
  let all_decls = decls @ initializers in
  (try TypeAnalysis.check_types_exn ctx all_decls
   with Compile_error e ->
     Base.raise (Compile_error (add_hints unavailable e)));
  ConstEval.evaluate_constant_expressions ctx all_decls;
  VariableAlloc.allocate_variables ctx all_decls;
  if sel.rebuild_globals then (
    Ain.clear_global_initvals base;
    GlobalInit.write_initvals ctx decls);
  (* Generate the code. *)
  let base_crcs =
    Array.init base_info.nr_functions ~f:(fun i ->
        (Ain.get_function_by_index base i).crc)
  in
  let debug_info = Option.value debug_info ~default:(DebugInfo.create ()) in
  let compile_block debug_path block =
    if not (List.is_empty block) then (
      SanityCheck.check_invariants ctx block;
      DebugInfo.begin_source debug_info debug_path;
      Codegen.compile ~eof:false ctx "" block debug_info)
  in
  List.iter (selected_bodies entries) ~f:(fun (src, block) ->
      compile_block src.debug_path block);
  compile_block "" initializers;
  if keep_crc then
    Array.iteri base_crcs ~f:(fun i crc ->
        let f = Ain.get_function_by_index base i in
        if not (Int32.equal f.crc crc) then
          Ain.write_function base { f with crc })
