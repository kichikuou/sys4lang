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

type role = Reference | Target

type jaf_source = {
  filename : string;
  role : role;
  declarations : Jaf.declaration list;
}

type source =
  | Jaf of jaf_source
  | Hll of {
      filename : string;
      name : string;
      import_name : string;
      declarations : Jaf.declaration list;
    }

type definition = {
  source : jaf_source;
  name : string;
  class_name : string option;
  declaration : Jaf.fundecl;
}

type selection =
  | FuncType of Jaf.fundecl
  | Delegate of Jaf.fundecl
  | Function of definition
  | Class of Jaf.structdecl
  | GlobalGroup of Jaf.global_group
  | Library of string
  | Global of Jaf.variable

type t = {
  project : Pje.t;
  sources : source list;
  targets : jaf_source list;
  selections : selection list;
  output_definitions : definition list;
  definitions : (string, definition) Hashtbl.t;
}

let find_definition t name = Hashtbl.find t.definitions name

let global_variables t =
  List.concat_map t.sources ~f:(function
    | Jaf source ->
        List.concat_map source.declarations ~f:(function
          | Jaf.Global ds -> ds.vars
          | GlobalGroup gg -> List.concat_map gg.vardecls ~f:(fun ds -> ds.vars)
          | _ -> [])
    | Hll _ -> [])

let rebuild_globals t =
  List.exists t.selections ~f:(function
    | Global _ | GlobalGroup _ -> true
    | Function _ | Class _ | FuncType _ | Delegate _ | Library _ -> false)

let definitions_in source =
  let definition ?class_name (f : Jaf.fundecl) =
    match f.body with
    | None -> []
    | Some _ ->
        let class_name, name =
          match class_name with
          | Some _ -> (class_name, f.name)
          | None -> Util.parse_qualified_name f.name
        in
        let name = Jaf.mangled_name { f with name; class_name } in
        [ { source; name; class_name; declaration = f } ]
  in
  List.concat_map source.declarations ~f:(function
    | Jaf.Function f -> definition f
    | StructDef s ->
        List.concat_map s.decls ~f:(function
          | Constructor f | Destructor f | Method f ->
              definition ~class_name:s.name f
          | AccessSpecifier _ | MemberDecl _ -> [])
    | Global _ | GlobalGroup _ | FuncTypeDef _ | DelegateDef _ | Enum _ -> [])

let fundecl_source_name ?owner (declaration : Jaf.fundecl) =
  let name = declaration.name in
  match (Util.parse_qualified_name name, owner) with
  | (Some _, _), _ -> name
  | (None, _), Some owner -> owner ^ "::" ^ name
  | (None, _), None -> name

let source_name (definition : definition) =
  fundecl_source_name ?owner:definition.class_name definition.declaration

let declared_function_names source =
  List.concat_map source.declarations ~f:(function
    | Jaf.Function f -> [ fundecl_source_name f ]
    | StructDef s ->
        List.filter_map s.decls ~f:(function
          | Constructor f | Destructor f | Method f ->
              Some (fundecl_source_name ~owner:s.name f)
          | AccessSpecifier _ | MemberDecl _ -> None)
    | Global _ | GlobalGroup _ | FuncTypeDef _ | DelegateDef _ | Enum _ -> [])

let selections_in source =
  let functions = definitions_in source |> List.map ~f:(fun d -> Function d) in
  let declarations =
    List.concat_map source.declarations ~f:(function
      | Jaf.StructDef s -> [ Class s ]
      | Global ds ->
          List.filter_map ds.vars ~f:(fun v ->
              if v.is_const then None else Some (Global v))
      | GlobalGroup gg ->
          GlobalGroup gg
          :: List.concat_map gg.vardecls ~f:(fun ds ->
              List.filter_map ds.vars ~f:(fun v ->
                  if v.is_const then None else Some (Global v)))
      | FuncTypeDef f -> [ FuncType f ]
      | DelegateDef f -> [ Delegate f ]
      | Function _ | Enum _ -> [])
  in
  functions @ declarations

let project_error project_file message =
  let pos = { Lexing.dummy_pos with pos_fname = project_file } in
  CompileError.raise message (pos, pos)

let absolute path =
  if Stdlib.Filename.is_relative path then
    Stdlib.Filename.concat (Stdlib.Sys.getcwd ()) path
  else path

let path_key path = Fpath.(v path |> to_string)

type parsed_sources = { sources : source list; target_sources : source list }

let parse_sources ~read_file ~patch_files ~project_file (project : Pje.t) =
  let project_dir = Stdlib.Filename.dirname project_file in
  let target_paths =
    Hash_set.of_list (module String) (List.map patch_files ~f:path_key)
  in
  (* A patch has two useful names: the path used to read it, which is relative
     to the current directory, and the name stored in locations/debug info,
     which is preferably relative to the project. *)
  let patch_filename path =
    match
      Fpath.relativize
        ~root:(Fpath.v (absolute project_dir) |> Fpath.to_dir_path)
        (Fpath.v (absolute path))
    with
    | Some path -> Fpath.to_string path
    | None -> path
  in
  let source_dir =
    let dir = project.source_dir in
    if String.equal dir "." then Stdlib.Filename.dirname project_file
    else if Stdlib.Filename.is_relative dir then
      Stdlib.Filename.concat (Stdlib.Filename.dirname project_file) dir
    else dir
  in
  let project_path path =
    if Stdlib.Filename.is_relative path then
      Stdlib.Filename.concat source_dir path
    else path
  in
  let read_source path =
    let text = read_file path in
    match project.encoding with Pje.UTF8 -> text | SJIS -> Sjis.to_utf8 text
  in
  let parsed = Hashtbl.create (module String) in
  let parse read_path filename binding =
    let key = path_key read_path in
    match Hashtbl.find parsed key with
    | Some (Jaf _) when Option.is_none binding -> None
    | Some (Hll h)
      when Option.equal
             (fun (name, import_name) (other_name, other_import) ->
               String.equal name other_name
               && String.equal import_name other_import)
             binding
             (Some (h.name, h.import_name)) ->
        None
    | Some _ ->
        project_error project_file
          ("Conflicting source registrations: " ^ filename)
    | None ->
        let source =
          match binding with
          | None ->
              Jaf
                {
                  filename;
                  role =
                    (if Hash_set.mem target_paths key then Target else Reference);
                  declarations =
                    SourceParser.parse_file Lexer.token Parser.jaf filename
                      (fun _ -> read_source read_path);
                }
          | Some (name, import_name) ->
              Hll
                {
                  filename;
                  name;
                  import_name;
                  declarations =
                    SourceParser.parse_file Lexer.token Parser.hll filename
                      (fun _ -> read_source read_path);
                }
        in
        Hashtbl.add_exn parsed ~key ~data:source;
        Some source
  in
  let sources =
    List.filter_map (Pje.collect_sources project) ~f:(function
      | Pje.Jaf path -> parse (project_path path) path None
      | Hll (path, import_name) ->
          let name = Stdlib.Filename.(chop_extension (basename path)) in
          parse (project_path path) path (Some (name, import_name))
      | Include _ -> assert false)
  in
  let sources =
    sources
    @ List.filter_map patch_files ~f:(fun path ->
        let binding =
          match Hashtbl.find parsed (path_key path) with
          | Some (Hll h) -> Some (h.name, h.import_name)
          | _ when String.is_suffix (String.lowercase path) ~suffix:".hll" ->
              let name = Stdlib.Filename.(chop_extension (basename path)) in
              Some (name, name)
          | _ -> None
        in
        parse path (patch_filename path) binding)
  in
  (* Rebuild this list in command-line order. [sources] instead preserves PJE
     declaration order and only appends patches that were not already there. *)
  let target_sources =
    List.map patch_files ~f:(fun path ->
        Hashtbl.find_exn parsed (path_key path))
  in
  { sources; target_sources }

let collect_definitions definitions =
  let table = Hashtbl.create (module String) in
  List.iter definitions ~f:(fun d ->
      match Hashtbl.add table ~key:d.name ~data:d with
      | `Ok -> ()
      | `Duplicate ->
          let previous = Hashtbl.find_exn table d.name in
          CompileError.raise
            ("Duplicate function definition: " ^ d.name
           ^ " (previous definition in " ^ previous.source.filename ^ ")")
            d.declaration.loc);
  table

let build_definition_table sources target_sources =
  let reference_definitions =
    List.concat_map sources ~f:(function
      | Jaf ({ role = Reference; _ } as source) -> definitions_in source
      | Jaf _ | Hll _ -> [])
  in
  let target_definitions = List.concat_map target_sources ~f:definitions_in in
  let definitions = collect_definitions reference_definitions in
  let output = collect_definitions target_definitions in
  (* A duplicate within either group is an error, but a patch definition is
     deliberately allowed to replace a definition from a reference source. *)
  Hashtbl.iteri output ~f:(fun ~key ~data -> Hashtbl.set definitions ~key ~data);
  definitions

type source_index = {
  definitions : definition list;
  structures : Jaf.structdecl list;
  functypes : Jaf.fundecl list;
  delegates : Jaf.fundecl list;
  globals : Jaf.variable list;
  groups : Jaf.global_group list;
  libraries : string list;
  declared_functions : string Hash_set.t;
}

let build_source_index sources definitions =
  let structures =
    List.concat_map sources ~f:(function
      | Jaf source ->
          List.filter_map source.declarations ~f:(function
            | Jaf.StructDef s -> Some s
            | _ -> None)
      | Hll _ -> [])
  in
  let globals =
    List.concat_map sources ~f:(function
      | Jaf source ->
          List.concat_map source.declarations ~f:(function
            | Jaf.Global ds -> ds.vars
            | GlobalGroup gg ->
                List.concat_map gg.vardecls ~f:(fun ds -> ds.vars)
            | _ -> [])
      | Hll _ -> [])
  in
  let types get =
    List.concat_map sources ~f:(function
      | Jaf source -> List.filter_map source.declarations ~f:get
      | Hll _ -> [])
  in
  let declared_functions =
    List.concat_map sources ~f:(function
      | Jaf source -> declared_function_names source
      | Hll _ -> [])
    |> Hash_set.of_list (module String)
  in
  {
    definitions = Hashtbl.data definitions;
    structures;
    functypes = types (function Jaf.FuncTypeDef f -> Some f | _ -> None);
    delegates = types (function Jaf.DelegateDef f -> Some f | _ -> None);
    globals;
    groups = types (function Jaf.GlobalGroup gg -> Some gg | _ -> None);
    libraries =
      List.filter_map sources ~f:(function
        | Hll h -> Some h.import_name
        | Jaf _ -> None);
    declared_functions;
  }

let resolve_named_selection ~project_file index requested =
  (* Source names (C::method) are matched here; [definition.name] remains the
     mangled AIN name (C@method) used by later compilation stages. *)
  let matches =
    List.filter_map index.definitions ~f:(fun d ->
        if String.equal (source_name d) requested then Some (Function d)
        else None)
    @ List.filter_map index.structures ~f:(fun s ->
        if String.equal s.name requested then Some (Class s) else None)
    @ List.filter_map index.functypes ~f:(fun f ->
        if String.equal f.name requested then Some (FuncType f) else None)
    @ List.filter_map index.delegates ~f:(fun f ->
        if String.equal f.name requested then Some (Delegate f) else None)
    @ List.filter_map index.globals ~f:(fun v ->
        if (not v.is_const) && String.equal v.name requested then
          Some (Global v)
        else None)
    @ List.filter_map index.groups ~f:(fun gg ->
        if String.equal gg.name requested then Some (GlobalGroup gg) else None)
    @ List.filter_map index.libraries ~f:(fun name ->
        if String.equal name requested then Some (Library name) else None)
  in
  if List.is_empty matches then
    if Hash_set.mem index.declared_functions requested then
      project_error project_file
        ("Patch target has no function body: " ^ requested)
    else project_error project_file ("Unknown patch target: " ^ requested);
  matches

let selection_key = function
  | Function d -> "function\000" ^ d.name
  | Class s -> "class\000" ^ s.name
  | Global v -> "global\000" ^ v.name
  | GlobalGroup gg -> "globalgroup\000" ^ gg.name
  | Library name -> "library\000" ^ name
  | FuncType f -> "functype\000" ^ f.name
  | Delegate f -> "delegate\000" ^ f.name

let resolve_selections ~project_file ~target_names ~sources ~target_sources
    definitions =
  let source_selections =
    List.concat_map target_sources ~f:(function
      | Jaf source -> selections_in source
      | Hll h -> [ Library h.import_name ])
  in
  let index = build_source_index sources definitions in
  let named_selections =
    List.concat_map target_names
      ~f:(resolve_named_selection ~project_file index)
  in
  (* Preserve the first occurrence so CLI/source order also determines output
     order, while still allowing a function, class and global of one name. *)
  let seen = Hash_set.create (module String) in
  List.filter (source_selections @ named_selections) ~f:(fun selection ->
      Hash_set.strict_add seen (selection_key selection) |> Result.is_ok)

let target_sources_for_codegen target_sources output_definitions =
  (* Name-selected functions can come from reference sources, so their source
     must be added even when no corresponding --source option was supplied. *)
  let seen = Hash_set.create (module String) in
  List.filter
    (target_sources @ List.map output_definitions ~f:(fun d -> d.source))
    ~f:(fun source -> Hash_set.strict_add seen source.filename |> Result.is_ok)

let load ?(read_file = Stdio.In_channel.read_all) ?(patch_files = [])
    ?targets:(target_names = []) project_file =
  let project = PjeLoader.load read_file project_file in
  if List.is_empty patch_files && List.is_empty target_names then
    project_error project_file "No patch targets or source files specified";
  let patch_files = List.stable_dedup patch_files ~compare:String.compare in
  let { sources; target_sources } =
    parse_sources ~read_file ~patch_files ~project_file project
  in
  let jaf_targets =
    List.filter_map target_sources ~f:(function
      | Jaf source -> Some source
      | Hll _ -> None)
  in
  let definitions = build_definition_table sources jaf_targets in
  let selections =
    resolve_selections ~project_file ~target_names ~sources ~target_sources
      definitions
  in
  if List.is_empty selections then
    project_error project_file "Selected source files contain no patch targets";
  let output_definitions =
    List.filter_map selections ~f:(function Function d -> Some d | _ -> None)
  in
  let targets = target_sources_for_codegen jaf_targets output_definitions in
  { project; sources; targets; selections; output_definitions; definitions }
