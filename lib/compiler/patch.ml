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

let unsupported what loc =
  CompileError.raise ("Patch does not yet support " ^ what) loc

class body_checker ?scope declarations =
  let ctx = PatchDeclarations.context declarations in
  object
    inherit
      TypeAnalysis.type_analyze_visitor ~register_entrypoints:false ctx as super

    method! env = match scope with Some env -> env | None -> super#env

    method! visit_type_specifier ts =
      PatchDeclarations.resolve_type declarations ts
  end

(* Evaluate constants and defaults in declaration order and declaration scope. *)
let prepare_values ~rebuild_globals declarations (program : PatchSources.t) =
  let ctx = PatchDeclarations.context declarations in
  if rebuild_globals then
    List.iter (PatchSources.global_variables program) ~f:(fun v ->
        if not v.is_const then Ain.set_global_initval_opt ctx.ain v.name None);
  let scope owner =
    let f =
      Option.map owner ~f:(fun name ->
          let index = Ain.get_struct_index ctx.ain name in
          {
            name = "";
            loc = dummy_location;
            return = { ty = Void; location = dummy_location };
            params = [];
            body = None;
            is_label = false;
            is_lambda = false;
            is_private = false;
            index = None;
            class_name = Some name;
            class_index = index;
          })
    in
    new environment ctx f
  in
  let evaluate owner v =
    if Option.is_some v.initval || v.is_const then
      let env = scope owner in
      let check = new body_checker ~scope:env declarations in
      let eval =
        object
          inherit ConstEval.const_eval_visitor ctx
          method! env = env
        end
      in
      try
        check#visit_variable v;
        eval#visit_variable v
      with Division_by_zero ->
        CompileError.raise "Division by zero in constant expression" v.location
  in
  let defaults = ref [] in
  let function_defaults f = defaults := (f.class_name, f.params) :: !defaults in
  List.iter program.sources ~f:(function
    | PatchSources.Hll s ->
        List.iter s.declarations ~f:(function
          | Function f -> function_defaults f
          | _ -> ())
    | Jaf source ->
        List.iter source.declarations ~f:(function
          | Global ds ->
              List.iter ds.vars ~f:(fun v ->
                  if v.is_const then evaluate None v
                  else if rebuild_globals && Option.is_some v.initval then
                    evaluate None v)
          | GlobalGroup gg ->
              List.iter gg.vardecls ~f:(fun ds ->
                  List.iter ds.vars ~f:(fun v ->
                      if v.is_const then evaluate None v
                      else if rebuild_globals && Option.is_some v.initval then
                        evaluate None v))
          | StructDef s ->
              List.iter s.decls ~f:(function
                | MemberDecl ds ->
                    List.iter ds.vars ~f:(fun v ->
                        if v.is_const then evaluate (Some s.name) v)
                | Method f | Constructor f | Destructor f -> function_defaults f
                | AccessSpecifier _ -> ())
          | Function f | FuncTypeDef f | DelegateDef f -> function_defaults f
          | Enum _ -> ()));
  List.iter (List.rev !defaults) ~f:(fun (owner, params) ->
      List.iter params ~f:(evaluate owner))

type output =
  | Body of PatchSources.definition
  | Initializer of PatchInitializers.target

let name = function Body d -> d.name | Initializer t -> t.name

let outputs (program : PatchSources.t) targets =
  let seen = Hash_set.create (module String) in
  List.filter
    (List.map program.output_definitions ~f:(fun d -> Body d)
    @ List.map targets ~f:(fun t -> Initializer t))
    ~f:(fun output -> Hash_set.strict_add seen (name output) |> Result.is_ok)

let register ain outputs =
  List.map outputs ~f:(fun output ->
      let func_name = name output in
      let existing = Ain.get_function ain func_name in
      let f =
        match existing with
        | Some f -> f
        | None -> Ain.add_function ain func_name
      in
      let owner =
        match output with
        | Body d ->
            d.declaration.index <- Some f.index;
            d.class_name
        | Initializer t -> Option.map t.owner ~f:(fun s -> s.Jaf.name)
      in
      if Option.is_none existing then
        Option.iter owner ~f:(fun owner ->
            let s = Option.value_exn (Ain.get_struct ain owner) in
            if String.equal func_name (owner ^ "@0") then
              Ain.write_struct ain { s with constructor = f.index }
            else if String.equal func_name (owner ^ "@1") then
              Ain.write_struct ain { s with destructor = f.index });
      (output, f.index))

type result = {
  functions : string list;
  added_types : (string * string) list;
  added_entries : (string * string) list;
}

let compile ?(debug_info = DebugInfo.create ()) ain (program : PatchSources.t) =
  if Ain.version ain >= 8 then unsupported "AIN v8 or later" dummy_location;
  List.iter program.output_definitions ~f:(fun d ->
      let f = d.declaration in
      if (f.is_label && Ain.version ain < 2) || String.equal d.name "NULL" then
        unsupported ("special function " ^ d.name) f.loc);
  let declarations = PatchDeclarations.prepare ain program in
  PatchDeclarations.resolve declarations program;
  PatchDeclarations.apply_additions declarations program;
  PatchDeclarations.validate declarations program;
  let generated = PatchInitializers.select ain program in
  let outputs = outputs program generated in
  let ctx = PatchDeclarations.context declarations in
  let rebuild_globals = PatchSources.rebuild_globals program in
  prepare_values ~rebuild_globals declarations program;
  let guard =
    object
      inherit ivisitor ctx as super

      method! visit_expression e =
        match e.node with
        | Lambda _ -> unsupported "lambdas in target bodies" e.loc
        | _ -> super#visit_expression e

      method! visit_statement s =
        match s.node with
        | (Jump _ | Jumps _) when Ain.version ain < 2 ->
            unsupported "scenario jumps" s.loc
        | _ -> super#visit_statement s
    end
  in
  List.iter program.output_definitions ~f:(fun d ->
      guard#visit_fundecl d.declaration);
  (* Reserve real trailing IDs for all selected new bodies before checking
     calls, including forward calls across files. Reference-only declarations
     never reach this loop. Existing entries are not registered again. *)
  let registered = register ain outputs in
  List.iter program.output_definitions ~f:(fun d ->
      if is_constructor d.declaration then (
        PatchDeclarations.bind_initializer_reference declarations d.declaration;
        ArrayInit.insert_array_initializer_call d.declaration));
  let generated_bodies =
    List.filter_map registered ~f:(function
      | Initializer target, index ->
          Some
            (Function
               (PatchInitializers.generate declarations program target index))
      | Body _, _ -> None)
  in
  let functions =
    List.map program.output_definitions ~f:(fun d -> Function d.declaration)
    @ generated_bodies
  in
  let checker = new body_checker declarations in
  checker#visit_toplevel functions;
  if not (List.is_empty checker#errors) then
    CompileError.raise_list checker#errors;
  (* Visit only selected functions, avoiding the ordinary whole-program scan of
     global constants and any global-initializer writes. *)
  let constants = new ConstEval.const_eval_visitor ctx in
  List.iter functions ~f:constants#visit_declaration;
  VariableAlloc.allocate_variables ctx functions;
  List.iter program.targets ~f:(fun source ->
      let bodies =
        List.filter_map program.output_definitions ~f:(fun d ->
            if phys_equal d.source source then Some (Function d.declaration)
            else None)
      in
      if not (List.is_empty bodies) then (
        SanityCheck.check_invariants ctx bodies;
        Codegen.compile ctx source.filename bodies debug_info));
  if not (List.is_empty generated_bodies) then (
    SanityCheck.check_invariants ctx generated_bodies;
    Codegen.compile ctx "" generated_bodies debug_info);
  {
    functions = List.map outputs ~f:name;
    added_types = PatchDeclarations.added_types declarations;
    added_entries = PatchDeclarations.added_entries declarations;
  }

type file_result = {
  replaced : string list;
  added : string list;
  added_types : (string * string) list;
  added_entries : (string * string) list;
  warnings : string list;
}

let compile_file ~project ?base ~targets ~sources ?output
    ?(write_debug_info = true) () =
  let program = PatchSources.load ~patch_files:sources ~targets project in
  let project_ain = Pje.ain_path program.project in
  let base = Option.value base ~default:project_ain in
  let output = Option.value output ~default:project_ain in
  let debug_file = Pje.debug_info_path program.project in
  let ain = Ain.load base in
  let debug_file_exists =
    write_debug_info && Stdlib.Sys.file_exists debug_file
  in
  let debug_info =
    if debug_file_exists then DebugInfo.load debug_file else DebugInfo.create ()
  in
  let update_debug_info =
    debug_file_exists && DebugInfo.has_mappings debug_info
  in
  DebugInfo.start_patch debug_info;
  let old_count = Ain.nr_functions ain in
  let result = compile ~debug_info ain program in
  let global_initializer = PatchSources.rebuild_globals program in
  let describe name =
    let suffix =
      if String.equal name "0" && global_initializer then
        " (global array initialization)"
      else if String.is_suffix name ~suffix:"@2" then
        " (member array initialization)"
      else if String.is_suffix name ~suffix:"@1" then " (destructor)"
      else if String.is_suffix name ~suffix:"@0" then
        if
          List.exists program.output_definitions ~f:(fun d ->
              String.equal d.name name)
        then " (constructor)"
        else " (constructor, member array initialization)"
      else ""
    in
    name ^ suffix
  in
  let replaced, added =
    List.partition_tf result.functions ~f:(fun name ->
        (Option.value_exn (Ain.get_function ain name)).index < old_count)
  in
  Ain.write_file ain output;
  if update_debug_info then DebugInfo.write_to_file debug_info debug_file;
  {
    replaced = List.map replaced ~f:describe;
    added = List.map added ~f:describe;
    added_types = result.added_types;
    added_entries = result.added_entries;
    warnings =
      (if write_debug_info && not debug_file_exists then
         [ debug_file ^ " was not found; debug information was not written" ]
       else if write_debug_info && not update_debug_info then
         [
           debug_file
           ^ " contains no mappings; debug information was not written";
         ]
       else []);
  }
