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
open Loc

let rec decompile_function (f : CodeSection.function_t) =
  let body =
    BasicBlock.create f
    |> BasicBlock.generate_var_decls f.func
    |> ControlFlow.analyze
    |> TypeAnalysis.analyze_function f.func f.struc
    |> Transform.expand_else_scope |> Transform.rename_labels
    |> Transform.recover_loop_initializer
    |> Transform.remove_implicit_array_free
    |> Transform.remove_array_free_for_dead_arrays
    |> Transform.remove_generated_lockpeek |> Transform.remove_redundant_return
    |> Transform.remove_dummy_variable_assignment
    |> Transform.remove_vardecl_default_rhs
    |> Transform.fold_newline_func_to_msg |> Transform.remove_optional_arguments
    |> Transform.simplify_boolean_expr
  in
  let lambdas = List.map ~f:decompile_function f.lambdas in
  CodeGen.
    {
      func = f.func;
      struc = f.struc;
      name = f.name;
      body;
      lambdas;
      parent = f.parent;
    }

let inspect_function (f : CodeSection.function_t) ~print_addr =
  BasicBlock.create f
  |> (fun bbs ->
  Stdio.printf "BasicBlock representation:\n%s\n\n"
    ([%show: BasicBlock.t list] bbs);
  bbs)
  |> BasicBlock.generate_var_decls f.func
  |> ControlFlow.analyze
  |> (fun stmt ->
  Stdio.printf "\nAST representation:\n%s\n" ([%show: Ast.statement loc] stmt);
  stmt)
  |> TypeAnalysis.analyze_function f.func f.struc
  |> Transform.expand_else_scope |> Transform.rename_labels
  |> Transform.recover_loop_initializer |> Transform.remove_implicit_array_free
  |> Transform.remove_array_free_for_dead_arrays
  |> Transform.remove_generated_lockpeek |> Transform.remove_redundant_return
  |> Transform.remove_dummy_variable_assignment
  |> Transform.remove_vardecl_default_rhs |> Transform.fold_newline_func_to_msg
  |> Transform.remove_optional_arguments |> Transform.simplify_boolean_expr
  |> fun body ->
  Stdio.printf "\nDecompiled code:\n";
  let printer = new CodeGen.code_printer ~print_addr Stdio.stdout "" in
  let lambdas = List.map ~f:decompile_function f.lambdas in
  printer#print_function
    {
      func = f.func;
      struc = f.struc;
      name = f.name;
      body;
      lambdas;
      parent = f.parent;
    }

let to_variable_list vars =
  List.map (Array.to_list vars) ~f:(fun v -> CodeGen.{ v; dims = [] })

let extract_array_dims stmt vars =
  let h = Stdlib.Hashtbl.create (Array.length vars) in
  if
    List.for_all
      (match stmt with { txt = Ast.Block stmts; _ } -> stmts | _ -> [ stmt ])
      ~f:(function
        | { txt = Ast.Return _; _ } -> true
        | {
            txt =
              Expression
                (Call (Builtin (Instructions.A_ALLOC, PageRef (_, v)), dims));
            _;
          } ->
            Stdlib.Hashtbl.add h v dims;
            true
        | {
            txt =
              Expression
                (Call
                   ( HllFunc ("Array", { name = "Alloc"; _ }),
                     Deref (PageRef (_, v)) :: dims ));
            _;
          } ->
            let dims =
              List.take_while dims ~f:(function
                | Number -1l -> false
                | _ -> true)
            in
            Stdlib.Hashtbl.add h v dims;
            true
        | _ -> false)
  then
    Some
      ( List.map (Array.to_list vars) ~f:(fun v ->
            match Stdlib.Hashtbl.find_opt h v with
            | Some dims -> CodeGen.{ v; dims }
            | None -> { v; dims = [] }),
        Stdlib.Hashtbl.length h > 0 )
  else None

let extract_array_dims_exn stmt vars =
  Option.value_exn
    (extract_array_dims stmt vars)
    ~message:"unexpected statement in array initializer"
  |> fst

type decompiled_ain = {
  structs : CodeGen.struct_t array;
  globals : CodeGen.variable list;
  srcs : (string * CodeGen.function_t list) list;
  ain_minor_version : int;
}

(* Ain 6 minor versions:
   - 6.0: Alice 2010, Shaman's Sanctuary, Daiteikoku, Rance Quest
   - 6.10 (DELG introduced): Oyako Rankan, Pastel Chime 3, Drapeko, Rance 01
   - 6.20 (MSG1 introduced): Rance 9, Blade Briders
   - 6.30 (SH_LOCALREF and other instructions removed): Evenicle, Rance 03 *)
let determine_ain_minor_version code =
  let has_sh_localref code =
    List.exists code ~f:(function
      | { txt = Instructions.SH_LOCALREF _; _ } -> true
      | _ -> false)
  in
  if Ain.ain.vers <> 6 then 0
  else if Array.is_empty Ain.ain.delg then 0
  else if Option.is_none Ain.ain.msg1_uk then 10
  else if has_sh_localref code then 20
  else 30

let is_rance7_bad_function (f : CodeGen.function_t) =
  match f with
  | {
      struc = Some {name = "tagBusho"; _};
      name = "getSp";
      body = { txt = (Block [{txt = Return (Some (Deref (PageRef (StructPage, {name = "m_sName"; _ })))); _ }]); _ }; _
    } -> true
  | _ -> false
[@@ocamlformat "disable"]

let decompile ~move_to_original_file ~continue_on_error =
  let code = Instructions.decode Ain.ain.code in
  let code = CodeSection.preprocess_ain_v0 code in
  Ain.ain.ifthen_optimized <- Instructions.detect_ifthen_optimization code;
  let files =
    CodeSection.parse code
    |> CodeSection.remove_overridden_functions ~move_to_original_file
    |> CodeSection.fix_or_remove_known_broken_functions
  in
  let structs =
    Array.map Ain.ain.strt ~f:(fun struc ->
        CodeGen.
          { struc; members = to_variable_list struc.members; methods = [] })
  in
  let globals = ref (to_variable_list Ain.ain.glob) in
  let srcs =
    List.map files ~f:(fun (fname, funcs) ->
        let decompiled_funcs = ref [] in
        let process_func func =
          try
            let f = decompile_function func in
            match f with
            | { struc = Some struc; _ } ->
                let s = structs.(struc.id) in
                if String.equal f.name "2" then
                  s.members <- extract_array_dims_exn f.body struc.members
                else if String.equal f.name "0" then (
                  match extract_array_dims f.body struc.members with
                  | Some (vs, true) -> s.members <- vs
                  | _ ->
                      s.methods <- f :: s.methods;
                      let body =
                        Transform.remove_array_initializer_call f.body
                      in
                      decompiled_funcs := { f with body } :: !decompiled_funcs)
                else if is_rance7_bad_function f then
                  Stdio.eprintf
                    "Warning: Removing ill-typed tagBusho::getSp() function\n"
                else (
                  if not f.func.is_lambda then s.methods <- f :: s.methods;
                  decompiled_funcs := f :: !decompiled_funcs)
            | { struc = None; name = "0"; _ } ->
                globals := extract_array_dims_exn f.body Ain.ain.glob
            | { struc = None; name = "NULL"; _ } -> ()
            | _ -> decompiled_funcs := f :: !decompiled_funcs
          with e ->
            Stdio.eprintf "Error while decompiling function %s\n" func.func.name;
            if continue_on_error then Stdio.eprintf "%s\n" (Exn.to_string e)
            else raise e
        in
        List.iter funcs ~f:process_func;
        (fname, List.rev !decompiled_funcs))
  in
  Array.iter structs ~f:(fun s -> s.methods <- List.rev s.methods);
  let ain_minor_version = determine_ain_minor_version code in
  { srcs; structs; globals = !globals; ain_minor_version }

let inspect funcname =
  let code = Instructions.decode Ain.ain.code in
  let code = CodeSection.preprocess_ain_v0 code in
  Ain.ain.ifthen_optimized <- Instructions.detect_ifthen_optimization code;
  let files =
    CodeSection.parse code
    |> CodeSection.remove_overridden_functions ~move_to_original_file:false
  in
  match
    List.find_map files ~f:(fun (_, funcs) ->
        List.find funcs ~f:(fun f ->
            String.equal f.CodeSection.func.name funcname))
  with
  | None -> failwith ("cannot find function " ^ funcname)
  | Some f -> inspect_function f

let export decompiled ain_path
    (output_to_printer : string -> (CodeGen.code_printer -> unit) -> unit) =
  let sources = ref [] in
  let output_source fname f =
    sources := fname :: !sources;
    output_to_printer fname f
  in
  output_source "constants.jaf" (fun pr -> pr#print_constants);
  output_source "classes.jaf" (fun pr ->
      Array.iter decompiled.structs ~f:(fun struc ->
          pr#print_struct_decl struc;
          pr#print_newline);
      Array.iter Ain.ain.fnct ~f:(fun ft ->
          pr#print_functype_decl "functype" ft);
      Array.iter Ain.ain.delg ~f:(fun ft ->
          pr#print_functype_decl "delegate" ft));
  output_source "globals.jaf" (fun pr -> pr#print_globals decompiled.globals);
  Array.iter Ain.ain.hll0 ~f:(fun hll ->
      output_to_printer
        ("HLL/" ^ hll.name ^ ".hll")
        (fun pr -> pr#print_hll hll.functions));
  output_source "HLL\\hll.inc" (fun pr -> pr#print_hll_inc);
  List.iter decompiled.srcs ~f:(fun (fname, funcs) ->
      if not (List.is_empty funcs) then
        output_source fname (fun pr ->
            List.iter funcs ~f:(fun func ->
                pr#print_function func;
                pr#print_newline)));
  output_to_printer "main.inc" (fun pr -> pr#print_inc (List.rev !sources));
  let project : CodeGen.project_t =
    {
      name = Stdlib.Filename.(remove_extension @@ basename ain_path);
      output_dir = Stdlib.Filename.dirname ain_path;
      ain_minor_version = decompiled.ain_minor_version;
    }
  in
  output_to_printer (project.name ^ ".pje") (fun pr -> pr#print_pje project);
  output_to_printer "debug_info.json" (fun pr -> pr#print_debug_info)
