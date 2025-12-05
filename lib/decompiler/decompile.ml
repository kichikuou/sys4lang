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
  let struc = match f.owner with Some (Struct s) -> Some s | _ -> None in
  let body =
    BasicBlock.create f
    |> BasicBlock.generate_var_decls f.func
    |> ControlFlow.analyze
    |> (new TypeAnalysis.analyzer f.func struc)#analyze_statement
    |> Transform.expand_else_scope |> Transform.rename_labels
    |> Transform.recover_loop_initializer |> Transform.recognize_foreach
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
    { func = f.func; struc; name = f.name; body; lambdas; parent = f.parent }

let inspect_function (f : CodeSection.function_t) ~print_addr =
  let struc = match f.owner with Some (Struct s) -> Some s | _ -> None in
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
  |> (new TypeAnalysis.analyzer f.func struc)#analyze_statement
  |> Transform.expand_else_scope |> Transform.rename_labels
  |> Transform.recover_loop_initializer |> Transform.recognize_foreach
  |> Transform.remove_implicit_array_free
  |> Transform.remove_array_free_for_dead_arrays
  |> Transform.remove_generated_lockpeek |> Transform.remove_redundant_return
  |> Transform.remove_dummy_variable_assignment
  |> Transform.remove_vardecl_default_rhs |> Transform.fold_newline_func_to_msg
  |> Transform.remove_optional_arguments |> Transform.simplify_boolean_expr
  |> fun body ->
  let printer = new CodeGen.code_printer ~print_addr "" in
  let lambdas = List.map ~f:decompile_function f.lambdas in
  printer#print_function
    { func = f.func; struc; name = f.name; body; lambdas; parent = f.parent };
  Stdio.printf "\nDecompiled code:\n%s\n" (Buffer.contents printer#get_buffer)

let to_variable_list vars =
  List.map (Array.to_list vars) ~f:CodeGen.from_ain_variable

type analyzed_initializer_function = {
  is_empty : bool;
  vtable : int array option;
  vars : CodeGen.variable list;
}

let analyze_initializer_function stmt vars =
  let stmts =
    match stmt with
    | { txt = Ast.Block stmts; _ } -> List.rev stmts
    | _ -> [ stmt ]
  in
  let h_dims = Stdlib.Hashtbl.create (Array.length vars) in
  let h_initvals = Stdlib.Hashtbl.create (Array.length vars) in
  let vtable = ref [||] in
  List.iter stmts ~f:(function
    | {
        txt =
          Expression
            (Call (Builtin (Instructions.A_ALLOC, PageRef (_, v)), dims));
        _;
      } ->
        Stdlib.Hashtbl.add h_dims v dims
    | {
        txt =
          Expression
            (Call
               ( HllFunc ("Array", { name = "Alloc"; _ }),
                 Deref (PageRef (_, v)) :: dims ));
        _;
      } -> (
        let dims =
          List.take_while dims ~f:(function Number -1l -> false | _ -> true)
        in
        match (v.name, dims) with
        | "<vtable>", [ Number len ] ->
            vtable := Array.create ~len:(Int32.to_int_exn len) (-1)
        | _ -> Stdlib.Hashtbl.add h_dims v dims)
    | {
        txt =
          Expression
            (AssignOp
               ( ASSIGN,
                 ArrayRef (Deref (PageRef (StructPage, v)), Number i),
                 Number m ));
        _;
      }
      when String.equal v.name "<vtable>" ->
        !vtable.(Int32.to_int_exn i) <- Int32.to_int_exn m
    | {
        txt =
          Expression
            ( AssignOp (_, PageRef ((StructPage | GlobalPage), v), e)
            | Call
                ( Builtin2
                    (X_SET, Deref (PageRef ((StructPage | GlobalPage), v))),
                  [ e ] ) );
        _;
      }
      when Ain.ain.vers >= 12 ->
        Stdlib.Hashtbl.add h_initvals v e
    | stmt ->
        Printf.failwithf "unexpected statement in initializer function: %s"
          (Ast.show_statement stmt.txt)
          ());
  {
    is_empty = List.is_empty stmts;
    vars =
      List.map (Array.to_list vars) ~f:(fun v ->
          let var = CodeGen.from_ain_variable v in
          {
            var with
            dims =
              (match Stdlib.Hashtbl.find_opt h_dims v with
              | None -> var.dims
              | Some dims -> dims);
            initval =
              Option.first_some
                (Stdlib.Hashtbl.find_opt h_initvals v)
                var.initval;
          });
    vtable = (if Array.is_empty !vtable then None else Some !vtable);
  }

let extract_enum_values = function
  | Ast.Return (Some e) ->
      let rec extract = function
        | Ast.TernaryOp (BinaryOp (EQUALE, _, EnumValue (_, n)), String s, rest)
          ->
            (s, n) :: extract rest
        | String "" -> []
        | _ -> failwith "unexpected expression in enum stringifier"
      in
      extract e
  | _ -> failwith "unexpected statement in enum stringifier"

type decompiled_ain = {
  structs : CodeGen.struct_t array;
  globals : CodeGen.variable list;
  enums : CodeGen.enum_t array;
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

let process_generated_constructors (structs : CodeGen.struct_t array) =
  List.map ~f:(fun (fname, funcs) ->
      let funcs =
        List.filter funcs ~f:(fun func ->
            match func with
            | { CodeSection.owner = Some (Struct struc); name = "0" | "2"; _ }
              -> (
                try
                  let f = decompile_function func in
                  let inits =
                    analyze_initializer_function f.body struc.members
                  in
                  if String.equal f.name "2" || not inits.is_empty then (
                    let s = structs.(struc.id) in
                    s.members <- inits.vars;
                    Option.iter inits.vtable ~f:(fun vt ->
                        Ain.ain.strt.(struc.id).vtable <- vt);
                    false)
                  else true
                with _ -> true)
            | _ -> true)
      in
      (fname, funcs))

let decompile ~move_to_original_file ~continue_on_error =
  let code = Instructions.decode Ain.ain.code in
  let code = CodeSection.preprocess_ain_v0 code in
  Ain.ain.ifthen_optimized <- Instructions.detect_ifthen_optimization code;
  let structs =
    Array.map Ain.ain.strt ~f:(fun struc ->
        CodeGen.
          { struc; members = to_variable_list struc.members; methods = [] })
  in
  let files =
    CodeSection.parse code
    |> CodeSection.remove_overridden_functions ~move_to_original_file
    |> CodeSection.fix_or_remove_known_broken_functions
    (* For vtable analysis, generated constructors need to be processed first. *)
    |> process_generated_constructors structs
  in
  let enums =
    Array.map Ain.ain.enum ~f:(fun name -> CodeGen.{ name; values = [] })
  in
  let globals = ref (to_variable_list Ain.ain.glob) in
  let srcs =
    List.map files ~f:(fun (fname, funcs) ->
        let decompiled_funcs = ref [] in
        let process_func func =
          try
            let f = decompile_function func in
            match func with
            | { owner = Some (Enum id); name = "String"; _ } ->
                enums.(id).values <- extract_enum_values f.body.txt
            | { owner = Some (Enum _); _ } -> () (* ignore *)
            | { owner = Some (Struct struc); _ } ->
                let s = structs.(struc.id) in
                let f =
                  if String.equal f.name "0" then
                    {
                      f with
                      body = Transform.remove_generated_initializer_call f.body;
                    }
                  else f
                in
                if is_rance7_bad_function f then
                  Stdio.eprintf
                    "Warning: Removing ill-typed tagBusho::getSp() function\n"
                else (
                  if not f.func.is_lambda then s.methods <- f :: s.methods;
                  decompiled_funcs := f :: !decompiled_funcs)
            | { owner = None; name = "0"; _ } ->
                globals :=
                  (analyze_initializer_function f.body Ain.ain.glob).vars
            | { owner = None; name = "NULL"; _ } -> ()
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
  { srcs; structs; globals = !globals; enums; ain_minor_version }

let inspect funcname =
  let code = Instructions.decode Ain.ain.code in
  let code = CodeSection.preprocess_ain_v0 code in
  Ain.ain.ifthen_optimized <- Instructions.detect_ifthen_optimization code;
  let structs =
    Array.map Ain.ain.strt ~f:(fun struc ->
        CodeGen.
          { struc; members = to_variable_list struc.members; methods = [] })
  in
  let files =
    CodeSection.parse code
    |> CodeSection.remove_overridden_functions ~move_to_original_file:false
    |> process_generated_constructors structs
  in
  match
    List.find_map files ~f:(fun (_, funcs) ->
        List.find funcs ~f:(fun f ->
            String.equal f.CodeSection.func.name funcname))
  with
  | None -> failwith ("cannot find function " ^ funcname)
  | Some f -> inspect_function f

let export ~print_addr decompiled ain_path write_to_file =
  let sources = ref [] in
  let dbginfo = CodeGen.create_debug_info () in
  let generate ?(add_to_inc = true) fname f =
    if add_to_inc then sources := fname :: !sources;
    let fname_components = String.split fname ~on:'\\' in
    let unix_fname = String.concat ~sep:"/" fname_components in
    let pr =
      new CodeGen.code_printer
        ~print_addr ~dbginfo ~enums:decompiled.enums unix_fname
    in
    f pr;
    write_to_file unix_fname pr#get_buffer
  in
  generate "constants.jaf" (fun pr -> pr#print_constants);
  generate "classes.jaf" (fun pr ->
      Array.iter decompiled.structs ~f:(fun struc ->
          pr#print_struct_decl struc;
          pr#print_newline);
      Array.iter decompiled.enums ~f:(fun enum ->
          pr#print_enum_decl enum;
          pr#print_newline);
      Array.iter Ain.ain.fnct ~f:(fun ft ->
          pr#print_functype_decl "functype" ft);
      Array.iter Ain.ain.delg ~f:(fun ft ->
          pr#print_functype_decl "delegate" ft));
  generate "globals.jaf" (fun pr -> pr#print_globals decompiled.globals);
  Array.iter Ain.ain.hll0 ~f:(fun hll ->
      generate ~add_to_inc:false
        ("HLL/" ^ hll.name ^ ".hll")
        (fun pr -> pr#print_hll hll.functions));
  generate "HLL\\hll.inc" (fun pr -> pr#print_hll_inc);
  List.iter decompiled.srcs ~f:(fun (fname, funcs) ->
      if not (List.is_empty funcs) then
        generate fname (fun pr ->
            List.iter funcs ~f:(fun func ->
                pr#print_function func;
                pr#print_newline)));
  generate ~add_to_inc:false "main.inc" (fun pr ->
      pr#print_inc (List.rev !sources));
  let project : CodeGen.project_t =
    {
      name = Stdlib.Filename.(remove_extension @@ basename ain_path);
      output_dir = Stdlib.Filename.dirname ain_path;
      ain_minor_version = decompiled.ain_minor_version;
    }
  in
  generate ~add_to_inc:false (project.name ^ ".pje") (fun pr ->
      pr#print_pje project);
  generate ~add_to_inc:false "debug_info.json" (fun pr -> pr#print_debug_info)
