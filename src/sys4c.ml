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

open Core
open Printf
open Jaf

let parse_jaf jaf_file =
  let do_parse file =
    let lexbuf = Lexing.from_channel file in
    Lexing.set_filename lexbuf jaf_file;
    try Parser.jaf Lexer.token lexbuf with
    | Lexer.Error | Parser.Error -> CompileError.syntax_error lexbuf
    | e -> raise e
  in
  match jaf_file with
  | "-" -> do_parse In_channel.stdin
  | path -> In_channel.with_file path ~f:(fun file -> do_parse file)

let compile_jaf ctx jaf_file decl_only =
  let jaf = parse_jaf jaf_file in
  Declarations.register_type_declarations ctx jaf;
  Declarations.resolve_types ctx jaf decl_only;
  Declarations.define_types ctx jaf;
  if not decl_only then (
    TypeAnalysis.check_types ctx jaf;
    ConstEval.evaluate_constant_expressions ctx jaf;
    VariableAlloc.allocate_variables ctx jaf;
    SanityCheck.check_invariants ctx jaf;
    (* TODO: disable in release builds *)
    Compiler.compile ctx jaf)

let compile_hll ctx hll_file =
  let do_parse file =
    let lexbuf = Lexing.from_channel file in
    Lexing.set_filename lexbuf hll_file;
    try Parser.hll Lexer.token lexbuf with
    | Lexer.Error | Parser.Error -> CompileError.syntax_error lexbuf
    | e -> raise e
  in
  let get_lib_name filename =
    Filename.chop_extension (Filename.basename filename)
  in
  let hll = In_channel.with_file hll_file ~f:(fun file -> do_parse file) in
  Declarations.define_library ctx hll (get_lib_name hll_file)

let compile_sources sources major minor decl_only =
  (* open/create the output .ain file *)
  (* XXX: if the first file is a .ain file, open it instead of linking against a blank file *)
  let ain, sources =
    match sources with
    | [] -> (Ain.create major minor, [ "-" ])
    | file :: rest when Filename.check_suffix file ".ain" ->
        (Ain.load file, rest)
    | _ -> (Ain.create major minor, sources)
  in
  (* compile sources *)
  let ctx = { ain; const_vars = [] } in
  let compile_file f =
    if Filename.check_suffix f ".jaf" || String.equal f "-" then
      compile_jaf ctx f decl_only
    else if Filename.check_suffix f ".hll" then compile_hll ctx f
    else if Filename.check_suffix f ".ain" then
      Link.link ctx.ain (Ain.load f) decl_only
    else failwith "unsupported file type"
  in
  List.iter sources ~f:compile_file;
  ctx.ain

let format_location (s, e) =
  Lexing.(
    let scol = s.pos_cnum - s.pos_bol + 1 in
    let ecol = e.pos_cnum - e.pos_bol + 1 in
    if s.pos_lnum = e.pos_lnum then
      sprintf "%s:%d:%d-%d" s.pos_fname s.pos_lnum scol ecol
    else sprintf "%s:%d:%d-%d:%d" s.pos_fname s.pos_lnum scol e.pos_lnum ecol)

let format_node_location node = format_location (ast_node_pos node)

let do_compile sources output major minor decl_only compile_unit match_decls =
  try
    (* create output .ain file by compiling/linking inputs *)
    let ain = compile_sources sources major minor decl_only in
    (* -m option: check if declarations match then return status code *)
    (match match_decls with
    | [] -> ()
    | _ ->
        let decl_ain = compile_sources match_decls major minor true in
        let matched = Link.declarations_match decl_ain ain in
        exit (if matched then 0 else 1));
    (* -c/-d option: skip final check for undefined functions *)
    if (not compile_unit) && not decl_only then Link.check_undefined ain;
    (* write output .ain file to disk *)
    Ain.write_file ain output
  with
  | CompileError.Syntax_error (s, e) ->
      printf "%s: Syntax error\n" (format_location (s, e));
      exit 1
  | CompileError.Type_error (expected, actual, parent) ->
      let s_expected = jaf_type_to_string expected in
      let s_actual =
        match actual with
        | None -> "void"
        | Some expr -> jaf_type_to_string expr.ty
      in
      printf "%s: Type error: expected %s; got %s\n"
        (format_node_location parent)
        s_expected s_actual;
      Option.iter actual ~f:(fun e -> printf "\tat: %s\n" (expr_to_string e));
      printf "\tin: %s\n" (ast_to_string parent);
      exit 1
  | CompileError.Undefined_variable (name, node) ->
      printf "%s: Undefined variable: %s\n" (format_node_location node) name;
      exit 1
  | CompileError.Arity_error (f, args, parent) ->
      printf
        "%s: wrong number of arguments to function %s (expected %d; got %d)\n"
        (format_node_location parent)
        f.name f.nr_args (List.length args);
      printf "\tin: %s\n" (ast_to_string parent);
      exit 1
  | CompileError.Not_lvalue_error (expr, parent) ->
      printf "%s: not an lvalue: %s\n"
        (format_node_location parent)
        (expr_to_string expr);
      printf "\tin: %s\n" (ast_to_string parent);
      exit 1
  | CompileError.Const_error var ->
      printf "%s: %s\n"
        (format_location var.location)
        (match var.initval with
        | Some _ -> "value of const variable is not constant"
        | None -> "const variable lacks initializer");
      printf "\tin: %s\n" (var_to_string var);
      exit 1
  | CompileError.CompileError (msg, node) ->
      printf "%s: %s\n" (format_node_location node) msg;
      printf "\tin: %s\n" (ast_to_string node);
      exit 1
  | CompileError.LinkError msg ->
      printf "Error: %s\n" msg;
      exit 1
  | CompileError.CompilerBug (msg, node) ->
      (match node with
      | Some n ->
          printf "%s: %s\n\tin: %s\n" (format_node_location n) msg
            (ast_to_string n)
      | None -> printf "Error: %s\n" msg);
      printf "(This is a compiler bug!)";
      exit 1
  | CompileError.LinkerBug msg ->
      printf "Error: %s\n" msg;
      printf "(This is a linker bug!)";
      exit 1

let cmd_compile_jaf =
  Command.basic ~summary:"Compile a .jaf file"
    ~readme:(fun () ->
      "Compile a .jaf file, optionally appending to an existing .ain file.")
    Command.Let_syntax.(
      let%map_open sources =
        anon (sequence ("source files" %: Filename_unix.arg_type))
      and output =
        flag "-output"
          (optional_with_default "out.ain" Filename_unix.arg_type)
          ~doc:"out-file The output .ain file"
      and major =
        flag "-ain-version"
          (optional_with_default 4 int)
          ~doc:"version The output .ain file version (default: 4)"
      and minor =
        flag "-ain-minor-version"
          (optional_with_default 0 int)
          ~doc:"version The output .ain file minor version (default: 0)"
      and decl_only =
        flag "-declarations-only" no_arg ~doc:" Output declarations only"
      and compile_unit =
        flag "-compile-unit" no_arg
          ~doc:" Compile as a unit (allow undefined functions)"
      and match_decls =
        flag "-match-declarations"
          (listed Filename_unix.arg_type)
          ~doc:"ain-file Compare declarations against the given .ain file"
      and test =
        flag "-test" (optional Filename_unix.arg_type) ~doc:" Testing"
      in
      fun () ->
        if Option.is_some test then
          let ain = Ain.load (Option.value_exn test) in
          Ain.write_file ain output
        else
          do_compile sources output major minor decl_only compile_unit
            match_decls)

let () = Command_unix.run ~version:"0.1" cmd_compile_jaf
