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
open Sys4cLib
open Jaf

type source =
  | Jaf of string * declaration list
  | Hll of string * declaration list

type program = source list

let parse_file parse_func file =
  let do_parse ch =
    let lexbuf = Lexing.from_channel ch in
    Lexing.set_filename lexbuf file;
    try parse_func Lexer.token lexbuf with
    | Lexer.Error | Parser.Error -> CompileError.syntax_error lexbuf
    | e -> raise e
  in
  match file with
  | "-" -> do_parse In_channel.stdin
  | path -> In_channel.with_file path ~f:(fun file -> do_parse file)

(* pass 1: Parse jaf/hll files and create symbol table entries *)
let pass_one ctx sources =
  List.map sources ~f:(fun f ->
      if Filename.check_suffix f ".jaf" || String.equal f "-" then (
        let jaf = parse_file Parser.jaf f in
        Declarations.register_type_declarations ctx jaf;
        Jaf (f, jaf))
      else if Filename.check_suffix f ".hll" then
        let hll = parse_file Parser.hll f in
        let lib_name = Filename.chop_extension (Filename.basename f) in
        Hll (lib_name, hll)
      else failwith "unsupported file type")

(* pass 2: Resolve type specifiers *)
let pass_two ctx program =
  let array_init_visitor = new ArrayInit.visitor ctx in
  List.iter program ~f:(function
    | Jaf (_, jaf) ->
        Declarations.resolve_types ctx jaf false;
        Declarations.define_types ctx jaf;
        List.iter ~f:array_init_visitor#visit_declaration jaf
    | Hll (lib_name, hll) ->
        Declarations.resolve_types ctx hll false;
        Declarations.define_library ctx hll lib_name);
  let initializers = array_init_visitor#generate_initializers () in
  program @ [ Jaf ("", initializers) ]

(* pass 3: Type checking and code generation *)
let pass_three ctx program =
  List.iter program ~f:(function
    | Jaf (jaf_name, jaf) ->
        TypeAnalysis.check_types ctx jaf;
        ConstEval.evaluate_constant_expressions ctx jaf;
        VariableAlloc.allocate_variables ctx jaf;
        (* TODO: disable in release builds *)
        SanityCheck.check_invariants ctx jaf;
        Compiler.compile ctx jaf_name jaf
    | Hll _ -> ())

let do_compile sources output major minor =
  try
    let ctx = context_from_ain (Ain.create major minor) in
    let program = pass_one ctx sources in
    let program = pass_two ctx program in
    pass_three ctx program;
    (* write output .ain file to disk *)
    Ain.write_file ctx.ain output
  with CompileError.CompileError e ->
    CompileError.print_error e;
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
      and test =
        flag "-test" (optional Filename_unix.arg_type) ~doc:" Testing"
      in
      fun () ->
        if Option.is_some test then
          let ain = Ain.load (Option.value_exn test) in
          Ain.write_file ain output
        else do_compile sources output major minor)

let () = Command_unix.run ~version:"0.1" cmd_compile_jaf
