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
  Declarations.resolve_types ctx hll false;
  Declarations.define_library ctx hll (get_lib_name hll_file)

let compile_sources sources major minor =
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
  let ctx = context_from_ain ain in
  let compile_file f =
    if Filename.check_suffix f ".jaf" || String.equal f "-" then
      compile_jaf ctx f false
    else if Filename.check_suffix f ".hll" then compile_hll ctx f
    else failwith "unsupported file type"
  in
  List.iter sources ~f:compile_file;
  ctx.ain

let do_compile sources output major minor =
  try
    (* create output .ain file by compiling/linking inputs *)
    let ain = compile_sources sources major minor in
    (* final check for undefined functions *)
    SanityCheck.check_undefined ain;
    (* write output .ain file to disk *)
    Ain.write_file ain output
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
