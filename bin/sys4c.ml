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
  | Hll of string * string * declaration list

type program = source list

let read_file input_encoding file =
  let content =
    match file with
    | "-" -> In_channel.input_all In_channel.stdin
    | _ -> In_channel.read_all file
  in
  match input_encoding with
  | "utf8" -> content
  | "sjis" -> Sjis.to_utf8 content
  | _ -> failwith ("unsupported character encoding: " ^ input_encoding)

let parse_file ctx parse_func dir file input_encoding =
  let source = read_file input_encoding (Stdlib.Filename.concat dir file) in
  Hashtbl.add_exn ctx.files ~key:file ~data:source;
  let lexbuf = Lexing.from_string source in
  Lexing.set_filename lexbuf file;
  try parse_func Lexer.token lexbuf with
  | Lexer.Error | Parser.Error -> CompileError.syntax_error lexbuf
  | e -> raise e

(* pass 1: Parse jaf/hll files and create symbol table entries *)
let parse_pass ctx source_dir sources input_encoding =
  List.map sources ~f:(function
    | Pje.Jaf f ->
        let jaf = parse_file ctx Parser.jaf source_dir f input_encoding in
        Declarations.register_type_declarations ctx jaf;
        Jaf (f, jaf)
    | Pje.Hll (f, import_name) ->
        let hll = parse_file ctx Parser.hll source_dir f input_encoding in
        let hll_name = Filename.chop_extension (Filename.basename f) in
        Hll (hll_name, import_name, hll)
    | _ -> failwith "unreachable")

(* pass 2: Resolve type specifiers *)
let type_resolve_pass ctx program =
  let array_init_visitor = new ArrayInit.visitor ctx in
  List.iter program ~f:(function
    | Jaf (_, jaf) ->
        Declarations.resolve_types ctx jaf false;
        Declarations.define_types ctx jaf;
        List.iter ~f:array_init_visitor#visit_declaration jaf
    | Hll (hll_name, import_name, hll) ->
        Declarations.resolve_hll_types ctx hll;
        Declarations.resolve_types ctx hll false;
        Declarations.define_library ctx hll hll_name import_name);
  let initializers = array_init_visitor#generate_initializers () in
  program @ [ Jaf ("", initializers) ]

(* pass 3: Type checking *)
let type_check_pass ctx program =
  List.iter program ~f:(function
    | Jaf (_, jaf) ->
        TypeAnalysis.check_types ctx jaf;
        ConstEval.evaluate_constant_expressions ctx jaf;
        VariableAlloc.allocate_variables ctx jaf
    | Hll _ -> ())

(* pass 4: Code generation *)
let codegen_pass ctx program =
  List.iter program ~f:(function
    | Jaf (jaf_name, jaf) ->
        (* TODO: disable in release builds *)
        SanityCheck.check_invariants ctx jaf;
        Compiler.compile ctx jaf_name jaf
    | Hll _ -> ())

let do_compile source_dir sources output major minor input_encoding =
  let ctx = context_from_ain (Ain.create major minor) in
  try
    let program = parse_pass ctx source_dir sources input_encoding in
    let program = type_resolve_pass ctx program in
    type_check_pass ctx program;
    codegen_pass ctx program;
    (* write output .ain file to disk *)
    Ain.write_file ctx.ain output
  with CompileError.CompileError e ->
    CompileError.print_error e (fun file -> Hashtbl.find ctx.files file);
    exit 1

let do_build pje_file input_encoding =
  try
    let pje = Project.load_pje (read_file input_encoding) pje_file in
    let sources = Pje.collect_sources pje in
    do_compile
      Stdlib.Filename.(concat (dirname pje_file) pje.source_dir)
      sources (Pje.ain_path pje) 4 0 input_encoding
  with CompileError.CompileError e ->
    CompileError.print_error e (fun _ -> None);
    exit 1

let cmd_compile_jaf =
  Command.basic ~summary:"Compile .jaf files"
    ~readme:(fun () -> "Compile .jaf files.")
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
      and import_as =
        flag "-import-as" (listed string)
          ~doc:"hll_name=name Import hll_name as name"
      and input_encoding =
        flag "-input-encoding"
          (optional_with_default "utf8" string)
          ~doc:"encoding The input file encoding. sjis or utf8 (default)"
      and test =
        flag "-test" (optional Filename_unix.arg_type) ~doc:" Testing"
      in
      fun () ->
        if Option.is_some test then
          let ain = Ain.load (Option.value_exn test) in
          Ain.write_file ain output
        else
          let import_as =
            List.map import_as ~f:(fun s ->
                match String.split s ~on:'=' with
                | [ hll_name; name ] -> (hll_name, name)
                | _ -> failwith "invalid import-as format")
          in
          let sources =
            List.map sources ~f:(fun f ->
                if String.is_suffix (String.lowercase f) ~suffix:".hll" then
                  let import_name =
                    let hll_name =
                      Filename.chop_extension (Filename.basename f)
                    in
                    match
                      List.Assoc.find import_as ~equal:String.equal hll_name
                    with
                    | Some name -> name
                    | None -> hll_name
                  in
                  Pje.Hll (f, import_name)
                else Pje.Jaf f)
          in
          do_compile "." sources output major minor input_encoding)

let cmd_build_pje =
  Command.basic ~summary:"Build a System 4 project"
    ~readme:(fun () -> "Build a System 4 project from a .pje file.")
    Command.Let_syntax.(
      let%map_open project = anon ("project file" %: Filename_unix.arg_type)
      and input_encoding =
        flag "-input-encoding"
          (optional_with_default "utf8" string)
          ~doc:"encoding The input file encoding. sjis or utf8 (default)"
      in
      fun () -> do_build project input_encoding)

let () =
  Command_unix.run ~version:"0.1"
    (Command.group ~summary:"System 4 Compiler"
       [ ("compile", cmd_compile_jaf); ("build", cmd_build_pje) ])
