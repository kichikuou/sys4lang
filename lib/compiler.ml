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
open Jaf

type source =
  | Jaf of string * declaration list
  | Hll of string * string * declaration list

type program = source list

let parse_file lexer parser file read_file =
  let source = read_file file in
  let lexbuf = Lexing.from_string source in
  Lexing.set_filename lexbuf file;
  try parser lexer lexbuf with
  | Lexer.Error | Parser.Error -> CompileError.syntax_error lexbuf
  | e -> raise e

(* pass 1: Parse jaf/hll files and create symbol table entries *)
let parse_pass ctx sources read_file =
  List.map sources ~f:(function
    | Pje.Jaf f ->
        let jaf = parse_file Lexer.token Parser.jaf f read_file in
        Declarations.register_type_declarations ctx jaf;
        Jaf (f, jaf)
    | Pje.Hll (f, import_name) ->
        let hll = parse_file Lexer.token Parser.hll f read_file in
        let hll_name = Stdlib.Filename.(chop_extension (basename f)) in
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
        TypeAnalysis.check_types_exn ctx jaf;
        ConstEval.evaluate_constant_expressions ctx jaf;
        VariableAlloc.allocate_variables ctx jaf
    | Hll _ -> ())

(* pass 4: Code generation *)
let codegen_pass ctx program debug_info =
  List.iter program ~f:(function
    | Jaf (jaf_name, jaf) ->
        (* TODO: disable in release builds *)
        SanityCheck.check_invariants ctx jaf;
        Codegen.compile ctx jaf_name jaf debug_info
    | Hll _ -> ())

let compile ctx sources debug_info read_file =
  let program = parse_pass ctx sources read_file in
  let program = type_resolve_pass ctx program in
  type_check_pass ctx program;
  codegen_pass ctx program debug_info
