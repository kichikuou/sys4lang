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

open Common
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

(* pass 1: Parse jaf/hll files and register the declarations *)
let parse_pass ctx sources read_file =
  List.map sources ~f:(function
    | Pje.Jaf f ->
        let jaf = parse_file Lexer.token Parser.jaf f read_file in
        Declarations.register ctx jaf;
        Jaf (f, jaf)
    | Pje.Hll (f, import_name) ->
        let hll = parse_file Lexer.token Parser.hll f read_file in
        let hll_name = Stdlib.Filename.(chop_extension (basename f)) in
        Hll (hll_name, import_name, hll)
    | _ -> failwith "unreachable")

(* pass 2: Resolve type specifiers, and write the AIN tables *)
let layout_pass ctx program =
  let libraries =
    List.filter_map program ~f:(function
      | Jaf (_, jaf) ->
          Declarations.resolve ctx jaf;
          None
      | Hll (hll_name, import_name, hll) ->
          Declarations.resolve_hll ctx hll;
          Some
            (Declarations.register_library ctx hll ~hll_name ~import_name, hll))
  in
  let jafs =
    List.concat_map program ~f:(function Jaf (_, jaf) -> jaf | Hll _ -> [])
  in
  Layout.layout ctx jafs;
  List.iter libraries ~f:(fun (lib, hll) -> Layout.add_library ctx lib hll);
  let initializers =
    List.map (Initializers.generate ctx jafs) ~f:(fun f -> Function f)
  in
  Declarations.register ctx initializers;
  Declarations.resolve ctx initializers;
  Layout.layout ctx initializers;
  (* The global initializer has the last index, and its code comes first. *)
  let global, classes =
    List.partition_tf initializers ~f:(function
      | Function { class_name = None; _ } -> true
      | _ -> false)
  in
  let null = Function (Initializers.null_function ()) in
  program @ [ Jaf ("", global @ classes @ [ null ]) ]

(* pass 3: Type checking. Constant evaluation reads expressions of other
   files, so it runs after the type analysis of all files. *)
let type_check_pass ctx program =
  List.iter program ~f:(function
    | Jaf (_, jaf) -> TypeAnalysis.check_types_exn ctx jaf
    | Hll _ -> ());
  List.iter program ~f:(function
    | Jaf (_, jaf) ->
        ConstEval.evaluate_constant_expressions ctx jaf;
        GlobalInit.write_initvals ctx jaf;
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
  let program = layout_pass ctx program in
  type_check_pass ctx program;
  codegen_pass ctx program debug_info
