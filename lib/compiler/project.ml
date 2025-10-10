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
open Pje

let rec load read_file pje_file initial_encoding =
  let pje_text = read_file pje_file in
  let lexbuf = Lexing.from_string pje_text in
  Lexing.set_filename lexbuf pje_file;
  let pje =
    try PjeParser.pje PjeLexer.token lexbuf initial_encoding with
    | PjeLexer.Error | PjeParser.Error -> CompileError.syntax_error lexbuf
    | Pje.KeyError key ->
        CompileError.raise ("Invalid name: " ^ key)
          (Lexing.lexeme_start_p lexbuf, Lexing.lexeme_end_p lexbuf)
  in
  let resolve =
    match Stdlib.Filename.dirname pje_file with
    | "." -> fun file -> file
    | dir -> fun file -> Stdlib.Filename.concat dir file
  in
  let read_file =
    match pje.source_dir with
    | "." -> read_file
    | dir -> fun file -> read_file (Stdlib.Filename.concat dir file)
  in
  let rec analyze_source_list = function
    | [] -> []
    | Jaf f :: rest ->
        let f_lower = String.lowercase f in
        if String.is_suffix f_lower ~suffix:".hll" then
          match rest with
          | Jaf name :: rest ->
              Hll (resolve f, name) :: analyze_source_list rest
          | _ ->
              (* FIXME: report correct source location *)
              CompileError.raise
                ("No import name for " ^ f)
                (Lexing.lexeme_start_p lexbuf, Lexing.lexeme_end_p lexbuf)
        else if String.is_suffix f_lower ~suffix:".inc" then
          Include (load read_file (resolve f) pje.encoding)
          :: analyze_source_list rest
        else Jaf (resolve f) :: analyze_source_list rest
    | _ -> failwith "unreachable"
  in
  pje.system_source <- analyze_source_list pje.system_source;
  pje.source <- analyze_source_list pje.source;
  pje

let load_pje read_file pje_file =
  let read_file =
    match Stdlib.Filename.dirname pje_file with
    | "." -> read_file
    | dir -> fun file -> read_file (Stdlib.Filename.concat dir file)
  in
  let pje = load read_file (Stdlib.Filename.basename pje_file) Pje.SJIS in
  pje.pje_path <- pje_file;
  pje
