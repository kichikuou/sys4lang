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

%{
open Pje

type value =
  | Bool of bool
  | Int of int
  | String of string
  | List of string list

type toplevel =
  | KeyValue of (string * value)
  | Formation of string * string list
  | SyncFolder of (string * string) list
  | HashDefine of (string * value)

let to_pje toplevels path initial_encoding =
  let pje = default_pje path initial_encoding in
  let decode s =
    match pje.encoding with
    | UTF8 -> s
    | SJIS -> Common.Sjis.to_utf8 s
  in
  let to_unix_path s = Base.String.tr ~target:'\\' ~replacement:'/' (decode s) in
  let uses_msg1 = ref false in
  List.iter (function
    | KeyValue ("ProjectName", String v) -> pje.project_name <- decode v
    | KeyValue ("Encoding", String v) -> pje.encoding <- encoding_of_string v
    | KeyValue ("CodeName", String v) -> pje.code_name <- decode v
    | KeyValue ("GameVersion", Int v) -> pje.game_version <- v
    | KeyValue ("SourceDir", String v) -> pje.source_dir <- to_unix_path v
    | KeyValue ("HLLDir", String v) -> pje.hll_dir <- to_unix_path v
    | KeyValue ("ObjDir", String v) -> pje.obj_dir <- to_unix_path v
    | KeyValue ("OutputDir", String v) -> pje.output_dir <- to_unix_path v
    | KeyValue ("Source", List v) -> pje.source <- List.map (fun s -> Jaf (to_unix_path s)) v
    | KeyValue ("SystemSource", List v) -> pje.system_source <- List.map (fun s -> Jaf (to_unix_path s)) v
    | KeyValue ("HLL", List v) -> pje.hll <- List.map decode v
    | KeyValue ("CopyToDLL", List v) -> pje.copy_to_dll <- List.map to_unix_path v
    | KeyValue ("CopyToRun", List v) -> pje.copy_to_run <- List.map to_unix_path v
    | KeyValue ("CopyToDP", List v) -> pje.copy_to_dp <- List.map to_unix_path v
    | SyncFolder pairs -> pje.sync_folder <- List.map (fun (k, v) -> (to_unix_path k, to_unix_path v)) pairs
    | KeyValue ("ScenarioFuncA", List v) -> pje.scenario_func_a <- List.map decode v
    | KeyValue ("ScenarioFuncR", List v) -> pje.scenario_func_r <- List.map decode v
    | KeyValue ("ScenarioFuncNAME", List v) -> pje.scenario_func_name <- List.map decode v
    | Formation (name, defs) ->
        pje.formations <- { name = decode name; defs = List.map decode defs } :: pje.formations
    | KeyValue ("SyncLock", Bool v) -> pje.sync_lock <- v
    | KeyValue ("UpdateIDEPath", String v) -> pje.update_ide_path <- Some (to_unix_path v)
    | KeyValue (k, _) -> raise (KeyError k)
    | HashDefine ("_AINVERSION", Int v) -> pje.ain_version <- v
    | HashDefine ("_AINMINORVERSION", Int v) -> pje.ain_minor_version <- v
    | HashDefine ("_KEYCODE", Int v) -> pje.key_code <- Int32.of_int v
    | HashDefine ("_ISAI2FILE", Bool v) -> pje.is_ai2_file <- v
    | HashDefine ("_USESMSG1", Bool v) -> uses_msg1 := v
    | HashDefine _ -> ()
  ) toplevels;
  if !uses_msg1 && pje.ain_version = 6 && pje.ain_minor_version < 20 then
    pje.ain_minor_version <- 20;
  pje

%}

%token <bool> B_CONSTANT
%token <int> I_CONSTANT
%token <string> S_CONSTANT
%token <string> IDENTIFIER
/* punctuations */
%token EQUAL LBRACE RBRACE COMMA ARROW
/* keywords */
%token FORMATION SYNCFOLDER DEFINE HASH_DEFINE

%token EOF

%start pje
%type <Pje.encoding -> Pje.t> pje

%%

pje
  : toplevel* EOF { to_pje $1 $startpos.Lexing.pos_fname }

toplevel
  : IDENTIFIER EQUAL value { KeyValue ($1, $3) }
  | FORMATION S_CONSTANT LBRACE flexible_list(COMMA, formation_item) RBRACE { Formation ($2, $4) }
  | SYNCFOLDER EQUAL LBRACE flexible_list(COMMA, separated_pair(S_CONSTANT, ARROW, S_CONSTANT)) RBRACE { SyncFolder $4 }
  | HASH_DEFINE IDENTIFIER value { HashDefine ($2, $3) }

value
  : B_CONSTANT { Bool $1 }
  | I_CONSTANT { Int $1 }
  | S_CONSTANT { String $1 }
  | LBRACE flexible_list(COMMA, S_CONSTANT) RBRACE { List $2 }

formation_item
  : DEFINE EQUAL S_CONSTANT { $3 }

(* delimited list where the final delimiter is optional *)
flexible_list(delim, X)
  : (* empty *) { [] }
  | X { [$1] }
  | X delim flexible_list(delim, X) { $1 :: $3 }
