(* Copyright (C) 2025 kichikuou <KichikuouChrome@gmail.com>
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
module Out_channel = Stdio.Out_channel

type debug_mapping = { addr : int; src : int; line : int }

type t = {
  mutable sources : string list;
  mutable current_src : int;
  mutable mappings : debug_mapping list;
  mutable force_new_source : bool;
}

let create () =
  { sources = []; current_src = -1; mappings = []; force_new_source = false }

let add dbginfo addr file line =
  let src =
    match dbginfo.sources with
    | s :: _ when (not dbginfo.force_new_source) && String.equal s file ->
        dbginfo.current_src
    | _ ->
        dbginfo.sources <- file :: dbginfo.sources;
        dbginfo.current_src <- dbginfo.current_src + 1;
        dbginfo.current_src
  in
  dbginfo.force_new_source <- false;
  dbginfo.mappings <-
    (match dbginfo.mappings with
    | [] -> [ { addr; src; line } ]
    | last :: rest ->
        if last.addr = addr then
          (* If the last mapping has the same address, update it *)
          { addr; src; line } :: rest
        else if last.src = src && last.line = line then
          (* If the last mapping has the same source and line, keep it *)
          last :: rest
        else
          (* Otherwise, add a new mapping *)
          { addr; src; line } :: dbginfo.mappings)

let add_loc dbginfo addr (loc : Lexing.position * Lexing.position) =
  let Lexing.{ pos_fname; pos_lnum; _ } = fst loc in
  if pos_lnum <> 0 then add dbginfo addr pos_fname pos_lnum

let to_json dbginfo =
  let sources = List.rev_map dbginfo.sources ~f:(fun s -> `String s) in
  let mappings =
    List.rev_map dbginfo.mappings ~f:(fun { addr; src; line } ->
        `List [ `Int addr; `Int src; `Int line ])
  in
  `Assoc
    [
      ("version", `String "alpha-1");
      ("sources", `List sources);
      ("mappings", `List mappings);
    ]

let invalid file message =
  raise (Sys_error (file ^ ": invalid debug information: " ^ message))

let load file =
  let json =
    try Yojson.Basic.from_file file with
    | Yojson.Json_error message -> invalid file message
    | Sys_error _ as error -> raise error
  in
  let member name fields =
    match List.Assoc.find fields ~equal:String.equal name with
    | Some value -> value
    | None -> invalid file ("missing " ^ name)
  in
  let fields =
    match json with
    | `Assoc fields -> fields
    | _ -> invalid file "top-level value is not an object"
  in
  (match member "version" fields with
  | `String "alpha-1" -> ()
  | `String version -> invalid file ("unsupported version " ^ version)
  | _ -> invalid file "version is not a string");
  let sources =
    match member "sources" fields with
    | `List values ->
        List.map values ~f:(function
          | `String source -> source
          | _ -> invalid file "source path is not a string")
    | _ -> invalid file "sources is not an array"
  in
  let nr_sources = List.length sources in
  let mappings =
    match member "mappings" fields with
    | `List values ->
        List.map values ~f:(function
          | `List [ `Int addr; `Int src; `Int line ] -> { addr; src; line }
          | _ -> invalid file "mapping is not an array of three integers")
    | _ -> invalid file "mappings is not an array"
  in
  {
    sources = List.rev sources;
    current_src = nr_sources - 1;
    mappings = List.rev mappings;
    force_new_source = false;
  }

let start_patch dbginfo =
  if not (List.is_empty dbginfo.mappings) then dbginfo.force_new_source <- true

let has_mappings dbginfo = not (List.is_empty dbginfo.mappings)

let write_to_channel dbginfo channel =
  Yojson.Basic.to_channel channel (to_json dbginfo)

let write_to_file dbginfo file = Yojson.Basic.to_file file (to_json dbginfo)
