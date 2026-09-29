(* Copyright (C) 2026 kichikuou <KichikuouChrome@gmail.com>
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

(* Shared fixtures and output helpers for patch tests. *)

open Common
open Compiler
open Base

let with_files files f =
  let root = Stdlib.Filename.temp_file ~temp_dir:"." "patch-sources-" "" in
  Stdlib.Sys.remove root;
  Unix.mkdir root 0o700;
  let root = Unix.realpath root in
  let rec mkdir dir =
    if not (Stdlib.Sys.file_exists dir) then (
      mkdir (Stdlib.Filename.dirname dir);
      Unix.mkdir dir 0o700)
  in
  let rec remove path =
    if Poly.equal (Unix.lstat path).st_kind Unix.S_DIR then (
      Array.iter (Stdlib.Sys.readdir path) ~f:(fun name ->
          remove (Stdlib.Filename.concat path name));
      Unix.rmdir path)
    else Stdlib.Sys.remove path
  in
  Exn.protect
    ~f:(fun () ->
      List.iter files ~f:(fun (name, data) ->
          let path = Stdlib.Filename.concat root name in
          mkdir (Stdlib.Filename.dirname path);
          Stdio.Out_channel.write_all path ~data);
      f root)
    ~finally:(fun () -> remove root)

let base ?(version = 4) ?(hlls = []) source =
  let ctx = Jaf.context_from_ain (Ain.create version 0) in
  Compile.compile ctx
    (List.map hlls ~f:(fun (name, _) -> Pje.Hll (name ^ ".hll", name))
    @ [ Pje.Jaf "base.jaf" ])
    (DebugInfo.create ())
    (fun filename ->
      if String.equal filename "base.jaf" then source
      else
        List.Assoc.find_exn hlls ~equal:String.equal
          (Stdlib.Filename.chop_extension filename));
  ctx.ain

let with_program reference patch f =
  with_files
    [
      ("project.pje", {|Source = { "reference.jaf", }|});
      ("reference.jaf", reference);
      ("patch.jaf", patch);
    ]
    (fun root ->
      let cwd = Stdlib.Sys.getcwd () in
      Exn.protect
        ~f:(fun () ->
          Unix.chdir root;
          let program =
            PatchSources.load ~patch_files:[ "patch.jaf" ]
              (Stdlib.Filename.concat root "project.pje")
          in
          f program)
        ~finally:(fun () -> Unix.chdir cwd))

let with_project ?(targets = []) source f =
  with_files
    [
      ("project.pje", {|Source = { "reference.jaf", }|});
      ("reference.jaf", source);
    ]
    (fun root ->
      f (PatchSources.load ~targets (Stdlib.Filename.concat root "project.pje")))

let raw ain =
  let file = Stdlib.Filename.temp_file "patch-declarations-" ".ain" in
  Exn.protect
    ~finally:(fun () -> Stdlib.Sys.remove file)
    ~f:(fun () ->
      Stdio.Out_channel.with_file file ~binary:true ~f:(Ain.write ~raw:true ain);
      Stdio.In_channel.read_all file)

let print_error f =
  try f ()
  with CompileError.Compile_error e ->
    let rec print = function
      | CompileError.Error (message, _) -> Stdio.print_endline message
      | ErrorList errors -> List.iter errors ~f:print
    in
    print e

let print_new_code ain start =
  let dasm = Dasm.create ain in
  Dasm.jump dasm start;
  while not (Dasm.eof dasm) do
    let op = Bytecode.opcode_of_int (Dasm.opcode dasm) in
    let args =
      List.map2_exn (Dasm.argument_types dasm) (Dasm.arguments dasm)
        ~f:(fun kind arg ->
          match kind with
          | Bytecode.File -> "<patch>"
          | _ -> CompileTest.arg_to_string dasm ain kind arg)
    in
    Stdio.printf "%s%s\n"
      (Bytecode.string_of_opcode op)
      (if List.is_empty args then "" else " " ^ String.concat ~sep:", " args);
    Dasm.next dasm
  done

let print_result (result : Patch.sources_result) =
  List.iter result.added_types ~f:(fun (kind, name) ->
      Stdio.printf "Added %s: %s\n" kind name);
  Stdio.printf "functions: %s\n" (String.concat ~sep:", " result.functions)

let print_entries (result : Patch.sources_result) =
  List.iter result.added_entries ~f:(fun (kind, name) ->
      Stdio.printf "Added %s: %s\n" kind name)
