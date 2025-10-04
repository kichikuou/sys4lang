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
open Cmdliner
open Decompiler

let rec mkdir_p path =
  if not (Stdlib.Sys.file_exists path) then (
    let parent = Stdlib.Filename.dirname path in
    if not (String.equal parent path) then mkdir_p parent;
    Stdlib.Sys.mkdir path 0o755)
  else if not (Stdlib.Sys.is_directory path) then
    failwith (path ^ " exists but is not a directory")

let output_printer_getter out_dir_opt fname f =
  match out_dir_opt with
  | None ->
      Stdio.printf "FILE %s\n\n" fname;
      f (CodeGen.create_printer Stdio.stdout "")
  | Some out_dir ->
      let fname_components = String.split fname ~on:'\\' in
      let unix_fname = String.concat ~sep:"/" fname_components in
      let output_path = Stdlib.Filename.concat out_dir unix_fname in
      mkdir_p (Stdlib.Filename.dirname output_path);
      let outc = Stdio.Out_channel.create output_path in
      f (CodeGen.create_printer outc unix_fname);
      Out_channel.close outc

let sys4dc output_dir inspect_function print_addr move_to_original_file ain_file
    =
  Ain.load ain_file;
  match inspect_function with
  | None ->
      let decompiled = Decompile.decompile move_to_original_file in
      Decompile.export decompiled
        (Stdlib.Filename.basename ain_file)
        (output_printer_getter output_dir)
        ~print_addr
  | Some funcname -> Decompile.inspect funcname ~print_addr

let cmd =
  let doc = "Decompile an .ain file" in
  let info = Cmd.info "sys4dc" ~doc in
  let output_dir =
    let doc = "Output directory" in
    let docv = "DIRECTORY" in
    Cmdliner.Arg.(value & opt (some string) None & info [ "o" ] ~docv ~doc)
  in
  let inspect_function =
    let doc = "Inspect the decompilation process of a function" in
    let docv = "FUNCTION" in
    Cmdliner.Arg.(
      value & opt (some string) None & info [ "inspect" ] ~docv ~doc)
  in
  let print_addr =
    let doc = "Print addresses" in
    Cmdliner.Arg.(value & flag & info [ "address" ] ~doc)
  in
  let move_to_original_file =
    let doc =
      "Move the overridden functions to the files where they were originally \
       defined.  Useful for mods made with AinDecompiler."
    in
    Cmdliner.Arg.(value & flag & info [ "move-to-original-file" ] ~doc)
  in
  let ain_file =
    let doc = "The .ain file to decompile" in
    let docv = "AIN_FILE" in
    Cmdliner.Arg.(required & pos 0 (some string) None & info [] ~docv ~doc)
  in
  Cmd.v info
    Term.(
      const sys4dc $ output_dir $ inspect_function $ print_addr
      $ move_to_original_file $ ain_file)

let () = Stdlib.exit (Cmd.eval cmd)
