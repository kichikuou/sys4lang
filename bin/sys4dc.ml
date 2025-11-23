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

let output_printer_getter ~print_addr out_dir fname f =
  if String.(out_dir = "-") then (
    Stdio.printf "FILE %s\n\n" fname;
    f (new CodeGen.code_printer ~print_addr Stdio.stdout ""))
  else
    let fname_components = String.split fname ~on:'\\' in
    let unix_fname = String.concat ~sep:"/" fname_components in
    let output_path = Stdlib.Filename.concat out_dir unix_fname in
    mkdir_p (Stdlib.Filename.dirname output_path);
    let outc = Stdio.Out_channel.create output_path in
    f (new CodeGen.code_printer ~print_addr outc unix_fname);
    Out_channel.close outc

let sys4dc output_dir inspect_function print_addr move_to_original_file
    continue_on_error ain_file =
  let output_dir = Option.value output_dir ~default:"." in
  Ain.load ain_file;
  match inspect_function with
  | None ->
      let decompiled =
        Decompile.decompile ~move_to_original_file ~continue_on_error
      in
      (* reroot ain_file to output_dir if possible *)
      let ain_path =
        Fpath.(
          let root =
            v @@ if String.(output_dir = "-") then "." else output_dir
          in
          match relativize ~root (v ain_file) with
          | Some p -> to_string @@ normalize p
          | None -> ain_file)
      in
      Decompile.export decompiled ain_path
        (output_printer_getter ~print_addr output_dir)
  | Some funcname -> Decompile.inspect funcname ~print_addr

let cmd =
  let version =
    Option.map (Build_info.V1.version ()) ~f:Build_info.V1.Version.to_string
  in
  let doc = "Decompile an .ain file" in
  let info = Cmd.info "sys4dc" ?version ~doc in
  let output_dir =
    let doc = "Output directory. Use '-' to print everything to stdout." in
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
  let continue_on_error =
    let doc = "Continue decompilation even if an error is encountered." in
    Cmdliner.Arg.(value & flag & info [ "continue-on-error" ] ~doc)
  in
  let ain_file =
    let doc = "The .ain file to decompile" in
    let docv = "AIN_FILE" in
    Cmdliner.Arg.(required & pos 0 (some string) None & info [] ~docv ~doc)
  in
  Cmd.v info
    Term.(
      const sys4dc $ output_dir $ inspect_function $ print_addr
      $ move_to_original_file $ continue_on_error $ ain_file)

let () = Stdlib.exit (Cmd.eval cmd)
