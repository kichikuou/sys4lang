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

let read_text_file input_encoding file =
  let content =
    match file with
    | "-" -> In_channel.input_all In_channel.stdin
    | _ -> In_channel.read_all file
  in
  match input_encoding with
  | "utf8" -> content
  | "sjis" -> Sjis.to_utf8 content
  | _ -> failwith ("unsupported character encoding: " ^ input_encoding)

let handle_errors f get_content =
  try f () with
  | CompileError.Compile_error e ->
      CompileError.print_error e get_content;
      exit 1
  | Sys_error msg ->
      Stdio.print_endline msg;
      exit 1

let do_compile sources output major minor import_as input_encoding =
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
            let hll_name = Filename.chop_extension (Filename.basename f) in
            match List.Assoc.find import_as ~equal:String.equal hll_name with
            | Some name -> name
            | None -> hll_name
          in
          Pje.Hll (f, import_name)
        else Pje.Jaf f)
  in
  let ctx = Jaf.context_from_ain (Ain.create major minor) in
  handle_errors
    (fun () ->
      Compiler.compile ctx sources (read_text_file input_encoding);
      Ain.write_file ctx.ain output)
    (fun file -> Hashtbl.find ctx.files file)

let do_build pje_file input_encoding =
  let pje =
    handle_errors
      (fun () -> Project.load_pje (read_text_file input_encoding) pje_file)
      (fun _ -> None)
  in
  let ctx = Jaf.context_from_ain (Ain.create pje.ain_version 0) in
  handle_errors
    (fun () ->
      let source_dir =
        Stdlib.Filename.(concat (dirname pje_file) pje.source_dir)
      in
      let read_file file =
        let file = Stdlib.Filename.(concat source_dir file) in
        read_text_file input_encoding file
      in
      let sources = Pje.collect_sources pje in
      Compiler.compile ctx sources read_file;
      Ain.write_file ctx.ain (Pje.ain_path pje))
    (fun file -> Hashtbl.find ctx.files file)

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
        else do_compile sources output major minor import_as input_encoding)

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
