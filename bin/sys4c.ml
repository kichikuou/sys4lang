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

open Common
open Base
open Compiler
open Cmdliner

let read_text_file ?(encoding = Pje.UTF8) file =
  let content =
    match file with
    | "-" -> In_channel.input_all In_channel.stdin
    | _ -> Stdio.In_channel.read_all file
  in
  match encoding with Pje.UTF8 -> content | Pje.SJIS -> Sjis.to_utf8 content

let handle_errors f get_content =
  try f () with
  | CompileError.Compile_error e ->
      CompileError.print_error e get_content;
      Stdlib.exit 1
  | Sys_error msg ->
      Stdio.print_endline msg;
      Stdlib.exit 1

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
            let hll_name = Stdlib.Filename.(chop_extension (basename f)) in
            match List.Assoc.find import_as ~equal:String.equal hll_name with
            | Some name -> name
            | None -> hll_name
          in
          Pje.Hll (f, import_name)
        else Pje.Jaf f)
  in
  let ctx = Jaf.context_from_ain (Ain.create major minor) in
  let files = Hashtbl.create (module String) in
  handle_errors
    (fun () ->
      let read_file file =
        let source = read_text_file ~encoding:input_encoding file in
        Hashtbl.add_exn files ~key:file ~data:source;
        source
      in
      let debug_info = DebugInfo.create () in
      Compile.compile ctx sources debug_info read_file;
      Ain.write_file ctx.ain output)
    (fun file -> Hashtbl.find files file)

let do_build pje_file output_dir_override =
  let pje =
    handle_errors
      (fun () -> Project.load_pje read_text_file pje_file)
      (fun _ -> None)
  in
  let ctx = Jaf.context_from_ain (Pje.create_ain pje) in
  let files = Hashtbl.create (module String) in
  handle_errors
    (fun () ->
      let source_dir =
        Stdlib.Filename.(concat (dirname pje_file) pje.source_dir)
      in
      let read_file file =
        let file = Stdlib.Filename.(concat source_dir file) in
        let source = read_text_file ~encoding:pje.encoding file in
        Hashtbl.add_exn files ~key:file ~data:source;
        source
      in
      let sources = Pje.collect_sources pje in
      let debug_info = DebugInfo.create () in
      Compile.compile ctx sources debug_info read_file;
      Ain.write_file ctx.ain (Pje.ain_path ?output_dir_override pje);
      DebugInfo.write_to_file debug_info (Pje.debug_info_path pje))
    (fun file -> Hashtbl.find files file)

let encoding_conv =
  let parse s =
    try Ok (Pje.encoding_of_string s)
    with Pje.KeyError msg -> Error (`Msg msg)
  in
  let print ppf e =
    Stdlib.Format.pp_print_string ppf (Pje.string_of_encoding e)
  in
  Arg.conv (parse, print)

let cmd_compile_jaf =
  let doc = "Compile .jaf files." in
  let info = Cmd.info "compile" ~doc in
  let sources =
    let doc = "Source files to compile." in
    Arg.(non_empty & pos_all string [] & info [] ~docv:"SOURCES" ~doc)
  in
  let output =
    let doc = "The output .ain file." in
    Arg.(
      value & opt string "out.ain"
      & info [ "o"; "output" ] ~docv:"OUT_FILE" ~doc)
  in
  let major =
    let doc = "The output .ain file version." in
    Arg.(value & opt int 4 & info [ "ain-version" ] ~docv:"MAJOR" ~doc)
  in
  let minor =
    let doc = "The output .ain file minor version." in
    Arg.(value & opt int 0 & info [ "ain-minor-version" ] ~docv:"MINOR" ~doc)
  in
  let import_as =
    let doc = "Import HLL_NAME as NAME." in
    Arg.(
      value & opt_all string []
      & info [ "import-as" ] ~docv:"HLL_NAME=NAME" ~doc)
  in
  let input_encoding =
    let doc = "The input file encoding. Shift_JIS or UTF-8." in
    Arg.(
      value & opt encoding_conv Pje.UTF8
      & info [ "input-encoding" ] ~docv:"ENCODING" ~doc)
  in
  let test =
    let doc = "Testing." in
    Arg.(value & opt (some string) None & info [ "test" ] ~docv:"TEST" ~doc)
  in
  let compile sources output major minor import_as input_encoding test =
    if Option.is_some test then
      let ain = Ain.load (Option.value_exn test) in
      Ain.write_file ain output
    else do_compile sources output major minor import_as input_encoding
  in
  Cmd.v info
    Term.(
      const compile $ sources $ output $ major $ minor $ import_as
      $ input_encoding $ test)

let cmd_build_pje =
  let doc = "Build a System 4 project from a .pje file." in
  let info = Cmd.info "build" ~doc in
  let project =
    let doc = "The project file to build." in
    Arg.(required & pos 0 (some string) None & info [] ~docv:"PROJECT" ~doc)
  in
  let output_dir =
    let doc = "Override the output directory specified in the pje." in
    Arg.(
      value
      & opt (some string) None
      & info [ "output-dir" ] ~docv:"OUTPUT_DIR" ~doc)
  in
  Cmd.v info Term.(const do_build $ project $ output_dir)

let cmd =
  let doc = "System 4 Compiler" in
  let version = "0.1" in
  let info = Cmd.info "sys4c" ~version ~doc in
  Cmd.group info [ cmd_compile_jaf; cmd_build_pje ]

let () = Stdlib.exit (Cmd.eval cmd)
