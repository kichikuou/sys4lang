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
  let ctx = Jaf.create_context (Ain.create major minor) in
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

let do_build pje_file output_dir_override no_debug_info =
  let pje =
    handle_errors
      (fun () -> PjeLoader.load read_text_file pje_file)
      (fun _ -> None)
  in
  let ctx = Jaf.create_context (Pje.create_ain pje) in
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
      if not no_debug_info then
        DebugInfo.write_to_file debug_info (Pje.debug_info_path pje))
    (fun file -> Hashtbl.find files file)

let realpath path = try Unix.realpath path with Unix.Unix_error _ -> path

let relative_path ~from path =
  let path = Fpath.v (realpath path) in
  match Fpath.relativize ~root:(Fpath.v (realpath from)) path with
  | Some p -> String.concat ~sep:"/" (Fpath.segs p)
  | None -> Fpath.to_string path

let do_patch pje_file targets base_ain extra_sources globals keep_crc output
    use_debug_info =
  let pje =
    handle_errors
      (fun () -> PjeLoader.load read_text_file pje_file)
      (fun _ -> None)
  in
  let base_ain = Option.value base_ain ~default:(Pje.ain_path pje) in
  let output = Option.value output ~default:(Pje.ain_path pje) in
  let base =
    try Ain.load base_ain
    with e ->
      let reason =
        match e with Sys_error msg | Failure msg -> msg | e -> Exn.to_string e
      in
      Stdio.print_endline ("Cannot load base AIN: " ^ reason);
      Stdlib.exit 1
  in
  let pje_dir = Stdlib.Filename.dirname pje_file in
  let source_dir = Stdlib.Filename.concat pje_dir pje.source_dir in
  let project_file path = Stdlib.Filename.concat source_dir path in
  let files = Hashtbl.create (module String) in
  handle_errors
    (fun () ->
      List.iter extra_sources ~f:(fun f ->
          if String.is_suffix (String.lowercase f) ~suffix:".hll" then
            CompileError.raise_message
              ("HLL files cannot be patch sources: " ^ f));
      let extra_paths = List.map extra_sources ~f:realpath in
      let project_sources =
        List.map (Pje.collect_sources pje) ~f:(function
          | Pje.Jaf f ->
              let selected =
                List.mem extra_paths
                  (realpath (project_file f))
                  ~equal:String.equal
              in
              Patch.
                {
                  path = f;
                  debug_path = f;
                  origin = (if selected then `Project_selected else `Project);
                  kind = `Jaf;
                }
          | Pje.Hll (f, import_name) ->
              Patch.
                {
                  path = f;
                  debug_path = f;
                  origin = `Project;
                  kind = `Hll import_name;
                }
          | Pje.Include _ -> failwith "unreachable")
      in
      let project_paths =
        List.filter_map project_sources ~f:(fun (src : Patch.source) ->
            match src.kind with
            | `Jaf -> Some (realpath (project_file src.path))
            | `Hll _ -> None)
      in
      let extra_sources =
        List.filter_map (List.zip_exn extra_sources extra_paths)
          ~f:(fun (f, abs) ->
            if List.mem project_paths abs ~equal:String.equal then None
            else
              Some
                Patch.
                  {
                    path = f;
                    debug_path = relative_path ~from:pje_dir f;
                    origin = `Extra;
                    kind = `Jaf;
                  })
      in
      let read_file (src : Patch.source) =
        let file =
          match src.origin with
          | `Project | `Project_selected -> project_file src.path
          | `Extra -> src.path
        in
        let content = read_text_file ~encoding:pje.encoding file in
        Hashtbl.set files ~key:src.path ~data:content;
        content
      in
      let debug_info_path = Pje.debug_info_path pje in
      let debug_info =
        if not use_debug_info then None
        else
          try Some (DebugInfo.load_file debug_info_path) with
          | Sys_error msg -> CompileError.raise_message ("Cannot load " ^ msg)
          | Yojson.Json_error msg | Yojson.Basic.Util.Type_error (msg, _) ->
              CompileError.raise_message
                (Printf.sprintf "Cannot load %s: %s" debug_info_path msg)
      in
      Patch.apply ~base ~pje
        ~sources:(project_sources @ extra_sources)
        ~targets ~globals ~keep_crc ~read_file ~debug_info;
      Ain.write_file base output;
      Option.iter debug_info ~f:(fun di ->
          DebugInfo.write_to_file di debug_info_path))
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
  Cmd.v info
    Term.(
      const do_compile $ sources $ output $ major $ minor $ import_as
      $ input_encoding)

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
  let no_debug_info =
    let doc = "Do not write the debug_info.json file." in
    Arg.(value & flag & info [ "no-debug-info" ] ~doc)
  in
  Cmd.v info Term.(const do_build $ project $ output_dir $ no_debug_info)

let cmd_patch =
  let doc = "Apply selected source changes to an existing .ain file." in
  let info = Cmd.info "patch" ~doc in
  let project =
    let doc = "The project file." in
    Arg.(required & pos 0 (some string) None & info [] ~docv:"PROJECT" ~doc)
  in
  let targets =
    let doc =
      "Names of functions, methods, structures, classes, function types, or \
       delegate types to apply."
    in
    Arg.(value & pos_right 0 string [] & info [] ~docv:"TARGET" ~doc)
  in
  let base_ain =
    let doc =
      "The .ain file to patch. Defaults to the .ain file of the project."
    in
    Arg.(value & opt (some string) None & info [ "base-ain" ] ~docv:"FILE" ~doc)
  in
  let sources =
    let doc = "A patch source file to apply. Can be repeated." in
    Arg.(value & opt_all string [] & info [ "source" ] ~docv:"FILE" ~doc)
  in
  let globals =
    let doc =
      "Add new globals and global groups, and rebuild global initialization."
    in
    Arg.(value & flag & info [ "globals" ] ~doc)
  in
  let keep_crc =
    let doc = "Keep the CRC values of the replaced functions." in
    Arg.(value & flag & info [ "keep-crc" ] ~doc)
  in
  let output =
    let doc =
      "The output .ain file. Defaults to the .ain file of the project."
    in
    Arg.(
      value & opt (some string) None & info [ "o"; "output" ] ~docv:"FILE" ~doc)
  in
  let debug_info =
    let doc = "Read and update the debug_info.json file." in
    Arg.(value & flag & info [ "debug-info" ] ~doc)
  in
  Cmd.v info
    Term.(
      const do_patch $ project $ targets $ base_ain $ sources $ globals
      $ keep_crc $ output $ debug_info)

let cmd =
  let doc = "System 4 Compiler" in
  let version =
    Option.map (Build_info.V1.version ()) ~f:Build_info.V1.Version.to_string
  in
  let info = Cmd.info "sys4c" ?version ~doc in
  Cmd.group info [ cmd_compile_jaf; cmd_build_pje; cmd_patch ]

let () = Stdlib.exit (Cmd.eval cmd)
