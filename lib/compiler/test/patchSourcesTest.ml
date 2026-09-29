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

(* Project loading and patch target selection. *)

open Common
open Compiler
open Base
open PatchTestSupport

let path = Stdlib.Filename.concat
let unix_path = String.tr ~target:'\\' ~replacement:'/'

let display_filename root file =
  let file = unix_path file in
  let prefixes =
    [ unix_path root ^ "/"; Stdlib.Filename.basename root ^ "/" ]
  in
  List.find_map prefixes ~f:(fun prefix -> String.chop_prefix file ~prefix)
  |> Option.value ~default:file

let print_outputs root (program : PatchSources.t) =
  List.iter program.output_definitions ~f:(fun d ->
      Stdio.printf "%s: %s\n" (display_filename root d.source.filename) d.name)

let print_selections (program : PatchSources.t) =
  List.iter program.selections ~f:(function
    | PatchSources.Function d -> Stdio.printf "function %s\n" d.name
    | Class s -> Stdio.printf "class %s\n" s.name
    | GlobalGroup gg -> Stdio.printf "globalgroup %s\n" gg.name
    | Library name -> Stdio.printf "library %s\n" name
    | Global v -> Stdio.printf "global %s\n" v.name
    | FuncType f -> Stdio.printf "functype %s\n" f.name
    | Delegate f -> Stdio.printf "delegate %s\n" f.name)

let report_error root f =
  try f ()
  with CompileError.Compile_error (Error (message, _)) ->
    Stdio.print_endline
      (String.substr_replace_all (unix_path message) ~pattern:(unix_path root)
         ~with_:"<project>")

let%expect_test "project INC HLL and patch paths, order and single parsing" =
  with_files
    [
      ( "game/project.pje",
        {|Encoding = "UTF-8"
          SourceDir = "src"
          SystemSource = { "system.inc", }
          Source = { "first.jaf", "second.jaf", }|}
      );
      ("game/src/system.inc", {|Source = { "nested/lib.inc", }|});
      ( "game/src/nested/lib.inc",
        {|Source = { "api.hll", "API", "declarations.jaf", }|} );
      ("game/src/nested/api.hll", "void Print(string text);");
      ("game/src/nested/declarations.jaf", "const int VALUE = 1;");
      ("game/src/first.jaf", "void first() {} void second_in_file() {}");
      ("game/src/second.jaf", "void second() {}");
      ("patch.jaf", "void patch() {}");
    ]
    (fun root ->
      let reads = Hashtbl.create (module String) in
      let read_file file =
        Hashtbl.incr reads file;
        Stdio.In_channel.read_all file
      in
      (* CLI paths are relative to cwd, not the PJE or SourceDir. *)
      let relative_root = Stdlib.Filename.basename root in
      let program =
        PatchSources.load
          ~patch_files:
            [
              path relative_root "patch.jaf";
              path relative_root "game/src/second.jaf";
              path relative_root "game/src/first.jaf";
              path relative_root "game/src/first.jaf";
            ]
          ~read_file
          (path relative_root "game/project.pje")
      in
      List.iter program.sources ~f:(function
        | PatchSources.Jaf s ->
            Stdio.printf "%s %s\n"
              (match s.role with
              | Reference -> "reference"
              | Target -> "target")
              (display_filename root s.filename)
        | Hll h ->
            Stdio.printf "hll %s %s as %s\n"
              (display_filename root h.filename)
              h.name h.import_name);
      Stdio.print_endline "output order:";
      print_outputs root program;
      Stdio.printf "all files read once: %b\n"
        (Hashtbl.for_all reads ~f:(Int.equal 1));
      let target = List.hd_exn program.targets in
      let definition = List.hd_exn program.output_definitions in
      Stdio.printf "shared target AST: %b\n"
        (phys_equal target definition.source));
  [%expect
    {|
    hll nested/api.hll api as API
    reference nested/declarations.jaf
    target first.jaf
    target second.jaf
    target ../patch.jaf
    output order:
    ../patch.jaf: patch
    second.jaf: second
    first.jaf: first
    first.jaf: second_in_file
    all files read once: true
    shared target AST: true
    |}]

let%expect_test "patch overrides reference, without checking unused bodies" =
  with_files
    [
      ("project.pje", {|Source = { "original.jaf", }|});
      ("original.jaf", "int score(int old_name) { return unknown_name; }");
      ("patch.jaf", "int score(int renamed) { return renamed; }");
    ]
    (fun root ->
      let program =
        PatchSources.load
          ~patch_files:[ path root "patch.jaf" ]
          (path root "project.pje")
      in
      print_outputs root program;
      let chosen =
        Option.value_exn (PatchSources.find_definition program "score")
      in
      Stdio.printf "chosen: %s, parameter: %s, unregistered: %b\n"
        (display_filename root chosen.source.filename)
        (List.hd_exn chosen.declaration.params).name
        (Option.is_none chosen.declaration.index));
  [%expect
    {|
    patch.jaf: score
    chosen: patch.jaf, parameter: renamed, unregistered: true
    |}]

let%expect_test "duplicate bodies among targets and among references" =
  List.iter [ true; false ] ~f:(fun duplicate_targets ->
      with_files
        [
          ( "project.pje",
            if duplicate_targets then "" else {|Source = { "a.jaf", "b.jaf", }|}
          );
          ("a.jaf", "void same() {}");
          ("b.jaf", "void same() {}");
          ("patch.jaf", "void same() {}");
        ]
        (fun root ->
          report_error root (fun () ->
              let patches =
                if duplicate_targets then [ "a.jaf"; "b.jaf" ]
                else [ "patch.jaf" ]
              in
              ignore
                (PatchSources.load
                   ~patch_files:(List.map patches ~f:(path root))
                   (path root "project.pje")))));
  [%expect
    {|
    Duplicate function definition: same (previous definition in a.jaf)
    Duplicate function definition: same (previous definition in a.jaf)
    |}]

let%expect_test "constant-only targets are accepted alongside bodies" =
  with_files
    [
      ("project.pje", "");
      ("constants.jaf", "const int VALUE = 2;");
      ("body.jaf", "int fresh() { return VALUE; }");
    ]
    (fun root ->
      let load files =
        PatchSources.load
          ~patch_files:(List.map files ~f:(path root))
          (path root "project.pje")
      in
      let program = load [ "constants.jaf"; "body.jaf" ] in
      Stdio.printf "target files: %d\n" (List.length program.targets);
      print_outputs root program;
      report_error root (fun () -> ignore (load [ "constants.jaf" ]));
      report_error root (fun () -> ignore (load [])));
  [%expect
    {|
    target files: 2
    body.jaf: fresh
    Selected source files contain no patch targets
    No patch targets or source files specified
    |}]

let%expect_test "source selections retain declaration kinds" =
  with_files
    [
      ("project.pje", {|Source = { "symbols.jaf", }|});
      ("symbols.jaf", "class Shared { int value; }; int Shared;");
      ("function.jaf", "void Shared() {}");
      ("data.jaf", "class Data { array@int values[2]; }; int scalar;");
    ]
    (fun root ->
      let load file =
        PatchSources.load
          ~patch_files:[ path root file ]
          (path root "project.pje")
      in
      print_selections (load "function.jaf");
      Stdio.print_endline "data:";
      print_selections (load "data.jaf"));
  [%expect
    {|
    function Shared
    data:
    class Data
    global scalar
    |}]

let%expect_test "method and special-function targets use JAF names" =
  with_files
    [
      ("project.pje", {|Source = { "types.jaf", }|});
      ( "types.jaf",
        "class C { public: void run() {} void missing(); C() {} ~C() {} };" );
    ]
    (fun root ->
      let program =
        PatchSources.load
          ~targets:[ "C::run"; "C::C"; "C::~C" ]
          (path root "project.pje")
      in
      print_outputs root program;
      report_error root (fun () ->
          ignore
            (PatchSources.load ~targets:[ "C::missing" ]
               (path root "project.pje"))));
  [%expect
    {|
    types.jaf: C@run
    types.jaf: C@0
    types.jaf: C@1
    Patch target has no function body: C::missing
    |}]
