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
open Sys4cLib

let pje_load_test pje_name mock_read_file =
  try
    let pje = Project.load_pje mock_read_file pje_name in
    List.iter (Pje.collect_sources pje) ~f:(function
      | Pje.Jaf f -> Stdio.print_endline f
      | Pje.Hll (f, name) -> Stdio.printf "%s as %s\n" f name
      | _ -> failwith "unreachable")
  with CompileError.Compile_error e ->
    CompileError.print_error e (fun _ -> None)

let%expect_test "simple" =
  pje_load_test "project.pje" (function
    | "project.pje" ->
        {|
          SourceDir = "Source"
          Source = {
            "main.jaf",
          }
        |}
    | f -> failwith "unexpected file: " ^ f);
  [%expect {|
    main.jaf |}]

let%expect_test "syntax error" =
  pje_load_test "project.pje" (function
    | "project.pje" -> {|
          SourceDir: "Source"
        |}
    | f -> failwith "unexpected file: " ^ f);
  [%expect {|
    project.pje:2:20-21: Syntax error |}]

let%expect_test "wrong key" =
  pje_load_test "project.pje" (function
    | "project.pje" -> {|
          Unknown = ""
        |}
    | f -> failwith "unexpected file: " ^ f);
  [%expect {|
    project.pje:3:9-9: Invalid name: Unknown |}]

let%expect_test "no hll name" =
  pje_load_test "project.pje" (function
    | "project.pje" ->
        {|
          SourceDir = "Source"
          Source = {
            "foo.hll",
          }
        |}
    | f -> failwith "unexpected file: " ^ f);
  [%expect {|
    project.pje:6:9-9: No import name for foo.hll |}]

let%expect_test "include" =
  pje_load_test "Proj/project.pje" (function
    | "Proj/project.pje" ->
        {|
          SourceDir = "Source"
          SystemSource = {
            "System\System.inc",
          }
          Source = {
            "game.inc",
          }
        |}
    | "Proj/Source/System/System.inc" ->
        {|
          Source = {
            "system.jaf",
            "SACT\SACT.inc",
          }
        |}
    | "Proj/Source/System/SACT/SACT.inc" ->
        {|
          Source = {
            "main\sact.jaf",
            "SACT2.hll", "SACT"
          }
        |}
    | "Proj/Source/game.inc" ->
        {|
          Source = {
            "main.jaf",
          }
        |}
    | f -> failwith ("unexpected file: " ^ f));
  [%expect
    {|
      System/system.jaf
      System/SACT/main/sact.jaf
      System/SACT/SACT2.hll as SACT
      main.jaf
    |}]
