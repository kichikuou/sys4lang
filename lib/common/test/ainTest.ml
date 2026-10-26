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

open Base
open Common

let string_of_format = function
  | Ain.Raw -> "Raw"
  | Ain.Compressed -> "Compressed"
  | Ain.Encrypted -> "Encrypted"

let write_and_read ain =
  let file = Stdlib.Filename.temp_file "ainTest" ".ain" in
  Exn.protect
    ~f:(fun () ->
      Ain.write_file ain file;
      let data = Stdio.In_channel.read_all file in
      (data, Ain.load file))
    ~finally:(fun () -> Stdlib.Sys.remove file)

let round_trip ain =
  let data, loaded = write_and_read ain in
  let data', _ = write_and_read loaded in
  Stdio.printf "%s %s, same output: %b\n"
    (string_of_format (Ain.format loaded))
    (String.escaped (String.prefix data 4))
    (String.equal data data')

let%expect_test "output format is preserved" =
  let ain = Ain.create ~is_ain2:false 4 0 in
  ignore (Ain.add_string ain "test" : int);
  round_trip ain;
  let ain = Ain.create ~is_ain2:true 4 0 in
  ignore (Ain.add_string ain "test" : int);
  round_trip ain;
  Ain.set_format ain Raw;
  round_trip ain;
  [%expect
    {|
    Encrypted ~\245\002\186, same output: true
    Compressed AI2\000, same output: true
    Raw VERS, same output: true
    |}]

let%expect_test "duplicate names" =
  let print_failure f =
    try f () with Failure msg -> Stdio.print_endline msg
  in
  let ain = Ain.create 4 0 in
  ignore (Ain.add_function ain "f" : Ain.Function.t);
  print_failure (fun () -> ignore (Ain.add_function ain "f" : Ain.Function.t));
  Ain.write_function ain { (Ain.add_function ain "g") with name = "f" };
  print_failure (fun () -> ignore (write_and_read ain : string * Ain.t));
  [%expect
    {|
    function f has multiple entries
    function f has multiple entries
    |}]

let%expect_test "duplicate library names" =
  let ain = Ain.create 4 0 in
  ignore (Ain.add_library ain "L" : Ain.Library.t);
  ignore (Ain.add_library ain "L" : Ain.Library.t);
  let _, loaded = write_and_read ain in
  Stdio.printf "%d libraries, L is %d\n" (Ain.nr_libraries loaded)
    (Option.value_exn (Ain.get_library_index loaded "L"));
  [%expect {| 2 libraries, L is 0 |}]

let%expect_test "FNCT and DELG sections" =
  List.iter
    [ (0, 0); (1, 0); (6, 0); (6, 10); (6, 20); (7, 0) ]
    ~f:(fun (major, minor) ->
      let ain = Ain.create major minor in
      Ain.set_format ain Raw;
      let data, _ = write_and_read ain in
      Stdio.printf "%d.%d: FNCT %b, DELG %b\n" major minor
        (String.is_substring data ~substring:"FNCT")
        (String.is_substring data ~substring:"DELG"));
  [%expect
    {|
    0.0: FNCT false, DELG false
    1.0: FNCT true, DELG false
    6.0: FNCT true, DELG false
    6.10: FNCT true, DELG true
    6.20: FNCT false, DELG true
    7.0: FNCT false, DELG true
    |}]
