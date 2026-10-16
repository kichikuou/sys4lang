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
