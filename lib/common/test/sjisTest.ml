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

let print_codes s =
  Sjis.from_utf8 s |> String.to_list
  |> List.map ~f:(fun c -> Printf.sprintf "%02x" (Char.to_int c))
  |> String.concat ~sep:" " |> Stdio.print_endline

let%expect_test "characters with more than one code" =
  (* JIS X 0208, not NEC special characters or IBM extensions *)
  print_codes "∵￢∪";
  (* NEC special characters, not IBM extensions *)
  print_codes "Ⅰ№㈱";
  (* IBM extensions, not NEC-selected IBM extensions *)
  print_codes "纊ⅰ";
  [%expect
    {|
    81 e6 81 ca 81 be
    87 54 87 82 87 8a
    fa 5c fa 40
    |}]
