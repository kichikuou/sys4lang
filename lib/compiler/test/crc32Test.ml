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
open Compiler

(* Feed a list of inputs (32-bit words or qualified label names) into the CRC. *)
let crc inputs =
  List.fold inputs ~init:Crc32.start ~f:(fun c -> function
    | `Word n -> Crc32.feed_word c n
    | `Name s -> Crc32.feed_string c s)
  |> Crc32.finalize

let%expect_test "CRC of empty input" =
  Stdio.printf "%08lx" (Crc32.finalize Crc32.start);
  [%expect {| 00000000 |}]

(* The CRC the original System 4 SDK compiler produces for this function:

     int main(void)
     {
     ラベル:
         system.Exit(0);
         goto ラベル;
         return 0;
     }

   The word sequence below mirrors how it compiles: the int return type, the
   label definition (0x406) and goto (0x407) markers each followed by the
   qualified name, and the body opcodes. *)
let%expect_test "function CRC with labels" =
  crc
    [
      `Word 10 (* return type: int *);
      `Word 0x406;
      `Name "main::ラベル" (* ラベル: *);
      `Word 0x00 (* PUSH 0 *);
      `Word 0x63 (* CALLSYS *);
      `Word 0x407;
      `Name "main::ラベル" (* goto ラベル; *);
      `Word 0x00 (* PUSH 0 *);
      `Word 0x2f (* RETURN *);
      `Word 0x00 (* PUSH 0 *);
      `Word 0x2f (* implicit return *);
    ]
  |> Stdio.printf "%08lx";
  [%expect {| 0b14f5a2 |}]
