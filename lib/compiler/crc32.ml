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

(* CRC-32 for Ain.Function.crc, accumulated incrementally over 32-bit words. *)

open Base

let table =
  lazy
    (Array.init 256 ~f:(fun n ->
         let c = ref n in
         for _ = 0 to 7 do
           c := if !c land 1 = 1 then 0xEDB88320 lxor (!c lsr 1) else !c lsr 1
         done;
         !c))

(* Fold the four little-endian bytes of the 32-bit word [n] into [v]. *)
let raw_feed_word v n =
  let t = Lazy.force table in
  let v = ref v in
  for i = 0 to 3 do
    let b = (n lsr (i * 8)) land 0xFF in
    v := (!v lsr 8) lxor t.(!v lxor b land 0xFF)
  done;
  !v

(* Fold a (UTF-8) string into [v] as its Shift_JIS bytes, each sign-extended to a
   32-bit word. *)
let raw_feed_string v s =
  String.fold (Common.Sjis.from_utf8 s) ~init:v ~f:(fun v c ->
      let b = Char.to_int c in
      raw_feed_word v (if b land 0x80 <> 0 then 0xFFFFFF00 lor b else b))

(* The accumulator is a small state machine. It is [Inactive] outside of a
   function body, turns [Active] with [start], and can be [freeze]d when a
   nested function begins (the original compiler hashes a function's opcodes
   only up to the first nested FUNC). *)
type t =
  | Inactive (* fed words are ignored *)
  | Active of int (* running pre-final CRC value *)
  | Frozen of int (* value kept for finalize *)

let start = Active 0xFFFFFFFF

let feed_word t n =
  match t with Active v -> Active (raw_feed_word v n) | _ -> t

let feed_string t s =
  match t with Active v -> Active (raw_feed_string v s) | _ -> t

(* Stop accumulating but keep the value (for a function reaching a nested FUNC). *)
let freeze = function Active v -> Frozen v | t -> t

(* Apply the final XOR and return the result as an int32. *)
let finalize = function
  | Active v | Frozen v -> Int32.of_int_trunc (v lxor 0xFFFFFFFF)
  | Inactive -> failwith "Crc32.finalize: accumulator not started"
