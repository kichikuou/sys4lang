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

type 'a t = { buf : bytes; mutable pos : int; context : 'a }

let create buf context = { buf; pos = 0; context }
let get_pos br = br.pos
let remaining br = Bytes.length br.buf - br.pos
let eof br = br.pos >= Bytes.length br.buf

let bytes br len =
  let sub = Bytes.sub br.buf ~pos:br.pos ~len in
  br.pos <- br.pos + len;
  sub

let blit br dst ~pos ~len =
  let len = min len (remaining br) in
  Bytes.blit ~src:br.buf ~src_pos:br.pos ~dst ~dst_pos:pos ~len;
  br.pos <- br.pos + len;
  len

let u16 br =
  let v = Stdlib.Bytes.get_uint16_le br.buf br.pos in
  br.pos <- br.pos + 2;
  v

let i32 br =
  let v = Stdlib.Bytes.get_int32_le br.buf br.pos in
  br.pos <- br.pos + 4;
  v

let int br = Int32.to_int_exn (i32 br)
let f32 br = Int32.float_of_bits (i32 br)

let bool br =
  match i32 br with
  | 0l -> false
  | 1l -> true
  | _ -> failwith "invalid boolean value"

let string br =
  let pos = br.pos in
  while Char.O.(Bytes.get br.buf br.pos <> '\x00') do
    br.pos <- br.pos + 1
  done;
  let s = Stdlib.Bytes.sub_string br.buf pos (br.pos - pos) in
  br.pos <- br.pos + 1;
  s

let sjis_string br = Common.Sjis.to_utf8 (string br)

let msg1_string br =
  let len = int br in
  let data = Bytes.sub br.buf ~pos:br.pos ~len in
  br.pos <- br.pos + len;
  for i = 0 to len - 1 do
    let c = Char.to_int (Bytes.get data i) in
    Bytes.set data i (Char.of_int_exn ((c - 0x60 - i) % 256))
  done;
  Common.Sjis.to_utf8 (Bytes.to_string data)

let tag br =
  let tag = Stdlib.Bytes.sub_string br.buf br.pos 4 in
  br.pos <- br.pos + 4;
  tag
