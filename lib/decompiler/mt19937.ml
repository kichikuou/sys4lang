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

let n = 624
let m = 397
let upper_mask = 0x80000000l
let lower_mask = 0x7fffffffl
let matrix_a = 0x9908b0dfl
let ( *** ) x y = Int32.( * ) x y
let ( &&& ) x y = Int32.( land ) x y
let ( ||| ) x y = Int32.( lor ) x y
let ( ^^^ ) x y = Int32.( lxor ) x y
let ( <<< ) x y = Int32.( lsl ) x y
let ( >>> ) x y = Int32.( lsr ) x y

let char_xor c k =
  Char.unsafe_of_int (Char.to_int c lxor (Int32.to_int_trunc k land 0xff))

let init seed =
  let st = Array.create ~len:n 0l in
  st.(0) <- seed;
  for i = 1 to n - 1 do
    st.(i) <- 69069l *** st.(i - 1)
  done;
  st

let genrand st =
  for kk = 0 to n - m - 1 do
    let y = st.(kk) &&& upper_mask ||| (st.(kk + 1) &&& lower_mask) in
    st.(kk) <- st.(kk + m) ^^^ (y >>> 1) ^^^ ((y &&& 1l) *** matrix_a)
  done;
  for kk = n - m to n - 2 do
    let y = st.(kk) &&& upper_mask ||| (st.(kk + 1) &&& lower_mask) in
    st.(kk) <- st.(kk + (m - n)) ^^^ (y >>> 1) ^^^ ((y &&& 1l) *** matrix_a)
  done;
  let y = st.(n - 1) &&& upper_mask ||| (st.(0) &&& lower_mask) in
  st.(n - 1) <- st.(m - 1) ^^^ (y >>> 1) ^^^ ((y &&& 1l) *** matrix_a);
  Array.init n ~f:(fun i ->
      let y = st.(i) in
      let y = y ^^^ (y >>> 11) in
      let y = y ^^^ (y <<< 7 &&& 0x9d2c5680l) in
      let y = y ^^^ (y <<< 15 &&& 0xefc60000l) in
      let y = y ^^^ (y >>> 18) in
      y)

let decrypt (bytes : bytes) seed =
  let st = init seed in
  let i = ref 0 in
  while !i < Bytes.length bytes do
    let rand = genrand st in
    for j = 0 to min n (Bytes.length bytes - !i) - 1 do
      Bytes.set bytes (!i + j) (char_xor (Bytes.get bytes (!i + j)) rand.(j))
    done;
    i := !i + n
  done
