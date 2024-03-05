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

{
open Base
open PjeParser

exception Error
}

let d  = ['0'-'9']
let h  = ['a'-'f' 'A'-'F' '0'-'9']
let hp = '0' ['x' 'X']
let l  = ['a'-'z' 'A'-'Z' '_']
let a  = ['a'-'z' 'A'-'Z' '_' '0'-'9']
let sc = [^ '\n' '"']

rule token = parse
    [' ' '\t' '\r']     { token lexbuf } (* skip blanks *)
  | "//" [^ '\n']*      { token lexbuf }
  | "/*"                { block_comment lexbuf }
  | ['\n' ]             { Lexing.new_line lexbuf; token lexbuf }
  | d+ as n             { I_CONSTANT (Int.of_string n) }
  | (hp h+) as n        { I_CONSTANT (Int.of_string n) }
  | '"' (sc* as s) '"'  { S_CONSTANT s }
  | "true"              { B_CONSTANT true }
  | "false"             { B_CONSTANT false }
  | '{'                 { LBRACE }
  | '}'                 { RBRACE }
  | '='                 { EQUAL }
  | "->"                { ARROW }
  | ','                 { COMMA }
  | "Define"            { DEFINE }
  | "Formation"         { FORMATION }
  | "SyncFolder"        { SYNCFOLDER }
  | "#define"           { HASH_DEFINE }
  | (l a*) as s         { IDENTIFIER s }
  | _                   { raise Error }
  | eof                 { EOF }

and block_comment = parse
    "*/"      { token lexbuf }
  | [^ '\n']  { block_comment lexbuf }
  | ['\n']    { Lexing.new_line lexbuf; block_comment lexbuf }
  | eof       { raise Error }
