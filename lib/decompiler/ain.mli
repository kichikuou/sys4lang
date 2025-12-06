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

type type_t = Type.ain_type

module Variable : sig
  type init_value = String of string | Int of int32 | Float of float
  [@@deriving show]

  type t = {
    name : string;
    name2 : string; (* ain v12+ *)
    type_ : type_t;
    init_val : init_value option;
    group_index : int;
  }
  [@@deriving show]
end

module Function : sig
  type t = {
    address : int;
    mutable name : string;
    is_label : bool;
    is_lambda : bool;
    capture : bool;
    return_type : type_t;
    vars : Variable.t array;
    nr_args : int;
    crc : int32;
  }
  [@@deriving show]

  type parsed_name = { struct_name : string option; name : string }

  val parse_name : t -> parsed_name
  val args : t -> Variable.t list
  val arg_types : t -> type_t list
  val to_type : t -> Type.func_type
end

module InitVal : sig
  type t = { global_index : int; type_ : type_t; value : Variable.init_value }
end

module Struct : sig
  type interface = { struct_type : int; vtable_offset : int } [@@deriving show]

  type t = {
    id : int;
    name : string;
    interfaces : interface array;
    constructor : int;
    destructor : int;
    members : Variable.t array;
    mutable vtable : int array;
    mutable implementers : interface list;
  }
  [@@deriving show]
end

module HLL : sig
  type function_t = {
    name : string;
    return_type : type_t;
    arguments : Variable.t array;
    nr_args_in_stack : int;
  }
  [@@deriving show]

  val args : function_t -> Variable.t list
  val arg_types : function_t -> type_t list

  type t = { name : string; functions : function_t array }
end

module Switch : sig
  type case_type = Int | String
  type case = { value : int32; address : int32 }

  type t = {
    case_type : case_type;
    default_address : int32;
    cases : case array;
  }
end

module ScenarioLabel : sig
  type t = { name : string; address : int32 }
end

module FuncType : sig
  type t = {
    id : int;
    name : string;
    return_type : type_t;
    nr_args : int;
    variables : Variable.t array;
  }
  [@@deriving show]

  val args : t -> Variable.t list
  val arg_types : t -> type_t list
  val to_type : t -> Type.func_type
end

type t = {
  mutable vers : int;
  mutable keyc : int32;
  mutable code : bytes;
  mutable func : Function.t array;
  mutable glob : Variable.t array;
  mutable gset : InitVal.t array;
  mutable strt : Struct.t array;
  mutable msg : string array;
  mutable msg1_uk : int32 option;
  mutable main : int32;
  mutable msgf : int32;
  mutable hll0 : HLL.t array;
  mutable swi0 : Switch.t array;
  mutable gver : int32;
  mutable slbl : ScenarioLabel.t array;
  mutable str0 : string array;
  mutable fnam : string array;
  mutable ojmp : int32;
  mutable fnct : FuncType.t array;
  mutable delg : FuncType.t array;
  mutable objg : string array;
  mutable enum : string array;
  mutable is_ai2 : bool;
  mutable struct_by_name : (string, Struct.t) Hashtbl.t;
  mutable enum_by_name : (string, int) Hashtbl.t;
  mutable ifthen_optimized : bool;
}

val ain : t
val load : string -> unit
