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
module BR = BytesReader

type reader_context = { mutable version : int }

let read_array (br : reader_context BR.t) n f =
  Array.init n ~f:(function _ -> f br)

let read_array_with_index (br : reader_context BR.t) n f =
  Array.init n ~f:(function i -> f i br)

let read_count_and_array br f =
  let n = BR.int br in
  read_array br n f

let read_count_and_array_with_index br f =
  let n = BR.int br in
  read_array_with_index br n f

type type_t = Type.ain_type [@@deriving show]

let rec read_variable_type br =
  let enum = BR.int br in
  let struc = BR.int br in
  if br.context.version >= 11 then
    let subtype = if BR.bool br then Some (read_variable_type br) else None in
    Type.create_ain11 enum ~struc ~subtype
  else
    let rank = BR.int br in
    Type.create enum ~struc ~rank

let read_return_type (br : reader_context BR.t) =
  if br.context.version >= 11 then read_variable_type br
  else
    let enum = BR.int br in
    let struc = BR.int br in
    Type.create enum ~struc ~rank:1

module Variable = struct
  type init_value = String of string | Int of int32 | Float of float
  [@@deriving show]

  let read_initval br type_ =
    if BR.bool br then
      match type_ with
      | Type.String -> Some (String (BR.sjis_string br))
      | Struct _ | Delegate _ | Ref _ | Array _ -> None
      | Float -> Some (Float (BR.f32 br))
      | _ -> Some (Int (BR.i32 br))
    else None

  type t = {
    name : string;
    name2 : string; (* ain v12+ *)
    type_ : type_t;
    init_val : init_value option;
    group_index : int;
  }
  [@@deriving show]

  let read br =
    let name = BR.sjis_string br in
    let name2 = if br.context.version >= 12 then BR.sjis_string br else "" in
    let type_ = read_variable_type br in
    let init_val =
      if br.context.version >= 8 then read_initval br type_ else None
    in
    { name; name2; type_; init_val; group_index = -1 }

  let read_global br =
    let name = BR.sjis_string br in
    let name2 = if br.context.version >= 12 then BR.sjis_string br else "" in
    let type_ = read_variable_type br in
    let group_index = if br.context.version >= 5 then BR.int br else -1 in
    { name; name2; type_; init_val = None; group_index }
end

module Function = struct
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

  let parse_name (func : t) =
    match String.lsplit2 func.name ~on:'@' with
    | None -> { struct_name = None; name = func.name }
    | Some (struct_name, method_name) ->
        { struct_name = Some struct_name; name = method_name }

  let args func = List.take (Array.to_list func.vars) func.nr_args
  let arg_types func = List.map (args func) ~f:(fun (v : Variable.t) -> v.type_)

  let to_type func =
    { Type.return_type = func.return_type; arg_types = arg_types func }

  let read br =
    let address = BR.int br in
    let name = BR.sjis_string br in
    let is_label =
      br.context.version > 1 && br.context.version < 7 && BR.bool br
    in
    let return_type = read_return_type br in
    let nr_args = BR.int br in
    let nr_vars = BR.int br in
    let is_lambda = String.is_substring name ~substring:"<lambda :" in
    let capture = br.context.version >= 11 && BR.bool br in
    let crc = if br.context.version > 1 then BR.i32 br else 0l in
    let vars = read_array br nr_vars Variable.read in
    {
      address;
      name;
      is_label;
      is_lambda;
      capture;
      return_type;
      vars;
      nr_args;
      crc;
    }
end

module InitVal = struct
  type t = { global_index : int; type_ : type_t; value : Variable.init_value }

  let read br =
    let global_index = BR.int br in
    let type_ = Type.create (BR.int br) ~struc:(-1) ~rank:1 in
    let value =
      match type_ with
      | String -> Variable.String (BR.sjis_string br)
      | Float -> Variable.Float (BR.f32 br)
      | _ -> Variable.Int (BR.i32 br)
    in
    { global_index; type_; value }
end

module Struct = struct
  type interface = { struct_type : int; vtable_offset : int } [@@deriving show]

  let read_interface br =
    let struct_type = BR.int br in
    let vtable_offset = BR.int br in
    { struct_type; vtable_offset }

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

  let read id br =
    let name = BR.sjis_string br in
    let interfaces =
      if br.context.version >= 11 then read_count_and_array br read_interface
      else [||]
    in
    let constructor = BR.int br in
    let destructor = BR.int br in
    let members = read_count_and_array br Variable.read in
    let vtable = [||] in
    let implementers = [] in
    {
      id;
      name;
      interfaces;
      constructor;
      destructor;
      members;
      vtable;
      implementers;
    }
end

module HLL = struct
  let read_hll_argument br =
    let name = BR.sjis_string br in
    (* if (AIN_VERSION_GTE(r->ain, 14, 0)) { ... } *)
    let type_ = Type.create (BR.int br) ~struc:(-1) ~rank:1 in
    Variable.{ name; name2 = name; type_; init_val = None; group_index = -1 }

  type function_t = {
    name : string;
    return_type : type_t;
    arguments : Variable.t array;
    nr_args_in_stack : int;
  }
  [@@deriving show]

  let args hllfunc = Array.to_list hllfunc.arguments
  let arg_types hllfunc = List.map (args hllfunc) ~f:(fun v -> v.type_)

  let read_hll_function br =
    let name = BR.sjis_string br in
    (* if (AIN_VERSION_GTE(r->ain, 14, 0)) { ... } *)
    let return_type = Type.create (BR.int br) ~struc:(-1) ~rank:1 in
    let arguments = read_count_and_array br read_hll_argument in
    let nr_args_in_stack =
      Array.fold arguments ~init:0 ~f:(fun acc arg ->
          acc + Type.size_in_stack arg.type_)
    in
    { name; return_type; arguments; nr_args_in_stack }

  type t = { name : string; functions : function_t array }

  let read br =
    let name = BR.sjis_string br in
    let functions = read_count_and_array br read_hll_function in
    { name; functions }
end

module Switch = struct
  type case_type = Int | String

  let read_type br =
    match BR.i32 br with
    | 2l -> Int
    | 4l -> String
    | _ as tag -> Printf.failwithf "unknown switch type %ld" tag ()

  type case = { value : int32; address : int32 }

  let read_case br =
    let value = BR.i32 br in
    let address = BR.i32 br in
    { value; address }

  type t = {
    case_type : case_type;
    default_address : int32;
    cases : case array;
  }

  let read br =
    let case_type = read_type br in
    let default_address = BR.i32 br in
    let cases = read_count_and_array br read_case in
    { case_type; default_address; cases }
end

module ScenarioLabel = struct
  type t = { name : string; address : int32 }

  let read br =
    let name = BR.sjis_string br in
    let address = BR.i32 br in
    { name; address }
end

module FuncType = struct
  type t = {
    id : int;
    name : string;
    return_type : type_t;
    nr_args : int;
    variables : Variable.t array;
  }
  [@@deriving show]

  let args func = List.take (Array.to_list func.variables) func.nr_args
  let arg_types func = List.map (args func) ~f:(fun (v : Variable.t) -> v.type_)

  let to_type func =
    { Type.return_type = func.return_type; arg_types = arg_types func }

  let read id br =
    let name = BR.sjis_string br in
    let return_type = read_return_type br in
    let nr_args = BR.int br in
    let variables = read_count_and_array br Variable.read in
    { id; name; return_type; nr_args; variables }
end

let readVERS br =
  let version = BR.int br in
  br.context.version <- version;
  version

let readKEYC br = BR.i32 br

let readCODE br =
  let length = BR.int br in
  BR.bytes br length

let readFUNC br = read_count_and_array br Function.read
let readGLOB br = read_count_and_array br Variable.read_global
let readGSET br = read_count_and_array br InitVal.read

let readSTRT br =
  let structs = read_count_and_array_with_index br Struct.read in
  Array.iter structs ~f:(fun strt ->
      Array.iter strt.interfaces ~f:(fun iface ->
          structs.(iface.struct_type).implementers <-
            { struct_type = strt.id; vtable_offset = iface.vtable_offset }
            :: structs.(iface.struct_type).implementers));
  structs

let readMSG0 br = read_count_and_array br BR.sjis_string

let readMSG1 br =
  let nr_msgs = BR.int br in
  let uk = BR.i32 br in
  (read_array br nr_msgs BR.msg1_string, uk)

let readMAIN br = BR.i32 br
let readMSGF br = BR.i32 br
let readHLL0 br = read_count_and_array br HLL.read
let readSWI0 br = read_count_and_array br Switch.read
let readGVER br = BR.i32 br
let readSLBL br = read_count_and_array br ScenarioLabel.read
let readSTR0 br = read_count_and_array br BR.sjis_string
let readFNAM br = read_count_and_array br BR.sjis_string
let readOJMP br = BR.i32 br

let readFNCT br =
  let _ = BR.i32 br in
  read_count_and_array_with_index br FuncType.read

let readDELG br =
  let _ = BR.i32 br in
  read_count_and_array_with_index br FuncType.read

let readOBJG br = read_count_and_array br BR.sjis_string
let readENUM br = read_count_and_array br BR.sjis_string

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

let applyGSET ain =
  Array.iter ain.gset ~f:(fun initval ->
      ain.glob.(initval.global_index) <-
        { (ain.glob.(initval.global_index)) with init_val = Some initval.value })

let ain =
  {
    vers = -1;
    keyc = -1l;
    code = Stdlib.Bytes.empty;
    func = [||];
    glob = [||];
    gset = [||];
    strt = [||];
    msg = [||];
    msg1_uk = None;
    main = -1l;
    msgf = -1l;
    hll0 = [||];
    swi0 = [||];
    gver = -1l;
    slbl = [||];
    str0 = [||];
    fnam = [||];
    ojmp = -1l;
    fnct = [||];
    delg = [||];
    objg = [||];
    enum = [||];
    is_ai2 = false;
    struct_by_name = Hashtbl.create (module String);
    enum_by_name = Hashtbl.create (module String);
    ifthen_optimized = false;
  }

let readSections br =
  while not (BR.eof br) do
    match BR.tag br with
    | "VERS" -> ain.vers <- readVERS br
    | "KEYC" -> ain.keyc <- readKEYC br
    | "CODE" -> ain.code <- readCODE br
    | "FUNC" -> ain.func <- readFUNC br
    | "GLOB" -> ain.glob <- readGLOB br
    | "GSET" -> ain.gset <- readGSET br
    | "STRT" ->
        ain.strt <- readSTRT br;
        ain.struct_by_name <-
          Hashtbl.create_with_key_exn
            (module String)
            ~get_key:(fun (s : Struct.t) -> s.name)
            (Array.to_list ain.strt)
    | "MSG0" -> ain.msg <- readMSG0 br
    | "MSG1" ->
        let msg, uk = readMSG1 br in
        ain.msg <- msg;
        ain.msg1_uk <- Some uk
    | "MAIN" -> ain.main <- readMAIN br
    | "MSGF" -> ain.msgf <- readMSGF br
    | "HLL0" -> ain.hll0 <- readHLL0 br
    | "SWI0" -> ain.swi0 <- readSWI0 br
    | "GVER" -> ain.gver <- readGVER br
    | "SLBL" -> ain.slbl <- readSLBL br
    | "STR0" -> ain.str0 <- readSTR0 br
    | "FNAM" -> ain.fnam <- readFNAM br
    | "OJMP" -> ain.ojmp <- readOJMP br
    | "FNCT" -> ain.fnct <- readFNCT br
    | "DELG" -> ain.delg <- readDELG br
    | "OBJG" -> ain.objg <- readOBJG br
    | "ENUM" ->
        ain.enum <- readENUM br;
        ain.enum_by_name <-
          Hashtbl.of_alist_exn
            (module String)
            (Array.to_list ain.enum |> List.mapi ~f:(fun i name -> (name, i)))
    | tag -> failwith ("unknown tag " ^ tag)
  done

let decode bytes =
  match Stdlib.Bytes.sub_string bytes 0 4 with
  (* encrypted "VERS" *)
  | "\x7e\xf5\x02\xba" ->
      Common.Mt19937.(decrypt ain_decrypt_seed bytes);
      (bytes, false)
  (* compressed ain *)
  | "AI2\x00" ->
      let br = BR.create bytes () in
      br.pos <- 8;
      let out_len = BR.int br in
      br.pos <- 16;
      let ain_buf = Buffer.create out_len in
      let refill buf = BR.blit br buf ~pos:0 ~len:(Bytes.length buf) in
      let flush buf len = Buffer.add_subbytes ain_buf buf ~pos:0 ~len in
      Zlib.uncompress refill flush;
      (Buffer.contents_bytes ain_buf, true)
  | _ -> failwith "unrecognized .ain format"

let load path =
  let bytes, is_ai2 =
    Bytes.of_string (Stdio.In_channel.read_all path) |> decode
  in
  ain.is_ai2 <- is_ai2;
  readSections (BR.create bytes { version = -1 });
  applyGSET ain
