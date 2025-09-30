(* Copyright (C) 2025 kichikuou <KichikuouChrome@gmail.com>
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
open Ppx_yojson_conv_lib.Yojson_conv.Primitives

module InitializationOptions = struct
  type t = {
    srcDir : string; [@default ""]
    ainPath : string; [@default ""]
    srcEncoding : string; [@default ""]
  }
  [@@deriving_inline of_yojson] [@@yojson.allow_extra_fields]

  let _ = fun (_ : t) -> ()

  let t_of_yojson =
    (let _tp_loc = "lib/types.ml.InitializationOptions.t" in
     function
     | `Assoc field_yojsons as yojson -> (
         let srcDir_field = ref Ppx_yojson_conv_lib.Option.None
         and ainPath_field = ref Ppx_yojson_conv_lib.Option.None
         and srcEncoding_field = ref Ppx_yojson_conv_lib.Option.None
         and duplicates = ref []
         and extra = ref [] in
         let rec iter = function
           | (field_name, _field_yojson) :: tail ->
               (match field_name with
               | "srcDir" -> (
                   match Ppx_yojson_conv_lib.( ! ) srcDir_field with
                   | Ppx_yojson_conv_lib.Option.None ->
                       let fvalue = string_of_yojson _field_yojson in
                       srcDir_field := Ppx_yojson_conv_lib.Option.Some fvalue
                   | Ppx_yojson_conv_lib.Option.Some _ ->
                       duplicates :=
                         field_name :: Ppx_yojson_conv_lib.( ! ) duplicates)
               | "ainPath" -> (
                   match Ppx_yojson_conv_lib.( ! ) ainPath_field with
                   | Ppx_yojson_conv_lib.Option.None ->
                       let fvalue = string_of_yojson _field_yojson in
                       ainPath_field := Ppx_yojson_conv_lib.Option.Some fvalue
                   | Ppx_yojson_conv_lib.Option.Some _ ->
                       duplicates :=
                         field_name :: Ppx_yojson_conv_lib.( ! ) duplicates)
               | "srcEncoding" -> (
                   match Ppx_yojson_conv_lib.( ! ) srcEncoding_field with
                   | Ppx_yojson_conv_lib.Option.None ->
                       let fvalue = string_of_yojson _field_yojson in
                       srcEncoding_field :=
                         Ppx_yojson_conv_lib.Option.Some fvalue
                   | Ppx_yojson_conv_lib.Option.Some _ ->
                       duplicates :=
                         field_name :: Ppx_yojson_conv_lib.( ! ) duplicates)
               | _ -> ());
               iter tail
           | [] -> ()
         in
         iter field_yojsons;
         match Ppx_yojson_conv_lib.( ! ) duplicates with
         | _ :: _ ->
             Ppx_yojson_conv_lib.Yojson_conv_error.record_duplicate_fields
               _tp_loc
               (Ppx_yojson_conv_lib.( ! ) duplicates)
               yojson
         | [] -> (
             match Ppx_yojson_conv_lib.( ! ) extra with
             | _ :: _ ->
                 Ppx_yojson_conv_lib.Yojson_conv_error.record_extra_fields
                   _tp_loc
                   (Ppx_yojson_conv_lib.( ! ) extra)
                   yojson
             | [] ->
                 let srcDir_value, ainPath_value, srcEncoding_value =
                   ( Ppx_yojson_conv_lib.( ! ) srcDir_field,
                     Ppx_yojson_conv_lib.( ! ) ainPath_field,
                     Ppx_yojson_conv_lib.( ! ) srcEncoding_field )
                 in
                 {
                   srcDir =
                     (match srcDir_value with
                     | Ppx_yojson_conv_lib.Option.None -> ""
                     | Ppx_yojson_conv_lib.Option.Some v -> v);
                   ainPath =
                     (match ainPath_value with
                     | Ppx_yojson_conv_lib.Option.None -> ""
                     | Ppx_yojson_conv_lib.Option.Some v -> v);
                   srcEncoding =
                     (match srcEncoding_value with
                     | Ppx_yojson_conv_lib.Option.None -> ""
                     | Ppx_yojson_conv_lib.Option.Some v -> v);
                 }))
     | _ as yojson ->
         Ppx_yojson_conv_lib.Yojson_conv_error.record_list_instead_atom _tp_loc
           yojson
      : Ppx_yojson_conv_lib.Yojson.Safe.t -> t)

  let _ = t_of_yojson

  [@@@deriving.end]

  let default = { srcDir = ""; ainPath = ""; srcEncoding = "" }
end
