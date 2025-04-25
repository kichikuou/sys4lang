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
open Bytecode
open Jaf

let make_params (types : jaf_type list) defaults =
  let defaults =
    match defaults with
    | [] -> List.map types ~f:(fun _ -> None)
    | _ -> defaults
  in
  List.mapi (List.zip_exn types defaults) ~f:(fun i (t, initval) ->
      {
        name = "";
        location = dummy_location;
        array_dim = [];
        is_const = false;
        is_private = false;
        kind = Parameter;
        type_spec = { ty = t; location = dummy_location };
        initval;
        index = Some i;
      })

let fundecl_of_syscall sys =
  let make return_type arg_types =
    {
      name = string_of_syscall sys;
      loc = dummy_location;
      return = { ty = return_type; location = dummy_location };
      params = make_params arg_types [];
      body = None;
      is_label = false;
      is_private = false;
      index = Some (int_of_syscall sys);
      class_name = None;
      class_index = None;
    }
  in
  match sys with
  | Exit -> make Void [ Int ]
  | GlobalSave -> make Int [ String; String ]
  | GlobalLoad -> make Int [ String; String ]
  | LockPeek -> make Int []
  | UnlockPeek -> make Int []
  | Reset -> make Void []
  | Output -> make String [ String ]
  | MsgBox -> make String [ String ]
  | ResumeSave -> make Int [ String; String; Ref Int ]
  | ResumeLoad -> make Void [ String; String ]
  | ExistFile -> make Int [ String ]
  | OpenWeb -> make Void [ String ]
  | GetSaveFolderName -> make String []
  | GetTime -> make Int []
  | GetGameName -> make String []
  | Error -> make String [ String ]
  | ExistSaveFile -> make Int [ String ]
  | IsDebugMode -> make Int []
  | MsgBoxOkCancel -> make Int [ String ]
  | GetFuncStackName -> make String [ Int ]
  | Peek -> make Void []
  | Sleep -> make Void [ Int ]
  | ResumeWriteComment -> make Bool [ String; String; Ref (Array String) ]
  | ResumeReadComment -> make Bool [ String; String; Ref (Array String) ]
  | GroupSave -> make Int [ String; String; String; Ref Int ]
  | GroupLoad -> make Int [ String; String; String; Ref Int ]
  | DeleteSaveFile -> make Int [ String ]
  | ExistFunc -> make Bool [ String ]
  | CopySaveFile -> make Int [ String; String ]

(* `&NULL` expression (used as default value for callback functions) *)
let addr_null =
  let null_func =
    make_expr ~ty:(TyFunction ("NULL", 0)) (Ident ("NULL", FunctionName "NULL"))
  in
  make_expr ~ty:(Ref null_func.ty) (Unary (AddrOf, null_func))

let fundecl_of_builtin builtin receiver_ty node_opt =
  let elem_ty = match receiver_ty with Array t -> t | _ -> Void in
  let rank = array_rank receiver_ty in
  let t_method = Ref (TyMethod ("", 0)) in
  let make return_type name ?(defaults = []) (arg_types : jaf_type list) =
    {
      name;
      loc = dummy_location;
      return = { ty = return_type; location = dummy_location };
      params = make_params arg_types defaults;
      body = None;
      is_label = false;
      is_private = false;
      index = None;
      class_name = None;
      class_index = None;
    }
  in
  match builtin with
  | Assert -> make Void "assert" [ Int; String; String; Int ]
  | IntString -> make String "String" []
  | FloatString -> make String "String" []
  | StringInt -> make Int "Int" []
  | StringLength -> make Int "Length" []
  | StringLengthByte -> make Int "LengthByte" []
  | StringEmpty -> make Int "Empty" []
  | StringFind -> make Int "Find" [ String ]
  | StringGetPart -> make String "GetPart" [ Int; Int ]
  | StringPushBack -> make Void "PushBack" [ Int ]
  | StringPopBack -> make Void "PopBack" []
  | StringErase -> make Void "Erase" [ Int ]
  | ArrayAlloc -> make Void "Alloc" (List.init rank ~f:(fun _ -> Int))
  | ArrayRealloc -> make Void "Realloc" [ Int ]
  | ArrayFree -> make Void "Free" []
  | ArrayNumof ->
      make Int "Numof" [ Int ]
        ~defaults:
          (if rank = 1 then [ Some (make_expr ~ty:Int (ConstInt 1)) ] else [])
  | ArrayCopy -> make Int "Copy" [ Int; Ref receiver_ty; Int; Int ]
  | ArrayFill -> make Int "Fill" [ Int; Int; elem_ty ]
  | ArrayPushBack -> make Void "PushBack" [ elem_ty ]
  | ArrayPopBack -> make Void "PopBack" []
  | ArrayEmpty -> make Int "Empty" []
  | ArrayErase -> make Int "Erase" [ Int ]
  | ArrayInsert -> make Void "Insert" [ Int; elem_ty ]
  | ArrayReverse -> make Void "Reverse" []
  | ArraySort ->
      let cb_argtype, cb_default =
        match elem_ty with
        | Int | Float | String -> (elem_ty, Some addr_null)
        | Struct _ -> (Ref elem_ty, None)
        | _ ->
            CompileError.compile_error
              ("Sort() is not supported for array@" ^ jaf_type_to_string elem_ty)
              (Option.value_exn node_opt)
      in
      make Void "Sort"
        [ Callback ([ cb_argtype; cb_argtype ], Int) ]
        ~defaults:[ cb_default ]
  | ArrayFind ->
      let cb_argtype, cb_default =
        match elem_ty with
        | Int | Float | Bool | String -> (elem_ty, Some addr_null)
        | Struct _ -> (Ref elem_ty, None)
        | _ ->
            CompileError.compile_error
              ("Find() is not supported for array@" ^ jaf_type_to_string elem_ty)
              (Option.value_exn node_opt)
      in
      make Int "Find"
        [ Int; Int; cb_argtype; Callback ([ cb_argtype; cb_argtype ], Bool) ]
        ~defaults:[ None; None; None; cb_default ]
  | DelegateSet -> make Void "Set" [ t_method ]
  | DelegateAdd -> make Void "Add" [ t_method ]
  | DelegateNumof -> make Int "Numof" []
  | DelegateExist -> make Int "Exist" [ t_method ]
  | DelegateErase -> make Void "Erase" [ t_method ]
  | DelegateClear -> make Void "Clear" []

let default_function : Ain.Function.t =
  {
    index = -1;
    name = "";
    address = 0;
    nr_args = 0;
    vars = [];
    return_type = Ain.Type.make Void;
    is_label = false;
    is_lambda = false;
    crc = 0l;
    struct_type = None;
    enum_type = None;
  }

let function_of_syscall sys =
  jaf_to_ain_function (fundecl_of_syscall sys)
    { default_function with index = int_of_syscall sys }

let function_of_builtin sys receiver_ty =
  jaf_to_ain_function (fundecl_of_builtin sys receiver_ty None) default_function

let fundecl_of_callback args ret =
  {
    name = "";
    loc = dummy_location;
    return = { ty = ret; location = dummy_location };
    params = make_params args [];
    body = None;
    is_label = false;
    is_private = false;
    index = None;
    class_name = None;
    class_index = None;
  }
