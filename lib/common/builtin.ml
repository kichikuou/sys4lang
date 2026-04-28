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

let make_params (params : (string * jaf_type) list) defaults =
  let defaults =
    match defaults with
    | [] -> List.map params ~f:(fun _ -> None)
    | _ -> defaults
  in
  List.mapi (List.zip_exn params defaults) ~f:(fun i ((name, t), initval) ->
      {
        name;
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
  let make return_type params =
    {
      name = string_of_syscall sys;
      loc = dummy_location;
      return = { ty = return_type; location = dummy_location };
      params = make_params params [];
      body = None;
      is_label = false;
      is_lambda = false;
      is_private = false;
      index = Some (int_of_syscall sys);
      class_name = None;
      class_index = None;
    }
  in
  match sys with
  | Exit -> make Void [ ("nResult", Int) ]
  | GlobalSave -> make Int [ ("szKeyName", String); ("szFileName", String) ]
  | GlobalLoad -> make Int [ ("szKeyName", String); ("szFileName", String) ]
  | LockPeek -> make Int []
  | UnlockPeek -> make Int []
  | Reset -> make Void []
  | Output -> make String [ ("szText", String) ]
  | MsgBox -> make String [ ("szText", String) ]
  | ResumeSave ->
      make Int
        [ ("szKeyName", String); ("szFileName", String); ("nResult", Ref Int) ]
  | ResumeLoad -> make Void [ ("szKeyName", String); ("szFileName", String) ]
  | ExistFile -> make Int [ ("szFileName", String) ]
  | OpenWeb -> make Void [ ("szURL", String) ]
  | GetSaveFolderName -> make String []
  | GetTime -> make Int []
  | GetGameName -> make String []
  | Error -> make String [ ("szText", String) ]
  | ExistSaveFile -> make Int [ ("szFileName", String) ]
  | IsDebugMode -> make Int []
  | MsgBoxOkCancel -> make Int [ ("szText", String) ]
  | GetFuncStackName -> make String [ ("nIndex", Int) ]
  | Peek -> make Void []
  | Sleep -> make Void [ ("nSleep", Int) ]
  | ResumeWriteComment ->
      make Bool
        [
          ("szKeyName", String);
          ("szFileName", String);
          ("aszComment", Ref (Array String));
        ]
  | ResumeReadComment ->
      make Bool
        [
          ("szKeyName", String);
          ("szFileName", String);
          ("aszComment", Ref (Array String));
        ]
  | GroupSave ->
      make Int
        [
          ("szKeyName", String);
          ("szFileName", String);
          ("szGroupName", String);
          ("nNumofLoad", Ref Int);
        ]
  | GroupLoad ->
      make Int
        [
          ("szKeyName", String);
          ("szFileName", String);
          ("szGroupName", String);
          ("nNumofLoad", Ref Int);
        ]
  | DeleteSaveFile -> make Int [ ("szFileName", String) ]
  | ExistFunc -> make Bool [ ("szFuncName", String) ]
  | CopySaveFile ->
      make Int [ ("szDestFileName", String); ("szSourceFileName", String) ]

(* `&NULL` expression (used as default value for callback functions) *)
let addr_null =
  make_expr ~ty:(TyFunction ([], Void)) (FuncAddr ("NULL", Some 0))

let method_null =
  let ty = TyMethod ([], Void) in
  make_expr ~ty (Cast (ty, addr_null))

let fundecl_of_builtin ctx builtin receiver_ty node_opt =
  let elem_ty = match receiver_ty with Array t -> t | _ -> Void in
  let rank = array_rank receiver_ty in
  let delegate_ft = function
    | Delegate (Some (dg_name, _)) ->
        TyMethod (ft_of_fundecl (Hashtbl.find_exn ctx.delegates dg_name))
    | _ -> failwith ("Delegate expected, got " ^ jaf_type_to_string receiver_ty)
  in
  let make return_type name ?(defaults = []) (params : (string * jaf_type) list)
      =
    {
      name;
      loc = dummy_location;
      return = { ty = return_type; location = dummy_location };
      params = make_params params defaults;
      body = None;
      is_label = false;
      is_lambda = false;
      is_private = false;
      index = None;
      class_name = None;
      class_index = None;
    }
  in
  match builtin with
  | Assert ->
      make Void "assert"
        [ ("exp", Int); ("szExp", String); ("file", String); ("line", Int) ]
  | IntString -> make String "String" []
  | FloatString ->
      make String "String"
        [ ("nDecimal", Int) ]
        ~defaults:[ Some (make_expr ~ty:Int (ConstInt (-1))) ]
  | StringInt -> make Int "Int" []
  | StringLength -> make Int "Length" []
  | StringLengthByte -> make Int "LengthByte" []
  | StringEmpty -> make Int "Empty" []
  | StringFind -> make Int "Find" [ ("szKey", String) ]
  | StringGetPart -> make String "GetPart" [ ("nIndex", Int); ("nLength", Int) ]
  | StringPushBack -> make Void "PushBack" [ ("nChara", Int) ]
  | StringPopBack -> make Void "PopBack" []
  | StringErase -> make Void "Erase" [ ("nIndex", Int) ]
  | ArrayAlloc ->
      make Void "Alloc" (List.init rank ~f:(fun _ -> ("nElements", Int)))
  | ArrayRealloc -> make Void "Realloc" [ ("nElements", Int) ]
  | ArrayFree -> make Void "Free" []
  | ArrayNumof ->
      make Int "Numof"
        [ ("nDimension", Int) ]
        ~defaults:
          (if rank = 1 then [ Some (make_expr ~ty:Int (ConstInt 1)) ] else [])
  | ArrayCopy ->
      make Int "Copy"
        [
          ("nDestIndex", Int);
          ("a", Ref receiver_ty);
          ("nSrcIndex", Int);
          ("nLength", Int);
        ]
  | ArrayFill ->
      make Int "Fill" [ ("nIndex", Int); ("nLength", Int); ("value", elem_ty) ]
  | ArrayPushBack -> make Void "PushBack" [ ("value", elem_ty) ]
  | ArrayPopBack -> make Void "PopBack" []
  | ArrayEmpty -> make Int "Empty" []
  | ArrayErase -> make Int "Erase" [ ("nIndex", Int) ]
  | ArrayInsert -> make Void "Insert" [ ("nIndex", Int); ("value", elem_ty) ]
  | ArrayReverse -> make Void "Reverse" []
  | ArraySort ->
      let cb_argtype, cb_default =
        match elem_ty with
        | Int | Float | String ->
            ( elem_ty,
              Some (if ctx.version < 800 then addr_null else method_null) )
        | Struct _ -> (Ref elem_ty, None)
        | _ ->
            CompileError.compile_error
              ("Sort() is not supported for array@" ^ jaf_type_to_string elem_ty)
              (Option.value_exn node_opt)
      in
      let cb_type =
        if ctx.version < 800 then TyFunction ([ cb_argtype; cb_argtype ], Int)
        else TyMethod ([ cb_argtype; cb_argtype ], Bool)
      in
      make Void "Sort" [ ("func", cb_type) ] ~defaults:[ cb_default ]
  | ArraySortBy -> (
      match elem_ty with
      | Struct (name, _) ->
          make Void "SortBy"
            [ ("func", MemberPtr (name, TypeUnion (Int, String))) ]
      | _ ->
          CompileError.compile_error
            ("SortBy() is not supported for array@" ^ jaf_type_to_string elem_ty)
            (Option.value_exn node_opt))
  | ArrayFind ->
      let cb_argtype, cb_default =
        match elem_ty with
        | Int | Float | Bool | String ->
            ( elem_ty,
              Some (if ctx.version < 800 then addr_null else method_null) )
        | Struct _ -> (Ref elem_ty, None)
        | _ ->
            CompileError.compile_error
              ("Find() is not supported for array@" ^ jaf_type_to_string elem_ty)
              (Option.value_exn node_opt)
      in
      let cb_type =
        if ctx.version < 800 then TyFunction ([ cb_argtype; cb_argtype ], Bool)
        else TyMethod ([ cb_argtype; cb_argtype ], Bool)
      in
      make Int "Find"
        [
          ("nBegin", Int); ("nEnd", Int); ("key", cb_argtype); ("func", cb_type);
        ]
        ~defaults:[ None; None; None; cb_default ]
  | DelegateNumof -> make Int "Numof" []
  | DelegateExist -> make Int "Exist" [ ("func", delegate_ft receiver_ty) ]
  | DelegateErase -> make Void "Erase" [ ("func", delegate_ft receiver_ty) ]
  | DelegateClear -> make Void "Clear" []

let default_function : Ain.Function.t =
  {
    index = -1;
    name = "";
    address = 0;
    nr_args = 0;
    vars = [];
    return_type = Void;
    is_label = false;
    is_lambda = false;
    crc = 0l;
    struct_type = None;
    enum_type = None;
  }

let function_of_syscall sys =
  jaf_to_ain_function (fundecl_of_syscall sys)
    { default_function with index = int_of_syscall sys }

let function_of_builtin ctx sys receiver_ty =
  jaf_to_ain_function
    (fundecl_of_builtin ctx sys receiver_ty None)
    default_function
