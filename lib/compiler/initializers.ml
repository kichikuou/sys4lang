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

open Common
open Base
open Jaf

(* Makes the functions that allocate arrays with dimensions: an initializer
   for each struct, and the initializer of the globals. The functions are
   registered and laid out as ordinary functions. *)

let make_stmt node = { node; delete_vars = []; loc = dummy_location }

let array_alloc_stmt (v : variable) =
  let var = make_expr (Ident (v.name, UnresolvedIdent)) in
  let func = make_expr (Member (var, "Alloc", UnresolvedMember)) in
  let call =
    make_expr
      (Call
         ( func,
           List.map ~f:Option.some v.array_dim,
           BuiltinCall Bytecode.ArrayAlloc ))
  in
  make_stmt (Expression call)

let array_alloc_stmts (vars : variable list) =
  List.filter_map vars ~f:(function
    | { array_dim = _ :: _; is_const = false; _ } as v ->
        Some (array_alloc_stmt v)
    | _ -> None)

let make_function ?class_name ?class_index name body =
  {
    name;
    loc = dummy_location;
    return = { ty = Void; location = dummy_location };
    params = [];
    body = Some body;
    is_label = false;
    is_lambda = false;
    is_private = false;
    index = None;
    class_name;
    class_index;
  }

let has_constructor (s : structdecl) =
  List.exists s.decls ~f:(function Constructor _ -> true | _ -> false)

(* The function that allocates the array members of a struct. If the struct
   declares a constructor, this is S@2, which the constructor calls. Otherwise
   this is the constructor S@0. *)
let struct_initializer ctx (s : structdecl) =
  let members =
    List.concat_map s.decls ~f:(function MemberDecl ds -> ds.vars | _ -> [])
  in
  make_function ~class_name:s.name
    ~class_index:(Hashtbl.find_exn ctx.structs s.name).index
    (if has_constructor s then "2" else "0")
    (array_alloc_stmts members)

(* A struct needs no initializer if it has no constructor and no array
   member. *)
let is_empty_constructor (f : fundecl) =
  String.equal f.name "0" && Option.exists f.body ~f:List.is_empty

(* The function "0", which allocates the global arrays. *)
let global_initializer decls =
  let globals =
    List.concat_map decls ~f:(function
      | Global ds -> ds.vars
      | GlobalGroup gg -> List.concat_map gg.vardecls ~f:(fun ds -> ds.vars)
      | _ -> [])
  in
  make_function "0" (array_alloc_stmts globals)

(* The function "NULL", which is the entry 0 of the function table. *)
let null_function () = { (make_function "NULL" []) with index = Some 0 }

(* Inserts the call of S@2 at the beginning of each constructor body. *)
let insert_initializer_calls decls =
  let insert (f : fundecl) =
    Option.iter f.body ~f:(fun body ->
        let func = make_expr (Ident ("2", UnresolvedIdent)) in
        let call = make_expr (Call (func, [], UnresolvedCall)) in
        f.body <- Some (make_stmt (Expression call) :: body))
  in
  List.iter decls ~f:(function
    | StructDef s ->
        List.iter s.decls ~f:(function Constructor f -> insert f | _ -> ())
    | Function f when is_constructor f -> insert f
    | _ -> ())

(* The initializers of a program, in the order of their function indices. *)
let generate ctx decls =
  insert_initializer_calls decls;
  let struct_initializers =
    List.filter_map decls ~f:(function
      | StructDef s ->
          let f = struct_initializer ctx s in
          if is_empty_constructor f then None else Some f
      | _ -> None)
  in
  let global = global_initializer decls in
  if Option.exists global.body ~f:List.is_empty then struct_initializers
  else struct_initializers @ [ global ]
