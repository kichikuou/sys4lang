(* Copyright (C) 2021 Nunuhara Cabbage <nunuhara@haniwa.technology>
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
open CompileError

(* Layout gives the indices of functions, globals, and struct members to
   resolved declarations, and writes the AIN tables. The indices of types come
   from the context. *)

(* Gives AIN table indices to declarations. When function_index returns None,
   the function gets no index. *)
class type allocator = object
  method function_index : fundecl -> string -> int option
  method lambda_index : string -> int
  method global_index : variable -> group:int -> int
  method global_group_index : global_group -> int
end

(* Adds an entry to the end of the table for each declaration. Only the
   functions with a body get an entry. *)
let build_allocator ain : allocator =
  object
    method function_index decl name =
      if Option.is_some decl.body then Some (Ain.add_function ain name).index
      else None

    method lambda_index name = (Ain.add_function ain name).index
    method global_index (g : variable) ~group = Ain.add_global ain g.name group

    method global_group_index (gg : global_group) =
      Ain.add_global_group ain gg.name
  end

(* The number of entries in each table of an AIN. *)
type table_sizes = {
  nr_functions : int;
  nr_globals : int;
  nr_structs : int;
  nr_functypes : int;
  nr_delegates : int;
}

let table_sizes ain =
  {
    nr_functions = Ain.nr_functions ain;
    nr_globals = Ain.nr_globals ain;
    nr_structs = Ain.nr_structs ain;
    nr_functypes = Ain.nr_functypes ain;
    nr_delegates = Ain.nr_delegates ain;
  }

(* Adds the entries for the numbers that are not in the table. *)
let add_type_entries (numbering : numbering) nr_entries add =
  Hashtbl.to_alist numbering.numbers
  |> List.filter ~f:(fun (_, i) -> i >= nr_entries)
  |> List.sort ~compare:(fun (_, a) (_, b) -> Int.compare a b)
  |> List.iter ~f:(fun (name, i) ->
      if add name <> i then
        compiler_bug ("table index of " ^ name ^ " is not its number") None)

let jaf_to_ain_variables j_p =
  let rec convert_params (params : variable list) (result : Ain.Variable.t list)
      index =
    match params with
    | [] -> List.rev result
    | x :: xs ->
        let var =
          Ain.Variable.make ~index x.name (jaf_to_ain_type x.type_spec.ty)
        in
        if is_ref_scalar x.type_spec.ty then
          let void = Ain.Variable.make ~index:(index + 1) "<void>" Void in
          convert_params xs (void :: var :: result) (index + 2)
        else convert_params xs (var :: result) (index + 1)
  in
  convert_params j_p [] 0

let jaf_to_ain_function j_f (a_f : Ain.Function.t) =
  let vars = jaf_to_ain_variables j_f.params in
  {
    a_f with
    vars;
    nr_args = List.length vars;
    return_type = jaf_to_ain_type j_f.return.ty;
    is_label = j_f.is_label;
  }

let jaf_to_ain_struct j_s (a_s : Ain.Struct.t) =
  let members =
    List.filter_map j_s.decls ~f:(function
      | MemberDecl ds when not ds.is_const_decls -> Some ds.vars
      | _ -> None)
    |> List.concat |> jaf_to_ain_variables
  in
  let is_ctor = function Constructor _ -> true | _ -> false in
  let constructor =
    match List.find j_s.decls ~f:is_ctor with
    | Some (Constructor ctor) -> Option.value_exn ctor.index
    | _ -> -1
  in
  let is_dtor = function Destructor _ -> true | _ -> false in
  let destructor =
    match List.find j_s.decls ~f:is_dtor with
    | Some (Destructor dtor) -> Option.value_exn dtor.index
    | _ -> -1
  in
  {
    a_s with
    members;
    constructor;
    destructor
    (* TODO: interfaces *)
    (* TODO: vmethods *);
  }

let jaf_to_ain_functype j_f =
  let variables = jaf_to_ain_variables j_f.params in
  Ain.FunctionType.
    {
      name = j_f.name;
      index = Option.value_exn j_f.index;
      variables;
      nr_arguments = List.length variables;
      return_type = jaf_to_ain_type j_f.return.ty;
    }

let jaf_to_ain_hll_function j_f =
  let jaf_to_ain_hll_argument (param : variable) =
    Ain.Library.Argument.create param.name (jaf_to_ain_type param.type_spec.ty)
  in
  let return_type = jaf_to_ain_type j_f.return.ty in
  let arguments = List.map j_f.params ~f:jaf_to_ain_hll_argument in
  Ain.Library.Function.create j_f.name return_type arguments

let member_variables (s : structdecl) =
  List.concat_map s.decls ~f:(function
    | MemberDecl ds when not ds.is_const_decls -> ds.vars
    | _ -> [])

(* The declaration and the definition of a function have the same index. *)
let set_function_index ctx (f : fundecl) index =
  f.index <- index;
  match function_entry_of ctx f with
  | Some { decl = Some decl; _ } -> decl.index <- index
  | _ -> ()

let check_methods_defined ctx (s : structdecl) =
  let has_index f =
    Option.exists
      (find_function ctx (mangled_name f))
      ~f:(fun f -> Option.is_some f.index)
  in
  List.iter s.decls ~f:(function
    | Method f | Constructor f | Destructor f ->
        if not (has_index f) then
          compile_error
            (Printf.sprintf "No definition of %s::%s found" s.name f.name)
            (ASTDeclaration (Function f))
    | _ -> ())

(* Gives the indices in the order of the declarations. A lambda gets the index
   that follows the index of the enclosing function. *)
class index_visitor ctx (allocator : allocator) (base : table_sizes) =
  object (self)
    inherit ivisitor as super
    val mutable gg_index = -1
    val mutable nr_lambdas = 0

    (* A lambda name is a sequence number that no function of the AIN has. *)
    method private next_lambda_name =
      nr_lambdas <- nr_lambdas + 1;
      let name = Printf.sprintf "<lambda : %d>" nr_lambdas in
      if Option.is_some (Ain.get_function ctx.ain name) then
        self#next_lambda_name
      else name

    (* ain v1 scenario labels are not recorded in the FUNC table, and get no
       index. *)
    method! visit_fundecl decl =
      if decl.is_lambda then (
        decl.name <- self#next_lambda_name;
        decl.index <- Some (allocator#lambda_index (mangled_name decl)))
      else if not (decl.is_label && Ain.version ctx.ain = 1) then
        set_function_index ctx decl
          (allocator#function_index decl (mangled_name decl));
      super#visit_fundecl decl

    method private visit_global (g : variable) =
      if not g.is_const then (
        let index = allocator#global_index g ~group:gg_index in
        g.index <- Some index;
        if index >= base.nr_globals then
          let entry = Ain.get_global_entry ctx.ain index in
          Ain.write_global ctx.ain
            {
              entry with
              variable =
                {
                  entry.variable with
                  value_type = jaf_to_ain_type g.type_spec.ty;
                };
            })

    method private visit_members (s : structdecl) =
      List.fold (member_variables s) ~init:0 ~f:(fun index v ->
          v.index <- Some index;
          index + if is_ref_scalar v.type_spec.ty then 2 else 1)
      |> ignore

    method! visit_declaration decl =
      match decl with
      | Global ds -> List.iter ds.vars ~f:self#visit_global
      | GlobalGroup gg ->
          gg_index <- allocator#global_group_index gg;
          List.iter gg.vardecls ~f:(fun ds ->
              List.iter ds.vars ~f:self#visit_global);
          gg_index <- -1
      | Function f -> (
          self#visit_fundecl f;
          match (f.class_name, f.name, f.index) with
          | None, "main", Some i -> Ain.set_main_function ctx.ain i
          | None, "message", Some i -> Ain.set_message_function ctx.ain i
          | _ -> ())
      | StructDef s ->
          self#visit_members s;
          List.iter s.decls ~f:(function
            | Constructor f | Destructor f | Method f -> self#visit_fundecl f
            | AccessSpecifier _ | MemberDecl _ -> ())
      | FuncTypeDef _ | DelegateDef _ | Enum _ -> ()
  end

(* Gives indices to the declarations of a program, and writes the table
   entries that are added. The entries that the AIN already has are not
   written. *)
let layout ?allocator ctx decls =
  let allocator =
    match allocator with Some a -> a | None -> build_allocator ctx.ain
  in
  let base = table_sizes ctx.ain in
  add_type_entries ctx.struct_numbers base.nr_structs (fun name ->
      (Ain.add_struct ctx.ain name).index);
  add_type_entries ctx.functype_numbers base.nr_functypes (fun name ->
      (Ain.add_functype ctx.ain name).index);
  add_type_entries ctx.delegate_numbers base.nr_delegates (fun name ->
      (Ain.add_delegate ctx.ain name).index);
  (new index_visitor ctx allocator base)#visit_toplevel decls;
  let is_new (f : fundecl) nr_entries =
    Option.value_exn f.index >= nr_entries
  in
  List.iter decls ~f:(function
    | FuncTypeDef f when is_new f base.nr_functypes ->
        Ain.write_functype ctx.ain (jaf_to_ain_functype f)
    | DelegateDef f when is_new f base.nr_delegates ->
        Ain.write_delegate ctx.ain (jaf_to_ain_functype f)
    | StructDef s ->
        let index = (Hashtbl.find_exn ctx.structs s.name).index in
        if index >= base.nr_structs then (
          check_methods_defined ctx s;
          Ain.get_struct_by_index ctx.ain index
          |> jaf_to_ain_struct s |> Ain.write_struct ctx.ain)
    | Function { name = "0"; class_index = Some s; index = Some index; _ } ->
        (* The generated constructor of a struct that declares none. *)
        Ain.write_struct ctx.ain
          { (Ain.get_struct_by_index ctx.ain s) with constructor = index }
    | _ -> ())

(* Adds a library to the AIN. [decls] are the declarations of its .hll
   file. *)
let add_library ctx (lib : library) decls =
  let functions =
    List.filter_map decls ~f:(function Function f -> Some f | _ -> None)
  in
  let ain_lib = Ain.add_library ctx.ain lib.hll_name in
  Ain.write_library ctx.ain
    {
      ain_lib with
      functions = Array.of_list_map functions ~f:jaf_to_ain_hll_function;
    };
  List.iteri functions ~f:(fun i f -> f.index <- Some i);
  lib.index <- Some ain_lib.index
