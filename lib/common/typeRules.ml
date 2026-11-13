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

open Base
open Jaf
open CompileError

(* The rules of types: type equality, values that a location accepts,
   references, and lvalues. The functions have no state. They report a
   violation as a compile error at [parent]. *)

(* When true, FuncType None and Delegate None will match any function types.
   This is necessary for the LSP contexts where functype/delegate information
   read from ain file is incomplete. *)
let loose_functype_check = ref false
let sprintf = Printf.sprintf

(* An lvalue is an expression which denotes a location that can be assigned to. *)
let is_lvalue = function
  | { ty = TyFunction _; _ } -> false
  | { node = Ident _ | Member _ | Subscript _ | New _; _ } -> true
  | _ -> false

(* A value from which a reference can be made. NULL, reference, this, and
   lvalue are referenceable. *)
let is_referenceable = function
  | { ty = NullType | Ref _; _ } -> true
  | { node = This; _ } -> true
  | e -> is_lvalue e

(* Implicit dereference of variables and members. The value of a comma
   expression follows its right operand. *)
let rec maybe_deref (e : expression) =
  match e with
  | { ty = Ref t; node = Ident _ | Member _; _ } -> e.ty <- t
  | { node = Seq (_, e2); _ } ->
      maybe_deref e2;
      e.ty <- e2.ty
  | _ -> ()

let insert_rvalue_ref e =
  if not (is_referenceable e) then (
    e.node <- RvalueRef (clone_expr e);
    e.ty <- Ref e.ty)

let rec type_equal (expected : jaf_type) (actual : jaf_type) =
  match (expected, actual) with
  | TypeUnion (a, b), t -> type_equal a t || type_equal b t
  | Ref a, Ref b -> type_equal a b
  | Void, Void -> true
  | Int, (Int | Bool | LongInt) -> true
  | Bool, (Int | Bool | LongInt) -> true
  | LongInt, (Int | Bool | LongInt) -> true
  | Float, Float -> true
  | String, String -> true
  | Struct (_, a), Struct (_, b) -> a = -1 (* any struct *) || a = b
  | IMainSystem, (IMainSystem | Int) -> true
  | FuncType (Some (_, a)), FuncType (Some (_, b)) -> a = b
  | FuncType None, FuncType None -> true
  | Delegate (Some (_, a)), Delegate (Some (_, b)) -> a = b
  | Delegate None, Delegate None -> true
  | MemberPtr (s1, t1), MemberPtr (s2, t2) ->
      String.equal s1 s2 && type_equal t1 t2
  | NullType, (FuncType _ | Delegate _ | IMainSystem | NullType) -> true
  | HLLParam, HLLParam -> true
  | Array a, Array b -> type_equal a b
  | Wrap a, Wrap b -> type_equal a b
  | HLLFunc, HLLFunc -> true
  | Void, _
  | Ref _, _
  | Int, _
  | Bool, _
  | LongInt, _
  | Float, _
  | String, _
  | Struct _, _
  | IMainSystem, _
  | FuncType _, _
  | Delegate _, _
  | HLLParam, _
  | Array _, _
  | Wrap _, _
  | HLLFunc, _
  | TyFunction _, _
  | TyMethod _, _
  | NullType, _
  | MemberPtr _, _ ->
      false
  | Untyped, _ -> compiler_bug "expected type is untyped" None
  | Unresolved _, _ -> compiler_bug "expected type is unresolved" None

let type_castable (dst : jaf_type) (src : jaf_type) =
  match (dst, src) with
  (* FIXME: cast to void should be allowed *)
  | Void, _ -> compiler_bug "type checker cast to void type" None
  | (Int | LongInt | Bool | Float | String), (Int | LongInt | Bool | Float) ->
      true
  | _ -> false

let type_check parent expected (actual : expression) =
  (match expected with Ref _ -> () | _ -> maybe_deref actual);
  match actual.ty with
  | Untyped ->
      compiler_bug "tried to type check untyped expression" (Some parent)
  | NullType -> (
      match expected with
      | Ref _ | FuncType _ | Delegate _ | IMainSystem -> actual.ty <- expected
      | _ -> type_error expected (Some actual) parent)
  | a_t ->
      if not (type_equal expected a_t) then
        type_error expected (Some actual) parent

let ref_type_check parent expected (actual : expression) =
  match actual.ty with
  | NullType -> actual.ty <- Ref expected
  | Untyped ->
      compiler_bug "tried to type check untyped expression" (Some parent)
  | Ref t ->
      if not (type_equal expected t) then
        type_error (Ref expected) (Some actual) parent
  | _ ->
      if not (type_equal expected actual.ty) then
        type_error (Ref expected) (Some actual) parent

let type_check_numeric parent (actual : expression) =
  maybe_deref actual;
  match actual.ty with
  | Int | Bool | LongInt | Float -> ()
  | Untyped ->
      compiler_bug "tried to type check untyped expression" (Some parent)
  | _ -> type_error Int (Some actual) parent

let type_check_member_lhs parent (actual : expression) =
  match actual.ty with
  | Ref (Struct (name, _)) -> name
  | Struct (name, _) -> (
      match actual.node with
      | Ident _ | Member _ | Subscript _ | This -> name
      | _ ->
          compile_error "Member access not allowed for temporary object" parent)
  | Untyped ->
      compiler_bug "tried to type check untyped expression" (Some parent)
  | _ -> type_error (Struct ("struct", 0)) (Some actual) parent

let check_not_array e =
  match e.ty with
  | Array _ | Ref (Array _) ->
      compile_error "array expression not allowed here" (ASTExpression e)
  | _ -> ()

let is_builtin = function
  | Int | Float | String | Array _ | Delegate _ -> true
  | Ref (Int | Float | String | Array _ | Delegate _) -> true
  | _ -> false

let resolve_builtin ctx e name =
  let lib_name, builtin_getter =
    match e.ty with
    | Int | Ref Int -> ("Int", Bytecode.int_builtin_of_string)
    | Float | Ref Float -> ("Float", Bytecode.float_builtin_of_string)
    | String | Ref String -> ("String", Bytecode.string_builtin_of_string)
    | Array _ | Ref (Array _) -> ("Array", Bytecode.array_builtin_of_string)
    | Delegate _ | Ref (Delegate _) ->
        ("Delegate", Bytecode.delegate_builtin_of_string)
    | _ -> failwith "cannot happen"
  in
  match Hashtbl.find ctx.libraries lib_name with
  | Some l when ctx.version >= 800 -> (
      match find_hll_function l name with
      | Some _ -> Some (BuiltinHLL l)
      | None -> None)
  | _ -> (
      maybe_deref e;
      match builtin_getter name with
      | Some b -> Some (BuiltinMethod b)
      | None -> None)

let insert_cast t (e : expression) =
  e.node <- Cast (t, clone_expr e);
  e.ty <- t

let type_coerce_numerics parent op a b =
  type_check_numeric parent a;
  type_check_numeric parent b;
  let coerce t e =
    insert_cast t e;
    t
  in
  let is_compare_op = function
    | Equal | NEqual | LT | GT | LTE | GTE -> true
    | _ -> false
  in
  match (a.ty, b.ty) with
  | Float, Float -> Float
  | Float, _ -> coerce Float b
  | _, Float -> coerce Float a
  | LongInt, LongInt -> LongInt
  | LongInt, Int when is_compare_op op -> LongInt
  | Int, LongInt when is_compare_op op -> LongInt
  | LongInt, _ -> coerce LongInt b
  | _, LongInt -> coerce LongInt a
  | Int, Int -> Int
  | Int, _ -> coerce Int b
  | _, Int -> coerce Int a
  | Bool, Bool -> (
      match op with
      | Equal | NEqual | LogOr | LogAnd | BitOr | BitAnd | BitXor -> Bool
      | _ -> compile_error "invalid operation on boolean type" parent)
  | _ -> compiler_bug "coerce_numerics: non-numeric type" (Some parent)

let check_lvalue e parent =
  if not (is_lvalue e) then not_an_lvalue_error e parent

let check_referenceable e parent =
  if not (is_referenceable e) then not_an_lvalue_error e parent

(*
 * Assigning to a functype or delegate variable is special.
 * The RHS should be an expression like &foo, which has type
 * 'ref function'. This is then converted into the declared
 * functype of the variable (if the prototypes match).
 *)
let check_functype_compatible ctx parent functype (expr : expression) =
  match (functype, expr.ty) with
  | Some (ft_name, _), TyFunction ft ->
      let fd = Hashtbl.find_exn ctx.functypes ft_name in
      if not (ft_compatible (ft_of_fundecl fd) ft) then
        type_error (FuncType functype) (Some expr) parent
  | Some (ft_name, _), FuncType (Some (ft2_name, _)) ->
      let ft = Hashtbl.find_exn ctx.functypes ft_name in
      let ft2 = Hashtbl.find_exn ctx.functypes ft2_name in
      if not (ft_compatible (ft_of_fundecl ft) (ft_of_fundecl ft2)) then
        type_error (FuncType functype) (Some expr) parent
  | Some _, String -> ()
  | Some _, NullType -> expr.ty <- FuncType functype
  | None, (TyFunction _ | FuncType _ | String | NullType)
    when !loose_functype_check ->
      ()
  | _ -> type_check parent (FuncType functype) expr

let check_delegate_compatible ctx parent delegate (expr : expression) =
  match delegate with
  | Some (dg_name, dg_i) -> (
      let dt = ft_of_fundecl (Hashtbl.find_exn ctx.delegates dg_name) in
      let check ft =
        if not (ft_compatible dt ft) then
          type_error (Delegate delegate) (Some expr) parent
      in
      match expr.ty with
      | TyMethod ft -> check ft
      | TyFunction ft ->
          check ft;
          insert_cast (TyMethod dt) expr
      | Delegate (Some (name, idx)) ->
          if not (String.equal name dg_name && dg_i = idx) then
            type_error (Delegate delegate) (Some expr) parent
      | NullType -> expr.ty <- Delegate delegate
      | String ->
          (* XXX: String -> Method conversion, but needs a delegate index
             for DG_STR_TO_METHOD instruction *)
          insert_cast (Delegate delegate) expr;
          expr.ty <- TyMethod dt
      | _ -> type_check parent (Delegate delegate) expr)
  | None -> (
      match expr.ty with
      | Delegate None -> ()
      | (TyMethod _ | TyFunction _ | Delegate _ | String | NullType)
        when !loose_functype_check ->
          ()
      | _ -> type_check parent (Delegate delegate) expr)

let check_assign ctx parent t (rhs : expression) =
  match t with
  | FuncType ft -> check_functype_compatible ctx parent ft rhs
  | Delegate dg -> check_delegate_compatible ctx parent dg rhs
  | TyFunction cb -> (
      match rhs.ty with
      | TyFunction f ->
          if not (ft_compatible cb f) then type_error t (Some rhs) parent
      | _ -> type_error t (Some rhs) parent)
  | TyMethod ft -> (
      match rhs.ty with
      | TyMethod m ->
          if not (ft_compatible ft m) then type_error t (Some rhs) parent
      | TyFunction f ->
          if not (ft_compatible ft f) then type_error t (Some rhs) parent;
          insert_cast (TyMethod ft) rhs
      | _ -> type_error t (Some rhs) parent)
  | Int | LongInt | Bool | Float ->
      type_check_numeric parent rhs;
      insert_cast t rhs
  | Struct _ -> (
      match rhs.ty with
      | Ref t' when type_equal t t' -> ()
      | _ -> type_check parent t rhs)
  | _ -> type_check parent t rhs

let check_funarg_or_return ctx parent t (rhs : expression) =
  match (t, rhs.ty) with
  | FuncType _, String -> type_error t (Some rhs) parent
  | _ -> check_assign ctx parent t rhs

let check_ref_assign parent (lhs : expression) (rhs : expression) =
  (* rhs must be a ref, or an lvalue in order to create a reference to it *)
  check_referenceable rhs parent;
  maybe_deref rhs;
  (* check that lhs is a reference variable of the appropriate type *)
  match lhs.node with
  | Ident (_, (LocalVariable v | GlobalVariable v)) -> (
      match v.type_spec.ty with
      | Ref ty -> ref_type_check parent ty rhs
      | _ -> type_error (Ref rhs.ty) (Some lhs) parent)
  | Member (_, _, ClassVariable _) -> (
      match lhs.ty with
      | Ref t -> ref_type_check parent t rhs
      | _ -> type_error (Ref rhs.ty) (Some lhs) parent)
  | _ ->
      (* FIXME? this isn't really a _type_ error *)
      type_error (Ref rhs.ty) (Some lhs) parent
