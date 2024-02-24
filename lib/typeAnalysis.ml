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

(* Implicit dereference of variables and members. *)
let maybe_deref (e : expression) =
  match e with
  | { ty = Ref t; node = Ident _ | Member _; _ } -> e.ty <- t
  | _ -> ()

let rec type_equal (expected : jaf_type) (actual : jaf_type) =
  match (expected, actual) with
  | Ref a, Ref b -> type_equal a b
  | Void, Void -> true
  | Int, (Int | Bool | LongInt) -> true
  | Bool, (Int | Bool | LongInt) -> true
  | LongInt, (Int | Bool | LongInt) -> true
  | Float, Float -> true
  | String, String -> true
  | Struct (_, a), Struct (_, b) -> a = b
  | IMainSystem, IMainSystem -> true
  | FuncType (_, a), FuncType (_, b) -> a = b
  | Delegate (_, a), Delegate (_, b) -> a = b
  | NullType, (FuncType _ | Delegate _ | IMainSystem | NullType) -> true
  | HLLParam, HLLParam -> true
  | Array a, Array b -> type_equal a b
  | Wrap a, Wrap b -> type_equal a b
  | HLLFunc, HLLFunc -> true
  | TyFunction _, TyFunction _ -> true
  | TyMethod _, TyMethod _ -> true
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
  | NullType, _ ->
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

let type_check_struct parent (actual : expression) =
  maybe_deref actual;
  match actual.ty with
  | Struct (name, _) -> name
  | Untyped ->
      compiler_bug "tried to type check untyped expression" (Some parent)
  | _ -> type_error (Struct ("", 0)) (Some actual) parent

let is_builtin = function
  | Int | Float | String | Array _ | Delegate _ -> true
  | Ref (Int | Float | String | Array _ | Delegate _) -> true
  | _ -> false

let builtin_of_string (t : Jaf.jaf_type) name =
  match t with
  | Int -> Bytecode.int_builtin_of_string name
  | Float -> Bytecode.float_builtin_of_string name
  | String -> Bytecode.string_builtin_of_string name
  | Array _ -> Bytecode.array_builtin_of_string name
  | Delegate _ -> Bytecode.delegate_builtin_of_string name
  | _ -> None

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
  match (a.ty, b.ty) with
  | Float, Float -> Float
  | Float, _ -> coerce Float b
  | _, Float -> coerce Float a
  | LongInt, LongInt -> LongInt
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

class type_analyze_visitor ctx =
  object (self)
    inherit ivisitor ctx as super
    val mutable errors : compile_error list = []
    method errors = List.rev errors

    method catch_errors f =
      try f () with CompileError e -> errors <- e :: errors

    (* an lvalue is an expression which denotes a location that can be assigned to *)
    method check_lvalue (e : expression) (parent : ast_node) =
      let check_lvalue_type = function
        | TyFunction _ -> not_an_lvalue_error e parent
        | _ -> ()
      in
      match e.node with
      | Ident (_, _) -> check_lvalue_type e.ty
      | Member (_, _, _) -> check_lvalue_type e.ty
      | Subscript (_, _) -> ()
      | New (_, _, _) -> ()
      | _ -> not_an_lvalue_error e parent

    (* A value from which a reference can be made. NULL, reference, this, and lvalue are referenceable. *)
    method check_referenceable (e : expression) (parent : ast_node) =
      match e.ty with
      | NullType -> ()
      | Ref _ -> ()
      | _ -> ( match e.node with This -> () | _ -> self#check_lvalue e parent)

    method check_delegate_compatible parent dg_name dg_i (expr : expression) =
      match expr.ty with
      | Ref (TyMethod (f_name, _)) ->
          let dg = Hashtbl.find_exn ctx.delegates dg_name in
          let f = Hashtbl.find_exn ctx.functions f_name in
          if not (fundecl_compatible dg f) then
            type_error (Delegate (dg_name, dg_i)) (Some expr) parent
      | Delegate (name, idx) ->
          if not (String.equal name dg_name && dg_i = idx) then
            type_error (Delegate (dg_name, dg_i)) (Some expr) parent
      | _ -> type_error (Ref (TyMethod ("", -1))) (Some expr) parent

    method check_assign parent t (rhs : expression) =
      match t with
      (*
       * Assigning to a functype or delegate variable is special.
       * The RHS should be an expression like &foo, which has type
       * 'ref function'. This is then converted into the declared
       * functype of the variable (if the prototypes match).
       *)
      | FuncType (ft_name, ft_i) -> (
          match rhs.ty with
          | Ref (TyFunction (f_name, _)) ->
              let ft = Hashtbl.find_exn ctx.functypes ft_name in
              let f = Hashtbl.find_exn ctx.functions f_name in
              if not (fundecl_compatible ft f) then
                type_error (FuncType (ft.name, ft_i)) (Some rhs) parent
          | FuncType (ft2_name, _) ->
              let ft = Hashtbl.find_exn ctx.functypes ft_name in
              let ft2 = Hashtbl.find_exn ctx.functypes ft2_name in
              if not (fundecl_compatible ft ft2) then
                type_error (FuncType (ft_name, ft_i)) (Some rhs) parent
          | String -> ()
          | NullType -> rhs.ty <- t
          | _ -> type_error (Ref (TyFunction ("", -1))) (Some rhs) parent)
      | Delegate (dn, di) -> self#check_delegate_compatible parent dn di rhs
      | Int | LongInt | Bool | Float ->
          type_check_numeric parent rhs;
          insert_cast t rhs
      | _ -> type_check parent t rhs

    method check_ref_assign parent (lhs : expression) (rhs : expression) =
      (* rhs must be a ref, or an lvalue in order to create a reference to it *)
      self#check_referenceable rhs parent;
      maybe_deref rhs;
      (* check that lhs is a reference variable of the appropriate type *)
      match lhs.node with
      | Ident (name, _) -> (
          match environment#resolve name with
          | ResolvedLocal v | ResolvedGlobal v -> (
              match v.type_spec.ty with
              | Ref ty -> ref_type_check parent ty rhs
              | _ -> type_error (Ref rhs.ty) (Some lhs) parent)
          | UnresolvedName -> undefined_variable_error name parent
          | _ -> type_error (Ref rhs.ty) (Some lhs) parent)
      | Member (_, _, Some (ClassVariable _)) -> (
          match lhs.ty with
          | Ref t -> ref_type_check parent t rhs
          | _ -> type_error (Ref rhs.ty) (Some lhs) parent)
      | _ ->
          (* FIXME? this isn't really a _type_ error *)
          type_error (Ref rhs.ty) (Some lhs) parent

    method! visit_expression expr =
      super#visit_expression expr;
      (* convenience functions which always pass parent expression *)
      let check = type_check (ASTExpression expr) in
      let check_numeric = type_check_numeric (ASTExpression expr) in
      let coerce_numerics = type_coerce_numerics (ASTExpression expr) in
      let check_struct = type_check_struct (ASTExpression expr) in
      let check_expr (a : expression) b = check a.ty b in
      (* check function call arguments *)
      let check_call name params args =
        let nr_params = List.length params in
        if not (nr_params = List.length args) then
          arity_error name nr_params args (ASTExpression expr)
        else if nr_params > 0 then
          let check_arg a v =
            match v.type_spec.ty with
            | Ref ty ->
                self#check_referenceable a (ASTExpression a);
                ref_type_check (ASTExpression a) ty a
            | _ -> self#check_assign (ASTExpression a) v.type_spec.ty a
          in
          List.iter2_exn args params ~f:check_arg
      in
      match expr.node with
      | ConstInt _ -> expr.ty <- Int
      | ConstFloat _ -> expr.ty <- Float
      | ConstChar _ -> expr.ty <- Int
      | ConstString _ -> expr.ty <- String
      | Ident (name, _) -> (
          match environment#resolve name with
          | ResolvedLocal v ->
              expr.node <- Ident (name, Some (LocalVariable (-1)));
              expr.ty <- v.type_spec.ty
          | ResolvedConstant v ->
              expr.node <- Ident (name, Some GlobalConstant);
              expr.ty <- v.type_spec.ty
          | ResolvedGlobal g ->
              expr.node <-
                Ident (name, Some (GlobalVariable (Option.value_exn g.index)));
              expr.ty <- g.type_spec.ty
          | ResolvedFunction f ->
              expr.node <- Ident (name, Some (FunctionName name));
              expr.ty <- TyFunction (name, Option.value_exn f.index)
          | ResolvedLibrary _ ->
              expr.node <- Ident (name, Some (HLLName name));
              expr.ty <- Void
          | ResolvedSystem ->
              expr.node <- Ident ("system", Some System);
              expr.ty <- Void
          | ResolvedBuiltin builtin ->
              expr.node <- Ident (name, Some (BuiltinFunction builtin));
              expr.ty <- Void
          | UnresolvedName -> undefined_variable_error name (ASTExpression expr)
          )
      | Unary (op, e) -> (
          match op with
          | UPlus | UMinus | PreInc | PreDec | PostInc | PostDec ->
              check_numeric e;
              expr.ty <- e.ty
          | LogNot | BitNot ->
              check Int e;
              expr.ty <- e.ty
          | AddrOf -> (
              match e.ty with
              | TyFunction _ as f -> expr.ty <- Ref f
              | TyMethod _ as m -> expr.ty <- Ref m
              | _ ->
                  type_error (TyFunction ("", -1)) (Some e) (ASTExpression expr)
              ))
      | Binary (op, a, b) -> (
          match op with
          | Plus -> (
              maybe_deref a;
              maybe_deref b;
              match a.ty with
              | String ->
                  check String b;
                  expr.ty <- a.ty
              | _ -> expr.ty <- coerce_numerics op a b)
          | Minus | Times | Divide -> expr.ty <- coerce_numerics op a b
          | LogOr | LogAnd | BitOr | BitXor | BitAnd | LShift | RShift ->
              maybe_deref a;
              maybe_deref b;
              check Int a;
              check Int b;
              expr.ty <- a.ty
          | Modulo ->
              maybe_deref a;
              maybe_deref b;
              (match a.ty with
              | String -> (
                  (* TODO: check type matches format specifier if format string is a literal *)
                  match b.ty with
                  | Int | Float | Bool | LongInt | String -> ()
                  | _ -> type_error Int (Some b) (ASTExpression expr))
              | Int | Bool | LongInt -> check Int b
              | _ -> type_error Int (Some a) (ASTExpression expr));
              expr.ty <- a.ty
          | Equal | NEqual ->
              maybe_deref a;
              maybe_deref b;
              (* NOTE: NULL is not allowed on lhs *)
              (match (a.ty, b.ty) with
              | String, _ -> check String b
              | FuncType (_, ft_i), FuncType (_, ft_j) ->
                  if ft_i <> ft_j then
                    type_error a.ty (Some b) (ASTExpression expr)
              | FuncType (ft_name, _), Ref (TyFunction (f_name, _)) ->
                  let ft = Hashtbl.find_exn ctx.functypes ft_name in
                  let f = Hashtbl.find_exn ctx.functions f_name in
                  if not (fundecl_compatible ft f) then
                    type_error a.ty (Some b) (ASTExpression expr)
              | FuncType _, NullType -> b.ty <- a.ty
              | _ -> coerce_numerics op a b |> ignore);
              expr.ty <- Int
          | LT | GT | LTE | GTE ->
              maybe_deref a;
              maybe_deref b;
              (match a.ty with
              | String -> check String b
              | _ -> coerce_numerics op a b |> ignore);
              expr.ty <- Int
          | RefEqual | RefNEqual ->
              (match a.node with
              | Ident _ | Member (_, _, Some (ClassVariable _)) ->
                  self#check_ref_assign (ASTExpression expr) a b
              | This -> not_an_lvalue_error a (ASTExpression expr)
              | _ -> (
                  self#check_referenceable b (ASTExpression expr);
                  match a.ty with
                  | Ref t -> ref_type_check (ASTExpression expr) t b
                  | _ -> not_an_lvalue_error a (ASTExpression expr)));
              expr.ty <- Int)
      | Assign (op, lhs, rhs) -> (
          self#check_lvalue lhs (ASTExpression expr);
          maybe_deref lhs;
          maybe_deref rhs;
          (match (lhs.ty, op) with
          | _, EqAssign -> self#check_assign (ASTExpression expr) lhs.ty rhs
          | String, PlusAssign -> check String rhs
          | Delegate (dn, di), (PlusAssign | MinusAssign) ->
              self#check_delegate_compatible (ASTExpression expr) dn di rhs
          | _, (PlusAssign | MinusAssign | TimesAssign | DivideAssign) ->
              check_numeric lhs;
              check_numeric rhs;
              insert_cast lhs.ty rhs;
              check_expr lhs rhs
          | ( _,
              ( ModuloAssign | OrAssign | XorAssign | AndAssign | LShiftAssign
              | RShiftAssign ) ) ->
              check Int lhs;
              check Int rhs);
          (* XXX: Nothing is left on stack after assigning method to delegate *)
          match (lhs.ty, rhs.ty) with
          | Delegate _, Ref (TyMethod _) -> expr.ty <- Void
          | _ -> expr.ty <- rhs.ty)
      | Seq (_, e) -> expr.ty <- e.ty
      | Ternary (test, con, alt) ->
          check Int test;
          check_expr con alt;
          expr.ty <- con.ty
      | Cast (t, e) ->
          maybe_deref e;
          if not (type_castable t e.ty) then
            type_error t (Some e) (ASTExpression expr);
          expr.ty <- t
      | Subscript (obj, i) -> (
          maybe_deref obj;
          check Int i;
          match obj.ty with
          | Array t -> expr.ty <- t
          | String -> expr.ty <- Int
          | _ ->
              (* FIXME: Expected type here is array<?>|string *)
              let expected = Array Void in
              type_error expected (Some obj) (ASTExpression expr))
      (* system function *)
      | Member (({ node = Ident (_, Some System); _ } as e), syscall_name, _)
        -> (
          match Bytecode.syscall_of_string syscall_name with
          | Some sys ->
              expr.node <- Member (e, syscall_name, Some (SystemFunction sys));
              expr.ty <- TyFunction ("", 0)
          | None ->
              (* TODO: separate error type for this? *)
              undefined_variable_error ("system." ^ syscall_name)
                (ASTExpression expr))
      (* HLL function *)
      | Member
          (({ node = Ident (lib_name, Some (HLLName _)); _ } as e), fun_name, _)
        -> (
          match find_hll_function ctx lib_name fun_name with
          | Some _ ->
              expr.node <-
                Member (e, fun_name, Some (HLLFunction (lib_name, fun_name)));
              expr.ty <- TyFunction ("", 0)
          | None ->
              (* TODO: separate error type for this? *)
              undefined_variable_error
                (lib_name ^ "." ^ fun_name)
                (ASTExpression expr))
      (* built-in methods *)
      | Member (e, name, _) when is_builtin e.ty -> (
          maybe_deref e;
          match builtin_of_string e.ty name with
          | Some builtin ->
              expr.node <- Member (e, name, Some (BuiltinMethod builtin));
              expr.ty <- TyFunction ("", 0)
          | None ->
              (* TODO: separate error type for this? *)
              undefined_variable_error name (ASTExpression expr))
      (* member variable OR method *)
      | Member (obj, member_name, _) -> (
          let struc = Hashtbl.find_exn ctx.structs (check_struct obj) in
          match Hashtbl.find struc.members member_name with
          | Some member ->
              expr.node <-
                Member
                  ( obj,
                    member_name,
                    Some
                      (ClassVariable (struc.index, Option.value_exn member.index))
                  );
              expr.ty <- member.type_spec.ty
          | None -> (
              let fun_name = struc.name ^ "@" ^ member_name in
              match Hashtbl.find ctx.functions fun_name with
              | Some f ->
                  expr.node <-
                    Member (obj, member_name, Some (ClassMethod fun_name));
                  expr.ty <- TyMethod (fun_name, Option.value_exn f.index)
              | None ->
                  (* TODO: separate error type for this? *)
                  undefined_variable_error
                    (struc.name ^ "." ^ member_name)
                    (ASTExpression expr)))
      (* regular function call *)
      | Call (({ node = Ident (_, Some (FunctionName name)); _ } as e), args, _)
        ->
          let f = Hashtbl.find_exn ctx.functions name in
          let fno = Option.value_exn f.index in
          check_call f.name f.params args;
          expr.node <- Call (e, args, Some (FunctionCall fno));
          expr.ty <- f.return.ty
      (* built-in function call *)
      | Call
          ( ({ node = Ident (_, Some (BuiltinFunction builtin)); _ } as e),
            args,
            _ ) ->
          let f = Builtin.fundecl_of_builtin builtin Void in
          check_call f.name f.params args;
          expr.node <- Call (e, args, Some (BuiltinCall builtin));
          expr.ty <- f.return.ty
      (* method call *)
      | Call
          (({ node = Member (_, _, Some (ClassMethod name)); _ } as e), args, _)
        ->
          let f = Hashtbl.find_exn ctx.functions name in
          check_call f.name f.params args;
          let mcall =
            MethodCall (Option.value_exn f.class_index, Option.value_exn f.index)
          in
          expr.node <- Call (e, args, Some mcall);
          expr.ty <- f.return.ty
      (* HLL call *)
      | Call
          ( ({ node = Member (_, _, Some (HLLFunction (lib_name, fun_name))); _ }
             as e),
            args,
            _ ) ->
          let f = Option.value_exn (find_hll_function ctx lib_name fun_name) in
          check_call f.name f.params args;
          let lib_no =
            Option.value_exn (Ain.get_library_index ctx.ain lib_name)
          in
          let fun_no =
            Option.value_exn
              (Ain.get_library_function_index ctx.ain lib_no fun_name)
          in
          expr.node <- Call (e, args, Some (HLLCall (lib_no, fun_no, -1)));
          expr.ty <- f.return.ty
      (* system call *)
      | Call
          ( ({ node = Member (_, _, Some (SystemFunction sys)); _ } as e),
            args,
            _ ) ->
          let f = Builtin.fundecl_of_syscall sys in
          check_call f.name f.params args;
          expr.node <- Call (e, args, Some (SystemCall sys));
          expr.ty <- f.return.ty
      (* built-in method call *)
      | Call
          ( ({ node = Member (obj, _, Some (BuiltinMethod builtin)); _ } as e),
            args,
            _ ) ->
          (* TODO: rewrite to HLL call for 11+ (?) *)
          if Ain.version_gte ctx.ain (11, 0) then
            compile_error "ain v11+ built-ins not implemented"
              (ASTExpression expr);
          let f = Builtin.fundecl_of_builtin builtin obj.ty in
          (* TODO: properly check type-generic arguments based on object type *)
          check_call f.name f.params args;
          expr.node <- Call (e, args, Some (BuiltinCall builtin));
          expr.ty <- f.return.ty
      (* functype/delegate call *)
      | Call (e, args, _) -> (
          match e.ty with
          | FuncType (name, _) ->
              let f = Hashtbl.find_exn ctx.functypes name in
              check_call f.name f.params args;
              expr.node <-
                Call (e, args, Some (FuncTypeCall (Option.value_exn f.index)));
              expr.ty <- f.return.ty
          | Delegate (name, _) ->
              let f = Hashtbl.find_exn ctx.delegates name in
              check_call f.name f.params args;
              expr.node <-
                Call (e, args, Some (DelegateCall (Option.value_exn f.index)));
              expr.ty <- f.return.ty
          | _ -> type_error (FuncType ("", -1)) (Some e) (ASTExpression expr))
      | New ({ ty; _ }, args, _) -> (
          match ty with
          | Struct (st_name, _) ->
              (* TODO: look up the correct constructor for given arguments *)
              (match Hashtbl.find ctx.functions (st_name ^ "@0") with
              | None ->
                  if not (List.length args = 0) then
                    (* TODO: signal error properly here *)
                    compile_error "Arguments provided to default constructor"
                      (ASTExpression expr)
              | Some ctor -> check_call ctor.name ctor.params args);
              expr.ty <- ty
          | _ -> type_error (Struct ("", -1)) None (ASTExpression expr))
      | This -> (
          match environment#current_class with
          | Some ty -> expr.ty <- ty
          | None ->
              (* TODO: separate error type for this? *)
              undefined_variable_error "this" (ASTExpression expr))
      | Null -> expr.ty <- NullType

    method! visit_statement stmt =
      (* rewrite character constants at statement-level as messages *)
      (match stmt.node with
      | Expression { node = ConstChar msg; _ } ->
          stmt.node <- MessageCall (msg, None, None)
      | _ -> ());
      self#catch_errors (fun () ->
          super#visit_statement stmt;
          match stmt.node with
          | EmptyStatement -> ()
          | Declarations _ -> ()
          | Expression _ -> ()
          | Compound _ -> ()
          | Label _ -> ()
          | If (test, _, _) | While (test, _) | DoWhile (test, _) ->
              type_check (ASTStatement stmt) Int test
          | For (_, Some test, _, _) -> type_check (ASTStatement stmt) Int test
          | For (_, None, _, _) -> ()
          | Goto _ -> ()
          | Continue -> ()
          | Break -> ()
          | Switch (expr, _) ->
              (* TODO: string switch *)
              type_check (ASTStatement stmt) Int expr
          | Case expr ->
              (* TODO: string switch *)
              type_check (ASTStatement stmt) Int expr
          | Default -> ()
          | Return (Some e) -> (
              match environment#current_function with
              | None ->
                  compiler_bug "return statement outside of function"
                    (Some (ASTStatement stmt))
              | Some f -> (
                  match f.return.ty with
                  | Ref ty ->
                      self#check_referenceable e (ASTExpression e);
                      ref_type_check (ASTStatement stmt) ty e
                  | _ -> self#check_assign (ASTStatement stmt) f.return.ty e))
          | Return None -> (
              match environment#current_function with
              | None ->
                  compiler_bug "return statement outside of function"
                    (Some (ASTStatement stmt))
              | Some f -> (
                  match f.return.ty with
                  | Void -> ()
                  | _ -> type_error f.return.ty None (ASTStatement stmt)))
          | Jump name -> (
              match environment#resolve name with
              | ResolvedFunction f when f.is_label -> ()
              | _ ->
                  compile_error
                    (name ^ " is not a scenario function")
                    (ASTStatement stmt))
          | Jumps e -> type_check (ASTExpression e) String e
          | MessageCall (msg, f_name, _) -> (
              match f_name with
              | Some name -> (
                  match Hashtbl.find ctx.functions name with
                  | Some f ->
                      if not (List.is_empty f.params) then
                        arity_error f.name (List.length f.params) []
                          (ASTStatement stmt);
                      stmt.node <-
                        MessageCall
                          (msg, f_name, Some (Option.value_exn f.index))
                  | None -> undefined_variable_error name (ASTStatement stmt))
              | None -> ())
          | RefAssign (lhs, rhs) ->
              self#check_ref_assign (ASTStatement stmt) lhs rhs
          | ObjSwap (lhs, rhs) ->
              self#check_lvalue lhs (ASTStatement stmt);
              self#check_lvalue rhs (ASTStatement stmt);
              (* FIXME: error if the type is ref or unsupported type *)
              type_check (ASTStatement stmt) lhs.ty rhs)

    method! visit_variable var =
      super#visit_variable var;
      let rec calculate_array_rank (t : jaf_type) =
        match t with Array sub_t -> 1 + calculate_array_rank sub_t | _ -> 0
      in
      let rank = calculate_array_rank var.type_spec.ty in
      let nr_dims = List.length var.array_dim in
      (* Only one array dimension may be specified in ain v11+ *)
      if nr_dims > 1 && Ain.version_gte ctx.ain (11, 0) then
        compile_error "Multiple array dimensions specified for ain v11+"
          (ASTVariable var);
      (* Check that there is no initializer if array has explicit dimensions *)
      if nr_dims > 0 && Option.is_some var.initval then
        compile_error "Initializer provided for array with explicit dimensions"
          (ASTVariable var);
      (* Check that number of dims matches rank of array *)
      if nr_dims > 0 && not (nr_dims = rank) then
        compile_error "Number of array dimensions does not match array rank"
          (ASTVariable var);
      (* Check that array dims are integers *)
      List.iter var.array_dim ~f:(fun e -> type_check (ASTVariable var) Int e);
      (* Check initval matches declared type *)
      match var.initval with
      | Some expr -> (
          match var.type_spec.ty with
          | Ref ty ->
              self#check_referenceable expr (ASTVariable var);
              maybe_deref expr;
              ref_type_check (ASTVariable var) ty expr
          | t -> self#check_assign (ASTVariable var) t expr)
      | None -> ()

    method! visit_declaration decl =
      self#catch_errors (fun () -> super#visit_declaration decl)

    method! visit_fundecl f =
      super#visit_fundecl f;
      if String.equal f.name "main" then
        match (f.return.ty, f.params) with
        | Int, [] -> Ain.set_main_function ctx.ain (Option.value_exn f.index)
        | _ ->
            compile_error "Invalid declaration of 'main' function"
              (ASTDeclaration (Function f))
      else if String.equal f.name "message" then
        match f.return.ty with
        | Void -> (
            match List.map f.params ~f:(fun v -> v.type_spec.ty) with
            | [ Int; Int; String ] ->
                Ain.set_message_function ctx.ain (Option.value_exn f.index)
            | _ ->
                compile_error "Invalid declaration of 'message' function"
                  (ASTDeclaration (Function f)))
        | _ ->
            compile_error "invalid declaration of 'message' function"
              (ASTDeclaration (Function f))
  end

let check_types ctx decls =
  let visitor = new type_analyze_visitor ctx in
  visitor#visit_toplevel decls;
  let errors = visitor#errors in
  if not (List.is_empty errors) then raise_error (CompileError.ErrorList errors)
