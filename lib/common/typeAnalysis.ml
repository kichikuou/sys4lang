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
open TypeRules

let sprintf = Printf.sprintf

class type_analyze_visitor ctx =
  object (self)
    inherit ivisitor ctx as super
    val mutable errors : compile_error list = []
    method errors = List.rev errors

    method catch_errors f =
      try f () with Compile_error e -> errors <- e :: errors

    method! visit_expression expr =
      super#visit_expression expr;
      (* convenience functions which always pass parent expression *)
      let check = type_check (ASTExpression expr) in
      let check_numeric = type_check_numeric (ASTExpression expr) in
      let coerce_numerics = type_coerce_numerics (ASTExpression expr) in
      let check_member_lhs = type_check_member_lhs (ASTExpression expr) in
      let check_expr (a : expression) b = check a.ty b in
      (* check function call arguments *)
      let check_call name params args =
        let nr_params = List.length params in
        let nr_args = List.length args in
        if nr_args > nr_params then
          arity_error name nr_params args (ASTExpression expr);
        let check_arg i a v =
          match (a, v.initval) with
          | Some a, _ ->
              (match v.type_spec.ty with
              | Ref ty ->
                  check_referenceable a (ASTExpression a);
                  ref_type_check (ASTExpression a) ty a
              | _ ->
                  check_funarg_or_return ctx (ASTExpression a) v.type_spec.ty a);
              Some a
          | None, Some e ->
              (* NOTE: `e` may be from another file that has not yet been type-checked. *)
              Some e
          | None, None ->
              if i < nr_args then
                compile_error
                  (sprintf "Missing argument #%d" i)
                  (ASTExpression expr)
              else arity_error name nr_params args (ASTExpression expr)
        in
        let args = args @ List.init (nr_params - nr_args) ~f:(fun _ -> None) in
        List.map3_exn
          (List.init nr_params ~f:(fun i -> i))
          args params ~f:check_arg
      in
      match expr.node with
      | ConstInt _ -> expr.ty <- Int
      | ConstFloat _ -> expr.ty <- Float
      | ConstChar _ -> expr.ty <- Int
      | ConstString _ -> expr.ty <- String
      | Ident (name, _) -> (
          match self#env#resolve name with
          | ResolvedLocal v ->
              expr.node <- Ident (name, LocalVariable v);
              expr.ty <- v.type_spec.ty
          | ResolvedGlobal g ->
              let ident_type =
                if g.is_const then GlobalConstant g else GlobalVariable g
              in
              expr.node <- Ident (name, ident_type);
              expr.ty <- g.type_spec.ty
          | ResolvedFunction f ->
              expr.node <- Ident (name, FunctionName name);
              expr.ty <- TyFunction (ft_of_fundecl f)
          | ResolvedMember (s, v) ->
              expr.node <-
                Member
                  ( make_expr ~ty:(Struct (s.name, s.index)) This,
                    name,
                    if v.is_const then ClassConst v else ClassVariable v );
              expr.ty <- v.type_spec.ty
          | ResolvedMethod (s, f) ->
              expr.node <-
                Member
                  ( make_expr ~ty:(Struct (s.name, s.index)) This,
                    name,
                    ClassMethod f );
              expr.ty <- TyMethod (ft_of_fundecl f)
          | ResolvedLibrary l ->
              expr.node <- Ident (name, HLLName l);
              expr.ty <- Void
          | ResolvedSystem ->
              expr.node <- Ident ("system", System);
              expr.ty <- Void
          | ResolvedBuiltin builtin ->
              expr.node <- Ident (name, BuiltinFunction builtin);
              expr.ty <- Void
          | UnresolvedName -> undefined_variable_error name (ASTExpression expr)
          )
      | FuncAddr (name, _) -> (
          match find_function ctx name with
          | Some f ->
              expr.node <- FuncAddr (name, Some f);
              expr.ty <- TyFunction (ft_of_fundecl f)
          | None -> (
              match Util.parse_qualified_name name with
              | None, name -> undefined_variable_error name (ASTExpression expr)
              | Some sname, name -> (
                  match self#env#resolve_qualified sname name with
                  | UnresolvedName ->
                      undefined_variable_error
                        (sname ^ "::" ^ name)
                        (ASTExpression expr)
                  | ResolvedMember (_, v) ->
                      expr.node <- MemberAddr (sname, v);
                      expr.ty <- MemberPtr (sname, v.type_spec.ty)
                  | _ ->
                      compiler_bug
                        "resolve_qualified returned an unexpected value"
                        (Some (ASTExpression expr)))))
      | MemberAddr _ ->
          compiler_bug "unexpected MemberAddr" (Some (ASTExpression expr))
      | Unary (op, e) -> (
          match op with
          | UPlus | UMinus | PreInc | PreDec | PostInc | PostDec ->
              check_numeric e;
              expr.ty <- e.ty
          | LogNot | BitNot ->
              check Int e;
              expr.ty <- Int)
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
              | FuncType (Some (_, ft_i)), FuncType (Some (_, ft_j)) ->
                  if ft_i <> ft_j then
                    type_error a.ty (Some b) (ASTExpression expr)
              | FuncType (Some (ft_name, _)), TyFunction f ->
                  let ft = Hashtbl.find_exn ctx.functypes ft_name in
                  if not (ft_compatible (ft_of_fundecl ft) f) then
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
              | Ident _ | Member (_, _, ClassVariable _) ->
                  check_ref_assign (ASTExpression expr) a b
              | This -> not_an_lvalue_error a (ASTExpression expr)
              | _ -> (
                  check_referenceable b (ASTExpression expr);
                  match a.ty with
                  | Ref t -> ref_type_check (ASTExpression expr) t b
                  | _ -> not_an_lvalue_error a (ASTExpression expr)));
              expr.ty <- Int)
      | Assign (op, lhs, rhs) -> (
          check_lvalue lhs (ASTExpression expr);
          maybe_deref lhs;
          maybe_deref rhs;
          (match (lhs.ty, op) with
          | _, EqAssign -> (
              check_assign ctx (ASTExpression expr) lhs.ty rhs;
              (* If lhs is a string subscript access, change the operator to CharAssign *)
              match lhs.node with
              | Subscript ({ ty = String; _ }, _) ->
                  expr.node <- Assign (CharAssign, lhs, rhs)
              | _ -> ())
          | String, PlusAssign -> check String rhs
          | Delegate dg, (PlusAssign | MinusAssign) ->
              check_delegate_compatible ctx (ASTExpression expr) dg rhs
          | _, (PlusAssign | MinusAssign | TimesAssign | DivideAssign) ->
              check_numeric lhs;
              check_numeric rhs;
              insert_cast lhs.ty rhs;
              check_expr lhs rhs
          | ( _,
              ( ModuloAssign | OrAssign | XorAssign | AndAssign | LShiftAssign
              | RShiftAssign ) ) ->
              check Int lhs;
              check Int rhs
          | _, CharAssign ->
              compiler_bug "unexpected CharAssign" (Some (ASTExpression expr)));
          (* XXX: Nothing is left on stack after assigning method to delegate *)
          match (lhs.ty, rhs.ty) with
          | Delegate _, (TyMethod _ | String) -> expr.ty <- Void
          | _ -> expr.ty <- rhs.ty)
      | Seq (e1, e2) ->
          check_not_array e1;
          expr.ty <- e2.ty
      | Ternary (test, con, alt) ->
          check Int test;
          (match (con.ty, alt.ty) with
          | Ref _, Ref _ -> ()
          | Ref _, _ -> maybe_deref con
          | _, Ref _ -> maybe_deref alt
          | _, _ -> ());
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
      | Member (({ node = Ident (_, System); _ } as e), syscall_name, _) -> (
          match Bytecode.syscall_of_string syscall_name with
          | Some sys ->
              expr.node <- Member (e, syscall_name, SystemFunction sys);
              expr.ty <- TyFunction ([], Void)
          | None ->
              (* TODO: separate error type for this? *)
              undefined_variable_error ("system." ^ syscall_name)
                (ASTExpression expr))
      (* HLL function *)
      | Member (({ node = Ident (lib_name, HLLName lib); _ } as e), fun_name, _)
        -> (
          match find_hll_function lib fun_name with
          | Some _ ->
              expr.node <- Member (e, fun_name, HLLFunction (lib, fun_name));
              expr.ty <- TyFunction ([], Void)
          | None ->
              (* TODO: separate error type for this? *)
              undefined_variable_error
                (lib_name ^ "." ^ fun_name)
                (ASTExpression expr))
      (* built-in methods *)
      | Member (e, name, _) when is_builtin e.ty -> (
          match resolve_builtin ctx e name with
          | Some builtin ->
              expr.node <- Member (e, name, builtin);
              expr.ty <- TyFunction ([], Void)
          | None ->
              (* TODO: separate error type for this? *)
              undefined_variable_error name (ASTExpression expr))
      (* member variable OR method *)
      | Member (obj, member_name, _) -> (
          let struc = Hashtbl.find_exn ctx.structs (check_member_lhs obj) in
          let access_check () =
            match self#env#current_class with
            | Some (Struct (_, i)) when i = struc.index -> ()
            | _ ->
                compile_error
                  (sprintf "%s::%s is not public" struc.name member_name)
                  (ASTExpression expr)
          in
          match Hashtbl.find struc.members member_name with
          | Some member ->
              if member.is_private then access_check ();
              expr.node <-
                Member
                  ( obj,
                    member_name,
                    if member.is_const then ClassConst member
                    else ClassVariable member );
              expr.ty <- member.type_spec.ty
          | None -> (
              let fun_name = struc.name ^ "@" ^ member_name in
              match find_function ctx fun_name with
              | Some f ->
                  if f.is_private then access_check ();
                  expr.node <- Member (obj, member_name, ClassMethod f);
                  expr.ty <- TyMethod (ft_of_fundecl f)
              | None ->
                  (* TODO: separate error type for this? *)
                  undefined_variable_error
                    (struc.name ^ "." ^ member_name)
                    (ASTExpression expr)))
      (* regular function call *)
      | Call (({ node = Ident (_, FunctionName name); _ } as e), args, _) ->
          let f = Option.value_exn (find_function ctx name) in
          let args = check_call f.name f.params args in
          expr.node <- Call (e, args, FunctionCall f);
          expr.ty <- f.return.ty
      (* built-in function call *)
      | Call (({ node = Ident (_, BuiltinFunction builtin); _ } as e), args, _)
        ->
          let f =
            Builtin.fundecl_of_builtin ctx builtin Void
              (Some (ASTExpression expr))
          in
          let args = check_call f.name f.params args in
          expr.node <- Call (e, args, BuiltinCall builtin);
          expr.ty <- f.return.ty
      (* method call *)
      | Call (({ node = Member (_, _, ClassMethod f); _ } as e), args, _) ->
          let args = check_call f.name f.params args in
          expr.node <- Call (e, args, MethodCall f);
          expr.ty <- f.return.ty
      (* HLL call *)
      | Call
          ( ({ node = Member (_, _, HLLFunction (lib, fun_name)); _ } as e),
            args,
            _ ) ->
          let f = Option.value_exn (find_hll_function lib fun_name) in
          let args = check_call f.name f.params args in
          expr.node <- Call (e, args, HLLCall (lib, f));
          expr.ty <- f.return.ty
      (* system call *)
      | Call (({ node = Member (_, _, SystemFunction sys); _ } as e), args, _)
        ->
          let f = Builtin.fundecl_of_syscall sys in
          let args = check_call f.name f.params args in
          expr.node <- Call (e, args, SystemCall sys);
          expr.ty <- f.return.ty
      (* built-in method call *)
      | Call
          (({ node = Member (obj, _, BuiltinMethod builtin); _ } as e), args, _)
        ->
          let f =
            Builtin.fundecl_of_builtin ctx builtin obj.ty
              (Some (ASTExpression expr))
          in
          let args = check_call f.name f.params args in
          expr.node <- Call (e, args, BuiltinCall builtin);
          expr.ty <- f.return.ty
      (* built-in method call via HLL *)
      | Call
          (({ node = Member (obj, fun_name, BuiltinHLL lib); _ } as e), args, _)
        ->
          let f = Option.value_exn (find_hll_function lib fun_name) in
          let args = check_call f.name (List.tl_exn f.params) args in
          insert_rvalue_ref obj;
          expr.node <- Call (e, Some obj :: args, HLLCall (lib, f));
          expr.ty <- f.return.ty
      (* functype/delegate call *)
      | Call (e, args, _) -> (
          match e.ty with
          | FuncType (Some (name, _)) ->
              let f = Hashtbl.find_exn ctx.functypes name in
              let args = check_call f.name f.params args in
              expr.node <- Call (e, args, FuncTypeCall f);
              expr.ty <- f.return.ty
          | Delegate (Some (name, _)) ->
              let f = Hashtbl.find_exn ctx.delegates name in
              let args = check_call f.name f.params args in
              expr.node <- Call (e, args, DelegateCall f);
              expr.ty <- f.return.ty
          | _ -> type_error (FuncType None) (Some e) (ASTExpression expr))
      | New { ty; _ } -> (
          match ty with
          | Struct _ -> expr.ty <- Ref ty
          | _ -> type_error (Struct ("", -1)) None (ASTExpression expr))
      | DummyRef _ ->
          compiler_bug "DummyRef in type checker" (Some (ASTExpression expr))
      | RvalueRef _ ->
          compiler_bug "RvalueRef in type checker" (Some (ASTExpression expr))
      | This -> (
          match self#env#current_class with
          | Some ty -> expr.ty <- ty
          | None ->
              (* TODO: separate error type for this? *)
              undefined_variable_error "this" (ASTExpression expr))
      | Null -> expr.ty <- NullType
      | Lambda f -> expr.ty <- TyMethod (ft_of_fundecl f)

    method! visit_statement stmt =
      self#catch_errors (fun () ->
          super#visit_statement stmt;
          match stmt.node with
          | EmptyStatement -> ()
          | Declarations _ -> ()
          | Expression ({ node = Ident (_, FunctionName _); _ } as e) ->
              (* rewrite bare function names at statement-level as function calls *)
              let expr =
                {
                  node = Call (e, [], UnresolvedCall);
                  ty = Untyped;
                  loc = e.loc;
                }
              in
              self#visit_expression expr;
              stmt.node <- Expression expr
          | Expression e -> check_not_array e
          | Compound _ -> ()
          | Label _ -> ()
          | If (test, _, _) | While (test, _) | DoWhile (test, _) ->
              type_check (ASTStatement stmt) Int test
          | For (_, test, inc, _) ->
              Option.iter ~f:(type_check (ASTStatement stmt) Int) test;
              Option.iter ~f:check_not_array inc
          | Goto _ -> ()
          | Continue -> ()
          | Break -> ()
          | Switch (expr, _) | Case expr -> (
              maybe_deref expr;
              match expr.ty with
              | String -> ()
              | _ -> type_check (ASTStatement stmt) Int expr)
          | Default -> ()
          | Return (Some e) -> (
              match self#env#current_function with
              | None ->
                  compiler_bug "return statement outside of function"
                    (Some (ASTStatement stmt))
              | Some f -> (
                  if f.is_label then
                    compile_error "cannot return from scenario function"
                      (ASTStatement stmt);
                  match f.return.ty with
                  | Ref ty ->
                      check_referenceable e (ASTExpression e);
                      ref_type_check (ASTStatement stmt) ty e
                  | _ ->
                      check_funarg_or_return ctx (ASTStatement stmt) f.return.ty
                        e))
          | Return None -> (
              match self#env#current_function with
              | None ->
                  compiler_bug "return statement outside of function"
                    (Some (ASTStatement stmt))
              | Some f -> (
                  if f.is_label then
                    compile_error "cannot return from scenario function"
                      (ASTStatement stmt);
                  match f.return.ty with
                  | Void -> ()
                  | _ -> type_error f.return.ty None (ASTStatement stmt)))
          | Jump name -> (
              match find_function ctx name with
              | Some f when f.is_label -> ()
              | _ ->
                  compile_error
                    (name ^ " is not a scenario function")
                    (ASTStatement stmt))
          | Jumps e -> type_check (ASTExpression e) String e
          | Message _ -> ()
          | RefAssign (lhs, rhs) -> check_ref_assign (ASTStatement stmt) lhs rhs
          | ObjSwap (lhs, rhs) ->
              check_lvalue lhs (ASTStatement stmt);
              check_lvalue rhs (ASTStatement stmt);
              (* FIXME: error if the type is ref or unsupported type *)
              type_check (ASTStatement stmt) lhs.ty rhs)

    method! visit_variable var =
      super#visit_variable var;
      let nr_dims = List.length var.array_dim in
      (* Check that there is no initializer if array has explicit dimensions *)
      if nr_dims > 0 && Option.is_some var.initval then
        compile_error "Initializer provided for array with explicit dimensions"
          (ASTVariable var);
      (* Check that number of dims matches rank of array *)
      if nr_dims > 0 && not (nr_dims = array_rank var.type_spec.ty) then
        compile_error "Number of array dimensions does not match array rank"
          (ASTVariable var);
      (* Check that array dims are integers *)
      List.iter var.array_dim ~f:(fun e -> type_check (ASTVariable var) Int e);
      (* Check initval matches declared type *)
      match var.initval with
      | Some expr -> (
          match var.type_spec.ty with
          | Ref ty ->
              check_referenceable expr (ASTVariable var);
              maybe_deref expr;
              ref_type_check (ASTVariable var) ty expr
          | t -> check_assign ctx (ASTVariable var) t expr)
      | None -> ()

    method! visit_declaration decl =
      self#catch_errors (fun () ->
          (match decl with
          | FuncTypeDef _ when Ain.version_gte ctx.ain (6, 20) ->
              compile_error
                "functype is not supported in AIN version 6.20 or later"
                (ASTDeclaration decl)
          | DelegateDef _ when Ain.version_lt ctx.ain (6, 10) ->
              compile_error "delegate requires AIN version 6.10 or later"
                (ASTDeclaration decl)
          | _ -> ());
          super#visit_declaration decl)

    method! visit_fundecl f =
      super#visit_fundecl f;
      if String.equal f.name "main" then
        match (f.return.ty, f.params) with
        | Int, [] -> ()
        | _ ->
            compile_error "Invalid declaration of 'main' function"
              (ASTDeclaration (Function f))
      else if String.equal f.name "message" then
        match f.return.ty with
        | Void -> (
            match List.map f.params ~f:(fun v -> v.type_spec.ty) with
            | [ Int; Int; String ] -> ()
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
  visitor#errors

let check_types_exn ctx decls =
  let errors = check_types ctx decls in
  if not (List.is_empty errors) then raise_list errors
