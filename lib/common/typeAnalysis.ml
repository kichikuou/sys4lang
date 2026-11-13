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
open NameResolution

let sprintf = Printf.sprintf

class type_analyze_visitor ctx =
  object (self)
    inherit ivisitor as super
    val mutable errors : compile_error list = []
    method errors = List.rev errors

    method catch_errors f =
      try f () with Compile_error e -> errors <- e :: errors

    (* Makes [expr] the access to the member [m] of [obj]. *)
    method private set_member (expr : expression) obj name m =
      match m with
      | MemberVar v ->
          expr.node <-
            Member
              (obj, name, if v.is_const then ClassConst v else ClassVariable v);
          expr.ty <- v.type_spec.ty
      | MemberFunctions fs ->
          let f = List.hd_exn fs in
          expr.node <- Member (obj, name, ClassMethod f);
          expr.ty <- TyMethod (ft_of_fundecl f)

    (* Checks the arguments of a call of the function [name], and returns
       them with the default values of the omitted arguments. *)
    method private check_arguments (expr : expression) name params args =
      let node = ASTExpression expr in
      let nr_params = List.length params in
      let nr_args = List.length args in
      if nr_args > nr_params then arity_error name nr_params args node;
      let check_arg i a v =
        match (a, v.initval) with
        | Some a, _ ->
            (match v.type_spec.ty with
            | Ref ty ->
                check_referenceable a (ASTExpression a);
                ref_type_check (ASTExpression a) ty a
            | _ -> check_funarg_or_return ctx (ASTExpression a) v.type_spec.ty a);
            Some a
        | None, Some e ->
            (* NOTE: `e` may be from another file that has not yet been type-checked. *)
            Some e
        | None, None ->
            if i < nr_args then
              compile_error (sprintf "Missing argument #%d" i) node
            else arity_error name nr_params args node
      in
      let args = args @ List.init (nr_params - nr_args) ~f:(fun _ -> None) in
      List.map3_exn
        (List.init nr_params ~f:(fun i -> i))
        args params ~f:check_arg

    method private type_ident (expr : expression) name =
      match resolve ctx self#env name with
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
      | ResolvedMember (s, m) ->
          let this = make_expr ~ty:(Struct (s.name, s.index)) This in
          self#set_member expr this name m
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

    method private type_func_addr (expr : expression) name =
      match find_function ctx name with
      | Some f ->
          expr.node <- FuncAddr (name, Some f);
          expr.ty <- TyFunction (ft_of_fundecl f)
      | None -> (
          match Util.parse_qualified_name name with
          | None, name -> undefined_variable_error name (ASTExpression expr)
          | Some sname, name -> (
              match
                Option.bind (Hashtbl.find ctx.structs sname) ~f:(fun s ->
                    find_member ctx s name)
              with
              | Some (MemberVar v) ->
                  expr.node <- MemberAddr (sname, v);
                  expr.ty <- MemberPtr (sname, v.type_spec.ty)
              | Some (MemberFunctions _) | None ->
                  undefined_variable_error
                    (sname ^ "::" ^ name)
                    (ASTExpression expr)))

    method private type_unary (expr : expression) op (e : expression) =
      match op with
      | UPlus | UMinus | PreInc | PreDec | PostInc | PostDec ->
          type_check_numeric (ASTExpression expr) e;
          expr.ty <- e.ty
      | LogNot | BitNot ->
          type_check (ASTExpression expr) Int e;
          expr.ty <- Int

    method private type_binary (expr : expression) op (a : expression)
        (b : expression) =
      let node = ASTExpression expr in
      let check = type_check node in
      let coerce_numerics = type_coerce_numerics node in
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
              | _ -> type_error Int (Some b) node)
          | Int | Bool | LongInt -> check Int b
          | _ -> type_error Int (Some a) node);
          expr.ty <- a.ty
      | Equal | NEqual ->
          maybe_deref a;
          maybe_deref b;
          (* NOTE: NULL is not allowed on lhs *)
          (match (a.ty, b.ty) with
          | String, _ -> check String b
          | FuncType (Some (_, ft_i)), FuncType (Some (_, ft_j)) ->
              if ft_i <> ft_j then type_error a.ty (Some b) node
          | FuncType (Some (ft_name, _)), TyFunction f ->
              let ft = Hashtbl.find_exn ctx.functypes ft_name in
              if not (ft_compatible (ft_of_fundecl ft) f) then
                type_error a.ty (Some b) node
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
              check_ref_assign node a b
          | This -> not_an_lvalue_error a node
          | _ -> (
              check_referenceable b node;
              match a.ty with
              | Ref t -> ref_type_check node t b
              | _ -> not_an_lvalue_error a node));
          expr.ty <- Int

    method private type_assign (expr : expression) op (lhs : expression)
        (rhs : expression) =
      let node = ASTExpression expr in
      let check = type_check node in
      check_lvalue lhs node;
      maybe_deref lhs;
      maybe_deref rhs;
      (match (lhs.ty, op) with
      | _, EqAssign -> (
          check_assign ctx node lhs.ty rhs;
          (* If lhs is a string subscript access, change the operator to CharAssign *)
          match lhs.node with
          | Subscript ({ ty = String; _ }, _) ->
              expr.node <- Assign (CharAssign, lhs, rhs)
          | _ -> ())
      | String, PlusAssign -> check String rhs
      | Delegate dg, (PlusAssign | MinusAssign) ->
          check_delegate_compatible ctx node dg rhs
      | _, (PlusAssign | MinusAssign | TimesAssign | DivideAssign) ->
          type_check_numeric node lhs;
          type_check_numeric node rhs;
          insert_cast lhs.ty rhs;
          check lhs.ty rhs
      | ( _,
          ( ModuloAssign | OrAssign | XorAssign | AndAssign | LShiftAssign
          | RShiftAssign ) ) ->
          check Int lhs;
          check Int rhs
      | _, CharAssign -> compiler_bug "unexpected CharAssign" (Some node));
      (* XXX: Nothing is left on stack after assigning method to delegate *)
      match (lhs.ty, rhs.ty) with
      | Delegate _, (TyMethod _ | String) -> expr.ty <- Void
      | _ -> expr.ty <- rhs.ty

    method private type_member (expr : expression) (obj : expression) name =
      let node = ASTExpression expr in
      match obj.node with
      (* system function *)
      | Ident (_, System) -> (
          match Bytecode.syscall_of_string name with
          | Some sys ->
              expr.node <- Member (obj, name, SystemFunction sys);
              expr.ty <- TyFunction ([], Void)
          | None ->
              (* TODO: separate error type for this? *)
              undefined_variable_error ("system." ^ name) node)
      (* HLL function *)
      | Ident (lib_name, HLLName lib) -> (
          match find_hll_function lib name with
          | Some _ ->
              expr.node <- Member (obj, name, HLLFunction (lib, name));
              expr.ty <- TyFunction ([], Void)
          | None ->
              (* TODO: separate error type for this? *)
              undefined_variable_error (lib_name ^ "." ^ name) node)
      (* built-in methods *)
      | _ when is_builtin obj.ty -> (
          match resolve_builtin ctx obj name with
          | Some builtin ->
              expr.node <- Member (obj, name, builtin);
              expr.ty <- TyFunction ([], Void)
          | None ->
              (* TODO: separate error type for this? *)
              undefined_variable_error name node)
      (* member variable OR method *)
      | _ -> (
          let struc =
            Hashtbl.find_exn ctx.structs (type_check_member_lhs node obj)
          in
          let access_check () =
            match self#env#current_class with
            | Some (Struct (_, i)) when i = struc.index -> ()
            | _ ->
                compile_error
                  (sprintf "%s::%s is not public" struc.name name)
                  node
          in
          match find_member ctx struc name with
          | Some m ->
              let is_private =
                match m with
                | MemberVar v -> v.is_private
                | MemberFunctions fs -> (List.hd_exn fs).is_private
              in
              if is_private then access_check ();
              self#set_member expr obj name m
          | None ->
              (* TODO: separate error type for this? *)
              undefined_variable_error (struc.name ^ "." ^ name) node)

    method private type_call (expr : expression) (e : expression) args =
      let node = ASTExpression expr in
      let set_call (f : fundecl) params call_type =
        let args = self#check_arguments expr f.name params args in
        (args, call_type, f.return.ty)
      in
      let args, call_type, ty =
        match e.node with
        (* regular function call *)
        | Ident (_, FunctionName name) ->
            let f = Option.value_exn (find_function ctx name) in
            set_call f f.params (FunctionCall f)
        (* built-in function call *)
        | Ident (_, BuiltinFunction builtin) ->
            let f = Builtin.fundecl_of_builtin ctx builtin Void (Some node) in
            set_call f f.params (BuiltinCall builtin)
        (* method call *)
        | Member (_, _, ClassMethod f) -> set_call f f.params (MethodCall f)
        (* HLL call *)
        | Member (_, _, HLLFunction (lib, fun_name)) ->
            let f = Option.value_exn (find_hll_function lib fun_name) in
            set_call f f.params (HLLCall (lib, f))
        (* system call *)
        | Member (_, _, SystemFunction sys) ->
            let f = Builtin.fundecl_of_syscall sys in
            set_call f f.params (SystemCall sys)
        (* built-in method call *)
        | Member (obj, _, BuiltinMethod builtin) ->
            let f = Builtin.fundecl_of_builtin ctx builtin obj.ty (Some node) in
            set_call f f.params (BuiltinCall builtin)
        (* built-in method call via HLL *)
        | Member (obj, fun_name, BuiltinHLL lib) ->
            let f = Option.value_exn (find_hll_function lib fun_name) in
            let args, call_type, ty =
              set_call f (List.tl_exn f.params) (HLLCall (lib, f))
            in
            insert_rvalue_ref obj;
            (Some obj :: args, call_type, ty)
        (* functype/delegate call *)
        | _ -> (
            match e.ty with
            | FuncType (Some (name, _)) ->
                let f = Hashtbl.find_exn ctx.functypes name in
                set_call f f.params (FuncTypeCall f)
            | Delegate (Some (name, _)) ->
                let f = Hashtbl.find_exn ctx.delegates name in
                set_call f f.params (DelegateCall f)
            | _ -> type_error (FuncType None) (Some e) node)
      in
      expr.node <- Call (e, args, call_type);
      expr.ty <- ty

    method! visit_expression expr =
      super#visit_expression expr;
      let node = ASTExpression expr in
      match expr.node with
      | ConstInt _ -> expr.ty <- Int
      | ConstFloat _ -> expr.ty <- Float
      | ConstChar _ -> expr.ty <- Int
      | ConstString _ -> expr.ty <- String
      | Ident (name, _) -> self#type_ident expr name
      | FuncAddr (name, _) -> self#type_func_addr expr name
      | MemberAddr _ -> compiler_bug "unexpected MemberAddr" (Some node)
      | Unary (op, e) -> self#type_unary expr op e
      | Binary (op, a, b) -> self#type_binary expr op a b
      | Assign (op, lhs, rhs) -> self#type_assign expr op lhs rhs
      | Seq (e1, e2) ->
          check_not_array e1;
          expr.ty <- e2.ty
      | Ternary (test, con, alt) ->
          type_check node Int test;
          (match (con.ty, alt.ty) with
          | Ref _, Ref _ -> ()
          | Ref _, _ -> maybe_deref con
          | _, Ref _ -> maybe_deref alt
          | _, _ -> ());
          type_check node con.ty alt;
          expr.ty <- con.ty
      | Cast (t, e) ->
          maybe_deref e;
          if not (type_castable t e.ty) then type_error t (Some e) node;
          expr.ty <- t
      | Subscript (obj, i) -> (
          maybe_deref obj;
          type_check node Int i;
          match obj.ty with
          | Array t -> expr.ty <- t
          | String -> expr.ty <- Int
          | _ ->
              (* FIXME: Expected type here is array<?>|string *)
              let expected = Array Void in
              type_error expected (Some obj) node)
      | Member (obj, name, _) -> self#type_member expr obj name
      | Call (e, args, _) -> self#type_call expr e args
      | New { ty; _ } -> (
          match ty with
          | Struct _ -> expr.ty <- Ref ty
          | _ -> type_error (Struct ("", -1)) None node)
      | DummyRef _ -> compiler_bug "DummyRef in type checker" (Some node)
      | RvalueRef _ -> compiler_bug "RvalueRef in type checker" (Some node)
      | This -> (
          match self#env#current_class with
          | Some ty -> expr.ty <- ty
          | None ->
              (* TODO: separate error type for this? *)
              undefined_variable_error "this" node)
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
