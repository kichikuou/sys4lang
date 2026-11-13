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
open Bytecode
open CompileError

let is_variable_ref = function
  | Ident _ | Member (_, _, ClassVariable _) | Subscript _ -> true
  | _ -> false

let var_index (v : variable) = Option.value_exn v.index
let fun_index (f : fundecl) = Option.value_exn f.index

let incdec_instruction op ty =
  match Opcodes.incdec op ty with
  | Some instruction -> instruction
  | None -> compiler_bug "invalid inc/dec expression" None

class jaf_compiler ctx debug_info =
  object (self)
    inherit CodeWriter.code_writer ctx debug_info

    method compile_lock_peek =
      if Ain.version_lt ctx.ain (6, 0) then (
        self#write_instruction1 CALLSYS (int_of_syscall LockPeek);
        self#write_instruction0 POP)

    method compile_unlock_peek =
      if Ain.version_lt ctx.ain (6, 0) then (
        self#write_instruction1 CALLSYS (int_of_syscall UnlockPeek);
        self#write_instruction0 POP)

    method compile_delete_var (v : variable) =
      match v.type_spec.ty with
      | Ref _ | Struct _ -> self#write_instruction1 SH_LOCALDELETE (var_index v)
      | Array _ ->
          self#compile_local_ref (var_index v);
          self#write_instruction0 A_FREE
      | _ -> ()

    (** Emit the code to put the value of a variable onto the stack (including
        member variables and array elements). Assumes a page + page-index is
        already on the stack. *)
    method compile_dereference (t : jaf_type) =
      match t with
      | Ref (Int | Float | Bool | LongInt | FuncType _) ->
          self#write_instruction0 REFREF;
          self#write_instruction0 REF
      | Int | Float | Bool | LongInt | FuncType _ -> self#write_instruction0 REF
      | String | Ref String -> self#write_instruction0 S_REF
      | Array _ | Ref (Array _) ->
          self#write_instruction0 REF;
          (* ain v0/v1 has no A_REF; array rvalues are passed by reference
             without a deep copy. *)
          if ctx.version > 100 then self#write_instruction0 A_REF
      | Struct (_, no) | Ref (Struct (_, no)) ->
          self#write_instruction1 SR_REF no
      | Delegate _ | Ref (Delegate _) ->
          self#write_instruction0 REF;
          self#write_instruction0 DG_COPY
      | _ -> compiler_bug "dereference not supported for type" None

    method compile_local_ref i =
      self#write_instruction0 PUSHLOCALPAGE;
      self#write_instruction1 PUSH i

    method compile_global_ref i =
      self#write_instruction0 PUSHGLOBALPAGE;
      self#write_instruction1 PUSH i

    method compile_identifier_ref id_type =
      match id_type with
      | LocalVariable v -> self#compile_local_ref (var_index v)
      | GlobalVariable v -> self#compile_global_ref (var_index v)
      | _ -> compiler_bug "Invalid identifier type" None

    method compile_variable_ref (e : expression) =
      match e.node with
      | Ident (_, id_type) -> self#compile_identifier_ref id_type
      | Member (e, _, ClassVariable v) ->
          self#compile_lvalue e;
          self#write_instruction1 PUSH (var_index v)
      | Subscript (obj, index) ->
          self#compile_lvalue obj;
          self#compile_expression index
      | _ -> compiler_bug "Invalid variable ref" (Some (ASTExpression e))

    method compile_delete_ref ty =
      self#write_instruction0 DUP2;
      if is_ref_scalar ty then (
        self#write_instruction0 REFREF;
        self#write_instruction0 POP)
      else self#write_instruction0 REF;
      self#write_instruction0 DELETE

    (** Emit the code to put a location (variable, struct member, or array
        element) onto the stack, e.g. to prepare for an assignment or to pass a
        variable by reference. *)
    method compile_lvalue (e : expression) =
      let compile_lvalue_after (t : jaf_type) =
        match t with
        | Ref (Int | Float | Bool | LongInt) -> self#write_instruction0 REFREF
        | Ref (String | Array _ | Struct _ | Delegate _) ->
            self#write_instruction0 REF
        | String | Array _ | Struct _ | Delegate _ ->
            self#write_instruction0 REF
        | _ -> ()
      in
      match e.node with
      | Ident (_, LocalVariable v) -> (
          match v.type_spec.ty with
          | String | Array _ | Struct _
          | Ref (String | Array _ | Struct _ | Delegate _)
            when ctx.version < 630 ->
              self#write_instruction1 SH_LOCALREF (var_index v)
          | t ->
              self#compile_local_ref (var_index v);
              compile_lvalue_after t)
      | Ident (_, GlobalVariable v) -> (
          match v.type_spec.ty with
          | String | Array _ | Struct _
          | Ref (String | Array _ | Struct _ | Delegate _)
            when ctx.version < 630 ->
              self#write_instruction1 SH_GLOBALREF (var_index v)
          | t ->
              self#compile_global_ref (var_index v);
              compile_lvalue_after t)
      | Member (obj, _, ClassVariable v) -> (
          match (obj.node, e.ty) with
          | ( This,
              ( Ref (String | Array _ | Struct _ | Delegate _)
              | String | Array _ | Struct _ | Delegate _ ) )
            when ctx.version < 630 ->
              self#write_instruction1 SH_STRUCTREF (var_index v)
          | _ ->
              self#compile_lvalue obj;
              self#write_instruction1 PUSH (var_index v);
              compile_lvalue_after v.type_spec.ty)
      | Subscript (obj, index) ->
          self#compile_lvalue obj;
          self#compile_expression index;
          compile_lvalue_after e.ty
      | New _ -> compiler_bug "bare new expression" (Some (ASTExpression e))
      | DummyRef (v, ref_expr) -> (
          self#scope_add_var v;
          (* prepare for assign to dummy variable *)
          self#write_instruction0 PUSHLOCALPAGE;
          self#write_instruction1 PUSH (var_index v);
          match ref_expr with
          | { node = New { ty = Struct (_, s_no); _ }; _ } ->
              self#write_instruction1 PUSH s_no;
              self#compile_lock_peek;
              self#write_instruction0 NEW;
              (* assign to dummy variable *)
              self#write_instruction0 ASSIGN;
              self#compile_unlock_peek
          | _ ->
              self#compile_expression ref_expr;
              self#write_instruction0
                (if is_ref_scalar ref_expr.ty then R_ASSIGN else ASSIGN))
      | RvalueRef e ->
          (* TODO: Insert <dummy : 右辺値参照化用> variable *)
          self#compile_expression e
      | This -> self#write_instruction0 PUSHSTRUCTPAGE
      | Null -> (
          match e.ty with
          | Ref t ->
              self#write_instruction1 PUSH (-1);
              if is_numeric t then self#write_instruction1 PUSH 0
          | ty ->
              compiler_bug
                ("unimplemented: NULL lvalue of type " ^ jaf_type_to_string ty)
                (Some (ASTExpression e)))
      | Ternary (test, con, alt) ->
          self#compile_expression test;
          let ifz_addr = current_address + 2 in
          self#write_instruction1 IFZ 0;
          self#compile_lvalue con;
          let jump_addr = current_address + 2 in
          self#write_instruction1 JUMP 0;
          self#write_address_at ifz_addr current_address;
          self#compile_lvalue alt;
          self#write_address_at jump_addr current_address
      | Seq (a, b) ->
          self#compile_expr_and_pop a;
          self#compile_lvalue b
      | _ ->
          compiler_bug
            ("invalid lvalue: " ^ expr_to_string e)
            (Some (ASTExpression e))

    (** Emit the code to pop a value off the stack. *)
    method compile_pop (t : jaf_type) parent =
      match t with
      | Void -> ()
      | Int | Float | Bool | LongInt | FuncType _ | Ref _ | TyFunction _
      | TyMethod _ ->
          self#write_instruction0 POP
      | String -> self#write_instruction0 S_POP
      | Delegate _ -> self#write_instruction0 DG_POP
      | Struct _ -> self#write_instruction0 SR_POP
      | IMainSystem | HLLParam | Array _ | Wrap _ | HLLFunc | NullType | Untyped
      | Unresolved _ | MemberPtr _ | TypeUnion _ ->
          compiler_bug
            ("compile_pop: unsupported value type " ^ jaf_type_to_string t)
            (Some parent)

    method compile_argument (expr : expression option) (t : jaf_type) =
      match expr with
      | None -> compiler_bug "missing argument" None
      | Some expr -> (
          match t with
          | Ref _ -> self#compile_lvalue expr
          | TyMethod _ ->
              (* XXX: for delegate builtins *)
              self#compile_expression expr
          | Delegate _ -> (
              self#compile_expression expr;
              match expr.ty with
              | TyMethod _ -> self#write_instruction0 DG_NEW_FROM_METHOD
              | _ -> ())
          | _ -> self#compile_expression expr)

    method compile_function_arguments args (f : fundecl) =
      List.iter2_exn args f.params ~f:(fun arg (param : variable) ->
          self#compile_argument arg param.type_spec.ty)

    (** Emit the code to call a method. The object upon which the method is to
        be called should already be on the stack before this code is executed.
    *)
    method compile_method_call args (f : fundecl) =
      self#compile_function_arguments args f;
      self#write_instruction1 CALLMETHOD (fun_index f)

    (** Emit the code to compute an expression. Computing an expression produces
        a value (of the expression's value type) on the stack. *)
    method compile_expression (expr : expression) =
      match expr.node with
      | ConstInt i -> self#write_instruction1 PUSH i
      | ConstFloat f -> self#write_instruction1_float F_PUSH f
      | ConstChar s -> (
          match Sjis.char_code s with
          | Some c -> self#write_instruction1 PUSH c
          | None ->
              compile_error "Invalid character constant" (ASTExpression expr))
      | ConstString s ->
          let no =
            if Ain.version_lt ctx.ain (1, 0) then self#add_message s
            else self#add_string s
          in
          self#write_instruction1 S_PUSH no
      | Ident (_, LocalVariable v) -> (
          match v.type_spec.ty with
          | (Int | Float | Bool | LongInt | FuncType _) when ctx.version < 630
            ->
              self#write_instruction1 SH_LOCALREF (var_index v)
          | t ->
              self#write_instruction0 PUSHLOCALPAGE;
              self#write_instruction1 PUSH (var_index v);
              self#compile_dereference t)
      | FuncAddr (_, Some f) -> self#write_instruction1 PUSH (fun_index f)
      | FuncAddr (_, None) ->
          compiler_bug "unresolved FuncAddr" (Some (ASTExpression expr))
      | MemberAddr (_, v) -> self#write_instruction1 PUSH (var_index v)
      | Ident (_, GlobalVariable v) -> (
          match v.type_spec.ty with
          | (Int | Float | Bool | LongInt | FuncType _) when ctx.version < 630
            ->
              self#write_instruction1 SH_GLOBALREF (var_index v)
          | t ->
              self#write_instruction0 PUSHGLOBALPAGE;
              self#write_instruction1 PUSH (var_index v);
              self#compile_dereference t)
      | Ident (_, GlobalConstant _) ->
          compiler_bug "global constant not eliminated"
            (Some (ASTExpression expr))
      | Ident (_, FunctionName _) ->
          compiler_bug "tried to compile function identifier"
            (Some (ASTExpression expr))
      | Ident (_, HLLName _) ->
          compiler_bug "tried to compile HLL identifier"
            (Some (ASTExpression expr))
      | Ident (_, System) ->
          compiler_bug "tried to compile system identifier"
            (Some (ASTExpression expr))
      | Ident (_, BuiltinFunction _) ->
          compiler_bug "tried to compile built-in function identifier"
            (Some (ASTExpression expr))
      | Ident (_, UnresolvedIdent) ->
          compiler_bug "identifier type is none" (Some (ASTExpression expr))
      | Unary (UPlus, e) -> self#compile_expression e
      | Unary (UMinus, e) ->
          self#compile_expression e;
          self#write_instruction0 (Opcodes.negate e.ty)
      | Unary (LogNot, e) ->
          self#compile_expression e;
          self#write_instruction0 NOT
      | Unary (BitNot, e) ->
          self#compile_expression e;
          self#write_instruction0 COMPL
      | Unary (((PreInc | PreDec) as op), e) ->
          self#compile_lvalue e;
          self#write_instruction0 DUP2;
          self#write_instruction0 (incdec_instruction op e.ty);
          self#write_instruction0 REF
      | Unary (((PostInc | PostDec) as op), e) ->
          self#compile_lvalue e;
          self#write_instruction0 DUP2;
          self#write_instruction0 REF;
          self#write_instruction0 DUP_X2;
          self#write_instruction0 POP;
          self#write_instruction0 (incdec_instruction op e.ty)
      | Binary (LogOr, a, b) ->
          self#compile_expression a;
          let lhs_true_addr = current_address + 2 in
          self#write_instruction1 IFNZ 0;
          self#compile_expression b;
          let rhs_true_addr = current_address + 2 in
          self#write_instruction1 IFNZ 0;
          self#write_instruction1 PUSH 0;
          let false_addr = current_address + 2 in
          self#write_instruction1 JUMP 0;
          self#write_address_at lhs_true_addr current_address;
          self#write_address_at rhs_true_addr current_address;
          self#write_instruction1 PUSH 1;
          self#write_address_at false_addr current_address
      | Binary (LogAnd, a, b) ->
          self#compile_expression a;
          let lhs_false_addr = current_address + 2 in
          self#write_instruction1 IFZ 0;
          self#compile_expression b;
          let rhs_false_addr = current_address + 2 in
          self#write_instruction1 IFZ 0;
          self#write_instruction1 PUSH 1;
          let true_addr = current_address + 2 in
          self#write_instruction1 JUMP 0;
          self#write_address_at lhs_false_addr current_address;
          self#write_address_at rhs_false_addr current_address;
          self#write_instruction1 PUSH 0;
          self#write_address_at true_addr current_address
      | Binary (op, a, b) -> (
          (match op with
          | RefEqual | RefNEqual ->
              self#compile_lvalue a;
              self#compile_lvalue b
          | _ ->
              self#compile_expression a;
              self#compile_expression b);
          match (Opcodes.binary a.ty op, a.ty, op) with
          | Some instruction, _, _ -> self#write_instruction0 instruction
          | None, String, Modulo -> (
              match Opcodes.string_format_type b.ty with
              | Some t -> self#write_instruction1 S_MOD t
              | None ->
                  compiler_bug "invalid type for string formatting"
                    (Some (ASTExpression expr)))
          | None, _, _ ->
              compiler_bug "invalid binary expression"
                (Some (ASTExpression expr)))
      | Assign (op, lhs, rhs) -> (
          self#compile_lvalue lhs;
          self#compile_expression rhs;
          match (Opcodes.assign op rhs.ty, op, rhs.ty) with
          | Some instruction, _, _ -> self#write_instruction0 instruction
          | None, EqAssign, String -> (
              match lhs.ty with
              | FuncType (Some (_, ft_i)) ->
                  self#write_instruction1 PUSH ft_i;
                  self#write_instruction0 FT_ASSIGNS
              | Delegate (Some (_, dg_i)) ->
                  self#write_instruction1 PUSH (-1);
                  self#write_instruction0 SWAP;
                  self#write_instruction1 PUSH dg_i;
                  self#write_instruction0 DG_STR_TO_METHOD;
                  self#write_instruction0 DG_SET
              | String -> self#write_instruction0 S_ASSIGN
              | _ ->
                  compiler_bug "invalid string assignment"
                    (Some (ASTExpression expr)))
          | None, PlusAssign, String -> (
              match lhs.ty with
              | Delegate (Some (_, dg_i)) ->
                  self#write_instruction1 PUSH (-1);
                  self#write_instruction0 SWAP;
                  self#write_instruction1 PUSH dg_i;
                  self#write_instruction0 DG_STR_TO_METHOD;
                  self#write_instruction0 DG_ADD
              | String ->
                  self#write_instruction0
                    (if ctx.version <= 100 then S_PLUSA else S_PLUSA2)
              | _ ->
                  compiler_bug "invalid string assignment"
                    (Some (ASTExpression expr)))
          | None, EqAssign, TyMethod _ -> self#write_instruction0 DG_SET
          | None, EqAssign, Delegate _ -> self#write_instruction0 DG_ASSIGN
          | None, PlusAssign, TyMethod _ -> self#write_instruction0 DG_ADD
          | None, PlusAssign, Delegate _ -> self#write_instruction0 DG_PLUSA
          | None, MinusAssign, TyMethod _ -> self#write_instruction0 DG_ERASE
          | None, MinusAssign, Delegate _ -> self#write_instruction0 DG_MINUSA
          | None, EqAssign, (Struct (_, sno) | Ref (Struct (_, sno))) ->
              if not (Ain.version ctx.ain <= 1 || Ain.version ctx.ain >= 11)
              then self#write_instruction1 PUSH sno;
              self#write_instruction0 SR_ASSIGN
          | None, _, _ ->
              compiler_bug "invalid assignment" (Some (ASTExpression expr)))
      | Seq (a, b) ->
          self#compile_expr_and_pop a;
          self#compile_expression b
      | Ternary (test, con, alt) ->
          self#compile_expression test;
          let ifz_addr = current_address + 2 in
          self#write_instruction1 IFZ 0;
          self#compile_expression con;
          let jump_addr = current_address + 2 in
          self#write_instruction1 JUMP 0;
          self#write_address_at ifz_addr current_address;
          self#compile_expression alt;
          self#write_address_at jump_addr current_address
      | Cast (dst_t, e) -> (
          let src_t = e.ty in
          self#compile_expression e;
          match (src_t, dst_t) with
          | Int, Int -> ()
          | LongInt, LongInt -> ()
          | (Int | LongInt), Bool -> self#write_instruction0 ITOB
          | (Int | LongInt), Float -> self#write_instruction0 ITOF
          | (Bool | Int), LongInt -> self#write_instruction0 ITOLI
          | LongInt, Int -> ()
          | (Bool | Int | LongInt), String -> self#write_instruction0 I_STRING
          | Bool, (Bool | Int) -> ()
          | Float, Float -> ()
          | Float, Int -> self#write_instruction0 FTOI
          | Float, LongInt ->
              self#write_instruction0 FTOI;
              self#write_instruction0 ITOLI
          | Float, String ->
              self#write_instruction1 PUSH (-1);
              self#write_instruction0 FTOS
          | String, String -> ()
          | String, Int -> self#write_instruction0 STOI
          | String, Delegate (Some (_, dg_i)) ->
              self#write_instruction1 PUSH (-1);
              self#write_instruction0 SWAP;
              self#write_instruction1 PUSH dg_i;
              self#write_instruction0 DG_STR_TO_METHOD
          | TyFunction _, TyMethod _ ->
              self#write_instruction1 PUSH (-1);
              self#write_instruction0 SWAP
          | _ ->
              compiler_bug
                (Printf.sprintf "invalid cast from %s to %s"
                   (jaf_type_to_string src_t) (jaf_type_to_string dst_t))
                (Some (ASTExpression expr)))
      | Subscript (obj, index) -> (
          self#compile_lvalue obj;
          self#compile_expression index;
          match obj.ty with
          | String -> self#write_instruction0 C_REF
          | _ -> self#compile_dereference expr.ty)
      | Member ({ node = This; _ }, _, ClassVariable v)
        when ctx.version < 630 && is_scalar v.type_spec.ty ->
          self#write_instruction1 SH_STRUCTREF (var_index v)
      | Member (e, _, ClassVariable v) ->
          self#compile_lvalue e;
          self#write_instruction1 PUSH (var_index v);
          self#compile_dereference v.type_spec.ty
      | Member (_, _, ClassConst _) ->
          compiler_bug "class constant not eliminated"
            (Some (ASTExpression expr))
      | Member (e, _, ClassMethod f) ->
          self#compile_lvalue e;
          self#write_instruction1 PUSH (fun_index f)
      | Member (_, _, HLLFunction (_, _)) ->
          compiler_bug "tried to compile HLL member expression"
            (Some (ASTExpression expr))
      | Member (_, _, SystemFunction _) ->
          compiler_bug "tried to compile system call member expression"
            (Some (ASTExpression expr))
      | Member (_, _, (BuiltinMethod _ | BuiltinHLL _)) ->
          compiler_bug "tried to compile built-in method member expression"
            (Some (ASTExpression expr))
      | Member (_, _, UnresolvedMember) ->
          compiler_bug "member expression has no member_type"
            (Some (ASTExpression expr))
      (* regular function call *)
      | Call (_, args, FunctionCall f) ->
          self#compile_function_arguments args f;
          self#write_instruction1 CALLFUNC (fun_index f)
      (* method call *)
      | Call ({ node = Member (e, _, _); _ }, args, MethodCall f) ->
          self#compile_lvalue e;
          self#compile_method_call args f
      (* HLL function call *)
      | Call (_, args, HLLCall (lib, f)) ->
          self#compile_function_arguments args f;
          self#write_instruction2 CALLHLL
            (Option.value_exn lib.index)
            (fun_index f)
      (* system call *)
      | Call (_, args, SystemCall sys) ->
          self#compile_function_arguments args (Builtin.fundecl_of_syscall sys);
          self#write_instruction1 CALLSYS (int_of_syscall sys)
      (* built-in method call *)
      | Call ({ node = Member (e, _, _); _ }, args, BuiltinCall builtin) -> (
          let receiver_ty = ref Void in
          (match builtin with
          | (StringLength | StringLengthByte) when is_variable_ref e.node ->
              self#compile_variable_ref e
          | IntString | FloatString | StringInt | StringLength
          | StringLengthByte | StringEmpty | StringFind | StringGetPart ->
              self#compile_expression e
          | StringPushBack | StringPopBack | StringErase | DelegateNumof
          | DelegateExist | DelegateErase | DelegateClear ->
              receiver_ty := e.ty;
              self#compile_lvalue e
          | ArrayAlloc | ArrayRealloc | ArrayFree | ArrayNumof | ArrayCopy
          | ArrayFill | ArrayPushBack | ArrayPopBack | ArrayEmpty | ArrayErase
          | ArrayInsert | ArraySort | ArraySortBy | ArrayReverse | ArrayFind ->
              receiver_ty := e.ty;
              self#compile_variable_ref e
          | Assert ->
              compiler_bug "invalid assert expression"
                (Some (ASTExpression expr)));
          let f = Builtin.fundecl_of_builtin ctx builtin !receiver_ty None in
          self#compile_function_arguments args f;
          match builtin with
          | IntString -> self#write_instruction0 I_STRING
          | FloatString -> self#write_instruction0 FTOS
          | StringInt -> self#write_instruction0 STOI
          | StringLength ->
              self#write_instruction0
                (if is_variable_ref e.node then S_LENGTH else S_LENGTH2)
          | StringLengthByte ->
              self#write_instruction0
                (if is_variable_ref e.node then S_LENGTHBYTE else S_LENGTHBYTE2)
          | StringEmpty -> self#write_instruction0 S_EMPTY
          | StringFind -> self#write_instruction0 S_FIND
          | StringGetPart -> self#write_instruction0 S_GETPART
          | StringPushBack -> self#write_instruction0 S_PUSHBACK2
          | StringPopBack -> self#write_instruction0 S_POPBACK2
          | StringErase ->
              self#write_instruction1 PUSH 1;
              self#write_instruction0 S_ERASE2
          | ArrayAlloc ->
              self#write_instruction1 PUSH (List.length args);
              self#write_instruction0 A_ALLOC
          | ArrayRealloc ->
              (* FIXME: this built-in should be variadic *)
              self#write_instruction1 PUSH 1;
              self#write_instruction0 A_REALLOC
          | ArrayFree -> self#write_instruction0 A_FREE
          | ArrayNumof -> self#write_instruction0 A_NUMOF
          | ArrayCopy -> self#write_instruction0 A_COPY
          | ArrayFill -> self#write_instruction0 A_FILL
          | ArrayPushBack -> self#write_instruction0 A_PUSHBACK
          | ArrayPopBack -> self#write_instruction0 A_POPBACK
          | ArrayEmpty -> self#write_instruction0 A_EMPTY
          | ArrayErase -> self#write_instruction0 A_ERASE
          | ArrayInsert -> self#write_instruction0 A_INSERT
          | ArraySort -> self#write_instruction0 A_SORT
          | ArraySortBy -> self#write_instruction0 A_SORT_MEM
          | ArrayReverse -> self#write_instruction0 A_REVERSE
          | ArrayFind -> self#write_instruction0 A_FIND
          | DelegateNumof -> self#write_instruction0 DG_NUMOF
          | DelegateExist -> self#write_instruction0 DG_EXIST
          | DelegateErase -> self#write_instruction0 DG_ERASE
          | DelegateClear -> self#write_instruction0 DG_CLEAR
          | Assert ->
              compiler_bug "invalid built-in method call"
                (Some (ASTExpression expr)))
      (* built-in function call *)
      | Call ({ node = Ident _; _ }, args, BuiltinCall builtin) -> (
          let f = Builtin.fundecl_of_builtin ctx builtin Void None in
          self#compile_function_arguments args f;
          match builtin with
          | Assert -> self#write_instruction0 ASSERT
          | _ ->
              compiler_bug "invalid built-in function call"
                (Some (ASTExpression expr)))
      (* functype call *)
      | Call (e, args, FuncTypeCall f) ->
          let compile_arg arg (param : variable) =
            self#compile_argument arg param.type_spec.ty;
            if is_ref_scalar param.type_spec.ty then (
              self#write_instruction0 DUP2_X1;
              self#write_instruction0 POP;
              self#write_instruction0 POP)
            else self#write_instruction0 SWAP
          in
          self#compile_expression e;
          List.iter2_exn args f.params ~f:compile_arg;
          self#write_instruction1 PUSH (fun_index f);
          self#write_instruction0 CALLFUNC2
      | Call (e, args, DelegateCall f) ->
          let no = fun_index f in
          self#compile_lvalue e;
          self#compile_function_arguments args f;
          self#write_instruction1 DG_CALLBEGIN no;
          let loop_addr = current_address in
          self#write_instruction2 DG_CALL no 0;
          self#write_instruction1 JUMP loop_addr;
          self#write_address_at (loop_addr + 6) current_address
      | Call (_, _, _) ->
          compiler_bug "invalid call expression" (Some (ASTExpression expr))
      | New _ -> compiler_bug "bare new expression" (Some (ASTExpression expr))
      | RvalueRef _ ->
          compiler_bug "RvalueRef in rvalue context" (Some (ASTExpression expr))
      | DummyRef _ -> (
          self#compile_lvalue expr;
          match expr.ty with
          | Ref (Struct (_, no)) -> self#write_instruction1 SR_REF2 no
          | _ ->
              compiler_bug "unexpected DummyRef type"
                (Some (ASTExpression expr)))
      | This -> (
          match expr.ty with
          | Struct (_, no) ->
              self#write_instruction0 PUSHSTRUCTPAGE;
              self#write_instruction1 SR_REF2 no
          | _ ->
              compiler_bug "unexpected type of this" (Some (ASTExpression expr))
          )
      | Null -> (
          match expr.ty with
          | FuncType _ | IMainSystem -> self#write_instruction1 PUSH 0
          | Delegate _ -> self#write_instruction0 DG_NEW
          | String -> self#write_instruction1 S_PUSH 0
          | ty ->
              compiler_bug
                ("unimplemented: NULL rvalue of type " ^ jaf_type_to_string ty)
                (Some (ASTExpression expr)))
      | Lambda f ->
          let jump_addr = current_address + 2 in
          self#write_instruction1 JUMP 0;
          self#compile_function f;
          self#write_address_at jump_addr current_address;
          self#write_instruction0 PUSHSTRUCTPAGE;
          self#write_instruction1 PUSH (fun_index f)

    method compile_expr_and_pop (expr : expression) =
      match expr.node with
      | Assign
          ( EqAssign,
            { node = Ident (_, LocalVariable v); _ },
            { node = ConstInt n; _ } )
        when ctx.version > 100 && ctx.version < 630
             && not (is_ref v.type_spec.ty) ->
          self#write_instruction2 SH_LOCALASSIGN (var_index v) n
      | Unary
          ( ((PreInc | PostInc | PreDec | PostDec) as op),
            { node = Ident (_, LocalVariable v); _ } )
        when ctx.version > 100 && ctx.version < 630
             && (not (is_ref v.type_spec.ty))
             && Poly.(expr.ty <> LongInt) ->
          self#write_instruction1
            (match op with PreInc | PostInc -> SH_LOCALINC | _ -> SH_LOCALDEC)
            (var_index v)
      | Unary (((PreInc | PreDec) as op), e) ->
          self#compile_lvalue e;
          self#write_instruction0 DUP2;
          self#write_instruction0 (incdec_instruction op e.ty);
          self#write_instruction0 POP;
          self#write_instruction0 POP
      | Seq (a, b) ->
          self#compile_expr_and_pop a;
          self#compile_expr_and_pop b
      | DummyRef _ ->
          self#compile_lvalue expr;
          self#compile_pop expr.ty (ASTExpression expr)
      | _ ->
          self#compile_expression expr;
          self#compile_pop expr.ty (ASTExpression expr)

    method private compile_ref_assign ~is_init ~parent lhs (rhs : expression) =
      self#compile_lock_peek;
      self#compile_variable_ref lhs;
      self#compile_delete_ref lhs.ty;
      (match (is_init, rhs.node) with
      | _, Null -> ()
      | true, _ -> self#write_instruction0 DUP2
      | false, _ -> ());
      self#compile_lvalue rhs;
      (match lhs.ty with
      | _ when is_ref_scalar lhs.ty -> (
          match rhs.node with
          | Null ->
              self#write_instruction0 R_ASSIGN;
              self#write_instruction0 POP;
              self#write_instruction0 POP
          | _ when is_init ->
              self#write_instruction0 R_ASSIGN;
              self#write_instruction0 POP;
              self#write_instruction0 POP;
              self#write_instruction0 REF;
              self#write_instruction0 SP_INC
          | _ ->
              self#write_instruction0 DUP_U2;
              self#write_instruction0 SP_INC;
              self#write_instruction0 R_ASSIGN;
              self#write_instruction0 POP;
              self#write_instruction0 POP)
      | Ref (String | Struct _ | Array _) -> (
          match rhs.node with
          | Null ->
              self#write_instruction0 ASSIGN;
              self#write_instruction0 POP
          | _ when is_init ->
              self#write_instruction0 ASSIGN;
              self#write_instruction0 DUP_X2;
              self#write_instruction0 POP;
              self#write_instruction0 REF;
              self#write_instruction0 SP_INC;
              self#write_instruction0 POP
          | _ ->
              self#write_instruction0 DUP;
              self#write_instruction0 SP_INC;
              self#write_instruction0 ASSIGN;
              self#write_instruction0 POP)
      | _ -> compiler_bug "Invalid LHS in reference assignment" (Some parent));
      self#compile_unlock_peek

    (** Emit the code for a statement. Statements are stack-neutral, i.e. the
        state of the stack is unchanged after executing a statement. *)
    method compile_statement (stmt : statement) =
      self#mark_location stmt.loc;
      (* delete locals that will be out-of-scope after this statement *)
      List.iter (List.rev stmt.delete_vars) ~f:self#compile_delete_var;
      match stmt.node with
      | EmptyStatement -> ()
      | Declarations decls ->
          List.iter decls.vars ~f:self#compile_variable_declaration
      | Expression e -> self#compile_expr_and_pop e
      | Compound stmts -> self#compile_block stmts
      | Label name -> self#add_label name stmt
      | If (test, con, alt) ->
          self#compile_expression test;
          let ifz_addr = current_address + 2 in
          self#write_instruction1 IFZ 0;
          self#compile_statement con;
          let jump_addr = current_address + 2 in
          self#write_instruction1 JUMP 0;
          self#write_address_at ifz_addr current_address;
          self#compile_statement alt;
          self#write_address_at jump_addr current_address
      | While (test, body) ->
          (* loop test *)
          let loop_addr = current_address in
          self#start_loop loop_addr;
          self#compile_expression test;
          let break_addr = current_address + 2 in
          self#write_instruction1 IFZ 0;
          (* loop body *)
          self#compile_statement body;
          self#write_instruction1 JUMP loop_addr;
          (* loop end *)
          self#write_address_at break_addr current_address;
          self#end_loop
      | DoWhile (test, body) ->
          (* start the loop with an unknown continue address *)
          let loop_addr = current_address in
          self#start_loop (-1);
          self#compile_statement body;
          (* loop test ('continue' jumps here) *)
          self#resolve_continues;
          self#compile_expression test;
          self#write_instruction1 IFNZ loop_addr;
          (* loop end *)
          self#end_loop
      | For (decl, None, None, body) ->
          (* loop init *)
          self#compile_block [ decl ];
          (* loop body *)
          let loop_addr = current_address in
          self#start_loop loop_addr;
          self#compile_statement body;
          self#write_instruction1 JUMP loop_addr;
          self#end_loop
      | For (decl, test, inc, body) ->
          (* loop init *)
          self#compile_block [ decl ];
          (* loop test *)
          let test_addr = current_address in
          let break_addr =
            Option.map test ~f:(fun e ->
                self#compile_expression e;
                let break_addr = current_address + 2 in
                self#write_instruction1 IFZ 0;
                break_addr)
          in
          let body_addr = current_address + 2 in
          self#write_instruction1 JUMP 0;
          (* loop increment *)
          let loop_addr = current_address in
          self#start_loop loop_addr;
          (* self#set_continue_addr loop_addr; *)
          Option.iter inc ~f:self#compile_expr_and_pop;
          self#write_instruction1 JUMP test_addr;
          (* loop body *)
          self#write_address_at body_addr current_address;
          self#compile_statement body;
          self#write_instruction1 JUMP loop_addr;
          (* loop end *)
          Option.iter break_addr ~f:(fun break_addr ->
              self#write_address_at break_addr current_address);
          self#end_loop
      | Goto name -> self#write_goto name stmt
      | Continue -> self#add_continue (ASTStatement stmt)
      | Break ->
          self#push_break_addr (current_address + 2) (ASTStatement stmt);
          self#write_instruction1 JUMP 0
      | Switch (expr, stmts) ->
          self#compile_expression expr;
          self#start_switch expr.ty (ASTExpression expr);
          self#push_break_addr (current_address + 2) (ASTStatement stmt);
          self#write_instruction1 JUMP 0;
          List.iter stmts ~f:self#compile_statement;
          self#end_switch
      | Case { node; _ } -> self#add_switch_case node (ASTStatement stmt)
      | Default -> self#set_switch_default (ASTStatement stmt)
      | Return None -> self#write_instruction0 RETURN
      | Return (Some e) ->
          (match ((Option.value_exn current_function).return.ty, e.node) with
          | Ref _, Null -> self#compile_lvalue e
          | Ref (Int | Float | Bool | LongInt | FuncType _), _ ->
              self#compile_lvalue e;
              self#write_instruction0 DUP_U2;
              self#write_instruction0 SP_INC
          | Ref (String | Struct _ | Array _), _ ->
              self#compile_lvalue e;
              self#write_instruction0 DUP;
              self#write_instruction0 SP_INC
          | Ref _, _ ->
              compile_error "return statement not implemented for ref type"
                (ASTStatement stmt)
          | _ -> self#compile_expression e);
          self#write_instruction0 RETURN
      | Jump funcname ->
          let no = self#add_string funcname in
          self#write_instruction1 S_PUSH no;
          self#write_instruction0 CALLONJUMP;
          self#write_instruction0 SJUMP
      | Jumps e ->
          self#compile_expression e;
          self#write_instruction0 CALLONJUMP;
          self#write_instruction0 SJUMP
      | Message msg ->
          let msg_no = self#add_message msg in
          self#write_instruction1 MSG msg_no
      | RefAssign (lhs, rhs) ->
          self#compile_ref_assign ~is_init:false ~parent:(ASTStatement stmt) lhs
            rhs
      | ObjSwap (a, b) ->
          self#compile_variable_ref a;
          self#compile_variable_ref b;
          let type_no =
            Ain.Type.int_of_data_type (Ain.version ctx.ain)
              (jaf_to_ain_type a.ty)
          in
          self#write_instruction1 PUSH type_no;
          self#write_instruction0 OBJSWAP

    (** Emit the code for a variable declaration. If the variable has an
        initval, the initval expression is computed and assigned to the
        variable. Otherwise a default value is assigned. *)
    method compile_variable_declaration (decl : variable) =
      if decl.is_const then ()
      else if
        Ain.version ctx.ain <= 1
        && Option.is_none decl.initval
        && List.is_empty decl.array_dim
      then ()
      else
        let index = var_index decl in
        let lhs =
          {
            node = Ident (decl.name, LocalVariable decl);
            ty = decl.type_spec.ty;
            loc = decl.location;
          }
        in
        self#scope_add_var decl;
        match decl.type_spec.ty with
        | Ref _ ->
            let rhs =
              match decl.initval with
              | Some e -> e
              | None -> make_expr ~ty:decl.type_spec.ty Null
            in
            self#compile_ref_assign ~is_init:true ~parent:(ASTVariable decl) lhs
              rhs
        | (Int | Bool | LongInt | Float | FuncType _ | String) as ty ->
            let rhs =
              match decl.initval with
              | Some e -> e
              | None ->
                  let value =
                    match ty with
                    | Int | Bool | LongInt -> ConstInt 0
                    | Float -> ConstFloat 0.0
                    | FuncType _ | String -> Null
                    | _ -> failwith "unreachable"
                  in
                  make_expr ~ty:decl.type_spec.ty value
            in
            self#compile_expr_and_pop
              {
                node = Assign (EqAssign, lhs, rhs);
                ty = rhs.ty;
                loc = decl.location;
              }
        | Struct (_, sno) -> (
            (* FIXME: use verbose versions *)
            self#write_instruction1 SH_LOCALDELETE index;
            self#write_instruction2 SH_LOCALCREATE index sno;
            match decl.initval with
            | Some e ->
                self#compile_lvalue lhs;
                self#compile_expression e;
                if not (Ain.version ctx.ain <= 1 || Ain.version ctx.ain >= 11)
                then self#write_instruction1 PUSH sno;
                self#write_instruction0 SR_ASSIGN;
                self#compile_pop decl.type_spec.ty (ASTVariable decl)
            | None -> ())
        | Array _ ->
            let has_dims = List.length decl.array_dim > 0 in
            self#compile_local_ref index;
            if has_dims then (
              List.iter decl.array_dim ~f:self#compile_expression;
              self#write_instruction1 PUSH (List.length decl.array_dim);
              self#write_instruction0 A_ALLOC)
            else self#write_instruction0 A_FREE
        | Delegate _ -> (
            self#compile_local_ref index;
            self#write_instruction0 REF;
            match decl.initval with
            | Some ({ ty = String; _ } as e) ->
                self#compile_expression e;
                self#write_instruction0 DG_SET
            | Some ({ ty = TyMethod _; _ } as e) ->
                self#compile_expression e;
                self#write_instruction0 DG_SET
            | Some ({ ty = Delegate _; _ } as e) ->
                self#compile_expression e;
                self#write_instruction0 DG_ASSIGN;
                self#write_instruction0 DG_POP
            | Some _ ->
                compiler_bug "invalid delegate initval"
                  (Some (ASTVariable decl))
            | None -> self#write_instruction0 DG_CLEAR)
        | _ -> compile_error "Unimplemented variable type" (ASTVariable decl)

    (** Emit the code for a block of statements. *)
    method compile_block (stmts : statement list) =
      self#start_scope;
      List.iter stmts ~f:self#compile_statement;
      self#end_scope

    (** Emit the code for a default return value. *)
    method compile_default_return (t : jaf_type) decl =
      match t with
      | Ref (String | Struct _ | Array _) -> self#write_instruction1 PUSH (-1)
      | Ref (Int | Float | Bool | LongInt) ->
          self#write_instruction1 PUSH (-1);
          self#write_instruction1 PUSH 0
      | Void -> ()
      | Int | Bool | LongInt | FuncType _ -> self#write_instruction1 PUSH 0
      | Float -> self#write_instruction1 F_PUSH 0
      | String -> self#write_instruction1 S_PUSH 0
      | Struct _ | Array _ | Delegate _ -> self#write_instruction1 PUSH (-1)
      | _ -> compile_error "default return value not implemented for type" decl

    (** Emit the code for a function. *)
    method compile_function (decl : fundecl) =
      (* ENDFUNC is not generated for the "NULL" function and methods except
         auto-generated array initializers. ain v0/v1 does not have ENDFUNC. *)
      let endfunc =
        match decl with
        | _ when ctx.version <= 100 -> false
        | { name = "NULL"; _ } -> false
        | { class_name = None; _ } | { name = "2"; _ } | { is_lambda = true; _ }
          ->
            true
        | _ -> false
      in
      self#write_function decl ~endfunc ~body:(fun () ->
          self#compile_block (Option.value_exn decl.body);
          if not (decl.is_label || String.equal (mangled_name decl) "NULL") then (
            self#compile_default_return decl.return.ty
              (ASTDeclaration (Function decl));
            self#write_instruction0 RETURN))

    (** Emit the code for an ain v1 scenario label. *)
    method compile_scenario_label (decl : fundecl) =
      self#add_scenario_label decl.name;
      let body = Option.value_exn decl.body in
      match body with
      | [ { node = Expression { node = Call (_, [], FunctionCall _); _ }; _ } ]
        ->
          self#compile_block body
      | _ ->
          compile_error
            "ain v1 scenario label body must be a single argument-less \
             function call"
            (ASTDeclaration (Function decl))

    (** Compile a list of declarations. *)
    method compile ?(eof = true) jaf_name (decls : declaration list) =
      let compile_decl = function
        | Jaf.Function f ->
            if f.is_label && Ain.version ctx.ain = 1 then
              self#compile_scenario_label f
            else self#compile_function f
        | Global _ | GlobalGroup _ | FuncTypeDef _ | DelegateDef _ -> ()
        | StructDef d ->
            let compile_struct_decl (d : struct_declaration) =
              match d with
              | AccessSpecifier _ -> ()
              | MemberDecl _ -> () (* TODO: member initvals? *)
              | Constructor f | Destructor f | Method f ->
                  if Option.is_some f.body then self#compile_function f
            in
            List.iter d.decls ~f:compile_struct_decl
        | Enum e ->
            (* TODO: built-in enum methods *)
            compile_error "Enums not implemented" (ASTDeclaration (Enum e))
      in
      List.iter decls ~f:compile_decl;
      if eof then self#write_eof jaf_name;
      self#write_buffer
  end

let compile ?eof ctx jaf_name decls debug_info =
  (new jaf_compiler ctx debug_info)#compile ?eof jaf_name decls
