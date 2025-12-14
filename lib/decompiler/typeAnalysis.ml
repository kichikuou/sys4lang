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
open Loc
open Type
open Ast

let auto_deref = function Ref t -> t | t -> t

let array_element_type = function
  | Array element_type -> element_type
  | _ -> failwith "array_element_type: non-array type"

let builtin_type receiver_type insn args =
  let array_callback_type () =
    if Ain.ain.vers < 8 then FuncType (TypeVar.create Var)
    else Delegate (TypeVar.create Var)
  in
  let open Instructions in
  match insn with
  | A_NUMOF ->
      if snd (array_base_and_rank receiver_type) = 1 then
        (PSEUDO_A_NUMOF1, Int, [ Int ])
      else (A_NUMOF, Int, [ Int ])
  | A_EMPTY -> (insn, Bool, [])
  | A_ALLOC -> (insn, Void, List.map args ~f:(fun _ -> Int))
  | A_REALLOC -> (insn, Void, [ Int ])
  | A_FREE -> (insn, Void, [])
  | A_PUSHBACK -> (insn, Void, [ array_element_type receiver_type ])
  | A_POPBACK -> (insn, Void, [])
  | A_INSERT -> (insn, Void, [ Int; array_element_type receiver_type ])
  | A_ERASE -> (insn, Int, [ Int ])
  | A_FILL -> (insn, Int, [ Int; Int; array_element_type receiver_type ])
  | A_COPY -> (insn, Int, [ Int; Ref receiver_type; Int; Int ])
  | A_FIND -> (insn, Int, [ Int; Int; Any; array_callback_type () ])
  | A_SORT -> (insn, Void, [ array_callback_type () ])
  | A_SORT_MEM -> (
      match receiver_type with
      | Array (Struct n) -> (insn, Void, [ StructMember n ])
      | _ ->
          Printf.failwithf "A_SORT_MEM: unexpected receiver type %s"
            (show_ain_type receiver_type)
            ())
  | A_REVERSE -> (insn, Void, [])
  | X_SET -> (insn, Void, [ receiver_type ])
  | S_EMPTY -> (insn, Bool, [])
  | S_LENGTH -> (insn, Int, [])
  | S_LENGTH2 -> (insn, Int, [])
  | S_LENGTHBYTE -> (insn, Int, [])
  | S_ERASE2 -> (insn, Void, [ Int ])
  | S_FIND -> (insn, Int, [ String ])
  | S_GETPART -> (insn, String, [ Int; Int ])
  | S_PUSHBACK2 -> (insn, Void, [ Char ])
  | S_POPBACK2 -> (insn, Void, [])
  | DG_NUMOF -> (insn, Int, [])
  | DG_CLEAR -> (insn, Void, [])
  | DG_EXIST -> (insn, Bool, [ receiver_type ])
  | DG_ADD | DG_ERASE -> (insn, Void, [ receiver_type ])
  | FTOS -> (insn, String, [ Int ])
  | op ->
      Printf.failwithf "builtin_type: unknown operator %s"
        (Instructions.show_instruction op)
        ()

let remove_cast (t : ain_type) e =
  match (t, e) with
  | Int, UnaryOp (FTOI, e) -> e
  | Float, UnaryOp (ITOF, e) -> e
  | LongInt, UnaryOp (ITOLI, e) -> e
  | _, _ -> e

let remove_binop_cast (insn : Instructions.instruction) lhs rhs =
  match insn with
  | F_ADD | F_SUB | F_MUL | F_DIV | F_EQUALE | F_NOTE | F_LT | F_LTE | F_GT
  | F_GTE -> (
      match (lhs, rhs) with
      | UnaryOp (ITOF, _), UnaryOp (ITOF, _) -> (lhs, rhs)
      | _, _ -> (remove_cast Float lhs, remove_cast Float rhs))
  | LI_ADD | LI_SUB | LI_MUL | LI_DIV | LI_MOD -> (
      match (lhs, rhs) with
      | UnaryOp (ITOLI, _), UnaryOp (ITOLI, _) -> (lhs, rhs)
      | _, _ -> (remove_cast LongInt lhs, remove_cast LongInt rhs))
  | _ -> (lhs, rhs)

let unify_if_functype t t' =
  match (t, t') with
  | FuncType ftv, FuncType ftv' -> Type.TypeVar.unify ftv ftv'
  | Delegate dtv, Delegate dtv' -> Type.TypeVar.unify dtv dtv'
  | _ -> ()

class analyzer (func : Ain.Function.t) (struc : Ain.Struct.t option) =
  object (self)
    method analyze_lvalue =
      function
      | NullRef -> (NullRef, Type.Void)
      | PageRef (_, var) as l -> (l, var.type_)
      | RefRef lval -> (
          match self#analyze_lvalue lval with
          | lval', Ref t -> (RefRef lval', t)
          | _ -> failwith "REFREF with non-reference value")
      | IncDec (fix, op, lval) ->
          let l, t = self#analyze_lvalue lval in
          (IncDec (fix, op, l), t)
      | ObjRef (obj, key) as lvalue -> (
          let obj', ot = self#analyze_expr Any obj
          and key', kt = self#analyze_expr Int key in
          match (auto_deref ot, auto_deref kt) with
          | Array t, (Int | LongInt | Char) -> (ArrayRef (obj', key'), t)
          | Struct s, Int -> (
              match key' with
              | Number n ->
                  let memb = Ain.ain.strt.(s).members.(Int32.to_int_exn n) in
                  (MemberRef (obj', memb), memb.type_)
              | _ -> failwith "oops1")
          | _ ->
              Printf.failwithf "lvalue: %s\n ot: %s" (show_lvalue lvalue)
                (show_ain_type ot) ())
      | RefValue expr ->
          let expr', t = self#analyze_expr Any expr in
          (RefValue expr', t)
      | ArrayRef _ | MemberRef _ -> failwith "cannot happen"

    method analyze_expr expected =
      function
      | Page StructPage as e -> (e, Ref (Struct (Option.value_exn struc).id))
      | Page _ as e -> failwith (show_expr e)
      | Number n as e -> (
          match (expected, n) with
          | Bool, 0l -> (Boolean false, Bool)
          | Bool, 1l -> (Boolean true, Bool)
          | Char, _ -> (Character n, Char)
          | Ref _, -1l -> (Null, Ref Any)
          | (FuncType _ as f), 0l -> (Null, f)
          | (FuncType ftv as f), n ->
              let func = Ain.ain.func.(Int32.to_int_exn n) in
              TypeVar.set_type ftv (Ain.Function.to_type func);
              (FuncAddr func, f)
          | (StructMember struc as t), _ ->
              (MemberPointer (struc, Int32.to_int_exn n), t)
          | IMainSystem, 0l -> (Null, IMainSystem)
          | _ -> (e, Int))
      | Boolean _ as e -> (e, Bool)
      | Character _ as e -> (e, Char)
      | Float _ as e -> (e, Float)
      | String _ as e -> (e, String)
      | FuncAddr _ -> failwith "cannot happen"
      | MemberPointer _ -> failwith "cannot happen"
      | BoundMethod (e, f) ->
          let e', _ = self#analyze_expr Any e in
          ( BoundMethod (e', f),
            Delegate (TypeVar.create (Type (Ain.Function.to_type f))) )
      | Deref lval ->
          let lval', t = self#analyze_lvalue lval in
          (Deref lval', t)
      | DerefRef lval ->
          let lval', t = self#analyze_lvalue lval in
          (DerefRef lval', Ref t)
      | Null -> (
          match expected with
          | Delegate _ -> (Null, expected)
          | _ -> (Null, Ref Any))
      | Void -> (Void, Void)
      | Option e ->
          let e, t = self#analyze_expr expected e in
          (Option e, t)
      | New n as e -> (e, Ref (Struct n))
      | DerefStruct (struc, expr) ->
          let expr, _ = self#analyze_expr (Struct struc) expr in
          (DerefStruct (struc, expr), Struct struc)
      | UnaryOp (insn, e) -> self#analyze_unary_op insn e
      | BinaryOp (insn, lhs, rhs) -> self#analyze_binary_op insn lhs rhs
      | AssignOp (insn, lval, rhs) -> self#analyze_assign_op insn lval rhs
      | Call (f, args) ->
          let f', return_type, arg_types = self#analyze_callable args f in
          let arg_types' =
            List.filter arg_types ~f:(function
              | (Void : ain_type) -> false
              | _ -> true)
          in
          let args' =
            List.map2_exn args arg_types' ~f:(fun arg t ->
                let arg', t' = self#analyze_expr t arg in
                unify_if_functype t t';
                remove_cast t arg')
          in
          (Call (f', args'), return_type)
      | TernaryOp (e1, e2, e3) ->
          let e1', _t1 = self#analyze_expr Bool e1
          and e2', t2 = self#analyze_expr expected e2
          and e3', _t3 = self#analyze_expr expected e3 in
          (TernaryOp (e1', e2', e3'), t2)
      | DelegateCast (expr, dg_type) ->
          let expr', _ = self#analyze_expr String expr in
          let t =
            Type.Delegate
              (TypeVar.create
                 (Id (dg_type, Ain.FuncType.to_type Ain.ain.delg.(dg_type))))
          in
          (* The DelegateCast annotation is no longer needed, so strip it out. *)
          (expr', t)
      | C_Ref (str, i) ->
          let str', _t1 = self#analyze_expr String str
          and i', _t2 = self#analyze_expr Int i in
          (C_Ref (str', i'), Char)
      | C_Assign (str, i, char) ->
          let str', _t1 = self#analyze_expr String str
          and i', _t2 = self#analyze_expr Int i
          and char', _t3 = self#analyze_expr Char char in
          (C_Assign (str', i', char'), Char)
      | PropertySet (obj, m, rhs) ->
          let obj, _ = self#analyze_expr Any obj in
          let arg_type =
            match Ain.Function.arg_types m with
            | [ t ] -> t
            | _ -> failwith "non-unary property setter function"
          in
          let rhs, t = self#analyze_expr arg_type rhs in
          unify_if_functype arg_type t;
          let rhs = remove_cast arg_type rhs in
          (PropertySet (obj, m, rhs), t)

    method private analyze_callable args =
      function
      | Function func as expr ->
          (expr, func.return_type, Ain.Function.arg_types func)
      | FuncPtr (ft, expr) -> (
          match self#analyze_expr Any expr with
          | expr', FuncType ftv ->
              Type.TypeVar.set_id ftv ft.id
                (Ain.FuncType.to_type Ain.ain.fnct.(ft.id));
              (FuncPtr (ft, expr'), ft.return_type, Ain.FuncType.arg_types ft)
          | _, t ->
              Printf.failwithf "Functype expected, got %s" (show_ain_type t) ())
      | Delegate (dt, expr) -> (
          match self#analyze_expr Any expr with
          | expr', Delegate dtv ->
              Type.TypeVar.set_id dtv dt.id
                (Ain.FuncType.to_type Ain.ain.delg.(dt.id));
              (Delegate (dt, expr'), dt.return_type, Ain.FuncType.arg_types dt)
          | _, t ->
              Printf.failwithf "Delegate expected, got %s" (show_ain_type t) ())
      | Method (this, func) ->
          let expr', _ = self#analyze_expr Any this in
          (Method (expr', func), func.return_type, Ain.Function.arg_types func)
      | HllFunc (_, func) as expr ->
          (expr, func.return_type, Ain.HLL.arg_types func)
      | SysCall n as expr ->
          let syscall = Instructions.syscalls.(n) in
          (expr, syscall.return_type, syscall.arg_types)
      | Builtin (insn, lval) ->
          let lval', t = self#analyze_lvalue lval in
          let insn', return_type, arg_types =
            builtin_type (auto_deref t) insn args
          in
          (Builtin (insn', lval'), return_type, arg_types)
      | Builtin2 (insn, this) ->
          let this', t = self#analyze_expr Any this in
          let insn', return_type, arg_types =
            builtin_type (auto_deref t) insn args
          in
          (Builtin2 (insn', this'), return_type, arg_types)

    method private analyze_unary_op insn e =
      let e', et = self#analyze_expr Any e in
      let t =
        match (insn, auto_deref et) with
        | FTOI, Float -> Int
        | ITOF, (Int | LongInt | Bool) -> Float
        | ITOLI, (Int | LongInt | Bool) -> LongInt
        | ITOB, (Int | LongInt | Bool) -> Bool
        | STOI, String -> Int
        | I_STRING, (Int | LongInt | Bool) -> String
        | (INV | COMPL), Int -> Int
        | F_INV, Float -> Float
        | NOT, t -> t
        | _ ->
            Printf.failwithf "analyze_unary_op (%s, %s)"
              (Instructions.show_instruction insn)
              (show_expr e) ()
      in
      (UnaryOp (insn, e'), t)

    method private analyze_binary_op insn lhs rhs =
      let result_type lt rt =
        match insn with
        | ADD | F_ADD | LI_ADD | S_ADD | SUB | F_SUB | LI_SUB | MUL | F_MUL
        | LI_MUL | DIV | F_DIV | LI_DIV | MOD | LI_MOD | S_MOD _ | LSHIFT
        | RSHIFT | AND | OR | XOR | PSEUDO_LOGAND | PSEUDO_LOGOR | OBJSWAP _
        | PSEUDO_NULL_COALESCE ->
            lt
        | S_PLUSA | S_PLUSA2 | PSEUDO_COMMA | DG_PLUSA | DG_MINUSA -> rt
        | EQUALE | S_EQUALE | F_EQUALE | R_EQUALE | NOTE | S_NOTE | F_NOTE
        | R_NOTE | LT | F_LT | S_LT | LTE | F_LTE | S_LTE | GT | F_GT | S_GT
        | GTE | F_GTE | S_GTE ->
            Bool
        | _ ->
            Printf.failwithf "analyze_binary_op: %s"
              (Instructions.show_instruction insn)
              ()
      in
      let result_insn lt _rt =
        match (insn, lt) with
        | EQUALE, Ref _ -> Instructions.R_EQUALE
        | NOTE, Ref _ -> R_NOTE
        | _, _ -> insn
      in
      let expected_arg_type =
        match insn with PSEUDO_LOGAND | PSEUDO_LOGOR -> Bool | _ -> Any
      in
      (* If either side is a numeric literal, match it to the other side's type. *)
      match (insn, lhs, rhs) with
      | (LSHIFT | RSHIFT), _, _ ->
          let lhs', lt = self#analyze_expr expected_arg_type lhs in
          let rhs', rt = self#analyze_expr Int rhs in
          (BinaryOp (result_insn lt rt, lhs', rhs'), result_type lt rt)
      | _, _, Number _ ->
          let lhs', lt = self#analyze_expr expected_arg_type lhs in
          let rhs', rt = self#analyze_expr lt rhs in
          (BinaryOp (result_insn lt rt, lhs', rhs'), result_type lt rt)
      | _, Number _, _ ->
          let rhs', rt = self#analyze_expr expected_arg_type rhs in
          let lhs', lt = self#analyze_expr rt lhs in
          (BinaryOp (result_insn lt rt, lhs', rhs'), result_type lt rt)
      | _, _, _ ->
          let lhs, lt = self#analyze_expr expected_arg_type lhs
          and rhs, rt = self#analyze_expr expected_arg_type rhs in
          unify_if_functype lt rt;
          let lhs, rhs = remove_binop_cast insn lhs rhs in
          (BinaryOp (result_insn lt rt, lhs, rhs), result_type lt rt)

    method private analyze_assign_op insn lval rhs =
      let lval', lt =
        match self#analyze_lvalue lval with
        | ( (RefValue (AssignOp (PSEUDO_REF_ASSIGN, PageRef (LocalPage, v), _))
             as lval'),
            Ref lt )
          when String.is_prefix v.name ~prefix:"<dummy" ->
            (lval', lt) (* allow `(<dummy> <- ref_expr) = value` *)
        | lval', lt -> (lval', lt)
      in
      let rhs', rt = self#analyze_expr lt rhs in
      match (lt, rt, insn) with
      | FuncType ftl, FuncType ftr, _ ->
          Type.TypeVar.unify ftl ftr;
          (AssignOp (insn, lval', rhs'), lt)
      | FuncType ftv, String, PSEUDO_FT_ASSIGNS ft_id ->
          Type.TypeVar.set_id ftv ft_id
            (Ain.FuncType.to_type Ain.ain.fnct.(ft_id));
          (AssignOp (insn, lval', rhs'), String)
      | (Delegate dtl | Ref (Delegate dtl)), Delegate dtr, _ ->
          Type.TypeVar.unify dtl dtr;
          (AssignOp (insn, lval', rhs'), lt)
      | (Int | Bool | LongInt | Char), (Int | Bool | LongInt | Char), _
      | Float, Float, _
      | FuncType _, Int, _
      | _, _, Instructions.S_ASSIGN
      | _, _, SR_ASSIGN ->
          let rhs' = remove_cast lt rhs' in
          (AssignOp (insn, lval', rhs'), lt)
      | Ref _, (Ref _ | Array _ | Struct _ | String), (ASSIGN | R_ASSIGN) ->
          (AssignOp (PSEUDO_REF_ASSIGN, lval', rhs'), lt)
      | _ ->
          Stdio.eprintf "left type:  %s\nright type: %s\nop: %s\nexpr: %s"
            (show_ain_type lt) (show_ain_type rt)
            (Instructions.show_instruction insn)
            (show_expr (AssignOp (insn, lval, rhs)));
          failwith "cannot type"

    method private analyze_expr_opt expected =
      function
      | None -> None
      | Some e -> Some (fst (self#analyze_expr expected e))

    method analyze_statement stmt =
      {
        stmt with
        txt =
          (match stmt.txt with
          | VarDecl (var, None) -> VarDecl (var, None)
          | VarDecl (var, Some (insn, expr)) ->
              let expr', _ = self#analyze_expr var.type_ expr in
              let expr' = remove_cast var.type_ expr' in
              (match (var.type_, insn) with
              | FuncType ftv, PSEUDO_FT_ASSIGNS ft_id ->
                  Type.TypeVar.set_id ftv ft_id
                    (Ain.FuncType.to_type Ain.ain.fnct.(ft_id))
              | _ -> ());
              VarDecl (var, Some (insn, expr'))
          | Expression expr -> (
              match self#analyze_expr Any expr with
              | _, Array _ ->
                  Stdio.eprintf
                    "Warning: %s: Removing array expression at statement \
                     position:\n"
                    func.name;
                  Block []
              | expr, _ -> Expression expr)
          | Label _ as stmt -> stmt
          | Block stmts -> Block (List.map stmts ~f:self#analyze_statement)
          | IfElse (cond, stmt1, stmt2) ->
              let cond', _ = self#analyze_expr Bool cond in
              IfElse
                ( cond',
                  self#analyze_statement stmt1,
                  self#analyze_statement stmt2 )
          | While (cond, stmt) ->
              let cond', _ = self#analyze_expr Bool cond in
              While (cond', self#analyze_statement stmt)
          | DoWhile (stmt, cond) ->
              let txt, _ = self#analyze_expr Bool cond.txt in
              DoWhile (self#analyze_statement stmt, { cond with txt })
          | Switch (id, expr, stmt) ->
              let expr', _ = self#analyze_expr Any expr in
              Switch (id, expr', self#analyze_statement stmt)
          | For (init, cond, inc, body) ->
              For
                ( self#analyze_expr_opt Any init,
                  self#analyze_expr_opt Bool cond,
                  self#analyze_expr_opt Any inc,
                  self#analyze_statement body )
          | Break -> Break
          | Continue -> Continue
          | Goto _ as stmt -> stmt
          | Return None as s -> s
          | Return (Some expr) ->
              let expr', t = self#analyze_expr func.return_type expr in
              unify_if_functype t func.return_type;
              let expr' = remove_cast func.return_type expr' in
              Return (Some expr')
          | ScenarioJump _ as stmt -> stmt
          | Msg _ as stmt -> stmt
          | Assert expr ->
              let expr', _ = self#analyze_expr Bool expr in
              Assert expr');
      }
  end
