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

type page_value = GlobalPage | LocalPage | StructPage | ParentPage of int
[@@deriving show { with_path = false }]

type incdec_fix = Prefix | Postfix [@@deriving show { with_path = false }]
type incdec_op = Increment | Decrement [@@deriving show { with_path = false }]

type callable =
  | Function of Ain.Function.t
  | FuncPtr of Ain.FuncType.t * expr
  | Delegate of Ain.FuncType.t * expr
  | Method of expr * Ain.Function.t
  | HllFunc of string * Ain.HLL.function_t
  | SysCall of int
  | Builtin of Instructions.instruction * lvalue
  | Builtin2 of Instructions.instruction * expr
[@@deriving show { with_path = false }]

and lvalue =
  | NullRef
  | PageRef of page_value * Ain.Variable.t
  | RefRef of lvalue
  | IncDec of incdec_fix * incdec_op * lvalue
  (* ObjRefs will be converted to ArrayRef or MemberRef in type analysis phase *)
  | ObjRef of expr * expr
  | ArrayRef of expr * expr
  | MemberRef of expr * Ain.Variable.t
  | RefValue of expr
[@@deriving show { with_path = false }]

and expr =
  | Page of page_value
  | Number of int32
  | Boolean of bool
  | Character of int32
  | Float of float
  | EnumValue of int * int32
  | String of string
  | FuncAddr of Ain.Function.t
  | MemberPointer of int * int (* struct, slot *)
  | BoundMethod of expr * Ain.Function.t
  | Deref of lvalue
  | DerefRef of lvalue
  | RvalueRef of Ain.Variable.t * expr
  | Null
  | Void
  | Option of expr
  | New of { struc : int; func : int; args : expr list }
  | ArrayLiteral of expr list
  | DerefStruct of int * expr
  | UnaryOp of Instructions.instruction * expr
  | BinaryOp of Instructions.instruction * expr * expr
  | AssignOp of Instructions.instruction * lvalue * expr
  | Call of callable * expr list (* func, args *)
  | TernaryOp of expr * expr * expr
  | DelegateCast of expr * int (* str, dg_type *)
  | C_Ref of expr * expr (* str, i *)
  | C_Assign of expr * expr * expr (* str, i, char *)
  | PropertySet of {
      obj : expr;
      op : Instructions.instruction;
      func : Ain.Function.t;
      rhs : expr;
    }
  | InterfaceCast of int * expr
[@@deriving show { with_path = false }]

type label =
  | Address of int
  | CaseInt of int * int32 (* switch-id, value *)
  | CaseStr of int * string (* switch-id, value *)
  | Default of int (* switch-id *)
[@@deriving show { with_path = false }]

type statement =
  | VarDecl of Ain.Variable.t * (Instructions.instruction * expr) option
  | Expression of expr
  | Label of label
  | Block of statement loc list (* in reversed order *)
  | IfElse of
      expr * statement loc * statement loc (* (cond, thenBlock, elseBlock) *)
  | While of expr * statement loc (* (cond, block) *)
  | DoWhile of statement loc * expr loc (* (block, cond) *)
  | Switch of int * expr * statement loc (* (switch_id, expr, body) *)
  | For of
      expr option
      * expr option
      * expr option
      * statement loc (* init, cond, inc, body *)
  | ForEach of {
      rev : bool;
      var : Ain.Variable.t;
      ivar : Ain.Variable.t option;
      array : expr;
      body : statement loc;
    }
  | Break
  | Continue
  | Goto of int * int (* target, address_after_JUMP *)
  | Return of expr option
  | ScenarioJump of string
  | Msg of string * expr option
  | Assert of expr
[@@deriving show { with_path = false }]

let make_block = function
  | [] -> { txt = Block []; addr = -1; end_addr = -1 }
  | [ stmt ] -> stmt
  | stmts ->
      {
        txt = Block stmts;
        addr = (List.last_exn stmts).addr;
        end_addr = (List.hd_exn stmts).end_addr;
      }

let rec map_stmt stmt ~f =
  let txt =
    match stmt.txt with
    | VarDecl _ -> f stmt.txt
    | Expression _ -> f stmt.txt
    | Label _ -> f stmt.txt
    | IfElse (e, stmt1, stmt2) ->
        let stmt1 = map_stmt stmt1 ~f in
        let stmt2 = map_stmt stmt2 ~f in
        IfElse (e, stmt1, stmt2) |> f
    | While (cond, body) -> While (cond, map_stmt body ~f) |> f
    | DoWhile (body, cond) -> DoWhile (map_stmt body ~f, cond) |> f
    | For (init, cond, inc, body) ->
        For (init, cond, inc, map_stmt body ~f) |> f
    | ForEach r -> ForEach { r with body = map_stmt r.body ~f } |> f
    | Break -> f stmt.txt
    | Continue -> f stmt.txt
    | Goto _ -> f stmt.txt
    | Return _ -> f stmt.txt
    | ScenarioJump _ -> f stmt.txt
    | Msg _ -> f stmt.txt
    | Assert _ -> f stmt.txt
    | Block stmts -> Block (List.rev_map (List.rev stmts) ~f:(map_stmt ~f)) |> f
    | Switch (id, e, stmt) -> Switch (id, e, map_stmt stmt ~f) |> f
  in
  { stmt with txt }

let walk_statement stmt ~f =
  let rec walk { txt = stmt; _ } =
    f stmt;
    match stmt with
    | VarDecl _ -> ()
    | Expression _ -> ()
    | Label _ -> ()
    | Block stmts -> List.iter (List.rev stmts) ~f:walk
    | IfElse (_, s1, s2) ->
        walk s1;
        walk s2
    | While (_, s) -> walk s
    | DoWhile (s, _) -> walk s
    | Switch (_, _, s) -> walk s
    | For (_, _, _, s) -> walk s
    | ForEach { body; _ } -> walk body
    | Break -> ()
    | Continue -> ()
    | Goto _ -> ()
    | Return _ -> ()
    | ScenarioJump _ -> ()
    | Msg _ -> ()
    | Assert _ -> ()
  in
  walk stmt

let rec map_block stmt ~f =
  let txt =
    match stmt.txt with
    | VarDecl _ -> stmt.txt
    | Expression _ -> stmt.txt
    | Label _ -> stmt.txt
    | IfElse (e, stmt1, stmt2) ->
        let stmt1 = map_block stmt1 ~f in
        let stmt2 = map_block stmt2 ~f in
        IfElse (e, stmt1, stmt2)
    | While (cond, body) -> While (cond, map_block body ~f)
    | DoWhile (body, cond) -> DoWhile (map_block body ~f, cond)
    | For (init, cond, inc, body) -> For (init, cond, inc, map_block body ~f)
    | ForEach r -> ForEach { r with body = map_block r.body ~f }
    | Break -> stmt.txt
    | Continue -> stmt.txt
    | Goto _ -> stmt.txt
    | Return _ -> stmt.txt
    | ScenarioJump _ -> stmt.txt
    | Msg _ -> stmt.txt
    | Assert _ -> stmt.txt
    | Block stmts -> Block (f (List.rev_map (List.rev stmts) ~f:(map_block ~f)))
    | Switch (id, e, stmt) -> Switch (id, e, map_block stmt ~f)
  in
  { stmt with txt }

let subst expr e1 e2 =
  let rec rec_expr expr =
    if Poly.(expr = e1) then e2
    else
      match expr with
      | Page _ | Number _ | Boolean _ | Character _ | Float _ | EnumValue _
      | String _ | FuncAddr _ | MemberPointer _ | Null | Void | New _ ->
          expr
      | BoundMethod (e, m) -> BoundMethod (rec_expr e, m)
      | Deref l -> Deref (rec_lvalue l)
      | DerefRef l -> DerefRef (rec_lvalue l)
      | RvalueRef (v, e) -> RvalueRef (v, rec_expr e)
      | Option e -> Option (rec_expr e)
      | ArrayLiteral es -> ArrayLiteral (List.map ~f:rec_expr es)
      | DerefStruct (n, e) -> DerefStruct (n, rec_expr e)
      | UnaryOp (inst, e) -> UnaryOp (inst, rec_expr e)
      | BinaryOp (inst, lhs, rhs) -> BinaryOp (inst, rec_expr lhs, rec_expr rhs)
      | AssignOp (inst, l, e) -> AssignOp (inst, rec_lvalue l, rec_expr e)
      | Call (c, args) -> Call (rec_callable c, List.map args ~f:rec_expr)
      | TernaryOp (e1, e2, e3) ->
          TernaryOp (rec_expr e1, rec_expr e2, rec_expr e3)
      | DelegateCast (e, id) -> DelegateCast (rec_expr e, id)
      | C_Ref (e1, e2) -> C_Ref (rec_expr e1, rec_expr e2)
      | C_Assign (e1, e2, e3) -> C_Assign (rec_expr e1, rec_expr e2, rec_expr e3)
      | PropertySet r ->
          PropertySet { r with obj = rec_expr r.obj; rhs = rec_expr r.rhs }
      | InterfaceCast (struc, e) -> InterfaceCast (struc, rec_expr e)
  and rec_lvalue = function
    | NullRef -> NullRef
    | PageRef _ as lval -> lval
    | RefRef l -> RefRef (rec_lvalue l)
    | IncDec (fix, op, l) -> IncDec (fix, op, rec_lvalue l)
    | ObjRef (e1, e2) -> ObjRef (rec_expr e1, rec_expr e2)
    | ArrayRef (e1, e2) -> ArrayRef (rec_expr e1, rec_expr e2)
    | MemberRef (e, v) -> MemberRef (rec_expr e, v)
    | RefValue e -> RefValue (rec_expr e)
  and rec_callable = function
    | Function _ as f -> f
    | FuncPtr (t, e) -> FuncPtr (t, rec_expr e)
    | Delegate (t, e) -> Delegate (t, rec_expr e)
    | Method (e, f) -> Method (rec_expr e, f)
    | HllFunc _ as f -> f
    | SysCall _ as f -> f
    | Builtin (inst, l) -> Builtin (inst, rec_lvalue l)
    | Builtin2 (inst, e) -> Builtin2 (inst, rec_expr e)
  in
  rec_expr expr

let map_expr stmt ~f =
  let rec rec_expr = function
    | Page _ as expr -> f expr
    | Number _ as expr -> f expr
    | Boolean _ as expr -> f expr
    | Character _ as expr -> f expr
    | Float _ as expr -> f expr
    | EnumValue _ as expr -> f expr
    | String _ as expr -> f expr
    | FuncAddr _ as expr -> f expr
    | MemberPointer _ as expr -> f expr
    | BoundMethod (expr, m) -> BoundMethod (rec_expr expr, m) |> f
    | Deref lval -> Deref (rec_lvalue lval) |> f
    | DerefRef lval -> DerefRef (rec_lvalue lval) |> f
    | RvalueRef (v, e) -> RvalueRef (v, rec_expr e) |> f
    | Null -> f Null
    | Void -> f Void
    | Option expr -> Option (rec_expr expr) |> f
    | New r -> New { r with args = List.map ~f:rec_expr r.args } |> f
    | ArrayLiteral es -> ArrayLiteral (List.map ~f:rec_expr es) |> f
    | DerefStruct (n, expr) -> DerefStruct (n, rec_expr expr) |> f
    | UnaryOp (inst, expr) -> UnaryOp (inst, rec_expr expr) |> f
    | BinaryOp (inst, lhs, rhs) ->
        BinaryOp (inst, rec_expr lhs, rec_expr rhs) |> f
    | AssignOp (inst, lval, expr) ->
        AssignOp (inst, rec_lvalue lval, rec_expr expr) |> f
    | Call (c, args) -> Call (rec_callable c, List.map args ~f:rec_expr) |> f
    | TernaryOp (e1, e2, e3) ->
        TernaryOp (rec_expr e1, rec_expr e2, rec_expr e3) |> f
    | DelegateCast (expr, id) -> DelegateCast (rec_expr expr, id) |> f
    | C_Ref (e1, e2) -> C_Ref (rec_expr e1, rec_expr e2) |> f
    | C_Assign (e1, e2, e3) ->
        C_Assign (rec_expr e1, rec_expr e2, rec_expr e3) |> f
    | PropertySet r ->
        PropertySet { r with obj = rec_expr r.obj; rhs = rec_expr r.rhs } |> f
    | InterfaceCast (struc, e) -> InterfaceCast (struc, rec_expr e) |> f
  and rec_lvalue = function
    | NullRef -> NullRef
    | PageRef _ as lval -> lval
    | RefRef lval -> RefRef (rec_lvalue lval)
    | IncDec (fix, op, lval) -> IncDec (fix, op, rec_lvalue lval)
    | ObjRef (e1, e2) -> ObjRef (rec_expr e1, rec_expr e2)
    | ArrayRef (e1, e2) -> ArrayRef (rec_expr e1, rec_expr e2)
    | MemberRef (e, v) -> MemberRef (rec_expr e, v)
    | RefValue e -> RefValue (rec_expr e)
  and rec_callable = function
    | Function _ as f -> f
    | FuncPtr (t, expr) -> FuncPtr (t, rec_expr expr)
    | Delegate (t, expr) -> Delegate (t, rec_expr expr)
    | Method (expr, f) -> Method (rec_expr expr, f)
    | HllFunc _ as f -> f
    | SysCall _ as f -> f
    | Builtin (inst, lval) -> Builtin (inst, rec_lvalue lval)
    | Builtin2 (inst, expr) -> Builtin2 (inst, rec_expr expr)
  in
  let rec rec_stmt stmt =
    let txt =
      match stmt.txt with
      | VarDecl (_, None) -> stmt.txt
      | VarDecl (v, Some (insn, e)) -> VarDecl (v, Some (insn, rec_expr e))
      | Expression e -> Expression (rec_expr e)
      | Label _ -> stmt.txt
      | IfElse (e, stmt1, stmt2) ->
          IfElse (rec_expr e, rec_stmt stmt1, rec_stmt stmt2)
      | While (cond, body) -> While (rec_expr cond, rec_stmt body)
      | DoWhile (body, cond) ->
          DoWhile (rec_stmt body, { cond with txt = rec_expr cond.txt })
      | For (init, cond, inc, body) ->
          For
            ( Option.map ~f:rec_expr init,
              Option.map ~f:rec_expr cond,
              Option.map ~f:rec_expr inc,
              rec_stmt body )
      | ForEach r ->
          ForEach { r with array = rec_expr r.array; body = rec_stmt r.body }
      | Break -> stmt.txt
      | Continue -> stmt.txt
      | Goto _ -> stmt.txt
      | Return None -> stmt.txt
      | Return (Some e) -> Return (Some (rec_expr e))
      | ScenarioJump _ -> stmt.txt
      | Msg (_, None) -> stmt.txt
      | Msg (m, Some e) -> Msg (m, Some (rec_expr e))
      | Assert e -> Assert (rec_expr e)
      | Block stmts -> Block (List.map stmts ~f:rec_stmt)
      | Switch (id, e, stmt) -> Switch (id, rec_expr e, rec_stmt stmt)
    in
    { stmt with txt }
  in
  rec_stmt stmt

let walk_expr ?(expr_cb = fun _ -> ()) ?(lvalue_cb = fun _ -> ()) =
  let rec rec_expr expr =
    expr_cb expr;
    match expr with
    | Page _ -> ()
    | Number _ -> ()
    | Boolean _ -> ()
    | Character _ -> ()
    | Float _ -> ()
    | EnumValue _ -> ()
    | String _ -> ()
    | FuncAddr _ -> ()
    | MemberPointer _ -> ()
    | BoundMethod (expr, _) -> rec_expr expr
    | Deref lval -> rec_lvalue lval
    | DerefRef lval -> rec_lvalue lval
    | RvalueRef (_, e) -> rec_expr e
    | Null -> ()
    | Void -> ()
    | Option expr -> rec_expr expr
    | New r -> List.iter ~f:rec_expr r.args
    | ArrayLiteral es -> List.iter ~f:rec_expr es
    | DerefStruct (_, expr) -> rec_expr expr
    | UnaryOp (_, expr) -> rec_expr expr
    | BinaryOp (_, lhs, rhs) ->
        rec_expr lhs;
        rec_expr rhs
    | AssignOp (_, lval, expr) ->
        rec_lvalue lval;
        rec_expr expr
    | Call (c, args) ->
        rec_callable c;
        List.iter args ~f:rec_expr
    | TernaryOp (e1, e2, e3) ->
        rec_expr e1;
        rec_expr e2;
        rec_expr e3
    | DelegateCast (expr, _) -> rec_expr expr
    | C_Ref (e1, e2) ->
        rec_expr e1;
        rec_expr e2
    | C_Assign (e1, e2, e3) ->
        rec_expr e1;
        rec_expr e2;
        rec_expr e3
    | PropertySet r ->
        rec_expr r.obj;
        rec_expr r.rhs
    | InterfaceCast (_, e) -> rec_expr e
  and rec_lvalue lval =
    lvalue_cb lval;
    match lval with
    | NullRef -> ()
    | PageRef _ -> ()
    | RefRef lval -> rec_lvalue lval
    | IncDec (_, _, lval) -> rec_lvalue lval
    | ObjRef (e1, e2) ->
        rec_expr e1;
        rec_expr e2
    | ArrayRef (e1, e2) ->
        rec_expr e1;
        rec_expr e2
    | MemberRef (e, _) -> rec_expr e
    | RefValue e -> rec_expr e
  and rec_callable = function
    | Function _ -> ()
    | FuncPtr (_, expr) -> rec_expr expr
    | Delegate (_, expr) -> rec_expr expr
    | Method (expr, _) -> rec_expr expr
    | HllFunc _ -> ()
    | SysCall _ -> ()
    | Builtin (_, lval) -> rec_lvalue lval
    | Builtin2 (_, expr) -> rec_expr expr
  in
  rec_expr

let walk ?(stmt_cb = fun _ -> ()) ?(expr_cb = fun _ -> ())
    ?(lvalue_cb = fun _ -> ()) stmt =
  let rec_expr = walk_expr ~expr_cb ~lvalue_cb in
  let rec rec_stmt { txt = stmt; _ } =
    stmt_cb stmt;
    match stmt with
    | VarDecl (_, None) -> ()
    | VarDecl (_, Some (_, e)) -> rec_expr e
    | Expression e -> rec_expr e
    | Label _ -> ()
    | IfElse (e, stmt1, stmt2) ->
        rec_expr e;
        rec_stmt stmt1;
        rec_stmt stmt2
    | While (cond, body) ->
        rec_expr cond;
        rec_stmt body
    | DoWhile (body, { txt = cond; _ }) ->
        rec_stmt body;
        rec_expr cond
    | For (init, cond, inc, body) ->
        Option.iter ~f:rec_expr init;
        Option.iter ~f:rec_expr cond;
        Option.iter ~f:rec_expr inc;
        rec_stmt body
    | ForEach { array; body; _ } ->
        rec_expr array;
        rec_stmt body
    | Break -> ()
    | Continue -> ()
    | Goto _ -> ()
    | Return e -> Option.iter ~f:rec_expr e
    | ScenarioJump _ -> ()
    | Msg (_, e) -> Option.iter ~f:rec_expr e
    | Assert e -> rec_expr e
    | Block stmts -> List.iter (List.rev stmts) ~f:rec_stmt
    | Switch (_, e, stmt) ->
        rec_expr e;
        rec_stmt stmt
  in
  rec_stmt stmt

let contains_expr expr sub_expr =
  let exception Found in
  let expr_cb e = if Poly.equal e sub_expr then raise Found in
  try
    walk_expr ~expr_cb expr;
    false
  with Found -> true

let contains_interface_expr expr iface =
  contains_expr expr iface
  ||
  (* Interfaces are NULL-checked with REF, but their values are referenced
     with REFREF. *)
  match iface with
  | Deref obj' -> contains_expr expr (DerefRef obj')
  | _ -> false

let insert_option expr obj =
  let expr = subst expr obj (Option obj) in
  match obj with
  | Deref lval -> subst expr (DerefRef lval) (Option (DerefRef lval))
  | _ -> expr
