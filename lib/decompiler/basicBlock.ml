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
open Ast
open Instructions

type terminator =
  | Seq
  | Jump of int (* addr *)
  | Branch of int * expr (* (addr, cond) - jumps if cond == 0 *)
  | Switch0 of int * expr
  | DoWhile0 of int (* addr of branching basic block *)
[@@deriving show { with_path = false }]

let seq_terminator = { txt = Seq; addr = -1; end_addr = -1 }

type fragment = terminator loc * Ast.statement loc list
[@@deriving show { with_path = false }]

type 'a basic_block = {
  addr : int;
  end_addr : int;
  labels : label loc list;
  code : 'a;
  mutable nr_jump_srcs : int;
}
[@@deriving show { with_path = false }]

type t = fragment basic_block [@@deriving show { with_path = false }]

let negate = function UnaryOp (NOT, e) -> e | e -> UnaryOp (NOT, e)

let branch_target = function
  | JUMP addr -> Some addr
  | IFZ addr -> Some addr
  | IFNZ addr -> Some addr
  | SH_IF_LOC_LT_IMM (_, _, addr) -> Some addr
  | SH_IF_LOC_GT_IMM (_, _, addr) -> Some addr
  | SH_IF_LOC_GE_IMM (_, _, addr) -> Some addr
  | SH_IF_LOC_NE_IMM (_, _, addr) -> Some addr
  | SH_IF_STRUCTREF_Z (_, addr) -> Some addr
  | SH_IF_STRUCT_A_NOT_EMPTY (_, addr) -> Some addr
  | SH_IF_SREF_NE_STR0 (_, addr) -> Some addr
  | SH_IF_STRUCTREF_GT_IMM (_, _, addr) -> Some addr
  | SH_IF_STRUCTREF_NE_IMM (_, _, addr) -> Some addr
  | SH_IF_STRUCTREF_EQ_IMM (_, _, addr) -> Some addr
  | SH_IF_STRUCTREF_NE_LOCALREF (_, _, addr) -> Some addr
  | _ -> None

let make_basic_blocks func_end_addr code =
  let head_addrs = Hashtbl.create (module Int) in
  let add d labels addr =
    let labels =
      List.map labels ~f:(fun label -> { txt = label; addr; end_addr = addr })
    in
    Hashtbl.update head_addrs addr ~f:(function
      | None -> (d, labels)
      | Some (n, labels') -> (n + d, labels @ labels'))
  in
  let add_case_addrs sw_id is_str =
    let sw = Ain.ain.swi0.(sw_id) in
    Array.iter sw.cases ~f:(function case ->
        let label =
          if is_str then
            CaseStr (sw_id, Ain.ain.str0.(Int32.to_int_exn case.value))
          else CaseInt (sw_id, case.value)
        in
        add 1 [ label ] (Int32.to_int_exn case.address));
    add 1 [ Default sw_id ] (Int32.to_int_exn sw.default_address)
  in
  let rec scan = function
    | { txt = SWITCH n; _ } :: tl ->
        add_case_addrs n false;
        add_and_scan tl
    | { txt = STRSWITCH n; _ } :: tl ->
        add_case_addrs n true;
        add_and_scan tl
    | { txt = op; _ } :: tl -> (
        match branch_target op with
        | Some addr ->
            add 1 [] addr;
            add_and_scan tl
        | None -> scan tl)
    | [] -> ()
  and add_and_scan code =
    match code with
    | hd :: _ ->
        add 0 [] hd.addr;
        scan code
    | [] -> ()
  in
  add_and_scan code;
  let rec aux acc = function
    | (inst : instruction loc) :: tl ->
        let insts, rest =
          List.split_while tl ~f:(function { addr; _ } ->
              not (Hashtbl.mem head_addrs addr))
        in
        let end_addr =
          match rest with { addr; _ } :: _ -> addr | [] -> func_end_addr
        in
        let nr_jump_srcs, labels = Hashtbl.find_exn head_addrs inst.addr in
        let basic_block =
          {
            addr = inst.addr;
            end_addr;
            labels;
            code = inst :: insts;
            nr_jump_srcs;
          }
        in
        aux (basic_block :: acc) rest
    | [] -> List.rev acc
  in
  aux [] code

type analyze_context = {
  func : Ain.Function.t;
  struc : Ain.Struct.t option;
  parent : Ain.Function.t option;
  mutable instructions : instruction loc list;
  mutable address : int;
  mutable end_address : int;
  mutable stack : expr list;
  mutable stmts : statement loc list;
}

let fetch_instruction ctx =
  match ctx.instructions with
  | [] -> failwith "unexpected end of basic block"
  | inst :: tl ->
      ctx.instructions <- tl;
      inst.txt

let current_address ctx =
  match ctx.instructions with hd :: _ -> hd.addr | [] -> ctx.end_address

let push ctx expr = ctx.stack <- expr :: ctx.stack
let pushl ctx exprs = ctx.stack <- List.rev_append exprs ctx.stack

let pop ctx =
  match ctx.stack with
  | [] -> failwith "stack underflow"
  | hd :: tl ->
      ctx.stack <- tl;
      hd

let pop2 ctx =
  match ctx.stack with
  | b :: a :: tl ->
      ctx.stack <- tl;
      (a, b)
  | _ -> failwith "stack underflow"

let pop_n ctx n =
  let es, rest = List.split_n ctx.stack n in
  ctx.stack <- rest;
  List.rev es

let update_stack ctx f = ctx.stack <- f ctx.stack

let take_stack ctx =
  let stack = ctx.stack in
  ctx.stack <- [];
  stack

let assert_stack_empty ctx =
  match take_stack ctx with
  | [] -> ()
  | stack ->
      Stdio.eprintf "0x%08x: Warning: Non-empty stack at statement end: %s\n"
        (current_address ctx)
        ([%show: expr list] stack)

let emit_statement ctx stmt =
  let end_addr = current_address ctx in
  ctx.stmts <- { addr = ctx.address; end_addr; txt = stmt } :: ctx.stmts;
  ctx.address <- end_addr

let emit_expression ctx expr =
  assert_stack_empty ctx;
  emit_statement ctx (Expression expr)

let take_stmts ctx =
  let stmts = ctx.stmts in
  ctx.stmts <- [];
  stmts

let unexpected_stack name stack =
  Printf.failwithf "%s: unexpected stack structure %s" name
    ([%derive.show: expr list] stack)
    ()

let varref ctx page n =
  match page with
  | GlobalPage -> Ain.ain.glob.(n)
  | LocalPage -> ctx.func.vars.(n)
  | StructPage -> (Option.value_exn ctx.struc).members.(n)
  | ParentPage -> (Option.value_exn ctx.parent).vars.(n)

let pageref ctx page n = PageRef (page, varref ctx page n)

let lvalue ctx page slot =
  match (page, slot) with
  | Number -1l, Number 0l -> NullRef
  | Page page, Number n -> pageref ctx page (Int32.to_int_exn n)
  | DerefRef lval, Void -> RefRef lval
  | Deref lval, Void -> lval
  | e, Void -> RefValue e
  | _, _ -> ObjRef (page, slot)

let delegate_value obj func =
  match (obj, func) with
  | _, Number func_no ->
      BoundMethod (obj, Ain.ain.func.(Int32.to_int_exn func_no))
  | Number -1l, DelegateCast _ -> func
  | _, _ -> failwith "oops"

let convert_stack_top_to_delegate ctx =
  update_stack ctx (function
    | func :: obj :: stack -> delegate_value obj func :: stack
    | stack -> unexpected_stack "convert_stack_top_to_delegate" stack)

let ref_ ctx =
  update_stack ctx (function
    | slot :: page :: stack -> Deref (lvalue ctx page slot) :: stack
    | stack -> unexpected_stack "ref" stack)

let refref ctx =
  update_stack ctx (function
    | slot :: page :: stack -> Void :: DerefRef (lvalue ctx page slot) :: stack
    | stack -> unexpected_stack "refref" stack)

let sr_ref ctx n =
  update_stack ctx (function
    | slot :: page :: stack ->
        DerefStruct (n, Deref (lvalue ctx page slot)) :: stack
    | stack -> unexpected_stack "sr_ref" stack)

let sr_ref2 ctx n =
  update_stack ctx (function
    | expr :: stack -> DerefStruct (n, expr) :: stack
    | stack -> unexpected_stack "sr_ref2" stack)

let new_ ctx struc _func =
  if Ain.ain.vers > 8 then push ctx (New struc)
  else
    update_stack ctx (function
      | Number struc :: stack -> New (Int32.to_int_exn struc) :: stack
      | stack -> unexpected_stack "NEW" stack)

let unary_op ctx op =
  update_stack ctx (function
    | v :: stack -> UnaryOp (op, v) :: stack
    | stack -> unexpected_stack (show_instruction op) stack)

let binary_op ctx op =
  update_stack ctx (function
    | rhs :: lhs :: stack -> BinaryOp (op, lhs, rhs) :: stack
    | stack -> unexpected_stack (show_instruction op) stack)

let ref_binary_op ctx op =
  update_stack ctx (function
    | rslot :: rpage :: lslot :: lpage :: stack ->
        BinaryOp
          ( op,
            DerefRef (lvalue ctx lpage lslot),
            DerefRef (lvalue ctx rpage rslot) )
        :: stack
    | stack -> unexpected_stack (show_instruction op) stack)

let assign_op ctx op =
  update_stack ctx (function
    | value :: slot :: page :: stack ->
        AssignOp (op, lvalue ctx page slot, value) :: stack
    | stack -> unexpected_stack (show_instruction op) stack)

let assign_op2 ctx op =
  update_stack ctx (function
    | value :: Deref lvalue :: stack -> AssignOp (op, lvalue, value) :: stack
    | stack -> unexpected_stack (show_instruction op) stack)

let r_assign ctx =
  update_stack ctx (function
    | src_slot :: src_page :: dst_slot :: dst_page :: stack ->
        Void
        :: AssignOp
             ( R_ASSIGN,
               lvalue ctx dst_page dst_slot,
               DerefRef (lvalue ctx src_page src_slot) )
        :: stack
    | stack -> unexpected_stack "R_ASSIGN" stack)

let builtin ctx insn nr_args =
  let args = pop_n ctx nr_args in
  update_stack ctx (function
    | slot :: page :: rest ->
        Call (Builtin (insn, lvalue ctx page slot), args) :: rest
    | stack -> unexpected_stack (show_instruction insn) (List.rev args @ stack))

let builtin2 ctx insn nr_args =
  let args = pop_n ctx nr_args in
  update_stack ctx (function
    | expr :: rest -> Call (Builtin2 (insn, expr), args) :: rest
    | stack -> unexpected_stack (show_instruction insn) (List.rev args @ stack))

let s_erase2 ctx =
  match take_stack ctx with
  | [ Number 1l; index; str ] ->
      emit_expression ctx (Call (Builtin2 (S_ERASE2, str), [ index ]))
  | stack -> unexpected_stack "S_ERASE2" stack

let ft_assigns ctx =
  update_stack ctx (function
    | Number functype :: str :: slot :: page :: stack ->
        AssignOp
          ( PSEUDO_FT_ASSIGNS (Int32.to_int_exn functype),
            lvalue ctx page slot,
            str )
        :: stack
    | stack -> unexpected_stack "FT_ASSIGNS" stack)

let c_ref ctx =
  update_stack ctx (function
    | i :: str :: stack -> C_Ref (str, i) :: stack
    | stack -> unexpected_stack "C_REF" stack)

let c_assign ctx =
  update_stack ctx (function
    | c :: i :: str :: stack -> C_Assign (str, i, c) :: stack
    | stack -> unexpected_stack "C_ASSIGN" stack)

let sr_assign ctx =
  if Ain.ain.vers <= 1 || Ain.ain.vers >= 11 then
    update_stack ctx (function
      | value :: Deref lvalue :: stack ->
          AssignOp (SR_ASSIGN, lvalue, value) :: stack
      | stack -> unexpected_stack "SR_ASSIGN" stack)
  else
    update_stack ctx (function
      | Number _struct_id :: value :: Deref lvalue :: stack ->
          AssignOp (SR_ASSIGN, lvalue, value) :: stack
      | stack -> unexpected_stack "SR_ASSIGN" stack)

let a_alloc ctx insn =
  match take_stack ctx with
  | Number rank :: stack -> (
      match List.split_n stack (Int32.to_int_exn rank) with
      | dims, [ slot; page ] ->
          emit_expression ctx
            (Call (Builtin (insn, lvalue ctx page slot), List.rev dims))
      | _ -> unexpected_stack (show_instruction insn) (Number rank :: stack))
  | stack -> unexpected_stack (show_instruction insn) stack

let objswap ctx type_ =
  if Ain.ain.vers > 8 then
    match take_stack ctx with
    | [ slot2; page2; slot1; page1 ] ->
        BinaryOp
          ( OBJSWAP type_,
            Deref (lvalue ctx page1 slot1),
            Deref (lvalue ctx page2 slot2) )
    | stack -> unexpected_stack "OBJSWAP" stack
  else
    match take_stack ctx with
    | [ Number type_; slot2; page2; slot1; page1 ] ->
        BinaryOp
          ( OBJSWAP (Int32.to_int_exn type_),
            Deref (lvalue ctx page1 slot1),
            Deref (lvalue ctx page2 slot2) )
    | stack -> unexpected_stack "OBJSWAP" stack

let incdec ctx op =
  let consume_localref varno =
    match ctx.instructions with
    | { txt = PUSHLOCALPAGE; _ }
      :: { txt = PUSH varno'; _ }
      :: { txt = REF; _ }
      :: rest
      when Int32.equal varno varno' ->
        ctx.instructions <- rest;
        true
    | _ -> false
  in
  update_stack ctx (function
    | slot :: page :: slot' :: page' :: stack'
      when phys_equal page page' && phys_equal slot slot' ->
        Void :: Deref (IncDec (Prefix, op, lvalue ctx page slot)) :: stack'
    (* Stack structure after the post-increment sequence (DUP2, REF, DUP_X2, POP, INC) *)
    | Number slot :: Page page :: Deref (PageRef (_, var) as lval) :: stack'
      when phys_equal var (varref ctx page (Int32.to_int_exn slot)) ->
        Deref (IncDec (Postfix, op, lval)) :: stack'
    | slot1
      :: Deref obj1
      :: Deref (ObjRef (Deref obj2, slot2) as operand)
      :: stack'
      when phys_equal obj1 obj2 && phys_equal slot1 slot2 ->
        Deref (IncDec (Postfix, op, operand)) :: stack'
    | Void :: DerefRef lval :: Deref (RefRef lval') :: stack'
      when phys_equal lval lval' ->
        Deref (IncDec (Postfix, op, lval)) :: stack'
    (* index variable of foreach statement. `.LOCALINC var; .LOCALREF var` *)
    | [ Number slot; Page LocalPage ] when consume_localref slot ->
        [
          Deref
            (IncDec (Prefix, op, pageref ctx LocalPage (Int32.to_int_exn slot)));
        ]
    | stack -> unexpected_stack (show_incdec_op op) stack)

let pop_args ctx vartypes =
  let rec aux acc (vartypes : Ain.type_t list) =
    match vartypes with
    | [] -> acc
    | Void :: ts -> aux acc ts
    | Ref (Int | LongInt | Bool | Float) :: ts ->
        let page, slot = pop2 ctx in
        aux (Deref (lvalue ctx page slot) :: acc) ts
    | HllFunc2 :: ts -> (
        match pop2 ctx with
        | obj, Number fno ->
            aux
              (BoundMethod (obj, Ain.ain.func.(Int32.to_int_exn fno)) :: acc)
              ts
        | a, b -> unexpected_stack "pop_args" (a :: b :: ctx.stack))
    | _ :: ts ->
        let arg = pop ctx in
        aux (arg :: acc) ts
  in
  aux [] (List.rev vartypes)

let rec reshape_args ctx (vartypes : Ain.type_t list) args =
  match (vartypes, args) with
  | [], [] -> []
  | _ :: Void :: ts, page :: slot :: args ->
      Deref (lvalue ctx page slot) :: reshape_args ctx ts args
  | _ :: ts, arg :: args -> arg :: reshape_args ctx ts args
  | _ -> failwith "reshape_args: argument count mismatch"

let determine_functype ctx = function
  | -1l ->
      let functype_name =
        match ctx.func.name with
        | "SP_SELECT" -> "select_callback_t"
        | "message" ->
            if Ain.ain.vers <= 5 then "sact_message_callback_t" else "FTMessage"
        | "tagScrollBar@scroll" -> "ftScrollCallback"
        | "tagScrollBar@checkWheel" -> "ftWheelCallback"
        | "tagBattleScroll@scroll" -> "ftScrollCallback"
        | "T_ScrollBar@scroll" -> "ftScrollCallback"
        | "T_ScrollBar@checkWheel" -> "ftWheelCallback"
        | "T_DragMouse@run" -> "ftDropCallback"
        | "T_DragMouse@setPos" -> "ftDragCallback"
        | "SYS_CallShowMessageWindowCallbackFuncList" ->
            "FTShowMessageWindowCallback"
        | "CMessageTextView@_DrawChar" -> "FTDrawMessageChar"
        | _ -> failwith ("Cannot determine functype in " ^ ctx.func.name)
      in
      Array.find_exn Ain.ain.fnct ~f:(fun f ->
          String.equal f.name functype_name)
  | n -> Ain.ain.fnct.(Int32.to_int_exn n)

let sh_apushback_localsref ctx page slot local =
  Call
    ( Builtin (A_PUSHBACK, pageref ctx page slot),
      [ Deref (pageref ctx LocalPage local) ] )

let sh_sassign_sref ctx page slot =
  match take_stack ctx with
  | [ Deref lval ] -> AssignOp (S_ASSIGN, lval, Deref (pageref ctx page slot))
  | stack -> unexpected_stack "sh_sassign_sref" stack

let sh_sref_ne_str0 ctx page slot strno =
  push ctx
    (BinaryOp
       (S_NOTE, Deref (pageref ctx page slot), String Ain.ain.str0.(strno)))

(* Analyzes a basic block. *)
let analyze ctx =
  let terminator = ref None in
  let set_terminator term =
    assert (List.is_empty ctx.instructions);
    terminator :=
      Some { txt = term; addr = ctx.address; end_addr = current_address ctx }
  in
  while not (List.is_empty ctx.instructions) do
    match fetch_instruction ctx with
    (* --- Stack Management --- *)
    | PUSH n -> push ctx (Number n)
    | POP | DG_POP -> (
        match pop ctx with
        | Void | Number _ | Page _ | Deref (PageRef _) ->
            (* Can be discarded safely *) ()
        | e when List.is_empty ctx.stack -> emit_expression ctx e
        | (AssignOp _ | Call _) as e ->
            (* Occurs during assignment to a reference *)
            emit_statement ctx (Expression e)
        | e -> unexpected_stack "POP" (e :: ctx.stack))
    | DELETE -> (
        match pop ctx with
        | Deref (PageRef _ | ObjRef _ | RefRef _)
        | DerefRef (PageRef _ | ObjRef _ | RefRef _) ->
            ()
        | e when List.is_empty ctx.stack -> emit_expression ctx e
        | e -> unexpected_stack "DELETE" (e :: ctx.stack))
    | SP_INC -> (
        match pop ctx with
        | AssignOp _ as e when List.is_empty ctx.stack -> emit_expression ctx e
        | _ -> () (* reference counting is implicit *))
    | CHECKUDO -> (
        match pop ctx with
        | Deref (PageRef (LocalPage, _)) -> ()
        | e -> unexpected_stack "CHECKUDO" (e :: ctx.stack))
    | F_PUSH f -> push ctx (Float f)
    | REF -> ref_ ctx
    | REFREF -> refref ctx
    | DUP ->
        update_stack ctx (function
          | x :: stack -> x :: x :: stack
          | stack -> unexpected_stack "DUP" stack)
    | DUP2 ->
        update_stack ctx (function
          | a :: b :: stack -> a :: b :: a :: b :: stack
          | stack -> unexpected_stack "DUP2" stack)
    | DUP_X2 -> (
        match List.hd ctx.instructions with
        | Some { txt = POP; _ } ->
            fetch_instruction ctx |> ignore;
            update_stack ctx (function
              | a :: b :: c :: stack -> b :: c :: a :: stack
              | stack -> unexpected_stack "DUP_X2; POP" stack)
        | _ ->
            update_stack ctx (function
              | a :: b :: c :: stack -> a :: b :: c :: a :: stack
              | stack -> unexpected_stack "DUP_X2" stack))
    | DUP2_X1 ->
        update_stack ctx (function
          | a :: b :: c :: stack -> a :: b :: c :: a :: b :: stack
          | stack -> unexpected_stack "DUP2_X1" stack)
    | DUP_U2 ->
        update_stack ctx (function
          | a :: b :: stack -> b :: a :: b :: stack
          | stack -> unexpected_stack "DUP_U2" stack)
    | SWAP ->
        update_stack ctx (function
          | a :: b :: stack -> b :: a :: stack
          | stack -> unexpected_stack "SWAP" stack)
    (* --- Variables --- *)
    | PUSHGLOBALPAGE -> push ctx (Page GlobalPage)
    | PUSHLOCALPAGE -> push ctx (Page LocalPage)
    | PUSHSTRUCTPAGE -> push ctx (Page StructPage)
    | X_GETENV -> (
        match pop ctx with
        | Page LocalPage -> push ctx (Page ParentPage)
        | e -> unexpected_stack "X_GETENV" (e :: ctx.stack))
    | (S_ASSIGN | DG_ASSIGN) as op -> assign_op2 ctx op
    | SH_GLOBALREF n -> push ctx (Deref (pageref ctx GlobalPage n))
    | SH_LOCALREF n -> push ctx (Deref (pageref ctx LocalPage n))
    | SH_STRUCTREF n -> push ctx (Deref (pageref ctx StructPage n))
    | SH_LOCALASSIGN (var, value) ->
        emit_expression ctx
          (AssignOp
             (ASSIGN, PageRef (LocalPage, ctx.func.vars.(var)), Number value))
    | SH_LOCALINC var ->
        emit_expression ctx
          (Deref
             (IncDec
                (Prefix, Increment, PageRef (LocalPage, ctx.func.vars.(var)))))
    | SH_LOCALDEC var ->
        emit_expression ctx
          (Deref
             (IncDec
                (Prefix, Decrement, PageRef (LocalPage, ctx.func.vars.(var)))))
    | SH_LOCALDELETE _slot -> (* ignore *) ()
    | SH_LOCALCREATE (var, _struct) ->
        assert_stack_empty ctx;
        emit_statement ctx (VarDecl (ctx.func.vars.(var), None))
    | R_ASSIGN -> r_assign ctx
    | NEW (struc, func) -> new_ ctx struc func
    | OBJSWAP type_ -> emit_expression ctx (objswap ctx type_)
    (* --- Control Flow --- *)
    | CALLFUNC n -> (
        let func = Ain.ain.func.(n) in
        let args = pop_args ctx (Ain.Function.arg_types func) in
        let e = Call (Function func, args) in
        match func.return_type with
        | Void -> emit_expression ctx e
        | Ref (Int | Bool | LongInt | Float) -> pushl ctx [ e; Void ]
        | _ -> push ctx e)
    | CALLFUNC2 -> (
        match pop2 ctx with
        | func, Number fnct -> (
            let functype = determine_functype ctx fnct in
            let args = pop_args ctx (Ain.FuncType.arg_types functype) in
            let e = Call (FuncPtr (functype, func), args) in
            match functype.return_type with
            | Void -> emit_expression ctx e
            | Ref (Int | Bool | LongInt | Float) -> pushl ctx [ e; Void ]
            | _ -> push ctx e)
        | a, b -> unexpected_stack "CALLFUNC2" (a :: b :: ctx.stack))
    | PSEUDO_DG_CALL n -> (
        let dg_type = Ain.ain.delg.(n) in
        let args = pop_args ctx (Ain.FuncType.arg_types dg_type) in
        let delg = pop ctx in
        let e = Call (Delegate (dg_type, delg), args) in
        match dg_type.return_type with
        | Void -> emit_expression ctx e
        | Ref (Int | Bool | LongInt | Float) -> pushl ctx [ e; Void ]
        | _ -> push ctx e)
    | CALLMETHOD n -> (
        if Ain.ain.vers >= 11 then
          let args = pop_n ctx n in
          match pop2 ctx with
          | this, Number fid -> (
              let func = Ain.ain.func.(Int32.to_int_exn fid) in
              let e =
                Call
                  ( Method (this, func),
                    reshape_args ctx (Ain.Function.arg_types func) args )
              in
              match func.return_type with
              | Void -> emit_expression ctx e
              | Ref (Int | Bool | LongInt | Float) -> pushl ctx [ e; Void ]
              | _ -> push ctx e)
          | a, b -> unexpected_stack "CALLMETHOD" (a :: b :: ctx.stack)
        else
          let func = Ain.ain.func.(n) in
          let args = pop_args ctx (Ain.Function.arg_types func) in
          let this = pop ctx in
          let e = Call (Method (this, func), args) in
          match func.return_type with
          | Void -> emit_expression ctx e
          | Ref (Int | Bool | LongInt | Float) -> pushl ctx [ e; Void ]
          | _ -> push ctx e)
    | CALLHLL (lib_id, func_id, type_param) -> (
        let lib = Ain.ain.hll0.(lib_id) in
        let func = lib.functions.(func_id) in
        let args = pop_args ctx (Ain.HLL.arg_types func) in
        let e = Call (HllFunc (lib.name, func), args) in
        match Type.replace_hll_param func.return_type type_param with
        | Void -> emit_expression ctx e
        | Ref (Int | Bool | LongInt | Float) -> pushl ctx [ e; Void ]
        | _ -> push ctx e)
    | RETURN -> (
        match (ctx.func.return_type, take_stack ctx) with
        | Void, [] -> emit_statement ctx (Return None)
        | _, [ v ] -> emit_statement ctx (Return (Some v))
        | Ref (Int | Bool | LongInt | Float), [ slot; obj ] ->
            emit_statement ctx (Return (Some (Deref (lvalue ctx obj slot))))
        | _, stack -> unexpected_stack "RETURN" stack)
    | CALLSYS n -> (
        let syscall = syscalls.(n) in
        let args = pop_args ctx syscall.arg_types in
        let e = Call (SysCall n, args) in
        match syscall.return_type with
        | Void -> emit_expression ctx e
        | Ref (Int | Bool | LongInt | Float) -> pushl ctx [ e; Void ]
        | _ -> push ctx e)
    | CALLONJUMP -> ()
    | SJUMP -> (
        match take_stack ctx with
        | [ String s ] -> emit_statement ctx (ScenarioJump s)
        | stack -> unexpected_stack "SJUMP" stack)
    | MSG n ->
        assert_stack_empty ctx;
        emit_statement ctx (Msg (Ain.ain.msg.(n), None))
    | JUMP addr -> set_terminator (Jump addr)
    | IFZ addr -> set_terminator (Branch (addr, pop ctx))
    | IFNZ addr -> set_terminator (Branch (addr, negate (pop ctx)))
    | SH_IF_LOC_LT_IMM (local, imm, addr) ->
        let e =
          BinaryOp (GTE, Deref (pageref ctx LocalPage local), Number imm)
        in
        set_terminator (Branch (addr, e))
    | SH_IF_LOC_GT_IMM (local, imm, addr) ->
        let e =
          BinaryOp (LTE, Deref (pageref ctx LocalPage local), Number imm)
        in
        set_terminator (Branch (addr, e))
    | SH_IF_LOC_GE_IMM (local, imm, addr) ->
        let e =
          BinaryOp (LT, Deref (pageref ctx LocalPage local), Number imm)
        in
        set_terminator (Branch (addr, e))
    | SH_IF_LOC_NE_IMM (local, imm, addr) ->
        let e =
          BinaryOp (EQUALE, Deref (pageref ctx LocalPage local), Number imm)
        in
        set_terminator (Branch (addr, e))
    | SH_IF_STRUCTREF_Z (memb, addr) ->
        let e =
          BinaryOp (NOTE, Deref (pageref ctx StructPage memb), Number 0l)
        in
        set_terminator (Branch (addr, e))
    | SH_IF_STRUCT_A_NOT_EMPTY (memb, addr) ->
        let e = Call (Builtin (A_EMPTY, pageref ctx StructPage memb), []) in
        set_terminator (Branch (addr, e))
    | SH_IF_SREF_NE_STR0 (strno, addr) ->
        update_stack ctx (function
          | slot :: page :: stack ->
              BinaryOp
                ( S_EQUALE,
                  Deref (lvalue ctx page slot),
                  String Ain.ain.str0.(strno) )
              :: stack
          | stack -> unexpected_stack "SH_IF_SREF_NE_STR0" stack);
        set_terminator (Branch (addr, pop ctx))
    | SH_IF_STRUCTREF_GT_IMM (memb, imm, addr) ->
        let e =
          BinaryOp (LTE, Deref (pageref ctx StructPage memb), Number imm)
        in
        set_terminator (Branch (addr, e))
    | SH_IF_STRUCTREF_NE_IMM (memb, imm, addr) ->
        let e =
          BinaryOp (EQUALE, Deref (pageref ctx StructPage memb), Number imm)
        in
        set_terminator (Branch (addr, e))
    | SH_IF_STRUCTREF_EQ_IMM (memb, imm, addr) ->
        let e =
          BinaryOp (NOTE, Deref (pageref ctx StructPage memb), Number imm)
        in
        set_terminator (Branch (addr, e))
    | SH_IF_STRUCTREF_NE_LOCALREF (memb, local, addr) ->
        let e =
          BinaryOp
            ( EQUALE,
              Deref (pageref ctx StructPage memb),
              Deref (pageref ctx LocalPage local) )
        in
        set_terminator (Branch (addr, e))
    | SWITCH id -> set_terminator (Switch0 (id, pop ctx))
    | STRSWITCH id -> set_terminator (Switch0 (id, pop ctx))
    | ASSERT -> (
        match take_stack ctx with
        | [ _line; _file; _expr; expr ] -> emit_statement ctx (Assert expr)
        | stack -> unexpected_stack "ASSERT" stack)
    (* --- Arithmetic --- *)
    | (INV | NOT | COMPL | ITOB | ITOF | ITOLI | FTOI | F_INV | I_STRING | STOI)
      as op ->
        unary_op ctx op
    | ( ADD | SUB | MUL | DIV | MOD | LT | GT | LTE | GTE | NOTE | EQUALE | AND
      | OR | XOR | LSHIFT | RSHIFT | F_ADD | F_SUB | F_MUL | F_DIV | F_LT | F_GT
      | F_LTE | F_GTE | F_EQUALE | F_NOTE | LI_ADD | LI_SUB | LI_MUL | LI_DIV
      | LI_MOD | S_PLUSA | S_PLUSA2 | S_ADD | S_LT | S_GT | S_LTE | S_GTE
      | S_NOTE | S_EQUALE | DG_PLUSA | DG_MINUSA ) as op ->
        binary_op ctx op
    | ( ASSIGN | F_ASSIGN | LI_ASSIGN | PLUSA | MINUSA | MULA | DIVA | MODA
      | ANDA | ORA | XORA | LSHIFTA | RSHIFTA | F_PLUSA | F_MINUSA | F_MULA
      | F_DIVA | LI_PLUSA | LI_MINUSA | LI_MULA | LI_DIVA | LI_MODA | LI_ANDA
      | LI_ORA | LI_XORA | LI_LSHIFTA | LI_RSHIFTA ) as op ->
        assign_op ctx op
    | INC | LI_INC -> incdec ctx Increment
    | DEC | LI_DEC -> incdec ctx Decrement
    | (R_EQUALE | R_NOTE) as op -> ref_binary_op ctx op
    (* --- Strings --- *)
    | S_PUSH n ->
        let tbl = if Ain.ain.vers = 0 then Ain.ain.msg else Ain.ain.str0 in
        push ctx (String tbl.(n))
    | S_POP -> emit_expression ctx (pop ctx)
    | S_REF -> ref_ ctx
    | S_MOD t ->
        let t =
          if Ain.ain.vers <= 8 then
            match pop ctx with
            | Number t -> Int32.to_int_exn t
            | e ->
                Printf.failwithf "S_MOD: unexpected argument %s" (show_expr e)
                  ()
          else t
        in
        binary_op ctx (S_MOD t)
    | S_LENGTH -> builtin ctx S_LENGTH 0
    | S_LENGTH2 -> builtin2 ctx S_LENGTH2 0
    | S_LENGTHBYTE -> builtin ctx S_LENGTHBYTE 0
    | S_EMPTY -> builtin2 ctx S_EMPTY 0
    | S_FIND -> builtin2 ctx S_FIND 1
    | S_GETPART -> builtin2 ctx S_GETPART 2
    | S_PUSHBACK2 ->
        builtin2 ctx S_PUSHBACK2 1;
        emit_expression ctx (pop ctx)
    | S_POPBACK2 ->
        builtin2 ctx S_POPBACK2 0;
        emit_expression ctx (pop ctx)
    | S_ERASE2 -> s_erase2 ctx
    | FTOS -> builtin2 ctx FTOS 1
    | FT_ASSIGNS -> ft_assigns ctx
    | C_REF -> c_ref ctx
    | C_ASSIGN -> c_assign ctx
    (* --- Structs --- *)
    | SR_REF struct_id -> sr_ref ctx struct_id
    | SR_REF2 struct_id -> sr_ref2 ctx struct_id
    | SR_POP -> emit_expression ctx (pop ctx)
    | SR_ASSIGN -> sr_assign ctx
    (* --- Arrays --- *)
    | A_NUMOF -> builtin ctx A_NUMOF 1
    | A_ALLOC -> a_alloc ctx A_ALLOC
    | A_REALLOC -> a_alloc ctx A_REALLOC
    | A_FREE ->
        builtin ctx A_FREE 0;
        emit_expression ctx (pop ctx)
    | A_REF -> ()
    | A_EMPTY -> builtin ctx A_EMPTY 0
    | A_COPY -> builtin ctx A_COPY 4
    | A_FILL -> builtin ctx A_FILL 3
    | A_PUSHBACK ->
        builtin ctx A_PUSHBACK 1;
        emit_expression ctx (pop ctx)
    | A_POPBACK ->
        builtin ctx A_POPBACK 0;
        emit_expression ctx (pop ctx)
    | A_INSERT ->
        builtin ctx A_INSERT 2;
        emit_expression ctx (pop ctx)
    | A_ERASE -> builtin ctx A_ERASE 1
    | A_SORT ->
        if Ain.ain.vers >= 8 then convert_stack_top_to_delegate ctx;
        builtin ctx A_SORT 1;
        emit_expression ctx (pop ctx)
    | A_SORT_MEM ->
        builtin ctx A_SORT_MEM 1;
        emit_expression ctx (pop ctx)
    | A_FIND ->
        if Ain.ain.vers >= 8 then convert_stack_top_to_delegate ctx;
        builtin ctx A_FIND 4
    | A_REVERSE ->
        builtin ctx A_REVERSE 0;
        emit_expression ctx (pop ctx)
    | SH_SR_ASSIGN -> (
        match take_stack ctx with
        | [ slot; page; Deref lval ] ->
            emit_expression ctx
              (AssignOp (SR_ASSIGN, lval, Deref (lvalue ctx page slot)))
        | stack -> unexpected_stack "SH_SR_ASSIGN" stack)
    | SH_MEM_ASSIGN_LOCAL (memb, local) ->
        emit_expression ctx
          (AssignOp
             ( ASSIGN,
               PageRef (StructPage, (Option.value_exn ctx.struc).members.(memb)),
               Deref (pageref ctx LocalPage local) ))
    | A_NUMOF_GLOB_1 var ->
        push ctx
          (Call (Builtin (A_NUMOF, pageref ctx GlobalPage var), [ Number 1l ]))
    | A_NUMOF_STRUCT_1 var ->
        push ctx
          (Call (Builtin (A_NUMOF, pageref ctx StructPage var), [ Number 1l ]))
    | DG_COPY -> ()
    | DG_NEW -> push ctx Null
    | DG_CLEAR ->
        builtin2 ctx DG_CLEAR 0;
        emit_expression ctx (pop ctx)
    | DG_NUMOF -> builtin2 ctx DG_NUMOF 0
    | DG_NEW_FROM_METHOD -> convert_stack_top_to_delegate ctx
    | (DG_SET | DG_ADD) as op -> (
        match take_stack ctx with
        | [ func; obj; Deref lvalue ] ->
            emit_expression ctx (AssignOp (op, lvalue, delegate_value obj func))
        | stack -> unexpected_stack (show_instruction op) stack)
    | DG_ERASE -> (
        match take_stack ctx with
        | [ func; obj; Deref lvalue ] ->
            emit_expression ctx
              (Call (Builtin (DG_ERASE, lvalue), [ delegate_value obj func ]))
        | stack -> unexpected_stack "DG_ERASE" stack)
    | DG_EXIST ->
        update_stack ctx (function
          | Number func_no :: obj :: delg :: stack ->
              let arg =
                BoundMethod (obj, Ain.ain.func.(Int32.to_int_exn func_no))
              in
              Call (Builtin2 (DG_EXIST, delg), [ arg ]) :: stack
          | stack -> unexpected_stack "DG_EXIST" stack)
    | DG_STR_TO_METHOD dg_type ->
        if Ain.ain.vers > 8 then
          update_stack ctx (function
            | str :: stack -> DelegateCast (str, dg_type) :: stack
            | stack -> unexpected_stack "DG_STR_TO_METHOD" stack)
        else
          update_stack ctx (function
            | Number dg_type :: str :: stack ->
                DelegateCast (str, Int32.to_int_exn dg_type) :: stack
            | stack -> unexpected_stack "DG_STR_TO_METHOD" stack)
    | SH_MEM_ASSIGN_IMM (slot, value) ->
        emit_expression ctx
          (AssignOp
             ( ASSIGN,
               PageRef (StructPage, (Option.value_exn ctx.struc).members.(slot)),
               Number value ))
    | SH_LOCALREFREF var ->
        pushl ctx [ DerefRef (pageref ctx LocalPage var); Void ]
    | SH_LOCALASSIGN_SUB_IMM (local, imm) ->
        emit_expression ctx
          (AssignOp (MINUSA, pageref ctx LocalPage local, Number imm))
    | SH_LOCREF_ASSIGN_MEM (local, memb) ->
        assert_stack_empty ctx;
        emit_expression ctx
          (AssignOp
             ( ASSIGN,
               RefRef (pageref ctx LocalPage local),
               Deref (pageref ctx StructPage memb) ))
    | PAGE_REF slot ->
        push ctx (Number slot);
        ref_ ctx
    | SH_GLOBAL_ASSIGN_LOCAL (glob, local) ->
        emit_expression ctx
          (AssignOp
             ( ASSIGN,
               pageref ctx GlobalPage glob,
               Deref (pageref ctx LocalPage local) ))
    | SH_LOCAL_ASSIGN_STRUCTREF (local, memb) ->
        emit_expression ctx
          (AssignOp
             ( ASSIGN,
               pageref ctx LocalPage local,
               Deref (pageref ctx StructPage memb) ))
    | SH_STRUCTREF_CALLMETHOD_NO_PARAM (memb, func) -> (
        let func = Ain.ain.func.(func) in
        let e = Call (Method (Deref (pageref ctx StructPage memb), func), []) in
        match func.return_type with
        | Void -> emit_expression ctx e
        | Ref (Int | Bool | LongInt | Float) -> pushl ctx [ e; Void ]
        | _ -> push ctx e)
    | SH_STRUCTREF2 (memb, slot) ->
        push ctx
          (Deref
             (lvalue ctx (Deref (pageref ctx StructPage memb)) (Number slot)))
    | SH_REF_STRUCTREF2 (slot1, slot2) ->
        update_stack ctx (function
          | page :: stack' ->
              let e = Deref (lvalue ctx page (Number slot1)) in
              let e = Deref (lvalue ctx e (Number slot2)) in
              e :: stack'
          | stack -> unexpected_stack "SH_REF_STRUCTREF2" stack)
    | SH_STRUCTREF3 (memb, slot1, slot2) ->
        let e = Deref (pageref ctx StructPage memb) in
        let e = Deref (lvalue ctx e (Number slot1)) in
        let e = Deref (lvalue ctx e (Number slot2)) in
        push ctx e
    | SH_STRUCTREF2_CALLMETHOD_NO_PARAM (memb, slot, func) -> (
        let func = Ain.ain.func.(func) in
        let lhs =
          lvalue ctx (Deref (pageref ctx StructPage memb)) (Number slot)
        in
        let e = Call (Method (Deref lhs, func), []) in
        match func.return_type with
        | Void -> emit_expression ctx e
        | Ref (Int | Bool | LongInt | Float) -> pushl ctx [ e; Void ]
        | _ -> push ctx e)
    | THISCALLMETHOD_NOPARAM n -> (
        let func = Ain.ain.func.(n) in
        let e = Call (Method (Page StructPage, func), []) in
        match func.return_type with
        | Void -> emit_expression ctx e
        | Ref (Int | Bool | LongInt | Float) -> pushl ctx [ e; Void ]
        | _ -> push ctx e)
    | SH_GLOBAL_ASSIGN_IMM (var, value) ->
        let e = AssignOp (ASSIGN, pageref ctx GlobalPage var, Number value) in
        emit_expression ctx e
    | SH_LOCALSTRUCT_ASSIGN_IMM (local, slot, imm) ->
        let e = Deref (pageref ctx LocalPage local) in
        let e = AssignOp (ASSIGN, lvalue ctx e (Number slot), Number imm) in
        emit_expression ctx e
    | SH_STRUCT_A_PUSHBACK_LOCAL_STRUCT (memb, local) ->
        emit_expression ctx
          (Call
             ( Builtin (A_PUSHBACK, pageref ctx StructPage memb),
               [ Deref (pageref ctx LocalPage local) ] ))
    | SH_GLOBAL_A_PUSHBACK_LOCAL_STRUCT (glob, local) ->
        emit_expression ctx
          (Call
             ( Builtin (A_PUSHBACK, pageref ctx GlobalPage glob),
               [ Deref (pageref ctx LocalPage local) ] ))
    | SH_LOCAL_A_PUSHBACK_LOCAL_STRUCT (arrayvar, structvar) ->
        emit_expression ctx
          (Call
             ( Builtin (A_PUSHBACK, pageref ctx LocalPage arrayvar),
               [ Deref (pageref ctx LocalPage structvar) ] ))
    | SH_S_ASSIGN_REF -> (
        match take_stack ctx with
        | [ slot; page; Deref lval ] ->
            let e = AssignOp (S_ASSIGN, lval, Deref (lvalue ctx page slot)) in
            emit_expression ctx e
        | stack -> unexpected_stack "SH_S_ASSIGN_REF" stack)
    | SH_A_FIND_SREF ->
        update_stack ctx (function
          | slot :: page :: stack ->
              Number 0l :: Deref (lvalue ctx page slot) :: stack
          | stack -> unexpected_stack "SH_A_FIND_SREF" stack);
        builtin ctx A_FIND 4
    | SH_SREF_EMPTY -> builtin ctx S_EMPTY 0
    | SH_STRUCTSREF_EQ_LOCALSREF (memb, local) ->
        push ctx
          (BinaryOp
             ( S_EQUALE,
               Deref (pageref ctx StructPage memb),
               Deref (pageref ctx LocalPage local) ))
    | SH_STRUCTSREF_NE_LOCALSREF (memb, local) ->
        push ctx
          (BinaryOp
             ( S_NOTE,
               Deref (pageref ctx StructPage memb),
               Deref (pageref ctx LocalPage local) ))
    | SH_LOCALSREF_EQ_STR0 (local, strno) ->
        push ctx
          (BinaryOp
             ( S_EQUALE,
               Deref (pageref ctx LocalPage local),
               String Ain.ain.str0.(strno) ))
    | SH_LOCALSREF_NE_STR0 (local, strno) ->
        sh_sref_ne_str0 ctx LocalPage local strno
    | SH_STRUCTSREF_NE_STR0 (memb, strno) ->
        sh_sref_ne_str0 ctx StructPage memb strno
    | SH_GLOBALSREF_NE_STR0 (glob, strno) ->
        sh_sref_ne_str0 ctx GlobalPage glob strno
    | SH_STRUCTREF_GT_IMM (memb, imm) ->
        push ctx
          (BinaryOp (GT, Deref (pageref ctx StructPage memb), Number imm))
    | SH_STRUCT_ASSIGN_LOCALREF_ITOB (memb, local) ->
        emit_expression ctx
          (AssignOp
             ( ASSIGN,
               pageref ctx StructPage memb,
               UnaryOp (ITOB, Deref (pageref ctx LocalPage local)) ))
    | SH_STRUCT_SR_REF (memb, struc) ->
        push ctx (DerefStruct (struc, Deref (pageref ctx StructPage memb)))
    | SH_STRUCT_S_REF slot -> push ctx (Deref (pageref ctx StructPage slot))
    | S_REF2 slot ->
        push ctx (Number slot);
        ref_ ctx
    | SH_GLOBAL_S_REF var -> push ctx (Deref (pageref ctx GlobalPage var))
    | SH_LOCAL_S_REF var -> push ctx (Deref (pageref ctx LocalPage var))
    | SH_LOCALREF_SASSIGN_LOCALSREF (lvar, rvar) ->
        emit_expression ctx
          (AssignOp
             ( S_ASSIGN,
               pageref ctx LocalPage lvar,
               Deref (pageref ctx LocalPage rvar) ))
    | SH_LOCAL_APUSHBACK_LOCALSREF (arrayvar, strvar) ->
        emit_expression ctx
          (sh_apushback_localsref ctx LocalPage arrayvar strvar)
    | SH_GLOBAL_APUSHBACK_LOCALSREF (glob, local) ->
        emit_expression ctx (sh_apushback_localsref ctx GlobalPage glob local)
    | SH_STRUCT_APUSHBACK_LOCALSREF (memb, local) ->
        emit_expression ctx (sh_apushback_localsref ctx StructPage memb local)
    | SH_S_ASSIGN_CALLSYS19 -> (
        match take_stack ctx with
        | [ expr; Deref lval ] ->
            emit_expression ctx
              (AssignOp (S_ASSIGN, lval, Call (SysCall 19, [ expr ])))
        | stack -> unexpected_stack "SH_S_ASSIGN_CALLSYS19" stack)
    | SH_S_ASSIGN_STR0 n -> (
        match take_stack ctx with
        | [ Deref lval ] ->
            emit_expression ctx
              (AssignOp (S_ASSIGN, lval, String Ain.ain.str0.(n)))
        | stack -> unexpected_stack "SH_S_ASSIGN_STR0" stack)
    | SH_SASSIGN_LOCALSREF local ->
        emit_expression ctx (sh_sassign_sref ctx LocalPage local)
    | SH_SASSIGN_STRUCTSREF memb ->
        emit_expression ctx (sh_sassign_sref ctx StructPage memb)
    | SH_SASSIGN_GLOBALSREF glob ->
        emit_expression ctx (sh_sassign_sref ctx GlobalPage glob)
    | SH_STRUCTREF_SASSIGN_LOCALSREF (memb, local) ->
        emit_expression ctx
          (AssignOp
             ( S_ASSIGN,
               pageref ctx StructPage memb,
               Deref (pageref ctx LocalPage local) ))
    | SH_LOCALSREF_EMPTY var ->
        push ctx
          (Call (Builtin2 (S_EMPTY, Deref (pageref ctx LocalPage var)), []))
    | SH_STRUCTSREF_EMPTY memb ->
        push ctx
          (Call (Builtin2 (S_EMPTY, Deref (pageref ctx StructPage memb)), []))
    | SH_GLOBALSREF_EMPTY var ->
        push ctx
          (Call (Builtin2 (S_EMPTY, Deref (pageref ctx GlobalPage var)), []))
    | SH_LOC_LT_IMM_OR_LOC_GE_IMM (local, imm1, imm2) ->
        let v = Deref (pageref ctx LocalPage local) in
        push ctx
          (BinaryOp
             ( PSEUDO_LOGOR,
               BinaryOp (LT, v, Number imm1),
               BinaryOp (GTE, v, Number imm2) ))
    | insn ->
        Printf.failwithf "Unknown instruction %s" (show_instruction insn) ()
  done;
  ( Option.value !terminator ~default:seq_terminator,
    take_stack ctx,
    take_stmts ctx )

let rec analyze_basic_blocks ctx stack = function
  | [] ->
      List.map stack ~f:(fun bb ->
          match bb.code with
          | b, [], ss -> { bb with code = (b, ss) }
          | _ ->
              Printf.failwithf "non-empty stack in analyzed basic block: %s"
                ([%show:
                   (terminator loc * expr list * statement loc list) basic_block]
                   bb)
                ())
      |> List.rev
  | bb :: rest ->
      ctx.instructions <- bb.code;
      ctx.address <-
        (match List.hd ctx.stmts with None -> bb.addr | Some s -> s.end_addr);
      ctx.end_address <- bb.end_addr;
      let fragment = analyze ctx in
      let stack = { bb with code = fragment } :: stack in
      reduce ctx stack rest

and reduce ctx stack rest =
  assert (List.is_empty ctx.stmts);
  match stack with
  (* && operator *)
  | { addr = label1; end_addr; code = { txt = Seq; _ }, [ Number 0l ], []; _ }
    :: { code = { txt = Jump label2; _ }, [ Number 1l ], []; _ }
    :: { code = { txt = Branch (label1', rhs); _ }, [], []; _ }
    :: ({ code = { txt = Branch (label1'', lhs); _ }, estack, stmts; _ } as top)
    :: stack'
    when label1 = label1' && label1 = label1'' && label2 = end_addr -> (
      match rest with
      | bb' :: rest' ->
          let bbs =
            { top with code = bb'.code; end_addr = bb'.end_addr } :: rest'
          in
          analyze_basic_blocks
            {
              ctx with
              stack = BinaryOp (PSEUDO_LOGAND, lhs, rhs) :: estack;
              stmts;
            }
            stack' bbs
      | [] -> failwith "unexpected end of function")
  (* || operator *)
  | { addr = label1; end_addr; code = { txt = Seq; _ }, [ Number 1l ], []; _ }
    :: { code = { txt = Jump label2; _ }, [ Number 0l ], []; _ }
    :: { code = { txt = Branch (label1', rhs); _ }, [], []; _ }
    :: ({ code = { txt = Branch (label1'', lhs); _ }, estack, stmts; _ } as top)
    :: stack'
    when label1 = label1' && label1 = label1'' && label2 = end_addr -> (
      match rest with
      | bb' :: rest' ->
          let bbs =
            { top with code = bb'.code; end_addr = bb'.end_addr } :: rest'
          in
          analyze_basic_blocks
            {
              ctx with
              stack = BinaryOp (PSEUDO_LOGOR, negate lhs, negate rhs) :: estack;
              stmts;
            }
            stack' bbs
      | [] -> failwith "unexpected end of function")
  (* ?: operator *)
  | { addr = label1; end_addr; code = { txt = Seq; _ }, [ c ], []; _ }
    :: { code = { txt = Jump label2; _ }, [ b ], []; _ }
    :: ({ code = { txt = Branch (label1', a); _ }, estack, stmts; _ } as top)
    :: stack'
    when label1 = label1' && label2 = end_addr ->
      let top' =
        {
          top with
          end_addr;
          code = (seq_terminator, TernaryOp (a, b, c) :: estack, stmts);
        }
      in
      reduce ctx (top' :: stack') rest
  (* ?: operator with type coercion *)
  | {
      addr = label1;
      end_addr = label2';
      code = { txt = Jump label3; _ }, [ c ], [];
      _;
    }
    :: { code = { txt = Jump label2; _ }, [ b ], []; _ }
    :: ({ code = { txt = Branch (label1', a); _ }, estack, stmts; _ } as top)
    :: stack'
    when label1 = label1' && label2 = label2' && label3 = label2 + 2 -> (
      match rest with
      | { code = [ { txt = ITOF; _ } ]; _ } :: rest ->
          let top' =
            {
              top with
              end_addr = label3;
              code =
                ( seq_terminator,
                  TernaryOp (a, UnaryOp (ITOF, b), c) :: estack,
                  stmts );
            }
          in
          reduce ctx (top' :: stack') rest
      | _ -> failwith "not implemented")
  | ({ code = { txt = Seq; _ }, (_ :: _ as estack), stmts; _ } as top) :: stack'
    -> (
      match rest with
      | bb' :: rest' ->
          let bbs =
            { top with code = bb'.code; end_addr = bb'.end_addr } :: rest'
          in
          analyze_basic_blocks { ctx with stack = estack; stmts } stack' bbs
      | [] -> failwith "unexpected end of function")
  | stack' ->
      analyze_basic_blocks { ctx with stack = []; stmts = [] } stack' rest

let rec replace_delegate_calls acc = function
  | { addr = addr1; txt = DG_CALLBEGIN dg_type; _ }
    :: { addr = addr2; txt = DG_CALL (dg_type', addr4); _ }
    :: { addr = addr3; txt = JUMP addr2' as jump_op; end_addr }
    :: rest
    when dg_type = dg_type' && addr2 = addr2'
         && addr4 = addr3 + Instructions.width jump_op ->
      replace_delegate_calls
        ({ addr = addr1; end_addr; txt = PSEUDO_DG_CALL dg_type } :: acc)
        rest
  | insn :: rest -> replace_delegate_calls (insn :: acc) rest
  | [] -> List.rev acc

let create (f : CodeSection.function_t) =
  f.code |> replace_delegate_calls []
  |> make_basic_blocks f.end_addr
  |> analyze_basic_blocks
       {
         func = f.func;
         struc = f.struc;
         parent = f.parent;
         instructions = [];
         address = -1;
         end_address = -1;
         stack = [];
         stmts = [];
       }
       []

let generate_var_decls (func : Ain.Function.t) bbs =
  let uninitialized_vars =
    ref (List.drop (Array.to_list func.vars) func.nr_args)
  in
  let mark_use var =
    uninitialized_vars :=
      List.filter !uninitialized_vars ~f:(fun v -> not (phys_equal v var))
  in
  let is_uninitialized var =
    if Stdlib.List.memq var !uninitialized_vars then (
      mark_use var;
      true)
    else false
  in
  let replace_stmt = function
    | VarDecl (var, None) as stmt ->
        mark_use var;
        stmt
    | Expression (AssignOp (insn, PageRef (LocalPage, var), expr))
      when is_uninitialized var ->
        VarDecl (var, Some (insn, expr))
    | Expression (Call (Builtin (A_ALLOC, PageRef (LocalPage, var)), _) as expr)
      when is_uninitialized var ->
        VarDecl (var, Some (ASSIGN, expr))
    | Expression (Call (Builtin (A_FREE, PageRef (LocalPage, var)), []))
      when is_uninitialized var ->
        VarDecl (var, None)
    | Expression
        (Call (Builtin2 (DG_CLEAR, Deref (PageRef (LocalPage, var))), []))
      when is_uninitialized var ->
        VarDecl (var, None)
    | stmt -> stmt
  in
  List.map bbs ~f:(function { code = terminator, stmts; _ } as bb ->
      let stmts' =
        List.rev_map (List.rev stmts) ~f:(fun stmt ->
            { stmt with txt = replace_stmt stmt.txt })
      in
      { bb with code = (terminator, stmts') })
