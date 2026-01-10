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

let ( == ) = phys_equal
let negate = function UnaryOp (NOT, e) -> e | e -> UnaryOp (NOT, e)

let are_negations e1 e2 =
  match (e1, e2) with
  | UnaryOp (NOT, e1), e2 when e1 == e2 -> true
  | e1, UnaryOp (NOT, e2) when e1 == e2 -> true
  | _ -> false

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

type predecessor = {
  condition : expr list;
  stack : expr list;
  stmts : Ast.statement loc list;
}
[@@deriving show { with_path = false }]

type analyze_context = {
  func : Ain.Function.t;
  struc : Ain.Struct.t option;
  parent : CodeSection.function_t option;
  mutable instructions : instruction loc list;
  mutable address : int;
  mutable end_address : int;
  mutable stack : expr list;
  mutable stmts : statement loc list;
  mutable condition : expr list;
  predecessors : (int, predecessor basic_block list) Hashtbl.t;
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
  | ParentPage level ->
      let rec loop (f : CodeSection.function_t) = function
        | 0 -> f.func.vars.(n)
        | n -> loop (Option.value_exn f.parent) (n - 1)
      in
      loop (Option.value_exn ctx.parent) level

let pageref ctx page n = PageRef (page, varref ctx page n)

let lvalue ctx page slot =
  match (page, slot) with
  | Number -1l, Number 0l -> NullRef
  | Page page, Number n -> pageref ctx page (Int32.to_int_exn n)
  | DerefRef lval, Void -> RefRef lval
  | Deref lval, Void -> lval
  | e, Void -> RefValue e
  | _, _ -> ObjRef (page, slot)

let rec interface_value obj vofs =
  match (obj, vofs) with
  | TernaryOp (c1, a1, b1), TernaryOp (c2, a2, b2) when c1 == c2 ->
      TernaryOp (c1, interface_value a1 a2, interface_value b1 b2)
  | Number -1l, Number 0l -> DerefRef NullRef
  | _, Void -> DerefRef (RefValue obj)
  | _, _ -> DerefRef (ObjRef (obj, vofs))

let resolve_method ctx obj index =
  let fid =
    match
      (new TypeAnalysis.analyzer ctx.func ctx.struc)#analyze_expr Any obj
    with
    | _, (Struct s | Ref (Struct s)) -> Ain.ain.strt.(s).vtable.(index)
    | _, (IFace iface | Ref (IFace iface)) -> (
        match Ain.ain.strt.(iface).implementers with
        | [] -> Ain.ain.strt.(iface).vtable.(index)
        | implementer :: _ ->
            let index = implementer.vtable_offset + index in
            Ain.ain.strt.(implementer.struct_type).vtable.(index))
    | _, t ->
        failwith
          ("resolve_method: non-struct/interface type " ^ Type.show_ain_type t)
  in
  Ain.ain.func.(fid)

let delegate_value ctx obj func =
  match (obj, func) with
  | _, Number func_no ->
      BoundMethod (obj, Ain.ain.func.(Int32.to_int_exn func_no))
  | Number -1l, DelegateCast _ -> func
  | ( _,
      Deref
        (ObjRef
           (Deref (ObjRef (obj', Number 0l)), BinaryOp (ADD, Void, Number index)))
    )
    when obj == obj' ->
      BoundMethod (obj, resolve_method ctx obj (Int32.to_int_exn index))
  | _, _ ->
      Printf.failwithf "cannot create delegate value:\nobj = %s\nfunc=%s"
        (show_expr obj) (show_expr func) ()

let convert_stack_top_to_delegate ctx =
  update_stack ctx (function
    | func :: obj :: stack -> delegate_value ctx obj func :: stack
    | stack -> unexpected_stack "convert_stack_top_to_delegate" stack)

let ref_ ctx =
  update_stack ctx (function
    | TernaryOp (cond, l12, l22) :: TernaryOp (cond', l11, l21) :: stack
      when cond == cond' ->
        TernaryOp (cond, Deref (lvalue ctx l11 l12), Deref (lvalue ctx l21 l22))
        :: stack
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

let unary_op ctx op =
  update_stack ctx (function
    | v :: stack -> UnaryOp (op, v) :: stack
    | stack -> unexpected_stack (show_instruction op) stack)

let binary_op ctx op =
  update_stack ctx (function
    | rhs :: lhs :: stack -> BinaryOp (op, lhs, rhs) :: stack
    | stack -> unexpected_stack (show_instruction op) stack)

let lift_ternary_fatref ctx page slot =
  match (page, slot) with
  | TernaryOp (c, p1, p2), TernaryOp (c', s1, s2) when c == c' ->
      TernaryOp (c, DerefRef (lvalue ctx p1 s1), DerefRef (lvalue ctx p2 s2))
  | _ -> DerefRef (lvalue ctx page slot)

let ref_binary_op ctx op =
  update_stack ctx (function
    | rslot :: rpage :: lslot :: lpage :: stack ->
        BinaryOp
          ( op,
            lift_ternary_fatref ctx lpage lslot,
            lift_ternary_fatref ctx rpage rslot )
        :: stack
    | stack -> unexpected_stack (show_instruction op) stack)

let assign_op ctx op =
  update_stack ctx (function
    | value :: slot :: page :: stack -> (
        let lhs = lvalue ctx page slot in
        match (op, lhs, slot, ctx.instructions) with
        | ( (ASSIGN | F_ASSIGN),
            PageRef (LocalPage, v),
            Number varno',
            { txt = POP; _ }
            :: { txt = PUSHLOCALPAGE; _ }
            :: { txt = PUSH varno; _ }
            :: rest )
          when Int32.(varno = varno')
               && Type.is_scalar v.type_
               && String.is_suffix v.name ~suffix:" : 右辺値参照化用>" ->
            ctx.instructions <- rest;
            Void :: RvalueRef (v, value) :: stack
        | _ -> AssignOp (op, lhs, value) :: stack)
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
      | value
        :: (AssignOp (ASSIGN, PageRef (LocalPage, v), _) as assign)
        :: stack
        when Ain.Variable.is_dummy v ->
          AssignOp (SR_ASSIGN, RefValue assign, value) :: stack
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
    | slot1 :: obj1 :: Deref (ObjRef (obj2, slot2) as operand) :: stack'
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
    | t :: ts when Type.is_fat_reference t ->
        let page, slot = pop2 ctx in
        aux (Deref (lvalue ctx page slot) :: acc) ts
    | IFace _ :: ts ->
        let obj, vofs = pop2 ctx in
        aux (interface_value obj vofs :: acc) ts
    | (HllFunc | HllFunc2) :: ts ->
        let obj, func = pop2 ctx in
        aux (delegate_value ctx obj func :: acc) ts
    | _ :: ts ->
        let arg = pop ctx in
        aux (arg :: acc) ts
  in
  aux [] (List.rev vartypes)

let new_ ctx struc func =
  if Ain.ain.vers < 11 then
    update_stack ctx (function
      | Number struc :: stack ->
          New { struc = Int32.to_int_exn struc; func = -1; args = [] } :: stack
      | stack -> unexpected_stack "NEW" stack)
  else if func = -1 then push ctx (New { struc; func = -1; args = [] })
  else
    let f = Ain.ain.func.(func) in
    let args = pop_args ctx (Ain.Function.arg_types f) in
    push ctx (New { struc; func; args })

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

let is_null_in_this_branch ctx expr =
  List.exists ctx.condition ~f:(function
    | BinaryOp (EQUALE, (Option e | e), Number -1l) -> (
        contains_expr expr e
        ||
        match e with
        | Deref l -> contains_expr expr (DerefRef l)
        | _ -> false)
    | _ -> false)

let push_call_result ctx (return_type : Ain.type_t) e =
  match return_type with
  | Void -> emit_expression ctx e
  | Option _ -> pushl ctx [ e; Option e ]
  | t when Type.is_fat t -> pushl ctx [ e; Void ]
  | _ -> push ctx e

let x_icast ctx struc =
  let obj = pop ctx in
  let e = InterfaceCast (struc, obj) in
  pushl ctx [ e; Void; Option e ]

let array_literal expr =
  let rec unfold args = function
    | Call (HllFunc ("Array", { name = "PushBack"; _ }), [ e; arg ]) ->
        unfold (arg :: args) e
    | Call (HllFunc ("Array", { name = "Free"; _ }), [ Deref lval ]) ->
        AssignOp (PSEUDO_ARRAY_ASSIGN, lval, ArrayLiteral args)
    | e ->
        Printf.failwithf "array_literal: unexpected expression %s" (show_expr e)
          ()
  in
  unfold [] expr

let ain11_callmethod ctx nr_args =
  let args = pop_n ctx nr_args in
  let obj, func_expr = pop2 ctx in
  let func =
    match func_expr with
    | Number fid -> Ain.ain.func.(Int32.to_int_exn fid)
    | Deref (ObjRef (_, BinaryOp (ADD, (Number 0l | Void), Number index))) ->
        resolve_method ctx obj (Int32.to_int_exn index)
    | _ -> unexpected_stack "CALLMETHOD" (func_expr :: obj :: ctx.stack)
  in
  let e =
    Call
      (Method (obj, func), reshape_args ctx (Ain.Function.arg_types func) args)
  in
  match (func, ctx.stack) with
  | { kind = Setter prop; _ }, Number 0l :: obj' :: stack when obj == obj' -> (
      match (ctx.instructions, List.hd_exn args) with
      | ( { txt = POP; _ }
          :: { txt = PUSH fid; _ }
          :: { txt = CALLMETHOD 0; _ }
          :: insns,
          BinaryOp
            ( insn,
              Call (Method (obj', { id = fid'; kind = Getter prop'; _ }), []),
              rhs ) )
        when obj == obj'
             && Int32.to_int_exn fid = fid'
             && String.equal prop prop' ->
          ctx.instructions <- insns;
          ctx.stack <- stack;
          let op = Instructions.to_assign_op insn in
          push ctx (PropertySet { obj; op; func; rhs })
      | _ -> emit_expression ctx e)
  | { kind = Setter _; _ }, e :: stack when e == List.hd_exn args ->
      ctx.stack <- stack;
      push ctx (PropertySet { obj; op = ASSIGN; func; rhs = List.hd_exn args })
  | { return_type = Void; _ }, _ -> emit_expression ctx e
  | _, _ -> push_call_result ctx func.return_type e

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
        | Void | Number _ | Page _
        | BinaryOp (MUL, _, Number 2l) (* index to interface array *)
        | TernaryOp (_, (Void | Number _), (Void | Number _))
        | Deref (PageRef _)
        | DerefRef (PageRef _)
        | Option _ ->
            (* Can be discarded safely *) ()
        | AssignOp
            ( ASSIGN,
              PageRef (LocalPage, { type_ = Struct _ | Ref _ | IFace _; _ }),
              Number -1l )
          when Ain.ain.vers >= 12 ->
            (* .LOCALDELETE, ignore *) ()
        | e when is_null_in_this_branch ctx e -> ()
        | e when List.is_empty ctx.stack -> emit_expression ctx e
        | (AssignOp _ | Call _) as e ->
            (* Occurs during assignment to a reference *)
            emit_statement ctx (Expression e)
        | e -> unexpected_stack "POP" (e :: ctx.stack))
    | DELETE -> (
        match pop ctx with
        | Deref (PageRef _ | ObjRef _ | RefRef _)
        | DerefRef (PageRef _ | ObjRef _ | RefRef _)
        | BoundMethod _ ->
            ()
        | e when is_null_in_this_branch ctx e -> ()
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
        | Page (ParentPage level) -> push ctx (Page (ParentPage (level + 1)))
        | Page LocalPage -> push ctx (Page (ParentPage 0))
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
    | CALLFUNC n ->
        let func = Ain.ain.func.(n) in
        let args = pop_args ctx (Ain.Function.arg_types func) in
        push_call_result ctx func.return_type (Call (Function func, args))
    | CALLFUNC2 -> (
        match pop2 ctx with
        | func, Number fnct ->
            let functype = determine_functype ctx fnct in
            let args = pop_args ctx (Ain.FuncType.arg_types functype) in
            let e = Call (FuncPtr (functype, func), args) in
            push_call_result ctx functype.return_type e
        | a, b -> unexpected_stack "CALLFUNC2" (a :: b :: ctx.stack))
    | PSEUDO_DG_CALL n ->
        let dg_type = Ain.ain.delg.(n) in
        let args = pop_args ctx (Ain.FuncType.arg_types dg_type) in
        let delg = pop ctx in
        push_call_result ctx dg_type.return_type
          (Call (Delegate (dg_type, delg), args))
    | CALLMETHOD n ->
        if Ain.ain.vers >= 11 then ain11_callmethod ctx n
        else
          let func = Ain.ain.func.(n) in
          let args = pop_args ctx (Ain.Function.arg_types func) in
          let this = pop ctx in
          let e = Call (Method (this, func), args) in
          push_call_result ctx func.return_type e
    | CALLHLL (lib_id, func_id, type_param) -> (
        let lib = Ain.ain.hll0.(lib_id) in
        let func = lib.functions.(func_id) in
        let args =
          pop_args ctx
            (Ain.HLL.arg_types func
            |> List.map ~f:(Type.replace_hll_param type_param))
        in
        let e = Call (HllFunc (lib.name, func), args) in
        match (lib.name, func.name, ctx.stack) with
        | "Array", ("Free" | "PushBack"), array :: stack
          when List.hd_exn args == array -> (
            match ctx.instructions with
            | { txt = DUP; _ } :: { txt = SP_INC; _ } :: _ ->
                ctx.stack <- array_literal e :: stack
            | { txt = DUP; _ } :: _ -> ctx.stack <- e :: stack
            | _ -> ctx.stack <- array_literal e :: stack)
        | _ ->
            push_call_result ctx
              (Type.replace_hll_param type_param func.return_type)
              e)
    | RETURN -> (
        match (ctx.func.return_type, take_stack ctx) with
        | Void, [] -> emit_statement ctx (Return None)
        | _, [ v ] -> emit_statement ctx (Return (Some v))
        | t, [ slot; obj ] when Type.is_fat_reference t ->
            emit_statement ctx
              (Return (Some (lift_ternary_fatref ctx obj slot)))
        | IFace _, [ vofs; obj ] ->
            emit_statement ctx (Return (Some (interface_value obj vofs)))
        | _, stack -> unexpected_stack "RETURN" stack)
    | CALLSYS n ->
        let syscall = syscalls.(n) in
        let args = pop_args ctx syscall.arg_types in
        let e = Call (SysCall n, args) in
        push_call_result ctx syscall.return_type e
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
      | S_NOTE | S_EQUALE | DG_PLUSA | DG_MINUSA | PSEUDO_NULL_COALESCE ) as op
      ->
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
    | X_SET -> builtin2 ctx X_SET 1
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
            emit_expression ctx
              (AssignOp (op, lvalue, delegate_value ctx obj func))
        | stack -> unexpected_stack (show_instruction op) stack)
    | DG_ERASE -> (
        match take_stack ctx with
        | [ func; obj; Deref lvalue ] ->
            emit_expression ctx
              (Call (Builtin (DG_ERASE, lvalue), [ delegate_value ctx obj func ]))
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
    | SH_STRUCTREF_CALLMETHOD_NO_PARAM (memb, func) ->
        let func = Ain.ain.func.(func) in
        let e = Call (Method (Deref (pageref ctx StructPage memb), func), []) in
        push_call_result ctx func.return_type e
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
    | SH_STRUCTREF2_CALLMETHOD_NO_PARAM (memb, slot, func) ->
        let func = Ain.ain.func.(func) in
        let lhs =
          lvalue ctx (Deref (pageref ctx StructPage memb)) (Number slot)
        in
        let e = Call (Method (Deref lhs, func), []) in
        push_call_result ctx func.return_type e
    | THISCALLMETHOD_NOPARAM n ->
        let func = Ain.ain.func.(n) in
        let e = Call (Method (Page StructPage, func), []) in
        push_call_result ctx func.return_type e
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
    | X_ICAST sno -> x_icast ctx sno
    | insn ->
        Printf.failwithf "Unknown instruction %s" (show_instruction insn) ()
  done;
  ( Option.value !terminator ~default:seq_terminator,
    take_stack ctx,
    take_stmts ctx )

let add_predecessor ctx addr predecessor =
  assert (ctx.end_address <= addr);
  Hashtbl.add_multi ctx.predecessors ~key:addr ~data:predecessor

let replace_top2_predecessors ctx addr predecessor =
  Hashtbl.update ctx.predecessors addr ~f:(function
    | Some (_ :: _ :: rest) -> predecessor :: rest
    | Some _ -> Printf.failwithf "only one predecessor at address %d" addr ()
    | None -> Printf.failwithf "no predecessors at address %d" addr ())

let make_option = function Option _ as obj -> obj | obj -> Option obj
let strip_option = function Option obj -> obj | obj -> obj

let merge_complemental_predecessors ctx (p1 : predecessor) (p2 : predecessor) =
  match (p1, p2) with
  (* {obj != -1} [e1]
     {obj == -1} [e2]
     => [e1{obj/Option(obj)} ?? e2] *)
  | ( { stack = e1 :: es1; _ },
      {
        condition =
          BinaryOp (EQUALE, (Option obj | obj), Number -1l) :: condition;
        stack = e2 :: es2;
        _;
      } )
    when Ain.ain.vers >= 11 && es1 == es2 && p1.stmts == p2.stmts ->
      Some
        {
          condition;
          stack =
            BinaryOp (PSEUDO_NULL_COALESCE, insert_option e1 obj, e2) :: es1;
          stmts = p1.stmts;
        }
  (* {obj != -1} [e, 0]
     {obj == -1} [-1, -1]
     => [e, Option(obj)] *)
  | ( { stack = Number 0l :: e :: es1; stmts; _ },
      {
        condition = BinaryOp (EQUALE, obj, Number -1l) :: condition;
        stack = Number -1l :: Number -1l :: es2;
        _;
      } )
    when es1 == es2 ->
      Some { condition; stack = make_option obj :: e :: es1; stmts }
  (* {obj != -1} [e, num, 0]
     {obj == -1} [-1, -1, -1]
     => [e, num, Option(obj)] *)
  | ( { stack = Number 0l :: (Number _ as n) :: e :: es1; stmts; _ },
      {
        condition = BinaryOp (EQUALE, obj, Number -1l) :: condition;
        stack = Number -1l :: Number -1l :: Number -1l :: es2;
        _;
      } )
    when es1 == es2 ->
      Some { condition; stack = make_option obj :: n :: e :: es1; stmts }
  (* expr?.iface_expr *)
  (* {Deref obj != -1} [e, Void, 0]
     {Deref obj == -1} [-1, -1, -1]
     => [e, Void, Option(DerefRef obj)] *)
  | ( { stack = Number 0l :: Void :: e :: es1; stmts; _ },
      {
        condition = BinaryOp (EQUALE, obj, Number -1l) :: condition;
        stack = Number -1l :: Number -1l :: Number -1l :: es2;
        _;
      } )
    when es1 == es2 ->
      let obj = match obj with Deref o -> DerefRef o | _ -> obj in
      Some { condition; stack = make_option obj :: Void :: e :: es1; stmts }
  (* obj?.void_method() *)
  (* {obj != -1} [e1] stmts=[stmt]
     {obj == -1} [-1] stmts=[]
     when e1 == 0 || (e1 == Option _ && e1 contains obj)
     => [Option(obj)] stmts=[stmt{obj/Option(obj)}] *)
  | ( {
        stack = e1 :: es1;
        stmts = ({ txt = Expression expr; _ } as stmt) :: stmts1;
        _;
      },
      {
        condition = BinaryOp (EQUALE, obj, Number -1l) :: condition;
        stack = Number -1l :: es2;
        stmts = stmts2;
      } )
    when es1 == es2 && stmts1 == stmts2
         &&
         match e1 with
         | Number 0l -> true
         | Option e -> contains_interface_expr e obj
         | _ -> false ->
      Some
        {
          condition;
          stack = Option obj :: es1;
          stmts =
            { stmt with txt = Expression (insert_option expr obj) } :: stmts1;
        }
  (* obj?.expr assign_op expr; *)
  (* {obj != -1} [] stmts=[stmt]
     {obj == -1} [] stmts=[]
     => [] stmts=[stmt{obj/Option(obj)}] *)
  | ( { stack = []; stmts = ({ txt = Expression expr; _ } as stmt) :: stmts1; _ },
      {
        condition = BinaryOp (EQUALE, Option obj, Number -1l) :: condition;
        stack = [];
        stmts = stmts2;
      } )
    when stmts1 == stmts2 ->
      Some
        {
          condition;
          stack = [];
          stmts =
            { stmt with txt = Expression (insert_option expr obj) } :: stmts1;
        }
  (* obj?.e1 ?? obj?.e2 *)
  (* {Option(obj) != -1} [e1, 0]
     {Option(obj) == -1} [e2, Option(obj2)]
     => [e1{obj/Option(obj)} ?? e2, Option(obj2)] *)
  | ( { stack = Number 0l :: e1 :: es2; _ },
      {
        condition = BinaryOp (EQUALE, Option obj, Number -1l) :: condition;
        stack = Option obj2 :: e2 :: es1;
        _;
      } )
    when es1 == es2 && p1.stmts == p2.stmts ->
      Some
        {
          condition;
          stack =
            Option obj2
            :: BinaryOp (PSEUDO_NULL_COALESCE, insert_option e1 obj, e2)
            :: es1;
          stmts = p1.stmts;
        }
  (* obj?.ref_expr ?? e *)
  (* {obj != -1} [e, Option(e')]
     {obj == -1} [-1, -1]
     when e contains e' and e' contains obj
     => [e, Option(obj)] *)
  | ( { stack = Option e' :: e :: es1; _ },
      {
        condition = BinaryOp (EQUALE, obj, Number -1l) :: condition;
        stack = Number -1l :: Number -1l :: es2;
        _;
      } )
    when es1 == es2 && contains_expr e e' && contains_interface_expr e' obj ->
      let e = if Poly.equal e e' then e else insert_option e e' in
      Some { condition; stack = make_option obj :: e :: es1; stmts = p1.stmts }
  (* obj?.fat_value ?? e *)
  (* {obj != -1} [e, e2, Option(e)]
     {obj == -1} [-1, -1, -1]
     when e contains obj
     => [e, e2, Option(obj)] *)
  | ( { stack = Option e :: e2 :: e' :: es1; _ },
      {
        condition = BinaryOp (EQUALE, obj, Number -1l) :: condition;
        stack = Number -1l :: Number -1l :: Number -1l :: es2;
        _;
      } )
    when Poly.equal e e' && es1 == es2
         && contains_interface_expr e (strip_option obj) ->
      Some
        {
          condition;
          stack = make_option obj :: e2 :: e' :: es1;
          stmts = p1.stmts;
        }
  (* {Option(obj) != -1} [LocalPage, slot] stmts=[local.slot = obj;]
     {Option(obj) == -1} [-1, 0] stmts=[]
     => [obj, Void]
     XXX: This removes assignment to <dummy : 右辺値参照化用> var *)
  | ( {
        stack = Number slot :: Page LocalPage :: es1;
        stmts =
          {
            txt = Expression (AssignOp (ASSIGN, PageRef (LocalPage, v), obj));
            _;
          }
          :: stmts;
        _;
      },
      {
        condition = BinaryOp (EQUALE, Option obj', Number -1l) :: condition;
        stack = Number 0l :: Number -1l :: es2;
        _;
      } )
    when obj == obj' && es1 == es2 && stmts == p2.stmts
         && ctx.func.vars.(Int32.to_int_exn slot) == v ->
      Some { condition; stack = Void :: obj :: es1; stmts }
  | _ -> None

let merge_predecessors ctx address (p1 : predecessor basic_block)
    (p2 : predecessor basic_block) =
  Option.value_or_thunk
    (match (p1.code, p2.code) with
    | ( {
          condition = UnaryOp (NOT, BinaryOp (EQUALE, obj, Number -1l)) :: cs1;
          _;
        },
        { condition = BinaryOp (EQUALE, obj', Number -1l) :: cs2; _ } )
      when obj == obj' && cs1 == cs2 ->
        merge_complemental_predecessors ctx p1.code p2.code
    | ( { condition = BinaryOp (EQUALE, obj', Number -1l) :: cs2; _ },
        {
          condition = UnaryOp (NOT, BinaryOp (EQUALE, obj, Number -1l)) :: cs1;
          _;
        } )
      when obj == obj' && cs1 == cs2 ->
        merge_complemental_predecessors ctx p2.code p1.code
    | _ -> None)
    ~default:(fun () ->
      match (p1.code, p2.code) with
      (* ?: operator *)
      | ( { condition = c1 :: cs1; stack = e1 :: es1; _ },
          { condition = c2 :: cs2; stack = e2 :: es2; _ } )
        when are_negations c1 c2 && cs1 == cs2 && es1 == es2
             && p1.code.stmts == p2.code.stmts ->
          let e =
            match c1 with
            | UnaryOp (NOT, _) when Ain.ain.vers >= 11 -> TernaryOp (c2, e2, e1)
            | _ -> TernaryOp (c1, e1, e2)
          in
          { condition = cs1; stack = e :: es1; stmts = p1.code.stmts }
      | ( { condition = c1 :: cs1; stack = e12 :: e11 :: es1; _ },
          { condition = c2 :: cs2; stack = e22 :: e21 :: es2; _ } )
        when are_negations c1 c2 && cs1 == cs2 && es1 == es2
             && p1.code.stmts == p2.code.stmts ->
          let stack =
            match c1 with
            | UnaryOp (NOT, _) ->
                TernaryOp (c2, e22, e12) :: TernaryOp (c2, e21, e11) :: es1
            | _ -> TernaryOp (c1, e12, e22) :: TernaryOp (c1, e11, e21) :: es1
          in
          { condition = cs1; stack; stmts = p1.code.stmts }
      (* && or || *)
      | { condition = c1 :: cs1; _ }, { condition = c2 :: c1' :: cs2; _ }
        when are_negations c1 c1' && cs1 == cs2
             && p1.code.stack == p2.code.stack
             && p1.code.stmts == p2.code.stmts ->
          { p1.code with condition = BinaryOp (PSEUDO_LOGOR, c1, c2) :: cs1 }
      (* && operator *)
      | ( { condition = c2 :: c1 :: cs1; stack = Number 1l :: es1; _ },
          {
            condition = BinaryOp (PSEUDO_LOGOR, c1', c2') :: cs2;
            stack = Number 0l :: es2;
            _;
          } )
        when are_negations c1 c1' && are_negations c2 c2' && cs1 == cs2
             && es1 == es2
             && p1.code.stmts == p2.code.stmts ->
          {
            condition = cs1;
            stack = BinaryOp (PSEUDO_LOGAND, c1, c2) :: es1;
            stmts = p1.code.stmts;
          }
      (* || operator *)
      | ( { condition = c2 :: c1 :: cs1; stack = Number 0l :: es1; _ },
          {
            condition = BinaryOp (PSEUDO_LOGOR, c1', c2') :: cs2;
            stack = Number 1l :: es2;
            _;
          } )
        when are_negations c1 c1' && are_negations c2 c2' && cs1 == cs2
             && es1 == es2
             && p1.code.stmts == p2.code.stmts ->
          {
            condition = cs1;
            stack = BinaryOp (PSEUDO_LOGOR, c1', c2') :: es1;
            stmts = p1.code.stmts;
          }
      | _ ->
          Printf.failwithf
            "cannot merge predecessors at 0x%x:\npred1 = %s\npred2 = %s" address
            ([%show: predecessor basic_block] p1)
            ([%show: predecessor basic_block] p2)
            ())
  |> fun code -> { p1 with code }

let rec analyze_basic_blocks ctx acc = function
  | [] -> List.rev acc
  | bb :: rest -> (
      let pred : predecessor basic_block =
        match Hashtbl.find_and_remove ctx.predecessors bb.addr with
        | None ->
            {
              bb with
              code = { condition = []; stack = []; stmts = [] };
              addr =
                (match List.hd ctx.stmts with
                | None -> bb.addr
                | Some s -> s.end_addr);
            }
        | Some preds ->
            List.reduce_exn preds ~f:(fun p1 p2 ->
                merge_predecessors ctx bb.addr p2 p1)
      in
      let bb =
        {
          bb with
          addr = pred.addr;
          labels = pred.labels;
          nr_jump_srcs = pred.nr_jump_srcs;
        }
      in
      ctx.condition <- pred.code.condition;
      ctx.stack <- pred.code.stack;
      ctx.stmts <- pred.code.stmts;
      ctx.instructions <- bb.code;
      ctx.address <-
        (match ctx.stmts with [] -> bb.addr | stmt :: _ -> stmt.end_addr);
      ctx.end_address <- bb.end_addr;
      match analyze ctx with
      | term, [], stmts when List.is_empty ctx.condition ->
          let acc = { bb with code = (term, stmts) } :: acc in
          reduce ctx acc rest
      | { txt = Branch (addr, cond); _ }, stack, stmts ->
          add_predecessor ctx addr
            {
              pred with
              code = { condition = negate cond :: ctx.condition; stack; stmts };
            };
          add_predecessor ctx bb.end_addr
            {
              pred with
              code = { condition = cond :: ctx.condition; stack; stmts };
            };
          reduce ctx acc rest
      | { txt = Jump addr; _ }, stack, stmts ->
          add_predecessor ctx addr
            { pred with code = { condition = ctx.condition; stack; stmts } };
          reduce ctx acc rest
      | { txt = Seq; _ }, stack, stmts ->
          add_predecessor ctx bb.end_addr
            { pred with code = { condition = ctx.condition; stack; stmts } };
          reduce ctx acc rest
      | _ -> failwith "cannot reduce")

and reduce ctx acc rest =
  assert (List.is_empty ctx.stmts);
  let predecessors =
    match rest with
    | [] -> None
    | bb :: _ ->
        Option.bind (Hashtbl.find ctx.predecessors bb.addr) ~f:(function
          | pred1 :: pred2 :: _ -> Some (pred1, pred2)
          | _ -> None)
  in
  match (acc, predecessors) with
  (* && operator *)
  | ( { code = { txt = Branch (label1', rhs); _ }, []; _ }
      :: ({ code = { txt = Branch (label1'', lhs); _ }, stmts; _ } as top)
      :: stack',
      Some
        ( ({ code = { stack = [ Number 0l ]; stmts = []; condition; _ }; _ } as
           pred1),
          ({ code = { stack = [ Number 1l ]; stmts = []; _ }; _ } as pred2) ) )
    when pred1.addr = label1' && pred1.addr = label1''
         && condition == pred2.code.condition ->
      replace_top2_predecessors ctx (List.hd_exn rest).addr
        {
          top with
          end_addr = pred1.end_addr;
          code =
            { condition; stack = [ BinaryOp (PSEUDO_LOGAND, lhs, rhs) ]; stmts };
        };
      analyze_basic_blocks ctx stack' rest
  (* || operator *)
  | ( { code = { txt = Branch (label1', rhs); _ }, []; _ }
      :: ({ code = { txt = Branch (label1'', lhs); _ }, stmts; _ } as top)
      :: stack',
      Some
        ( ({ code = { stack = [ Number 1l ]; stmts = []; condition; _ }; _ } as
           pred1),
          ({ code = { stack = [ Number 0l ]; stmts = []; _ }; _ } as pred2) ) )
    when pred1.addr = label1' && pred1.addr = label1''
         && condition == pred2.code.condition ->
      replace_top2_predecessors ctx (List.hd_exn rest).addr
        {
          top with
          end_addr = pred1.end_addr;
          code =
            {
              condition;
              stack = [ BinaryOp (PSEUDO_LOGOR, negate lhs, negate rhs) ];
              stmts;
            };
        };
      analyze_basic_blocks ctx stack' rest
  (* ?: operator *)
  | ( ({ code = { txt = Branch (label1', a); _ }, stmts; _ } as top) :: stack',
      Some
        ( ({ code = { stack = ([ _ ] | [ _; _ ]) as stack1; stmts = []; _ }; _ }
           as pred1),
          ({ code = { stack = stack2; stmts = []; _ }; _ } as pred2) ) )
    when (pred1.addr = label1' || pred2.addr = label1')
         && List.length stack1 = List.length stack2
         && pred1.code.condition == pred2.code.condition ->
      let stack =
        match (stack1, stack2) with
        | [ c ], [ b ] when pred1.addr = label1' -> [ TernaryOp (a, b, c) ]
        | [ b ], [ c ] when pred2.addr = label1' -> [ TernaryOp (a, b, c) ]
        | [ c2; c1 ], [ b2; b1 ] when pred1.addr = label1' ->
            [ TernaryOp (a, b2, c2); TernaryOp (a, b1, c1) ]
        | [ b2; b1 ], [ c2; c1 ] when pred2.addr = label1' ->
            [ TernaryOp (a, b2, c2); TernaryOp (a, b1, c1) ]
        | _ -> failwith "cannot happen"
      in
      replace_top2_predecessors ctx (List.hd_exn rest).addr
        {
          top with
          end_addr = pred1.end_addr;
          code = { condition = pred1.code.condition; stack; stmts };
        };
      reduce ctx stack' rest
  | stack', _ -> analyze_basic_blocks ctx stack' rest

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

let from_instructions (f : CodeSection.function_t) code =
  code |> replace_delegate_calls []
  |> make_basic_blocks f.end_addr
  |> analyze_basic_blocks
       {
         func = f.func;
         struc = (match f.owner with Some (Struct s) -> Some s | _ -> None);
         parent = f.parent;
         instructions = [];
         address = -1;
         end_address = -1;
         stack = [];
         stmts = [];
         condition = [];
         predecessors = Hashtbl.create (module Int);
       }
       []

let from_stmt (stmt : statement loc) =
  {
    addr = stmt.addr;
    end_addr = stmt.end_addr;
    labels = [];
    code = (seq_terminator, [ stmt ]);
    nr_jump_srcs = 0;
  }

let from_generated_constructor (s : Ain.Struct.t) (f : CodeSection.function_t) =
  match f.code with
  | { txt = PUSHSTRUCTPAGE; _ }
    :: { txt = PUSH varno; _ }
    :: { txt = REF; _ }
    :: { txt = DUP; _ }
    :: { txt = PUSH d1; _ }
    :: { txt = PUSH d2; _ }
    :: { txt = PUSH d3; _ }
    :: { txt = PUSH d4; _ }
    :: { txt = CALLHLL (lib, func, _); _ }
    :: code
    when let var = s.members.(Int32.to_int_exn varno) in
         let lib = Ain.ain.hll0.(lib) in
         let func = lib.functions.(func) in
         String.(
           var.name = "<vtable>" && lib.name = "Array" && func.name = "Alloc")
    ->
      let var =
        Deref (PageRef (StructPage, s.members.(Int32.to_int_exn varno)))
      in
      let alloc =
        Expression
          (Call
             ( HllFunc ("Array", Ain.ain.hll0.(lib).functions.(func)),
               [ var; Number d1; Number d2; Number d3; Number d4 ] ))
      in
      let rec parse_vtable_initializer acc = function
        | { txt = DUP; _ }
          :: { txt = PUSH i; _ }
          :: { txt = PUSH m; _ }
          :: { txt = ASSIGN; _ }
          :: { txt = POP; _ }
          :: rest ->
            parse_vtable_initializer
              (Expression (AssignOp (ASSIGN, ObjRef (var, Number i), Number m))
              :: acc)
              rest
        | { txt = POP; _ } :: rest -> (acc, rest)
        | _ -> failwith "unexpected code in vtable initializer"
      in
      let stmts, rest = parse_vtable_initializer [ alloc ] code in
      let stmts =
        List.map stmts ~f:(fun stmt ->
            from_stmt
              {
                txt = stmt;
                addr = f.end_addr (* FIMXE *);
                end_addr = f.end_addr;
              })
      in
      List.rev_append stmts (from_instructions f rest)
  | _ -> from_instructions f f.code

let from_enum_stringifier (f : CodeSection.function_t) =
  match List.map ~f:(fun i -> i.txt) f.code with
  | PUSHLOCALPAGE :: PUSH varno :: REF :: code ->
      let var =
        Deref (PageRef (LocalPage, f.func.vars.(Int32.to_int_exn varno)))
      in
      let rec parse = function
        | DUP :: PUSH n :: EQUALE :: IFZ _ :: POP :: S_PUSH s :: RETURN :: rest
          ->
            TernaryOp
              ( BinaryOp (EQUALE, var, Number n),
                String Ain.ain.str0.(s),
                parse rest )
        | [ POP; S_PUSH s; RETURN ] -> String Ain.ain.str0.(s)
        | _ -> failwith ("unexpected code in enum stringifier " ^ f.name)
      in
      from_stmt
        {
          txt = Return (Some (parse code));
          addr = (List.hd_exn f.code).addr;
          end_addr = f.end_addr;
        }
  | _ -> failwith ("unexpected prologue in enum stringifier " ^ f.name)

let create (f : CodeSection.function_t) =
  match (f.owner, f.name) with
  | Some (Enum _), _ -> (
      match f.name with
      | "String" -> [ from_enum_stringifier f ]
      | _ -> [] (* Enum functions other than String are ignored *))
  | Some (Struct s), ("0" | "2") -> from_generated_constructor s f
  | _ -> from_instructions f f.code

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
    | Expression
        (Call
           ( HllFunc ("Array", { name = "Alloc"; _ }),
             Deref (PageRef (_, var)) :: dims ))
      when is_uninitialized var ->
        let dims =
          List.take_while dims ~f:(function Number -1l -> false | _ -> true)
        in
        VarDecl
          ( var,
            Some
              (ASSIGN, Call (Builtin (A_ALLOC, PageRef (LocalPage, var)), dims))
          )
    | Expression
        ( Call (Builtin (A_FREE, PageRef (LocalPage, var)), [])
        | Call
            ( HllFunc ("Array", { name = "Free"; _ }),
              [ Deref (PageRef (_, var)) ] ) )
      when is_uninitialized var && not (Ain.Variable.is_dummy var) ->
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
