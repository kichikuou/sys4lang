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
open Stdlib.Printf
open Loc
open Type
open Ast
open Instructions

type variable = { v : Ain.Variable.t; dims : Ast.expr list }

type function_t = {
  func : Ain.Function.t;
  struc : Ain.Struct.t option;
  name : string;
  body : Ast.statement loc;
}

type struct_t = {
  struc : Ain.Struct.t;
  mutable members : variable list;
  mutable methods : function_t list;
}

type op_prec =
  | PREC_COMMA
  | PREC_ASSIGN
  | PREC_QUESTION
  | PREC_LOGOR
  | PREC_LOGAND
  | PREC_BITOR
  | PREC_BITXOR
  | PREC_BITAND
  | PREC_EQUAL
  | PREC_ORDER
  | PREC_BITSHIFT
  | PREC_ADD
  | PREC_MUL
  | PREC_UNARY
  | PREC_DOT
[@@deriving enum]

(* suppress "unused value" warning *)
let _ = (min_op_prec, max_op_prec, op_prec_of_enum)

type op_associativity = Left | Right

let print_string = Out_channel.output_string

let print_list sep f pr l =
  List.iteri l ~f:(fun i x ->
      if i > 0 then print_string pr sep;
      f pr x)

let prec_value p = op_prec_to_enum p * 2
let open_paren prec op_prec oc = if prec > op_prec then print_string oc "("
let close_paren prec op_prec oc = if prec > op_prec then print_string oc ")"

let format_float x =
  let s = Printf.sprintf "%f" x in
  let i = ref (String.length s - 1) in
  while Char.equal (String.get s !i) '0' do
    Int.decr i
  done;
  if Char.equal (String.get s !i) '.' then Int.incr i;
  String.sub s ~pos:0 ~len:(!i + 1)

let escape_map = [ ('\t', 't'); ('\r', 'r'); ('\n', 'n'); ('\x00', '0') ]

let escape_sq =
  String.Escaping.escape_gen_exn ~escape_char:'\\'
    ~escapeworthy_map:(('\'', '\'') :: escape_map)
  |> Staged.unstage

let escape_dq =
  String.Escaping.escape_gen_exn ~escape_char:'\\'
    ~escapeworthy_map:(('"', '"') :: escape_map)
  |> Staged.unstage

let pr_char oc c =
  if Common.Sjis.is_valid c then (
    let buf = Buffer.create 2 in
    Buffer.add_char buf (Char.of_int_exn (c land 0xff));
    if c > 0xff then Buffer.add_char buf (Char.of_int_exn (c lsr 8));
    fprintf oc "'%s'" (escape_sq (Common.Sjis.to_utf8 (Buffer.contents buf))))
  else fprintf oc "%d" c

let strip_class_name s =
  match String.lsplit2 s ~on:'@' with None -> s | Some (_, right) -> right

let pr_array_rank oc rank = if rank > 1 then fprintf oc "%@%d" rank

let pr_number oc = function
  | Number n -> fprintf oc "%ld" n
  | _ -> failwith "pr_number: non-number"

let pr_array_dims ?(pr_expr = pr_number) oc dims =
  List.iter dims ~f:(fun e -> fprintf oc "[%a]" pr_expr e)

let pr_initval oc (v : Ain.Variable.t) =
  match v.init_val with
  | None -> ()
  | Some (Int n) -> (
      match v.type_ with
      | Bool -> fprintf oc " = %s" (if Int32.(n = 0l) then "false" else "true")
      | Ref _ -> fprintf oc " = %s" Ain.ain.glob.(Int32.to_int_exn n).name
      | _ -> fprintf oc " = %ld" n)
  | Some (Float f) -> fprintf oc " = %s" (format_float f)
  | Some (Ain.Variable.String s) -> fprintf oc " = \"%s\"" (escape_dq s)

type operator = { sym : string; prec : int; lprec : int; rprec : int }

let make_op sym prec assoc =
  let p = prec_value prec in
  match assoc with
  | Left -> { sym; prec = p; lprec = p; rprec = p + 1 }
  | Right -> { sym; prec = p; lprec = p + 1; rprec = p }

let incdec_op = function
  | Increment -> make_op "++" PREC_UNARY Left
  | Decrement -> make_op "--" PREC_UNARY Left

let operator insn =
  match insn with
  | PSEUDO_COMMA -> make_op "," PREC_COMMA Left
  | OBJSWAP _ -> make_op "<=>" PREC_ASSIGN Left
  | ASSIGN | F_ASSIGN | LI_ASSIGN | S_ASSIGN | R_ASSIGN | SR_ASSIGN | DG_ASSIGN
  | DG_SET | PSEUDO_FT_ASSIGNS _ ->
      make_op "=" PREC_ASSIGN Right
  | PSEUDO_REF_ASSIGN -> make_op "<-" PREC_ASSIGN Right
  | PLUSA | F_PLUSA | LI_PLUSA | S_PLUSA | S_PLUSA2 | DG_PLUSA ->
      make_op "+=" PREC_ASSIGN Right
  | MINUSA | F_MINUSA | LI_MINUSA | DG_MINUSA -> make_op "-=" PREC_ASSIGN Right
  | MULA | F_MULA | LI_MULA -> make_op "*=" PREC_ASSIGN Right
  | DIVA | F_DIVA | LI_DIVA -> make_op "/=" PREC_ASSIGN Right
  | MODA | LI_MODA -> make_op "%=" PREC_ASSIGN Right
  | ORA -> make_op "|=" PREC_ASSIGN Right
  | ANDA -> make_op "&=" PREC_ASSIGN Right
  | XORA -> make_op "^=" PREC_ASSIGN Right
  | PSEUDO_LOGOR -> make_op "||" PREC_LOGOR Left
  | PSEUDO_LOGAND -> make_op "&&" PREC_LOGAND Left
  | OR -> make_op "|" PREC_BITOR Left
  | XOR -> make_op "^" PREC_BITXOR Left
  | AND -> make_op "&" PREC_BITAND Left
  | EQUALE | S_EQUALE | F_EQUALE -> make_op "==" PREC_EQUAL Left
  | NOTE | S_NOTE | F_NOTE -> make_op "!=" PREC_EQUAL Left
  | R_EQUALE -> make_op "===" PREC_EQUAL Left
  | R_NOTE -> make_op "!==" PREC_EQUAL Left
  | LT | F_LT | S_LT -> make_op "<" PREC_ORDER Left
  | LTE | F_LTE | S_LTE -> make_op "<=" PREC_ORDER Left
  | GT | F_GT | S_GT -> make_op ">" PREC_ORDER Left
  | GTE | F_GTE | S_GTE -> make_op ">=" PREC_ORDER Left
  | LSHIFT -> make_op "<<" PREC_BITSHIFT Left
  | RSHIFT -> make_op ">>" PREC_BITSHIFT Left
  | ADD | F_ADD | LI_ADD | S_ADD -> make_op "+" PREC_ADD Left
  | SUB | F_SUB | LI_SUB -> make_op "-" PREC_ADD Left
  | MUL | F_MUL | LI_MUL -> make_op "*" PREC_MUL Left
  | DIV | F_DIV | LI_DIV -> make_op "/" PREC_MUL Left
  | MOD | LI_MOD | S_MOD _ -> make_op "%" PREC_MUL Left
  | INV | F_INV -> make_op "-" PREC_UNARY Right
  | NOT -> make_op "!" PREC_UNARY Right
  | COMPL -> make_op "~" PREC_UNARY Right
  | op ->
      Printf.failwithf "cannot print operator for %s" (show_instruction op) ()

let pr_param_list pr_var oc (params : Ain.Variable.t list) =
  let params =
    List.filter params ~f:(fun arg ->
        match arg.type_ with Void -> false | _ -> true)
  in
  print_list ", " pr_var oc params

let rec pr_lvalue prec oc = function
  | NullRef -> print_string oc "NULL"
  | PageRef (StructPage, var) -> fprintf oc "this.%s" var.name
  | PageRef (_, var) -> print_string oc var.name
  | RefRef lval -> pr_lvalue prec oc lval
  | ArrayRef (array, index) ->
      fprintf oc "%a[%a]"
        (pr_expr (prec_value PREC_DOT))
        array (pr_expr 0) index
  | MemberRef (obj, memb) ->
      fprintf oc "%a.%s" (pr_expr (prec_value PREC_DOT)) obj memb.name
  | RefValue e -> pr_expr (prec_value PREC_DOT) oc e
  | ObjRef _ as lval ->
      failwith ("pr_lvalue: unresolved ObjRef " ^ show_lvalue lval)
  | IncDec (fix, op, lval) ->
      let op = incdec_op op in
      open_paren prec op.prec oc;
      (match fix with
      | Prefix -> fprintf oc "%s%a" op.sym (pr_lvalue prec) lval
      | Postfix -> fprintf oc "%a%s" (pr_lvalue prec) lval op.sym);
      close_paren prec op.prec oc

and pr_expr ?parent_op prec oc = function
  | Number n -> fprintf oc "%ld" n
  | Boolean b -> print_string oc (if b then "true" else "false")
  | Character c -> pr_char oc (Int32.to_int_exn c)
  | Float x -> print_string oc (format_float x)
  | String s -> fprintf oc "\"%s\"" (escape_dq s)
  | FuncAddr f -> fprintf oc "&%s" f.name
  | MemberPointer (struc, slot) ->
      fprintf oc "&%s::%s" Ain.ain.strt.(struc).name
        Ain.ain.strt.(struc).members.(slot).name
  | BoundMethod (Number -1l, f) ->
      fprintf oc "&%s" (Ain.Function.parse_name f).name
  | BoundMethod (expr, f) ->
      fprintf oc "%a.%s"
        (pr_expr (prec_value PREC_DOT))
        expr (Ain.Function.parse_name f).name
  | Deref lval -> pr_lvalue prec oc lval
  | DerefRef lval -> pr_lvalue prec oc lval
  | New n -> fprintf oc "new %s" Ain.ain.strt.(n).name
  | DerefStruct (_, expr) -> pr_expr prec oc expr
  | Page StructPage -> print_string oc "this"
  | Null -> print_string oc "NULL"
  | Void -> print_string oc "<void>" (* FIXME *)
  | UnaryOp (FTOI, expr) -> fprintf oc "int(%a)" (pr_expr 0) expr
  | UnaryOp (ITOF, expr) -> fprintf oc "float(%a)" (pr_expr 0) expr
  | UnaryOp (ITOLI, expr) -> fprintf oc "lint(%a)" (pr_expr 0) expr
  | UnaryOp (ITOB, Number 0l) -> print_string oc "false"
  | UnaryOp (ITOB, Number 1l) -> print_string oc "true"
  | UnaryOp (ITOB, expr) -> pr_expr prec oc expr
  | UnaryOp (STOI, expr) ->
      fprintf oc "%a.Int()" (pr_expr (prec_value PREC_DOT)) expr
  | UnaryOp (I_STRING, expr) -> fprintf oc "string(%a)" (pr_expr 0) expr
  | UnaryOp (insn, expr) ->
      let op = operator insn in
      open_paren prec op.prec oc;
      fprintf oc "%s%a" op.sym (pr_expr op.rprec) expr;
      close_paren prec op.prec oc
  | BinaryOp (insn, lhs, rhs) ->
      let op = operator insn in
      pr_binary_op parent_op prec op oc lhs rhs
  | AssignOp (insn, lval, rhs) ->
      let op = operator insn in
      pr_binary_op parent_op prec op oc (Deref lval) rhs
  | TernaryOp (expr1, expr2, expr3) ->
      let op_prec = prec_value PREC_QUESTION in
      open_paren prec op_prec oc;
      fprintf oc "%a ? %a : %a"
        (pr_expr (op_prec + 1))
        expr1
        (pr_expr (op_prec + 1))
        expr2 (pr_expr op_prec) expr3;
      close_paren prec op_prec oc
  | Call (f, args) -> fprintf oc "%a(%a)" pr_callable f pr_arg_list args
  | C_Ref (str, i) ->
      fprintf oc "%a[%a]" (pr_expr (prec_value PREC_DOT)) str (pr_expr 0) i
  | C_Assign (str, i, ch) ->
      pr_binary_op parent_op prec (operator ASSIGN) oc (C_Ref (str, i)) ch
  | e ->
      eprintf "%s\n" (show_expr e);
      failwith "pr_expr: not implemented"

and pr_binary_op parent_op prec op oc lhs rhs =
  (* Match the AinDecompiler's parenthesizing rules. *)
  let prec' =
    match parent_op with
    | Some pop ->
        if prec = op.prec && not (String.equal pop.sym op.sym) then prec + 1
        else prec
    | None -> prec
  in
  let space = if String.equal op.sym "," then "" else " " in
  open_paren prec' op.prec oc;
  fprintf oc "%a%s%s %a"
    (pr_expr ~parent_op:op op.lprec)
    lhs space op.sym
    (pr_expr ~parent_op:op op.rprec)
    rhs;
  close_paren prec' op.prec oc

and pr_callable oc = function
  | Function func -> print_string oc func.name
  | FuncPtr (_, e) -> pr_expr (prec_value PREC_DOT) oc e
  | Delegate (_, e) -> pr_expr (prec_value PREC_DOT) oc e
  | SysCall n -> print_string oc syscalls.(n).name
  | HllFunc (lib, func) -> fprintf oc "%s.%s" lib func.name
  | Method (expr, func) ->
      fprintf oc "%a.%s"
        (pr_expr (prec_value PREC_DOT))
        expr
        (strip_class_name func.name)
  | Builtin (insn, lval) ->
      fprintf oc "%a.%s"
        (pr_lvalue (prec_value PREC_DOT))
        lval (builtin_method_name insn)
  | Builtin2 (insn, expr) ->
      fprintf oc "%a.%s"
        (pr_expr (prec_value PREC_DOT))
        expr (builtin_method_name insn)

and pr_arg_list oc args = print_list ", " (pr_expr 0) oc args

type debug_mapping = { addr : int; src : int; line : int }

type debug_info = {
  mutable sources : string list;
  mutable current_src : int;
  mutable mappings : debug_mapping list;
}

let create_debug_info () = { sources = []; current_src = -1; mappings = [] }

let add_debug_info dbginfo addr file line =
  let src =
    match dbginfo.sources with
    | s :: _ when String.equal s file -> dbginfo.current_src
    | _ ->
        dbginfo.sources <- file :: dbginfo.sources;
        dbginfo.current_src <- dbginfo.current_src + 1;
        dbginfo.current_src
  in
  (* If multiple lines are mapped to the same address, discard all but the last line *)
  dbginfo.mappings <-
    { addr; src; line }
    ::
    (match dbginfo.mappings with
    | hd :: tl when hd.addr = addr -> tl
    | _ -> dbginfo.mappings)

let debug_info_to_json dbginfo =
  let sources = List.rev_map dbginfo.sources ~f:(fun s -> `String s) in
  let mappings =
    List.rev_map dbginfo.mappings ~f:(fun { addr; src; line } ->
        `List [ `Int addr; `Int src; `Int line ])
  in
  `Assoc
    [
      ("version", `String "alpha-1");
      ("sources", `List sources);
      ("mappings", `List mappings);
    ]

type printer = { oc : Stdio.Out_channel.t; file : string; mutable line : int }

let create_printer oc file = { oc; file; line = 1 }

let print_newline pr =
  pr.line <- pr.line + 1;
  Stdio.Out_channel.newline pr.oc

let print_indent pr n = print_string pr.oc (String.make n '\t')
let println pr fmt = kfprintf (fun _ -> print_newline pr) pr.oc fmt

let rec pr_type pr oc = function
  | Any -> failwith "unresolved type"
  | Char -> failwith "variables cannot have Char type"
  | Int -> print_string oc "int"
  | Float -> print_string oc "float"
  | String -> print_string oc "string"
  | Bool -> print_string oc "bool"
  | LongInt -> print_string oc "lint"
  | Void -> print_string oc "void"
  | Struct n ->
      print_string oc (if n < 0 then "struct" else Ain.ain.strt.(n).name)
  | Array _ as t ->
      print_string oc "array@";
      let base, rank = Type.array_base_and_rank t in
      pr_type pr oc base;
      pr_array_rank oc rank
  | Ref t ->
      print_string oc "ref ";
      pr_type pr oc t
  | IMainSystem -> print_string oc "IMainSystem"
  | FuncType ftv -> (
      match Type.TypeVar.get_value ftv with
      | Id (n, _) -> print_string oc Ain.ain.fnct.(n).name
      | Type t ->
          (* Output the first functype matching the inferred type *)
          let ft =
            Array.find_exn Ain.ain.fnct ~f:(fun ft ->
                Poly.(t = Ain.FuncType.to_type ft))
          in
          print_string oc ft.name
      | Var -> print_string oc "unknown_functype")
  | StructMember _ -> failwith "cannot happen"
  | Delegate dtv -> (
      match Type.TypeVar.get_value dtv with
      | Id (n, _) -> print_string oc Ain.ain.delg.(n).name
      | Type t ->
          (* Output the first delegate type matching the inferred type *)
          let dt =
            Array.find_exn Ain.ain.delg ~f:(fun ft ->
                Poly.(t = Ain.FuncType.to_type ft))
          in
          print_string oc dt.name
      | Var -> print_string oc "unknown_delegate")
  | HllFunc2 -> print_string oc "hll_func2"
  | HllParam -> print_string oc "hll_param"

let pr_vartype pr oc (arg : Ain.Variable.t) =
  fprintf oc "%a" (pr_type pr) arg.type_

let pr_vardecl pr oc (arg : Ain.Variable.t) =
  fprintf oc "%a %s" (pr_type pr) arg.type_ arg.name

let print_function ~print_addr pr dbginfo (func : function_t) =
  let addr_and_indent addr indent =
    if addr > 0 then add_debug_info dbginfo addr pr.file pr.line;
    if print_addr then fprintf pr.oc "/* %08x */" addr;
    print_indent pr indent
  in
  let pr_label = function
    | Address label -> println pr "label%d:" label
    | CaseInt (_, k) -> println pr "case %ld:" k
    | CaseStr (_, s) -> println pr "case \"%s\":" (escape_dq s)
    | Default _ -> println pr "default:"
  in
  let rec print_stmt indent in_else_if stmt =
    match stmt.txt with
    | Block stmts ->
        addr_and_indent stmt.addr indent;
        println pr "{";
        print_stmt_list (indent + 1) (List.rev stmts);
        let end_addr =
          match stmts with [] -> stmt.end_addr | s :: _ -> s.end_addr
        in
        addr_and_indent end_addr indent;
        println pr "}"
    | Expression expr ->
        addr_and_indent stmt.addr indent;
        println pr "%a;" (pr_expr 0) expr
    | Return None ->
        addr_and_indent stmt.addr indent;
        println pr "return;"
    | Return (Some expr) ->
        addr_and_indent stmt.addr indent;
        println pr "return %a;" (pr_expr 0) expr
    | Break ->
        addr_and_indent stmt.addr indent;
        println pr "break;"
    | Continue ->
        addr_and_indent stmt.addr indent;
        println pr "continue;"
    | Goto (label, _) ->
        addr_and_indent stmt.addr indent;
        println pr "goto label%d;" label
    | VarDecl (var, None) ->
        addr_and_indent stmt.addr indent;
        println pr "%a;" (pr_vardecl pr) var
    | VarDecl (var, Some (_, Call (Builtin (A_ALLOC, _), dims))) ->
        addr_and_indent stmt.addr indent;
        println pr "%a%a;" (pr_vardecl pr) var
          (pr_array_dims ~pr_expr:(pr_expr 0))
          dims
    | VarDecl (var, Some (insn, e)) ->
        let op = operator insn in
        addr_and_indent stmt.addr indent;
        println pr "%a = %a;" (pr_vardecl pr) var
          (pr_expr ~parent_op:op op.rprec)
          e
    | IfElse (expr, stmt1, stmt2) -> (
        if not in_else_if then addr_and_indent stmt.addr indent;
        println pr "if (%a)" (pr_expr 0) expr;
        addr_and_indent stmt1.addr indent;
        println pr "{";
        print_stmt_list (indent + 1)
          (match stmt1.txt with
          | Block stmts -> List.rev stmts
          | _ -> [ stmt1 ]);
        addr_and_indent stmt1.end_addr indent;
        println pr "}";
        match stmt2.txt with
        | Block [] -> ()
        | IfElse _ ->
            addr_and_indent stmt2.addr indent;
            print_string pr.oc "else ";
            print_stmt indent true stmt2
        | _ ->
            addr_and_indent stmt2.addr indent;
            println pr "else";
            addr_and_indent stmt2.addr indent;
            println pr "{";
            print_stmt_list (indent + 1)
              (match stmt2.txt with
              | Block stmts -> List.rev stmts
              | _ -> [ stmt2 ]);
            addr_and_indent stmt2.end_addr indent;
            println pr "}")
    | Switch (_, expr, body) ->
        addr_and_indent stmt.addr indent;
        println pr "switch (%a)" (pr_expr 0) expr;
        addr_and_indent body.addr indent;
        println pr "{";
        print_stmt_list (indent + 1)
          (match body.txt with Block stmts -> List.rev stmts | _ -> [ body ]);
        addr_and_indent body.end_addr indent;
        println pr "}"
    | While (cond, body) ->
        addr_and_indent stmt.addr indent;
        println pr "while (%a)" (pr_expr 0) cond;
        addr_and_indent body.addr indent;
        println pr "{";
        print_stmt_list (indent + 1)
          (match body.txt with Block stmts -> List.rev stmts | _ -> [ body ]);
        addr_and_indent body.end_addr indent;
        println pr "}"
    | DoWhile (body, cond) ->
        addr_and_indent stmt.addr indent;
        println pr "do {";
        print_stmt_list (indent + 1)
          (match body.txt with Block stmts -> List.rev stmts | _ -> [ body ]);
        addr_and_indent cond.addr indent;
        println pr "} while (%a);" (pr_expr 0) cond.txt
    | For (init, cond, inc, body) ->
        addr_and_indent stmt.addr indent;
        print_string pr.oc "for (";
        (match init with None -> () | Some e -> pr_expr 0 pr.oc e);
        print_string pr.oc "; ";
        (match cond with None -> () | Some e -> pr_expr 0 pr.oc e);
        print_string pr.oc "; ";
        (match inc with None -> () | Some e -> pr_expr 0 pr.oc e);
        println pr ")";
        addr_and_indent body.addr indent;
        println pr "{";
        print_stmt_list (indent + 1)
          (match body.txt with Block stmts -> List.rev stmts | _ -> [ body ]);
        addr_and_indent body.end_addr indent;
        println pr "}"
    | Label label ->
        addr_and_indent stmt.addr (indent - 1);
        pr_label label
    | Assert expr ->
        addr_and_indent stmt.addr indent;
        println pr "assert(%a);" (pr_expr 0) expr
    | ScenarioJump s ->
        addr_and_indent stmt.addr indent;
        println pr "jump %s;" s
    | Msg (s, Some (Call (f, []))) ->
        addr_and_indent stmt.addr indent;
        println pr "'%s' %a;" (escape_sq s) pr_callable f
    | Msg (s, Some e) ->
        addr_and_indent stmt.addr indent;
        println pr "'%s' %a;" (escape_sq s) (pr_expr 0) e
    | Msg (s, None) ->
        addr_and_indent stmt.addr indent;
        println pr "'%s';" (escape_sq s)
  and print_stmt_list indent stmts =
    List.iter stmts ~f:(fun stmt -> print_stmt indent false stmt)
  in
  let print_func_signature (func : function_t) =
    let return_type = func.func.return_type in
    (match func.struc with
    | Some (struc : Ain.Struct.t) ->
        if String.equal func.name "0" then
          fprintf pr.oc "%s::%s" struc.name struc.name
        else if String.equal func.name "1" then
          fprintf pr.oc "%s::~%s" struc.name struc.name
        else
          fprintf pr.oc "%a %s::%s" (pr_type pr) return_type struc.name
            func.name
    | None ->
        if func.func.is_label then fprintf pr.oc "#%s" func.name
        else fprintf pr.oc "%a %s" (pr_type pr) return_type func.name);
    println pr "(%a)"
      (pr_param_list (pr_vardecl pr))
      (Ain.Function.args func.func)
  in
  print_func_signature func;
  let body =
    match func.body.txt with
    | Block _ -> func.body
    | _ -> { func.body with txt = Block [ func.body ] }
  in
  print_stmt 0 false body

let print_struct_decl pr (struc : struct_t) =
  println pr "class %s" struc.struc.name;
  println pr "{";
  println pr "public:";
  List.iter struc.members ~f:(fun v ->
      match v.v.type_ with
      | Void -> ()
      | _ ->
          print_indent pr 1;
          pr_vardecl pr pr.oc v.v;
          pr_array_dims pr.oc v.dims;
          println pr ";");
  if
    (not (Array.is_empty struc.struc.members))
    && not (List.is_empty struc.methods)
  then print_newline pr;
  List.iter struc.methods ~f:(fun func ->
      print_indent pr 1;
      if String.equal func.name "0" then fprintf pr.oc "%s" struc.struc.name
      else if String.equal func.name "1" then
        fprintf pr.oc "~%s" struc.struc.name
      else fprintf pr.oc "%a %s" (pr_type pr) func.func.return_type func.name;
      println pr "(%a);"
        (pr_param_list (pr_vardecl pr))
        (Ain.Function.args func.func));
  println pr "};"

let print_functype_decl pr keyword (ft : Ain.FuncType.t) =
  fprintf pr.oc "%s %a %s " keyword (pr_type pr) ft.return_type ft.name;
  match Ain.FuncType.args ft with
  | [] -> println pr "(void);"
  | args -> println pr "(%a);" (pr_param_list (pr_vartype pr)) args

let print_globals pr (globals : variable list) =
  let groups =
    List.group globals ~break:(fun a b -> a.v.group_index <> b.v.group_index)
  in
  let print_group indent =
    List.iter ~f:(fun (v : variable) ->
        print_indent pr indent;
        pr_vardecl pr pr.oc v.v;
        pr_array_dims pr.oc v.dims;
        pr_initval pr.oc v.v;
        println pr ";")
  in
  List.iter groups ~f:(fun group ->
      match (List.hd_exn group).v.group_index with
      | -1 -> print_group 0 group
      | gindex ->
          println pr "globalgroup %s" Ain.ain.objg.(gindex);
          println pr "{";
          print_group 1 group;
          println pr "}")

let print_constants pr =
  println pr "const int true = 1;";
  println pr "const int false = 0;";
  print_newline pr

let print_hll_function pr (func : Ain.HLL.function_t) =
  fprintf pr.oc "%a %s" (pr_type pr) func.return_type func.name;
  match Ain.HLL.args func with
  | [] -> println pr "(void);"
  | args -> println pr "(%a);" (pr_param_list (pr_vardecl pr)) args

let print_hll_inc pr =
  println pr "SystemSource = {";
  Array.iter Ain.ain.hll0 ~f:(fun hll ->
      println pr "\t\"%s.hll\",\t\"%s\"," hll.name hll.name);
  println pr "}"

let print_inc pr srcs =
  println pr "Source = {";
  List.iter srcs ~f:(fun src -> println pr "\t\"%s\"," src);
  println pr "}"

type project_t = { name : string; output_dir : string }

let print_pje pr proj =
  println pr "// Project Environment File";
  println pr "Encoding = \"UTF-8\"";
  println pr "ProjectName = \"%s\"" proj.name;
  print_newline pr;
  println pr "CodeName = \"%s.ain\"" proj.name;
  print_newline pr;
  println pr "#define _AINVERSION %d" Ain.ain.vers;
  println pr "#define _KEYCODE 0x%08lX" Ain.ain.keyc;
  println pr "#define _ISAI2FILE %B" Ain.ain.is_ai2;
  if Ain.ain.vers >= 6 then
    println pr "#define _USESMSG1 %B" (Option.is_some Ain.ain.msg1_uk);
  print_newline pr;
  println pr "GameVersion = %ld" Ain.ain.gver;
  print_newline pr;
  println pr "// Settings for each directory";
  println pr "SourceDir = \".\"";
  println pr "HLLDir = \"HLL\"";
  println pr "ObjDir = \"OBJ\"";
  println pr "OutputDir = \"%s\"" proj.output_dir;
  print_newline pr;
  println pr "Source = {";
  println pr "\t\"main.inc\",";
  println pr "}"

let print_debug_info pr dbginfo =
  debug_info_to_json dbginfo |> Yojson.Basic.to_string |> print_string pr.oc
