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
  lambdas : function_t list;
  parent : Ain.Function.t option;
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

(* strip_qualifiers "a::b::c" returns "c" *)
let strip_qualifiers name =
  match String.rindex name ':' with
  | None -> name
  | Some i -> String.sub name ~pos:(i + 1) ~len:(String.length name - i - 1)

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
  | PLUSA | F_PLUSA | LI_PLUSA | S_PLUSA | S_PLUSA2 | DG_PLUSA | DG_ADD ->
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
  | LSHIFTA -> make_op "<<=" PREC_ASSIGN Right
  | RSHIFTA -> make_op ">>=" PREC_ASSIGN Right
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

type project_t = { name : string; output_dir : string; ain_minor_version : int }

class code_printer ?(print_addr = false) (oc : Stdio.Out_channel.t)
  (file : string) =
  object (self)
    val mutable line = 1
    val mutable indent = 0
    val dbginfo = create_debug_info ()
    val current_function = Stack.create ()

    method print_newline =
      line <- line + 1;
      Stdio.Out_channel.newline oc

    method private print_indent = print_string oc (String.make indent '\t')

    method private with_indent ?(delta = 1) f =
      indent <- indent + delta;
      f ();
      indent <- indent - delta

    method private addr_and_indent addr =
      if addr > 0 then add_debug_info dbginfo addr file line;
      if print_addr then fprintf oc "/* %08x */" addr;
      self#print_indent

    method private println :
        'a. ('a, Stdio.Out_channel.t, unit, unit) format4 -> 'a =
      fun fmt -> kfprintf (fun _ -> self#print_newline) oc fmt

    method private pr_lvalue prec oc lval =
      match lval with
      | NullRef -> print_string oc "NULL"
      | PageRef (StructPage, var) -> fprintf oc "this.%s" var.name
      | PageRef (_, var) -> print_string oc var.name
      | RefRef lval -> self#pr_lvalue prec oc lval
      | ArrayRef (array, index) ->
          fprintf oc "%a[%a]"
            (self#pr_expr (prec_value PREC_DOT))
            array (self#pr_expr 0) index
      | MemberRef (obj, memb) ->
          fprintf oc "%a.%s" (self#pr_expr (prec_value PREC_DOT)) obj memb.name
      | RefValue e -> self#pr_expr (prec_value PREC_DOT) oc e
      | ObjRef _ as lval ->
          failwith ("pr_lvalue: unresolved ObjRef " ^ show_lvalue lval)
      | IncDec (fix, op, lval) ->
          let op = incdec_op op in
          open_paren prec op.prec oc;
          (match fix with
          | Prefix -> fprintf oc "%s%a" op.sym (self#pr_lvalue prec) lval
          | Postfix -> fprintf oc "%a%s" (self#pr_lvalue prec) lval op.sym);
          close_paren prec op.prec oc

    method private pr_expr ?parent_op prec oc =
      function
      | Number n -> fprintf oc "%ld" n
      | Boolean b -> print_string oc (if b then "true" else "false")
      | Character c -> pr_char oc (Int32.to_int_exn c)
      | Float x -> print_string oc (format_float x)
      | String s -> fprintf oc "\"%s\"" (escape_dq s)
      | FuncAddr f -> fprintf oc "&%s" f.name
      | MemberPointer (struc, slot) ->
          fprintf oc "&%s::%s" Ain.ain.strt.(struc).name
            Ain.ain.strt.(struc).members.(slot).name
      | BoundMethod (_, ({ is_lambda = true; _ } as func)) -> (
          match
            List.find (Stack.top_exn current_function).lambdas ~f:(fun f ->
                Poly.equal f.func func)
          with
          | Some func -> self#print_function ~as_lambda:true func
          | None -> Printf.failwithf "unresolved lambda %s" func.name ())
      | BoundMethod (Number -1l, f) ->
          fprintf oc "&%s" (Ain.Function.parse_name f).name
      | BoundMethod (expr, f) ->
          let method_name =
            (Ain.Function.parse_name f).name
            |> String.chop_suffix_if_exists ~suffix:"::set"
          in
          fprintf oc "%a.%s"
            (self#pr_expr (prec_value PREC_DOT))
            expr method_name
      | Deref lval -> self#pr_lvalue prec oc lval
      | DerefRef lval -> self#pr_lvalue prec oc lval
      | New n -> fprintf oc "new %s" Ain.ain.strt.(n).name
      | DerefStruct (_, expr) -> self#pr_expr prec oc expr
      | Page StructPage -> print_string oc "this"
      | Null -> print_string oc "NULL"
      | Void -> print_string oc "<void>" (* FIXME *)
      | UnaryOp (FTOI, expr) -> fprintf oc "int(%a)" (self#pr_expr 0) expr
      | UnaryOp (ITOF, expr) -> fprintf oc "float(%a)" (self#pr_expr 0) expr
      | UnaryOp (ITOLI, expr) -> fprintf oc "lint(%a)" (self#pr_expr 0) expr
      | UnaryOp (ITOB, Number 0l) -> print_string oc "false"
      | UnaryOp (ITOB, Number 1l) -> print_string oc "true"
      | UnaryOp (ITOB, expr) -> self#pr_expr prec oc expr
      | UnaryOp (STOI, expr) ->
          fprintf oc "%a.Int()" (self#pr_expr (prec_value PREC_DOT)) expr
      | UnaryOp (I_STRING, expr) ->
          fprintf oc "string(%a)" (self#pr_expr 0) expr
      | UnaryOp (insn, expr) ->
          let op = operator insn in
          open_paren prec op.prec oc;
          fprintf oc "%s%a" op.sym (self#pr_expr op.rprec) expr;
          close_paren prec op.prec oc
      | BinaryOp (insn, lhs, rhs) ->
          let op = operator insn in
          self#pr_binary_op parent_op prec op lhs rhs
      | AssignOp (insn, lval, rhs) ->
          let op = operator insn in
          self#pr_binary_op parent_op prec op (Deref lval) rhs
      | TernaryOp
          ( expr1,
            (Deref (RefRef (PageRef (_, { type_ = Ref Int; _ }))) as expr2),
            (Deref (RefRef (PageRef (_, { type_ = Ref Int; _ }))) as expr3) ) ->
          (* For Rance 9: ref_int = bool ? ref_int : ref_int
             Add casts so that the right hand side of the assignment is an int
             instead of a ref int *)
          let op_prec = prec_value PREC_QUESTION in
          open_paren prec op_prec oc;
          fprintf oc "%a ? int(%a) : int(%a)"
            (self#pr_expr (op_prec + 1))
            expr1
            (self#pr_expr (op_prec + 1))
            expr2 (self#pr_expr op_prec) expr3;
          close_paren prec op_prec oc
      | TernaryOp (expr1, expr2, expr3) ->
          let op_prec = prec_value PREC_QUESTION in
          open_paren prec op_prec oc;
          fprintf oc "%a ? %a : %a"
            (self#pr_expr (op_prec + 1))
            expr1
            (self#pr_expr (op_prec + 1))
            expr2 (self#pr_expr op_prec) expr3;
          close_paren prec op_prec oc
      | Call (f, args) ->
          fprintf oc "%a(%a)" self#pr_callable f self#pr_arg_list args
      | C_Ref (str, i) ->
          fprintf oc "%a[%a]"
            (self#pr_expr (prec_value PREC_DOT))
            str (self#pr_expr 0) i
      | C_Assign (str, i, ch) ->
          self#pr_binary_op parent_op prec (operator ASSIGN) (C_Ref (str, i)) ch
      | PropertySet (obj, m, rhs) ->
          self#pr_binary_op parent_op prec (operator ASSIGN)
            (BoundMethod (obj, m))
            rhs
      | e ->
          eprintf "%s\n" (show_expr e);
          failwith "pr_expr: not implemented"

    method private pr_binary_op parent_op prec op lhs rhs =
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
        (self#pr_expr ~parent_op:op op.lprec)
        lhs space op.sym
        (self#pr_expr ~parent_op:op op.rprec)
        rhs;
      close_paren prec' op.prec oc

    method private pr_callable oc =
      function
      | Function func -> print_string oc func.name
      | FuncPtr (_, e) -> self#pr_expr (prec_value PREC_DOT) oc e
      | Delegate (_, e) -> self#pr_expr (prec_value PREC_DOT) oc e
      | SysCall n -> print_string oc syscalls.(n).name
      | HllFunc (lib, func) -> fprintf oc "%s.%s" lib func.name
      | Method (expr, func) ->
          fprintf oc "%a.%s"
            (self#pr_expr (prec_value PREC_DOT))
            expr
            (strip_class_name func.name)
      | Builtin (insn, lval) ->
          fprintf oc "%a.%s"
            (self#pr_lvalue (prec_value PREC_DOT))
            lval (builtin_method_name insn)
      | Builtin2 (insn, expr) ->
          fprintf oc "%a.%s"
            (self#pr_expr (prec_value PREC_DOT))
            expr (builtin_method_name insn)

    method private pr_arg_list oc args =
      print_list ", " (self#pr_expr 0) oc args

    method private pr_type oc =
      function
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
      | Array Any -> print_string oc "array"
      | Array _ as t ->
          print_string oc "array@";
          let base, rank = Type.array_base_and_rank t in
          self#pr_type oc base;
          pr_array_rank oc rank
      | Ref t ->
          print_string oc "ref ";
          self#pr_type oc t
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

    method private pr_vartype oc (arg : Ain.Variable.t) =
      fprintf oc "%a" self#pr_type arg.type_

    method private pr_vardecl oc (arg : Ain.Variable.t) =
      fprintf oc "%a %s" self#pr_type arg.type_ arg.name

    method print_function ?(as_lambda = false) (func : function_t) =
      let pr_label = function
        | Address label -> self#println "label%d:" label
        | CaseInt (_, k) -> self#println "case %ld:" k
        | CaseStr (_, s) -> self#println "case \"%s\":" (escape_dq s)
        | Default _ -> self#println "default:"
      in
      let rec print_stmt ?(in_else_if = false) ?(is_lambda_top = false) stmt =
        match stmt.txt with
        | Block stmts ->
            if not is_lambda_top then self#addr_and_indent stmt.addr;
            self#println "{";
            self#with_indent (fun () -> print_stmt_list (List.rev stmts));
            let end_addr =
              match stmts with [] -> stmt.end_addr | s :: _ -> s.end_addr
            in
            self#addr_and_indent end_addr;
            if is_lambda_top then print_string oc "}" else self#println "}"
        | Expression expr ->
            self#addr_and_indent stmt.addr;
            self#println "%a;" (self#pr_expr 0) expr
        | Return None ->
            self#addr_and_indent stmt.addr;
            self#println "return;"
        | Return (Some expr) ->
            self#addr_and_indent stmt.addr;
            self#println "return %a;" (self#pr_expr 0) expr
        | Break ->
            self#addr_and_indent stmt.addr;
            self#println "break;"
        | Continue ->
            self#addr_and_indent stmt.addr;
            self#println "continue;"
        | Goto (label, _) ->
            self#addr_and_indent stmt.addr;
            self#println "goto label%d;" label
        | VarDecl (var, None) ->
            self#addr_and_indent stmt.addr;
            self#println "%a;" self#pr_vardecl var
        | VarDecl (var, Some (_, Call (Builtin (A_ALLOC, _), dims))) ->
            self#addr_and_indent stmt.addr;
            self#println "%a%a;" self#pr_vardecl var
              (pr_array_dims ~pr_expr:(self#pr_expr 0))
              dims
        | VarDecl (var, Some (insn, e)) ->
            let op = operator insn in
            self#addr_and_indent stmt.addr;
            self#println "%a = %a;" self#pr_vardecl var
              (self#pr_expr ~parent_op:op op.rprec)
              e
        | IfElse (expr, stmt1, stmt2) -> (
            if not in_else_if then self#addr_and_indent stmt.addr;
            self#println "if (%a) {" (self#pr_expr 0) expr;
            self#with_indent (fun () ->
                print_stmt_list
                  (match stmt1.txt with
                  | Block stmts -> List.rev stmts
                  | _ -> [ stmt1 ]));
            self#addr_and_indent stmt1.end_addr;
            print_string oc "}";
            match stmt2.txt with
            | Block [] -> self#print_newline
            | IfElse _ ->
                print_string oc " else ";
                print_stmt ~in_else_if:true stmt2
            | _ ->
                self#println " else {";
                self#with_indent (fun () ->
                    print_stmt_list
                      (match stmt2.txt with
                      | Block stmts -> List.rev stmts
                      | _ -> [ stmt2 ]));
                self#addr_and_indent stmt2.end_addr;
                self#println "}")
        | Switch (_, expr, body) ->
            self#addr_and_indent stmt.addr;
            self#println "switch (%a) {" (self#pr_expr 0) expr;
            self#with_indent (fun () ->
                print_stmt_list
                  (match body.txt with
                  | Block stmts -> List.rev stmts
                  | _ -> [ body ]));
            self#addr_and_indent body.end_addr;
            self#println "}"
        | While (cond, body) ->
            self#addr_and_indent stmt.addr;
            self#println "while (%a) {" (self#pr_expr 0) cond;
            self#with_indent (fun () ->
                print_stmt_list
                  (match body.txt with
                  | Block stmts -> List.rev stmts
                  | _ -> [ body ]));
            self#addr_and_indent body.end_addr;
            self#println "}"
        | DoWhile (body, cond) ->
            self#addr_and_indent stmt.addr;
            self#println "do {";
            self#with_indent (fun () ->
                print_stmt_list
                  (match body.txt with
                  | Block stmts -> List.rev stmts
                  | _ -> [ body ]));
            self#addr_and_indent cond.addr;
            self#println "} while (%a);" (self#pr_expr 0) cond.txt
        | For (init, cond, inc, body) ->
            self#addr_and_indent stmt.addr;
            print_string oc "for (";
            (match init with None -> () | Some e -> self#pr_expr 0 oc e);
            print_string oc "; ";
            (match cond with None -> () | Some e -> self#pr_expr 0 oc e);
            print_string oc "; ";
            (match inc with None -> () | Some e -> self#pr_expr 0 oc e);
            self#println ") {";
            self#with_indent (fun () ->
                print_stmt_list
                  (match body.txt with
                  | Block stmts -> List.rev stmts
                  | _ -> [ body ]));
            self#addr_and_indent body.end_addr;
            self#println "}"
        | Label label ->
            self#with_indent ~delta:(-1) (fun () ->
                self#addr_and_indent stmt.addr;
                pr_label label)
        | Assert expr ->
            self#addr_and_indent stmt.addr;
            self#println "assert(%a);" (self#pr_expr 0) expr
        | ScenarioJump s ->
            self#addr_and_indent stmt.addr;
            self#println "jump %s;" s
        | Msg (s, Some (Call (f, []))) ->
            self#addr_and_indent stmt.addr;
            self#println "'%s' %a;" (escape_sq s) self#pr_callable f
        | Msg (s, Some e) ->
            self#addr_and_indent stmt.addr;
            self#println "'%s' %a;" (escape_sq s) (self#pr_expr 0) e
        | Msg (s, None) ->
            self#addr_and_indent stmt.addr;
            self#println "'%s';" (escape_sq s)
      and print_stmt_list = List.iter ~f:print_stmt in
      let print_func_signature (func : function_t) =
        let return_type = func.func.return_type in
        (if not as_lambda then
           match func.struc with
           | Some (struc : Ain.Struct.t) ->
               if String.equal func.name "0" then
                 fprintf oc "%s::%s" struc.name (strip_qualifiers struc.name)
               else if String.equal func.name "1" then
                 fprintf oc "%s::~%s" struc.name (strip_qualifiers struc.name)
               else
                 fprintf oc "%a %s::%s" self#pr_type return_type struc.name
                   func.name
           | None ->
               if func.func.is_label then fprintf oc "#%s" func.name
               else fprintf oc "%a %s" self#pr_type return_type func.name);
        fprintf oc "(%a)"
          (pr_param_list self#pr_vardecl)
          (Ain.Function.args func.func);
        if as_lambda then fprintf oc " => %a " self#pr_type return_type
        else self#print_newline
      in
      print_func_signature func;
      let body =
        match func.body.txt with
        | Block _ -> func.body
        | _ -> { func.body with txt = Block [ func.body ] }
      in
      Stack.push current_function func;
      print_stmt ~is_lambda_top:as_lambda body;
      Stack.pop_exn current_function |> ignore

    method print_struct_decl (struc : struct_t) =
      self#println "class %s {" struc.struc.name;
      self#println "public:";
      self#with_indent (fun () ->
          List.iter struc.members ~f:(fun v ->
              match v.v.type_ with
              | Void -> ()
              | _ ->
                  self#print_indent;
                  self#pr_vardecl oc v.v;
                  pr_array_dims oc v.dims;
                  self#println ";");
          if
            (not (Array.is_empty struc.struc.members))
            && not (List.is_empty struc.methods)
          then self#print_newline;
          List.iter struc.methods ~f:(fun func ->
              self#print_indent;
              if String.equal func.name "0" then
                fprintf oc "%s" (strip_qualifiers struc.struc.name)
              else if String.equal func.name "1" then
                fprintf oc "~%s" (strip_qualifiers struc.struc.name)
              else
                fprintf oc "%a %s" self#pr_type func.func.return_type func.name;
              self#println "(%a);"
                (pr_param_list self#pr_vardecl)
                (Ain.Function.args func.func)));
      self#println "};"

    method print_functype_decl keyword (ft : Ain.FuncType.t) =
      if String.contains ft.name '@' then ()
      else (
        fprintf oc "%s %a %s " keyword self#pr_type ft.return_type ft.name;
        match Ain.FuncType.args ft with
        | [] -> self#println "(void);"
        | args -> self#println "(%a);" (pr_param_list self#pr_vartype) args)

    method print_globals (globals : variable list) =
      let groups =
        List.group globals ~break:(fun a b ->
            a.v.group_index <> b.v.group_index)
      in
      let print_group =
        List.iter ~f:(fun (v : variable) ->
            self#print_indent;
            self#pr_vardecl oc v.v;
            pr_array_dims oc v.dims;
            pr_initval oc v.v;
            self#println ";")
      in
      List.iter groups ~f:(fun group ->
          match (List.hd_exn group).v.group_index with
          | -1 -> print_group group
          | gindex ->
              self#println "globalgroup %s {" Ain.ain.objg.(gindex);
              self#with_indent (fun () -> print_group group);
              self#println "}")

    method print_constants =
      self#println "const int true = 1;";
      self#println "const int false = 0;";
      self#print_newline

    method private print_hll_function (func : Ain.HLL.function_t) =
      fprintf oc "%a %s" self#pr_type func.return_type func.name;
      match Ain.HLL.args func with
      | [] -> self#println "(void);"
      | args -> self#println "(%a);" (pr_param_list self#pr_vardecl) args

    method print_hll (funcs : Ain.HLL.function_t array) =
      let printed = Hash_set.create (module String) in
      Array.iter funcs ~f:(fun func ->
          if Hash_set.mem printed func.name then
            print_string oc "// (duplicated) "
          else Hash_set.add printed func.name;
          self#print_hll_function func)

    method print_hll_inc =
      self#println "SystemSource = {";
      let printed = Hash_set.create (module String) in
      Array.iter Ain.ain.hll0 ~f:(fun hll ->
          if Hash_set.mem printed hll.name then
            Stdio.eprintf
              "Warning: %s: Removing duplicate HLL include for %s.hll\n" file
              hll.name
          else (
            Hash_set.add printed hll.name;
            self#println "\t\"%s.hll\",\t\"%s\"," hll.name hll.name));
      self#println "}"

    method print_inc srcs =
      self#println "Source = {";
      List.iter srcs ~f:(fun src -> self#println "\t\"%s\"," src);
      self#println "}"

    method print_pje (proj : project_t) =
      self#println "// Project Environment File";
      self#println "Encoding = \"UTF-8\"";
      self#println "ProjectName = \"%s\"" proj.name;
      self#print_newline;
      self#println "CodeName = \"%s.ain\"" proj.name;
      self#print_newline;
      self#println "#define _AINVERSION %d" Ain.ain.vers;
      if proj.ain_minor_version <> 0 then
        self#println "#define _AINMINORVERSION %d" proj.ain_minor_version;
      self#println "#define _KEYCODE 0x%08lX" Ain.ain.keyc;
      self#println "#define _ISAI2FILE %B" Ain.ain.is_ai2;
      self#print_newline;
      self#println "GameVersion = %ld" Ain.ain.gver;
      self#print_newline;
      self#println "// Settings for each directory";
      self#println "SourceDir = \".\"";
      self#println "HLLDir = \"HLL\"";
      self#println "ObjDir = \"OBJ\"";
      self#println "OutputDir = \"%s\"" proj.output_dir;
      self#print_newline;
      self#println "Source = {";
      self#println "\t\"main.inc\",";
      self#println "}"

    method print_debug_info =
      debug_info_to_json dbginfo |> Yojson.Basic.to_string |> print_string oc
  end
