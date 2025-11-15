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

(* Expect the following menhir warnings when compiling this grammar:
 *
 *  Warning: one state has shift/reduce conflicts.
 *  Warning: one state has reduce/reduce conflicts.
 *  Warning: one shift/reduce conflict was arbitrarily resolved.
 *  Warning: 7 reduce/reduce conflicts were arbitrarily resolved.
 *)
%{

open Jaf

let implicit_void pos = { ty = Void; location = (pos, pos) }

let stmt loc ast =
  { node=ast; delete_vars=[]; loc }

type varinit = {
  name: string;
  loc: location;
  dims: expression list;
  initval: expression option;
}

let vardecl kind is_const type_spec vi =
  {
    name = vi.name;
    location = vi.loc;
    array_dim = List.rev vi.dims;
    is_const;
    is_private = false;
    kind;
    type_spec;
    initval = vi.initval;
    index = None;
  }

let vardecls kind is_const type_spec var_list =
  let vars = List.map (vardecl kind is_const type_spec) var_list in
  match is_const, type_spec.ty with
  | true, Int ->
    (* If initval is omitted, set it to 0 (for the first constant) or the
       previous value + 1 (for subsequent constants). *)
    Base.List.folding_map vars ~init:(make_expr (ConstInt 0), 0) ~f:(fun (base, delta) v ->
        match v.initval with
        | Some e -> ((e, 1), v)
        | None ->
            let value = make_expr (Binary (Plus, base, make_expr (ConstInt delta))) in
            ((base, delta + 1), { v with initval = Some value }))
  | _ -> vars

let func loc typespec name params body =
  (* XXX: hack for `functype name(void)` *)
  let plist =
    match params with
    | [{ type_spec = { ty = Void; _ }; _ }] -> []
    | _ -> params
  in
  {
    name;
    loc;
    return = typespec;
    params = plist;
    body;
    is_label = false;
    is_private = false;
    index = None;
    class_name = None;
    class_index = None;
  }

let rec multidim_array dims t =
  if dims <= 0 then t else multidim_array (dims - 1) (Array t)

%}

%token <int> I_CONSTANT
%token <float> F_CONSTANT
%token <string> C_CONSTANT
%token <string> S_CONSTANT
%token <string> IDENTIFIER
/* arithmetic */
%token PLUS MINUS TIMES DIV MOD
/* bitwise */
%token LSHIFT RSHIFT BITAND BITOR BITXOR
/* logic/comparison */
%token AND OR LT GT LTE GTE EQUAL NEQUAL REF_EQUAL REF_NEQUAL
/* unary */
%token INC DEC BITNOT LOGNOT
/* assignment */
%token ASSIGN PLUSASSIGN MINUSASSIGN TIMESASSIGN DIVIDEASSIGN MODULOASSIGN
%token ORASSIGN XORASSIGN ANDASSIGN LSHIFTASSIGN RSHIFTASSIGN REFASSIGN
%token SWAP
/* delimiters */
%token LPAREN RPAREN RBRACKET LBRACKET LBRACE RBRACE
%token QUESTION COLON COCO SEMICOLON AT COMMA DOT HASH
/* types */
%token VOID CHAR INT LINT FLOAT BOOL STRING HLL_PARAM HLL_FUNC HLL_DELEGATE
/* keywords */
%token IF ELSE WHILE DO FOR SWITCH CASE DEFAULT NULL THIS NEW
%token GOTO CONTINUE BREAK RETURN JUMP JUMPS ASSERT
%token CONST REF ARRAY WRAP FUNCTYPE DELEGATE STRUCT CLASS PRIVATE PUBLIC ENUM
%token FILE_MACRO LINE_MACRO DATE_MACRO TIME_MACRO GLOBALGROUP UNKNOWN_FUNCTYPE
%token UNKNOWN_DELEGATE

%token EOF

%nonassoc IFX
%nonassoc ELSE

%start jaf
%type <declaration list> jaf

%start hll
%type <declaration list> hll

%%

jaf
  : external_declaration* EOF { $1 }
  ;

hll
  : hll_declaration* EOF { $1 }
  ;

qualified_name
  : IDENTIFIER { $1 }
  | IDENTIFIER COCO qualified_name { $1 ^ "::" ^ $3 }
  ;

qualified_funcname
  : IDENTIFIER { $1 }
  | BITNOT IDENTIFIER { "~" ^ $2 }
  | IDENTIFIER COCO qualified_funcname { $1 ^ "::" ^ $3 }
  ;

primary_expression
  : qualified_name { make_expr ~loc:$sloc (Ident ($1, UnresolvedIdent)) }
  | BITAND qualified_name { make_expr ~loc:$sloc (FuncAddr ($2, None)) }
  | THIS { make_expr ~loc:$sloc This }
  | NULL { make_expr ~loc:$sloc Null }
  | constant { make_expr ~loc:$sloc $1 }
  | string { make_expr ~loc:$sloc $1 }
  | LPAREN expression RPAREN { {$2 with loc=$sloc} }
  ;

(* Due to the way menhir handles reduce/reduce conflicts, the generation rule
 * for message_statement needs to be placed before the constant rule so that
 * C_CONSTANT at the statement level is treated as a message rather than a
 * character constant. *)
message_statement
  : C_CONSTANT { Message $1 }
  ;

constant
  : I_CONSTANT { ConstInt ($1) }
  | C_CONSTANT { ConstChar ($1) }
  | F_CONSTANT { ConstFloat ($1) }
  (* E_CONSTANT *)
  ;

string
  : S_CONSTANT { ConstString ($1) }
  | FILE_MACRO { ConstString $startpos.Lexing.pos_fname }
  | LINE_MACRO { ConstString (Int.to_string $startpos.Lexing.pos_lnum) }
  (* FUNC_MACRO *)
  | DATE_MACRO {
      let tm = Unix.localtime (Unix.time ()) in
      ConstString (Printf.sprintf "%04d/%02d/%02d" (tm.tm_year + 1900) (tm.tm_mon + 1) tm.tm_mday)
    }
  | TIME_MACRO {
      let tm = Unix.localtime (Unix.time ()) in
      ConstString (Printf.sprintf "%02d:%02d:%02d" tm.tm_hour tm.tm_min tm.tm_sec)
    }
  ;

postfix_expression
  : primary_expression { $1 }
  | postfix_expression LBRACKET expression RBRACKET { make_expr ~loc:$sloc (Subscript ($1, $3)) }
  | primitive_type_specifier LPAREN expression RPAREN { make_expr ~loc:$sloc (Cast ($1, $3)) }
  | postfix_expression arglist { make_expr ~loc:$sloc (Call ($1, $2, UnresolvedCall)) }
  | NEW qualified_name { make_expr ~loc:$sloc (New { ty = Unresolved $2; location = $loc($2) }) }
  | postfix_expression DOT IDENTIFIER { make_expr ~loc:$sloc (Member ($1, $3, UnresolvedMember)) }
  | postfix_expression INC { make_expr ~loc:$sloc (Unary (PostInc, $1)) }
  | postfix_expression DEC { make_expr ~loc:$sloc (Unary (PostDec, $1)) }
  ;

arglist
  : LPAREN separated_nonempty_list(COMMA, option(assign_expression)) RPAREN
    { match $2 with [None] -> [] | _ -> $2 }

unary_expression
  : postfix_expression { $1 }
  | INC unary_expression { make_expr ~loc:$sloc (Unary (PreInc, $2)) }
  | DEC unary_expression { make_expr ~loc:$sloc (Unary (PreDec, $2)) }
  | unary_operator cast_expression { make_expr ~loc:$sloc (Unary ($1, $2)) }
  ;

unary_operator
  : PLUS { UPlus }
  | MINUS { UMinus }
  | BITNOT { BitNot }
  | LOGNOT { LogNot }
  ;

cast_expression
  : unary_expression { $1 }
  | LPAREN primitive_type_specifier RPAREN cast_expression { make_expr ~loc:$sloc (Cast ($2, $4)) }
  ;

mul_expression
  : cast_expression { $1 }
  | mul_expression TIMES cast_expression { make_expr ~loc:$sloc (Binary (Times, $1, $3)) }
  | mul_expression DIV cast_expression { make_expr ~loc:$sloc (Binary (Divide, $1, $3)) }
  | mul_expression MOD cast_expression { make_expr ~loc:$sloc (Binary (Modulo, $1, $3)) }
  ;

add_expression
  : mul_expression { $1 }
  | add_expression PLUS mul_expression { make_expr ~loc:$sloc (Binary (Plus, $1, $3)) }
  | add_expression MINUS mul_expression { make_expr ~loc:$sloc (Binary (Minus, $1, $3)) }
  ;

shift_expression
  : add_expression { $1 }
  | shift_expression LSHIFT add_expression { make_expr ~loc:$sloc (Binary (LShift, $1, $3)) }
  | shift_expression RSHIFT add_expression { make_expr ~loc:$sloc (Binary (RShift, $1, $3)) }
  ;

rel_expression
  : shift_expression { $1 }
  | rel_expression LT shift_expression { make_expr ~loc:$sloc (Binary (LT, $1, $3)) }
  | rel_expression GT shift_expression { make_expr ~loc:$sloc (Binary (GT, $1, $3)) }
  | rel_expression LTE shift_expression { make_expr ~loc:$sloc (Binary (LTE, $1, $3)) }
  | rel_expression GTE shift_expression { make_expr ~loc:$sloc (Binary (GTE, $1, $3)) }
  ;

eql_expression
  : rel_expression { $1 }
  | eql_expression EQUAL rel_expression { make_expr ~loc:$sloc (Binary (Equal, $1, $3)) }
  | eql_expression NEQUAL rel_expression { make_expr ~loc:$sloc (Binary (NEqual, $1, $3)) }
  | eql_expression REF_EQUAL rel_expression { make_expr ~loc:$sloc (Binary (RefEqual, $1, $3)) }
  | eql_expression REF_NEQUAL rel_expression { make_expr ~loc:$sloc (Binary (RefNEqual, $1, $3)) }
  ;

and_expression
  : eql_expression { $1 }
  | and_expression BITAND eql_expression { make_expr ~loc:$sloc (Binary (BitAnd, $1, $3)) }
  ;

xor_expression
  : and_expression { $1 }
  | xor_expression BITXOR and_expression { make_expr ~loc:$sloc (Binary (BitXor, $1, $3)) }
  ;

ior_expression
  : xor_expression { $1 }
  | ior_expression BITOR xor_expression { make_expr ~loc:$sloc (Binary (BitOr, $1, $3)) }
  ;

logand_expression
  : ior_expression { $1 }
  | logand_expression AND ior_expression { make_expr ~loc:$sloc (Binary (LogAnd, $1, $3)) }
  ;

logor_expression
  : logand_expression { $1 }
  | logor_expression OR logand_expression { make_expr ~loc:$sloc (Binary (LogOr, $1, $3)) }
  ;

cond_expression
  : logor_expression { $1 }
  | logor_expression QUESTION expression COLON cond_expression { make_expr ~loc:$sloc (Ternary ($1, $3, $5)) }
  ;

assign_expression
  : cond_expression { $1 }
  | unary_expression assign_operator assign_expression { make_expr ~loc:$sloc (Assign ($2, $1, $3)) }
  ;

assign_operator
  : ASSIGN       { EqAssign }
  | PLUSASSIGN   { PlusAssign }
  | MINUSASSIGN  { MinusAssign }
  | TIMESASSIGN  { TimesAssign }
  | DIVIDEASSIGN { DivideAssign }
  | MODULOASSIGN { ModuloAssign }
  | ORASSIGN     { OrAssign }
  | XORASSIGN    { XorAssign }
  | ANDASSIGN    { AndAssign }
  | LSHIFTASSIGN { LShiftAssign }
  | RSHIFTASSIGN { RShiftAssign }
  ;

expression
  : assign_expression { $1 }
  | expression COMMA assign_expression { make_expr ~loc:$sloc (Seq ($1, $3)) }
  ;

constant_expression
  : cond_expression { $1 }
  ;

primitive_type_specifier
  : VOID         { Void }
  | CHAR         { Int }
  | INT          { Int }
  | LINT         { LongInt }
  | FLOAT        { Float }
  | BOOL         { Bool }
  | STRING       { String }
  | STRUCT       { Struct("struct", -1) }
  | HLL_PARAM    { HLLParam }
  | HLL_FUNC     { HLLFunc }
  | HLL_DELEGATE { Delegate (Some ("hll_delegate", -1)) }
  | UNKNOWN_FUNCTYPE { FuncType None }
  | UNKNOWN_DELEGATE { Delegate None }
  ;

atomic_type_specifier
  : primitive_type_specifier { $1 }
  | qualified_name { Unresolved $1 }

type_specifier
  : atomic_type_specifier { $1 }
  (* FIXME: this disallows arrays/wraps of ref-qualified types *)
  | ARRAY AT atomic_type_specifier AT I_CONSTANT { multidim_array $5 $3 }
  | ARRAY AT atomic_type_specifier { Array $3 }
  | WRAP AT type_specifier { Wrap $3 }

statement
  : declaration_statement { stmt $sloc $1 }
  | label_statement { stmt $sloc $1 }
  | switch_statement { stmt $sloc $1 }
  | compound_statement { stmt $sloc $1 }
  | expression_statement { stmt $sloc $1 }
  | selection_statement { stmt $sloc $1 }
  | iteration_statement { stmt $sloc $1 }
  | jump_statement { stmt $sloc $1 }
  | message_statement { stmt $sloc $1 }
  | rassign_statement { stmt $sloc $1 }
  | objswap_statement { stmt $sloc $1 }
  | assert_statement { stmt $sloc $1 }
  ;

switch_statement
  : CASE constant_expression COLON { Case $2 }
  | DEFAULT COLON { Default }
  ;

declaration_statement
  : declaration(IDENTIFIER) { Declarations $1 }

label_statement
  : IDENTIFIER COLON { Label $1 }
  ;

compound_statement
  : block { match $1 with [] -> EmptyStatement | _ -> Compound $1 }
  ;

block
  : LBRACE nonempty_list(statement) RBRACE { $2 }
  | LBRACE RBRACE { [] }
  ;

expression_statement
  : SEMICOLON { EmptyStatement }
  | expression SEMICOLON { Expression ($1) }
  ;

selection_statement
  : IF LPAREN expression RPAREN statement %prec IFX
    { If ($3, $5, stmt ($endpos, $endpos) EmptyStatement) }
  | IF LPAREN expression RPAREN statement ELSE statement
    { If ($3, $5, $7) }
  | SWITCH LPAREN expression RPAREN LBRACE statement+ RBRACE
    { Switch ($3, $6) }
  ;

iteration_statement
  : WHILE LPAREN expression RPAREN statement { While ($3, $5) }
  | DO statement WHILE LPAREN expression RPAREN { DoWhile ($5, $2) }
  | FOR LPAREN expression_statement expression? SEMICOLON expression? RPAREN statement
    { For (stmt $loc($3) $3,
           $4,
           $6,
           $8)
    }
  | FOR LPAREN declaration(IDENTIFIER) expression? SEMICOLON expression? RPAREN statement
    { For (stmt $loc($3) (Declarations $3),
           $4,
           $6,
           $8)
    }
  ; 

jump_statement
  : GOTO IDENTIFIER SEMICOLON { Goto ($2) }
  | CONTINUE SEMICOLON { Continue }
  | BREAK SEMICOLON { Break }
  | RETURN expression? SEMICOLON { Return ($2) }
  | JUMP qualified_name SEMICOLON { Jump $2 }
  | JUMPS expression SEMICOLON { Jumps $2 }
  ;

rassign_statement
  : expression REFASSIGN expression SEMICOLON { RefAssign ($1, $3) }

objswap_statement
  : expression SWAP expression SEMICOLON { ObjSwap ($1, $3) }

assert_statement
  : ASSERT LPAREN expression RPAREN SEMICOLON
    { let args = [Some $3;
                  Some (make_expr ~loc:$loc($3) (ConstString (expr_to_string $3)));
                  Some (make_expr ~loc:$loc($1) (ConstString $startpos.Lexing.pos_fname));
                  Some (make_expr ~loc:$loc($1) (ConstInt $startpos.pos_lnum))] in
      Expression (make_expr ~loc:$sloc (Call (make_expr ~loc:$loc($1) (Ident ("assert", UnresolvedIdent)), args, UnresolvedCall))) }

declaration(X)
  : CONST declaration_specifiers separated_nonempty_list(COMMA, init_declarator(X)) SEMICOLON
    { { decl_loc = $sloc; typespec = $2; is_const_decls = true; vars = vardecls LocalVar true $2 $3 } }
  | declaration_specifiers separated_nonempty_list(COMMA, init_declarator(X)) SEMICOLON
    { { decl_loc = $sloc; typespec = $1; is_const_decls = false; vars = vardecls LocalVar false $1 $2 } }
  ;

declaration_specifiers
  : REF type_specifier { { location = $sloc; ty = Ref $2 } }
  | type_specifier { { location = $sloc; ty = $1 } }
  ;

init_declarator(X)
  : declarator(X) ASSIGN assign_expression { { $1 with initval = Some $3; loc = $sloc } }
  | declarator(X) { $1 }
  ;

declarator(X)
  : X { { name=$1; dims=[]; initval=None; loc=$sloc } }
  | array_allocation(X) { $1 }
  ;

array_allocation(X)
  : X LBRACKET expression RBRACKET { { name=$1; loc=$sloc; initval=None; dims=[$3] } }
  | array_allocation(X) LBRACKET expression RBRACKET
    { { $1 with dims = $3 :: $1.dims; loc = $sloc } }
  ;

external_declaration
  : declaration(qualified_name)
    { Global { $1 with vars = (List.map (fun d -> { d with kind = GlobalVar }) $1.vars) } }
  | ioption(declaration_specifiers) qualified_funcname parameter_list(init_declarator(IDENTIFIER)) block
    { Function (func $sloc (Option.value $1 ~default:(implicit_void $symbolstartpos)) $2 $3 (Some $4)) }
  | HASH qualified_name LPAREN VOID? RPAREN block
    { Function { (func $sloc (implicit_void $symbolstartpos) $2 [] (Some $6)) with is_label=true } }
  | FUNCTYPE declaration_specifiers qualified_name functype_parameter_list SEMICOLON
    { FuncTypeDef (func $sloc $2 $3 $4 None) }
  | DELEGATE declaration_specifiers qualified_name functype_parameter_list SEMICOLON
    { DelegateDef (func $sloc $2 $3 $4 None) }
  | struct_or_class qualified_name LBRACE struct_declaration* RBRACE SEMICOLON
    { StructDef ({ loc = $sloc; is_class = $1; name = $2; decls = $4 }) }
  | ENUM enumerator_list SEMICOLON
    { Enum ({ loc=$sloc; name=None; values=$2 }) }
  | ENUM IDENTIFIER enumerator_list SEMICOLON
    { Enum ({ loc=$sloc; name=Some $2; values=$3 }) }
  | GLOBALGROUP IDENTIFIER SEMICOLON
    { GlobalGroup { name = $2; loc = $loc; vardecls = [] } }
  | GLOBALGROUP IDENTIFIER LBRACE declaration(qualified_name)* RBRACE
    {
      let update_decls ds = { ds with vars = (List.map (fun d -> { d with kind = GlobalVar }) ds.vars) } in
      GlobalGroup { name = $2; loc = $loc; vardecls = List.map update_decls $4 }
    }

hll_declaration
  : declaration_specifiers IDENTIFIER parameter_list(declarator(IDENTIFIER)) SEMICOLON
    { Function (func $sloc $1 $2 $3 None) }

%inline struct_or_class
  : STRUCT { false }
  | CLASS { true }
  ;

enumerator_list
  : LBRACE separated_nonempty_list(COMMA, enumerator) RBRACE { $2 }
  ;

enumerator
  : IDENTIFIER ASSIGN constant_expression { ($1, Some $3) }
  | IDENTIFIER { ($1, None) }
  ;

parameter_declaration(X)
  : declaration_specifiers X { vardecl Parameter false $1 { $2 with loc=$sloc } }
  ;

parameter_list(X)
  : LPAREN separated_list(COMMA, parameter_declaration(X)) RPAREN { $2 }
  | LPAREN VOID RPAREN { [] }
  ;

functype_parameter_declaration
  : declaration_specifiers { vardecl Parameter false $1 { name="<anonymous>"; dims=[]; initval=None; loc=$sloc } }
  | parameter_declaration(declarator(IDENTIFIER)) { $1 }
  ;

functype_parameter_list
  : LPAREN separated_list(COMMA, functype_parameter_declaration) RPAREN { $2 }
  ;

struct_declaration
  : access_specifier COLON
    { AccessSpecifier $1 }
  | CONST declaration_specifiers separated_nonempty_list(COMMA, init_declarator(IDENTIFIER)) SEMICOLON
    { let vars = vardecls ClassVar true $2 $3 in
      MemberDecl { decl_loc=$sloc; typespec=$2; is_const_decls = true; vars } }
  | declaration_specifiers separated_nonempty_list(COMMA, declarator(IDENTIFIER)) SEMICOLON
    { let vars = vardecls ClassVar false $1 $2 in
      MemberDecl { decl_loc=$sloc; typespec=$1; is_const_decls = false; vars } }
  | declaration_specifiers IDENTIFIER parameter_list(init_declarator(IDENTIFIER)) opt_body
    { Method (func $sloc $1 $2 $3 $4) }
  | IDENTIFIER LPAREN VOID? RPAREN opt_body
    { Constructor (func $sloc (implicit_void $symbolstartpos) $1 [] $5) }
  | BITNOT IDENTIFIER LPAREN RPAREN opt_body
    { Destructor (func $sloc (implicit_void $symbolstartpos) ("~" ^ $2) [] $5) }
  ;

access_specifier
  : PUBLIC { Public }
  | PRIVATE { Private }
  ;

opt_body
  : SEMICOLON { None }
  | block { Some $1 }
  ;
