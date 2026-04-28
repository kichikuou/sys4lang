(* Copyright (C) 2026 kichikuou <KichikuouChrome@gmail.com>
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
module Lsp = Linol_lsp.Lsp

(* --- UTF-8 / UTF-16 position helpers --------------------------------- *)

let line_start_byte text line =
  let len = Bytes.length text in
  let rec loop i remaining =
    if remaining <= 0 || i >= len then i
    else if Char.equal (Bytes.get text i) '\n' then loop (i + 1) (remaining - 1)
    else loop (i + 1) remaining
  in
  loop 0 line

(* Convert a UTF-16 character offset on a line to a UTF-8 byte offset. *)
let byte_offset_of_utf16 text line_start target_utf16 =
  let len = Bytes.length text in
  let rec loop byte_pos utf16 =
    if utf16 >= target_utf16 || byte_pos >= len then byte_pos
    else
      let c = Char.to_int (Bytes.get text byte_pos) in
      if c = Char.to_int '\n' then byte_pos
      else if c < 0x80 then loop (byte_pos + 1) (utf16 + 1)
      else if c < 0xc0 then byte_pos (* invalid; bail *)
      else if c < 0xe0 then loop (byte_pos + 2) (utf16 + 1)
      else if c < 0xf0 then loop (byte_pos + 3) (utf16 + 1)
      else if c < 0xf8 then loop (byte_pos + 4) (utf16 + 2)
      else byte_pos
  in
  loop line_start 0

(* --- Identifier boundary analysis (UTF-8 aware) --------------------- *)

(* JAF identifier characters, per lexer.mll:
   l = [a-zA-Z_] | uch,  a = [a-zA-Z_0-9] | uch
   uch = u2 u | u3 u u | u4 u u u  (UTF-8 multibyte, 2–4 bytes) *)

let is_ascii_ident_cont c = Char.is_alphanum c || Char.equal c '_'

let is_utf8_cont c =
  let n = Char.to_int c in
  n >= 0x80 && n < 0xc0

let is_utf8_leader c =
  let n = Char.to_int c in
  n >= 0xc2 && n <= 0xf4

(* Walk backwards from [pos] over identifier characters, stopping at
   [line_start]. Returns the byte offset of the start of the identifier
   immediately preceding [pos] (or [pos] itself if there is none). *)
let skip_ident_backwards text line_start pos =
  let rec skip_cont j =
    if j <= line_start then j
    else if is_utf8_cont (Bytes.get text (j - 1)) then skip_cont (j - 1)
    else j
  in
  let rec loop i =
    if i <= line_start then i
    else
      let b = Bytes.get text (i - 1) in
      if is_ascii_ident_cont b then loop (i - 1)
      else if is_utf8_cont b then
        let j = skip_cont i in
        if j > line_start && is_utf8_leader (Bytes.get text (j - 1)) then
          loop (j - 1)
        else i
      else i
  in
  loop pos

(* [Member dot_idx] indicates that the cursor is in member-completion mode,
   with the dot at byte offset [dot_idx]. *)
type context_kind = Identifier | Member of int

let classify text line_start cursor =
  let start = skip_ident_backwards text line_start cursor in
  if start > line_start && Char.equal (Bytes.get text (start - 1)) '.' then
    Member (start - 1)
  else Identifier

(* --- Scope analysis ------------------------------------------------- *)

(* Compare an LSP position with a (Lexing) source location. *)
let position_before (pos : Lsp.Types.Position.t) (p : Lexing.position) text =
  let p_lsp = Document.to_lsp_position text p in
  pos.line < p_lsp.line
  || (pos.line = p_lsp.line && pos.character < p_lsp.character)

let loc_before_pos pos text ((_, end_) : Jaf.location) =
  (* True if the statement ends before the cursor. *)
  let end_lsp = Document.to_lsp_position text end_ in
  end_lsp.line < pos.Lsp.Types.Position.line
  || (end_lsp.line = pos.line && end_lsp.character <= pos.character)

let loc_contains_pos pos text ((start, end_) : Jaf.location) =
  (not (position_before pos start text)) && position_before pos end_ text

(* Snapshot collected at the cursor position: variables visible in scope,
   the name of the enclosing class (if any), and the enclosing fundecl
   (used to set up an environment for analyzing a member receiver). *)
type scope_snapshot = {
  locals : Jaf.variable list;
  enclosing_class : string option;
  enclosing_function : Jaf.fundecl option;
}

let empty_snapshot =
  { locals = []; enclosing_class = None; enclosing_function = None }

class scope_collector (ctx : Jaf.context) text pos =
  object (self)
    inherit Jaf.ivisitor ctx as super
    val mutable snapshot : scope_snapshot = empty_snapshot
    val mutable snapshot_taken : bool = false
    method snapshot = snapshot

    method private take_snapshot () =
      if not snapshot_taken then (
        let enclosing_function = self#env#current_function in
        let enclosing_class =
          match enclosing_function with
          | Some f -> f.class_name
          | None -> self#current_struct_name
        in
        snapshot <-
          { locals = self#env#var_list; enclosing_class; enclosing_function };
        snapshot_taken <- true)

    method! visit_fundecl (f : Jaf.fundecl) =
      if loc_contains_pos pos text f.loc then (
        self#visit_type_specifier f.return;
        List.iter f.params ~f:self#visit_variable;
        Option.iter f.body ~f:(fun body ->
            Stack.push env_stack (new Jaf.environment ctx (Some f));
            List.iter body ~f:self#visit_statement;
            self#take_snapshot ();
            Stack.pop_exn env_stack |> ignore))
    (* else: this fundecl doesn't contain the cursor - skip entirely. *)

    method! visit_statement (s : Jaf.statement) =
      if loc_before_pos pos text s.loc then
        (* Statement ends before the cursor; process for env side effects
           (e.g., variable declarations). *)
        super#visit_statement s
      else if loc_contains_pos pos text s.loc then
        match s.node with
        | Compound stmts ->
            self#env#push;
            List.iter stmts ~f:self#visit_statement;
            self#take_snapshot ();
            self#env#pop
        | For (init, test, inc, body) ->
            self#env#push;
            self#visit_statement init;
            Option.iter test ~f:self#visit_expression;
            Option.iter inc ~f:self#visit_expression;
            self#visit_statement body;
            self#take_snapshot ();
            self#env#pop
        | _ ->
            (* Recurse first so that nested constructs (e.g., the body of a
               while/if/switch) get a chance to set up their inner scope and
               take the snapshot from there. If no descendant snapshot fires,
               fall back to capturing the env at this level. *)
            super#visit_statement s;
            self#take_snapshot ()
    (* else: statement starts after the cursor - skip. *)
  end

let collect_scope ctx text pos toplevel =
  let v = new scope_collector ctx text pos in
  v#visit_toplevel toplevel;
  v#snapshot

(* --- Candidate generation ------------------------------------------- *)

let item ~label ~kind ?detail () =
  Lsp.Types.CompletionItem.create ~label ~kind ?detail ()

(* Skip class methods, lambdas, and the synthetic [NULL] entry. *)
let is_non_global_function (f : Jaf.fundecl) =
  Option.is_some f.class_name || f.is_lambda || String.equal f.name "NULL"

let variable_kind (v : Jaf.variable) =
  if v.is_const then Lsp.Types.CompletionItemKind.Constant else Variable

let variable_item (v : Jaf.variable) =
  item ~label:v.name ~kind:(variable_kind v)
    ~detail:(Jaf.jaf_type_to_string v.type_spec.ty)
    ()

let function_item ~kind (f : Jaf.fundecl) =
  item ~label:f.name ~kind
    ~detail:(Jaf.decl_to_string (Jaf.Function { f with body = None }))
    ()

let keyword_item label = item ~label ~kind:Keyword ()

let global_keyword_candidates () =
  [ keyword_item "NULL"; keyword_item "system" ]

let this_keyword_candidate () = keyword_item "this"

let global_identifier_candidates (ctx : Jaf.context) =
  let items = ref [] in
  let add it = items := it :: !items in
  Hashtbl.iter ctx.globals ~f:(fun v -> add (variable_item v));
  Hashtbl.iter ctx.functions ~f:(fun f ->
      if not (is_non_global_function f) then
        add (function_item ~kind:Function f));
  Hashtbl.iter_keys ctx.structs ~f:(fun name ->
      add (item ~label:name ~kind:Class ()));
  Hashtbl.iter_keys ctx.functypes ~f:(fun name ->
      add (item ~label:name ~kind:Interface ()));
  Hashtbl.iter_keys ctx.delegates ~f:(fun name ->
      add (item ~label:name ~kind:Interface ()));
  Hashtbl.iter_keys ctx.libraries ~f:(fun name ->
      add (item ~label:name ~kind:Module ()));
  !items

let local_candidates (locals : Jaf.variable list) =
  (* env#var_list can contain duplicates (outer scope entries are kept as
     the scope is extended); dedupe by name, preferring the most recent. *)
  let seen = Hash_set.create (module String) in
  List.filter_map locals ~f:(fun v ->
      if Hash_set.mem seen v.name then None
      else (
        Hash_set.add seen v.name;
        Some (variable_item v)))

let is_destructor (f : Jaf.fundecl) = String.is_prefix f.name ~prefix:"~"

let class_member_candidates (ctx : Jaf.context) ?(include_private = false)
    class_name =
  match Hashtbl.find ctx.structs class_name with
  | None -> []
  | Some s ->
      let visible_var (v : Jaf.variable) =
        include_private || not v.is_private
      in
      let visible_fn (f : Jaf.fundecl) = include_private || not f.is_private in
      let field_items =
        Hashtbl.data s.members |> List.filter ~f:visible_var
        |> List.map ~f:(fun (v : Jaf.variable) ->
            item ~label:v.name ~kind:Field
              ~detail:(Jaf.jaf_type_to_string v.type_spec.ty)
              ())
      in
      let method_items =
        Hashtbl.data ctx.functions
        |> List.filter ~f:(fun (f : Jaf.fundecl) ->
            (match f.class_name with
              | Some cn -> String.equal cn class_name
              | None -> false)
            && (not (Jaf.is_constructor f))
            && (not (is_destructor f))
            && visible_fn f)
        |> List.map ~f:(function_item ~kind:Method)
      in
      field_items @ method_items

(* --- Member completion: receiver text extraction -------------------- *)

(* Walk backward from [end_idx] to find the start byte of an expression.
   Handles identifier chains, '.' chains, balanced (), [], and string
   literals (including strings nested inside brackets). Used both for
   member completion (right boundary = '.') and signature help
   (right boundary = '('). Returns the [start, end_idx) byte range of
   the expression, or [None] if no plausible expression was found. *)
let extract_receiver text line_start end_idx =
  (* State: byte index [i] (walking backward), bracket [depth], and
     whether we are currently scanning the inside of a string literal
     (between two double-quote characters, walking backward). *)
  let rec walk i depth in_string =
    if i < line_start then i + 1
    else
      let c = Bytes.get text i in
      if in_string then
        (* Skip everything until we find the matching opening quote. *)
        walk (i - 1) depth (not (Char.equal c '"'))
      else if depth > 0 then
        match c with
        | ']' | ')' -> walk (i - 1) (depth + 1) false
        | '[' | '(' -> walk (i - 1) (depth - 1) false
        | '"' -> walk (i - 1) depth true
        | _ -> walk (i - 1) depth false
      else
        match c with
        | ']' | ')' -> walk (i - 1) 1 false
        | '.' -> walk (i - 1) 0 false
        | '"' -> walk (i - 1) 0 true
        | c when is_ascii_ident_cont c || is_utf8_cont c || is_utf8_leader c ->
            walk (i - 1) 0 false
        | _ -> i + 1
  in
  let start = walk (end_idx - 1) 0 false in
  if start >= end_idx then None else Some (start, end_idx)

(* --- Member completion: receiver type analysis ---------------------- *)

(* Subclass of [type_analyze_visitor] that starts with a pre-built
   environment matching the cursor position (enclosing function + locals
   in scope). The base class normally builds the env from a fundecl visit;
   here we feed it directly. *)
class scoped_type_analyzer ctx (initial_env : Jaf.environment) =
  object
    inherit TypeAnalysis.type_analyze_visitor ctx
    initializer Stack.push env_stack initial_env
  end

let parse_receiver text =
  let lexbuf = Lexing.from_string text in
  try Some (Parser.expression_eof Lexer.token lexbuf) with _ -> None

(* Build an environment that matches the cursor's lexical scope, then
   type-analyze the receiver expression in that environment. Returns
   the typed expression or [None] on parse / type errors. *)
let type_analyze_receiver ctx (snapshot : scope_snapshot) text =
  match parse_receiver text with
  | None -> None
  | Some expr -> (
      let env = new Jaf.environment ctx snapshot.enclosing_function in
      List.iter snapshot.locals ~f:(fun v -> env#push_var v);
      let v = new scoped_type_analyzer ctx env in
      try
        v#visit_expression expr;
        Some expr
      with _ -> None)

(* --- Member completion: candidate generation ------------------------ *)

let strip_ref = function Jaf.Ref t -> t | t -> t

let builtin_method_item ctx receiver_ty (b : Bytecode.builtin) =
  try
    let f = Builtin.fundecl_of_builtin ctx b receiver_ty None in
    Some (function_item ~kind:Method f)
  with _ -> None

let builtin_candidates (ctx : Jaf.context) (ty : Jaf.jaf_type) =
  let lib_name, builtins =
    match ty with
    | Jaf.Int -> ("Int", Bytecode.int_builtins)
    | Float -> ("Float", Bytecode.float_builtins)
    | String -> ("String", Bytecode.string_builtins)
    | Array _ -> ("Array", Bytecode.array_builtins)
    | Delegate _ -> ("Delegate", Bytecode.delegate_builtins)
    | _ -> ("", [])
  in
  if String.is_empty lib_name then []
  else
    match Hashtbl.find ctx.libraries lib_name with
    | Some l when ctx.version >= 800 ->
        Hashtbl.data l.functions |> List.map ~f:(function_item ~kind:Method)
    | _ -> List.filter_map builtins ~f:(builtin_method_item ctx ty)

let syscall_candidates () =
  List.map Bytecode.all_syscalls ~f:(fun sys ->
      let f = Builtin.fundecl_of_syscall sys in
      function_item ~kind:Function f)

let hll_function_candidates (ctx : Jaf.context) lib_name =
  match Hashtbl.find ctx.libraries lib_name with
  | None -> []
  | Some lib ->
      Hashtbl.data lib.functions |> List.map ~f:(function_item ~kind:Function)

let with_sort_prefix prefix items =
  List.map items ~f:(fun (it : Lsp.Types.CompletionItem.t) ->
      { it with sortText = Some (prefix ^ it.label) })

let member_candidates ctx ~viewer_class (expr : Jaf.expression) =
  match expr.node with
  | Ident (_, System) -> syscall_candidates ()
  | Ident (lib_name, HLLName) -> hll_function_candidates ctx lib_name
  | _ -> (
      match strip_ref expr.ty with
      | Struct (name, _) ->
          let include_private =
            match viewer_class with
            | Some c -> String.equal c name
            | None -> false
          in
          class_member_candidates ctx ~include_private name
      | (Int | Float | String | Array _ | Delegate _) as ty ->
          builtin_candidates ctx ty
      | _ -> [])

(* --- Entry point ----------------------------------------------------- *)

let get_completion ctx ~text ~scope (pos : Lsp.Types.Position.t) =
  let line_start = line_start_byte text pos.line in
  let cursor = byte_offset_of_utf16 text line_start pos.character in
  let snapshot () =
    match scope with
    | None -> empty_snapshot
    | Some (toplevel, scope_text) -> collect_scope ctx scope_text pos toplevel
  in
  let result items =
    Some
      (`CompletionList
         (Lsp.Types.CompletionList.create ~isIncomplete:false ~items ()))
  in
  match classify text line_start cursor with
  | Identifier ->
      let snap = snapshot () in
      let class_items =
        match snap.enclosing_class with
        | None -> []
        | Some cn ->
            this_keyword_candidate ()
            :: class_member_candidates ctx ~include_private:true cn
      in
      let items =
        with_sort_prefix "0_" (local_candidates snap.locals)
        @ with_sort_prefix "1_" class_items
        @ with_sort_prefix "2_"
            (global_identifier_candidates ctx @ global_keyword_candidates ())
      in
      result items
  | Member dot_idx -> (
      match extract_receiver text line_start dot_idx with
      | None -> None
      | Some (s, e) -> (
          let receiver_text = Stdlib.Bytes.sub_string text s (e - s) in
          let snap = snapshot () in
          match type_analyze_receiver ctx snap receiver_text with
          | None -> None
          | Some expr ->
              result
                (member_candidates ctx ~viewer_class:snap.enclosing_class expr))
      )

(* --- Signature help -------------------------------------------------- *)

(* Cap on how far we scan backward from the cursor when looking for the
   enclosing call site. Calls longer than this are not supported (and
   are extremely rare in practice). *)
let max_signature_scan_back = 4096

(* Byte offset of the start of the line containing [byte_idx]. *)
let line_start_of_byte text byte_idx =
  match Stdlib.Bytes.rindex_from_opt text (byte_idx - 1) '\n' with
  | None -> 0
  | Some i -> i + 1

(* Byte offset of the next '\n' at or after [byte_idx], or [len] if none. *)
let line_end_of_byte text byte_idx =
  match Stdlib.Bytes.index_from_opt text byte_idx '\n' with
  | None -> Bytes.length text
  | Some i -> i

(* Forward-scan a single line [line_start, line_end) and return the byte
   offset of the first "//" that is not inside a string literal. Returns
   [line_end] if the line has no line comment. *)
let line_comment_start text line_start line_end =
  let rec loop i in_string =
    if i >= line_end then line_end
    else
      let c = Bytes.get text i in
      if in_string then loop (i + 1) (not (Char.equal c '"'))
      else
        match c with
        | '"' -> loop (i + 1) true
        | '/' when i + 1 < line_end && Char.equal (Bytes.get text (i + 1)) '/'
          ->
            i
        | _ -> loop (i + 1) false
  in
  loop line_start false

(* Scan backward from [cursor] looking for the innermost unmatched '('.
   Returns its byte offset along with the number of top-level commas
   between it and the cursor (= activeParameter index). Returns [None]
   if the cursor is not inside a call. Stops at statement / block
   boundaries (';', '{', '}'). Bytes inside a '//' line comment are
   masked out (treated as whitespace) so a '(' or ',' in a comment is
   not picked up. '/* */' block comments are not handled. *)
let scan_back_for_call_site text cursor =
  let len = Bytes.length text in
  let cursor = min cursor len in
  let stop = max 0 (cursor - max_signature_scan_back) in
  let initial_line_start = line_start_of_byte text cursor in
  let initial_line_end = line_end_of_byte text initial_line_start in
  let initial_comment_start =
    line_comment_start text initial_line_start initial_line_end
  in
  let rec loop i depth arg_index in_string comment_start =
    if i < stop then None
    else
      let c = Bytes.get text i in
      if Char.equal c '\n' then
        let new_line_start = line_start_of_byte text i in
        let new_comment_start = line_comment_start text new_line_start i in
        loop (i - 1) depth arg_index in_string new_comment_start
      else if i >= comment_start then
        loop (i - 1) depth arg_index in_string comment_start
      else if in_string then
        loop (i - 1) depth arg_index (not (Char.equal c '"')) comment_start
      else if depth > 0 then
        match c with
        | ')' | ']' -> loop (i - 1) (depth + 1) arg_index false comment_start
        | '(' | '[' -> loop (i - 1) (depth - 1) arg_index false comment_start
        | '"' -> loop (i - 1) depth arg_index true comment_start
        | _ -> loop (i - 1) depth arg_index false comment_start
      else
        match c with
        | '(' -> Some (i, arg_index)
        | ',' -> loop (i - 1) 0 (arg_index + 1) false comment_start
        | ')' | ']' -> loop (i - 1) 1 arg_index false comment_start
        | ';' | '{' | '}' -> None
        | '"' -> loop (i - 1) 0 arg_index true comment_start
        | _ -> loop (i - 1) 0 arg_index false comment_start
  in
  loop (cursor - 1) 0 0 false initial_comment_start

(* Count UTF-16 code units in a UTF-8 encoded string. ASCII = 1 unit,
   2–3 byte sequences = 1 unit (BMP), 4 byte sequences = 2 units
   (a surrogate pair). Invalid bytes are skipped without contributing. *)
let utf16_units_of_string s =
  let len = String.length s in
  let rec loop i count =
    if i >= len then count
    else
      let c = Char.to_int s.[i] in
      if c < 0x80 then loop (i + 1) (count + 1)
      else if c < 0xc0 then loop (i + 1) count
      else if c < 0xe0 then loop (i + 2) (count + 1)
      else if c < 0xf0 then loop (i + 3) (count + 1)
      else loop (i + 4) (count + 2)
  in
  loop 0 0

(* Build the signature label and per-parameter UTF-16 offsets in lockstep.
   Output mirrors [Jaf.decl_to_string (Function { f with body = None })]:
   `<ret> <name>(<p1>, <p2>, ...);`. The buffer contents are UTF-8 (LSP
   transmits the label as UTF-8), but [ParameterInformation.label] offsets
   are in UTF-16 code units, so we keep a parallel counter. *)
let format_signature (f : Jaf.fundecl) =
  let buf = Buffer.create 64 in
  let utf16_pos = ref 0 in
  let append s =
    Buffer.add_string buf s;
    utf16_pos := !utf16_pos + utf16_units_of_string s
  in
  let append_param (p : Jaf.variable) =
    let start = !utf16_pos in
    append (Jaf.var_to_string' p);
    let end_ = !utf16_pos in
    Lsp.Types.ParameterInformation.create ~label:(`Offset (start, end_)) ()
  in
  append (Jaf.jaf_type_to_string f.return.ty);
  append " ";
  append f.name;
  append "(";
  let parameters =
    match f.params with
    | [] -> []
    | p :: ps ->
        let first = append_param p in
        let rest =
          List.map ps ~f:(fun p ->
              append ", ";
              append_param p)
        in
        first :: rest
  in
  append ");";
  Lsp.Types.SignatureInformation.create ~label:(Buffer.contents buf) ~parameters
    ()

(* Resolve the typed callee expression to a fundecl. *)
let fundecl_of_callee (ctx : Jaf.context) (e : Jaf.expression) =
  match e.node with
  | Ident (_, FunctionName name) | Member (_, _, ClassMethod (name, _)) ->
      Hashtbl.find ctx.functions name
  | Member (_, _, SystemFunction sys) -> Some (Builtin.fundecl_of_syscall sys)
  | Member (_, _, HLLFunction (lib, fn)) -> Jaf.find_hll_function ctx lib fn
  | Member (recv, _, BuiltinMethod b) -> (
      try Some (Builtin.fundecl_of_builtin ctx b (strip_ref recv.ty) None)
      with _ -> None)
  | _ -> (
      (* Funcptr / functype / delegate value: fall back on the expression's
         resolved type. *)
      match strip_ref e.ty with
      | FuncType (Some (name, _)) -> Hashtbl.find ctx.functypes name
      | Delegate (Some (name, _)) -> Hashtbl.find ctx.delegates name
      | _ -> None)

(* `assert` is a keyword in the JAF grammar (it's a statement form, not a
   regular function call) and the parser auto-supplies three trailing
   arguments (stringified expression, file, line). The user only ever
   types the condition, so synthesize a one-parameter signature directly
   instead of going through the parse / type-analysis path - which can't
   parse `assert` as an expression anyway. *)
let assert_fundecl : Jaf.fundecl =
  let int_param : Jaf.variable =
    {
      name = "condition";
      location = Jaf.dummy_location;
      array_dim = [];
      is_const = false;
      is_private = false;
      kind = Parameter;
      type_spec = { ty = Int; location = Jaf.dummy_location };
      initval = None;
      index = Some 0;
    }
  in
  {
    name = "assert";
    loc = Jaf.dummy_location;
    return = { ty = Void; location = Jaf.dummy_location };
    params = [ int_param ];
    body = None;
    is_label = false;
    is_lambda = false;
    is_private = false;
    index = None;
    class_name = None;
    class_index = None;
  }

let signature_help_response f arg_index =
  Lsp.Types.SignatureHelp.create
    ~signatures:[ format_signature f ]
    ~activeSignature:0 ~activeParameter:(Some arg_index) ()

let get_signature_help ctx ~text ~scope (pos : Lsp.Types.Position.t) =
  let line_start = line_start_byte text pos.line in
  let cursor = byte_offset_of_utf16 text line_start pos.character in
  match scan_back_for_call_site text cursor with
  | None -> None
  | Some (open_paren_idx, arg_index) -> (
      let callee_line_start = line_start_of_byte text open_paren_idx in
      match extract_receiver text callee_line_start open_paren_idx with
      | None -> None
      | Some (s, e) -> (
          let callee_text = Stdlib.Bytes.sub_string text s (e - s) in
          if String.equal callee_text "assert" then
            Some (signature_help_response assert_fundecl arg_index)
          else
            let snap =
              match scope with
              | None -> empty_snapshot
              | Some (toplevel, scope_text) ->
                  collect_scope ctx scope_text pos toplevel
            in
            match type_analyze_receiver ctx snap callee_text with
            | None -> None
            | Some expr ->
                Option.map (fundecl_of_callee ctx expr) ~f:(fun f ->
                    signature_help_response f arg_index)))
