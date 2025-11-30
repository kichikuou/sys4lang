(* Copyright (C) 2025 kichikuou <KichikuouChrome@gmail.com>
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

(* LSP expects character offsets based on utf-16 representation. *)
let count_utf16_code_units_of_utf8_bytes bytes start end_ =
  let rec loop i n =
    if i >= end_ then n
    else
      let ch = Bytes.get bytes i in
      if Char.O.(ch <= '\x7f') then loop (i + 1) (n + 1)
      else if Char.O.(ch <= '\xbf') then failwith "invalid utf-8 sequence"
      else if Char.O.(ch <= '\xdf') then loop (i + 2) (n + 1)
      else if Char.O.(ch <= '\xef') then loop (i + 3) (n + 1)
      else if Char.O.(ch <= '\xf7') then loop (i + 4) (n + 2)
      else failwith "invalid utf-8 sequence"
  in
  loop start 0

let to_lsp_position (text : bytes) (p : Lexing.position) =
  try
    Lsp.Types.Position.create ~line:(p.pos_lnum - 1)
      ~character:
        (count_utf16_code_units_of_utf8_bytes text p.pos_bol p.pos_cnum)
  with _ ->
    Printf.failwithf "to_lsp_position failed: %s %d %d %d" p.pos_fname
      p.pos_lnum p.pos_bol p.pos_cnum ()

let to_lsp_range text (start, end_) =
  Lsp.Types.Range.create
    ~start:(to_lsp_position text start)
    ~end_:(to_lsp_position text end_)

let range_contains text range (pos : Lsp.Types.Position.t) =
  let Lsp.Types.Range.{ start; end_ } = to_lsp_range text range in
  (start.line < pos.line
  || (start.line = pos.line && start.character <= pos.character))
  && (end_.line > pos.line
     || (end_.line = pos.line && end_.character >= pos.character))

type t = {
  ctx : Jaf.context;
  text : bytes;
  toplevel : Jaf.declaration list;
  errors : (Lsp.Types.Range.t * string) list;
}

external reraise : exn -> 'a = "%reraise"

let make_error lexbuf exn =
  let make (lexbuf : Lexing.lexbuf) loc message =
    let range = to_lsp_range lexbuf.lex_buffer loc in
    (range, message)
  in
  match exn with
  | Lexer.Error | Parser.Error ->
      make lexbuf (lexbuf.lex_start_p, lexbuf.lex_curr_p) "Syntax error."
  | CompileError.Compile_error (Error (msg, loc)) -> make lexbuf loc msg
  | e -> reraise e

let create ctx ~fname text =
  let lexbuf = Lexing.from_string text in
  Lexing.set_filename lexbuf fname;
  try
    let toplevel = Parser.jaf Lexer.token lexbuf in
    Declarations.register_type_declarations ctx toplevel;
    Declarations.resolve_types ctx toplevel false;
    let errors =
      TypeAnalysis.check_types ctx toplevel
      |> List.map ~f:(fun ce ->
          make_error lexbuf (CompileError.Compile_error ce))
    in
    { ctx; text = lexbuf.lex_buffer; toplevel; errors }
  with e ->
    {
      ctx;
      text = lexbuf.lex_buffer;
      toplevel = [];
      errors = [ make_error lexbuf e ];
    }

let initial_scan ctx ~fname ?hll_import_name text =
  let lexbuf = Lexing.from_string text in
  Lexing.set_filename lexbuf fname;
  try
    match hll_import_name with
    | None ->
        let decls = Parser.jaf Lexer.token lexbuf in
        Declarations.register_type_declarations ctx decls;
        Declarations.resolve_types ctx decls true
    | Some import_name ->
        let hll_name = Stdlib.Filename.(chop_extension (basename fname)) in
        let decls = Parser.hll Lexer.token lexbuf in
        Declarations.resolve_hll_types ctx decls;
        Declarations.resolve_types ctx decls false;
        Declarations.define_library ctx decls hll_name import_name
  with _ -> ()

class ast_locator (doc : t) (pos : Lsp.Types.Position.t) =
  object
    inherit Jaf.ivisitor doc.ctx as super
    val mutable nodes : Jaf.ast_node list = []
    method nodes = nodes

    method! visit_expression expr =
      if range_contains doc.text expr.loc pos then (
        nodes <- ASTExpression expr :: nodes;
        super#visit_expression expr)

    method! visit_statement stmt =
      if range_contains doc.text stmt.loc pos then (
        nodes <- ASTStatement stmt :: nodes;
        super#visit_statement stmt)

    method! visit_declaration decl =
      let node = Jaf.ASTDeclaration decl in
      if range_contains doc.text (Jaf.ast_node_pos node) pos then (
        nodes <- node :: nodes;
        super#visit_declaration decl)

    method! visit_struct_declaration decl =
      let node = Jaf.ASTStructDecl decl in
      if range_contains doc.text (Jaf.ast_node_pos node) pos then (
        nodes <- node :: nodes;
        super#visit_struct_declaration decl)

    method! visit_variable var =
      let node = Jaf.ASTVariable var in
      if range_contains doc.text (Jaf.ast_node_pos node) pos then (
        nodes <- node :: nodes;
        super#visit_variable var)

    method! visit_type_specifier t =
      let node = Jaf.ASTType t in
      if range_contains doc.text (Jaf.ast_node_pos node) pos then (
        nodes <- node :: nodes;
        super#visit_type_specifier t)
  end

(* Returns the most specific node first. *)
let get_nodes_for_pos doc pos =
  let locator = new ast_locator doc pos in
  locator#visit_toplevel doc.toplevel;
  locator#nodes
