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
module Lsp = Linol_lsp.Lsp

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
  path : string;
  import_name : string option;
  lexbuf : Lexing.lexbuf;
  toplevel : Jaf.declaration list;
  last_good_toplevel : Jaf.declaration list;
  last_good_lexbuf : Lexing.lexbuf;
  mutable last_good_library : Jaf.library option;
  mutable errors : (Lsp.Types.Range.t * string) list;
  mutable fully_resolved : bool;
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

let has_syntax_error doc = not (phys_equal doc.lexbuf doc.last_good_lexbuf)

(* Removes from the context what [doc] has put there. *)
let unregister doc =
  Declarations.unregister doc.ctx doc.last_good_toplevel;
  Option.iter doc.last_good_library ~f:(fun lib ->
      Declarations.unregister_library doc.ctx
        ~import_name:(Option.value_exn doc.import_name)
        lib);
  doc.last_good_library <- None

(* A global declaration replaces the predefined constant of the same name. The
   constant comes back when the declaration is unregistered. *)
let hide_predefined (ctx : Jaf.context) predefined decls =
  List.iter predefined ~f:(fun (v : Jaf.variable) ->
      Hashtbl.add ctx.globals ~key:v.name ~data:v |> ignore);
  let hide (ds : Jaf.vardecls) =
    List.iter ds.vars ~f:(fun g ->
        match Hashtbl.find ctx.globals g.name with
        | Some v when List.exists predefined ~f:(phys_equal v) ->
            Hashtbl.remove ctx.globals g.name
        | _ -> ())
  in
  List.iter decls ~f:(function
    | Jaf.Global ds -> hide ds
    | GlobalGroup gg -> List.iter gg.vardecls ~f:hide
    | _ -> ())

(* An error in a declaration does not stop the registration of the other
   declarations. *)
let parse ctx ~fname ?hll_import_name ?previous ?(predefined = []) text =
  let lexbuf = Lexing.from_string text in
  Lexing.set_filename lexbuf fname;
  let parser =
    if Option.is_none hll_import_name then Parser.jaf else Parser.hll
  in
  match parser Lexer.token lexbuf with
  | toplevel ->
      Option.iter previous ~f:unregister;
      hide_predefined ctx predefined toplevel;
      let errors =
        if Option.is_some hll_import_name then []
        else
          List.filter_map toplevel ~f:(fun decl ->
              try
                Declarations.register ctx [ decl ];
                None
              with e -> Some (make_error lexbuf e))
      in
      {
        ctx;
        path = fname;
        import_name = hll_import_name;
        lexbuf;
        toplevel;
        last_good_toplevel = toplevel;
        last_good_lexbuf = lexbuf;
        last_good_library = None;
        errors;
        fully_resolved = false;
      }
  | exception e ->
      let last_good_toplevel, last_good_lexbuf, last_good_library =
        match previous with
        | Some prev ->
            ( prev.last_good_toplevel,
              prev.last_good_lexbuf,
              prev.last_good_library )
        | None -> ([], Lexing.from_string "", None)
      in
      {
        ctx;
        path = fname;
        import_name = hll_import_name;
        lexbuf;
        toplevel = [];
        last_good_toplevel;
        last_good_lexbuf;
        last_good_library;
        errors = [ make_error lexbuf e ];
        fully_resolved = false;
      }

let resolve ?(decl_only = false) doc =
  if not (has_syntax_error doc) then
    try
      (match doc.import_name with
      | None ->
          Declarations.resolve doc.ctx doc.toplevel;
          if not decl_only then
            doc.errors <-
              doc.errors
              @ (TypeAnalysis.check_types doc.ctx doc.toplevel
                |> List.map ~f:(fun ce ->
                    make_error doc.lexbuf (CompileError.Compile_error ce)))
      | Some import_name ->
          let hll_name = Stdlib.Filename.(chop_extension (basename doc.path)) in
          Declarations.resolve_hll doc.ctx doc.toplevel;
          if Option.is_none doc.last_good_library then
            doc.last_good_library <-
              Some
                (Declarations.register_library doc.ctx doc.toplevel ~hll_name
                   ~import_name));
      if not decl_only then doc.fully_resolved <- true
    with e -> doc.errors <- doc.errors @ [ make_error doc.lexbuf e ]

let create ctx ~fname ?hll_import_name ?(decl_only = false) ?previous
    ?predefined text =
  let doc = parse ctx ~fname ?hll_import_name ?previous ?predefined text in
  resolve ~decl_only doc;
  doc

class ast_locator (doc : t) (pos : Lsp.Types.Position.t) =
  object
    inherit Jaf.ivisitor doc.ctx as super
    val mutable nodes : Jaf.ast_node list = []
    method nodes = nodes

    method! visit_expression expr =
      if range_contains doc.lexbuf.lex_buffer expr.loc pos then (
        nodes <- ASTExpression expr :: nodes;
        super#visit_expression expr)

    method! visit_statement stmt =
      if range_contains doc.lexbuf.lex_buffer stmt.loc pos then (
        nodes <- ASTStatement stmt :: nodes;
        super#visit_statement stmt)

    method! visit_declaration decl =
      let node = Jaf.ASTDeclaration decl in
      if range_contains doc.lexbuf.lex_buffer (Jaf.ast_node_pos node) pos then (
        nodes <- node :: nodes;
        super#visit_declaration decl)

    method! visit_struct_declaration decl =
      let node = Jaf.ASTStructDecl decl in
      if range_contains doc.lexbuf.lex_buffer (Jaf.ast_node_pos node) pos then (
        nodes <- node :: nodes;
        super#visit_struct_declaration decl)

    method! visit_variable var =
      let node = Jaf.ASTVariable var in
      if range_contains doc.lexbuf.lex_buffer (Jaf.ast_node_pos node) pos then (
        nodes <- node :: nodes;
        super#visit_variable var)

    method! visit_type_specifier t =
      let node = Jaf.ASTType t in
      if range_contains doc.lexbuf.lex_buffer (Jaf.ast_node_pos node) pos then (
        nodes <- node :: nodes;
        super#visit_type_specifier t)
  end

(* Returns the most specific node first. *)
let get_nodes_for_pos doc pos =
  let locator = new ast_locator doc pos in
  locator#visit_toplevel doc.toplevel;
  locator#nodes
