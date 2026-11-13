module Lsp = Linol_lsp.Lsp

type t = {
  ctx : Common.Jaf.context;
  path : string;
  import_name : string option;
  lexbuf : Lexing.lexbuf;
  (* The declarations of the current text. Empty while the text has a syntax
     error. *)
  toplevel : Common.Jaf.declaration list;
  (* The declarations of the last text that had no syntax error, the
     lex_buffer that they were produced from, and the library that the
     declarations of a .hll file make. The context has these declarations and
     this library. Positions in [last_good_toplevel] are meaningful only
     against [last_good_lexbuf]. *)
  last_good_toplevel : Common.Jaf.declaration list;
  last_good_lexbuf : Lexing.lexbuf;
  mutable last_good_library : Common.Jaf.library option;
  mutable errors : (Lsp.Types.Range.t * string) list;
  mutable fully_resolved : bool;
}

(* Parses the text, and registers its declarations in place of the declarations
   of [previous]. If the text has a syntax error, the declarations of
   [previous] stay registered. A global declaration replaces the constant of
   the same name in [predefined]. *)
val parse :
  Common.Jaf.context ->
  fname:string ->
  ?hll_import_name:string ->
  ?previous:t ->
  ?predefined:Common.Jaf.variable list ->
  string ->
  t

(* Resolves the types of the declarations, and registers the library of a .hll
   file. Unless [decl_only] is true, checks the types of function bodies. *)
val resolve : ?decl_only:bool -> t -> unit

val create :
  Common.Jaf.context ->
  fname:string ->
  ?hll_import_name:string ->
  ?decl_only:bool ->
  ?previous:t ->
  ?predefined:Common.Jaf.variable list ->
  string ->
  t

val get_nodes_for_pos : t -> Lsp.Types.Position.t -> Common.Jaf.ast_node list
val to_lsp_range : bytes -> Common.Jaf.location -> Lsp.Types.Range.t
val to_lsp_position : bytes -> Lexing.position -> Lsp.Types.Position.t
