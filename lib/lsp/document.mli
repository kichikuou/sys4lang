module Lsp = Linol_lsp.Lsp

type t = {
  ctx : Common.Jaf.context;
  path : string;
  import_name : string option;
  lexbuf : Lexing.lexbuf;
  toplevel : Common.Jaf.declaration list;
  (* Snapshot of the most recently-parsed declarations along with the
     lex_buffer those declarations were produced from. Positions in
     [last_good_toplevel] are meaningful only against [last_good_lexbuf].
     Carried forward when a subsequent parse fails, so that features like
     completion can still locate enclosing functions. *)
  last_good_toplevel : Common.Jaf.declaration list;
  last_good_lexbuf : Lexing.lexbuf;
  mutable errors : (Lsp.Types.Range.t * string) list;
  mutable fully_resolved : bool;
}

val parse :
  Common.Jaf.context ->
  fname:string ->
  ?hll_import_name:string ->
  ?previous:t ->
  string ->
  t

val resolve : ?decl_only:bool -> t -> unit

val create :
  Common.Jaf.context ->
  fname:string ->
  ?hll_import_name:string ->
  ?decl_only:bool ->
  ?previous:t ->
  string ->
  t

val get_nodes_for_pos : t -> Lsp.Types.Position.t -> Common.Jaf.ast_node list
val to_lsp_range : bytes -> Common.Jaf.location -> Lsp.Types.Range.t
val to_lsp_position : bytes -> Lexing.position -> Lsp.Types.Position.t
