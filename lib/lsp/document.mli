type t = {
  ctx : Common.Jaf.context;
  path : string;
  import_name : string option;
  lexbuf : Lexing.lexbuf;
  toplevel : Common.Jaf.declaration list;
  mutable errors : (Lsp.Types.Range.t * string) list;
}

val parse :
  Common.Jaf.context -> fname:string -> ?hll_import_name:string -> string -> t

val resolve : ?decl_only:bool -> t -> unit

val create :
  Common.Jaf.context ->
  fname:string ->
  ?hll_import_name:string ->
  ?decl_only:bool ->
  string ->
  t

val get_nodes_for_pos : t -> Lsp.Types.Position.t -> Common.Jaf.ast_node list
val to_lsp_range : bytes -> Common.Jaf.location -> Lsp.Types.Range.t
