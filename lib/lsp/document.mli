type t = {
  ctx : Common.Jaf.context;
  text : bytes;
  toplevel : Common.Jaf.declaration list;
  errors : (Lsp.Types.Range.t * string) list;
}

val create :
  Common.Jaf.context ->
  fname:string ->
  ?hll_import_name:string ->
  ?decl_only:bool ->
  string ->
  t

val get_nodes_for_pos : t -> Lsp.Types.Position.t -> Common.Jaf.ast_node list
val to_lsp_range : bytes -> Common.Jaf.location -> Lsp.Types.Range.t
