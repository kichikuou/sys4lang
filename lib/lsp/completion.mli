module Lsp = Linol_lsp.Lsp

val get_completion :
  Common.Jaf.context ->
  text:bytes ->
  scope:(Common.Jaf.declaration list * bytes) option ->
  Lsp.Types.Position.t ->
  [ `CompletionList of Lsp.Types.CompletionList.t
  | `List of Lsp.Types.CompletionItem.t list ]
  option

val get_signature_help :
  Common.Jaf.context ->
  text:bytes ->
  scope:(Common.Jaf.declaration list * bytes) option ->
  Lsp.Types.Position.t ->
  Lsp.Types.SignatureHelp.t option
