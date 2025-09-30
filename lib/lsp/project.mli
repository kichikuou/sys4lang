open Base

type t

val create : unit -> t
val initialize : t -> Types.InitializationOptions.t -> unit
val update_document : t -> Lsp.Uri.t -> string -> Lsp.Types.Diagnostic.t list
val load_document : t -> string -> unit

(* LSP request handlers *)

val get_hover :
  t -> Lsp.Uri.t -> Lsp.Types.Position.t -> Lsp.Types.Hover.t option

val get_definition :
  t -> Lsp.Uri.t -> Lsp.Types.Position.t -> Lsp.Types.Locations.t option

val get_type_definition :
  t -> Lsp.Uri.t -> Lsp.Types.Position.t -> Lsp.Types.Locations.t option
