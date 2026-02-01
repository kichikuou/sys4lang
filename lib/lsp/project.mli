open Base

type t

val create : read_file:(string -> string) -> t
val initialize : t -> Types.InitializationOptions.t -> unit
val update_document : t -> path:string -> string -> Lsp.Types.Diagnostic.t list
val load_document : t -> string -> unit
val initial_scan : t -> unit

(* LSP request handlers *)

val get_hover :
  t -> path:string -> Lsp.Types.Position.t -> Lsp.Types.Hover.t option

val get_definition :
  t -> path:string -> Lsp.Types.Position.t -> Lsp.Types.Locations.t option

val get_type_definition :
  t -> path:string -> Lsp.Types.Position.t -> Lsp.Types.Locations.t option

val get_entrypoint : t -> Lsp.Types.Location.t option
