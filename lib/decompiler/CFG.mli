open BasicBlock

type node
type t

val of_list : fragment basic_block list -> t
val to_list : t -> fragment basic_block list
val value : node option -> fragment basic_block option
val value_exn : node option -> fragment basic_block
val next : node option -> node option
val prev : node option -> node option
val first : t -> node option
val last : t -> node option
val is_end : 'a option -> bool
val node_equal : node option -> node option -> bool
val insert_before : t -> node option -> fragment basic_block -> node option
val insert_last : t -> fragment basic_block -> node option
val remove : t -> node option -> unit
val set : node option -> fragment basic_block -> unit

val iterate :
  t -> node option -> node option -> (fragment basic_block -> unit) -> unit

val find :
  t ->
  node option ->
  next:(node option -> node option) ->
  f:(fragment basic_block -> bool) ->
  node option

val find_forward :
  t -> node option -> f:(fragment basic_block -> bool) -> node option

val find_backward :
  t -> node option -> f:(fragment basic_block -> bool) -> node option

val by_address : int -> 'a basic_block -> bool
val by_jump_target : int -> (terminator Loc.loc * 'a) basic_block -> bool
val splice : t -> node option -> node option -> t
