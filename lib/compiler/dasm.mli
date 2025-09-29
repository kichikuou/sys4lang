type t

val create : Common.Ain.t -> t
val eof : t -> bool
val addr : t -> int
val jump : t -> int -> unit
val next : t -> unit
val peek : t -> Common.Bytecode.opcode option
val opcode : t -> int
val nr_args : t -> int
val arg_type : t -> int -> Common.Bytecode.argtype
val argument_types : t -> Common.Bytecode.argtype list
val arg : t -> int -> int32
val arguments : t -> int32 list
val current_func : t -> int option
