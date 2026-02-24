type t

val version : t -> int
val minor_version : t -> int
val version_gte : t -> int * int -> bool
val version_lt : t -> int * int -> bool

module Type : sig
  type t =
    | Void
    | Int
    | Float
    | String
    | Struct of int
    | IMainSystem
    | FuncType of int
    | Bool
    | LongInt
    | Delegate of int
    | HLLFunc2
    | HLLParam
    | Array of t
    | Ref of t
    | Wrap of t
    | Option of t
    | Unknown87 of t
    | IFace of int
    | Enum2 of int
    | Enum of int
    | HLLFunc
    | Unknown98
    | IFaceWrap of int
    | Function
    | Method
    | NullType

  val to_string : t -> string
  val int_of_data_type : int -> t -> int
  val is_ref : t -> bool
  val is_scalar : t -> bool
end

module Variable : sig
  type initval = Void | Int of int32 | Float of float | String of string

  type t = {
    index : int;
    name : string;
    name2 : string option;
    value_type : Type.t;
    initval : initval option;
  }

  val make : ?index:int -> string -> Type.t -> t
end

module Global : sig
  type t = { variable : Variable.t; group_index : int }
end

module Function : sig
  type t = {
    index : int;
    name : string;
    address : int;
    nr_args : int;
    vars : Variable.t list;
    return_type : Type.t;
    is_label : bool;
    is_lambda : bool;
    crc : int32;
    struct_type : int option;
    enum_type : int option;
  }

  val create : ?index:int -> string -> t
  val set_undefined : t -> t
  val is_defined : t -> bool
  val logical_parameters : t -> Variable.t list
end

module Struct : sig
  type interface = { struct_type : int; vtable_offset : int }

  type t = {
    index : int;
    name : string;
    interfaces : interface list;
    constructor : int;
    destructor : int;
    members : Variable.t list;
    vmethods : int list;
  }
end

module Library : sig
  module Argument : sig
    type t = { name : string; value_type : Type.t }

    val create : string -> Type.t -> t
  end

  module Function : sig
    type t = {
      index : int;
      lib_no : int;
      name : string;
      return_type : Type.t;
      arguments : Argument.t list;
    }

    val create : string -> Type.t -> Argument.t list -> t
  end

  type t = { index : int; name : string; functions : Function.t list }
end

module Switch : sig
  type case_type = IntCase | StringCase

  type t = {
    index : int;
    case_type : case_type;
    mutable default_address : int;
    mutable cases : (int32 * int) list;
  }
end

module FunctionType : sig
  type t = {
    index : int;
    name : string;
    return_type : Type.t;
    nr_arguments : int;
    variables : Variable.t list;
  }

  val logical_parameters : t -> Variable.t list
end

val create :
  ?is_ain2:bool -> ?keyc:int32 -> ?game_version:int -> int -> int -> t

val load : string -> t
val write : ?raw:bool -> t -> Stdio.Out_channel.t -> unit
val write_file : t -> string -> unit
val get_global : t -> string -> Variable.t option
val get_global_by_index : t -> int -> Variable.t
val set_global_type : t -> string -> Type.t -> unit
val set_global_initval : t -> string -> Variable.initval -> unit
val write_new_global : t -> Variable.t -> int
val add_global : t -> string -> int -> int
val add_global_group : t -> string -> int
val get_function : t -> string -> Function.t option
val get_function_by_index : t -> int -> Function.t
val write_function : t -> Function.t -> unit
val write_new_function : t -> Function.t -> int
val add_function : t -> string -> Function.t
val get_struct : t -> string -> Struct.t option
val get_struct_index : t -> string -> int option
val get_struct_by_index : t -> int -> Struct.t
val write_struct : t -> Struct.t -> unit
val write_new_struct : t -> Struct.t -> int
val add_struct : t -> string -> Struct.t
val write_switch : t -> Switch.t -> unit
val add_switch : t -> Switch.case_type -> Switch.t
val get_enum : t -> string -> int option
val get_library_index : t -> string -> int option
val get_library_function_index : t -> int -> string -> int option
val get_library_by_index : t -> int -> Library.t
val write_library : t -> Library.t -> unit
val add_library : t -> string -> Library.t
val function_of_hll_function_index : t -> int -> int -> Function.t
val get_functype : t -> string -> FunctionType.t option
val get_functype_index : t -> string -> int option
val get_functype_by_index : t -> int -> FunctionType.t
val write_functype : t -> FunctionType.t -> unit
val write_new_functype : t -> FunctionType.t -> int
val add_functype : t -> string -> FunctionType.t
val function_of_functype_index : t -> int -> Function.t
val get_delegate : t -> string -> FunctionType.t option
val get_delegate_index : t -> string -> int option
val get_delegate_by_index : t -> int -> FunctionType.t
val write_delegate : t -> FunctionType.t -> unit
val write_new_delegate : t -> FunctionType.t -> int
val add_delegate : t -> string -> FunctionType.t
val function_of_delegate_index : t -> int -> Function.t
val get_string : t -> int -> string option
val add_string : t -> string -> int
val get_string_no : t -> string -> int option
val get_message : t -> int -> string option
val add_message : t -> string -> int
val get_file : t -> int -> string option
val add_file : t -> string -> int
val get_code : t -> bytes
val append_bytecode : t -> CBuffer.t -> unit
val code_size : t -> int
val set_main_function : t -> int -> unit
val set_message_function : t -> int -> unit
val nr_globals : t -> int
val nr_functions : t -> int
val nr_structs : t -> int
val nr_functypes : t -> int
val nr_delegates : t -> int
val nr_libraries : t -> int
val global_iter : ?from:int -> f:(Global.t -> unit) -> t -> unit
val function_iter : ?from:int -> f:(Function.t -> unit) -> t -> unit
val struct_iter : ?from:int -> f:(Struct.t -> unit) -> t -> unit
val functype_iter : ?from:int -> f:(FunctionType.t -> unit) -> t -> unit
val delegate_iter : ?from:int -> f:(FunctionType.t -> unit) -> t -> unit
val library_iter : ?from:int -> f:(Library.t -> unit) -> t -> unit

exception File_error
exception Unrecognized_format
exception Invalid_format
