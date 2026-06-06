(* Copyright (C) 2026 kichikuou <KichikuouChrome@gmail.com>
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, see <http://gnu.org/licenses/>.
 *)

(* A disassembler for the AIN code section, in a resolved form (identifiers and
   jump labels resolved) and a raw form (address-prefixed, unresolved). *)

open Base
open Loc
open Instructions

(* --- safe index lookups into the global Ain tables --- *)

let lookup arr i ~f =
  if i >= 0 && i < Array.length arr then f arr.(i) else Printf.sprintf "#%d" i

(* Append the slot index to a name that is not unique within [arr], so
   duplicate names stay distinguishable.  [count] returns the number of slots
   sharing a name; by default [arr] is scanned on each call. *)
let indexed ?count arr i ~name_of =
  lookup arr i ~f:(fun x ->
      let name = name_of x in
      let n =
        match count with
        | Some count -> count name
        | None -> Array.count arr ~f:(fun x -> String.equal (name_of x) name)
      in
      if n > 1 then Printf.sprintf "%s#%d" name i else name)

(* Functions are numerous, so count name occurrences once rather than scanning
   the whole table on every reference. *)
let func_name_counts =
  lazy
    (let counts = Hashtbl.create (module String) in
     Array.iter Ain.ain.func ~f:(fun (f : Ain.Function.t) ->
         Hashtbl.incr counts f.name);
     counts)

let func_name i =
  indexed Ain.ain.func i
    ~count:(fun name -> Hashtbl.find_exn (Lazy.force func_name_counts) name)
    ~name_of:(fun (f : Ain.Function.t) -> f.name)

let global_name i =
  lookup Ain.ain.glob i ~f:(fun (v : Ain.Variable.t) -> v.name)

let file_name i = lookup Ain.ain.fnam i ~f:Fn.id
let struct_name i = lookup Ain.ain.strt i ~f:(fun (s : Ain.Struct.t) -> s.name)

let delegate_name i =
  lookup Ain.ain.delg i ~f:(fun (d : Ain.FuncType.t) -> d.name)

let enum_name i = lookup Ain.ain.enum i ~f:Fn.id
let syscall_name i = lookup syscalls i ~f:(fun s -> s.name)
let hll_lib_name i = lookup Ain.ain.hll0 i ~f:(fun (h : Ain.HLL.t) -> h.name)

let hll_func_name lib func =
  if lib >= 0 && lib < Array.length Ain.ain.hll0 then
    indexed Ain.ain.hll0.(lib).functions func
      ~name_of:(fun (f : Ain.HLL.function_t) -> f.name)
  else Printf.sprintf "#%d" func

(* --- string literals --- *)

let string_at arr i =
  if i >= 0 && i < Array.length arr then "\"" ^ CodeGen.escape_dq arr.(i) ^ "\""
  else Printf.sprintf "#%d" i

(* In Ain v0, string constants live in the message table. *)
let s_push_table () = if Ain.ain.vers = 0 then Ain.ain.msg else Ain.ain.str0

(* --- type rendering (best-effort, for function headers) --- *)

let rec type_to_string (t : Type.ain_type) =
  let open Type in
  match t with
  | Any -> "any"
  | Void -> "void"
  | Int -> "int"
  | Float -> "float"
  | Char -> "char"
  | String -> "string"
  | Bool -> "bool"
  | LongInt -> "lint"
  | IMainSystem -> "IMainSystem"
  | Struct n | IFace n | StructMember n -> struct_name n
  | Enum n | Enum2 n -> enum_name n
  | Array t -> "array<" ^ type_to_string t ^ ">"
  | Ref t -> "ref " ^ type_to_string t
  | FatRef t -> "fatref " ^ type_to_string t
  | Option t -> "option<" ^ type_to_string t ^ ">"
  (* Function-type/delegate identities are recovered by the decompiler's type
     inference, which the disassembler does not run; the parsed variable type
     also stores no usable index (delegate's is almost always -1).  Fall back to
     generic keywords. *)
  | FuncType _ -> "functype"
  | Delegate _ -> "delegate"
  | HllFunc -> "hll_func"
  | HllFunc2 -> "hll_func2"
  | HllParam -> "hll_param"

(* --- operand formatting --- *)

(* The deriving-show form wraps instructions with operands in a single pair of
   parens, e.g. "(SH_LOCALASSIGN (0, 3l))".  Strip that outermost pair. *)
let unwrap_show s =
  let n = String.length s in
  if n >= 2 && Char.equal s.[0] '(' && Char.equal s.[n - 1] ')' then
    String.sub s ~pos:1 ~len:(n - 2)
  else s

(* Resolve a local variable index against the current function. *)
let local_name (cur : Ain.Function.t option) i =
  match cur with
  | Some f -> indexed f.vars i ~name_of:(fun (v : Ain.Variable.t) -> v.name)
  | None -> Printf.sprintf "#%d" i

(* --- struct-member resolution and validity predicates (for macro folding) --- *)

(* Struct-member indices resolve against the function's owning struct, which we
   recover from the "Struct@method" function name. *)
let struct_of (f : Ain.Function.t option) =
  match f with
  | None -> None
  | Some f -> (
      match (Ain.Function.parse_name f).struct_name with
      | Some name -> Hashtbl.find Ain.ain.struct_by_name name
      | None -> None)

(* Render "<struct> <member>". *)
let struct_and_member (cs : Ain.Struct.t option) i =
  match cs with
  | Some s when i >= 0 && i < Array.length s.members ->
      Printf.sprintf "%s %s" s.name s.members.(i).name
  | _ -> Printf.sprintf "#? #%d" i

let is_local (cur : Ain.Function.t option) n =
  match cur with Some f -> n >= 0 && n < Array.length f.vars | None -> false

let is_global n = n >= 0 && n < Array.length Ain.ain.glob
let is_struct_type n = n >= 0 && n < Array.length Ain.ain.strt

let is_member (cs : Ain.Struct.t option) n =
  match cs with Some s -> n >= 0 && n < Array.length s.members | None -> false

let is_vtable (cs : Ain.Struct.t option) n =
  match cs with
  | Some s when n >= 0 && n < Array.length s.members ->
      String.equal s.members.(n).name "<vtable>"
  | _ -> false

(* Resolved-mode rendering of a single instruction.  Operands of common
   opcodes are resolved to names/strings/addresses; instructions not listed
   here are printed in the deriving-show form. *)
let format_resolved cur cur_struct insn =
  let addr a = Printf.sprintf "0x%x" a in
  let loc = local_name cur in
  let glob = global_name in
  let mem = struct_and_member cur_struct in
  let str n = string_at Ain.ain.str0 n in
  match insn with
  | PUSH n -> Printf.sprintf "PUSH %ld" n
  | F_PUSH f -> Printf.sprintf "F_PUSH %s" (CodeGen.format_float f)
  | JUMP a -> Printf.sprintf "JUMP %s" (addr a)
  | IFZ a -> Printf.sprintf "IFZ %s" (addr a)
  | IFNZ a -> Printf.sprintf "IFNZ %s" (addr a)
  | CALLFUNC i -> Printf.sprintf "CALLFUNC %s" (func_name i)
  | CALLMETHOD i ->
      if Ain.ain.vers >= 11 then Printf.sprintf "CALLMETHOD %d" i
      else Printf.sprintf "CALLMETHOD %s" (func_name i)
  | CALLSYS i -> Printf.sprintf "CALLSYS %s" (syscall_name i)
  | CALLHLL (lib, func, t) ->
      let s =
        Printf.sprintf "CALLHLL %s %s" (hll_lib_name lib)
          (hll_func_name lib func)
      in
      (* The type operand is only present for vers > 8 (the condition under which
         decode reads it); [Any] is the untyped default and carries no info. *)
      if Ain.ain.vers > 8 then
        match t with Type.Any -> s | _ -> s ^ " " ^ type_to_string t
      else s
  | S_PUSH n -> Printf.sprintf "S_PUSH %s" (string_at (s_push_table ()) n)
  | MSG n -> Printf.sprintf "MSG %s" (string_at Ain.ain.msg n)
  | SH_GLOBALREF n -> Printf.sprintf "SH_GLOBALREF %s" (glob n)
  | SH_LOCALREF n -> Printf.sprintf "SH_LOCALREF %s" (loc n)
  | SH_LOCALREFREF n -> Printf.sprintf "SH_LOCALREFREF %s" (loc n)
  | SH_LOCALINC n -> Printf.sprintf "SH_LOCALINC %s" (loc n)
  | SH_LOCALDEC n -> Printf.sprintf "SH_LOCALDEC %s" (loc n)
  | SH_LOCALDELETE n -> Printf.sprintf "SH_LOCALDELETE %s" (loc n)
  | SH_LOCALCREATE (n, s) ->
      Printf.sprintf "SH_LOCALCREATE %s %s" (loc n) (struct_name s)
  | SH_LOCALASSIGN (n, v) -> Printf.sprintf "SH_LOCALASSIGN %s %ld" (loc n) v
  | FUNC i -> Printf.sprintf "FUNC %d" i
  | ENDFUNC i -> Printf.sprintf "ENDFUNC %s" (func_name i)
  | EOF i -> Printf.sprintf "EOF %s" (file_name i)
  | NEW (s, f) -> Printf.sprintf "NEW %s %s" (struct_name s) (func_name f)
  | SWITCH n -> Printf.sprintf "SWITCH %d" n
  | STRSWITCH n -> Printf.sprintf "STRSWITCH %d" n
  | DG_CALL (dg, a) ->
      Printf.sprintf "DG_CALL %s %s" (delegate_name dg) (addr a)
  | DG_CALLBEGIN dg -> Printf.sprintf "DG_CALLBEGIN %s" (delegate_name dg)
  | DG_STR_TO_METHOD dg ->
      Printf.sprintf "DG_STR_TO_METHOD %s" (delegate_name dg)
  | OBJSWAP t -> Printf.sprintf "OBJSWAP %d" t
  | S_MOD t -> Printf.sprintf "S_MOD %d" t
  | X_ICAST s -> Printf.sprintf "X_ICAST %s" (struct_name s)
  (* --- fused SH_* super-instructions, operands resolved to names --- *)
  (* struct-member operands *)
  | SH_STRUCTREF m -> Printf.sprintf "SH_STRUCTREF %s" (mem m)
  | SH_STRUCT_S_REF m -> Printf.sprintf "SH_STRUCT_S_REF %s" (mem m)
  | SH_STRUCTSREF_EMPTY m -> Printf.sprintf "SH_STRUCTSREF_EMPTY %s" (mem m)
  | SH_SASSIGN_STRUCTSREF m -> Printf.sprintf "SH_SASSIGN_STRUCTSREF %s" (mem m)
  | SH_MEM_ASSIGN_IMM (m, v) ->
      Printf.sprintf "SH_MEM_ASSIGN_IMM %s %ld" (mem m) v
  | SH_MEM_ASSIGN_LOCAL (m, l) ->
      Printf.sprintf "SH_MEM_ASSIGN_LOCAL %s %s" (mem m) (loc l)
  | SH_STRUCTREF_GT_IMM (m, v) ->
      Printf.sprintf "SH_STRUCTREF_GT_IMM %s %ld" (mem m) v
  | SH_STRUCT_ASSIGN_LOCALREF_ITOB (m, l) ->
      Printf.sprintf "SH_STRUCT_ASSIGN_LOCALREF_ITOB %s %s" (mem m) (loc l)
  | SH_LOCAL_ASSIGN_STRUCTREF (l, m) ->
      Printf.sprintf "SH_LOCAL_ASSIGN_STRUCTREF %s %s" (loc l) (mem m)
  | SH_LOCREF_ASSIGN_MEM (l, m) ->
      Printf.sprintf "SH_LOCREF_ASSIGN_MEM %s %s" (loc l) (mem m)
  | SH_STRUCTREF_CALLMETHOD_NO_PARAM (m, f) ->
      Printf.sprintf "SH_STRUCTREF_CALLMETHOD_NO_PARAM %s %s" (mem m)
        (func_name f)
  | SH_STRUCTREF2 (m, s) -> Printf.sprintf "SH_STRUCTREF2 %s %ld" (mem m) s
  | SH_STRUCTREF3 (m, s1, s2) ->
      Printf.sprintf "SH_STRUCTREF3 %s %ld %ld" (mem m) s1 s2
  | SH_STRUCTREF2_CALLMETHOD_NO_PARAM (m, s, f) ->
      Printf.sprintf "SH_STRUCTREF2_CALLMETHOD_NO_PARAM %s %ld %s" (mem m) s
        (func_name f)
  | SH_STRUCT_A_PUSHBACK_LOCAL_STRUCT (m, l) ->
      Printf.sprintf "SH_STRUCT_A_PUSHBACK_LOCAL_STRUCT %s %s" (mem m) (loc l)
  | SH_STRUCTSREF_EQ_LOCALSREF (m, l) ->
      Printf.sprintf "SH_STRUCTSREF_EQ_LOCALSREF %s %s" (mem m) (loc l)
  | SH_STRUCTSREF_NE_LOCALSREF (m, l) ->
      Printf.sprintf "SH_STRUCTSREF_NE_LOCALSREF %s %s" (mem m) (loc l)
  | SH_STRUCT_SR_REF (m, s) ->
      Printf.sprintf "SH_STRUCT_SR_REF %s %s" (mem m) (struct_name s)
  | SH_REF_LOCAL_ASSIGN_STRUCTREF2 (m, l, s) ->
      Printf.sprintf "SH_REF_LOCAL_ASSIGN_STRUCTREF2 %s %s %ld" (mem m) (loc l)
        s
  | SH_STRUCTREF_SASSIGN_LOCALSREF (m, l) ->
      Printf.sprintf "SH_STRUCTREF_SASSIGN_LOCALSREF %s %s" (mem m) (loc l)
  | SH_STRUCT_APUSHBACK_LOCALSREF (m, l) ->
      Printf.sprintf "SH_STRUCT_APUSHBACK_LOCALSREF %s %s" (mem m) (loc l)
  | SH_STRUCTSREF_NE_STR0 (m, s) ->
      Printf.sprintf "SH_STRUCTSREF_NE_STR0 %s %s" (mem m) (str s)
  | SH_IF_STRUCTREF_NE_LOCALREF (m, l, a) ->
      Printf.sprintf "SH_IF_STRUCTREF_NE_LOCALREF %s %s %s" (mem m) (loc l)
        (addr a)
  | SH_IF_STRUCTREF_GT_IMM (m, v, a) ->
      Printf.sprintf "SH_IF_STRUCTREF_GT_IMM %s %ld %s" (mem m) v (addr a)
  | SH_IF_STRUCTREF_Z (m, a) ->
      Printf.sprintf "SH_IF_STRUCTREF_Z %s %s" (mem m) (addr a)
  | SH_IF_STRUCT_A_NOT_EMPTY (m, a) ->
      Printf.sprintf "SH_IF_STRUCT_A_NOT_EMPTY %s %s" (mem m) (addr a)
  | SH_IF_STRUCTREF_NE_IMM (m, v, a) ->
      Printf.sprintf "SH_IF_STRUCTREF_NE_IMM %s %ld %s" (mem m) v (addr a)
  | SH_IF_STRUCTREF_EQ_IMM (m, v, a) ->
      Printf.sprintf "SH_IF_STRUCTREF_EQ_IMM %s %ld %s" (mem m) v (addr a)
  (* local operands *)
  | SH_LOCAL_S_REF l -> Printf.sprintf "SH_LOCAL_S_REF %s" (loc l)
  | SH_LOCALSREF_EMPTY l -> Printf.sprintf "SH_LOCALSREF_EMPTY %s" (loc l)
  | SH_SASSIGN_LOCALSREF l -> Printf.sprintf "SH_SASSIGN_LOCALSREF %s" (loc l)
  | SH_LOCALASSIGN_SUB_IMM (l, v) ->
      Printf.sprintf "SH_LOCALASSIGN_SUB_IMM %s %ld" (loc l) v
  | SH_IF_LOC_LT_IMM (l, v, a) ->
      Printf.sprintf "SH_IF_LOC_LT_IMM %s %ld %s" (loc l) v (addr a)
  | SH_IF_LOC_GE_IMM (l, v, a) ->
      Printf.sprintf "SH_IF_LOC_GE_IMM %s %ld %s" (loc l) v (addr a)
  | SH_IF_LOC_GT_IMM (l, v, a) ->
      Printf.sprintf "SH_IF_LOC_GT_IMM %s %ld %s" (loc l) v (addr a)
  | SH_IF_LOC_NE_IMM (l, v, a) ->
      Printf.sprintf "SH_IF_LOC_NE_IMM %s %ld %s" (loc l) v (addr a)
  | SH_LOC_LT_IMM_OR_LOC_GE_IMM (l, v1, v2) ->
      Printf.sprintf "SH_LOC_LT_IMM_OR_LOC_GE_IMM %s %ld %ld" (loc l) v1 v2
  | SH_LOCALSTRUCT_ASSIGN_IMM (l, s, v) ->
      Printf.sprintf "SH_LOCALSTRUCT_ASSIGN_IMM %s %ld %ld" (loc l) s v
  | SH_LOCAL_A_PUSHBACK_LOCAL_STRUCT (a, s) ->
      Printf.sprintf "SH_LOCAL_A_PUSHBACK_LOCAL_STRUCT %s %s" (loc a) (loc s)
  | SH_LOCALSREF_EQ_STR0 (l, s) ->
      Printf.sprintf "SH_LOCALSREF_EQ_STR0 %s %s" (loc l) (str s)
  | SH_LOCALSREF_NE_STR0 (l, s) ->
      Printf.sprintf "SH_LOCALSREF_NE_STR0 %s %s" (loc l) (str s)
  | SH_LOCALREF_SASSIGN_LOCALSREF (a, b) ->
      Printf.sprintf "SH_LOCALREF_SASSIGN_LOCALSREF %s %s" (loc a) (loc b)
  | SH_LOCAL_APUSHBACK_LOCALSREF (a, b) ->
      Printf.sprintf "SH_LOCAL_APUSHBACK_LOCALSREF %s %s" (loc a) (loc b)
  (* global operands *)
  | SH_GLOBAL_S_REF g -> Printf.sprintf "SH_GLOBAL_S_REF %s" (glob g)
  | SH_GLOBALSREF_EMPTY g -> Printf.sprintf "SH_GLOBALSREF_EMPTY %s" (glob g)
  | SH_SASSIGN_GLOBALSREF g ->
      Printf.sprintf "SH_SASSIGN_GLOBALSREF %s" (glob g)
  | SH_GLOBAL_ASSIGN_LOCAL (g, l) ->
      Printf.sprintf "SH_GLOBAL_ASSIGN_LOCAL %s %s" (glob g) (loc l)
  | SH_GLOBAL_ASSIGN_IMM (g, v) ->
      Printf.sprintf "SH_GLOBAL_ASSIGN_IMM %s %ld" (glob g) v
  | SH_GLOBAL_A_PUSHBACK_LOCAL_STRUCT (g, l) ->
      Printf.sprintf "SH_GLOBAL_A_PUSHBACK_LOCAL_STRUCT %s %s" (glob g) (loc l)
  | SH_GLOBAL_APUSHBACK_LOCALSREF (g, l) ->
      Printf.sprintf "SH_GLOBAL_APUSHBACK_LOCALSREF %s %s" (glob g) (loc l)
  | SH_GLOBALSREF_NE_STR0 (g, s) ->
      Printf.sprintf "SH_GLOBALSREF_NE_STR0 %s %s" (glob g) (str s)
  (* str0 operands *)
  | SH_S_ASSIGN_STR0 s -> Printf.sprintf "SH_S_ASSIGN_STR0 %s" (str s)
  | SH_IF_SREF_NE_STR0 (s, a) ->
      Printf.sprintf "SH_IF_SREF_NE_STR0 %s %s" (str s) (addr a)
  | insn -> unwrap_show (show_instruction insn)

(* --- macro folding (peephole ".XXX" pseudo-ops) --- *)

(* Fold an instruction sequence starting with a page-push instruction into a
   single ".XXX" pseudo-op.  Returns the rendered line and the number of
   instructions consumed.  Arms are ordered longest-first so that a longer
   macro takes precedence over a shorter one sharing its prefix.  The X_REF /
   X_ASSIGN / X_DUP / X_MOV macros of alice-tools are not supported.  The
   caller rejects a fold if a jump target points into the middle of the
   sequence. *)
let try_fold cur cur_struct code =
  let to_int = Int32.to_int_exn in
  let loc = local_name cur in
  let glob = global_name in
  let mem = struct_and_member cur_struct in
  (* Only the head of [code] can match; the longest macro is 11 instructions. *)
  match List.take code 12 |> List.map ~f:(fun l -> l.txt) with
  (* local page *)
  | PUSHLOCALPAGE
    :: PUSH n
    :: REF :: DELETE :: PUSHLOCALPAGE :: SWAP
    :: PUSH m
    :: SWAP :: ASSIGN :: _
    when is_local cur (to_int n) && Int32.equal n m ->
      Some (Printf.sprintf ".STACK_LOCALASSIGN %s" (loc (to_int n)), 9)
  | PUSHLOCALPAGE
    :: PUSH n
    :: DUP2 :: REF :: DELETE :: DUP2
    :: NEW (s, f)
    :: ASSIGN :: POP :: POP :: POP :: _
    when is_local cur (to_int n) && is_struct_type s && f = -1 ->
      Some
        ( Printf.sprintf ".LOCALCREATE %s %s" (loc (to_int n)) (struct_name s),
          11 )
  | PUSHLOCALPAGE
    :: PUSH n
    :: DUP2 :: REF :: DELETE
    :: PUSH m
    :: ASSIGN :: POP :: _
    when is_local cur (to_int n) && Int32.equal m (-1l) ->
      Some (Printf.sprintf ".LOCALDELETE %s" (loc (to_int n)), 8)
  | PUSHLOCALPAGE :: PUSH n :: DUP2 :: REF :: DUP_X2 :: POP :: INC :: POP :: _
    when is_local cur (to_int n) ->
      Some (Printf.sprintf ".LOCALINC2 %s" (loc (to_int n)), 8)
  | PUSHLOCALPAGE :: PUSH n :: DUP2 :: REF :: DUP_X2 :: POP :: DEC :: POP :: _
    when is_local cur (to_int n) ->
      Some (Printf.sprintf ".LOCALDEC2 %s" (loc (to_int n)), 8)
  | PUSHLOCALPAGE :: PUSH n :: REF :: S_PUSH s :: S_ASSIGN :: DELETE :: _
    when is_local cur (to_int n) ->
      Some
        ( Printf.sprintf ".S_LOCALASSIGN %s %s"
            (loc (to_int n))
            (string_at (s_push_table ()) s),
          6 )
  | PUSHLOCALPAGE :: PUSH n :: F_PUSH f :: F_ASSIGN :: POP :: _
    when is_local cur (to_int n) ->
      Some
        ( Printf.sprintf ".F_LOCALASSIGN %s %s"
            (loc (to_int n))
            (CodeGen.format_float f),
          5 )
  | PUSHLOCALPAGE :: PUSH n :: PUSH v :: ASSIGN :: POP :: _
    when is_local cur (to_int n) ->
      Some (Printf.sprintf ".LOCALASSIGN %s %ld" (loc (to_int n)) v, 5)
  | PUSHLOCALPAGE :: PUSH n :: PUSH v :: PLUSA :: POP :: _
    when is_local cur (to_int n) ->
      Some (Printf.sprintf ".LOCALPLUSA %s %ld" (loc (to_int n)) v, 5)
  | PUSHLOCALPAGE :: PUSH n :: PUSH v :: MINUSA :: POP :: _
    when is_local cur (to_int n) ->
      Some (Printf.sprintf ".LOCALMINUSA %s %ld" (loc (to_int n)) v, 5)
  | PUSHLOCALPAGE :: SWAP :: PUSH n :: SWAP :: ASSIGN :: _
    when is_local cur (to_int n) ->
      Some (Printf.sprintf ".LOCALASSIGN2 %s" (loc (to_int n)), 5)
  | PUSHLOCALPAGE :: PUSH n :: REFREF :: _ when is_local cur (to_int n) ->
      Some (Printf.sprintf ".LOCALREFREF %s" (loc (to_int n)), 3)
  | PUSHLOCALPAGE :: PUSH n :: INC :: _ when is_local cur (to_int n) ->
      Some (Printf.sprintf ".LOCALINC %s" (loc (to_int n)), 3)
  | PUSHLOCALPAGE :: PUSH n :: DEC :: _ when is_local cur (to_int n) ->
      Some (Printf.sprintf ".LOCALDEC %s" (loc (to_int n)), 3)
  | PUSHLOCALPAGE :: PUSH n :: REF :: _ when is_local cur (to_int n) ->
      Some (Printf.sprintf ".LOCALREF %s" (loc (to_int n)), 3)
  (* global page *)
  | PUSHGLOBALPAGE :: PUSH n :: PUSH v :: ASSIGN :: POP :: _
    when is_global (to_int n) ->
      Some (Printf.sprintf ".GLOBALASSIGN %s %ld" (glob (to_int n)) v, 5)
  | PUSHGLOBALPAGE :: PUSH n :: F_PUSH f :: F_ASSIGN :: POP :: _
    when is_global (to_int n) ->
      Some
        ( Printf.sprintf ".F_GLOBALASSIGN %s %s"
            (glob (to_int n))
            (CodeGen.format_float f),
          5 )
  | PUSHGLOBALPAGE :: PUSH n :: REFREF :: _ when is_global (to_int n) ->
      Some (Printf.sprintf ".GLOBALREFREF %s" (glob (to_int n)), 3)
  | PUSHGLOBALPAGE :: PUSH n :: INC :: _ when is_global (to_int n) ->
      Some (Printf.sprintf ".GLOBALINC %s" (glob (to_int n)), 3)
  | PUSHGLOBALPAGE :: PUSH n :: DEC :: _ when is_global (to_int n) ->
      Some (Printf.sprintf ".GLOBALDEC %s" (glob (to_int n)), 3)
  | PUSHGLOBALPAGE :: PUSH n :: REF :: _ when is_global (to_int n) ->
      Some (Printf.sprintf ".GLOBALREF %s" (glob (to_int n)), 3)
  (* struct page *)
  | PUSHSTRUCTPAGE
    :: PUSH a0
    :: DUP_U2
    :: PUSH a1
    :: REF :: SWAP
    :: PUSH a2
    :: ADD :: REF :: _
    when to_int a0 >= 0 && is_vtable cur_struct (to_int a1) && to_int a2 >= 0 ->
      Some (Printf.sprintf ".PUSHVMETHOD %ld %ld" a0 a2, 9)
  | PUSHSTRUCTPAGE :: PUSH n :: PUSH v :: ASSIGN :: POP :: _
    when is_member cur_struct (to_int n) ->
      Some (Printf.sprintf ".STRUCTASSIGN %s %ld" (mem (to_int n)) v, 5)
  | PUSHSTRUCTPAGE :: PUSH n :: F_PUSH f :: F_ASSIGN :: POP :: _
    when is_member cur_struct (to_int n) ->
      Some
        ( Printf.sprintf ".F_STRUCTASSIGN %s %s"
            (mem (to_int n))
            (CodeGen.format_float f),
          5 )
  | PUSHSTRUCTPAGE :: PUSH n :: REFREF :: _ when is_member cur_struct (to_int n)
    ->
      Some (Printf.sprintf ".STRUCTREFREF %s" (mem (to_int n)), 3)
  | PUSHSTRUCTPAGE :: PUSH n :: INC :: _ when is_member cur_struct (to_int n) ->
      Some (Printf.sprintf ".STRUCTINC %s" (mem (to_int n)), 3)
  | PUSHSTRUCTPAGE :: PUSH n :: DEC :: _ when is_member cur_struct (to_int n) ->
      Some (Printf.sprintf ".STRUCTDEC %s" (mem (to_int n)), 3)
  | PUSHSTRUCTPAGE :: PUSH n :: REF :: _ when is_member cur_struct (to_int n) ->
      Some (Printf.sprintf ".STRUCTREF %s" (mem (to_int n)), 3)
  | _ -> None

(* --- jump-target label collection --- *)

let targets_of = function
  | JUMP a | IFZ a | IFNZ a -> [ a ]
  | SH_IF_LOC_LT_IMM (_, _, a)
  | SH_IF_LOC_GE_IMM (_, _, a)
  | SH_IF_LOC_GT_IMM (_, _, a)
  | SH_IF_LOC_NE_IMM (_, _, a)
  | SH_IF_STRUCTREF_NE_IMM (_, _, a)
  | SH_IF_STRUCTREF_GT_IMM (_, _, a)
  | SH_IF_STRUCTREF_EQ_IMM (_, _, a)
  | SH_IF_STRUCTREF_NE_LOCALREF (_, _, a) ->
      [ a ]
  | SH_IF_STRUCTREF_Z (_, a)
  | SH_IF_STRUCT_A_NOT_EMPTY (_, a)
  | SH_IF_SREF_NE_STR0 (_, a) ->
      [ a ]
  | DG_CALL (_, a) -> [ a ]
  | _ -> []

let collect_labels code =
  List.fold code
    ~init:(Set.empty (module Int))
    ~f:(fun acc { txt; _ } ->
      List.fold (targets_of txt) ~init:acc ~f:(fun acc a ->
          if a >= 0 then Set.add acc a else acc))

(* --- switch case/default markers --- *)

(* A switch dispatches to case targets via its table (referenced by the SWITCH
   [id] operand), not via ordinary jumps, so a bare address label at the target
   carries no hint of which case it is.  Instead, mark each target address with a
   ".CASE id value" / ".STRCASE id \"str\"" / ".DEFAULT id" directive tying it
   back to its SWITCH.  Only switches referenced by [code] are included, keeping
   single-function disassembly scoped to that function.  [resolve] turns a string
   case's str0 index into the literal (off in raw mode). *)
let collect_switch_labels ~resolve code =
  let tbl = Hashtbl.create (module Int) in
  let add addr line = Hashtbl.add_multi tbl ~key:addr ~data:line in
  let add_switch id =
    if id >= 0 && id < Array.length Ain.ain.swi0 then begin
      let sw = Ain.ain.swi0.(id) in
      let is_str =
        match sw.case_type with Ain.Switch.String -> true | Int -> false
      in
      Array.iter sw.cases ~f:(fun c ->
          let line =
            if is_str then
              let v = Int32.to_int_exn c.value in
              if resolve then
                Printf.sprintf ".STRCASE %d %s" id (string_at Ain.ain.str0 v)
              else Printf.sprintf ".STRCASE %d %d" id v
            else Printf.sprintf ".CASE %d %ld" id c.value
          in
          add (Int32.to_int_exn c.address) line);
      add
        (Int32.to_int_exn sw.default_address)
        (Printf.sprintf ".DEFAULT %d" id)
    end
  in
  List.fold code
    ~init:(Set.empty (module Int))
    ~f:(fun acc { txt; _ } ->
      match txt with SWITCH n | STRSWITCH n -> Set.add acc n | _ -> acc)
  |> Set.iter ~f:add_switch;
  tbl

(* --- function headers --- *)

let print_function_header (f : Ain.Function.t) =
  Stdio.printf "\n; %s\n" f.name;
  Array.iteri f.vars ~f:(fun i (v : Ain.Variable.t) ->
      let kind = if i < f.nr_args then "ARG" else "VAR" in
      Stdio.printf "; %s %2d: %s : %s\n" kind i v.name (type_to_string v.type_));
  Stdio.printf "; RETURN: %s\n" (type_to_string f.return_type)

(* --- function selection --- *)

let func_by_id i =
  if i >= 0 && i < Array.length Ain.ain.func then Some Ain.ain.func.(i)
  else None

(* Extract the [FUNC..ENDFUNC] slice for a named function.  Accepts the
   "name#id" form emitted for names shared by several functions; a bare name
   selects the last function with that name. *)
let select_function code name =
  let by_name name =
    Array.foldi Ain.ain.func ~init:None ~f:(fun i acc f ->
        if String.equal f.name name then Some i else acc)
  in
  let id =
    match String.rsplit2 name ~on:'#' with
    | Some (base, idx) -> (
        match Int.of_string_opt idx with
        | Some id
          when Option.exists (func_by_id id) ~f:(fun f ->
                   String.equal f.name base) ->
            Some id
        | _ -> by_name name)
    | None -> by_name name
  in
  let is_lambda n =
    match func_by_id n with
    | Some f -> phys_equal f.kind Ain.Function.Lambda
    | None -> false
  in
  match id with
  | None -> failwith ("cannot find function " ^ name)
  | Some id -> (
      let rec drop = function
        | { txt = FUNC n; _ } :: _ as code when n = id -> code
        | _ :: tl -> drop tl
        | [] -> failwith ("cannot find function " ^ name)
      in
      (* Collect from the target's FUNC up to its matching ENDFUNC, keeping inline
         lambdas (each closed by its own ENDFUNC) as part of the body via a depth
         counter.  A missing ENDFUNC (e.g. constructors) ends the function at the
         next top-level FUNC/EOF.  Mirrors CodeSection.parse_function's rules. *)
      let rec take acc depth = function
        | ({ txt = ENDFUNC _; _ } as hd) :: tl ->
            if depth = 0 then List.rev (hd :: acc)
            else take (hd :: acc) (depth - 1) tl
        | ({ txt = FUNC n; _ } as hd) :: tl when is_lambda n ->
            take (hd :: acc) (depth + 1) tl
        | { txt = FUNC _ | EOF _; _ } :: _ -> List.rev acc
        | hd :: tl -> take (hd :: acc) depth tl
        | [] -> List.rev acc
      in
      match drop code with
      | header :: rest -> header :: take [] 0 rest
      | [] -> failwith ("cannot find function " ^ name))

(* --- entry point --- *)

let disassemble ~raw ?func () =
  let code =
    Instructions.decode Ain.ain.code |> CodeSection.preprocess_ain_v0
  in
  let code =
    match func with None -> code | Some name -> select_function code name
  in
  let switch_labels = collect_switch_labels ~resolve:(not raw) code in
  let print_switch_markers addr =
    match Hashtbl.find switch_labels addr with
    | Some lines -> List.iter (List.rev lines) ~f:(Stdio.printf "%s\n")
    | None -> ()
  in
  if raw then
    List.iter code ~f:(fun { addr; txt; _ } ->
        (match txt with
        | FUNC id -> Option.iter (func_by_id id) ~f:print_function_header
        | _ -> ());
        print_switch_markers addr;
        Stdio.printf "0x%08x:\t%s\n" addr (unwrap_show (show_instruction txt)))
  else begin
    let labels = collect_labels code in
    (* A fold is allowed only if no jump target or switch case marker points
       at its interior (non-head) instructions. *)
    let is_anchor addr =
      Set.mem labels addr || Hashtbl.mem switch_labels addr
    in
    let interior_clear code k =
      let rec go i = function
        | [] -> true
        | { addr; _ } :: tl ->
            if i >= k then true
            else if i >= 1 && is_anchor addr then false
            else go (i + 1) tl
      in
      go 0 code
    in
    (* Functions can nest (a lambda body appears inside its enclosing function),
       so track a stack of frames: FUNC pushes, ENDFUNC pops back to the parent.
       Code between a nested ENDFUNC and the next FUNC continues the parent, so
       its local/member references must resolve against the parent frame. *)
    let rec emit stack = function
      | [] -> ()
      | { addr; txt; _ } :: tl as code -> (
          let stack =
            match txt with
            | FUNC id ->
                let f = func_by_id id in
                Option.iter f ~f:print_function_header;
                (f, struct_of f) :: stack
            | ENDFUNC _ -> ( match stack with _ :: rest -> rest | [] -> [])
            | _ -> stack
          in
          let cur, cur_struct =
            match stack with frame :: _ -> frame | [] -> (None, None)
          in
          print_switch_markers addr;
          if Set.mem labels addr then Stdio.printf "0x%x:\n" addr;
          let folded =
            match txt with
            | PUSHLOCALPAGE | PUSHGLOBALPAGE | PUSHSTRUCTPAGE ->
                try_fold cur cur_struct code
            | _ -> None
          in
          match folded with
          | Some (line, k) when interior_clear code k ->
              Stdio.printf "\t%s\n" line;
              emit stack (List.drop code k)
          | _ ->
              (match txt with
              | FUNC _ | ENDFUNC _ | EOF _ ->
                  Stdio.printf "%s\n" (format_resolved cur cur_struct txt)
              | _ -> Stdio.printf "\t%s\n" (format_resolved cur cur_struct txt));
              emit stack tl)
    in
    emit [] code
  end
