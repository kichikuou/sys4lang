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

open Common
open Base
open Jaf
open CompileError

let initval_of_expression ctx (v : variable) (e : expression) =
  match e.node with
  | ConstInt i | Cast (LongInt, { node = ConstInt i; _ }) ->
      Ain.Variable.Int (Int32.of_int_exn i)
  | ConstFloat f -> Ain.Variable.Float f
  | ConstString s -> Ain.Variable.String s
  | Ident (name, _) -> (
      match Hashtbl.find ctx.globals name with
      | Some g when not g.is_const ->
          Ain.Variable.Int (Int32.of_int_exn (Option.value_exn g.index))
      | _ -> const_error v)
  | _ -> const_error v

let write_initvals ctx decls =
  let write_vardecls (ds : vardecls) =
    List.iter ds.vars ~f:(fun v ->
        match (v.is_const, v.initval) with
        | false, Some e ->
            Ain.set_global_initval_by_index ctx.ain (Option.value_exn v.index)
              (initval_of_expression ctx v e)
        | _ -> ())
  in
  List.iter decls ~f:(function
    | Global ds -> write_vardecls ds
    | GlobalGroup gg -> List.iter gg.vardecls ~f:write_vardecls
    | _ -> ())
