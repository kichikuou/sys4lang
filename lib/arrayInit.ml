(* Copyright (C) 2024 kichikuou <KichikuouChrome@gmail.com>
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

open Base
open Jaf

class visitor ctx =
  object (self)
    inherit ivisitor ctx as _super
    val mutable global_initializer : statement list = []

    method make_array_initializer v =
      let var =
        {
          ty = v.type_spec.ty;
          node = Ident (v.name, GlobalVariable (Option.value_exn v.index));
          loc = dummy_location;
        }
      in
      let lhs =
        {
          ty = Untyped;
          node = Member (var, "Alloc", UnresolvedMember);
          loc = dummy_location;
        }
      in
      let expr = Call (lhs, v.array_dim, BuiltinCall Bytecode.ArrayAlloc) in
      let stmt = Expression { ty = Void; node = expr; loc = dummy_location } in
      { node = stmt; delete_vars = []; loc = dummy_location }

    method! visit_declaration decl =
      match decl with
      | Global ds ->
          List.iter ds.vars ~f:(function
            | { array_dim = _ :: _; is_const = false; _ } as g ->
                global_initializer <-
                  self#make_array_initializer g :: global_initializer
            | _ -> ())
      | _ -> ()

    method generate_initializers () =
      if List.is_empty global_initializer then []
      else
        let global_init =
          Function
            {
              name = "0";
              loc = dummy_location;
              return = { ty = Void; location = dummy_location };
              params = [];
              body = Some (List.rev global_initializer);
              is_label = false;
              index = Some (Ain.add_function ctx.ain "0").index;
              class_name = None;
              class_index = None;
            }
        in
        [ global_init ]
  end
