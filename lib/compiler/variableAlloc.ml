(* Copyright (C) 2021 Nunuhara Cabbage <nunuhara@haniwa.technology>
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

type scope_kind = ScopeAnon | ScopeLoop | ScopeSwitch
type var_set = (int, Int.comparator_witness) Set.t

type scope = {
  (* variables allocated before entering the scope *)
  initial_vars : var_set;
  (* list of unresolved break statements *)
  mutable breaks : (statement * var_set) list;
  (* list of unresolved continue statements *)
  mutable continues : (statement * var_set) list;
}

type label_data = {
  (* list of variables allocated at the label *)
  mutable live_vars : var_set option;
  (* list of goto statements to the label *)
  mutable gotos : (statement * var_set) list;
}

let dummy_var_seqno = ref 0

class variable_alloc_visitor ctx =
  object (self)
    inherit ivisitor ctx as super
    val mutable vars : variable list = []
    val scopes = Stack.create ()
    val labels = Hashtbl.create (module String)

    method start_scope =
      Stack.push scopes
        { initial_vars = self#current_var_set; breaks = []; continues = [] }

    method end_scope kind =
      let scope = Stack.pop_exn scopes in
      let update_break_continue (stmt, vars) =
        stmt.delete_vars <- Set.elements (Set.diff vars scope.initial_vars)
      in
      (* function to transfer breaks to parent scope *)
      let carry_breaks () =
        match Stack.top scopes with
        | None -> (
            match scope.breaks with
            | [] -> ()
            | (stmt, _) :: _ ->
                compile_error "Unresolved break statement" (ASTStatement stmt))
        | Some parent -> parent.breaks <- List.append parent.breaks scope.breaks
      in
      (* function to transfer continues to parent scope *)
      let carry_continues () =
        match Stack.top scopes with
        | None -> (
            match scope.continues with
            | [] -> ()
            | (stmt, _) :: _ ->
                compile_error "Unresolved continue statement"
                  (ASTStatement stmt))
        | Some parent ->
            parent.continues <- List.append parent.continues scope.continues
      in
      match kind with
      | ScopeLoop ->
          List.iter scope.breaks ~f:update_break_continue;
          List.iter scope.continues ~f:update_break_continue
      | ScopeSwitch ->
          List.iter scope.breaks ~f:update_break_continue;
          carry_continues ()
      | ScopeAnon ->
          carry_breaks ();
          carry_continues ()

    method resolve_gotos =
      Hashtbl.iter labels ~f:(fun { live_vars; gotos } ->
          match live_vars with
          | Some label_vars ->
              List.iter gotos ~f:(fun (stmt, goto_vars) ->
                  (* variables which aren't in-scope at the target label should be deleted *)
                  stmt.delete_vars <-
                    Set.elements (Set.diff goto_vars label_vars))
          | None ->
              compile_error "Unresolved label"
                (ASTStatement (fst (List.last_exn gotos))));
      Hashtbl.clear labels

    method current_var_set =
      Set.of_list
        (module Int)
        (List.filter_map environment#var_list ~f:(fun v -> v.index))

    method add_continue stmt =
      let scope = Stack.top_exn scopes in
      scope.continues <- (stmt, self#current_var_set) :: scope.continues

    method add_break stmt =
      let scope = Stack.top_exn scopes in
      scope.breaks <- (stmt, self#current_var_set) :: scope.breaks

    method add_label name stmt =
      Hashtbl.update labels name ~f:(function
        | None -> { live_vars = Some self#current_var_set; gotos = [] }
        | Some { live_vars = None; gotos } ->
            { live_vars = Some self#current_var_set; gotos }
        | Some _ -> compile_error "Duplicate label" (ASTStatement stmt))

    method add_goto name stmt =
      let d =
        Hashtbl.find_or_add labels name ~default:(fun _ ->
            { live_vars = None; gotos = [] })
      in
      d.gotos <- (stmt, self#current_var_set) :: d.gotos

    method get_var_no name =
      match environment#get_local name with
      | Some v -> Option.value_exn v.index
      | None -> compiler_bug ("Undefined variable: " ^ name) None

    method add_var (v : variable) =
      let i = List.length vars in
      v.index <- Some i;
      if is_ref_scalar v.type_spec.ty then
        let void =
          {
            name = "<void>";
            location = v.location;
            array_dim = [];
            is_const = false;
            is_private = false;
            kind = v.kind;
            type_spec = { ty = Void; location = v.type_spec.location };
            initval = None;
            index = Some (i + 1);
          }
        in
        vars <- void :: v :: vars
      else vars <- v :: vars

    method create_dummy_var name ty =
      (* create dummy ref variable to store object for extent of statement *)
      let v =
        {
          name = Printf.sprintf "<dummy : %s : %d>" name !dummy_var_seqno;
          location = dummy_location;
          array_dim = [];
          is_const = false;
          is_private = false;
          kind = LocalVar;
          type_spec = { ty; location = dummy_location };
          initval = None;
          index = None;
        }
      in
      self#add_var v;
      environment#push_var v;
      dummy_var_seqno := !dummy_var_seqno + 1;
      Option.value_exn v.index

    method! visit_expression expr =
      super#visit_expression expr;
      match expr.node with
      | Ident (name, t) -> (
          (* save local variable number at identifier nodes *)
          match t with
          | LocalVariable (_, loc) ->
              expr.node <-
                Ident (name, LocalVariable (self#get_var_no name, loc))
          | _ -> ())
      | Call (_, _, calltype) -> (
          match expr.ty with
          | Ref _ ->
              let varname =
                match calltype with
                | FunctionCall fno | MethodCall (_, fno) ->
                    (Ain.get_function_by_index ctx.ain fno).name
                | _ ->
                    compiler_bug "variable_alloc_visitor: unexpected call type"
                      (Some (ASTExpression expr))
              in
              let v = self#create_dummy_var varname expr.ty in
              expr.node <- DummyRef (v, clone_expr expr)
          | _ -> ())
      | New ts ->
          let varname =
            match ts.ty with
            | Struct (name, _) -> name
            | _ ->
                compiler_bug "Non-struct type in new expression"
                  (Some (ASTExpression expr))
          in
          let v = self#create_dummy_var varname (Ref ts.ty) in
          expr.node <- DummyRef (v, clone_expr expr)
      | _ -> ()

    method! visit_statement stmt =
      (match stmt.node with
      | Compound _ -> self#start_scope
      | While (_, _) | DoWhile (_, _) -> self#start_scope
      | For (_, _, _, _) -> self#start_scope
      | Switch (_, _) -> self#start_scope
      | Label name -> self#add_label name stmt
      | Goto name -> self#add_goto name stmt
      | Continue -> self#add_continue stmt
      | Break -> self#add_break stmt
      | _ -> ());
      super#visit_statement stmt;
      match stmt.node with
      | Compound _ -> self#end_scope ScopeAnon
      | While (_, _) | DoWhile (_, _) -> self#end_scope ScopeLoop
      | For (_, _, _, _) -> self#end_scope ScopeLoop
      | Switch (_, _) -> self#end_scope ScopeSwitch
      | _ -> ()

    method! visit_variable v =
      (match v.kind with
      | (Parameter | LocalVar) when not v.is_const -> self#add_var v
      | _ -> ());
      super#visit_variable v

    method! visit_fundecl f =
      if Option.is_some f.body then (
        let conv_var index (v : variable) =
          Ain.Variable.make ~index v.name (jaf_to_ain_type v.type_spec.ty)
        in
        let add_vars (a_f : Ain.Function.t) =
          { a_f with vars = List.mapi (List.rev vars) ~f:conv_var }
        in
        self#start_scope;
        super#visit_fundecl f;
        self#end_scope ScopeAnon;
        self#resolve_gotos;
        (* write updated fundecl to ain file *)
        (match Ain.get_function ctx.ain (mangled_name f) with
        | Some obj ->
            obj |> jaf_to_ain_function f |> add_vars
            |> Ain.write_function ctx.ain
        | None ->
            compiler_bug "Undefined function"
              (Some (ASTDeclaration (Function f))));
        vars <- [])
  end

let allocate_variables ctx decls =
  (new variable_alloc_visitor ctx)#visit_toplevel decls
