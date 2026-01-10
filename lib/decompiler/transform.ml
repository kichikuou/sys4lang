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
open Ast
open Loc

type ast_transform = statement loc -> statement loc

(* Rewrites
      if (cond) { /*empty*/ } else {
        <else-body>
      }
   to
      if (cond)
        goto label;
      <else-body>
      label:
   if <else-body> contains declarations for variables used in the rest of the function. *)
let expand_else_scope stmt =
  let live_vars = ref Set.Poly.empty in
  let process_expr =
    walk_expr ~lvalue_cb:(function
      | PageRef (LocalPage, v) -> live_vars := Set.Poly.add !live_vars v
      | _ -> ())
  in
  let process_expr_opt = Option.iter ~f:process_expr in
  let rec process_stmt stmt =
    let return txt = [ { stmt with txt } ] in
    match stmt.txt with
    | VarDecl (_, None) -> [ stmt ]
    | VarDecl (_, Some (_, e)) ->
        process_expr e;
        [ stmt ]
    | Expression e ->
        process_expr e;
        [ stmt ]
    | Label _ -> [ stmt ]
    | IfElse (e, ({ txt = Block []; _ } as stmt1), stmt2) -> (
        let live_vars_after_else = !live_vars in
        let has_decls_for_live_vars { txt; _ } =
          match txt with
          | VarDecl (v, _) ->
              if Set.Poly.mem live_vars_after_else v then true else false
          | _ -> false
        in
        match rec_stmt stmt2 with
        | { txt = Block stmts; _ } as stmt2
          when List.exists stmts ~f:has_decls_for_live_vars ->
            let goto_stmt = { stmt1 with txt = Goto (stmt2.end_addr, -1) } in
            let else_block = { stmt1 with txt = Block [] } in
            let label =
              {
                txt = Label (Address stmt2.end_addr);
                addr = stmt2.end_addr;
                end_addr = stmt2.end_addr;
              }
            in
            let if_stmt =
              { stmt with txt = IfElse (e, goto_stmt, else_block) }
            in
            (label :: stmts) @ [ if_stmt ]
        | _ -> return (IfElse (e, stmt1, stmt2)))
    | IfElse (e, stmt1, stmt2) ->
        let stmt1 = rec_stmt stmt1 in
        let stmt2 = rec_stmt stmt2 in
        return @@ IfElse (e, stmt1, stmt2)
    | While (cond, body) ->
        let body = rec_stmt body in
        process_expr cond;
        return @@ While (cond, body)
    | DoWhile (body, cond) ->
        process_expr cond.txt;
        let body = rec_stmt body in
        return @@ DoWhile (body, cond)
    | For (init, cond, inc, body) ->
        let body = rec_stmt body in
        process_expr_opt init;
        process_expr_opt cond;
        process_expr_opt inc;
        return @@ For (init, cond, inc, body)
    | ForEach r ->
        let body = rec_stmt r.body in
        process_expr r.array;
        return @@ ForEach { r with body }
    | Break -> [ stmt ]
    | Continue -> [ stmt ]
    | Goto _ -> [ stmt ]
    | Return e ->
        process_expr_opt e;
        [ stmt ]
    | ScenarioJump _ -> [ stmt ]
    | Msg (_, e) ->
        process_expr_opt e;
        [ stmt ]
    | Assert e ->
        process_expr e;
        [ stmt ]
    | Block stmts ->
        return @@ Block (List.concat (List.map stmts ~f:process_stmt))
        (* reversed order *)
    | Switch (id, e, stmt) ->
        let stmt = rec_stmt stmt in
        process_expr e;
        return @@ Switch (id, e, stmt)
  and rec_stmt stmt = make_block (process_stmt stmt) in
  if Ain.ain.ifthen_optimized then rec_stmt stmt else stmt

let rename_labels stmt =
  let targets = ref [] in
  walk_statement stmt ~f:(function
    | Goto (addr, _) when not (List.mem !targets addr ~equal:( = )) ->
        targets := addr :: !targets
    | _ -> ());
  let targets =
    List.rev !targets
    |> List.mapi ~f:(fun i addr -> (addr, i))
    |> Hashtbl.of_alist_exn (module Int)
  in
  let last_label_addr = ref (-1) in
  let rec update stmt =
    let txt =
      match stmt.txt with
      | Label (Address addr) -> (
          match Hashtbl.find targets addr with
          | Some i when addr <> !last_label_addr ->
              last_label_addr := addr;
              Label (Address i)
          | _ -> Block [] (* remove unused or duplicate labels *))
      | IfElse (e, stmt1, stmt2) -> IfElse (e, update stmt1, update stmt2)
      | While (cond, body) -> While (cond, update body)
      | DoWhile (body, cond) -> DoWhile (update body, cond)
      | For (init, cond, inc, body) -> For (init, cond, inc, update body)
      | Block stmts ->
          (List.map stmts ~f:update
          |> List.filter ~f:(function
            | { txt = Block []; _ } -> false
            | _ -> true)
          |> make_block)
            .txt
      | Switch (id, e, stmt) -> Switch (id, e, update stmt)
      | Goto (addr, x) -> Goto (Hashtbl.find_exn targets addr, x)
      | stmt -> stmt
    in
    { stmt with txt }
  in
  update stmt

let recover_loop_initializer stmt =
  let rec reduce left = function
    | [] -> left
    | s1 :: ({ txt = For (None, None, None, _); _ } as s2) :: right ->
        (* Do not transform loops where both cond and inc are empty. *)
        reduce (s2 :: s1 :: left) right
    | { txt = Expression (AssignOp _ as init); addr; _ }
      :: { txt = For (None, cond, inc, body); end_addr; _ }
      :: right ->
        reduce
          ({ txt = For (Some init, cond, inc, body); addr; end_addr } :: left)
          right
    | { txt = VarDecl (var, Some (inst, expr)); addr; _ }
      :: { txt = For (None, cond, inc, body); end_addr; _ }
      :: right ->
        reduce
          ({
             txt =
               For
                 ( Some (AssignOp (inst, PageRef (LocalPage, var), expr)),
                   cond,
                   inc,
                   body );
             addr;
             end_addr;
           }
          :: { txt = VarDecl (var, None); addr; end_addr = addr }
          :: left)
          right
    | stmt :: right -> reduce (stmt :: left) right
  in
  map_block stmt ~f:(fun stmts -> reduce [] (List.rev stmts))

let remove_redundant_return stmt =
  {
    stmt with
    txt =
      (match stmt.txt with
      | Return None -> Block []
      | Block ({ txt = Return None; _ } :: stmts) -> Block stmts
      | Block ({ txt = Return _; _ } :: ({ txt = Return _; _ } :: _ as stmts))
        ->
          Block stmts
      | stmt -> stmt);
  }

let remove_implicit_array_free stmt =
  let process_block stmts =
    let vars =
      List.rev_filter_map stmts ~f:(function
        | { txt = VarDecl (({ type_ = Array _; _ } as var), _); _ } -> Some var
        | _ -> None)
    in
    let remove_free vars stmts =
      List.drop_while stmts ~f:(function
        | {
            txt =
              Expression
                ( Call (Builtin (A_FREE, PageRef (LocalPage, v)), [])
                | Call
                    ( HllFunc ("Array", { name = "Free"; _ }),
                      [ Deref (PageRef (_, v)) ] ) );
            _;
          } ->
            List.exists vars ~f:(fun var -> phys_equal var v)
        | _ -> false)
    in
    let rec walk vars stmts =
      match stmts with
      | [] -> []
      | ({ txt = Goto _ | Break | Continue; _ } as stmt) :: stmts ->
          stmt :: walk vars (remove_free vars stmts)
      | stmt :: stmts -> stmt :: walk vars stmts
    in
    if List.is_empty vars then stmts else walk vars (remove_free vars stmts)
  in
  match stmt with
  | { txt = Block stmts; _ } ->
      { stmt with txt = Block (List.map stmts ~f:(map_block ~f:process_block)) }
  | stmt -> map_block stmt ~f:process_block

(* Some functions in Rance 6 and Tsuma Shibori have Array.free for out-of-scope
   variables. This transform removes them. *)
let remove_array_free_for_dead_arrays stmt =
  let dead_arrays = ref [] in
  let process_block stmts =
    let arrays =
      List.filter_map stmts ~f:(function
        | { txt = VarDecl (({ type_ = Array _; _ } as var), _); _ } -> Some var
        | _ -> None)
    in
    let rec remove_free = function
      | {
          txt = Expression (Call (Builtin (A_FREE, PageRef (LocalPage, v)), []));
          _;
        }
        :: stmts
        when List.exists !dead_arrays ~f:(fun var -> phys_equal var v) ->
          Stdio.eprintf
            "Warning: Removing Array.free for out-of-scope variable %s\n" v.name;
          remove_free stmts
      | ({ txt = Break | Goto _; _ } as stmt) :: stmts ->
          stmt :: remove_free stmts
      | stmts -> stmts
    in
    let stmts = remove_free stmts in
    dead_arrays := List.append arrays !dead_arrays;
    stmts
  in
  map_block stmt ~f:process_block

(* Removes Array.Free() for temporary arrays for array literals. *)
let remove_array_free_for_temporary_arrays stmt =
  if Ain.ain.vers < 12 then stmt
  else
    let process_block =
      List.filter ~f:(function
        | {
            txt =
              Expression
                (Call
                   ( HllFunc ("Array", { name = "Free"; _ }),
                     [ Deref (PageRef (_, v)) ] ));
            _;
          } ->
            not (String.is_prefix v.name ~prefix:"<dummy : new array")
        | _ -> true)
    in
    map_block stmt ~f:process_block

let remove_generated_initializer_call = function
  | { txt = Block stmts; _ } as stmt -> (
      match List.rev stmts with
      | { txt = Expression (Call (Method (Page StructPage, f), [])); _ } :: rest
        when String.is_suffix f.name ~suffix:"@2" ->
          { stmt with txt = Block (List.rev rest) }
      | _ -> stmt)
  | stmt -> stmt

let remove_dummy_variable_assignment stmt =
  let strip_dummy_assignment = function
    | AssignOp (_, PageRef (LocalPage, v), expr) when Ain.Variable.is_dummy v ->
        expr
    | expr -> expr
  in
  map_expr ~f:strip_dummy_assignment stmt
  |> map_stmt ~f:(function
    | VarDecl (v, Some (_, e)) when Ain.Variable.is_dummy v -> Expression e
    | stmt -> stmt)

let remove_generated_lockpeek stmt =
  let rec reduce left = function
    | [] -> left
    | ({ txt = Expression (Call (SysCall 4, [])); _ } as unlockpeek) :: right
      -> (
        match left with
        | (( { txt = VarDecl ({ type_ = Ref _; _ }, Some _); _ }
           | { txt = Expression (AssignOp (PSEUDO_REF_ASSIGN, _, _)); _ } ) as
           stmt)
          :: { txt = Expression (Call (SysCall 3, [])); _ }
          :: left ->
            reduce (stmt :: left) right
        | { txt = Expression (Call (SysCall 3, [])); _ } :: left ->
            reduce left right
        | _ -> reduce (unlockpeek :: left) right)
    | stmt :: right -> reduce (stmt :: left) right
  in
  map_block stmt ~f:(fun stmts -> reduce [] (List.rev stmts))

let remove_vardecl_default_rhs stmt =
  map_stmt stmt ~f:(function
    | VarDecl
        ( v,
          Some (_, (Null | DerefRef NullRef | Number 0l | Float 0.0 | String ""))
        ) ->
        VarDecl (v, None)
    | s -> s)

let fold_newline_func_to_msg stmt =
  let rec reduce left = function
    | [] -> left
    | { txt = Msg (m, None); addr; _ }
      :: { txt = Expression (Call _ as e); end_addr; _ }
      :: right ->
        reduce ({ txt = Msg (m, Some e); addr; end_addr } :: left) right
    | stmt :: right -> reduce (stmt :: left) right
  in
  map_block stmt ~f:(fun stmts -> reduce [] (List.rev stmts))

let remove_optional_arguments =
  map_expr ~f:(function
    | Call ((Builtin (PSEUDO_A_NUMOF1, _) as f), [ Number 1l ]) -> Call (f, [])
    | Call
        ( (Builtin (A_SORT, _) as f),
          [ (Null | BoundMethod (Number -1l, { name = "NULL"; _ })) ] ) ->
        Call (f, [])
    | Call
        ( (Builtin (A_FIND, _) as f),
          [ a; b; c; (Null | BoundMethod (Number -1l, { name = "NULL"; _ })) ]
        ) ->
        Call (f, [ a; b; c ])
    | Call ((Builtin2 (FTOS, _) as f), [ Number -1l ]) -> Call (f, [])
    | expr -> expr)

(** Rewrites
    {[
      ref array@T dummy2 = array_expr;
      int dummy1 = -1;
      while (++dummy1 < Array.Numof(dummy2)) {
        ref T var = dummy2[dummy1];
        body;
      }
    ]}
    to
    {[
      foreach (var : array_expr) { body }
    ]}

    and
    {[
      ref array@T dummy2 = array_expr;
      int dummy1 = Array.Numof(dummy2);
      while (--dummy1 >= 0) {
        ref T var = dummy2[dummy1];
        body;
      }
    ]}
    to
    {[
      foreach_r (var : array_expr) { body }
    ]} *)
let recognize_foreach stmt =
  let maybe_match_foreach i_assign arr_assign while_stmt =
    match (i_assign, arr_assign, while_stmt) with
    | ( { txt = VarDecl (arr_dummy, Some (ASSIGN, array_expr)); _ },
        { txt = VarDecl (i_var, Some (ASSIGN, i_init)); _ },
        { txt = While (while_cond, while_body); addr; end_addr } ) -> (
        match (i_init, while_cond) with
        | ( Number -1l,
            BinaryOp
              ( LT,
                Deref (IncDec (Prefix, Increment, PageRef (LocalPage, i_var'))),
                Call
                  ( HllFunc ("Array", { name = "Numof"; _ }),
                    [ Deref (PageRef (LocalPage, arr_var)) ] ) ) )
        | ( Call
              ( HllFunc ("Array", { name = "Numof"; _ }),
                [ Deref (PageRef (LocalPage, arr_var)) ] ),
            BinaryOp
              ( GTE,
                Deref (IncDec (Prefix, Decrement, PageRef (LocalPage, i_var'))),
                Number 0l ) )
          when phys_equal i_var i_var'
               && phys_equal arr_dummy arr_var
               && Ain.Variable.is_dummy arr_dummy -> (
            let body_stmts =
              match while_body.txt with
              | Block stmts -> stmts
              | s -> [ { while_body with txt = s } ]
            in
            match List.rev body_stmts with
            | {
                txt =
                  VarDecl
                    ( loop_var,
                      Some
                        ( R_ASSIGN,
                          DerefRef
                            (ArrayRef
                               ( Deref (PageRef (LocalPage, arr_var'')),
                                 Deref (PageRef (LocalPage, i_var'')) )) ) );
                _;
              }
              :: body_rest ->
                if phys_equal arr_var arr_var'' && phys_equal i_var i_var'' then
                  let new_body = make_block (List.rev body_rest) in
                  let foreach_stmt =
                    {
                      txt =
                        ForEach
                          {
                            rev = not Poly.(i_init = Number (-1l));
                            var = loop_var;
                            ivar =
                              (if Ain.Variable.is_dummy i_var then None
                               else Some i_var);
                            array = array_expr;
                            body = new_body;
                          };
                      addr;
                      end_addr;
                    }
                  in
                  Some foreach_stmt
                else None
            | _ -> None)
        | _ -> None)
    | _ -> None
  in
  let rec reduce acc stmts =
    match stmts with
    | s3 :: s2 :: s1 :: tail -> (
        match maybe_match_foreach s1 s2 s3 with
        | Some new_stmt -> reduce (new_stmt :: acc) tail
        | None -> reduce (s3 :: acc) (s2 :: s1 :: tail))
    | s :: tail -> reduce (s :: acc) tail
    | [] -> List.rev acc
  in
  map_block stmt ~f:(fun stmts -> reduce [] stmts)

let simplify_boolean_expr stmt =
  if Ain.ain.vers < 6 then stmt
  else
    map_expr stmt ~f:(function
      | UnaryOp (NOT, BinaryOp (GT, e1, e2)) -> BinaryOp (LTE, e1, e2)
      | UnaryOp (NOT, BinaryOp (LT, e1, e2)) -> BinaryOp (GTE, e1, e2)
      | UnaryOp (NOT, BinaryOp (GTE, e1, e2)) -> BinaryOp (LT, e1, e2)
      | UnaryOp (NOT, BinaryOp (LTE, e1, e2)) -> BinaryOp (GT, e1, e2)
      | UnaryOp (NOT, BinaryOp (EQUALE, e1, e2)) -> BinaryOp (NOTE, e1, e2)
      | UnaryOp (NOT, BinaryOp (NOTE, e1, e2)) -> BinaryOp (EQUALE, e1, e2)
      | BinaryOp (NOTE, e, Boolean false) -> e
      | expr -> expr)

let strip_option = function Option obj -> obj | obj -> obj

let convert_ternary_op_to_null_coalescing stmt =
  if Ain.ain.vers < 11 then stmt
  else
    map_expr stmt ~f:(function
      | TernaryOp
          ( UnaryOp
              (NOT, BinaryOp ((EQUALE | R_EQUALE), obj, (Null | Number -1l))),
            e1,
            e2 )
        when contains_expr e1 (strip_option obj) ->
          BinaryOp
            (PSEUDO_NULL_COALESCE, insert_option e1 (strip_option obj), e2)
      | TernaryOp
          (BinaryOp ((EQUALE | R_EQUALE), obj, (Null | Number -1l)), e1, e2)
        when contains_expr e2 (strip_option obj) ->
          BinaryOp
            (PSEUDO_NULL_COALESCE, insert_option e2 (strip_option obj), e1)
      | expr -> expr)

let simplify_null_coalescing stmt =
  if Ain.ain.vers < 11 then stmt
  else
    map_expr stmt ~f:(function
      (* expr? ?? NULL | expr ?? NULL => expr *)
      | BinaryOp (PSEUDO_NULL_COALESCE, (Option e1 | e1), Null) -> e1
      (* expr1? ?? expr2 => expr1 ?? expr2 *)
      | BinaryOp (PSEUDO_NULL_COALESCE, Option e1, e2) ->
          BinaryOp (PSEUDO_NULL_COALESCE, e1, e2)
      | expr -> expr)

let apply_all_transforms stmt =
  stmt |> convert_ternary_op_to_null_coalescing |> simplify_null_coalescing
  |> expand_else_scope |> rename_labels |> recover_loop_initializer
  |> recognize_foreach |> remove_implicit_array_free
  |> remove_array_free_for_dead_arrays |> remove_array_free_for_temporary_arrays
  |> remove_generated_lockpeek |> remove_redundant_return
  |> remove_dummy_variable_assignment |> remove_vardecl_default_rhs
  |> fold_newline_func_to_msg |> remove_optional_arguments
  |> simplify_boolean_expr
