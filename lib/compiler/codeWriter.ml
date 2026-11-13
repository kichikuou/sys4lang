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
open Bytecode
open CompileError

type cflow_type =
  | CFlowLoop of { continue_addr : int (* -1 if it is not yet known *) }
  | CFlowSwitch of Ain.Switch.t

type cflow_stmt = {
  kind : cflow_type;
  mutable break_addrs : int list;
  mutable continue_addrs : int list;
}

type scope = { mutable vars : variable list }

type label_data = {
  mutable address : int option;
  mutable gotos : (int * statement) list;
}

(* Writes the code of a source file to the AIN: instructions and their
   addresses, the CRC and the table entry of each function, debug information,
   labels, scopes, and the switch and string tables. A code generator inherits
   this class. *)
class virtual code_writer ctx debug_info =
  object (self)
    (* The function currently being compiled. *)
    val mutable current_function : fundecl option = None

    (* The bytecode output buffer. *)
    val mutable buffer = CBuffer.create 2048

    (* Address of the start of the current buffer. *)
    val mutable start_address : int = Ain.code_size ctx.ain

    (* Current address within the code section. *)
    val mutable current_address : int = Ain.code_size ctx.ain

    (* The currently active control flow constructs. *)
    val mutable cflow_stmts = Stack.create ()

    (* The currentl active scopes. *)
    val scopes = Stack.create ()

    (* Labels/gotos record for the current function. *)
    val mutable labels = Hashtbl.create (module String)

    (* Running CRC-32 of the current function. *)
    val mutable crc_state : Crc32.t = Crc32.Inactive

    (** Emit the code to delete a variable at the end of its scope. *)
    method virtual compile_delete_var : variable -> unit

    (** Record the source location of the code that follows. *)
    method mark_location loc = DebugInfo.add_loc debug_info current_address loc

    (** Record the current address as an ain v1 scenario label. *)
    method add_scenario_label name =
      Ain.add_scenario_label ctx.ain name current_address

    method add_string s = Ain.add_string ctx.ain s
    method add_message s = Ain.add_message ctx.ain s

    (** Begin a scope. Variables created within a scope are deleted when the
        scope ends. *)
    method start_scope = Stack.push scopes { vars = [] }

    (** End a scope. Deletes variable created within the scope. *)
    method end_scope =
      let scope = Stack.pop_exn scopes in
      (* delete scope-local variables *)
      (* NOTE: Variables are deleted automatically by the VM upon function
               return. This code is emitted only to ensure that destructors are
               called at the correct time; hence function-scoped variables need
               not be deleted here. *)
      match Stack.top scopes with
      | None -> ()
      | Some _ -> List.iter scope.vars ~f:self#compile_delete_var

    (** Add a variable to the current scope. *)
    method scope_add_var v =
      match Stack.top scopes with
      | Some scope -> scope.vars <- v :: scope.vars
      | None -> compiler_bug "tried to add variable to null scope" None

    (** Add a label for the current function. *)
    method add_label name stmt =
      self#crc_push_word 0x406;
      self#crc_push_label_name name;
      Hashtbl.update labels name ~f:(function
        | None -> { address = Some current_address; gotos = [] }
        | Some { address = None; gotos } ->
            { address = Some current_address; gotos }
        | Some _ -> compile_error "Duplicate label" (ASTStatement stmt))

    (** Emit a jump to a label of the current function. *)
    method write_goto name stmt =
      self#crc_push_word 0x407;
      self#crc_push_label_name name;
      let d =
        Hashtbl.find_or_add labels name ~default:(fun _ ->
            { address = None; gotos = [] })
      in
      d.gotos <- (current_address + 2, stmt) :: d.gotos;
      (* The 0x407 marker replaces the JUMP, so don't hash the JUMP. *)
      let saved = crc_state in
      crc_state <- Crc32.Inactive;
      self#write_instruction1 JUMP 0;
      crc_state <- saved

    (** Resolve all goto addresses in the current function. *)
    method private resolve_gotos =
      Hashtbl.iter labels ~f:(fun { address; gotos } ->
          match address with
          | Some addr ->
              List.iter gotos ~f:(fun (addr_loc, _) ->
                  self#write_address_at addr_loc addr)
          | None ->
              compile_error "Unresolved label"
                (ASTStatement (snd (List.last_exn gotos))));
      Hashtbl.clear labels

    (** Begin a loop. *)
    method start_loop continue_addr =
      Stack.push cflow_stmts
        {
          kind = CFlowLoop { continue_addr };
          break_addrs = [];
          continue_addrs = [];
        }

    (** Begin a switch statement. *)
    method start_switch ty node =
      let op, case_type =
        match ty with
        | Jaf.Bool | Int | LongInt -> (SWITCH, Ain.Switch.IntCase)
        | String -> (STRSWITCH, Ain.Switch.StringCase)
        | _ -> compiler_bug "invalid switch type" (Some node)
      in
      let switch = Ain.add_switch ctx.ain case_type in
      Stack.push cflow_stmts
        { kind = CFlowSwitch switch; break_addrs = []; continue_addrs = [] };
      self#write_instruction1 op switch.index

    (** End the current control flow construct. Updates 'break' addresses. *)
    method end_cflow_stmt =
      let stmt = Stack.pop_exn cflow_stmts in
      List.iter stmt.break_addrs ~f:(fun addr ->
          self#write_address_at addr current_address)

    (** End the current loop. Updates 'break' addresses. *)
    method end_loop =
      (match Stack.top cflow_stmts with
      | Some { kind = CFlowLoop _; _ } -> ()
      | _ -> compiler_bug "Mismatched start/end of control flow construct" None);
      self#end_cflow_stmt

    (** End the current switch statement. Updates 'break' addresses. *)
    method end_switch =
      (match Stack.top cflow_stmts with
      | Some { kind = CFlowSwitch switch; _ } -> Ain.write_switch ctx.ain switch
      | _ -> compiler_bug "Mismatched start/end of control flow construct" None);
      self#end_cflow_stmt

    method add_switch_case expr node =
      let (switch : Ain.Switch.t) = self#current_switch node in
      let value =
        match expr with
        | ConstInt n -> (
            match switch.case_type with
            | Ain.Switch.IntCase -> n
            | Ain.Switch.StringCase ->
                compile_error "int case in string switch" node)
        | ConstString s -> (
            match switch.case_type with
            | Ain.Switch.StringCase -> self#add_string s
            | Ain.Switch.IntCase ->
                compile_error "string case in int switch" node)
        | _ -> compile_error "invalid expression in switch case" node
      in
      switch.cases <-
        List.append switch.cases [ (Int32.of_int_exn value, current_address) ]

    method set_switch_default node =
      let switch = self#current_switch node in
      switch.default_address <- current_address

    (** Emit a 'continue' jump for the innermost enclosing loop. If the loop's
        continue target is not yet known (do-while), the jump operand location
        is recorded for later patching. *)
    method add_continue node =
      let nearest_loop =
        Stack.find cflow_stmts ~f:(function
          | { kind = CFlowLoop _; _ } -> true
          | _ -> false)
      in
      match nearest_loop with
      | Some { kind = CFlowLoop { continue_addr }; _ } when continue_addr >= 0
        ->
          self#write_instruction1 JUMP continue_addr
      | Some loop ->
          loop.continue_addrs <- (current_address + 2) :: loop.continue_addrs;
          self#write_instruction1 JUMP 0
      | None -> compile_error "'continue' statement outside of loop" node

    (** Make the pending 'continue' jumps of the innermost loop jump to the
        current address. *)
    method resolve_continues =
      List.iter (Stack.top_exn cflow_stmts).continue_addrs ~f:(fun addr ->
          self#write_address_at addr current_address)

    (** Retrieves the index for the current switch statement. *)
    method current_switch node =
      match Stack.top cflow_stmts with
      | Some { kind = CFlowSwitch switch; _ } -> switch
      | _ -> compile_error "switch case outside of switch statement" node

    (** Push the location of a 32-bit integer that should be updated to the
        address of the current scope's end point. *)
    method push_break_addr addr node =
      match Stack.top cflow_stmts with
      | Some stmt -> stmt.break_addrs <- addr :: stmt.break_addrs
      | None -> compile_error "'break' statement outside of loop" node

    (* Feed a 32-bit word into the running CRC. *)
    method private crc_push_word n = crc_state <- Crc32.feed_word crc_state n

    (* Hash a label/goto's qualified name "FuncName::labelName" into the CRC. *)
    method private crc_push_label_name label =
      let name =
        mangled_name (Option.value_exn current_function) ^ "::" ^ label
      in
      crc_state <- Crc32.feed_string crc_state name

    method write_instruction0 op =
      CBuffer.write_int16 buffer (int_of_opcode op);
      self#crc_push_word (int_of_opcode op);
      current_address <- current_address + 2

    method write_instruction1 op arg0 =
      match op with
      | SH_STRUCTREF when Ain.version_lt ctx.ain (1, 0) ->
          (* ain v0 encodes SH_STRUCTREF as 0x62 (which is EOF from v1 on). *)
          CBuffer.write_int16 buffer 0x62;
          self#crc_push_word 0x62;
          CBuffer.write_int32 buffer arg0;
          current_address <- current_address + 6
      | S_MOD when Ain.version_lt ctx.ain (11, 0) ->
          self#write_instruction1 PUSH arg0;
          self#write_instruction0 S_MOD
      | _ ->
          CBuffer.write_int16 buffer (int_of_opcode op);
          self#crc_push_word (int_of_opcode op);
          CBuffer.write_int32 buffer arg0;
          current_address <- current_address + 6

    method write_instruction1_float op arg0 =
      CBuffer.write_int16 buffer (int_of_opcode op);
      self#crc_push_word (int_of_opcode op);
      CBuffer.write_float buffer arg0;
      current_address <- current_address + 6

    method write_instruction2 op arg0 arg1 =
      CBuffer.write_int16 buffer (int_of_opcode op);
      self#crc_push_word (int_of_opcode op);
      CBuffer.write_int32 buffer arg0;
      CBuffer.write_int32 buffer arg1;
      current_address <- current_address + 10

    method write_instruction3 op arg0 arg1 arg2 =
      CBuffer.write_int16 buffer (int_of_opcode op);
      self#crc_push_word (int_of_opcode op);
      CBuffer.write_int32 buffer arg0;
      CBuffer.write_int32 buffer arg1;
      CBuffer.write_int32 buffer arg2;
      current_address <- current_address + 14

    method write_address_at dst addr =
      CBuffer.write_int32_at buffer (dst - start_address) addr

    method write_buffer =
      if current_address > start_address then (
        Ain.append_bytecode ctx.ain buffer;
        CBuffer.clear buffer;
        start_address <- current_address)

    (** Emit the EOF instruction that ends the code of a source file. *)
    method write_eof jaf_name =
      if Ain.version_gte ctx.ain (1, 0) then
        let jaf_name = String.tr ~target:'/' ~replacement:'\\' jaf_name in
        self#write_instruction1 EOF (Ain.add_file ctx.ain jaf_name)

    (** Emit a function, and write its address and CRC to the function table.
        [body] emits the code between FUNC and ENDFUNC. *)
    method write_function (decl : fundecl) ~endfunc ~(body : unit -> unit) =
      let index = Option.value_exn decl.index in
      let address = current_address + 6 in
      let prev_function = current_function in
      current_function <- Some decl;
      let prev_cflow_stmts = cflow_stmts in
      cflow_stmts <- Stack.create ();
      let prev_labels = labels in
      labels <- Hashtbl.create (module String);
      (* Freeze the parent's CRC: it stops at this nested FUNC (lambda). *)
      let prev_crc_state = Crc32.freeze crc_state in
      self#write_instruction1 FUNC index;
      (* Accumulate the function CRC over the return/argument type codes and the
         body opcodes. FUNC and ENDFUNC are excluded. *)
      crc_state <- Crc32.start;
      let int_of_data_type t =
        Ain.Type.int_of_data_type (Ain.version ctx.ain) (jaf_to_ain_type t)
      in
      self#crc_push_word (int_of_data_type decl.return.ty);
      List.iter decl.params ~f:(fun v ->
          self#crc_push_word (int_of_data_type v.type_spec.ty));
      body ();
      let crc = Crc32.finalize crc_state in
      crc_state <- prev_crc_state;
      if endfunc then self#write_instruction1 ENDFUNC index;
      self#resolve_gotos;
      Ain.write_function ctx.ain
        { (Ain.get_function_by_index ctx.ain index) with address; crc };
      current_function <- prev_function;
      cflow_stmts <- prev_cflow_stmts;
      labels <- prev_labels
  end
