(* Copyright (C) 2025 kichikuou <KichikuouChrome@gmail.com>
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
open Document
module Lsp = Linol_lsp.Lsp

let encoding_of_string s =
  match String.lowercase s with
  | "utf-8" -> Pje.UTF8
  | "shift_jis" -> Pje.SJIS
  | _ -> raise (Invalid_argument ("Invalid encoding: " ^ s))

type t = {
  read_file : string -> string;
  mutable ctx : Jaf.context;
  mutable pje : Pje.t;
  documents : (string, Document.t) Hashtbl.t;
}

let backslash_to_slash = String.map ~f:(function '\\' -> '/' | c -> c)

let find_document proj path =
  Hashtbl.find proj.documents (backslash_to_slash path)

let set_document proj path doc =
  Hashtbl.set proj.documents ~key:(backslash_to_slash path) ~data:doc

let predefined_constants =
  Jaf.
    [
      {
        name = "true";
        location = dummy_location;
        array_dim = [];
        is_const = true;
        is_private = false;
        kind = GlobalVar;
        type_spec = { ty = Bool; location = dummy_location };
        initval = None;
        index = None;
      };
      {
        name = "false";
        location = dummy_location;
        array_dim = [];
        is_const = true;
        is_private = false;
        kind = GlobalVar;
        type_spec = { ty = Bool; location = dummy_location };
        initval = None;
        index = None;
      };
    ]

let create ~read_file =
  {
    read_file;
    ctx = Jaf.context_from_ain ~constants:predefined_constants (Ain.create 4 0);
    pje = Pje.default_pje "default.pje" SJIS;
    documents = Hashtbl.create (module String);
  }

let initialize proj (options : Types.InitializationOptions.t) =
  match options.pjePath with
  | "" ->
      if not (String.is_empty options.ainPath) then
        proj.ctx <-
          Jaf.context_from_ain ~constants:predefined_constants
            (Ain.load options.ainPath);
      proj.pje.source_dir <- options.srcDir;
      if not (String.is_empty options.srcEncoding) then
        proj.pje.encoding <- encoding_of_string options.srcEncoding
  | pjePath ->
      proj.pje <- PjeLoader.load proj.read_file pjePath;
      let open Stdlib.Filename in
      if String.equal proj.pje.source_dir "." then
        proj.pje.source_dir <- dirname pjePath
      else if is_relative proj.pje.source_dir then
        proj.pje.source_dir <- concat (dirname pjePath) proj.pje.source_dir

let resolve_source_path proj fname =
  Stdlib.Filename.concat proj.pje.source_dir fname

let update_document proj ~path contents =
  let doc = Document.create proj.ctx ~fname:path contents in
  set_document proj path doc;
  List.map doc.errors ~f:(fun (range, message) ->
      Lsp.Types.Diagnostic.create ~range ~message:(`String message) ())

let load_document proj fname =
  let path = resolve_source_path proj fname in
  let to_utf8 =
    match proj.pje.encoding with UTF8 -> Fn.id | SJIS -> Sjis.to_utf8
  in
  let contents = proj.read_file path |> to_utf8 in
  update_document proj ~path contents |> ignore

let initial_scan proj =
  let to_utf8 =
    match proj.pje.encoding with UTF8 -> Fn.id | SJIS -> Sjis.to_utf8
  in
  List.map (Pje.collect_sources proj.pje) ~f:(fun source ->
      match source with
      | Jaf fname ->
          let path = resolve_source_path proj fname in
          Document.parse proj.ctx ~fname:path (proj.read_file path |> to_utf8)
      | Hll (fname, hll_import_name) ->
          let path = resolve_source_path proj fname in
          Document.parse proj.ctx ~fname:path ~hll_import_name
            (proj.read_file path |> to_utf8)
      | Include _ -> failwith "unexpected include")
  |> List.iter ~f:(fun doc ->
      Document.resolve ~decl_only:true doc;
      set_document proj doc.path doc)

let rec jaf_base_type = function
  | Jaf.Ref t | Jaf.Array t | Jaf.Wrap t -> jaf_base_type t
  | t -> t

let get_hover proj ~path pos =
  match find_document proj path with
  | None -> None
  | Some doc -> (
      let make_hover location content =
        Some
          (Lsp.Types.Hover.create
             ~contents:
               (`MarkupContent
                  (Lsp.Types.MarkupContent.create ~kind:PlainText ~value:content))
             ~range:(to_lsp_range doc.lexbuf.lex_buffer location)
             ())
      in
      match get_nodes_for_pos doc pos with
      | Jaf.ASTExpression { node = Member (_, _, SystemFunction sys); loc; _ }
        :: _ ->
          let f = Builtin.fundecl_of_syscall sys in
          make_hover loc (Jaf.decl_to_string (Function f))
      | Jaf.ASTExpression
          { node = Member (_, _, HLLFunction (lib_name, fun_name)); loc; _ }
        :: _ ->
          Option.bind (Jaf.find_hll_function proj.ctx lib_name fun_name)
            ~f:(fun decl -> make_hover loc (Jaf.decl_to_string (Function decl)))
      | (Jaf.ASTExpression
           { node = Member (obj, _, BuiltinMethod builtin); loc; _ } as ast_node)
        :: _ ->
          let f =
            Builtin.fundecl_of_builtin proj.ctx builtin obj.ty (Some ast_node)
          in
          make_hover loc (Jaf.decl_to_string (Function f))
      | Jaf.ASTExpression
          { node = Member (_, _, ClassMethod (name, _)); loc; _ }
        :: _
      | Jaf.ASTExpression { node = Ident (_, FunctionName name); loc; _ } :: _
        ->
          Option.bind (Hashtbl.find proj.ctx.functions name) ~f:(fun decl ->
              make_hover loc
                (Jaf.decl_to_string (Function { decl with body = None })))
      | Jaf.ASTExpression { ty; loc; _ } :: _ ->
          make_hover loc (Jaf.jaf_type_to_string ty)
      | Jaf.ASTType { ty; location } :: _ -> (
          match jaf_base_type ty with
          | Struct (name, _) ->
              let s = Hashtbl.find_exn proj.ctx.structs name in
              make_hover location ("class " ^ s.name)
          | FuncType (Some (name, _)) ->
              let ft = Hashtbl.find_exn proj.ctx.functypes name in
              make_hover location ("functype " ^ ft.name)
          | Delegate (Some (name, _)) ->
              let dg = Hashtbl.find_exn proj.ctx.delegates name in
              make_hover location ("delegate " ^ dg.name)
          | _ -> None)
      | (Jaf.ASTStructDecl sdecl as decl) :: _ ->
          make_hover (Jaf.ast_node_pos decl) (Jaf.sdecl_to_string sdecl)
      | _ -> None)

let filename_of_func ain (func : Ain.Function.t) =
  let code = Ain.get_code ain in
  let rec find_eof addr =
    match Bytecode.opcode_of_int (Stdlib.Bytes.get_int16_le code addr) with
    | EOF ->
        let i = Stdlib.Bytes.get_int32_le code (addr + 2) in
        Ain.get_file ain (Int32.to_int_exn i)
    | op ->
        let nr_args = List.length (Bytecode.args_of_opcode op) in
        find_eof (addr + 2 + (nr_args * 4))
  in
  find_eof func.address

let location_of_func proj name =
  match Hashtbl.find proj.ctx.functions name with
  | Some f when Option.is_some f.body -> Some f.loc
  | _ ->
      (* Load .jaf file and try again. *)
      Option.(
        Ain.get_function proj.ctx.ain name >>= fun func ->
        filename_of_func proj.ctx.ain func >>= fun fname ->
        load_document proj (backslash_to_slash fname);
        Hashtbl.find proj.ctx.functions name >>| fun f -> f.loc)

let find_location proj path pos f =
  match find_document proj path with
  | None -> None
  | Some doc -> (
      match f (get_nodes_for_pos doc pos) with
      | Some loc -> (
          let fname = (fst loc).Lexing.pos_fname in
          match find_document proj fname with
          | None -> None
          | Some doc ->
              let range = to_lsp_range doc.lexbuf.lex_buffer loc in
              let uri = Lsp.Types.DocumentUri.of_path fname in
              Some (`Location [ Lsp.Types.Location.create ~uri ~range ]))
      | None -> None)

let get_definition proj ~path pos =
  find_location proj path pos (function
    | Jaf.ASTExpression { node = Ident (_, LocalVariable (_, loc)); _ } :: _ ->
        Some loc
    | Jaf.ASTExpression
        { node = Ident (name, (GlobalVariable _ | GlobalConstant)); _ }
      :: _ -> (
        match Hashtbl.find proj.ctx.globals name with
        | Some v -> Some v.location
        | None -> None)
    | Jaf.ASTExpression { node = Ident (_, FunctionName name); _ } :: _
    | Jaf.ASTExpression { node = Member (_, _, ClassMethod (name, _)); _ } :: _
      ->
        location_of_func proj name
    | Jaf.ASTExpression
        { node = Member (_, _, HLLFunction (lib_name, fun_name)); _ }
      :: _ ->
        Option.map (Jaf.find_hll_function proj.ctx lib_name fun_name)
          ~f:(fun decl -> decl.loc)
    | Jaf.ASTExpression
        {
          node = Member ({ ty = Struct (s_name, _); _ }, m_name, ClassVariable _);
          _;
        }
      :: _ ->
        let s = Hashtbl.find_exn proj.ctx.structs s_name in
        let v = Hashtbl.find_exn s.members m_name in
        Some v.location
    | Jaf.ASTType { ty; _ } :: _ -> (
        match jaf_base_type ty with
        | Struct (name, _) -> Some (Hashtbl.find_exn proj.ctx.structs name).loc
        | FuncType (Some (name, _)) ->
            Some (Hashtbl.find_exn proj.ctx.functypes name).loc
        | Delegate (Some (name, _)) ->
            Some (Hashtbl.find_exn proj.ctx.delegates name).loc
        | _ -> None)
    | Jaf.ASTStructDecl (Method d | Constructor d | Destructor d) :: _ ->
        location_of_func proj (Jaf.mangled_name d)
    | _ -> None)

let get_type_definition proj ~path pos =
  find_location proj path pos (function
    | Jaf.ASTExpression { ty; _ } :: _ -> (
        match jaf_base_type ty with
        | Struct (name, _) -> Some (Hashtbl.find_exn proj.ctx.structs name).loc
        | FuncType (Some (name, _)) ->
            Some (Hashtbl.find_exn proj.ctx.functypes name).loc
        | Delegate (Some (name, _)) ->
            Some (Hashtbl.find_exn proj.ctx.delegates name).loc
        | _ -> None)
    | _ -> None)

(* ---- Find references ---- *)

type ref_symbol =
  | RefGlobal of string
  | RefFunction of string
  | RefStructMember of string * string
  | RefStruct of string
  | RefFuncType of string
  | RefDelegate of string
  | RefLocalVar of Jaf.location

let loc_equal (a : Jaf.location) (b : Jaf.location) = Poly.equal a b

let symbol_at_nodes nodes =
  let rec enclosing_struct = function
    | Jaf.ASTDeclaration (Jaf.StructDef s) :: _ -> Some s.name
    | _ :: rest -> enclosing_struct rest
    | [] -> None
  in
  match nodes with
  | Jaf.ASTExpression { node = Ident (_, LocalVariable (_, loc)); _ } :: _ ->
      Some (RefLocalVar loc)
  | Jaf.ASTExpression
      { node = Ident (name, (GlobalVariable _ | GlobalConstant)); _ }
    :: _ ->
      Some (RefGlobal name)
  | Jaf.ASTExpression { node = Ident (_, FunctionName name); _ } :: _
  | Jaf.ASTExpression { node = Member (_, _, ClassMethod (name, _)); _ } :: _
  | Jaf.ASTExpression { node = FuncAddr (name, _); _ } :: _ ->
      Some (RefFunction name)
  | Jaf.ASTExpression
      {
        node = Member ({ ty = Struct (s_name, _); _ }, m_name, ClassVariable _);
        _;
      }
    :: _ ->
      Some (RefStructMember (s_name, m_name))
  | Jaf.ASTExpression { node = MemberAddr (s_name, m_name, _); _ } :: _ ->
      Some (RefStructMember (s_name, m_name))
  | Jaf.ASTType { ty; _ } :: _ -> (
      match jaf_base_type ty with
      | Struct (name, _) -> Some (RefStruct name)
      | FuncType (Some (name, _)) -> Some (RefFuncType name)
      | Delegate (Some (name, _)) -> Some (RefDelegate name)
      | _ -> None)
  | Jaf.ASTStructDecl (Method d | Constructor d | Destructor d) :: _ ->
      Some (RefFunction (Jaf.mangled_name d))
  | Jaf.ASTDeclaration (Function d) :: _ ->
      Some (RefFunction (Jaf.mangled_name d))
  | Jaf.ASTDeclaration (StructDef s) :: _ -> Some (RefStruct s.name)
  | Jaf.ASTDeclaration (FuncTypeDef f) :: _ -> Some (RefFuncType f.name)
  | Jaf.ASTDeclaration (DelegateDef f) :: _ -> Some (RefDelegate f.name)
  | Jaf.ASTVariable v :: rest -> (
      match v.kind with
      | GlobalVar -> Some (RefGlobal v.name)
      | LocalVar | Parameter -> Some (RefLocalVar v.location)
      | ClassVar -> (
          match enclosing_struct rest with
          | Some s_name -> Some (RefStructMember (s_name, v.name))
          | None -> None))
  | _ -> None

(* Walks a subtree (fundecl or toplevel) and collects locations of
   expressions/types/declarations matching [target]. Declaration-site
   matches are emitted only when [include_declaration] is true. *)
class reference_collector ctx target ~include_declaration =
  object (self)
    inherit Jaf.ivisitor ctx as super
    val mutable refs : Jaf.location list = []
    method refs = refs
    method private add loc = refs <- loc :: refs

    method! visit_expression expr =
      (match (expr.node, target) with
      | Ident (_, LocalVariable (_, loc)), RefLocalVar tgt
        when loc_equal loc tgt ->
          self#add expr.loc
      | Ident (name, (GlobalVariable _ | GlobalConstant)), RefGlobal tgt
        when String.equal name tgt ->
          self#add expr.loc
      | Ident (_, FunctionName name), RefFunction tgt when String.equal name tgt
        ->
          self#add expr.loc
      | Member (_, _, ClassMethod (name, _)), RefFunction tgt
        when String.equal name tgt ->
          self#add expr.loc
      | FuncAddr (name, _), RefFunction tgt when String.equal name tgt ->
          self#add expr.loc
      | ( Member ({ ty = Struct (s, _); _ }, m, ClassVariable _),
          RefStructMember (ts, tm) )
        when String.equal s ts && String.equal m tm ->
          self#add expr.loc
      | MemberAddr (s, m, _), RefStructMember (ts, tm)
        when String.equal s ts && String.equal m tm ->
          self#add expr.loc
      | _ -> ());
      super#visit_expression expr

    method! visit_type_specifier ts =
      (match (jaf_base_type ts.ty, target) with
      | Struct (name, _), RefStruct tgt when String.equal name tgt ->
          self#add ts.location
      | FuncType (Some (name, _)), RefFuncType tgt when String.equal name tgt ->
          self#add ts.location
      | Delegate (Some (name, _)), RefDelegate tgt when String.equal name tgt ->
          self#add ts.location
      | _ -> ());
      super#visit_type_specifier ts

    method! visit_variable v =
      (if include_declaration then
         match (v.kind, target) with
         | GlobalVar, RefGlobal tgt when String.equal v.name tgt ->
             self#add v.location
         | (LocalVar | Parameter), RefLocalVar tgt when loc_equal v.location tgt
           ->
             self#add v.location
         | ClassVar, RefStructMember (ts, tm) when String.equal v.name tm -> (
             match self#current_struct_name with
             | Some s when String.equal s ts -> self#add v.location
             | _ -> ())
         | _ -> ());
      super#visit_variable v

    method! visit_fundecl f =
      (if include_declaration then
         match target with
         | RefFunction tgt when String.equal (Jaf.mangled_name f) tgt ->
             self#add f.loc
         | _ -> ());
      super#visit_fundecl f

    method! visit_declaration d =
      (if include_declaration then
         match (d, target) with
         | StructDef s, RefStruct tgt when String.equal s.name tgt ->
             self#add s.loc
         | FuncTypeDef f, RefFuncType tgt when String.equal f.name tgt ->
             self#add f.loc
         | DelegateDef f, RefDelegate tgt when String.equal f.name tgt ->
             self#add f.loc
         | _ -> ());
      super#visit_declaration d
  end

let ensure_fully_resolved proj =
  Hashtbl.iter proj.documents ~f:(fun doc ->
      if not doc.fully_resolved then (
        let saved_errors = doc.errors in
        Document.resolve doc;
        (* Errors from type analysis on files the user hasn't opened should
           not leak into diagnostics. *)
        doc.errors <- saved_errors;
        doc.fully_resolved <- true))

let location_to_lsp proj (loc : Jaf.location) =
  let fname = (fst loc).Lexing.pos_fname in
  match find_document proj fname with
  | None -> None
  | Some doc ->
      let range = to_lsp_range doc.lexbuf.lex_buffer loc in
      let uri = Lsp.Types.DocumentUri.of_path fname in
      Some (Lsp.Types.Location.create ~uri ~range)

(* Find the innermost enclosing fundecl from a node stack returned by
   [get_nodes_for_pos] (innermost-first). *)
let rec enclosing_fundecl_of_nodes = function
  | Jaf.ASTDeclaration (Jaf.Function f) :: _ -> Some f
  | Jaf.ASTStructDecl (Method f | Constructor f | Destructor f) :: _ -> Some f
  | _ :: rest -> enclosing_fundecl_of_nodes rest
  | [] -> None

let get_references proj ~path pos ~include_declaration =
  match find_document proj path with
  | None -> None
  | Some doc ->
      let nodes = get_nodes_for_pos doc pos in
      Option.map (symbol_at_nodes nodes) ~f:(fun target ->
          let locs =
            match target with
            | RefLocalVar _ ->
                let v =
                  new reference_collector proj.ctx target ~include_declaration
                in
                Option.iter
                  (enclosing_fundecl_of_nodes nodes)
                  ~f:v#visit_fundecl;
                v#refs
            | _ ->
                ensure_fully_resolved proj;
                Hashtbl.fold proj.documents ~init:[]
                  ~f:(fun ~key:_ ~data:doc acc ->
                    let v =
                      new reference_collector
                        proj.ctx target ~include_declaration
                    in
                    v#visit_toplevel doc.toplevel;
                    List.rev_append v#refs acc)
          in
          List.filter_map locs ~f:(location_to_lsp proj))

let get_entrypoint proj =
  match location_of_func proj "main" with
  | Some loc -> (
      let fname = (fst loc).Lexing.pos_fname in
      match find_document proj fname with
      | None -> None
      | Some doc ->
          let range = to_lsp_range doc.lexbuf.lex_buffer loc in
          let uri = Lsp.Types.DocumentUri.of_path fname in
          Some (Lsp.Types.Location.create ~uri ~range))
  | None -> None
