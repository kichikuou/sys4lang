open Base
open Cmdliner
open System4_lsp
open Types
open Project
module Lsp = Linol_lsp.Lsp

let show_error notify_back message =
  let params =
    Lsp.Types.ShowMessageParams.create ~type_:Lsp.Types.MessageType.Error
      ~message
  in
  notify_back#send_notification (Lsp.Server_notification.ShowMessage params)

let show_exn notify_back e =
  let msg = Stdlib.Printexc.to_string e in
  Eio.Fiber.all
    [
      (fun () -> show_error notify_back msg);
      (* Also notify the backtrace with logMessage. *)
      (fun () ->
        notify_back#send_log_msg ~type_:Lsp.Types.MessageType.Error
          (msg ^ "\n" ^ Backtrace.to_string (Backtrace.Exn.most_recent ())));
    ]

(* The default exception printer escapes utf-8 sequences. Try to prevent that
   from happening as much as possible. *)
let () =
  Stdlib.Printexc.register_printer (function
    | Sys_error msg -> Some msg
    | _ -> None)

class lsp_server ~sw ~fs ~domain_mgr ~default_pje_path =
  object (self)
    inherit Linol_eio.Jsonrpc2.server as super

    val project =
      Project.create ~read_file:(fun path ->
          if String.equal Sys.os_type "Win32" then
            (* Workaround for Eio.Path not handling absolute paths correctly on Windows.
               See https://github.com/ocaml-multicore/eio/issues/762 *)
            Eio.Domain_manager.run domain_mgr (fun () ->
                Stdio.In_channel.read_all path)
          else Eio.Path.(load (fs / path)))

    val initial_scan_done = Eio.Promise.create ()
    method spawn_query_handler f = Linol_eio.spawn ~sw f

    method private _on_doc ~(notify_back : Linol_eio.Jsonrpc2.notify_back)
        (uri : Lsp.Types.DocumentUri.t) (contents : string) =
      try
        Eio.Promise.await (fst initial_scan_done);
        let path = Lsp.Types.DocumentUri.to_path uri in
        let diagnostics = update_document project ~path contents in
        notify_back#send_diagnostic diagnostics
      with e -> show_exn notify_back e

    (* Do not use incremental update, to work around a bug in lsp 1.14 where its
       content change application logic is confused when the newline code is CRLF. *)
    method! config_sync_opts =
      {
        (super#config_sync_opts) with
        change = Some Lsp.Types.TextDocumentSyncKind.Full;
      }

    method! config_modify_capabilities c =
      {
        c with
        typeDefinitionProvider = Some (`Bool true);
        referencesProvider = Some (`Bool true);
        signatureHelpProvider =
          Some
            (Lsp.Types.SignatureHelpOptions.create
               ~triggerCharacters:[ "("; "," ] ~retriggerCharacters:[ ")" ] ());
      }

    method! config_completion =
      Some
        (Lsp.Types.CompletionOptions.create ~triggerCharacters:[ "." ]
           ~resolveProvider:false ())

    method! on_req_completion ~notify_back:_ ~id:_ ~uri ~pos ~ctx:_
        ~workDoneToken:_ ~partialResultToken:_ _doc =
      let path = Lsp.Types.DocumentUri.to_path uri in
      get_completion project ~path pos

    method! on_request_unhandled : type r.
        notify_back:Linol_eio.Jsonrpc2.notify_back ->
        id:Linol_eio.Jsonrpc2.Req_id.t ->
        r Lsp.Client_request.t ->
        r Linol_eio.t =
      fun ~notify_back ~id -> function
        | Lsp.Client_request.TextDocumentTypeDefinition
            { textDocument; position; _ } ->
            let path = Lsp.Types.DocumentUri.to_path textDocument.uri in
            get_type_definition project ~path position
        | Lsp.Client_request.TextDocumentReferences
            { textDocument; position; context; _ } ->
            let path = Lsp.Types.DocumentUri.to_path textDocument.uri in
            get_references project ~path position
              ~include_declaration:context.includeDeclaration
        | Lsp.Client_request.SignatureHelp { textDocument; position; _ } ->
            let path = Lsp.Types.DocumentUri.to_path textDocument.uri in
            (* The LSP `SignatureHelp` response is non-optional in
               lsp-ocaml; we use an empty signatures list to mean
               "no help". *)
            Option.value
              (get_signature_help project ~path position)
              ~default:(Lsp.Types.SignatureHelp.create ~signatures:[] ())
        | r -> super#on_request_unhandled ~notify_back ~id r

    method! on_req_initialize ~notify_back i =
      let options =
        InitializationOptions.t_of_yojson
          (Option.value i.initializationOptions ~default:(`Assoc []))
      in
      (* Fall back to the pje path given on the command line when the client
         did not specify one via initializationOptions. *)
      let options =
        if String.is_empty options.pjePath then
          { options with pjePath = default_pje_path }
        else options
      in
      (try
         Project.initialize project options;
         Eio.Fiber.fork ~sw (fun () ->
             (try Project.initial_scan project
              with e -> show_exn notify_back e);
             Eio.Promise.resolve (snd initial_scan_done) ());
         notify_back#send_log_msg ~type_:Lsp.Types.MessageType.Info
           (options.pjePath ^ " loaded")
       with e -> show_exn notify_back e);
      super#on_req_initialize ~notify_back i

    method on_notif_doc_did_open ~notify_back d ~content =
      self#_on_doc ~notify_back d.uri content

    method on_notif_doc_did_change ~notify_back d _c ~old_content:_old
        ~new_content =
      self#_on_doc ~notify_back d.uri new_content

    method on_notif_doc_did_close ~notify_back:_ _ = ()
    method! config_hover = Some (`Bool true)

    method! on_req_hover ~notify_back:_ ~id:_ ~uri ~pos ~workDoneToken:_ _ =
      let path = Lsp.Types.DocumentUri.to_path uri in
      get_hover project ~path pos

    method! config_definition = Some (`Bool true)

    method! on_req_definition ~notify_back:_ ~id:_ ~uri ~pos ~workDoneToken:_
        ~partialResultToken:_ _ =
      let path = Lsp.Types.DocumentUri.to_path uri in
      get_definition project ~path pos

    method! on_unknown_request ~notify_back ~server_request ~id meth params =
      if String.equal meth "system4/entryPoint" then
        match get_entrypoint project with
        | Some loc -> Lsp.Types.Location.yojson_of_t loc
        | None -> `Null
      else super#on_unknown_request ~notify_back ~server_request ~id meth params
  end

let run default_pje_path =
  let default_pje_path = Option.value default_pje_path ~default:"" in
  Common.TypeAnalysis.loose_functype_check := true;
  Eio_main.run @@ fun env ->
  Eio.Switch.run @@ fun sw ->
  let fs = Eio.Stdenv.fs env in
  let domain_mgr = Eio.Stdenv.domain_mgr env in
  let s = new lsp_server ~sw ~fs ~domain_mgr ~default_pje_path in
  let server = Linol_eio.Jsonrpc2.create_stdio ~env s in
  let task () =
    let shutdown () = Poly.(s#get_status = `ReceivedExit) in
    Linol_eio.Jsonrpc2.run ~shutdown server
  in
  match task () with
  | () -> ()
  | exception e ->
      let e = Stdlib.Printexc.to_string e in
      Stdio.eprintf "error: %s\n%!" e;
      Stdlib.exit 1

let cmd =
  let version =
    Option.map (Build_info.V1.version ()) ~f:Build_info.V1.Version.to_string
  in
  let doc = "Language server for the System 4 language" in
  let man =
    [
      `S Manpage.s_description;
      `P
        "sys4lsp is a Language Server Protocol server for the AliceSoft's \
         System 4 programming language. It is normally launched by an LSP \
         client (such as an editor), which configures the project via the \
         $(b,initializationOptions) field of the $(b,initialize) request.";
      `S "INITIALIZATION OPTIONS";
      `P
        "The client may pass the following fields in the \
         $(b,initializationOptions) object of the $(b,initialize) request:";
      `I
        ( "$(b,pjePath)",
          "Path to the .pje project file to load. When omitted, the \
           $(i,PJE_FILE) command-line argument is used instead." );
    ]
  in
  let info = Cmd.info "sys4lsp" ?version ~doc ~man in
  let pje_file =
    let doc =
      "The .pje project file to load. Used as a fallback when the client does \
       not specify pjePath via initializationOptions."
    in
    let docv = "PJE_FILE" in
    Cmdliner.Arg.(value & pos 0 (some string) None & info [] ~docv ~doc)
  in
  Cmd.v info Term.(const run $ pje_file)

let () = Stdlib.exit (Cmd.eval cmd)
