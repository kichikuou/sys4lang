open Base
open System4_lsp
open Types
open Project

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

class lsp_server ~sw ~fs =
  object (self)
    inherit Linol_eio.Jsonrpc2.server as super

    val project =
      Project.create ~read_file:(fun path -> Eio.Path.(load (fs / path)))

    val initial_scan_done = Eio.Promise.create ()
    method spawn_query_handler f = Linol_eio.spawn f

    method private _on_doc ~(notify_back : Linol_eio.Jsonrpc2.notify_back)
        (uri : Lsp.Types.DocumentUri.t) (contents : string) =
      try
        Eio.Promise.await (fst initial_scan_done);
        let diagnostics = update_document project uri contents in
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
      { c with typeDefinitionProvider = Some (`Bool true) }

    method! on_request_unhandled : type r.
        notify_back:Linol_eio.Jsonrpc2.notify_back ->
        id:Linol_eio.Jsonrpc2.Req_id.t ->
        r Lsp.Client_request.t ->
        r Linol_eio.t =
      fun ~notify_back ~id -> function
        | Lsp.Client_request.TextDocumentTypeDefinition
            { textDocument; position; _ } ->
            get_type_definition project textDocument.uri position
        | r -> super#on_request_unhandled ~notify_back ~id r

    method! on_req_initialize ~notify_back i =
      let options =
        InitializationOptions.t_of_yojson
          (Option.value i.initializationOptions ~default:(`Assoc []))
      in
      (try
         Project.initialize project options;
         Eio.Fiber.fork ~sw (fun () ->
             Project.initial_scan project;
             Eio.Promise.resolve (snd initial_scan_done) ());
         notify_back#send_log_msg ~type_:Lsp.Types.MessageType.Info
           (options.ainPath ^ " loaded")
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
      get_hover project uri pos

    method! config_definition = Some (`Bool true)

    method! on_req_definition ~notify_back:_ ~id:_ ~uri ~pos ~workDoneToken:_
        ~partialResultToken:_ _ =
      get_definition project uri pos

    method! on_unknown_request ~notify_back ~server_request ~id meth params =
      if String.equal meth "system4/entryPoint" then
        match get_entrypoint project with
        | Some loc -> Lsp.Types.Location.yojson_of_t loc
        | None -> `Null
      else super#on_unknown_request ~notify_back ~server_request ~id meth params
  end

let run () =
  Common.TypeAnalysis.loose_functype_check := true;
  Eio_main.run @@ fun env ->
  Eio.Switch.run @@ fun sw ->
  let fs = Eio.Stdenv.fs env in
  let s = new lsp_server ~sw ~fs in
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

let print_version () =
  Stdio.printf "system4-lsp %s\n"
    (match Build_info.V1.version () with
    | None -> "n/a"
    | Some v -> Build_info.V1.Version.to_string v)

let () =
  let argv = Sys.get_argv () in
  if Array.length argv = 2 && String.equal argv.(1) "--version" then
    print_version ()
  else run ()
