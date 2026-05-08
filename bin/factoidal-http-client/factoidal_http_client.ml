(* factoidal_http_client — minimal HTTP/1.1 client I/O glue.

   Pure-OCaml I/O glue around the F*-extracted [SPARQL.HTTP.Client] module
   (a.k.a. [SPARQL_HTTP_Client]). The glue's sole job is:

     1. Open a TCP connection to (host, port).
     2. Write the request bytes produced by
        [SPARQL_HTTP_Client.format_request] to the socket.
     3. Read the response into a buffer until EOF (or until we've
        satisfied the Content-Length, if honouring that is wired in
        later phases).
     4. Hand the buffer back to [SPARQL_HTTP_Client.parse_http_response].

   Rules honoured:

     * CLAUDE.md rule #10 / anti-pattern #15: zero RDF/SPARQL semantics
       live here. No decisions about SPARQL protocol shape — that is all
       in F*. This file is sockets only.
     * CLAUDE.md rule #13: this file is *hand-authored*, not produced
       by extraction, so the "never edit extracted .ml" rule doesn't
       apply. It is a sibling of factoidal_http.ml (the server glue).

   Phase 0 limitations (deliberate):
     * HTTP/1.1 only, no HTTPS / TLS.
     * No chunked transfer encoding (honours Content-Length, otherwise
       reads until EOF).
     * No keep-alive: one request per connection.
     * No redirect following.
     * No timeout on socket reads (the main thread rebuild will likely
       want SO_RCVTIMEO; parked until we wire this into GP_Service).
     * IPv4 + IPv6 via Unix.getaddrinfo; first address wins.

   Smoke test: set FACTOIDAL_HTTP_CLIENT_SMOKE=1 in the environment and
   launch any binary that links this module; it will attempt a GET of
   http://example.org/ and print the response status + a short prefix
   of the body. Normal builds do not phone home.
*)

(* The F* module name extracts to [SPARQL_HTTP_Client] (see
   ocaml-output/SPARQL_HTTP_Client.ml after extraction). We keep the
   [module C] alias so changes in extraction naming land in one place. *)
module C = SPARQL_HTTP_Client

(* ========================================================================
   Socket I/O primitives.
   ======================================================================== *)

(* Resolve a host name + port to the first usable [sockaddr]. Raises
   [Failure] if nothing resolves. *)
let resolve_host ~host ~port : Unix.sockaddr =
  let opts = [ Unix.AI_SOCKTYPE Unix.SOCK_STREAM ] in
  match Unix.getaddrinfo host (string_of_int port) opts with
  | [] -> failwith (Printf.sprintf "factoidal_http_client: cannot resolve %s:%d" host port)
  | ai :: _ -> ai.Unix.ai_addr

(* Open a TCP connection; caller is responsible for [Unix.close]. *)
let socket_connect ~host ~port : Unix.file_descr =
  let addr = resolve_host ~host ~port in
  let domain =
    match addr with
    | Unix.ADDR_INET (ip, _) ->
      if Unix.is_inet6_addr ip then Unix.PF_INET6 else Unix.PF_INET
    | Unix.ADDR_UNIX _ -> Unix.PF_UNIX
  in
  let fd = Unix.socket domain Unix.SOCK_STREAM 0 in
  (try Unix.connect fd addr
   with e -> (try Unix.close fd with _ -> ()); raise e);
  fd

(* Write the entire buffer, coping with partial writes. *)
let send_all (fd : Unix.file_descr) (buf : string) : unit =
  let total = String.length buf in
  let written = ref 0 in
  while !written < total do
    let n = Unix.write_substring fd buf !written (total - !written) in
    if n = 0 then failwith "factoidal_http_client: write returned 0";
    written := !written + n
  done

(* Read until EOF. Returns everything the peer sent as a single string.
   Phase 0: we don't try to honour Content-Length on the read side — the
   F* response parser will clamp the body to whatever Content-Length says.
   Keep-alive support will need this to read exactly headers + body. *)
let read_until_eof (fd : Unix.file_descr) : string =
  let buf = Buffer.create 4096 in
  let chunk = Bytes.create 4096 in
  let rec loop () =
    let n = Unix.read fd chunk 0 (Bytes.length chunk) in
    if n = 0 then ()
    else begin
      Buffer.add_subbytes buf chunk 0 n;
      loop ()
    end
  in
  loop ();
  Buffer.contents buf

(* End-to-end: connect, write request bytes, read response bytes, close. *)
let perform_request ~host ~port ~(req_bytes : string) : string =
  let fd = socket_connect ~host ~port in
  let finish () = try Unix.close fd with _ -> () in
  (try
    send_all fd req_bytes;
    (* Half-close the write side so the peer knows we're done sending. Some
       HTTP/1.0 servers (and many echo servers) wait for EOF on the request
       before sending a response. Safe for HTTP/1.1 GET/POST without body
       follow-up. *)
    (try Unix.shutdown fd Unix.SHUTDOWN_SEND with _ -> ());
    let resp = read_until_eof fd in
    finish ();
    resp
  with e ->
    finish ();
    raise e)


(* ========================================================================
   Optional smoke test — guarded by FACTOIDAL_HTTP_CLIENT_SMOKE=1.
   ======================================================================== *)

(* Build a GET request for (host, path) using the F*-extracted formatter. *)
let build_get_request ~host ~path : string =
  let req = {
    C.rm_method    = "GET";
    C.rm_path      = path;
    C.rm_query_str = "";
    C.rm_version   = "HTTP/1.1";
    C.rm_host      = host;
    C.rm_headers   = [
      ("Accept", "*/*");
      ("User-Agent", "factoidal-http-client/0.1 (+phase0)");
      ("Connection", "close");
    ];
    C.rm_body      = "";
  } in
  C.format_request req

let smoke_test () : unit =
  let host = match Sys.getenv_opt "FACTOIDAL_HTTP_CLIENT_SMOKE_HOST" with
    | Some s when s <> "" -> s
    | _ -> "example.org"
  in
  let port = match Sys.getenv_opt "FACTOIDAL_HTTP_CLIENT_SMOKE_PORT" with
    | Some s -> (try int_of_string s with _ -> 80)
    | None -> 80
  in
  let path = match Sys.getenv_opt "FACTOIDAL_HTTP_CLIENT_SMOKE_PATH" with
    | Some s when s <> "" -> s
    | _ -> "/"
  in
  Printf.eprintf "[factoidal_http_client smoke] GET http://%s:%d%s\n%!" host port path;
  let req = build_get_request ~host ~path in
  let resp = perform_request ~host ~port ~req_bytes:req in
  Printf.eprintf "[factoidal_http_client smoke] got %d bytes\n%!" (String.length resp);
  match C.parse_http_response resp (Z.of_int 16384) (Z.of_int (16 * 1024 * 1024)) with
  | FStar_Pervasives.Inl r ->
    let status = Z.to_int r.C.rsp_status in
    let body = r.C.rsp_body in
    let body_preview =
      if String.length body > 120 then String.sub body 0 120 ^ "..." else body
    in
    Printf.eprintf "[factoidal_http_client smoke] status=%d reason=%s\n%!"
      status r.C.rsp_reason;
    Printf.eprintf "[factoidal_http_client smoke] body_preview=%s\n%!" body_preview
  | FStar_Pervasives.Inr _ ->
    Printf.eprintf "[factoidal_http_client smoke] parse error\n%!"

(* Auto-run the smoke test at module init time when the env var is set.
   This means any binary that links factoidal_http_client.ml will
   exercise the round-trip. Production builds don't set the var. *)
let () =
  match Sys.getenv_opt "FACTOIDAL_HTTP_CLIENT_SMOKE" with
  | Some "1" ->
    (try smoke_test ()
     with e ->
       Printf.eprintf "[factoidal_http_client smoke] exception: %s\n%!"
         (Printexc.to_string e))
  | _ -> ()
