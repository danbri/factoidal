(* factoidal-http — a minimal SPARQL 1.1 Protocol HTTP server.

   Pure-OCaml I/O glue around the F*-extracted [SPARQL.Protocol] module.
   The server's job is:
     1. Accept one HTTP/1.1 request at a time (no pipelining, no keep-alive).
     2. Parse the request line + headers + Content-Length body.
     3. Hand (method, path, query, content-type, body) to
        [SPARQL_Protocol.decode_request].
     4. Depending on the PR_Query / PR_Update / PR_Bad result, either run
        the query through the F*-extracted evaluator or respond with an
        error.
     5. Choose a response format from the Accept header and serialise via
        [SPARQL_Protocol.serialise_response_json/_xml/_csv/_tsv] (or the
        _boolean_* variants for ASK).

   What is here is I/O-layer code ONLY. No RDF or SPARQL semantics are
   decided in this file — all of that stays in the verified F* core
   (rule #10 / anti-pattern #15). In particular the request decoding and
   response body are produced by F* functions.

   Stage-1 limitations (deliberate; not all-in-one bugs):
     * UPDATE execution is not wired; PR_Update responds 501.
     * CONSTRUCT/DESCRIBE responses are stubbed — the F* evaluator's
       eval_select_query returns [] for QF_Construct today.
     * Per-request default-graph-uri / named-graph-uri parameters are
       ignored (they would require a remote fetch). The server always
       serves the --dataset that was passed on the command line.
     * Accept wildcard matching ("* /*", "application/*") is not
       explicitly handled beyond what the F* core does — unknown media
       types fall back to RF_Json.
     * No keep-alive, no chunked encoding, no pipelining, no gzip.
     * No TLS.

   Launch:
     factoidal-http -p 3030 --dataset data.ttl
*)

open RDF_Graph_Executable
open SPARQL11_Algebra
module P = SPARQL_Protocol

(* ============================================================================
   RDF file loading — same shape as factoidal_cli, inlined here so we don't
   link factoidal_cli.ml (which has its own [let () = ...] main).
   ============================================================================ *)

type rdf_format = NT | Turtle | NQuads | TriG | RDFXML

let detect_format filename =
  let ext = String.lowercase_ascii (Filename.extension filename) in
  match ext with
  | ".nt" | ".ntriples" -> NT
  | ".ttl" | ".turtle" -> Turtle
  | ".nq" | ".nquads" -> NQuads
  | ".trig" -> TriG
  | ".rdf" | ".xml" | ".rdfxml" | ".owl" -> RDFXML
  | _ -> Turtle

let format_of_string s =
  match String.lowercase_ascii s with
  | "ntriples" | "nt" | "n-triples" -> Some NT
  | "turtle" | "ttl" -> Some Turtle
  | "nquads" | "nq" | "n-quads" -> Some NQuads
  | "trig" -> Some TriG
  | "rdfxml" | "rdf/xml" | "rdf" | "xml" -> Some RDFXML
  | _ -> None

let read_file path =
  let ic = open_in path in
  let n = in_channel_length ic in
  let b = Bytes.create n in
  really_input ic b 0 n;
  close_in ic;
  Bytes.to_string b

let file_base_iri path =
  let abs = if Filename.is_relative path
            then Filename.concat (Sys.getcwd ()) path
            else path in
  "file://" ^ abs

let load_rdf_dataset ?(format=None) ?(base=None) path =
  let content = read_file path in
  let fmt = match format with Some f -> f | None -> detect_format path in
  let base_iri =
    match base with
    | Some _ as b -> b
    | None -> Some (file_base_iri path)
  in
  match fmt with
  | NQuads ->
    Parser_NQuads.parse_nquads content
  | TriG ->
    (match base_iri with
     | Some b -> Parser_TriG.parse_trig_with_base_lenient content b
     | None -> Parser_TriG.parse_trig_lenient content)
  | _ ->
    let triples = match fmt with
      | NT -> Parser_NTriples.parse_ntriples content
      | Turtle ->
        (match base_iri with
         | Some b -> Parser_Turtle.parse_turtle_with_base content b
         | None -> Parser_Turtle.parse_turtle content)
      | RDFXML ->
        (match base_iri with
         | Some b -> Parser_RDFXML.parse_rdfxml_with_base b content
         | None -> Parser_RDFXML.parse_rdfxml content)
      | _ -> [] in
    { ds_default = triples; ds_named = [] }

(* ============================================================================
   Command-line configuration
   ============================================================================ *)

type config = {
  mutable port : int;
  mutable dataset_file : string option;
  mutable input_format : rdf_format option;
  mutable base_iri : string option;
  mutable host : string;
  mutable verbose : bool;
  mutable help_mode : bool;
}

let default_config () = {
  port = 3030;
  dataset_file = None;
  input_format = None;
  base_iri = None;
  host = "127.0.0.1";
  verbose = false;
  help_mode = false;
}

let usage () =
  print_endline "factoidal-http — formally verified SPARQL 1.1 Protocol endpoint";
  print_endline "";
  print_endline "Usage:";
  print_endline "  factoidal-http [-p PORT] [--dataset FILE] [-f FORMAT]";
  print_endline "";
  print_endline "Options:";
  print_endline "  -p, --port PORT        TCP port to listen on (default 3030)";
  print_endline "      --host HOST        Bind address (default 127.0.0.1)";
  print_endline "      --dataset FILE     Seed default graph from an RDF file";
  print_endline "                         (auto-detected: .ttl .nt .nq .trig .rdf)";
  print_endline "  -f, --format FMT       Force input format (turtle|ntriples|nquads|trig|rdfxml)";
  print_endline "  -b, --base IRI         Base IRI for parsing";
  print_endline "  -v, --verbose          Log every request";
  print_endline "  -h, --help             This help";
  print_endline "";
  print_endline "Endpoints:";
  print_endline "  GET  /query?query=...        SPARQL query via URL";
  print_endline "  POST /query  application/sparql-query                  raw body";
  print_endline "  POST /query  application/x-www-form-urlencoded         query=...";
  print_endline "  POST /update                                           (parses + executes; LOAD → 501)";
  print_endline "";
  print_endline "Supported response media types via Accept:";
  print_endline "  application/sparql-results+json  (default)";
  print_endline "  application/sparql-results+xml";
  print_endline "  text/csv";
  print_endline "  text/tab-separated-values";
  print_endline "";
  print_endline "Stage 1 limitations:";
  print_endline "  * Per-request default-graph-uri / named-graph-uri are ignored";
  print_endline "  * UPDATE supports INSERT/DELETE DATA, DELETE WHERE, Modify";
  print_endline "    (INSERT/DELETE WHERE), CLEAR, DROP, CREATE, ADD, MOVE, COPY.";
  print_endline "    LOAD still returns 501 (needs an HTTP client).";
  print_endline "  * UPDATEs mutate a single shared dataset ref for the server's";
  print_endline "    lifetime; not thread-safe, not persisted.";
  print_endline "  * CONSTRUCT/DESCRIBE return empty results (evaluator stub)";
  print_endline "  * No TLS, no keep-alive, no pipelining"

let parse_args () =
  let cfg = default_config () in
  let args = Array.to_list Sys.argv |> List.tl in
  let rec loop = function
    | [] -> ()
    | ("-h" | "--help") :: _ -> cfg.help_mode <- true
    | ("-p" | "--port") :: p :: rest ->
      (match int_of_string_opt p with
       | Some n when n > 0 && n < 65536 -> cfg.port <- n
       | _ -> Printf.eprintf "Error: --port needs 1..65535, got '%s'\n" p; exit 1);
      loop rest
    | "--host" :: h :: rest -> cfg.host <- h; loop rest
    | "--dataset" :: f :: rest -> cfg.dataset_file <- Some f; loop rest
    | ("-f" | "--format") :: fmt :: rest ->
      (match format_of_string fmt with
       | Some f -> cfg.input_format <- Some f
       | None -> Printf.eprintf "Error: unknown format '%s'\n" fmt; exit 1);
      loop rest
    | ("-b" | "--base") :: b :: rest -> cfg.base_iri <- Some b; loop rest
    | ("-v" | "--verbose") :: rest -> cfg.verbose <- true; loop rest
    | arg :: _ ->
      Printf.eprintf "Error: unrecognised argument '%s' (try --help)\n" arg;
      exit 1
  in
  loop args;
  cfg

(* ============================================================================
   Dataset loading — delegates to the loader that factoidal_cli already uses.
   ============================================================================ *)

let load_dataset cfg =
  match cfg.dataset_file with
  | None -> { ds_default = []; ds_named = [] }
  | Some f ->
    try load_rdf_dataset
          ~format:cfg.input_format ~base:cfg.base_iri f
    with e ->
      Printf.eprintf "Error loading dataset %s: %s\n" f (Printexc.to_string e);
      exit 1

(* ============================================================================
   HTTP/1.1 request parsing (line-oriented, blocking reads).

   Shape we accept:
     METHOD SP URI SP HTTP/1.1 CRLF
     Name: value CRLF
     ...
     CRLF
     [body (Content-Length bytes)]

   We read the request-line + headers using buffered line reads, then read
   exactly Content-Length bytes for the body. No chunked transfer.
   ============================================================================ *)

exception Bad_request of string

(* Read one CRLF-terminated line from [ic]. Trailing CRLF is stripped.
   Raises End_of_file if the connection closes mid-line. *)
let read_line_crlf ic =
  let buf = Buffer.create 128 in
  let rec loop prev =
    let c = input_char ic in
    if prev = '\r' && c = '\n' then Buffer.sub buf 0 (Buffer.length buf - 1)
    else begin
      Buffer.add_char buf c;
      loop c
    end
  in
  try loop ' ' with End_of_file ->
    if Buffer.length buf = 0 then raise End_of_file
    else Buffer.contents buf

(* Split an HTTP request line: "GET /path?qs HTTP/1.1". *)
let parse_request_line line =
  let parts = String.split_on_char ' ' line in
  match parts with
  | [meth; uri; version] -> (meth, uri, version)
  | _ -> raise (Bad_request (Printf.sprintf "malformed request line: %s" line))

(* Split a header line "Name: value". Returns (lowercased_name, trimmed_value). *)
let parse_header line =
  match String.index_opt line ':' with
  | None -> None
  | Some i ->
    let name = String.lowercase_ascii (String.trim (String.sub line 0 i)) in
    let value = String.trim (String.sub line (i + 1) (String.length line - i - 1)) in
    Some (name, value)

(* Read headers until the empty line. Returns an assoc list. *)
let read_headers ic =
  let hs = ref [] in
  let rec loop () =
    let line = read_line_crlf ic in
    if line = "" then ()
    else begin
      (match parse_header line with
       | Some kv -> hs := kv :: !hs
       | None -> ());
      loop ()
    end
  in
  loop ();
  List.rev !hs

let header_value headers name =
  let lname = String.lowercase_ascii name in
  try Some (List.assoc lname headers) with Not_found -> None

(* Read exactly [n] bytes from [ic]; short reads are a Bad_request. *)
let read_body ic n =
  if n <= 0 then ""
  else begin
    let b = Bytes.create n in
    let rec loop pos remaining =
      if remaining = 0 then ()
      else
        let got = input ic b pos remaining in
        if got = 0 then raise (Bad_request "body shorter than Content-Length")
        else loop (pos + got) (remaining - got)
    in
    loop 0 n;
    Bytes.unsafe_to_string b
  end

(* Split a URI "/path?query" into (path, qs). *)
let split_uri uri =
  match String.index_opt uri '?' with
  | None -> (uri, "")
  | Some i ->
    (String.sub uri 0 i, String.sub uri (i + 1) (String.length uri - i - 1))

(* ============================================================================
   HTTP response helpers.

   Status-line + common headers (Content-Type, Content-Length, Connection:
   close). Body is a byte-string; we pass it through unmodified.
   ============================================================================ *)

let status_text = function
  | 200 -> "OK"
  | 204 -> "No Content"
  | 400 -> "Bad Request"
  | 404 -> "Not Found"
  | 405 -> "Method Not Allowed"
  | 500 -> "Internal Server Error"
  | 501 -> "Not Implemented"
  | _ -> "Unknown"

let write_response oc ~status ~content_type ~body =
  let text = status_text status in
  let headers =
    Printf.sprintf
      "HTTP/1.1 %d %s\r\nContent-Type: %s\r\nContent-Length: %d\r\nConnection: close\r\n\r\n"
      status text content_type (String.length body)
  in
  output_string oc headers;
  output_string oc body;
  flush oc

let write_plain_error oc ~status msg =
  write_response oc ~status ~content_type:"text/plain; charset=utf-8"
    ~body:(msg ^ "\n")

(* ============================================================================
   SELECT / ASK / CONSTRUCT dispatch.

   All of the semantic work lives in SPARQL11_Algebra (verified Fstar code).
   We only choose which evaluator entry point to call and which Fstar
   serialiser to wrap the result in.
   ============================================================================ *)

(* What the final response looks like. *)
type response_body = {
  rb_status : int;
  rb_content_type : string;
  rb_body : string;
}

let response_format_of_accept accept =
  let entries = P.parse_accept_header accept in
  P.pick_response_format entries P.RF_Json

(* Extract variable list from a SELECT query (same shape as factoidal_cli). *)
let select_vars query results =
  match query.q_form with
  | QF_Select (Select_Vars items) ->
    List.map (fun item -> match item with
      | SI_Var v -> v
      | SI_Expr (_, v) -> v) items
  | _ ->
    (* Star projection — collect from actual result rows, keep first-seen order. *)
    let seen = Hashtbl.create 16 in
    let acc = ref [] in
    List.iter (fun row ->
      List.iter (fun (v, _) ->
        if not (Hashtbl.mem seen v) then begin
          Hashtbl.add seen v ();
          acc := v :: !acc
        end) row
    ) results;
    List.rev !acc

(* Run the query and produce a response_body.
   F* evaluator does the work; we just pick serialiser + content type. *)
let run_query ~dataset ~accept query =
  let graph = dataset.ds_default in
  match query.q_form with
  | QF_Ask ->
    let b = eval_ask_query query graph dataset in
    let fmt = response_format_of_accept accept in
    (* For ASK, only JSON and XML have dedicated boolean serialisers;
       other formats fall back to JSON. *)
    let (ct, body) = match fmt with
      | P.RF_Xml -> (P.content_type_for P.RF_Xml,
                     P.serialise_response_boolean_xml b)
      | _        -> (P.content_type_for P.RF_Json,
                     P.serialise_response_boolean_json b)
    in
    { rb_status = 200; rb_content_type = ct; rb_body = body }
  | QF_Select _ ->
    let rows = eval_select_query query graph dataset in
    let vars = select_vars query rows in
    let fmt = response_format_of_accept accept in
    let (ct, body) = match fmt with
      | P.RF_Xml -> (P.content_type_for P.RF_Xml,
                     P.serialise_response_xml vars rows)
      | P.RF_Csv -> (P.content_type_for P.RF_Csv,
                     P.serialise_response_csv vars rows)
      | P.RF_Tsv -> (P.content_type_for P.RF_Tsv,
                     P.serialise_response_tsv vars rows)
      | _        -> (P.content_type_for P.RF_Json,
                     P.serialise_response_json vars rows)
    in
    { rb_status = 200; rb_content_type = ct; rb_body = body }
  | QF_Construct _ | QF_Describe _ ->
    (* CONSTRUCT / DESCRIBE: the F* evaluator returns [] for these today
       (SPARQL11.Algebra.fst's eval_select_query has stub arms for
       QF_Construct / QF_Describe). We surface that as an empty result
       in the caller's preferred results format so at least the protocol
       round-trips cleanly. Serialising real triples in Turtle is a
       future-stage deliverable. *)
    let rows = eval_select_query query graph dataset in
    let fmt = response_format_of_accept accept in
    let vars = select_vars query rows in
    let (ct, body) = match fmt with
      | P.RF_Xml -> (P.content_type_for P.RF_Xml,
                     P.serialise_response_xml vars rows)
      | _        -> (P.content_type_for P.RF_Json,
                     P.serialise_response_json vars rows)
    in
    { rb_status = 200; rb_content_type = ct; rb_body = body }

let parse_and_run ~dataset ~accept query_text =
  match SPARQL11_Parser.parse_sparql query_text with
  | SPARQL11_Parser.ParseErr msg ->
    { rb_status = 400;
      rb_content_type = "text/plain; charset=utf-8";
      rb_body = "SPARQL parse error: " ^ msg ^ "\n" }
  | SPARQL11_Parser.ParseOk (query, _tokens) ->
    (try run_query ~dataset ~accept query
     with e ->
       { rb_status = 500;
         rb_content_type = "text/plain; charset=utf-8";
         rb_body = "Query evaluation error: " ^ Printexc.to_string e ^ "\n" })

(* ============================================================================
   Per-connection handling.

   Each connection reads exactly one HTTP request, answers it, then closes.
   Socket errors are logged but never crash the accept loop.
   ============================================================================ *)

(* Detect whether an update contains any U_Load op (LOAD is still
   unimplemented — needs HTTP client).  We return 501 for requests
   that contain LOAD rather than silently skipping it. *)
let update_has_load (u : SPARQL11_Algebra.sparql_update) : bool =
  List.exists (fun op ->
    match op with
    | SPARQL11_Algebra.U_Load (_, _, _) -> true
    | _ -> false
  ) u.u_ops

let handle_connection cfg dataset_ref ic oc =
  try
    let req_line = read_line_crlf ic in
    let (meth, uri, _version) = parse_request_line req_line in
    let headers = read_headers ic in
    let content_length =
      match header_value headers "content-length" with
      | Some s -> (try int_of_string (String.trim s) with _ -> 0)
      | None -> 0
    in
    let body = read_body ic content_length in
    let (path, qs) = split_uri uri in
    let ct = match header_value headers "content-type" with
             | Some v -> v | None -> "" in
    let accept = match header_value headers "accept" with
                 | Some v -> v | None -> "" in
    if cfg.verbose then
      Printf.eprintf "[%s] %s %s (body=%d, accept=%s, ct=%s)\n%!"
        (let t = Unix.localtime (Unix.time ()) in
         Printf.sprintf "%04d-%02d-%02d %02d:%02d:%02d"
           (t.tm_year + 1900) (t.tm_mon + 1) t.tm_mday
           t.tm_hour t.tm_min t.tm_sec)
        meth uri (String.length body) accept ct;

    let dataset = !dataset_ref in
    let resp =
      match P.decode_request meth path qs ct body with
      | P.PR_Bad msg ->
        { rb_status = 400;
          rb_content_type = "text/plain; charset=utf-8";
          rb_body = msg ^ "\n" }
      | P.PR_Update (update_text, _dflt, _named) ->
        (* Parse the update string and dispatch through apply_update.
           LOAD is still unimplemented (needs an HTTP client). *)
        (match SPARQL11_Parser.parse_sparql_update update_text with
         | SPARQL11_Parser.ParseErr msg ->
           { rb_status = 400;
             rb_content_type = "text/plain; charset=utf-8";
             rb_body = "SPARQL Update parse error: " ^ msg ^ "\n" }
         | SPARQL11_Parser.ParseOk (u, _rest) ->
           if update_has_load u then
             { rb_status = 501;
               rb_content_type = "text/plain; charset=utf-8";
               rb_body =
                 "SPARQL UPDATE with LOAD is not yet implemented.\n\
                  LOAD requires an HTTP client, which factoidal-http\n\
                  does not yet embed.\n" }
           else begin
             let new_ds =
               try SPARQL11_Algebra.apply_update dataset u
               with e ->
                 Printf.eprintf "  update execution error: %s\n%!"
                   (Printexc.to_string e);
                 dataset
             in
             dataset_ref := new_ds;
             { rb_status = 204;
               rb_content_type = "text/plain; charset=utf-8";
               rb_body = "" }
           end)
      | P.PR_Query (q, _dflt, _named) ->
        (* Stage 1: ignore default-graph-uri / named-graph-uri (would
           require HTTP fetch to honour). The dataset preloaded via
           --dataset is served as the default graph; UPDATE ops
           accumulated via POST /update mutate the shared ref. *)
        parse_and_run ~dataset ~accept q
    in
    write_response oc
      ~status:resp.rb_status
      ~content_type:resp.rb_content_type
      ~body:resp.rb_body
  with
  | Bad_request msg ->
    (try write_plain_error oc ~status:400 ("Bad request: " ^ msg)
     with _ -> ())
  | End_of_file ->
    (* Client closed before sending anything — benign. *)
    ()
  | e ->
    Printf.eprintf "  connection error: %s\n%!" (Printexc.to_string e);
    (try write_plain_error oc ~status:500 "Internal server error"
     with _ -> ())

(* ============================================================================
   Accept loop.

   Single-threaded for simplicity. One request at a time. This is fine for
   the W3C Protocol harness and for smoke testing; a production deployment
   would want Lwt / Unix.fork per connection.
   ============================================================================ *)

let resolve_host h =
  try (Unix.gethostbyname h).h_addr_list.(0)
  with Not_found ->
    Printf.eprintf "Error: cannot resolve host '%s'\n" h;
    exit 1

let run_server cfg =
  let dataset_ref = ref (load_dataset cfg) in
  let addr = Unix.ADDR_INET (resolve_host cfg.host, cfg.port) in
  let sock = Unix.socket Unix.PF_INET Unix.SOCK_STREAM 0 in
  (try Unix.setsockopt sock Unix.SO_REUSEADDR true with _ -> ());
  (try Unix.bind sock addr
   with Unix.Unix_error (err, _, _) ->
     Printf.eprintf "Error: cannot bind %s:%d — %s\n"
       cfg.host cfg.port (Unix.error_message err);
     exit 1);
  Unix.listen sock 16;
  let triple_count = List.length (!dataset_ref).ds_default in
  Printf.printf "factoidal-http listening on http://%s:%d/query\n"
    cfg.host cfg.port;
  (match cfg.dataset_file with
   | Some f -> Printf.printf "  default graph: %s (%d triples)\n" f triple_count
   | None -> Printf.printf "  default graph: <empty>\n");
  Printf.printf "  try: curl -H 'Accept: application/sparql-results+json' \\\n";
  Printf.printf "         'http://%s:%d/query?query=SELECT%%20*%%20WHERE%%20%%7B%%3Fs%%20%%3Fp%%20%%3Fo%%7D'\n"
    cfg.host cfg.port;
  flush stdout;
  (* Ignore SIGPIPE so a client closing early doesn't kill the server. *)
  (try Sys.set_signal Sys.sigpipe Sys.Signal_ignore with _ -> ());
  while true do
    match (try Some (Unix.accept sock) with
           | Unix.Unix_error (err, _, _) ->
             Printf.eprintf "  accept() failed: %s\n%!" (Unix.error_message err);
             None) with
    | None -> ()
    | Some (client, _caddr) ->
      let ic = Unix.in_channel_of_descr client in
      let oc = Unix.out_channel_of_descr client in
      (try handle_connection cfg dataset_ref ic oc
       with e ->
         Printf.eprintf "  unhandled: %s\n%!" (Printexc.to_string e));
      (try close_out oc with _ -> ());
      (try Unix.close client with _ -> ())
  done

let () =
  let cfg = parse_args () in
  if cfg.help_mode then (usage (); exit 0);
  run_server cfg
