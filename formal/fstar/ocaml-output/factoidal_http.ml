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

(* CORS policy — how the server should respond to cross-origin browser
   requests. [CORS_Off] is the default and emits no CORS headers at all, so
   browsers block cross-origin calls (matches historical behaviour).
   [CORS_Any] echoes "Access-Control-Allow-Origin: *" on every response and
   is convenient but defeats the browser's same-origin CSRF protection, so
   we warn at startup if combined with write access.
   [CORS_List origins] echoes the requesting Origin back only if it appears
   in the allowlist, and adds "Vary: Origin". *)
type cors_policy =
  | CORS_Off
  | CORS_Any
  | CORS_List of string list

type config = {
  mutable port : int;
  mutable dataset_file : string option;
  mutable input_format : rdf_format option;
  mutable base_iri : string option;
  mutable host : string;
  mutable verbose : bool;
  mutable help_mode : bool;
  mutable read_only : bool;
  mutable cors : cors_policy;
  (* Trusted-header auth: name of the HTTP header whose value is treated
     as the authenticated identity. Safe only when the server is bound to
     loopback and reached solely via a proxy/tunnel that sets this header
     (e.g. Cloudflare Access -> cloudflared -> 127.0.0.1). *)
  mutable auth_header : string;
  (* When Some template, UPDATE is gated on the auth-header being set AND
     all ops being restricted to the graph GR_Graph USERGRAPH where
     USERGRAPH is the template with "{authid}" replaced by the header value.
     Template MUST contain "{authid}". *)
  mutable proxied_auth_rw_graphnames : string option;
  (* Dump every named graph whose IRI starts with the template prefix (i.e.
     user-writable graphs) to N-Quads on SIGTERM/SIGINT. None = off. Some
     is the target directory. *)
  mutable dump_rw_graphs_on_exit : string option;
  (* Load named graphs from this N-Quads file on startup (after --dataset). *)
  mutable load_rw_graphs : string option;
}

let default_dump_dir =
  "./tmp/autoexec.bot-llms_exclude-keep_out_this_is_not_a_place_of_honour/"

let default_config () = {
  port = 3030;
  dataset_file = None;
  input_format = None;
  base_iri = None;
  host = "127.0.0.1";
  verbose = false;
  help_mode = false;
  read_only = false;
  cors = CORS_Off;
  auth_header = "Cf-Access-Authenticated-User-Email";
  proxied_auth_rw_graphnames = None;
  dump_rw_graphs_on_exit = None;
  load_rw_graphs = None;
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
  print_endline "      --read-only        Reject POST /update with 403 Forbidden";
  print_endline "                         (safe for public tunnels)";
  print_endline "      --cors=ORIGINS     Enable CORS. ORIGINS is either \"*\" (allow any";
  print_endline "                         origin) or a comma-separated allowlist of exact";
  print_endline "                         origin strings (e.g. https://foo.example,https://bar.example).";
  print_endline "                         Absent = no CORS headers (cross-origin browser calls";
  print_endline "                         blocked by default). WARNING: --cors=* combined with";
  print_endline "                         write access lets any browser page POST /update —";
  print_endline "                         pair with --read-only or use an allowlist.";
  print_endline "      --auth-header=NAME";
  print_endline "                         HTTP header whose value is the authenticated";
  print_endline "                         identity (default: Cf-Access-Authenticated-User-Email).";
  print_endline "                         TRUSTED-HEADER MODE: only trustworthy when the";
  print_endline "                         server is bound to 127.0.0.1 and reached solely";
  print_endline "                         via an auth-enforcing tunnel/proxy. JWT signature";
  print_endline "                         verification is not yet implemented.";
  print_endline "      --proxied-auth-rw-graphnames=TEMPLATE";
  print_endline "                         Per-user UPDATE sandboxing. TEMPLATE must contain";
  print_endline "                         {authid}. Each authenticated user may only write";
  print_endline "                         into the single named graph whose IRI is the";
  print_endline "                         template with {authid} substituted. Unauthenticated";
  print_endline "                         requests are rejected with 403. If combined with";
  print_endline "                         --read-only, read-only wins (and a warning is printed).";
  print_endline "      --dump-rw-graphs-on-exit[=DIR]";
  print_endline "                         On SIGTERM/SIGINT write every user-writable named";
  print_endline "                         graph to an N-Quads file in DIR";
  print_endline "                         (default: ./tmp/autoexec.bot-.../).";
  print_endline "                         A README.md with a \"please don't crawl or train on";
  print_endline "                         this\" notice is written alongside.";
  print_endline "      --load-rw-graphs=FILE.nq";
  print_endline "                         After loading --dataset, also parse FILE.nq and";
  print_endline "                         add its named graphs to the dataset (counterpart";
  print_endline "                         to --dump-rw-graphs-on-exit).";
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
  print_endline "  * No TLS, no keep-alive, no pipelining";
  print_endline "  * --read-only gates POST /update with 403; useful when";
  print_endline "    exposing the server behind a public tunnel."

(* Parse the value of --cors=VAL into a cors_policy.
   "*" -> CORS_Any; otherwise split on commas and trim whitespace. An empty
   list (e.g. --cors= with nothing after) falls back to CORS_Off so the flag
   is effectively a no-op rather than rejecting every origin silently. *)
let parse_cors_value (v : string) : cors_policy =
  let v = String.trim v in
  if v = "*" then CORS_Any
  else begin
    let parts =
      String.split_on_char ',' v
      |> List.map String.trim
      |> List.filter (fun s -> s <> "")
    in
    match parts with
    | [] -> CORS_Off
    | _  -> CORS_List parts
  end

(* Human-readable description of the CORS mode, for the startup log. *)
let cors_mode_to_string = function
  | CORS_Off -> "off (no Access-Control-* headers)"
  | CORS_Any -> "any origin (Access-Control-Allow-Origin: *)"
  | CORS_List origins ->
    Printf.sprintf "allowlist (%s)" (String.concat ", " origins)

(* Split "--key=value" into ("--key", Some "value"); otherwise (arg, None). *)
let split_eq arg =
  match String.index_opt arg '=' with
  | None -> (arg, None)
  | Some i ->
    (String.sub arg 0 i,
     Some (String.sub arg (i + 1) (String.length arg - i - 1)))

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
    | "--read-only" :: rest -> cfg.read_only <- true; loop rest
    | ("-v" | "--verbose") :: rest -> cfg.verbose <- true; loop rest
    | arg :: rest ->
      let (key, eq_val) = split_eq arg in
      (match (key, eq_val, rest) with
       | ("--cors", Some v, _) ->
         cfg.cors <- parse_cors_value v; loop rest
       | ("--cors", None, v :: rest') ->
         cfg.cors <- parse_cors_value v; loop rest'
       | ("--auth-header", Some v, _) -> cfg.auth_header <- v; loop rest
       | ("--auth-header", None, v :: rest') -> cfg.auth_header <- v; loop rest'
       | ("--proxied-auth-rw-graphnames", Some v, _) ->
         cfg.proxied_auth_rw_graphnames <- Some v; loop rest
       | ("--proxied-auth-rw-graphnames", None, v :: rest') ->
         cfg.proxied_auth_rw_graphnames <- Some v; loop rest'
       | ("--dump-rw-graphs-on-exit", Some v, _) ->
         cfg.dump_rw_graphs_on_exit <- Some v; loop rest
       | ("--dump-rw-graphs-on-exit", None, _) ->
         cfg.dump_rw_graphs_on_exit <- Some default_dump_dir; loop rest
       | ("--load-rw-graphs", Some v, _) ->
         cfg.load_rw_graphs <- Some v; loop rest
       | ("--load-rw-graphs", None, v :: rest') ->
         cfg.load_rw_graphs <- Some v; loop rest'
       | _ ->
         Printf.eprintf "Error: unrecognised argument '%s' (try --help)\n" arg;
         exit 1)
  in
  loop args;
  (* Startup validation: template must contain {authid}. *)
  (match cfg.proxied_auth_rw_graphnames with
   | Some tmpl when not (String.length tmpl >= 8 &&
                         (let rec contains s sub =
                            let ls = String.length s in
                            let lsub = String.length sub in
                            if lsub > ls then false
                            else if String.sub s 0 lsub = sub then true
                            else contains (String.sub s 1 (ls - 1)) sub
                          in contains tmpl "{authid}")) ->
     Printf.eprintf
       "Error: --proxied-auth-rw-graphnames template must contain \"{authid}\".\n\
        Got: %s\n" tmpl;
     exit 1
   | _ -> ());
  (* Read-only wins over proxied-auth if both are set. *)
  (match (cfg.read_only, cfg.proxied_auth_rw_graphnames) with
   | (true, Some _) ->
     Printf.eprintf
       "Warning: --read-only overrides --proxied-auth-rw-graphnames. \
        All POST /update requests will be rejected with 403.\n";
     cfg.proxied_auth_rw_graphnames <- None
   | _ -> ());
  cfg

(* ============================================================================
   Dataset loading — delegates to the loader that factoidal_cli already uses.
   ============================================================================ *)

let load_dataset cfg =
  let base_ds =
    match cfg.dataset_file with
    | None -> { ds_default = []; ds_named = [] }
    | Some f ->
      try load_rdf_dataset
            ~format:cfg.input_format ~base:cfg.base_iri f
      with e ->
        Printf.eprintf "Error loading dataset %s: %s\n" f (Printexc.to_string e);
        exit 1
  in
  match cfg.load_rw_graphs with
  | None -> base_ds
  | Some f ->
    (try
       let content = read_file f in
       let extra = Parser_NQuads.parse_nquads content in
       (* Merge: extra's default-graph triples go into default; named graphs
          are appended (later entries with the same name shadow earlier ones
          only via lookup_named_graph's first-match semantics). *)
       { ds_default = base_ds.ds_default @ extra.ds_default;
         ds_named = base_ds.ds_named @ extra.ds_named }
     with e ->
       Printf.eprintf "Error loading --load-rw-graphs %s: %s\n"
         f (Printexc.to_string e);
       exit 1)

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
  | 403 -> "Forbidden"
  | 404 -> "Not Found"
  | 405 -> "Method Not Allowed"
  | 500 -> "Internal Server Error"
  | 501 -> "Not Implemented"
  | _ -> "Unknown"

(* [extra_headers] is a list of already-formatted "Name: value" lines (no CRLF)
   that are emitted between the standard headers and the body. CORS headers
   go here. Empty list = historical behaviour. *)
let write_response ?(extra_headers=[]) oc ~status ~content_type ~body =
  let text = status_text status in
  let extras =
    List.fold_left (fun acc h -> acc ^ h ^ "\r\n") "" extra_headers
  in
  let headers =
    Printf.sprintf
      "HTTP/1.1 %d %s\r\nContent-Type: %s\r\nContent-Length: %d\r\nConnection: close\r\n%s\r\n"
      status text content_type (String.length body) extras
  in
  output_string oc headers;
  output_string oc body;
  flush oc

let write_plain_error ?(extra_headers=[]) oc ~status msg =
  write_response ~extra_headers oc ~status ~content_type:"text/plain; charset=utf-8"
    ~body:(msg ^ "\n")

(* Build the CORS headers for a response given the current CORS policy and the
   requesting Origin (if any). Returns a (possibly empty) list of pre-formatted
   "Name: value" header lines suitable for [extra_headers].

   For [CORS_Off], returns []. For [CORS_Any], always emits the wildcard and
   is origin-independent. For [CORS_List origins], echoes the requesting
   Origin only if it's in the allowlist, and adds "Vary: Origin"; if the
   requesting origin is absent or not allowlisted, returns [] (letting the
   browser's default cross-origin rejection apply — the canonical pattern). *)
let cors_headers ~(policy : cors_policy) ~(origin : string option) : string list =
  let common_headers =
    [ "Access-Control-Allow-Methods: GET, POST, OPTIONS";
      "Access-Control-Allow-Headers: Content-Type, Authorization, Cf-Access-Jwt-Assertion, Cf-Access-Authenticated-User-Email, X-Authid";
      "Access-Control-Max-Age: 86400" ]
  in
  match policy with
  | CORS_Off -> []
  | CORS_Any ->
    "Access-Control-Allow-Origin: *" :: common_headers
  | CORS_List allowed ->
    (match origin with
     | Some o when List.mem o allowed ->
       ("Access-Control-Allow-Origin: " ^ o)
       :: "Vary: Origin"
       :: common_headers
     | _ -> [])

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

(* ============================================================================
   Per-user UPDATE sandboxing.

   Given an auth template like "urn:fct:user:{authid}" and the authenticated
   identity "alice@example.com", the user's permitted graph IRI is
   "urn:fct:user:alice@example.com". Every op in the update must target
   exactly this graph:

   * U_InsertData / U_DeleteData / U_DeleteWhere / U_Modify: the template
     pattern's top-level GP_Graph wrapper (if any) must resolve to USERGRAPH.
     If the template has no GRAPH wrapper (i.e. the user wrote to the default
     graph), we rewrite it to GRAPH <USERGRAPH> { ... } — friendly default.

   * U_Clear / U_Drop / U_Create / U_Add / U_Move / U_Copy: examine the
     graph_ref. Only GR_Graph iri with iri = USERGRAPH is allowed.

   * U_Load: always 501 (unchanged; separate pre-check earlier).

   This is a validator/rewriter pass over the sparql_update AST between
   parse_sparql_update and apply_update. Pure OCaml glue, no F* changes.
   ============================================================================ *)

(* Simple substring replace: replace every literal occurrence of [needle]
   in [haystack] with [replacement]. *)
let string_replace_all ~needle ~replacement haystack =
  if needle = "" then haystack
  else begin
    let nlen = String.length needle in
    let hlen = String.length haystack in
    let buf = Buffer.create (hlen + 16) in
    let i = ref 0 in
    while !i <= hlen - nlen do
      if String.sub haystack !i nlen = needle then begin
        Buffer.add_string buf replacement;
        i := !i + nlen
      end else begin
        Buffer.add_char buf haystack.[!i];
        incr i
      end
    done;
    (* tail *)
    while !i < hlen do
      Buffer.add_char buf haystack.[!i];
      incr i
    done;
    Buffer.contents buf
  end

let expand_user_graph ~template ~authid =
  string_replace_all ~needle:"{authid}" ~replacement:authid template

(* The fixed prefix of the user-graph template: everything before
   "{authid}". We use this to detect which named graphs in the dataset
   belong to the user-writable sandbox when dumping on exit. *)
let template_prefix template =
  match String.index_opt template '{' with
  | None -> template
  | Some i ->
    (* Only treat "{authid}" as the placeholder. *)
    if i + 8 <= String.length template
       && String.sub template i 8 = "{authid}"
    then String.sub template 0 i
    else template

(* Unwrap a GP_Graph (PT_IRI g) { body } wrapper if the target graph matches
   [usergraph]. Returns:
     - `Ok: no change needed (no outer GRAPH wrapper, or wrapper matches)
     - `Mismatch iri: outer GRAPH wrapper targets a different specific IRI
     - `NonIri: outer GRAPH wrapper uses a variable (we reject; can't prove
       this stays inside the sandbox at parse time) *)
let check_ggp_graph_target (g : SPARQL11_Algebra.group_graph_pattern)
    ~(usergraph : string) :
  [ `Ok | `Mismatch of string | `NonIri ] =
  match g with
  | SPARQL11_Algebra.GP_Graph (pt, _inner) ->
    (match pt with
     | SPARQL11_Algebra.PT_IRI iri ->
       if iri = usergraph then `Ok else `Mismatch iri
     | _ -> `NonIri)
  | _ -> `Ok

(* If the ggp has no outer GRAPH wrapper, wrap it with GRAPH <usergraph> { ... }.
   If it already has one (matching usergraph — caller has checked), leave as-is. *)
let wrap_if_unwrapped (g : SPARQL11_Algebra.group_graph_pattern)
    ~(usergraph : string) : SPARQL11_Algebra.group_graph_pattern =
  match g with
  | SPARQL11_Algebra.GP_Graph _ -> g
  | _ -> SPARQL11_Algebra.GP_Graph (SPARQL11_Algebra.PT_IRI usergraph, g)

type sandbox_result =
  | SB_Ok of SPARQL11_Algebra.update_op
  | SB_Reject of string  (* human-readable reason *)

(* Sandbox-check one update op. Returns SB_Ok (rewritten op) or SB_Reject msg. *)
let sandbox_op ~usergraph (op : SPARQL11_Algebra.update_op) : sandbox_result =
  let open SPARQL11_Algebra in
  let check_ggp which g =
    match check_ggp_graph_target g ~usergraph with
    | `Ok -> `Rewrite (wrap_if_unwrapped g ~usergraph)
    | `Mismatch iri ->
      `Reject (Printf.sprintf
                 "%s targets graph <%s>; your sandbox is <%s>"
                 which iri usergraph)
    | `NonIri ->
      `Reject (Printf.sprintf
                 "%s uses a non-IRI graph target; only GRAPH <%s> is allowed"
                 which usergraph)
  in
  let check_gref which gr =
    match gr with
    | GR_Graph iri when iri = usergraph -> `Ok
    | GR_Graph iri ->
      `Reject (Printf.sprintf
                 "%s targets graph <%s>; your sandbox is <%s>"
                 which iri usergraph)
    | GR_Default ->
      `Reject (Printf.sprintf
                 "%s targets the default graph; your sandbox is <%s>"
                 which usergraph)
    | GR_Named ->
      `Reject (Printf.sprintf
                 "%s targets NAMED; your sandbox is <%s>"
                 which usergraph)
    | GR_All ->
      `Reject (Printf.sprintf
                 "%s targets ALL graphs; your sandbox is <%s>"
                 which usergraph)
  in
  match op with
  | U_InsertData g ->
    (match check_ggp "INSERT DATA" g with
     | `Rewrite g' -> SB_Ok (U_InsertData g')
     | `Reject msg -> SB_Reject msg)
  | U_DeleteData g ->
    (match check_ggp "DELETE DATA" g with
     | `Rewrite g' -> SB_Ok (U_DeleteData g')
     | `Reject msg -> SB_Reject msg)
  | U_DeleteWhere g ->
    (match check_ggp "DELETE WHERE" g with
     | `Rewrite g' -> SB_Ok (U_DeleteWhere g')
     | `Reject msg -> SB_Reject msg)
  | U_Modify (w, del_tpl, ins_tpl, using, where) ->
    (* Template graphs (INSERT / DELETE clauses) must resolve to usergraph.
       The WHERE clause is a query-side pattern — we leave it alone; the
       query side can read from anywhere the dataset exposes. Sandbox is
       about *writes*. *)
    let check_tpl_opt label t =
      match t with
      | FStar_Pervasives_Native.None -> `Rewrite FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some g ->
        (match check_ggp label g with
         | `Rewrite g' -> `Rewrite (FStar_Pervasives_Native.Some g')
         | `Reject msg -> `Reject msg)
    in
    (match check_tpl_opt "INSERT/DELETE: DELETE clause" del_tpl with
     | `Reject msg -> SB_Reject msg
     | `Rewrite del_tpl' ->
       (match check_tpl_opt "INSERT/DELETE: INSERT clause" ins_tpl with
        | `Reject msg -> SB_Reject msg
        | `Rewrite ins_tpl' ->
          SB_Ok (U_Modify (w, del_tpl', ins_tpl', using, where))))
  | U_Clear (silent, gr) ->
    (match check_gref "CLEAR" gr with
     | `Ok -> SB_Ok (U_Clear (silent, gr))
     | `Reject msg -> SB_Reject msg)
  | U_Drop (silent, gr) ->
    (match check_gref "DROP" gr with
     | `Ok -> SB_Ok (U_Drop (silent, gr))
     | `Reject msg -> SB_Reject msg)
  | U_Create (silent, iri) ->
    if iri = usergraph then SB_Ok (U_Create (silent, iri))
    else SB_Reject (Printf.sprintf
                      "CREATE targets graph <%s>; your sandbox is <%s>"
                      iri usergraph)
  | U_Add (silent, src, dst) ->
    (match check_gref "ADD source" src with
     | `Reject msg -> SB_Reject msg
     | `Ok ->
       (match check_gref "ADD dest" dst with
        | `Ok -> SB_Ok (U_Add (silent, src, dst))
        | `Reject msg -> SB_Reject msg))
  | U_Move (silent, src, dst) ->
    (match check_gref "MOVE source" src with
     | `Reject msg -> SB_Reject msg
     | `Ok ->
       (match check_gref "MOVE dest" dst with
        | `Ok -> SB_Ok (U_Move (silent, src, dst))
        | `Reject msg -> SB_Reject msg))
  | U_Copy (silent, src, dst) ->
    (match check_gref "COPY source" src with
     | `Reject msg -> SB_Reject msg
     | `Ok ->
       (match check_gref "COPY dest" dst with
        | `Ok -> SB_Ok (U_Copy (silent, src, dst))
        | `Reject msg -> SB_Reject msg))
  | U_Load _ ->
    (* U_Load is caught upstream by update_has_load -> 501. Defensive. *)
    SB_Reject "LOAD is not permitted in sandboxed updates"

(* Sandbox-check and rewrite a whole sparql_update. Returns either the
   rewritten update or an error message identifying the first offending op. *)
let sandbox_update ~usergraph (u : SPARQL11_Algebra.sparql_update) :
  (SPARQL11_Algebra.sparql_update, string) result =
  let rec go acc = function
    | [] -> Ok (List.rev acc)
    | op :: rest ->
      (match sandbox_op ~usergraph op with
       | SB_Ok op' -> go (op' :: acc) rest
       | SB_Reject msg -> Error msg)
  in
  match go [] u.u_ops with
  | Error msg -> Error msg
  | Ok ops' -> Ok { u with u_ops = ops' }

(* ============================================================================
   N-Quads emitter — inline, for dump-on-exit.

   We don't have an F*-extracted N-Quads serialiser today. The output shape
   is the standard N-Quads line:
       <s> <p> <o> <g> .
   Literals are quoted with proper escaping. Blank nodes are "_:id".
   ============================================================================ *)

let nq_escape_literal s =
  let buf = Buffer.create (String.length s + 4) in
  String.iter (fun c ->
    match c with
    | '\\' -> Buffer.add_string buf "\\\\"
    | '"'  -> Buffer.add_string buf "\\\""
    | '\n' -> Buffer.add_string buf "\\n"
    | '\r' -> Buffer.add_string buf "\\r"
    | '\t' -> Buffer.add_string buf "\\t"
    | c    -> Buffer.add_char buf c
  ) s;
  Buffer.contents buf

let nq_term_to_string (t : rdf_term) =
  match t with
  | T_IRI i -> Printf.sprintf "<%s>" i
  | T_BNode b -> Printf.sprintf "_:%s" b
  | T_Literal l ->
    let xsd_string = "http://www.w3.org/2001/XMLSchema#string" in
    let rdf_lang_string =
      "http://www.w3.org/1999/02/22-rdf-syntax-ns#langString" in
    let esc = nq_escape_literal l.lexical_form in
    (match l.lang_tag with
     | Some tag -> Printf.sprintf "\"%s\"@%s" esc tag
     | None ->
       if l.datatype = "" || l.datatype = xsd_string then
         Printf.sprintf "\"%s\"" esc
       else if l.datatype = rdf_lang_string then
         (* Malformed — langString with no tag. Preserve lexically. *)
         Printf.sprintf "\"%s\"^^<%s>" esc l.datatype
       else
         Printf.sprintf "\"%s\"^^<%s>" esc l.datatype)

let nq_subject_to_string (s : subject) =
  match s with
  | S_IRI i -> Printf.sprintf "<%s>" i
  | S_BNode b -> Printf.sprintf "_:%s" b

let nq_line_for_triple ~graph_iri (t : triple) =
  Printf.sprintf "%s <%s> %s <%s> .\n"
    (nq_subject_to_string t.s)
    t.p
    (nq_term_to_string t.o)
    graph_iri

(* Which named graphs in the current dataset belong to user-writable
   sandboxes? We compute this by listing every named graph whose IRI is not
   in the startup snapshot of named-graph IRIs. (Simple and conservative —
   any graph created or written to during server runtime is dumped.) *)
let diff_named_graphs ~(snapshot_iris : string list) (ds : rdf_dataset)
  : named_graph list =
  List.filter (fun ng -> not (List.mem ng.ng_name snapshot_iris))
    ds.ds_named

let write_dump_readme dir =
  let path = Filename.concat dir "README.md" in
  if not (Sys.file_exists path) then begin
    let oc = open_out path in
    output_string oc
      "# factoidal-http RW-graphs dump\n\
       \n\
       This directory is a per-user sandbox dump from a factoidal SPARQL\n\
       endpoint. The data here was written by authenticated users via POST\n\
       /update and MAY contain unreviewed, low-quality, or deliberately\n\
       adversarial content.\n\
       \n\
       **Please do not crawl or include in training datasets.** This is not\n\
       a curated corpus.\n";
    close_out oc
  end

let rec mkdir_p dir =
  if dir = "" || dir = "." || dir = "/" then ()
  else if Sys.file_exists dir && Sys.is_directory dir then ()
  else begin
    let parent = Filename.dirname dir in
    if parent <> dir then mkdir_p parent;
    (try Unix.mkdir dir 0o755 with Unix.Unix_error (Unix.EEXIST, _, _) -> ())
  end

let timestamp_compact () =
  let t = Unix.gmtime (Unix.time ()) in
  Printf.sprintf "%04d%02d%02d-%02d%02d%02d"
    (t.tm_year + 1900) (t.tm_mon + 1) t.tm_mday
    t.tm_hour t.tm_min t.tm_sec

let dump_rw_graphs ~dir ~snapshot_iris (ds : rdf_dataset) =
  try
    mkdir_p dir;
    let rw = diff_named_graphs ~snapshot_iris ds in
    let fname = Filename.concat dir
        (Printf.sprintf "rw-graphs-%s.nq" (timestamp_compact ())) in
    let oc = open_out fname in
    List.iter (fun ng ->
      List.iter (fun t ->
        output_string oc (nq_line_for_triple ~graph_iri:ng.ng_name t)
      ) ng.ng_graph
    ) rw;
    close_out oc;
    write_dump_readme dir;
    Printf.eprintf "[dump] wrote %d graph(s) to %s\n%!"
      (List.length rw) fname
  with e ->
    Printf.eprintf "[dump] error: %s\n%!" (Printexc.to_string e)

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
    let origin = header_value headers "origin" in
    let cors_hdrs = cors_headers ~policy:cfg.cors ~origin in
    if cfg.verbose then
      Printf.eprintf "[%s] %s %s (body=%d, accept=%s, ct=%s)\n%!"
        (let t = Unix.localtime (Unix.time ()) in
         Printf.sprintf "%04d-%02d-%02d %02d:%02d:%02d"
           (t.tm_year + 1900) (t.tm_mon + 1) t.tm_mday
           t.tm_hour t.tm_min t.tm_sec)
        meth uri (String.length body) accept ct;

    (* CORS preflight: answer OPTIONS with 204 and the CORS headers, never
       try to parse it as a SPARQL request. When CORS is off, fall through
       and the F* decoder will reply 405 (method not allowed) as before. *)
    if meth = "OPTIONS" && cfg.cors <> CORS_Off then begin
      write_response ~extra_headers:cors_hdrs oc
        ~status:204
        ~content_type:"text/plain; charset=utf-8"
        ~body:""
    end else

    let dataset = !dataset_ref in
    let resp =
      match P.decode_request meth path qs ct body with
      | P.PR_Bad msg ->
        { rb_status = 400;
          rb_content_type = "text/plain; charset=utf-8";
          rb_body = msg ^ "\n" }
      | P.PR_Update (update_text, _dflt, _named) ->
        if cfg.read_only then
          { rb_status = 403;
            rb_content_type = "text/plain; charset=utf-8";
            rb_body =
              "SPARQL UPDATE is disabled on this endpoint (--read-only).\n\
               This server is configured to accept queries only.\n" }
        else
        (* If proxied-auth-rw-graphnames is set, enforce trusted-header auth
           and sandbox the update to the user's own graph. Otherwise, fall
           through to the unconstrained update path. *)
        let auth_result =
          match cfg.proxied_auth_rw_graphnames with
          | None -> `Unsandboxed
          | Some template ->
            (match header_value headers cfg.auth_header with
             | None | Some "" ->
               `Unauthenticated
             | Some authid ->
               `Sandboxed (template, authid,
                           expand_user_graph ~template ~authid))
        in
        (match auth_result with
         | `Unauthenticated ->
           { rb_status = 403;
             rb_content_type = "text/plain; charset=utf-8";
             rb_body =
               Printf.sprintf
                 "unauthenticated — set %s header via your auth proxy\n"
                 cfg.auth_header }
         | _ ->
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
             (* Sandbox-pass: rewrite or reject depending on auth mode. *)
             let sandboxed =
               match auth_result with
               | `Unsandboxed -> Ok u
               | `Sandboxed (_template, _authid, usergraph) ->
                 sandbox_update ~usergraph u
               | `Unauthenticated -> assert false (* handled above *)
             in
             match sandboxed with
             | Error msg ->
               { rb_status = 403;
                 rb_content_type = "text/plain; charset=utf-8";
                 rb_body = "update rejected: " ^ msg ^ "\n" }
             | Ok u' ->
               let new_ds =
                 try SPARQL11_Algebra.apply_update dataset u'
                 with e ->
                   Printf.eprintf "  update execution error: %s\n%!"
                     (Printexc.to_string e);
                   dataset
               in
               dataset_ref := new_ds;
               { rb_status = 204;
                 rb_content_type = "text/plain; charset=utf-8";
                 rb_body = "" }
           end))
      | P.PR_Query (q, _dflt, _named) ->
        (* Stage 1: ignore default-graph-uri / named-graph-uri (would
           require HTTP fetch to honour). The dataset preloaded via
           --dataset is served as the default graph; UPDATE ops
           accumulated via POST /update mutate the shared ref. *)
        parse_and_run ~dataset ~accept q
    in
    write_response ~extra_headers:cors_hdrs oc
      ~status:resp.rb_status
      ~content_type:resp.rb_content_type
      ~body:resp.rb_body
  with
  | Bad_request msg ->
    (* If the request line was malformed enough that we never read an
       Origin header, we just omit CORS headers on the 400 response —
       the client wasn't going to honour them anyway. *)
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
  (* Snapshot the set of named-graph IRIs at startup (after dataset +
     load-rw-graphs) — on graceful exit we diff against this to identify
     user-writable graphs. *)
  let snapshot_iris =
    List.map (fun ng -> ng.ng_name) (!dataset_ref).ds_named
  in
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
  Printf.printf "  mode: %s\n"
    (if cfg.read_only
     then "read-only (POST /update -> 403)"
     else if cfg.proxied_auth_rw_graphnames <> None
     then Printf.sprintf "proxied-auth (header: %s; template: %s)"
            cfg.auth_header
            (match cfg.proxied_auth_rw_graphnames with
             | Some t -> t | None -> "<none>")
     else "read-write (POST /update mutates in-memory dataset)");
  Printf.printf "  cors: %s\n" (cors_mode_to_string cfg.cors);
  (* Loud warning: --cors=* combined with writes lets any browser page hit
     POST /update cross-origin, bypassing same-origin CSRF protection. Flush
     stderr immediately so the warning lands before any request log lines. *)
  (match cfg.cors with
   | CORS_Any when not cfg.read_only ->
     Printf.eprintf "warning: --cors=* combined with write access is dangerous\n";
     Printf.eprintf "warning: any browser page can issue POST /update against this server\n";
     Printf.eprintf "warning: either add --read-only or an allowlist\n%!"
   | _ -> ());
  (match cfg.dataset_file with
   | Some f -> Printf.printf "  default graph: %s (%d triples)\n" f triple_count
   | None -> Printf.printf "  default graph: <empty>\n");
  (match cfg.load_rw_graphs with
   | Some f ->
     Printf.printf "  loaded RW graphs from: %s (%d named graph(s) now)\n"
       f (List.length (!dataset_ref).ds_named)
   | None -> ());
  (match cfg.dump_rw_graphs_on_exit with
   | Some d ->
     Printf.printf "  dump-on-exit: %s (SIGTERM/SIGINT)\n" d
   | None -> ());
  Printf.printf "  try: curl -H 'Accept: application/sparql-results+json' \\\n";
  Printf.printf "         'http://%s:%d/query?query=SELECT%%20*%%20WHERE%%20%%7B%%3Fs%%20%%3Fp%%20%%3Fo%%7D'\n"
    cfg.host cfg.port;
  flush stdout;
  (* Ignore SIGPIPE so a client closing early doesn't kill the server. *)
  (try Sys.set_signal Sys.sigpipe Sys.Signal_ignore with _ -> ());
  (* Graceful-exit handler: dump user-writable graphs to N-Quads. *)
  let install_exit_handler signal_name sig_id =
    Sys.set_signal sig_id (Sys.Signal_handle (fun _ ->
      Printf.eprintf "\n[%s] graceful shutdown requested\n%!" signal_name;
      (match cfg.dump_rw_graphs_on_exit with
       | Some dir ->
         dump_rw_graphs ~dir ~snapshot_iris !dataset_ref
       | None -> ());
      exit 0))
  in
  (try install_exit_handler "SIGTERM" Sys.sigterm with _ -> ());
  (try install_exit_handler "SIGINT" Sys.sigint with _ -> ());
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
