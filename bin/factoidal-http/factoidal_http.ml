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
module S = SPARQL11_Store

(* Issue #275 (rule #11 ASSUME-IO): explicitly realise the JSON-LD
   documentLoader seam as an honest "no remote loading" for the HTTP
   endpoint — see JSONLD.Loader.fst's banner and jsonld_runner.ml (the
   ONE consumer with a real fixture-file loader). *)
let () = JSONLD_Loader.jsonld_loader_register (fun _ -> FStar_Pervasives_Native.None)

(* ============================================================================
   RDF file loading — same shape as factoidal_cli, inlined here so we don't
   link factoidal_cli.ml (which has its own [let () = ...] main).
   ============================================================================ *)

(* RDF format identification — F* is the source of truth.
   Logic lives in formal/fstar/RDF.Format.fst (extracted as
   RDF_Format.ml). The wrappers below re-export the constructors and
   adapt F*'s option to OCaml's native option so existing
   match-Some/None call sites compile unchanged. *)
type rdf_format = RDF_Format.rdf_format =
  | NT
  | Turtle
  | NQuads
  | TriG
  | RDFXML
  | JSONLD

let detect_format filename =
  RDF_Format.detect_format_or_default (Filename.extension filename)

let format_of_string s =
  match RDF_Format.format_of_string s with
  | FStar_Pervasives_Native.Some f -> Some f
  | FStar_Pervasives_Native.None -> None

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
  | JSONLD ->
    (* Context processing + document base threading per issue #275 —
       see formal/fstar/Parser.JSONLD.fst module banner. Remote
       contexts / "@import" are an honest FAIL here (no loader
       registered above). *)
    let fs_base = match base_iri with
      | Some b -> FStar_Pervasives_Native.Some b
      | None -> FStar_Pervasives_Native.None in
    (match Parser_JSONLD.parse_jsonld content fs_base FStar_Pervasives_Native.None FStar_Pervasives_Native.None FStar_Pervasives_Native.None with
     | FStar_Pervasives_Native.Some ds -> ds
     | FStar_Pervasives_Native.None ->
       failwith "invalid JSON-LD (parse or unsupported feature — remote contexts need a loader this endpoint does not have)")
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
(* The cors_policy type is defined in F* (SPARQL.HTTP.Response) so the
   header-emitter logic that switches on it can live in the verified spec.
   We re-export the F*-extracted type here with an alias that re-binds the
   constructor names, so the rest of this file (and any callers) keep
   using [CORS_Off] / [CORS_Any] / [CORS_List] without qualification. *)
type cors_policy = SPARQL_HTTP_Response.cors_policy =
  | CORS_Off
  | CORS_Any
  | CORS_List of string list

(* --server-timing=on|off|auto (issue #266).

   The Server-Timing header (parse/eval/format/total, ms-rounded) is a
   diagnostic convenience for the web client's Details pane, but it is
   also a timing side channel: eval;dur leaks query-cost information
   that can be used to infer named-graph cardinality or FILTER
   success/failure against data the requester shouldn't otherwise be
   able to observe. That's only a real threat when the requester might
   be untrusted, so the flag defaults to policy-driven auto-detection
   rather than a single hardcoded default. This is deployment policy
   for the HTTP consumer binary, not RDF/SPARQL semantics, so per rule
   #11 it is fine as hand-written OCaml in bin/factoidal-http/ rather
   than F*.

   ST_On  / ST_Off : explicit override, ignores the deployment shape.
   ST_Auto         : off when the deployment looks multi-tenant or
                     tunnel-exposed (--proxied-auth-rw-graphnames is
                     set, --cors is anything but off, or --host is not
                     127.0.0.1); on otherwise (bound to loopback, no
                     CORS, no per-user write sandboxing — i.e.
                     local-dev / single-user mode, where the side
                     channel is moot). See [server_timing_enabled]
                     below for the actual predicate. *)
type server_timing_mode = ST_On | ST_Off | ST_Auto

let server_timing_mode_of_string = function
  | "on" -> Some ST_On
  | "off" -> Some ST_Off
  | "auto" -> Some ST_Auto
  | _ -> None

let server_timing_mode_to_string = function
  | ST_On -> "on"
  | ST_Off -> "off"
  | ST_Auto -> "auto"

type config = {
  mutable port : int;
  mutable dataset_file : string option;
  (* Binary COTTAS/Parquet dataset(s) to seed the store from. Repeatable.
     Loaded after --dataset; default-graph triples are concatenated, named
     graphs appended. Decoder lives in F* (Parser.BallyhooCOTTAS,
     Parquet.Footer). *)
  mutable data_cottas_files : string list;
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
  (* Per-dataset web UI to mount at "/". Either a bare demo id (resolved
     under docs/web/demos/<id>/) or an absolute path. None = generic
     landing page in docs/web/landing/. The directory is served as a
     recursive static-file tree; UI changes do not require a recompile. *)
  mutable web_demo : string option;
  (* Per-query result-cardinality cap (issue: tav5 SIGBUS circuit breaker).
     When [eval_select_query_backend_dataset] returns more than [max_rows]
     solutions, the handler short-circuits with HTTP 413 *before* the
     marshalling path runs. macOS pthread default stack is 544 KB and the
     non-tail-rec list walks in the JSON / XML serialisers blow it out at
     ~3 M rows. 0 = disabled (use only when investigating tail-rec bugs). *)
  mutable max_rows : int;
  (* Per-query wall-clock budget in seconds. Implemented as a cooperative
     [SPARQL.Eval.TimeBudget.budget] value built via
     [SPARQL_Eval_TimeBudget.mk_budget_secs]. The OCaml HTTP boundary
     constructs the budget per request; after [parse_and_run] returns,
     [SPARQL_Eval_TimeBudget.poll] is consulted and an HTTP 504 Gateway
     Timeout is emitted (instead of the response) when the wallclock
     deadline has elapsed. 0 = disabled (infinite).

     Heth3 retirement: the prior implementation used Unix.alarm + SIGALRM
     and an OCaml-side [Query_timeout] exception. SIGALRM is process-
     global, so in the multi-threaded accept-loop / COTTAS-loader thread
     pairing it could fire in the wrong thread. Replaced per recovery
     plan Phase 5 (docs/designissues/2026-05-07-query-planning-fstar-
     recovery.md) and Iron Rule #11. In-flight cancellation at evaluator
     yield boundaries is a follow-up; this change retires the SIGALRM
     architectural violation and relocates the timeout decision to F*. *)
  mutable query_timeout : int;
  (* --server-timing=on|off|auto (issue #266). See [server_timing_mode]
     above for the threat model and [server_timing_enabled] for the
     auto predicate. Default ST_Auto. *)
  mutable server_timing : server_timing_mode;
}

let default_dump_dir =
  "./tmp/autoexec.bot-llms_exclude-keep_out_this_is_not_a_place_of_honour/"

let default_config () = {
  port = 3030;
  dataset_file = None;
  data_cottas_files = [];
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
  web_demo = None;
  max_rows = 50_000;
  query_timeout = 30;
  server_timing = ST_Auto;
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
  print_endline "      --data-cottas FILE Seed dataset from a binary COTTAS/Parquet";
  print_endline "                         artifact (repeatable). Decoded via the";
  print_endline "                         F*-verified Parquet footer + DeltaLengthByteArray";
  print_endline "                         path; Zstd via the C stub. Much faster than";
  print_endline "                         re-parsing N-Quads/TriG on startup.";
  print_endline "                         Alias: --cottas-data FILE.";
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
  print_endline "      --web-demo=ID_OR_PATH";
  print_endline "                         Per-dataset web UI mounted at /. Bare id";
  print_endline "                         resolves under docs/web/demos/<id>/; an";
  print_endline "                         absolute path is served as-is. Default";
  print_endline "                         (no flag) serves docs/web/landing/.";
  print_endline "                         Examples: --web-demo=ukparliament";
  print_endline "                                   --web-demo=/path/to/dir";
  print_endline "      --max-rows N       Per-query result-cardinality cap. When the";
  print_endline "                         BGP/algebra evaluator returns more than N solution";
  print_endline "                         rows, the handler short-circuits with HTTP 413";
  print_endline "                         (Payload Too Large) before marshalling. This";
  print_endline "                         protects the daemon from stack overflow on very";
  print_endline "                         large unbounded queries. 0 = disabled.";
  print_endline "                         (default 50000)";
  print_endline "      --query-timeout SECS  Per-query wall-clock budget. When the evaluator";
  print_endline "                         takes longer than SECS, the handler returns HTTP";
  print_endline "                         504 Gateway Timeout (freeing the worker for the";
  print_endline "                         next request) instead of letting one slow query";
  print_endline "                         block the single-threaded accept loop.";
  print_endline "                         Cooperative budget via SPARQL.Eval.TimeBudget.";
  print_endline "                         0 = disabled (infinite). (default 30)";
  print_endline "      --server-timing=on|off|auto";
  print_endline "                         Emit a Server-Timing response header on POST/GET";
  print_endline "                         /query and /sparql (parse;dur=, eval;dur=,";
  print_endline "                         format;dur=, total;dur=, millisecond-rounded).";
  print_endline "                         SECURITY: eval;dur is a timing side channel — it";
  print_endline "                         can leak query-cost information (named-graph";
  print_endline "                         cardinality, FILTER success/failure) to a";
  print_endline "                         requester who shouldn't otherwise observe it.";
  print_endline "                         on    always emit the header.";
  print_endline "                         off   never emit the header.";
  print_endline "                         auto  (default) off when the deployment looks";
  print_endline "                               multi-tenant or tunnel-exposed:";
  print_endline "                               --proxied-auth-rw-graphnames is set, OR";
  print_endline "                               --cors is anything but unset/off, OR";
  print_endline "                               --host is not 127.0.0.1.";
  print_endline "                               on otherwise (loopback, no CORS, no";
  print_endline "                               per-user write sandbox — local-dev /";
  print_endline "                               single-user mode, where the side channel";
  print_endline "                               is moot).";
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
(* Forward to the F*-verified parse + display functions in
   SPARQL_HTTP_Response. The semantic decisions (string -> CORS variant,
   variant -> human description) are F*-source-of-truth per rule #1.
   See formal/fstar/SPARQL.HTTP.Response.fst. *)
let parse_cors_value : string -> cors_policy =
  SPARQL_HTTP_Response.parse_cors_value

let cors_mode_to_string : cors_policy -> string =
  SPARQL_HTTP_Response.cors_mode_to_string

(* Split "--key=value" into ("--key", Some "value"); otherwise (arg, None). *)
let split_eq arg =
  match String.index_opt arg '=' with
  | None -> (arg, None)
  | Some i ->
    (String.sub arg 0 i,
     Some (String.sub arg (i + 1) (String.length arg - i - 1)))

(* parse_args reads from an explicit args list (NOT Sys.argv directly) so
   the unified CLI dispatcher in factoidal_cli.ml can hand it the
   post-`serve` argv tail. The default ?args resolves to the legacy
   "tail of Sys.argv" path used by the standalone factoidal-http binary. *)
let parse_args ?args () =
  let cfg = default_config () in
  let args = match args with
    | Some a -> a
    | None -> Array.to_list Sys.argv |> List.tl in
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
    | ("--data-cottas" | "--cottas-data") :: f :: rest ->
      cfg.data_cottas_files <- cfg.data_cottas_files @ [f]; loop rest
    | ("-f" | "--format") :: fmt :: rest ->
      (match format_of_string fmt with
       | Some f -> cfg.input_format <- Some f
       | None -> Printf.eprintf "Error: unknown format '%s'\n" fmt; exit 1);
      loop rest
    | ("-b" | "--base") :: b :: rest -> cfg.base_iri <- Some b; loop rest
    | "--read-only" :: rest -> cfg.read_only <- true; loop rest
    | ("-v" | "--verbose") :: rest -> cfg.verbose <- true; loop rest
    | "--max-rows" :: n :: rest ->
      (match int_of_string_opt n with
       | Some k when k >= 0 -> cfg.max_rows <- k
       | _ ->
         Printf.eprintf
           "Error: --max-rows needs a non-negative integer (0 = disabled), got '%s'\n" n;
         exit 1);
      loop rest
    | "--query-timeout" :: n :: rest ->
      (match int_of_string_opt n with
       | Some k when k >= 0 -> cfg.query_timeout <- k
       | _ ->
         Printf.eprintf
           "Error: --query-timeout needs a non-negative integer (0 = disabled), got '%s'\n" n;
         exit 1);
      loop rest
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
       | ("--web-demo", Some v, _) ->
         cfg.web_demo <- Some v; loop rest
       | ("--web-demo", None, v :: rest') ->
         cfg.web_demo <- Some v; loop rest'
       | ("--query-timeout", Some v, _) ->
         (match int_of_string_opt v with
          | Some k when k >= 0 -> cfg.query_timeout <- k
          | _ ->
            Printf.eprintf
              "Error: --query-timeout needs a non-negative integer (0 = disabled), got '%s'\n" v;
            exit 1);
         loop rest
       | ("--server-timing", Some v, _) ->
         (match server_timing_mode_of_string v with
          | Some m -> cfg.server_timing <- m
          | None ->
            Printf.eprintf
              "Error: --server-timing needs on|off|auto, got '%s'\n" v;
            exit 1);
         loop rest
       | ("--server-timing", None, v :: rest') ->
         (match server_timing_mode_of_string v with
          | Some m -> cfg.server_timing <- m
          | None ->
            Printf.eprintf
              "Error: --server-timing needs on|off|auto, got '%s'\n" v;
            exit 1);
         loop rest'
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

(* Background-load state (issue #99). When a --data-cottas artifact is large
   enough that the parquet → in-memory rdf_dataset materialisation takes more
   than a second or so, we'd rather bind the listening socket immediately and
   load the data in a worker thread. While the worker runs:

     - GET / and other static / landing-page routes serve normally;
     - /backend-info.json serves the (currently empty / partial) dataset_ref;
     - /sparql, /query, /update return HTTP 503 + Retry-After: 5.

   Single-threaded accept loop + one loader thread = at most one writer at a
   time to dataset_ref. The mutex protects the loading flag's flip + the ref
   swap, so the request thread sees a consistent (loaded, ref) pair after the
   flag goes false. *)
let loading : bool ref = ref false
let loading_mu : Mutex.t = Mutex.create ()
let is_loading () =
  Mutex.lock loading_mu;
  let r = !loading in
  Mutex.unlock loading_mu;
  r

(* Load a COTTAS/Parquet artifact as an rdf_dataset. Mirrors the loader
   in factoidal_cli.ml. Pure OCaml glue: the Parquet footer parsing and
   DeltaLengthByteArray decode happen in F*-extracted
   [Parser_BallyhooCOTTAS] / [Parquet_Footer]; we only walk the cached
   quad rows and bucket them into default + named graphs. *)
let load_cottas_dataset (path : string) : rdf_dataset =
  match Parser_BallyhooCOTTAS.cottas_open_dataset_store path
          FStar_Pervasives_Native.None with
  | FStar_Pervasives_Native.None ->
    Printf.eprintf "Error: could not open COTTAS artifact: %s\n" path;
    exit 1
  | FStar_Pervasives_Native.Some ds ->
    let cache = Parser_BallyhooCOTTAS.Ballyhoo_cottas_runtime.cache_for_store ds in
    let open Parser_BallyhooCOTTAS.Ballyhoo_cottas_runtime in
    (* OCaml-side resolution: hashtable lookups are O(1); F* lists
       are O(n). For parliament-scale corpora (3M quads × 1M ids)
       only the OCaml hashtable path is tractable. *)
    let resolved = List.map (fun row ->
      let s = match Hashtbl.find_opt cache.id_to_subject row.qr_s with
        | Some s -> s
        | None -> failwith "cottas: missing subject id" in
      let p = match Hashtbl.find_opt cache.id_to_predicate row.qr_p with
        | Some p -> p
        | None -> failwith "cottas: missing predicate id" in
      let o = match Hashtbl.find_opt cache.id_to_object row.qr_o with
        | Some o -> o
        | None -> failwith "cottas: missing object id" in
      let triple = RDF_Graph_Executable.({ s; p; o }) in
      let g_opt = match row.qr_g with
        | None -> FStar_Pervasives_Native.None
        | Some gid ->
          (match Hashtbl.find_opt cache.id_to_graph gid with
           | Some g_iri -> FStar_Pervasives_Native.Some g_iri
           | None -> failwith "cottas: missing graph id") in
      RDF_Store_Loader.({ rq_triple = triple; rq_graph = g_opt })
    ) cache.quads in
    (* Pure F* fold: bucket resolved quads into default + named
       graphs. #200 Section A non-codename migration, 2026-05-09. *)
    RDF_Store_Loader.bucket_quads resolved

(* Load only the cheap parts of the dataset: --dataset (RDF file) and
   --load-rw-graphs (N-Quads). COTTAS folding is deferred to
   [load_cottas_part] so the HTTP listener can bind first.

   For a server with no COTTAS at all this returns the full dataset; the
   caller can skip the background thread entirely. *)
let load_dataset_fast cfg =
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
       { ds_default = base_ds.ds_default @ extra.ds_default;
         ds_named = base_ds.ds_named @ extra.ds_named }
     with e ->
       Printf.eprintf "Error loading --load-rw-graphs %s: %s\n"
         f (Printexc.to_string e);
       exit 1)

(* Fold each --data-cottas FILE into [base]. Default-graph triples
   concatenate; named graphs are appended (lookup_named_graph uses
   first-match, so earlier --data-cottas wins on collision with the
   --dataset file). Run on the loader thread; do NOT call exit on error
   from a non-main thread — return the partial dataset and log instead.

   Migration #200 PR3 (Section A non-codename, 2026-05-08): the pure
   fold is now in F* at RDF.Store.Loader.merge_datasets. OCaml owns
   the Parquet I/O (load_cottas_dataset path) + per-file try/with;
   F* owns the pure merge. *)
let load_cottas_part cfg base =
  let extras =
    List.map (fun path ->
      try load_cottas_dataset path
      with e ->
        Printf.eprintf "Error loading --data-cottas %s: %s\n%!"
          path (Printexc.to_string e);
        { ds_default = []; ds_named = [] }
    ) cfg.data_cottas_files
  in
  RDF_Store_Loader.merge_datasets base extras

(* Convenience for callers that don't need the bind-first behaviour
   (e.g. rdfc10_runner-style synchronous loaders, or future test code). *)
let load_dataset cfg =
  load_cottas_part cfg (load_dataset_fast cfg)

(* ===========================================================================
   Backend wiring (issue #100 Phase 2.5).

   The SPARQL engine (SPARQL11_Store.eval_*_backend_dataset) operates on a
   `dataset_backend` rather than the eager rdf_dataset. This lets us serve
   queries from on-disk COTTAS without materialising every quad in RAM.

   Two orthogonal pieces of state in this server:

     - dataset_ref : rdf_dataset ref
         Holds the in-memory side. UPDATE mutates this. SIGTERM dump and
         /backend-info.json triple counts come from here.

     - backend_ref : SPARQL11_Store.dataset_backend ref
         Holds the engine view. Built from dataset_ref (indexed) plus, for
         each --data-cottas file, an on-disk GB_CottasOnDisk leaf, all
         union'd together. Queries run through this.

   Invariant: after every loader step or UPDATE, backend_ref is rebuilt to
   reflect dataset_ref + the open cottas-ondisk handles.
   =========================================================================== *)

(* A pair of (path, opened on-disk store) for each --data-cottas file.
   Opens are stable for the lifetime of the server (no eviction yet); the
   on-disk store holds Parquet readers + dictionary arrays, not the parsed
   triples. *)
type cottas_ondisk_loaded = {
  cod_path : string;
  cod_store : RDF_CottasStore.cottas_ondisk_store;
}

(* Pre-warm all four lazy-populated dictionaries on the COTTAS handle.

   Bet7's commit 7ecf720 shrank cottas_ondisk_open to ~0.023s by deferring
   the per-column dictionary populate (subjects, predicates, objects,
   graphs) until the FIRST query that needs each column. That helps the
   open() latency, but the demo's first user-visible query then pays:

     - first predicate-bound query: ~14s   (ensure_predicates_loaded)
     - first subject-decoding query: ~30s  (ensure_subjects_loaded)
     - first object-decoding query: ~30s   (ensure_objects_loaded)
     - first graph-decoding query: ms..s   (ensure_graphs_loaded)

   For interactive demos we'd rather pay the populate cost up-front
   during daemon boot (the runner waits once) and have every user
   query be warm. So immediately after each successful
   cottas_ondisk_open, walk all four ensure_*_loaded helpers.

   The four helpers are idempotent + per-path; calling them again from
   the *_fast lookup paths is a hashtbl-mem hit and a no-op. Issue #100,
   followup to 7ecf720. *)
let prewarm_cottas_columns (path : string) (store : RDF_CottasStore.cottas_ondisk_store)
    : unit =
  (* Vav3 (issue #100, 2026-04-26): persistent mmap'd companion indexes.
     First boot: companions absent, build them once (~110s on parliament,
     same as the old pre-warm) then mmap. Subsequent boots: mmap +
     bulk-load Hashtbls in <2s. The companion file format is fully
     F*-defined in RDF.CottasStore.OnDiskIndex.fst.

     The bulk-load step keeps the existing *_fast Hashtbl-backed query
     paths intact — they consult tables_for h.coh_path which is now
     populated from the mmap'd .dict + .presence files. A follow-on
     phase (Phase E) will swap the query path to consult the mmap'd
     companions directly via RDF_CottasStore_OnDiskIndex.companion_*
     functions, eliminating the Hashtbls entirely.
  *)
  let h = store.RDF_CottasStore.cods_handle in
  RDF_CottasStore.Cottas_companion_boot.prewarm_via_companions path h

(* Open all --data-cottas files as on-disk stores. Errors from individual
   files are logged + skipped (mirrors load_cottas_part: don't kill the
   loader thread). Runs on the worker thread once the listener is bound.

   After each successful open, immediately pre-warm all four lazy
   dictionaries (subjects, predicates, objects, graphs) so the first
   user-visible query doesn't pay the cold-start tax. See
   [prewarm_cottas_columns] above. *)
let open_cottas_ondisk_files (paths : string list) : cottas_ondisk_loaded list =
  List.filter_map (fun path ->
    try
      match RDF_CottasStore.cottas_ondisk_open path with
      | FStar_Pervasives_Native.Some store ->
        (* Pre-warm before returning. Failures here shouldn't kill the
           open — log and continue; the lazy populators will run on first
           query as a fallback. *)
        (try prewarm_cottas_columns path store
         with e ->
           Printf.eprintf "[mim3-trace] pre-warm of %s failed: %s (lazy fallback)\n%!"
             path (Printexc.to_string e));
        Some { cod_path = path; cod_store = store }
      | FStar_Pervasives_Native.None ->
        Printf.eprintf "Error: cottas_ondisk_open returned None for %s\n%!" path;
        None
    with e ->
      Printf.eprintf "Error opening --data-cottas %s on-disk: %s\n%!"
        path (Printexc.to_string e);
      None
  ) paths

(* Combine the in-memory rdf_dataset side and the cottas-ondisk side into a
   single dataset_backend. Default + per-named-graph slots are unioned so
   the engine sees both halves through the same backend_search dispatch.

   Three shapes:
     - cottas-ondisk only: union over each ondisk store's
       cottas_ondisk_dataset_backend; the in-memory side contributes empty.
     - in-memory only: indexed_dataset_backend over dataset_ref. *)
let build_dataset_backend
    (in_memory : rdf_dataset)
    (cottas_stores : cottas_ondisk_loaded list)
    : S.dataset_backend =
  let in_memory_backend = S.indexed_dataset_backend in_memory in
  let cottas_backends =
    List.map (fun s -> S.cottas_ondisk_dataset_backend s.cod_store) cottas_stores
  in
  RDF_Store_Combine.combine_dataset_backends
    (in_memory_backend :: cottas_backends)

(* ============================================================================
   HTTP/1.1 request framing.

   The framing parser (request line + headers + body split, Content-Length
   bookkeeping) lives in F* (module SPARQL.HTTP, extracted as
   SPARQL_HTTP.ml). All that stays here is the socket-read glue that
   buffers bytes from [in_channel] up to a caller-supplied cap and hands
   the whole blob to [SPARQL_HTTP.parse_http_request].

   Size limits (see also the F* module):
     max_header_bytes = 64 KiB  — a request whose headers exceed this is
                                  rejected with 413 before we try to parse.
     max_body_bytes   = 10 MiB  — anti-DOS cap on request bodies.
   ============================================================================ *)

exception Bad_request of string  (* retained for legacy raise sites *)

(* Heth3 retired: the per-query wall-clock timeout was previously
   implemented as a SIGALRM-driven [Query_timeout] exception. The signal
   handler is process-global, which is architecturally wrong in a
   multi-threaded server (one thread's deadline could fire in another
   thread's context). The cooperative budget pattern in
   SPARQL.Eval.TimeBudget.fst is now the source of truth; the OCaml side
   constructs a budget value via [SPARQL_Eval_TimeBudget.mk_budget_secs]
   and consults [SPARQL_Eval_TimeBudget.poll] at the HTTP boundary. The
   exception type is retired with the SIGALRM machinery. See
   docs/designissues/2026-05-07-query-planning-fstar-recovery.md
   Phase 5. *)

let max_header_bytes = 65536
let max_body_bytes   = 10 * 1024 * 1024

(* Streaming-buffer wrappers. The byte-level decisions live in
   SPARQL.HTTP.fst (find_header_terminator_pos, ci_substring_index,
   extract_content_length); these shims only convert Buffer.t / int
   at the boundary. *)
let find_header_terminator (b : Buffer.t) : int =
  match SPARQL_HTTP.find_header_terminator_pos (Buffer.contents b) with
  | Some pos -> Z.to_int pos
  | None -> -1

let ci_find (s : string) (t : string) : int =
  match SPARQL_HTTP.ci_substring_index s t with
  | Some pos -> Z.to_int pos
  | None -> -1

let extract_content_length (s : string) (term : int) : int option =
  match SPARQL_HTTP.extract_content_length s (Z.of_int term) with
  | Some n when Z.fits_int n -> Some (Z.to_int n)
  | Some _ ->
    (* Content-Length is well-formed digits but the value doesn't fit
       OCaml's native int. Treat as malformed rather than letting
       Z.to_int raise Z.Overflow (which would crash the accept loop
       and turn an oversized header into a DoS). The phase-2 body
       reader caps reads at max_body_bytes anyway, so any sane
       Content-Length is far below int_max in practice. *)
    None
  | None -> None

(* Read bytes from [ic] until the HTTP header terminator is found or the
   header cap is exceeded. Then, if Content-Length is present and valid,
   read exactly that many more bytes (capped at max_body_bytes). Returns
   the full buffered request as a string.

   [input] returns the number of bytes actually read, which may be less
   than requested; that's fine — we just keep looping until either the
   structural terminator appears or the kernel tells us EOF. *)
let read_full_request ic ~max_header_bytes ~max_body_bytes =
  let chunk = 4096 in
  let buf = Buffer.create chunk in
  let b = Bytes.create chunk in
  let header_cap = max_header_bytes in
  let body_cap   = max_body_bytes in
  (* Phase 1: pull bytes until we find CRLFCRLF or exceed header_cap. *)
  let rec phase1 () =
    if Buffer.length buf >= header_cap then ()
    else
      let want = min chunk (header_cap + 4 - Buffer.length buf) in
      let want = if want < 1 then 1 else want in
      let got =
        try input ic b 0 want
        with End_of_file -> 0
      in
      if got = 0 then ()
      else begin
        Buffer.add_subbytes buf b 0 got;
        if find_header_terminator buf < 0 then phase1 ()
      end
  in
  phase1 ();
  (* Phase 2: if headers are present and Content-Length says more bytes,
     pull the rest. *)
  let term = find_header_terminator buf in
  if term < 0 then Buffer.contents buf
  else
    let s = Buffer.contents buf in
    let total_len = String.length s in
    let body_start = term + 4 in
    let already = if total_len > body_start then total_len - body_start else 0 in
    (match extract_content_length s term with
     | None -> ()  (* No Content-Length: nothing more to read. *)
     | Some n ->
       let need = n - already in
       let need = if need < 0 then 0 else need in
       let need = if need > body_cap then body_cap else need in
       let rec phase2 remaining =
         if remaining <= 0 then ()
         else
           let want = if remaining < chunk then remaining else chunk in
           let got =
             try input ic b 0 want
             with End_of_file -> 0
           in
           if got = 0 then ()
           else begin
             Buffer.add_subbytes buf b 0 got;
             phase2 (remaining - got)
           end
       in
       phase2 need);
    Buffer.contents buf

(* Case-insensitive header lookup — delegates to the F* implementation so
   the semantics match the parser that produced the list. *)
let header_value headers name =
  SPARQL_HTTP.header_lookup_ci headers name

(* ============================================================================
   HTTP response helpers.

   Status-line + common headers (Content-Type, Content-Length, Connection:
   close). Body is a byte-string; we pass it through unmodified.
   ============================================================================ *)

(* Reason phrase lookup lives in SPARQL.HTTP.Response. The F-star-extracted
   version takes Z.t (Prims.int); we cast at the boundary. *)
let status_text code = SPARQL_HTTP_Response.status_text (Z.of_int code)

(* [extra_headers] is a list of already-formatted "Name: value" lines (no CRLF)
   that are emitted between the standard headers and the body. CORS headers
   go here. Empty list = historical behaviour. *)
let write_response ?(extra_headers=[]) oc ~status ~content_type ~body =
  (* Response-head template lives in F* per rule #1; see
     SPARQL.HTTP.Response.render_response_head. *)
  let head =
    SPARQL_HTTP_Response.render_response_head
      (Z.of_int status) content_type (Z.of_int (String.length body)) extra_headers
  in
  output_string oc head;
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
(* Header-list construction lives in SPARQL.HTTP.Response. *)
let cors_headers ~(policy : cors_policy) ~(origin : string option) : string list =
  SPARQL_HTTP_Response.cors_headers policy origin

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

(* Extract variable list from a SELECT query.
   The "explicit projection" half (Select_Vars items) goes through the
   F*-verified SPARQL11_Algebra.select_item_vars (rule #1 — F* is the
   source of truth for SPARQL semantics). The star-projection fallback
   "collect distinct vars from the actual result rows in first-seen
   order" stays here as glue: it observes runtime data, doesn't make a
   semantic decision about what the SELECT clause projects. *)
let select_vars query results =
  match query.q_form with
  | QF_Select (Select_Vars items) ->
    SPARQL11_Algebra.select_item_vars items
  | _ ->
    (* #200 Section F: Hashtbl-based first-seen-order var collector
       moved to F* as `collect_distinct_vars_in_order` (commit 9597f84,
       SPARQL11.Algebra.fst). The list-mem dedup in the F* version is
       O(N*K) where K is the result var count; for typical < 50-var
       row widths this is observationally equivalent to the prior
       Hashtbl-based code. *)
    SPARQL11_Algebra.collect_distinct_vars_in_order results

(* Run the query and produce a response_body.
   F* evaluator does the work; we just pick serialiser + content type.

   Phase 2.5 (issue #100): SELECT/ASK go through the backend evaluator
   (S.eval_*_backend_dataset) so that --data-cottas dispatches into
   GB_CottasOnDisk without materialising the corpus in RAM. The
   evaluators return option (None for unsupported query forms); we
   surface that as an empty result rather than 500. *)
(* Qof3 defensive instrumentation stringifiers live in F*
   (SPARQL.Diagnostics). The OCaml side here is now a thin alias so
   the existing call sites in run_query / parse_and_run_timed don't
   have to change. Rule #1 / #15. *)
let qof3_graph_kind (g : S.graph_backend) : string =
  SPARQL_Diagnostics.graph_backend_kind_string g

let qof3_backend_kind (b : S.dataset_backend) : string =
  SPARQL_Diagnostics.dataset_backend_kind_string b

let qof3_query_form_str (q : SPARQL11_Algebra.query) : string =
  SPARQL_Diagnostics.query_form_string q

(* Build the standard 413 result-cap response. Used by run_query when the
   BGP/algebra evaluator returns more rows than the configured [max_rows]
   cap. The body is intentionally a tiny constant string — we never touch
   the oversized [rows] list (that's the whole point of bailing here:
   marshalling 3 M rows blows out the 544 KB pthread stack). *)
let _result_cap_response ~cap ~actual_size =
  Printf.eprintf
    "[tav5-trace] result-cap exceeded for query=<not-rendered, cap fired> \
     cap=%d actual_size=%d\n%!" cap actual_size;
  { rb_status = 413;
    rb_content_type = "application/json; charset=utf-8";
    rb_body = SPARQL_HTTP_Response.result_cap_response_body (Z.of_int cap) }

(* Row-cap circuit breaker (recovery plan Phase 5 — codename Tav5
   retired). The policy "stop after N rows" is defined in F* —
   see formal/fstar/SPARQL.Eval.Limits.fst — and instantiated here
   per request via [SPARQL_Eval_Limits.mk_cap]. The OCaml side is
   now thin glue: build the cap record, ask F* whether the row list
   reaches the cap, render the HTTP-413 response on overflow.

   The long-standing OCaml [exceeds_cap] semantics are strictly-greater
   (a result of exactly [cap] rows is allowed through; only
   [length > cap] triggers HTTP 413). The F* predicate [cap_reached]
   uses [n_rows >= max_rows] — i.e. it answers "is the cap reached?"
   given a row count. To encode strict overflow we pass [cap + 1] as
   the cap argument: [n >= cap + 1] iff [n > cap]. Wrapping it through
   F* keeps the policy under [SPARQL.Eval.Limits] and lets a future
   PR change the strict-vs-inclusive convention in one F* line.

   List.length is tail-rec in the OCaml stdlib, so this is safe to call
   on a 3 M-element list.

   Heth3 (per-query timeout) is a separate F* module
   ([SPARQL.Eval.TimeBudget]); the OCaml HTTP boundary consults it via
   [with_query_budget] / [SPARQL_Eval_TimeBudget.poll]. *)
let row_cap_of_int (cap : int) : SPARQL_Eval_Limits.row_cap =
  SPARQL_Eval_Limits.mk_cap (Z.of_int (max 0 cap))

let _exceeds_cap ~cap rows =
  if cap <= 0 then None
  else
    (* mk_cap (cap + 1) so [n >= cap + 1] iff [n > cap] (strict). *)
    let strict_overflow_cap = row_cap_of_int (cap + 1) in
    let n = List.length rows in
    if SPARQL_Eval_Limits.cap_reached strict_overflow_cap (Z.of_int n)
    then Some n
    else None

(* F*-defined truncation combinator, exposed for future call sites
   (streaming serialisers, paginated CONSTRUCT/DESCRIBE). The 413
   path above doesn't use it because we want to detect overflow
   rather than silently truncate; both behaviours sit under
   [SPARQL.Eval.Limits]. The [_] prefix suppresses OCaml's
   "unused let" warning until the first consumer lands. *)
let _take_capped_rows ~cap rows =
  SPARQL_Eval_Limits.take_capped (row_cap_of_int cap) rows

(* Convert the F*-typed `SPARQL_HTTP_Response.response_body` (with
   `nat`-encoded status, surfaced as `Z.t` in OCaml) into the local
   OCaml `response_body` record (`int`-encoded status). The two records
   have the same shape but different OCaml types because the local one
   predates the F* lift. Used by both `run_query` (Commit 2) and
   `parse_and_run_timed`'s error paths (Commit 3). *)
let convert_fstar_response_body (r : SPARQL_HTTP_Response.response_body)
  : response_body =
  { rb_status       = Z.to_int r.SPARQL_HTTP_Response.rb_status;
    rb_content_type = r.SPARQL_HTTP_Response.rb_content_type;
    rb_body         = r.SPARQL_HTTP_Response.rb_body }

(* #200 Section F Commit 2 (2026-05-13): the entire ASK / SELECT /
   CONSTRUCT / DESCRIBE dispatch + cap + serialiser-strategy + body
   assembly now lives in F* `SPARQL_HTTP_RunQuery.run_query`. The
   OCaml side reduces to: log, run the evaluator inside try/with for
   host-runtime exception capture (rule #11(c)), compute vars, hand
   the option to F*, convert the F*-typed response_body record to
   the locally-defined response_body record. The local OCaml record
   stays for one more commit so the ~10 unrelated `serve_*` helpers
   keep compiling; Commit 3 inlines them onto the F* type. *)
let run_query ~backend ~accept ~max_rows query =
  let bkind = qof3_backend_kind backend in
  let qfstr = qof3_query_form_str query in
  Printf.eprintf "[qof3] run_query: backend=%s form=%s max_rows=%d\n%!"
    bkind qfstr max_rows;
  let try_eval label thunk =
    try thunk () with e ->
      let bt = Printexc.get_backtrace () in
      Printf.eprintf "[qof3] %s raised: %s\n%s%!"
        label (Printexc.to_string e) bt;
      raise e
  in
  let to_some v = FStar_Pervasives_Native.Some v in
  let from_opt = function
    | FStar_Pervasives_Native.Some v -> Some v
    | FStar_Pervasives_Native.None   -> None
  in
  let ask_result, rows_result = match query.q_form with
    | QF_Ask ->
      Printf.eprintf "[qof3] calling S.eval_ask_query_backend_dataset (backend=%s)\n%!" bkind;
      let r = try_eval "eval_ask" (fun () ->
        from_opt (S.eval_ask_query_backend_dataset query backend))
      in
      Printf.eprintf "[qof3] eval_ask returned %s\n%!"
        (match r with Some v -> Printf.sprintf "Some %b" v | None -> "None");
      (r, None)
    | _ ->
      Printf.eprintf "[qof3] calling S.eval_select_query_backend_dataset (backend=%s, form=%s)\n%!"
        bkind qfstr;
      let r = try_eval "eval_select" (fun () ->
        from_opt (S.eval_select_query_backend_dataset query backend))
      in
      (match r with
       | Some rows -> Printf.eprintf "[qof3] eval_select returned Some %d rows\n%!" (List.length rows)
       | None -> Printf.eprintf "[qof3] eval_select returned None\n%!");
      (None, r)
  in
  let rows_for_vars = match rows_result with Some r -> r | None -> [] in
  let vars = select_vars query rows_for_vars in
  let fmt = response_format_of_accept accept in
  let ask_opt_z = match ask_result with Some v -> to_some v | None -> FStar_Pervasives_Native.None in
  let rows_opt_z = match rows_result with Some r -> to_some r | None -> FStar_Pervasives_Native.None in
  convert_fstar_response_body
    (SPARQL_HTTP_RunQuery.run_query
       query.q_form fmt (Z.of_int (max 0 max_rows)) vars ask_opt_z rows_opt_z)

(* ============================================================================
   Per-query timing instrumentation (2026-05-02).

   Goal: every SPARQL request produces a structured trace of where the wall
   clock went — parse, eval, format. Surfaces three ways:
     1. eprintf log line (always on, single line per query, easy to grep)
     2. X-Factoidal-Timing response header (machine-readable per-request)
     3. /admin/recent.json (last N queries, ring-buffered in memory)

   This is reporting glue, not semantic logic — it measures how long the
   F*-extracted entrypoints took, never decides anything. (Rule #11 OK.)
   ============================================================================ *)

type query_timing = {
  qt_parse_ms : float;     (* SPARQL11_Parser.parse_sparql wall time *)
  qt_eval_ms  : float;     (* eval_select / eval_ask wall time *)
  qt_format_ms : float;    (* serialise_response_* wall time *)
  qt_total_ms : float;     (* parse_and_run wall time (≈ sum + bookkeeping) *)
  qt_status : int;         (* HTTP status returned *)
  qt_rows : int;           (* rows in result set, -1 if unknown / ASK *)
  qt_form : string;        (* SELECT / ASK / CONSTRUCT / DESCRIBE / parse-error *)
  qt_body_bytes : int;     (* serialised body size *)
}

let zero_timing : query_timing = {
  qt_parse_ms = 0.0; qt_eval_ms = 0.0; qt_format_ms = 0.0;
  qt_total_ms = 0.0; qt_status = 0; qt_rows = -1;
  qt_form = "?"; qt_body_bytes = 0;
}

(* Format a single-line trace for stderr. Pattern keeps fields fixed-position
   so `grep '\[timing\]'` lines can be column-extracted by awk. *)
(* Per-query timing formatters — F* owns the output bytes
   (SPARQL.HTTP.Admin.fst per rule #1). The OCaml side handles the
   Printf "%.Nf" float-to-string conversion (F* has no equivalent
   FP formatter), and wraps the query text in OCaml-style quoting
   for the [timing] log line ("%S" -> Scanf-compatible quoted form). *)
let timing_log_line (qt : query_timing) (q_summary : string) : string =
  SPARQL_HTTP_Admin.render_timing_log_line
    qt.qt_form (Z.of_int qt.qt_status) (Z.of_int qt.qt_rows) (Z.of_int qt.qt_body_bytes)
    (Printf.sprintf "%.1f" qt.qt_parse_ms)
    (Printf.sprintf "%.1f" qt.qt_eval_ms)
    (Printf.sprintf "%.1f" qt.qt_format_ms)
    (Printf.sprintf "%.1f" qt.qt_total_ms)
    (Printf.sprintf "%S" q_summary)

(* Issue #266 security note: even when Server-Timing is on, round to
   whole milliseconds (no sub-millisecond resolution) so the header
   doesn't hand a requester more precision than the four documented
   stage names already concede. The eprintf log line and
   /admin/recent.json JSON (operator-only surfaces, not exposed to
   arbitrary browser clients) keep their finer-grained "%.1f" / "%.2f"
   formatting — only this response-header path is public. *)
let timing_response_header (qt : query_timing) : string =
  SPARQL_HTTP_Admin.render_timing_response_header
    (Printf.sprintf "%.0f" qt.qt_parse_ms)
    (Printf.sprintf "%.0f" qt.qt_eval_ms)
    (Printf.sprintf "%.0f" qt.qt_format_ms)
    (Printf.sprintf "%.0f" qt.qt_total_ms)

(* Effective on/off decision for --server-timing (issue #266). ST_On /
   ST_Off are unconditional; ST_Auto applies the deployment-shape
   heuristic from the flag's doc comment above [server_timing_mode]:
   off wherever an untrusted requester is plausible (per-user write
   sandboxing configured, CORS enabled for any origin, or the listener
   is not bound to loopback), on otherwise. *)
let server_timing_enabled (cfg : config) : bool =
  match cfg.server_timing with
  | ST_On -> true
  | ST_Off -> false
  | ST_Auto ->
    let looks_multi_tenant_or_tunnelled =
      cfg.proxied_auth_rw_graphnames <> None
      || cfg.cors <> CORS_Off
      || cfg.host <> "127.0.0.1"
    in
    not looks_multi_tenant_or_tunnelled

(* ----- Recent-query ring buffer ------------------------------------------- *)

type recent_query = {
  rq_started_at : float;       (* Unix epoch seconds *)
  rq_query_text : string;      (* truncated to 500 chars *)
  rq_timing : query_timing;
}

let recent_queries_mu = Mutex.create ()
let recent_queries : recent_query list ref = ref []
let recent_queries_cap = 50

let truncate_for_log : string -> int -> string =
  fun s n -> SPARQL_HTTP_Admin.truncate_for_log s (Z.of_int n)

let push_recent_query (rq : recent_query) =
  Mutex.lock recent_queries_mu;
  let trimmed =
    let rec take n = function
      | [] -> []
      | _ :: _ when n = 0 -> []
      | x :: xs -> x :: take (n - 1) xs
    in
    take recent_queries_cap (rq :: !recent_queries)
  in
  recent_queries := trimmed;
  Mutex.unlock recent_queries_mu

let snapshot_recent_queries () =
  Mutex.lock recent_queries_mu;
  let xs = !recent_queries in
  Mutex.unlock recent_queries_mu;
  xs

(* Aggregate counters: cumulative since process start. Useful for /admin/
   stats and for sanity-checking that timings are being recorded at all. *)
let total_queries_seen = ref 0
let total_query_wall_ms = ref 0.0
let queries_status_2xx = ref 0
let queries_status_4xx = ref 0
let queries_status_5xx = ref 0
let counters_mu = Mutex.create ()

let bump_counters (qt : query_timing) =
  Mutex.lock counters_mu;
  incr total_queries_seen;
  total_query_wall_ms := !total_query_wall_ms +. qt.qt_total_ms;
  (if qt.qt_status >= 200 && qt.qt_status < 300 then incr queries_status_2xx
   else if qt.qt_status >= 400 && qt.qt_status < 500 then incr queries_status_4xx
   else if qt.qt_status >= 500 then incr queries_status_5xx);
  Mutex.unlock counters_mu

(* JSON encoder for a recent_query. Strings escape via simple replacement of
   the characters JSON cares about: backslash, double-quote, newline,
   carriage return, and tab. Plus a generic \uXXXX escape for any other
   control character. Good enough for admin debug output; not a public
   format. *)
let json_string_escape s =
  let buf = Buffer.create (String.length s + 8) in
  String.iter (fun c ->
    match c with
    | '\\' -> Buffer.add_string buf "\\\\"
    | '"'  -> Buffer.add_string buf "\\\""
    | '\n' -> Buffer.add_string buf "\\n"
    | '\r' -> Buffer.add_string buf "\\r"
    | '\t' -> Buffer.add_string buf "\\t"
    | c when Char.code c < 0x20 ->
      Buffer.add_string buf (Printf.sprintf "\\u%04x" (Char.code c))
    | c -> Buffer.add_char buf c
  ) s;
  Buffer.contents buf

(* /admin/recent.json renderer — F* owns the JSON template
   (SPARQL.HTTP.Admin.fst per rule #1). The OCaml side keeps the
   ring buffer / counter Mutex protection (runtime mutable state =
   thin glue per rule #11(c)) and pre-formats the per-call float
   strings (OCaml Printf "%.Nf" semantics; F* has no equivalent
   formatter). *)
let recent_query_to_json (rq : recent_query) : string =
  SPARQL_HTTP_Admin.render_recent_query_json
    (Printf.sprintf "%.3f" rq.rq_started_at)
    (SPARQL_JSON_Escape.json_escape rq.rq_query_text)
    rq.rq_timing.qt_form
    (Z.of_int rq.rq_timing.qt_status)
    (Z.of_int rq.rq_timing.qt_rows)
    (Z.of_int rq.rq_timing.qt_body_bytes)
    (Printf.sprintf "%.2f" rq.rq_timing.qt_parse_ms)
    (Printf.sprintf "%.2f" rq.rq_timing.qt_eval_ms)
    (Printf.sprintf "%.2f" rq.rq_timing.qt_format_ms)
    (Printf.sprintf "%.2f" rq.rq_timing.qt_total_ms)

let serve_recent_queries_json () : response_body =
  let xs = snapshot_recent_queries () in
  Mutex.lock counters_mu;
  let total = !total_queries_seen in
  let total_wall = !total_query_wall_ms in
  let s2 = !queries_status_2xx in
  let s4 = !queries_status_4xx in
  let s5 = !queries_status_5xx in
  Mutex.unlock counters_mu;
  let body =
    SPARQL_HTTP_Admin.render_recent_queries_envelope
      (Z.of_int total)
      (Printf.sprintf "%.1f" total_wall)
      (Z.of_int s2) (Z.of_int s4) (Z.of_int s5)
      (List.map recent_query_to_json xs)
  in
  { rb_status = 200;
    rb_content_type = "application/json; charset=utf-8";
    rb_body = body }

(* Wrap a unit -> 'a thunk, return result paired with elapsed wall ms. *)
let timed (f : unit -> 'a) : 'a * float =
  let t0 = Unix.gettimeofday () in
  let r = f () in
  let dt_ms = (Unix.gettimeofday () -. t0) *. 1000.0 in
  (r, dt_ms)

(* /admin — built-in HTML dashboard. Polls /admin/recent.json every 2s
   and renders a live table of recent queries with stage bars. Embedded
   in this binary (not served from the demo dir) so it works regardless
   of which --web-demo was selected. Pure UI glue: no F* logic. *)
let admin_html_body : string =
  "<!doctype html>\n\
<html lang=\"en\"><head><meta charset=\"utf-8\">\n\
<title>factoidal admin — recent queries</title>\n\
<meta name=\"viewport\" content=\"width=device-width,initial-scale=1\">\n\
<style>\n\
:root{color-scheme:light dark;--ok:#4caf50;--warn:#ff9800;--err:#f44336;--mute:#888;--bar:#5b9dff}\n\
body{font:14px/1.45 system-ui,-apple-system,sans-serif;max-width:1200px;margin:1em auto;padding:0 1em}\n\
h1{margin:.2em 0}\n\
.stats{display:flex;gap:1.5em;flex-wrap:wrap;margin:.6em 0 1em}\n\
.stat{padding:.4em .7em;border:1px solid #ccc4;border-radius:6px;min-width:90px}\n\
.stat .label{font-size:11px;color:var(--mute);text-transform:uppercase;letter-spacing:.05em}\n\
.stat .num{font-size:1.4em;font-weight:600}\n\
.stat .num.warn{color:var(--warn)}\n\
.stat .num.err{color:var(--err)}\n\
.controls{margin:.5em 0;color:var(--mute);font-size:12px}\n\
table{border-collapse:collapse;width:100%;font-size:12px}\n\
th,td{text-align:left;padding:.35em .5em;border-bottom:1px solid #ccc4;vertical-align:top}\n\
th{font-size:11px;text-transform:uppercase;color:var(--mute);letter-spacing:.04em}\n\
td.q{font-family:ui-monospace,Menlo,Consolas,monospace;font-size:11.5px;max-width:480px;word-break:break-all}\n\
td.num{text-align:right;white-space:nowrap;font-variant-numeric:tabular-nums}\n\
.bars{display:grid;grid-template-columns:60px 1fr 50px;gap:.3em;align-items:center;margin:.1em 0;font-size:11px}\n\
.bars .lbl{color:var(--mute);text-align:right}\n\
.bars .bar{height:8px;background:var(--bar);border-radius:1px;min-width:1px}\n\
.bars .v{text-align:right;font-variant-numeric:tabular-nums;color:var(--mute)}\n\
.status-2xx{color:var(--ok)}\n\
.status-4xx{color:var(--warn)}\n\
.status-5xx{color:var(--err)}\n\
footer{margin-top:1.5em;color:var(--mute);font-size:11px}\n\
@media(prefers-color-scheme:dark){.stat{border-color:#5556}}\n\
</style></head><body>\n\
<h1>factoidal — recent queries</h1>\n\
<div class=\"stats\" id=\"stats\">\n\
  <div class=\"stat\"><div class=\"label\">total queries</div><div class=\"num\" id=\"s-total\">…</div></div>\n\
  <div class=\"stat\"><div class=\"label\">total wall</div><div class=\"num\" id=\"s-wall\">…</div></div>\n\
  <div class=\"stat\"><div class=\"label\">2xx</div><div class=\"num status-2xx\" id=\"s-2xx\">…</div></div>\n\
  <div class=\"stat\"><div class=\"label\">4xx</div><div class=\"num status-4xx\" id=\"s-4xx\">…</div></div>\n\
  <div class=\"stat\"><div class=\"label\">5xx</div><div class=\"num status-5xx\" id=\"s-5xx\">…</div></div>\n\
  <div class=\"stat\"><div class=\"label\">avg total</div><div class=\"num\" id=\"s-avg\">…</div></div>\n\
</div>\n\
<div class=\"controls\">\n\
  Auto-refreshing every 2 s. <span id=\"last-update\"></span>\n\
  <a href=\"/admin/recent.json\" style=\"margin-left:1em\">raw JSON</a>\n\
  <a href=\"/backend-info.json\" style=\"margin-left:1em\">/backend-info.json</a>\n\
  <a href=\"/\" style=\"margin-left:1em\">SPARQL playground</a>\n\
</div>\n\
<table id=\"q\"><thead><tr>\n\
  <th>when</th><th>form</th><th>status</th>\n\
  <th>parse / eval / format</th>\n\
  <th class=\"num\">total</th>\n\
  <th class=\"num\">body</th>\n\
  <th>query</th>\n\
</tr></thead><tbody></tbody></table>\n\
<footer>Built into factoidal-http. Last 50 queries, ring-buffered in process memory. Query text truncated to 500 chars.</footer>\n\
<script>\n\
function fmtMs(ms){if(ms==null)return '—';if(ms<1)return '<1 ms';if(ms<1000)return ms.toFixed(0)+' ms';return (ms/1000).toFixed(2)+' s'}\n\
function fmtBytes(n){if(n==null)return '';if(n<1024)return n+' B';if(n<1048576)return (n/1024).toFixed(1)+' KB';return (n/1048576).toFixed(2)+' MB'}\n\
function fmtTime(ts){const d=new Date(ts*1000);return d.toLocaleTimeString()}\n\
function statusClass(s){if(s>=500)return 'status-5xx';if(s>=400)return 'status-4xx';return 'status-2xx'}\n\
function bar(label,ms,maxMs){const w=Math.max(1,Math.round(220*ms/Math.max(1,maxMs)));return `<div class='bars'><span class='lbl'>${label}</span><span class='bar' style='width:${w}px'></span><span class='v'>${fmtMs(ms)}</span></div>`}\n\
async function tick(){\n\
  let d;try{d=await(await fetch('/admin/recent.json',{cache:'no-store'})).json()}catch(e){return}\n\
  document.getElementById('s-total').textContent=d.total_queries_seen;\n\
  document.getElementById('s-wall').textContent=fmtMs(d.total_wall_ms);\n\
  document.getElementById('s-2xx').textContent=d.status_2xx;\n\
  document.getElementById('s-4xx').textContent=d.status_4xx;\n\
  document.getElementById('s-5xx').textContent=d.status_5xx;\n\
  const avg=d.total_queries_seen>0?d.total_wall_ms/d.total_queries_seen:0;\n\
  document.getElementById('s-avg').textContent=fmtMs(avg);\n\
  document.getElementById('last-update').textContent='Updated '+new Date().toLocaleTimeString();\n\
  const maxMs=Math.max(1,...d.recent.map(r=>r.total_ms));\n\
  const tb=document.querySelector('#q tbody');\n\
  tb.innerHTML=d.recent.map(r=>{\n\
    const stages=bar('parse',r.parse_ms,maxMs)+bar('eval',r.eval_ms,maxMs)+bar('format',r.format_ms,maxMs);\n\
    const qEsc=r.query.replace(/[<>&]/g,c=>({'<':'&lt;','>':'&gt;','&':'&amp;'}[c]));\n\
    return `<tr><td>${fmtTime(r.started_at)}</td><td>${r.form}</td><td class='${statusClass(r.status)}'>${r.status}</td><td>${stages}</td><td class='num'>${fmtMs(r.total_ms)}</td><td class='num'>${fmtBytes(r.body_bytes)}</td><td class='q'>${qEsc}</td></tr>`;\n\
  }).join('');\n\
}\n\
tick();setInterval(tick,2000);\n\
</script></body></html>\n"

let serve_admin_html () : response_body =
  { rb_status = 200;
    rb_content_type = "text/html; charset=utf-8";
    rb_body = admin_html_body }

(* parse_and_run with explicit per-stage timings. Returns the response
   alongside a query_timing record.

   #200 Section F Commit 3 (2026-05-13): the parse-error and eval-error
   response bodies are built via the F* `make_parse_error_response` /
   `make_eval_error_response` constructors in `SPARQL.HTTP.RunQuery`,
   then converted to the local OCaml `response_body` via
   `convert_fstar_response_body`. The error-status / content-type /
   body string are 100% owned by F*; the OCaml side here just times,
   logs, and converts.

   Pre-Commit 3 inline status+body assembly is gone. *)

let parse_and_run_timed ~backend ~accept ~max_rows query_text =
  let t_total_start = Unix.gettimeofday () in
  Printf.eprintf "[qof3] parse_and_run_timed: %d bytes of query text\n%!"
    (String.length query_text);
  let (parse_result, parse_ms) =
    timed (fun () -> SPARQL11_Parser.parse_sparql query_text) in
  match parse_result with
  | SPARQL11_Parser.ParseErr msg ->
    Printf.eprintf "[qof3] parse_and_run_timed: SPARQL parse error: %s\n%!" msg;
    let total_ms = (Unix.gettimeofday () -. t_total_start) *. 1000.0 in
    let resp =
      convert_fstar_response_body
        (SPARQL_HTTP_RunQuery.make_parse_error_response msg) in
    let qt = { zero_timing with
               qt_parse_ms = parse_ms; qt_total_ms = total_ms;
               qt_status = resp.rb_status; qt_form = "parse-error";
               qt_body_bytes = String.length resp.rb_body } in
    (resp, qt)
  | SPARQL11_Parser.ParseOk (query, _tokens) ->
    Printf.eprintf "[qof3] parse_and_run_timed: parsed OK in %.1fms, dispatching run_query\n%!"
      parse_ms;
    let form = qof3_query_form_str query in
    (try
       (* run_query bundles eval + format. We can't split them without
          touching its signature; the eval cost dominates format on every
          query we've seen, so reporting the sum as eval_ms and leaving
          format_ms = 0.0 is acceptable for v1. Future: split run_query
          into eval + format halves and stamp both. *)
       let (r, run_ms) =
         timed (fun () -> run_query ~backend ~accept ~max_rows query) in
       let total_ms = (Unix.gettimeofday () -. t_total_start) *. 1000.0 in
       Printf.eprintf "[qof3] parse_and_run_timed: run_query returned status=%d body_bytes=%d in %.1fms\n%!"
         r.rb_status (String.length r.rb_body) run_ms;
       let qt = { qt_parse_ms = parse_ms;
                  qt_eval_ms = run_ms;
                  qt_format_ms = 0.0;
                  qt_total_ms = total_ms;
                  qt_status = r.rb_status;
                  qt_rows = -1;
                  qt_form = form;
                  qt_body_bytes = String.length r.rb_body } in
       (r, qt)
     with
     | e ->
       let bt = Printexc.get_backtrace () in
       Printf.eprintf "[qof3] parse_and_run_timed: run_query raised: %s\n%s%!"
         (Printexc.to_string e) bt;
       let total_ms = (Unix.gettimeofday () -. t_total_start) *. 1000.0 in
       let resp =
         convert_fstar_response_body
           (SPARQL_HTTP_RunQuery.make_eval_error_response (Printexc.to_string e) bt) in
       let qt = { qt_parse_ms = parse_ms;
                  qt_eval_ms = (total_ms -. parse_ms);
                  qt_format_ms = 0.0;
                  qt_total_ms = total_ms;
                  qt_status = resp.rb_status;
                  qt_rows = -1;
                  qt_form = form;
                  qt_body_bytes = String.length resp.rb_body } in
       (resp, qt))

let parse_and_run ~backend ~accept ~max_rows query_text =
  let (r, _qt) = parse_and_run_timed ~backend ~accept ~max_rows query_text in
  r

(* Build the standard 504 Gateway Timeout body when a query exceeds the
   configured wall-clock budget. The JSON body shape is owned by
   SPARQL.HTTP.Response.fst (rule #1). *)
let query_timeout_response ~secs =
  { rb_status = 504;
    rb_content_type = "application/json; charset=utf-8";
    rb_body = SPARQL_HTTP_Response.query_timeout_response_body (Z.of_int secs) }

(* Heth3 cooperative budget shim. Replaces the SIGALRM-based
   [with_query_timeout] (process-global, wrong for a multi-threaded
   server). The OCaml side here is a thin dispatcher: build the budget
   in F* via [SPARQL_Eval_TimeBudget.mk_budget_secs], hand it to the
   continuation [f], and let the caller decide whether to consult
   [SPARQL_Eval_TimeBudget.poll] post-eval (or, in a future change that
   threads the budget through the F* evaluator, between yield points).

   No semantic decision is taken here — everything (deadline arithmetic,
   wallclock read, expiry test) lives in F*. Iron Rule #11.

   secs <= 0 is the project-wide convention for "disabled"; F*
   [mk_budget_secs 0] returns the disabled-budget sentinel
   ([is_disabled = true], [poll = false] always). *)
let with_query_budget
    ~secs
    (f : SPARQL_Eval_TimeBudget.budget -> 'a) : 'a =
  let secs_z = Z.of_int (max 0 secs) in
  let b = SPARQL_Eval_TimeBudget.mk_budget_secs secs_z in
  f b

(* ============================================================================
   Per-connection handling.

   Each connection reads exactly one HTTP request, answers it, then closes.
   Socket errors are logged but never crash the accept loop.
   ============================================================================ *)

(* Detect whether an update contains any U_Load op (LOAD is still
   unimplemented — needs HTTP client).  We return 501 for requests
   that contain LOAD rather than silently skipping it. *)
(* update_has_load lives in F* per rule #1; see
   formal/fstar/SPARQL.Update.Analysis.fst. *)
let update_has_load : SPARQL11_Algebra.sparql_update -> bool =
  SPARQL_Update_Analysis.update_has_load

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

(* string_replace_all lives in F* per rule #1
   (formal/fstar/SPARQL.Update.Sandbox.fst). The local copy here
   duplicated that logic; replaced with a thin alias. *)
let string_replace_all ~needle ~replacement haystack =
  SPARQL_Update_Sandbox.string_replace_all needle replacement haystack

(* Thin OCaml dispatch shims around the verified F-star sandbox module.
   The semantic policy (graph-target rewriting, alias expansion, accept/
   reject decisions) lives in formal/fstar/SPARQL.Update.Sandbox.fst per
   CLAUDE.md rule #1. Do not re-add OCaml-side semantic logic here. *)
let expand_user_graph ~template ~authid =
  SPARQL_Update_Sandbox.expand_user_graph template authid

(* template_prefix is implemented in F-star (SPARQL.Update.Sandbox.fst);
   this OCaml shim is a thin re-export so existing call sites are
   unchanged. CLAUDE.md rule #1. *)
let template_prefix template = SPARQL_Update_Sandbox.template_prefix template

(* Sandbox checking is implemented in F-star; this OCaml file only
   converts at the boundary. See SPARQL.Update.Sandbox.fst. *)
type sandbox_result =
  | SB_Ok of SPARQL11_Algebra.update_op
  | SB_Reject of string  (* human-readable reason *)

(* Sandbox-check one update op. Returns SB_Ok (rewritten op) or SB_Reject msg.
   This is a one-line dispatch through the verified F-star module. *)
let sandbox_op ~usergraph (op : SPARQL11_Algebra.update_op) : sandbox_result =
  match SPARQL_Update_Sandbox.sandbox_op usergraph op with
  | SPARQL_Update_Sandbox.SB_Ok op' -> SB_Ok op'
  | SPARQL_Update_Sandbox.SB_Reject msg -> SB_Reject msg

(* Sandbox-check and rewrite a whole sparql_update. Returns either the
   rewritten update or an error message identifying the first offending op. *)
let sandbox_update ~usergraph (u : SPARQL11_Algebra.sparql_update) :
  (SPARQL11_Algebra.sparql_update, string) result =
  match SPARQL_Update_Sandbox.sandbox_update usergraph u with
  | SPARQL_Update_Sandbox.USR_Ok u' -> Ok u'
  | SPARQL_Update_Sandbox.USR_Error msg -> Error msg

(* ============================================================================
   N-Quads emitter — inline, for dump-on-exit.

   We don't have an F*-extracted N-Quads serialiser today. The output shape
   is the standard N-Quads line:
       <s> <p> <o> <g> .
   Literals are quoted with proper escaping. Blank nodes are "_:id".
   ============================================================================ *)

(* N-Quads wire-format serializers — F* is the source of truth.
   formal/fstar/RDF.NQuads.Serialize.fst owns the byte-correct
   escape/term/subject/line rendering. *)
let nq_escape_literal : string -> string =
  RDF_NQuads_Serialize.nq_escape_literal
let nq_term_to_string : rdf_term -> string =
  RDF_NQuads_Serialize.nq_term_to_string
let nq_subject_to_string : subject -> string =
  RDF_NQuads_Serialize.nq_subject_to_string
let nq_line_for_triple ~graph_iri (t : triple) : string =
  RDF_NQuads_Serialize.nq_line_for_triple graph_iri t

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

(* ============================================================================
   Landing page + bundled web component.

   Pure I/O glue (rule #15): the dispatch decision "/ is HTML, /sparql is
   the SPARQL Protocol endpoint" is an HTTP routing concern and lives here,
   not in the F* protocol logic.

   The HTML page mounts <factoidal-sparql-client endpoint="/sparql"> —
   the same web component shipped in the static demos — talking to this
   server's own /sparql via the SPARQL 1.1 Protocol (Aleph3's remote-
   endpoint mode, commit 56ab457). On load, the page fetches
   /parliament-queries.json and assigns the array to the component's
   `queries` property; the component renders them as a sample-query
   dropdown above its textarea. No bespoke fetch code lives in the
   landing page — the W3C Protocol client is the component itself.
   ============================================================================ *)

(* Resolve the on-disk location of the factoidal-sparql-client.js bundle.
   We try a small list of candidates derived from the executable's
   directory and CWD, returning the first that exists. None = bundle not
   found, which leads to a 404 with a helpful message. *)
let resolve_component_bundle () : string option =
  let exe_dir =
    try Filename.dirname (Unix.realpath Sys.argv.(0))
    with _ -> Filename.dirname Sys.argv.(0)
  in
  let cwd = try Sys.getcwd () with _ -> "." in
  let rel = "docs/fstar-extracted/factoidal-sparql-client.js" in
  let candidates = [
    Filename.concat exe_dir "factoidal-sparql-client.js";
    Filename.concat exe_dir (Filename.concat ".." rel);
    Filename.concat exe_dir (Filename.concat "../.." rel);
    Filename.concat exe_dir (Filename.concat "../../.." rel);
    Filename.concat cwd rel;
    Filename.concat cwd "factoidal-sparql-client.js";
  ] in
  List.find_opt Sys.file_exists candidates

(* Read the bundle into memory. We do not cache; the server is single-
   threaded and the bundle is ~54 KB — reading it per-request keeps the
   logic trivial and avoids stale-after-edit confusion in dev. *)
let serve_component_bundle () : response_body =
  match resolve_component_bundle () with
  | None ->
    { rb_status = 404;
      rb_content_type = "text/plain; charset=utf-8";
      rb_body =
        "factoidal-sparql-client.js bundle not found.\n\
         Searched paths derived from argv[0] and CWD; expected at\n\
         docs/fstar-extracted/factoidal-sparql-client.js.\n" }
  | Some path ->
    (try
       let body = read_file path in
       { rb_status = 200;
         rb_content_type = "application/javascript; charset=utf-8";
         rb_body = body }
     with e ->
       { rb_status = 500;
         rb_content_type = "text/plain; charset=utf-8";
         rb_body = "error reading bundle: " ^ Printexc.to_string e ^ "\n" })

(* Per-dataset web demo (rule #15: pure I/O glue).

   The landing UI used to be a single inline OCaml string. It now lives as
   static files under [docs/web/], so UI tweaks don't require recompiling
   factoidal-http. Selection is via [--web-demo]:

     None         -> docs/web/landing/   (generic SPARQL playground)
     Some "id"    -> docs/web/demos/<id>/ (resolved relative to repo root)
     Some "/abs"  -> /abs                 (absolute path served as-is)

   The chosen directory is served as a recursive static-file tree at GET /.
   /sparql, /factoidal-sparql-client.js, /parliament-queries.json,
   /backend-info.json continue to be handled by their dedicated routes
   (the demo HTML fetches them).

   IGNORED: holes in F* logic do not belong here. This module's job is
   filesystem -> bytes -> response_body, nothing more. *)

(* Pick a list of plausible on-disk locations for the configured demo
   directory and return the first that exists. Mirrors the search order
   in [resolve_component_bundle] / [resolve_parliament_dir] so it works
   from the repo root, from ocaml-output/, or from bin/<platform>/. *)
let resolve_web_demo_dir (demo : string option) : string option =
  let exe_dir =
    try Filename.dirname (Unix.realpath Sys.argv.(0))
    with _ -> Filename.dirname Sys.argv.(0)
  in
  let cwd = try Sys.getcwd () with _ -> "." in
  let rels = match demo with
    | None ->
        ["docs/web/landing"]
    | Some s when String.length s > 0 && s.[0] = '/' ->
        [s]  (* absolute path: try as-is *)
    | Some id ->
        ["docs/web/demos/" ^ id]
  in
  let candidates =
    List.concat_map (fun rel ->
      if String.length rel > 0 && rel.[0] = '/' then [rel]
      else [
        Filename.concat exe_dir (Filename.concat ".." rel);
        Filename.concat exe_dir (Filename.concat "../.." rel);
        Filename.concat exe_dir (Filename.concat "../../.." rel);
        Filename.concat exe_dir (Filename.concat "../../../.." rel);
        Filename.concat cwd rel;
      ]
    ) rels
  in
  List.find_opt (fun p ->
    try Sys.is_directory p with _ -> false) candidates

(* Cheap content-type sniff by filename suffix. We deliberately keep the
   table small — the demos only ship HTML/JS/CSS/JSON/SVG/PNG today. *)
(* Static-file content-type mapping and path-traversal guard live in
   F* per rule #1 (formal/fstar/SPARQL.HTTP.StaticFiles.fst); the
   OCaml side is the read/stat syscalls. *)
let content_type_for_path : string -> string =
  SPARQL_HTTP_StaticFiles.content_type_for_path

let path_has_dotdot : string -> bool =
  SPARQL_HTTP_StaticFiles.path_has_dotdot

(* Strip a leading slash from URL path. *)
let strip_leading_slash s =
  if String.length s > 0 && s.[0] = '/'
    then String.sub s 1 (String.length s - 1)
  else s

(* Resolve [/foo/bar] inside [root] to a full filesystem path, mapping
   "/" and "/<dir>/" to "/<dir>/index.html". Returns None if the path
   contains ".." or the resulting file does not exist. *)
let resolve_demo_file (root : string) (url_path : string) : string option =
  if path_has_dotdot url_path then None
  else
    let rel = strip_leading_slash url_path in
    let rel = if rel = "" then "index.html" else rel in
    let p = Filename.concat root rel in
    let p =
      if (try Sys.is_directory p with _ -> false)
      then Filename.concat p "index.html" else p
    in
    if (try Sys.file_exists p && not (Sys.is_directory p)
        with _ -> false) then Some p else None

(* Serve a single static file from the configured demo directory.
   - demo dir not found -> 404 plaintext pointing at --web-demo
   - file not found     -> 404 plaintext
   - read error         -> 500 plaintext *)
let serve_static_demo ~cfg (url_path : string) : response_body =
  match resolve_web_demo_dir cfg.web_demo with
  | None ->
    let id = match cfg.web_demo with
      | None -> "(default: docs/web/landing)"
      | Some s -> s in
    { rb_status = 404;
      rb_content_type = "text/plain; charset=utf-8";
      rb_body =
        "Web demo directory not found: " ^ id ^
        ". Pass --web-demo=<id-or-path> (see docs/web/demos/).\n" }
  | Some root ->
    (match resolve_demo_file root url_path with
     | None ->
       { rb_status = 404;
         rb_content_type = "text/plain; charset=utf-8";
         rb_body = "Not found: " ^ url_path ^ "\n" }
     | Some p ->
       try
         let body = read_file p in
         { rb_status = 200;
           rb_content_type = content_type_for_path p;
           rb_body = body }
       with e ->
         { rb_status = 500;
           rb_content_type = "text/plain; charset=utf-8";
           rb_body = "error reading " ^ p ^ ": " ^ Printexc.to_string e ^ "\n" })


(* ----- /parliament-queries.json --------------------------------------------
   Build a JSON manifest of the 24 vendored UK Parliament SPARQL queries
   in third_party/data/ukparliament/sparql/{main,detail}/*.rq. Pure I/O
   glue (rule #15): we just walk the directory, read each file's bytes,
   and emit JSON. The web component on /  consumes the manifest as
   [{key, label, body}, ...].

   Resolution mirrors resolve_component_bundle: try a few argv[0]/CWD-
   relative paths so the binary works whether invoked from the repo root,
   from ocaml-output/, or from an installed location. *)
let resolve_parliament_dir () : string option =
  let exe_dir =
    try Filename.dirname (Unix.realpath Sys.argv.(0))
    with _ -> Filename.dirname Sys.argv.(0)
  in
  let cwd = try Sys.getcwd () with _ -> "." in
  let rel = "third_party/data/ukparliament/sparql" in
  let candidates = [
    Filename.concat exe_dir (Filename.concat ".." rel);
    Filename.concat exe_dir (Filename.concat "../.." rel);
    Filename.concat exe_dir (Filename.concat "../../.." rel);
    Filename.concat exe_dir (Filename.concat "../../../.." rel);
    Filename.concat cwd rel;
  ] in
  List.find_opt (fun p ->
    try Sys.is_directory p with _ -> false) candidates

(* JSON string escaper — dispatched to F*-extracted SPARQL.JSON.Escape
   per CLAUDE.md rule #1 (factoidal_http.ml unwind step 1).
   See SPARQL.JSON.Escape.fst for the verification surface (the algorithm
   is verified in F*; the byte primitives are assume-val glue). *)
let json_escape (s : string) : string =
  SPARQL_JSON_Escape.json_escape s

(* Strip the .rq suffix and return "<group> / <stem>". Dispatched to
   F-star-extracted SPARQL.HTTP.QueriesIndex.parliament_label per
   CLAUDE.md rule #1 (factoidal_http.ml unwind step 4). *)
let parliament_label ~group ~filename : string =
  SPARQL_HTTP_QueriesIndex.parliament_label group filename

(* Walk one of the {main,detail} subdirectories, collecting (key, label,
   body) for every .rq file. Files that fail to read are skipped silently
   — a malformed/locked file shouldn't break the dropdown for the others. *)
let parliament_entries_for_group (root : string) (group : string)
    : (string * string * string) list =
  let dir = Filename.concat root group in
  let entries =
    try Sys.readdir dir with _ -> [||]
  in
  Array.sort compare entries;
  Array.fold_left (fun acc name ->
    if Filename.check_suffix name ".rq" then
      let path = Filename.concat dir name in
      try
        let body = read_file path in
        let key = group ^ "/" ^ Filename.chop_suffix name ".rq" in
        let label = parliament_label ~group ~filename:name in
        (key, label, body) :: acc
      with _ -> acc
    else acc
  ) [] entries
  |> List.rev

(* He2's modernised queries (commit cf22aad) live alongside the repo,
   not under third_party/. The directory layout mirrors third_party's:
     tools/sample-queries/ukparliament/{main,detail}/*_modern.rq
   Resolution mirrors resolve_parliament_dir — try a few argv[0]/CWD-
   relative paths so the binary works whether invoked from the repo
   root, ocaml-output/, or an installed location. *)
let resolve_modern_queries_dir () : string option =
  let exe_dir =
    try Filename.dirname (Unix.realpath Sys.argv.(0))
    with _ -> Filename.dirname Sys.argv.(0)
  in
  let cwd = try Sys.getcwd () with _ -> "." in
  let rel = "tools/sample-queries/ukparliament" in
  let candidates = [
    Filename.concat exe_dir (Filename.concat ".." rel);
    Filename.concat exe_dir (Filename.concat "../.." rel);
    Filename.concat exe_dir (Filename.concat "../../.." rel);
    Filename.concat exe_dir (Filename.concat "../../../.." rel);
    Filename.concat cwd rel;
  ] in
  List.find_opt (fun p ->
    try Sys.is_directory p with _ -> false) candidates

(* Walk one of the {main,detail} subdirectories under the modernised-
   queries root, collecting (key, label, body) for every file ending in
   _modern.rq. We deliberately filter on the _modern suffix so a future
   sibling of vendored queries in the same tree won't bleed in. *)
let modern_entries_for_group (root : string) (group : string)
    : (string * string * string) list =
  let dir = Filename.concat root group in
  let entries =
    try Sys.readdir dir with _ -> [||]
  in
  Array.sort compare entries;
  Array.fold_left (fun acc name ->
    let is_modern =
      Filename.check_suffix name ".rq"
      && (let stem = Filename.chop_suffix name ".rq" in
          let n = String.length stem in
          n >= 7 && String.sub stem (n - 7) 7 = "_modern")
    in
    if is_modern then
      let path = Filename.concat dir name in
      try
        let body = read_file path in
        let stem = Filename.chop_suffix name ".rq" in
        let key = "modern/" ^ group ^ "/" ^ stem in
        let label = "Modernised \xe2\x80\x94 " ^ group ^ " / " ^ stem in
        (key, label, body) :: acc
      with _ -> acc
    else acc
  ) [] entries
  |> List.rev

(* Build the JSON array as a string. We emit one line per object; ~32 KB
   total once the modernised queries are folded in. The component re-
   reads this on every page load, so He2's modernisations to the .rq
   files surface naturally.

   Each entry carries a `group` field ("Vendored" / "Modernised") so a
   future component upgrade can render <optgroup>s. The current component
   ignores extra fields, so this is forward-compatible. The label is
   prefixed too so the existing flat dropdown still groups visually. *)
(* The OCaml side keeps Sys.readdir + read_file (pure I/O glue, rule #15).
   The JSON shape is rendered by F-star-extracted
   SPARQL.HTTP.QueriesIndex.render_queries_index per CLAUDE.md rule #1
   (factoidal_http.ml unwind step 4). Output is byte-for-byte identical
   to the previous Buffer-based emission. *)
let build_parliament_queries_json () : string =
  let to_entry (group : string) (key : string) (label : string) (body : string)
    : SPARQL_HTTP_QueriesIndex.query_entry =
    { qe_group = group; qe_key = key; qe_label = label; qe_body = body }
  in
  let vendored =
    match resolve_parliament_dir () with
    | None -> []
    | Some root ->
      let main = parliament_entries_for_group root "main" in
      let detail = parliament_entries_for_group root "detail" in
      List.map (fun (k, l, b) ->
        to_entry "Vendored" k ("Vendored \xe2\x80\x94 " ^ l) b)
        (main @ detail)
  in
  let modernised =
    match resolve_modern_queries_dir () with
    | None -> []
    | Some root ->
      let main = modern_entries_for_group root "main" in
      let detail = modern_entries_for_group root "detail" in
      List.map (fun (k, l, b) -> to_entry "Modernised" k l b)
        (main @ detail)
  in
  SPARQL_HTTP_QueriesIndex.render_queries_index (vendored @ modernised)

let serve_parliament_queries_json () : response_body =
  try
    let body = build_parliament_queries_json () in
    { rb_status = 200;
      rb_content_type = "application/json; charset=utf-8";
      rb_body = body }
  with e ->
    { rb_status = 500;
      rb_content_type = "text/plain; charset=utf-8";
      rb_body = "error building parliament queries: "
                ^ Printexc.to_string e ^ "\n" }

(* ----- /backend-info.json --------------------------------------------------
   Self-describing record so the landing-page JS can render a "Backend:
   ... (N triples)" pill. Pure I/O glue (rule #15): we just look at the
   config + the current dataset_ref and serialise. The "kind" is
   determined entirely by which command-line flags were used:

     --dataset only          -> "in-memory"
     --data-cottas only      -> "binary"
     both                    -> "mixed"
     neither                 -> "empty"

   `triples` is a live count over the current ref (post-UPDATE); it's
   List.length on an in-memory immutable graph, fast enough for a UI
   pill at our dataset sizes. *)
(* Dataset triple-count + backend-kind classification — F* is the
   source of truth (formal/fstar/SPARQL.HTTP.BackendInfo.fst). *)
let count_dataset_triples (ds : rdf_dataset) : int * int * int * int =
  let (a, b, c, d) = SPARQL_HTTP_BackendInfo.count_dataset_triples ds in
  (Z.to_int a, Z.to_int b, Z.to_int c, Z.to_int d)

let backend_kind_of_cfg (cfg : config) : SPARQL_HTTP_BackendInfo.backend_kind =
  SPARQL_HTTP_BackendInfo.backend_kind_of_flags
    (cfg.dataset_file <> None)
    (cfg.data_cottas_files <> [])

(* Source-mounted-paths display string — F* owns the format decisions
   (separator, "(none)" placeholder, dataset-before-cottas ordering);
   OCaml supplies the path basenames. See SPARQL.HTTP.BackendInfo.fst. *)
let backend_source_string (cfg : config) : string =
  let dataset_bn =
    match cfg.dataset_file with
    | Some f -> FStar_Pervasives_Native.Some (Filename.basename f)
    | None -> FStar_Pervasives_Native.None
  in
  let cottas_bns = List.map Filename.basename cfg.data_cottas_files in
  SPARQL_HTTP_BackendInfo.backend_source_string dataset_bn cottas_bns

(* Build a per-store cottas_summary list for the backend_info record.
   Pure I/O glue: read whatever the F-star-extracted summary getter
   gives us and forward the fields. Stores whose summary is absent
   (cottas_ondisk_open should always populate cods_summary, but be
   defensive) contribute 0 / 0 — same accounting the previous
   sum-only path used. *)
let cottas_stores_summaries (stores : cottas_ondisk_loaded list)
    : SPARQL_HTTP_BackendInfo.cottas_summary list =
  List.map (fun s ->
    let (n_quads, n_rg) =
      match RDF_CottasStore.cottas_ondisk_summary s.cod_store with
      | FStar_Pervasives_Native.Some summ ->
        (Z.to_int summ.Parser_BallyhooCOTTAS.cas_num_quads,
         Z.to_int summ.Parser_BallyhooCOTTAS.cas_num_row_groups)
      | FStar_Pervasives_Native.None -> (0, 0)
    in
    { SPARQL_HTTP_BackendInfo.cs_path = s.cod_path;
      SPARQL_HTTP_BackendInfo.cs_quads = Z.of_int n_quads;
      SPARQL_HTTP_BackendInfo.cs_row_groups = Z.of_int n_rg }
  ) stores

(* /backend-info.json. Reports the union of in-memory dataset_ref AND
   open cottas-ondisk stores — both feed backend_ref, which is the
   actual query-time view. Earlier versions only counted dataset_ref,
   so a --data-cottas-only daemon advertised "kind":"binary" with
   "triples":0, despite COUNT-star returning 3.14M. Reviewer flagged
   2026-04-26.

   The aggregation rule (sum, not max, not first) and the JSON shape
   are now owned by F-star — see SPARQL.HTTP.BackendInfo.fst. This
   function is reduced to pure I/O glue: deref the live state, pack a
   `backend_info` record, ask the F-star renderer for the bytes. *)
let serve_backend_info_json
    (cfg : config)
    (dataset_ref : rdf_dataset ref)
    (cottas_stores_ref : cottas_ondisk_loaded list ref)
    : response_body =
  try
    let ds = !dataset_ref in
    let stores = !cottas_stores_ref in
    let (in_mem_total, in_mem_dflt, in_mem_ng_count, in_mem_ng_triples) =
      count_dataset_triples ds in
    let bi : SPARQL_HTTP_BackendInfo.backend_info =
      { SPARQL_HTTP_BackendInfo.bi_kind = backend_kind_of_cfg cfg;
        SPARQL_HTTP_BackendInfo.bi_source = backend_source_string cfg;
        SPARQL_HTTP_BackendInfo.bi_in_memory_triples = Z.of_int in_mem_total;
        SPARQL_HTTP_BackendInfo.bi_in_memory_default_graph_triples = Z.of_int in_mem_dflt;
        SPARQL_HTTP_BackendInfo.bi_in_memory_named_graphs = Z.of_int in_mem_ng_count;
        SPARQL_HTTP_BackendInfo.bi_in_memory_named_graph_triples = Z.of_int in_mem_ng_triples;
        SPARQL_HTTP_BackendInfo.bi_cottas = cottas_stores_summaries stores }
    in
    let body = SPARQL_HTTP_BackendInfo.render_backend_info bi in
    { rb_status = 200;
      rb_content_type = "application/json; charset=utf-8";
      rb_body = body }
  with e ->
    { rb_status = 500;
      rb_content_type = "text/plain; charset=utf-8";
      rb_body = "error building backend info: "
                ^ Printexc.to_string e ^ "\n" }

(* Does the Accept header indicate the client wants HTML? Coarse check —
   substring match for "text/html" is enough; we don't need full media-
   type parsing for this redirect heuristic. *)
let accept_wants_html (accept : string) : bool =
  ci_find accept "text/html" >= 0

(* Try to handle the request as a static / landing-page route. Returns
   Some response_body if the path matched, None to fall through to the
   F* SPARQL Protocol decoder.

   [cfg] / [dataset_ref] are threaded through so /backend-info.json can
   describe what's currently loaded; everything else here is stateless.

   Routing order:
     1. Reserved data / bundle endpoints win (parliament-queries.json,
        backend-info.json, factoidal-sparql-client.js, favicon.ico).
     2. /sparql GET with no body and Accept: text/html redirects to /
        so a browser sees the console, not a 400.
     3. Anything else GET-shaped is delegated to the static-file demo
        directory (default docs/web/landing/, or whatever --web-demo
        selected). Missing files yield 404 plaintext, not 500. *)
let try_static_route ~cfg ~dataset_ref ~cottas_stores_ref ~meth ~path ~qs ~accept
    : response_body option =
  if meth <> "GET" then None
  else match path with
  | "/factoidal-sparql-client.js" ->
    Some (serve_component_bundle ())
  | "/parliament-queries.json" ->
    Some (serve_parliament_queries_json ())
  | "/backend-info.json" ->
    Some (serve_backend_info_json cfg dataset_ref cottas_stores_ref)
  | "/admin/recent.json" ->
    (* Last N queries with per-stage timings + cumulative counters.
       Read-only debug surface — populated by parse_and_run_timed. *)
    Some (serve_recent_queries_json ())
  | "/admin" | "/admin/" | "/admin/index.html" ->
    (* Built-in HTML dashboard: live table of recent queries with
       per-stage bars + counters. Polls /admin/recent.json every 2s. *)
    Some (serve_admin_html ())
  | "/favicon.ico" ->
    (* Try the demo dir first (so a demo can ship its own favicon); on
       miss, return 204 to keep the browser's devtools console quiet
       rather than 404 spam. *)
    let demo_resp = serve_static_demo ~cfg path in
    if demo_resp.rb_status = 200 then Some demo_resp
    else Some { rb_status = 204;
                rb_content_type = "image/x-icon";
                rb_body = "" }
  | "/sparql" | "/query" when qs = "" && accept_wants_html accept ->
    (* Browser hit the bare protocol endpoint. Redirect to / so the
       human gets a console rather than a 400. curl / RDFLib / Jena send
       Accept: application/sparql-results+* and skip this branch. *)
    Some { rb_status = 303;
           rb_content_type = "text/plain; charset=utf-8";
           rb_body = "See /\n" }
  | p when SPARQL_HTTP_Routes.is_sparql_protocol_path p ->
    (* Protocol endpoint per F* `SPARQL.HTTP.Routes.is_sparql_protocol_path`
       (the canonical SPARQL 1.1 Protocol query/update endpoint set —
       /sparql, /query, /update). Fall through to the F* SPARQL
       Protocol decoder. #200 Section 2 MIXED-row migration. *)
    None
  | _ ->
    (* Everything else: try to serve from the configured demo dir. *)
    Some (serve_static_demo ~cfg path)

let handle_connection cfg dataset_ref backend_ref cottas_stores_ref ic oc =
  try
    (* Read the whole request (headers + body) into a single buffer,
       then hand off to the F*-extracted framing parser. *)
    let raw = read_full_request ic ~max_header_bytes ~max_body_bytes in
    if String.length raw = 0 then raise End_of_file;
    match SPARQL_HTTP.parse_http_request raw
            (Z.of_int max_header_bytes) (Z.of_int max_body_bytes) with
    | FStar_Pervasives.Inr SPARQL_HTTP.HE_HeadersTooLarge ->
      write_plain_error oc ~status:413 "Request headers too large"
    | FStar_Pervasives.Inr SPARQL_HTTP.HE_BodyTooLarge ->
      write_plain_error oc ~status:413 "Request body too large"
    | FStar_Pervasives.Inr SPARQL_HTTP.HE_MalformedRequestLine ->
      write_plain_error oc ~status:400 "Bad request: malformed request line"
    | FStar_Pervasives.Inr SPARQL_HTTP.HE_MalformedHeader ->
      write_plain_error oc ~status:400 "Bad request: malformed header"
    | FStar_Pervasives.Inr SPARQL_HTTP.HE_MissingCRLF ->
      write_plain_error oc ~status:400 "Bad request: missing CRLF terminator"
    | FStar_Pervasives.Inr (SPARQL_HTTP.HE_BadRequest msg) ->
      write_plain_error oc ~status:400 ("Bad request: " ^ msg)
    | FStar_Pervasives.Inl req ->
    let meth = req.SPARQL_HTTP.hr_method in
    let path = req.SPARQL_HTTP.hr_path in
    let qs   = req.SPARQL_HTTP.hr_query_str in
    let body = req.SPARQL_HTTP.hr_body in
    let headers = req.SPARQL_HTTP.hr_headers in
    (* Reconstruct a uri string for verbose logging only. *)
    let uri = if String.length qs = 0 then path else path ^ "?" ^ qs in
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

    (* Static / landing-page routes intercept before the F* protocol
       decoder. Pure I/O glue (rule #15). *)
    (match try_static_route ~cfg ~dataset_ref ~cottas_stores_ref
              ~meth ~path ~qs ~accept with
     | Some resp ->
       let static_extras =
         (* 303 needs a Location header; everything else just inherits CORS. *)
         if resp.rb_status = 303 then ("Location: /") :: cors_hdrs
         else cors_hdrs
       in
       write_response ~extra_headers:static_extras oc
         ~status:resp.rb_status
         ~content_type:resp.rb_content_type
         ~body:resp.rb_body
     | None ->

    (* Background-load gate (issue #99). If the COTTAS loader thread is
       still running, the dataset is empty / partial and any SPARQL
       request would return misleading results. Reject with 503 +
       Retry-After so clients back off and try again. Static routes
       and /backend-info.json have already been handled above. *)
    if is_loading () then
      (* #200 Section C: Retry-After headers + body lifted to F* per
         rule #11. SPARQL_HTTP_Response.service_unavailable_loading_body
         and service_unavailable_retry_after_headers pin the bytes via
         assert_norm; OCaml side does only the I/O wrapper. *)
      let retry_hdrs =
        SPARQL_HTTP_Response.service_unavailable_retry_after_headers () in
      let body_str =
        SPARQL_HTTP_Response.service_unavailable_loading_body () in
      write_response ~extra_headers:(retry_hdrs @ cors_hdrs) oc
        ~status:503
        ~content_type:"text/plain; charset=utf-8"
        ~body:body_str
    else

    let dataset = !dataset_ref in
    (* PR_Query stashes Server-Timing here; other request kinds leave it []. *)
    let timing_extras_ref : string list ref = ref [] in
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
               (* Rebuild the backend so subsequent queries see the
                  updated in-memory side. The cottas-ondisk handles are
                  read-only and unchanged across UPDATEs (rule #15: glue
                  only — no semantic change). *)
               backend_ref :=
                 build_dataset_backend new_ds !cottas_stores_ref;
               { rb_status = 204;
                 rb_content_type = "text/plain; charset=utf-8";
                 rb_body = "" }
           end))
      | P.PR_Query (q, _dflt, _named) ->
        (* Stage 1: ignore default-graph-uri / named-graph-uri (would
           require HTTP fetch to honour). Phase 2.5 (issue #100):
           queries dispatch through backend_ref so on-disk COTTAS rows
           never have to be materialised. UPDATE keeps using the
           in-memory dataset_ref.

           Heth3 (cooperative budget): wrap parse_and_run in
           with_query_budget so a single slow query (e.g. unbound BGP
           estimate_fast walking 26 row groups) cannot, in steady state,
           swallow the response slot for the next queued request — the
           HTTP boundary consults SPARQL_Eval_TimeBudget.poll after
           parse_and_run returns and emits HTTP 504 in lieu of the
           result body when the deadline has elapsed.

           This retires the prior SIGALRM mechanism (process-global, see
           docs/designissues/2026-05-07-query-planning-fstar-recovery.md
           Phase 5). In-flight cancellation across F* yield boundaries
           is a follow-up that needs the budget threaded through
           SPARQL11.Algebra / SPARQL11.Store eval signatures.

           Timing path (2026-05-02): use parse_and_run_timed so we can
           emit Server-Timing on the response and push a recent_query
           record into the ring buffer. *)
        let started_at = Unix.gettimeofday () in
        let (resp, qt) =
          with_query_budget ~secs:cfg.query_timeout (fun budget ->
            let (resp, qt) =
              parse_and_run_timed ~backend:!backend_ref ~accept
                ~max_rows:cfg.max_rows q in
            (* F*-extracted poll: re-reads now_ms, compares against
               the deadline. is_disabled-budgets always poll false,
               so this is a no-op when --query-timeout 0. *)
            if SPARQL_Eval_TimeBudget.poll budget then begin
              Printf.eprintf
                "[heth3] query timeout after %ds — returning 504\n%!"
                cfg.query_timeout;
              let r = query_timeout_response ~secs:cfg.query_timeout in
              let total_ms =
                (Unix.gettimeofday () -. started_at) *. 1000.0 in
              let qt = { zero_timing with
                         qt_total_ms = total_ms;
                         qt_eval_ms = total_ms;
                         qt_status = r.rb_status;
                         qt_form = "timeout";
                         qt_body_bytes = String.length r.rb_body } in
              (r, qt)
            end else (resp, qt))
        in
        let q_summary = truncate_for_log q 200 in
        Printf.eprintf "%s\n%!" (timing_log_line qt q_summary);
        push_recent_query {
          rq_started_at = started_at;
          rq_query_text = truncate_for_log q 500;
          rq_timing = qt;
        };
        bump_counters qt;
        (* Issue #266: the ring buffer / eprintf log / admin dashboard
           above are operator-only surfaces and stay unconditional;
           only the response header (visible to the requester) is
           gated by --server-timing. *)
        timing_extras_ref :=
          if server_timing_enabled cfg then [timing_response_header qt] else [];
        resp
    in
    write_response ~extra_headers:(!timing_extras_ref @ cors_hdrs) oc
      ~status:resp.rb_status
      ~content_type:resp.rb_content_type
      ~body:resp.rb_body)
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
    let bt = Printexc.get_backtrace () in
    Printf.eprintf "[qof3] handle_connection error: %s\n%s%!"
      (Printexc.to_string e) bt;
    (try write_plain_error oc ~status:500
       ("Internal server error: " ^ Printexc.to_string e)
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
  (* Issue #99: bind the listening socket BEFORE doing any heavy COTTAS
     parquet decoding. Load the cheap RDF/N-Quads parts up front (these
     are usually fast and the user reasonably expects an "empty" or
     "loaded" startup state to be reflected in the first request). *)
  let dataset_ref = ref (load_dataset_fast cfg) in
  let has_cottas = cfg.data_cottas_files <> [] in
  (* Phase 2.5 (issue #100): cottas_stores_ref holds the open on-disk
     COTTAS handles; backend_ref holds the engine view (in-memory side
     unioned with each on-disk store). Both are rebuilt after the
     COTTAS loader thread completes and after every UPDATE. *)
  let cottas_stores_ref : cottas_ondisk_loaded list ref = ref [] in
  let backend_ref : S.dataset_backend ref =
    ref (build_dataset_backend !dataset_ref []) in
  (* snapshot_iris is the list of named-graph IRIs present at full-load
     completion. It's used by the graceful-shutdown handler to diff
     against the live dataset and dump user-added (RW) graphs. We can't
     compute it until the COTTAS load finishes; populate it then. *)
  let snapshot_iris_ref : string list ref = ref [] in
  let snapshot_iris_ready = ref (not has_cottas) in
  if not has_cottas then
    snapshot_iris_ref :=
      List.map (fun ng -> ng.ng_name) (!dataset_ref).ds_named;
  let addr = Unix.ADDR_INET (resolve_host cfg.host, cfg.port) in
  let sock = Unix.socket Unix.PF_INET Unix.SOCK_STREAM 0 in
  (try Unix.setsockopt sock Unix.SO_REUSEADDR true with _ -> ());
  (try Unix.bind sock addr
   with Unix.Unix_error (err, _, _) ->
     Printf.eprintf "Error: cannot bind %s:%d — %s\n"
       cfg.host cfg.port (Unix.error_message err);
     exit 1);
  Unix.listen sock 16;
  let initial_triple_count = List.length (!dataset_ref).ds_default in
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
  Printf.printf "  query timeout: %s\n"
    (if cfg.query_timeout <= 0 then "disabled (queries may run indefinitely)"
     else Printf.sprintf "%ds (HTTP 504 on overrun)" cfg.query_timeout);
  Printf.printf "  web demo: %s%s\n"
    (match cfg.web_demo with
     | None -> "(default landing)"
     | Some s -> s)
    (match resolve_web_demo_dir cfg.web_demo with
     | Some d -> " -> " ^ d
     | None -> " (NOT FOUND on disk; GET / will 404 with a hint)");
  (* Loud warning: --cors=* combined with writes lets any browser page hit
     POST /update cross-origin, bypassing same-origin CSRF protection. Flush
     stderr immediately so the warning lands before any request log lines. *)
  (match cfg.cors with
   | CORS_Any when not cfg.read_only ->
     Printf.eprintf "warning: --cors=* combined with write access is dangerous\n";
     Printf.eprintf "warning: any browser page can issue POST /update against this server\n";
     Printf.eprintf "warning: either add --read-only or an allowlist\n%!"
   | _ -> ());
  (match cfg.dataset_file, cfg.data_cottas_files with
   | Some f, [] ->
     Printf.printf "  default graph: %s (%d triples)\n" f initial_triple_count
   | None, [] -> Printf.printf "  default graph: <empty>\n"
   | dsf, cottas ->
     (* Mixed and/or COTTAS-only: COTTAS parquet decode runs in a worker
        thread (issue #99). Per-source totals appear once the worker
        finishes. *)
     (match dsf with
      | Some f -> Printf.printf "  default graph: --dataset %s + COTTAS (loading…)\n" f
      | None -> Printf.printf "  default graph: COTTAS-only (loading…)\n");
     List.iter (fun p ->
       Printf.printf "    --data-cottas %s\n" p
     ) cottas;
     Printf.printf "  store totals: %d default-graph triples loaded so far\n"
       initial_triple_count);
  (match cfg.load_rw_graphs with
   | Some f ->
     Printf.printf "  loaded RW graphs from: %s (%d named graph(s) now)\n"
       f (List.length (!dataset_ref).ds_named)
   | None -> ());
  (match cfg.dump_rw_graphs_on_exit with
   | Some d ->
     Printf.printf "  dump-on-exit: %s (SIGTERM/SIGINT)\n" d
   | None -> ());
  if has_cottas then
    Printf.printf
      "  port bound at t=0; SPARQL endpoints will return 503 + Retry-After: 5 until COTTAS load completes\n";
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
         (* If the loader thread never finished, snapshot_iris stays []
            (safe: diff treats every named graph as "user-added" and
            dumps everything, which is the right behaviour for an
            interrupted load). *)
         if not !snapshot_iris_ready then
           Printf.eprintf "  warning: COTTAS load did not complete; dump may include preloaded graphs\n%!";
         dump_rw_graphs ~dir
           ~snapshot_iris:!snapshot_iris_ref !dataset_ref
       | None -> ());
      exit 0))
  in
  (try install_exit_handler "SIGTERM" Sys.sigterm with _ -> ());
  (try install_exit_handler "SIGINT" Sys.sigint with _ -> ());
  (* Issue #99: when --data-cottas is present, we want the listener up
     immediately while the COTTAS parquet decode runs in the background.
     The accept loop's per-request stack usage is bounded, so we put it
     on a worker thread; the COTTAS loader stays on the main thread
     (which has the OS's full default stack — typically 8 MB on macOS,
     vs ~512 KB for pthread workers — and the loader's deep traversal
     of large quad arrays would otherwise SIGBUS on a thread stack).

     When there's no --data-cottas, we skip the thread entirely and
     just run the accept loop inline as before. *)
  let accept_loop () =
    while true do
      match (try Some (Unix.accept sock) with
             | Unix.Unix_error (err, _, _) ->
               Printf.eprintf "  accept() failed: %s\n%!" (Unix.error_message err);
               None) with
      | None -> ()
      | Some (client, caddr) ->
        (* Qof3 defensive instrumentation: log every accepted connection so
           we can confirm whether the daemon dies at-accept or mid-handler. *)
        let peer = match caddr with
          | Unix.ADDR_INET (a, p) ->
            Printf.sprintf "%s:%d" (Unix.string_of_inet_addr a) p
          | Unix.ADDR_UNIX s -> "unix:" ^ s in
        Printf.eprintf "[qof3] [accept] peer=%s\n%!" peer;
        let ic = Unix.in_channel_of_descr client in
        let oc = Unix.out_channel_of_descr client in
        (try handle_connection cfg dataset_ref backend_ref cottas_stores_ref ic oc
         with e ->
           let bt = Printexc.get_backtrace () in
           Printf.eprintf "[qof3] unhandled in accept_loop: %s\n%s%!"
             (Printexc.to_string e) bt);
        Printf.eprintf "[qof3] [accept] peer=%s done\n%!" peer;
        (try close_out oc with _ -> ());
        (try Unix.close client with _ -> ())
    done
  in
  if not has_cottas then
    accept_loop ()
  else begin
    Mutex.lock loading_mu;
    loading := true;
    Mutex.unlock loading_mu;
    let load_t0 = Unix.gettimeofday () in
    (* Run the accept loop on a worker thread; it just routes requests
       and never recurses, so 512 KB of pthread stack is plenty. *)
    let _tid = Thread.create accept_loop () in
    (* Main thread: open each --data-cottas file as an on-disk store.
       Phase 2.5 (issue #100): we no longer materialise the COTTAS
       corpus into an rdf_dataset. cottas_ondisk_open returns a handle
       wrapping per-column term-id arrays + dictionaries; queries walk
       these arrays through GB_CottasOnDisk dispatch.

       After the open completes:
         - dataset_ref keeps whatever the --dataset side contributed
           (UPDATE will mutate this; cottas-ondisk is read-only).
         - cottas_stores_ref holds the opened on-disk handles.
         - backend_ref is rebuilt as the union of the two halves.
         - snapshot_iris is taken from the named-graph IRIs visible
           through cottas_ondisk_named_graphs + the in-memory side.

       The accept thread reads backend_ref + loading flag through the
       mutex; we still flip loading=false at the end so 503 stops. *)
    (try
       let opened = open_cottas_ondisk_files cfg.data_cottas_files in
       Mutex.lock loading_mu;
       cottas_stores_ref := opened;
       backend_ref := build_dataset_backend !dataset_ref opened;
       (* Build snapshot_iris from the union of in-memory named graphs
          and cottas-ondisk named graphs. This gives the SIGTERM dumper
          a complete pre-RW baseline; user-added graphs will diff out. *)
       let cottas_named_iris =
         List.concat_map (fun (s : cottas_ondisk_loaded) ->
           List.map (fun (g : (RDF_Graph_Executable.iri *
                              Parser_BallyhooCOTTAS.cottas_graph_ref)) ->
             let (iri, _) = g in iri)
             (RDF_CottasStore.cottas_ondisk_named_graphs s.cod_store))
           opened
       in
       snapshot_iris_ref :=
         List.map (fun ng -> ng.ng_name) (!dataset_ref).ds_named
         @ cottas_named_iris;
       snapshot_iris_ready := true;
       loading := false;
       Mutex.unlock loading_mu;
       let dt = Unix.gettimeofday () -. load_t0 in
       (* For an on-disk store, "total quads" is what cottas_ondisk_summary
          reports per file plus the in-memory side. We compute the
          in-memory total here; per-file totals were already printed by
          cottas_ondisk_open's runtime glue (or are available via
          cottas_ondisk_summary). *)
       let in_mem_total =
         let (t, _, _, _) = count_dataset_triples !dataset_ref in t in
       Printf.printf
         "  COTTAS open complete: %d on-disk file(s), %d in-memory triple(s) in %.1fs\n%!"
         (List.length opened) in_mem_total dt
     with e ->
       Printf.eprintf "  COTTAS open failed: %s\n%!" (Printexc.to_string e);
       (* Flip loading=false so clients stop seeing 503; subsequent
          SPARQL requests will see whatever subset of data was already
          in dataset_ref + any cottas stores opened so far. *)
       Mutex.lock loading_mu;
       snapshot_iris_ref :=
         List.map (fun ng -> ng.ng_name) (!dataset_ref).ds_named;
       snapshot_iris_ready := true;
       loading := false;
       Mutex.unlock loading_mu);
    (* Block forever so the accept thread keeps running. The signal
       handlers installed above call exit, so SIGTERM/SIGINT still
       gracefully shut down the whole process. *)
    while true do
      Unix.sleep 3600
    done
  end

(* Top-level [let () = ...] lives in factoidal_http_main.ml so this file
   is also linkable as a library module from factoidal_cli.ml. The CLI's
   `factoidal serve …` subcommand now calls Factoidal_http.parse_args +
   run_server in-process (no exec). See
   docs/designissues/2026-04-25-cli-http-unification-phase2.md. *)
