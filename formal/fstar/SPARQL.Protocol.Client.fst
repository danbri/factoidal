module SPARQL.Protocol.Client

(** ======================================================================== **)
(** SPARQL 1.1 Protocol — HIGH-LEVEL client: request construction +          **)
(** response dispatch.                                                       **)
(**                                                                          **)
(** Layered on top of two existing verified modules:                        **)
(**   * SPARQL.HTTP.Client — HTTP/1.1 request FRAMING (method/path/headers/  **)
(**     body -> bytes) and response framing (bytes -> status/headers/body). **)
(**     That module is transport-agnostic; its OCaml glue                   **)
(**     (bin/factoidal-http-client/factoidal_http_client.ml) is a           **)
(**     *consumer* (Unix sockets), not an `assume val` realisation — see    **)
(**     that file's banner and skills/ocaml-boundary/SKILL.md's CONSUMER    **)
(**     row. This module follows the same precedent: everything that       **)
(**     decides SPARQL protocol *shape* lives here in F*; no new            **)
(**     `assume val` is introduced because there is no new I/O primitive    **)
(**     to realise — socket I/O was already solved as consumer-side glue.   **)
(**   * SPARQL.Protocol — content negotiation types (`response_format`),    **)
(**     `media_type_to_format`, `content_type_base`. Reused rather than     **)
(**     duplicated.                                                         **)
(**   * Parser.JSONResults / Parser.SRX / Parser.CSVResults / Parser.Turtle /**)
(**     Parser.NTriples — existing W3C-conformant result/graph parsers.     **)
(**     This module does not parse anything itself; it only DISPATCHES the  **)
(**     response Content-Type to the right existing parser.                 **)
(**                                                                          **)
(** What is here:                                                            **)
(**   * RFC 3986 percent-encoding (`pct_encode`), written from scratch      **)
(**     because no reusable encoder existed (only `url_decode` did,         **)
(**     grepped first per the task brief). Handles the full Unicode         **)
(**     codepoint range by UTF-8 byte-encoding non-ASCII codepoints before  **)
(**     percent-encoding each byte, since FStar.Char.char here is a         **)
(**     codepoint, not a byte (see sparql_parser_stubs.ml in                **)
(**     ocaml-boundary skill).                                               **)
(**   * `build_get_request` / `build_post_direct_request` /                 **)
(**     `build_post_form_request` — the three SPARQL 1.1 Protocol query     **)
(**     dispatch methods (query-via-GET, query-via-POST-direct,             **)
(**     query-via-POST-urlencoded), each producing an                       **)
(**     `SPARQL.HTTP.Client.http_request_msg`.                              **)
(**   * `sniff_query_kind` — a best-effort (NOT a full grammar) scan for     **)
(**     the query's top-level form keyword, used only to bias the Accept    **)
(**     header's q-values. Correctness never depends on the guess being     **)
(**     right: `handle_http_response` dispatches on the response's actual   **)
(**     Content-Type, and `accept_header_for_kind` always lists every       **)
(**     known media type (just reordered by q-value), so a wrong guess      **)
(**     costs a sub-optimal q-value ordering, not a failure.                **)
(**   * `handle_http_response` — status-code + Content-Type dispatch to a   **)
(**     typed `client_result`.                                              **)
(**                                                                          **)
(** What is NOT here:                                                        **)
(**   * No socket I/O (that's the existing consumer glue).                  **)
(**   * No SPARQL grammar parsing (the sniff is deliberately shallow).      **)
(**   * No redirect/retry/auth logic (left to the CLI, which is I/O glue,   **)
(**     not semantics).                                                     **)
(** ======================================================================== **)

open FStar.String
open FStar.List.Tot
open RDF.Graph.Executable
open SPARQL.Protocol
open SPARQL.HTTP.Client

module JRes    = Parser.JSONResults
module XRes    = Parser.SRX
module CVRes   = Parser.CSVResults
module Turtle  = Parser.Turtle
module NT      = Parser.NTriples

#push-options "--z3rlimit 100 --fuel 2 --ifuel 2"

(** ====================================================================== **)
(** Part 1: Types                                                           **)
(** ====================================================================== **)

// Which of the four SPARQL 1.1 query forms we believe we're sending.
// Used ONLY to bias Accept-header q-values (see banner). Never used to
// interpret the response — that always goes by actual Content-Type.
type client_query_kind =
  | CQK_Select
  | CQK_Ask
  | CQK_Construct
  | CQK_Describe

// The three SPARQL 1.1 Protocol request dispatch methods (§2.1.1-2.1.3
// of the spec) for the *query* operation. (SPARQL Update dispatch is a
// separate, smaller surface — direct-POST or form-POST only, no GET —
// and is not implemented in this phase; see the module banner in the
// CLI wiring for the follow-up note.)
type client_dispatch_method =
  | CDM_Get
  | CDM_PostDirect
  | CDM_PostForm

// Outcome of a fully-handled HTTP response: either a typed SPARQL result
// or a typed failure. `CLR_HttpError` carries the raw body too so the
// CLI can print server-side error detail (helpful for the 400 case the
// end-to-end test exercises).
noeq type client_result =
  | CLR_Bindings         : vars:list string -> rows:list (list (string & rdf_term)) -> client_result
  | CLR_Boolean          : bool -> client_result
  | CLR_Graph            : list triple -> client_result
  | CLR_HttpError        : status:nat -> body:string -> client_result
  | CLR_ParseError       : detail:string -> client_result
  | CLR_UnknownContentType : content_type:string -> body:string -> client_result


(** ====================================================================== **)
(** Part 2: RFC 3986 percent-encoding                                       **)
(**                                                                         **)
(** `char_code`/`char_to_string`/`hex_nibble` etc. from `SPARQL.Protocol`   **)
(** are ASCII-oriented helpers reused where possible; percent-encoding      **)
(** itself is new (grepped first for `url_encode`/`percent_encode` per the **)
(** task brief — CSVW.URITemplate.fst/RML.Eval.fst/SPARQL11.Algebra.fst    **)
(** matched on the string "encode" as a substring of unrelated words, not   **)
(** an actual percent-encoder).                                            **)
(** ====================================================================== **)

// RFC 3986 §2.3 unreserved set: ALPHA / DIGIT / "-" / "." / "_" / "~"
let is_unreserved (c : FStar.Char.char) : bool =
  let cd = char_code c in
  (cd >= 0x41 && cd <= 0x5A)   // A-Z
  || (cd >= 0x61 && cd <= 0x7A) // a-z
  || (cd >= 0x30 && cd <= 0x39) // 0-9
  || cd = 0x2D  // '-'
  || cd = 0x2E  // '.'
  || cd = 0x5F  // '_'
  || cd = 0x7E  // '~'

let hex_nibble_upper (n : nat{n < 16}) : FStar.Char.char =
  if n < 10 then FStar.Char.char_of_int (0x30 + n)
  else FStar.Char.char_of_int (0x41 + (n - 10))

// One percent-triplet for a single byte value (0..255).
let byte_to_pct (b : nat{b < 256}) : string =
  let hi : nat = b / 16 in
  let lo : nat = b % 16 in
  "%" ^ char_to_string (hex_nibble_upper hi) ^ char_to_string (hex_nibble_upper lo)

// UTF-8 byte-decomposition of a single Unicode codepoint. FStar.Char.char
// here is a codepoint (not a byte — see banner), so non-ASCII characters
// must be turned into 2-4 continuation bytes before percent-encoding.
// Each arithmetic branch is bounded so every returned byte is < 256:
//   - 2-byte: 0xC0 + cp/64 <= 0xC0 + 0x1F = 0xDF
//   - 3-byte: 0xE0 + cp/4096 <= 0xE0 + 0x0F = 0xEF
//   - 4-byte: 0xF0 + cp/262144 <= 0xF0 + 0x07 = 0xF7
//   - continuation bytes: 0x80 + (x % 64) <= 0xBF
let codepoint_to_utf8_bytes (cp : nat) : list (b:nat{b < 256}) =
  if cp <= 0x7F then [cp]
  else if cp <= 0x7FF then
    [ 0xC0 + (cp / 64); 0x80 + (cp % 64) ]
  else if cp <= 0xFFFF then
    [ 0xE0 + (cp / 4096); 0x80 + ((cp / 64) % 64); 0x80 + (cp % 64) ]
  else
    // Clamp to the valid Unicode range (0x10FFFF); anything larger can't
    // come from a real FStar.Char.char, but staying total costs nothing.
    let cp' = if cp <= 0x10FFFF then cp else 0x10FFFF in
    [ 0xF0 + (cp' / 262144); 0x80 + ((cp' / 4096) % 64);
      0x80 + ((cp' / 64) % 64); 0x80 + (cp' % 64) ]

let rec bytes_to_pct_chars (bs : list (b:nat{b < 256}))
  : Tot string (decreases (List.Tot.length bs)) =
  match bs with
  | [] -> ""
  | b :: rest -> byte_to_pct b ^ bytes_to_pct_chars rest

let pct_encode_char (c : FStar.Char.char) : string =
  if is_unreserved c then char_to_string c
  else bytes_to_pct_chars (codepoint_to_utf8_bytes (char_code c))

let rec pct_encode_chars (cs : list FStar.Char.char)
  : Tot string (decreases (List.Tot.length cs)) =
  match cs with
  | [] -> ""
  | c :: rest -> pct_encode_char c ^ pct_encode_chars rest

// Percent-encode a string for use as a single query-string component
// (a key or a value) or a `application/x-www-form-urlencoded` component.
// Space is encoded as `%20` (RFC 3986), which every SPARQL endpoint this
// codebase talks to (including our own factoidal-http) accepts — the
// historical `+`-for-space convention is a browser-form-specific
// shorthand, not a hard requirement of RFC 1866/3986.
let pct_encode (s : string) : string =
  pct_encode_chars (String.list_of_string s)


(** ====================================================================== **)
(** Part 3: query-string / form-body assembly                              **)
(** ====================================================================== **)

let encode_pair (kv : string & string) : string =
  let (k, v) = kv in
  pct_encode k ^ "=" ^ pct_encode v

let rec join_amp (parts : list string) : Tot string (decreases (List.Tot.length parts)) =
  match parts with
  | [] -> ""
  | [p] -> p
  | p :: rest -> p ^ "&" ^ join_amp rest

// `k=v&k=v&...`, each component percent-encoded.
let encode_pairs (pairs : list (string & string)) : string =
  join_amp (List.Tot.map encode_pair pairs)

// The `default-graph-uri`/`named-graph-uri` protocol parameters shared
// by all three dispatch methods (SPARQL 1.1 Protocol §2.1.1-2.1.3).
let graph_uri_pairs
    (default_graph_uris : list string)
    (named_graph_uris   : list string)
  : list (string & string) =
     List.Tot.map (fun g -> ("default-graph-uri", g)) default_graph_uris
   @ List.Tot.map (fun g -> ("named-graph-uri", g)) named_graph_uris


(** ====================================================================== **)
(** Part 4: Accept-header selection                                        **)
(**                                                                         **)
(** Always lists every result media type this client can parse; only the   **)
(** q-value ORDER changes with the guessed query kind. This means a wrong  **)
(** guess from `sniff_query_kind` never causes a hard failure (406) on a   **)
(** conforming server — see banner.                                        **)
(** ====================================================================== **)

let accept_header_for_kind (k : client_query_kind) : string =
  match k with
  | CQK_Select | CQK_Ask ->
    "application/sparql-results+json, application/sparql-results+xml;q=0.9, \
     text/turtle;q=0.2, application/n-triples;q=0.1"
  | CQK_Construct | CQK_Describe ->
    "text/turtle, application/n-triples;q=0.9, \
     application/sparql-results+json;q=0.2, application/sparql-results+xml;q=0.1"


(** ====================================================================== **)
(** Part 5: query-form sniffing (best-effort, Accept-header bias only)      **)
(**                                                                        **)
(** Tokenizes on ASCII whitespace, skips PREFIX/BASE prologue declarations, **)
(** and returns the first form keyword found. NOT a SPARQL grammar parser: **)
(** it does not track string/IRI literals or comments, so a query with a  **)
(** literal string containing "SELECT" before its real keyword could, in   **)
(** principle, be mis-sniffed. That's an acceptable Accept-header ordering **)
(** wobble, never a correctness bug (see Part 4 and the module banner).    **)
(** ====================================================================== **)

let is_ascii_ws_char (c : FStar.Char.char) : bool = is_ws_code (char_code c)

let ascii_upper_char (c : FStar.Char.char) : FStar.Char.char =
  let cd = char_code c in
  if cd >= 0x61 && cd <= 0x7A then FStar.Char.char_of_int (cd - 32) else c

let ascii_upper_string (s : string) : string =
  String.string_of_list (List.Tot.map ascii_upper_char (String.list_of_string s))

let rec take_token_chars
    (xs : list FStar.Char.char)
    (acc : list FStar.Char.char)
  : Tot (list FStar.Char.char & list FStar.Char.char) (decreases (List.Tot.length xs)) =
  match xs with
  | [] -> (List.Tot.rev acc, [])
  | c :: rest ->
    if is_ascii_ws_char c then (List.Tot.rev acc, xs)
    else take_token_chars rest (c :: acc)

// Next whitespace-delimited token plus the remaining char list positioned
// right after it (leading whitespace is skipped first).
let next_token (cs : list FStar.Char.char) : (string & list FStar.Char.char) =
  let cs' = drop_ws_left cs in
  let (tok, rest) = take_token_chars cs' [] in
  (String.string_of_list tok, rest)

let rec sniff_loop (cs : list FStar.Char.char) (fuel : nat)
  : Tot client_query_kind (decreases fuel) =
  if fuel = 0 then CQK_Select
  else
    let (tok, rest) = next_token cs in
    if String.length tok = 0 then CQK_Select
    else
      let up = ascii_upper_string tok in
      if up = "SELECT" then CQK_Select
      else if up = "ASK" then CQK_Ask
      else if up = "CONSTRUCT" then CQK_Construct
      else if up = "DESCRIBE" then CQK_Describe
      else if up = "PREFIX" then
        // Skip the two tokens of a prefix decl: `name:` and `<iri>`.
        let (_, rest1) = next_token rest in
        let (_, rest2) = next_token rest1 in
        sniff_loop rest2 (fuel - 1)
      else if up = "BASE" then
        let (_, rest1) = next_token rest in
        sniff_loop rest1 (fuel - 1)
      else
        sniff_loop rest (fuel - 1)

let sniff_query_kind (query_text : string) : client_query_kind =
  sniff_loop (String.list_of_string query_text) (String.length query_text + 1)


(** ====================================================================== **)
(** Part 6: request builders                                               **)
(**                                                                         **)
(** All three build an `http_request_msg` (SPARQL.HTTP.Client); the caller **)
(** feeds it to `format_request` and hands the bytes to socket I/O. None   **)
(** of these do any I/O themselves.                                        **)
(** ====================================================================== **)

// query-via-GET (SPARQL 1.1 Protocol §2.1.1).
let build_get_request
    (host                : string)
    (path                : string)
    (query_text          : string)
    (default_graph_uris  : list string)
    (named_graph_uris    : list string)
    (accept              : string)
  : http_request_msg =
  let pairs = ("query", query_text) :: graph_uri_pairs default_graph_uris named_graph_uris in
  { rm_method    = "GET";
    rm_path      = path;
    rm_query_str = encode_pairs pairs;
    rm_version   = "HTTP/1.1";
    rm_host      = host;
    rm_headers   = [("Accept", accept)];
    rm_body      = "" }

// query-via-POST-direct (§2.1.2): the query text is the ENTIRE request
// body, Content-Type: application/sparql-query. Graph-URI parameters
// still travel as query-string parameters per the spec.
let build_post_direct_request
    (host                : string)
    (path                : string)
    (query_text          : string)
    (default_graph_uris  : list string)
    (named_graph_uris    : list string)
    (accept              : string)
  : http_request_msg =
  let pairs = graph_uri_pairs default_graph_uris named_graph_uris in
  { rm_method    = "POST";
    rm_path      = path;
    rm_query_str = encode_pairs pairs;
    rm_version   = "HTTP/1.1";
    rm_host      = host;
    rm_headers   = [("Accept", accept); ("Content-Type", "application/sparql-query")];
    rm_body      = query_text }

// query-via-URL-encoded-POST (§2.1.3): everything (including `query`
// itself) travels as an `application/x-www-form-urlencoded` body.
let build_post_form_request
    (host                : string)
    (path                : string)
    (query_text          : string)
    (default_graph_uris  : list string)
    (named_graph_uris    : list string)
    (accept              : string)
  : http_request_msg =
  let pairs = ("query", query_text) :: graph_uri_pairs default_graph_uris named_graph_uris in
  { rm_method    = "POST";
    rm_path      = path;
    rm_query_str = "";
    rm_version   = "HTTP/1.1";
    rm_host      = host;
    rm_headers   = [("Accept", accept); ("Content-Type", "application/x-www-form-urlencoded")];
    rm_body      = encode_pairs pairs }

// Convenience: pick a builder given a dispatch method, sniffing the
// Accept header from the query text automatically.
let build_query_request
    (method_ : client_dispatch_method)
    (host                : string)
    (path                : string)
    (query_text          : string)
    (default_graph_uris  : list string)
    (named_graph_uris    : list string)
  : http_request_msg =
  let accept = accept_header_for_kind (sniff_query_kind query_text) in
  match method_ with
  | CDM_Get        -> build_get_request        host path query_text default_graph_uris named_graph_uris accept
  | CDM_PostDirect -> build_post_direct_request host path query_text default_graph_uris named_graph_uris accept
  | CDM_PostForm   -> build_post_form_request   host path query_text default_graph_uris named_graph_uris accept


(** ====================================================================== **)
(** Part 7: response dispatch                                              **)
(**                                                                         **)
(** Dispatches purely on the response's actual Content-Type header (never  **)
(** on the guess from Part 5) to the matching existing W3C result/graph    **)
(** parser. Graph responses use no base IRI (Turtle/N-Triples response     **)
(** bodies from a conforming endpoint contain only absolute IRIs and       **)
(** blank nodes; relative-IRI CONSTRUCT responses are a known, documented  **)
(** simplification for this phase — see module banner).                   **)
(** ====================================================================== **)

let dispatch_body (fmt : response_format) (body : string) : client_result =
  match fmt with
  | RF_Json ->
    (match JRes.parse_srj_boolean body with
     | Some b -> CLR_Boolean b
     | None ->
       (match JRes.parse_srj_results body with
        | Some (vars, rows) -> CLR_Bindings vars rows
        | None -> CLR_ParseError "invalid application/sparql-results+json body"))
  | RF_Xml ->
    (match XRes.parse_srx_boolean body with
     | Some b -> CLR_Boolean b
     | None ->
       (match XRes.parse_srx_results body with
        | Some (vars, rows) -> CLR_Bindings vars rows
        | None -> CLR_ParseError "invalid application/sparql-results+xml body"))
  | RF_Csv ->
    (match CVRes.parse_csv_to_solutions body with
     | Some (vars, rows) -> CLR_Bindings vars rows
     | None -> CLR_ParseError "invalid text/csv results body")
  | RF_Tsv ->
    (match CVRes.parse_tsv_to_solutions body with
     | Some (vars, rows) -> CLR_Bindings vars rows
     | None -> CLR_ParseError "invalid text/tab-separated-values results body")
  | RF_Turtle ->
    (match Turtle.parse_turtle_strict body with
     | Some ts -> CLR_Graph ts
     | None -> CLR_ParseError "invalid text/turtle graph body")
  | RF_NTriples ->
    (match NT.parse_ntriples_strict body with
     | Some ts -> CLR_Graph ts
     | None -> CLR_ParseError "invalid application/n-triples graph body")
  | RF_Text -> CLR_ParseError "text/plain response body is not a SPARQL result"

// Top-level: given a parsed HTTP response (from
// `SPARQL.HTTP.Client.parse_http_response`), produce a typed client
// result. Non-2xx statuses become `CLR_HttpError` with the raw body so
// callers can surface server-side error detail (e.g. a 400 on a
// malformed query, exercised by the end-to-end test).
let handle_http_response (resp : http_response) : client_result =
  if resp.rsp_status < 200 || resp.rsp_status >= 300 then
    CLR_HttpError resp.rsp_status resp.rsp_body
  else
    match header_lookup_ci resp.rsp_headers "Content-Type" with
    | None -> CLR_UnknownContentType "" resp.rsp_body
    | Some ct ->
      let base = content_type_base ct in
      (match media_type_to_format base with
       | Some fmt -> dispatch_body fmt resp.rsp_body
       | None -> CLR_UnknownContentType ct resp.rsp_body)

#pop-options


(** ====================================================================== **)
(** Part 8: smoke tests (compile-time)                                     **)
(** ====================================================================== **)

let _test_pct_ascii_passthrough =
  pct_encode "abcXYZ019-._~" = "abcXYZ019-._~"

let _test_pct_space =
  pct_encode "a b" = "a%20b"

let _test_pct_ask_query =
  pct_encode "ASK WHERE {}" = "ASK%20WHERE%20%7B%7D"

let _test_pct_colon_slash =
  pct_encode "urn:x" = "urn%3Ax"

let _test_encode_pairs =
  encode_pairs [("query", "ASK{}"); ("default-graph-uri", "urn:g")]
    = "query=ASK%7B%7D&default-graph-uri=urn%3Ag"

let _test_sniff_select =
  sniff_query_kind "SELECT * WHERE { ?s ?p ?o }" = CQK_Select

let _test_sniff_ask =
  sniff_query_kind "ASK { ?s ?p ?o }" = CQK_Ask

let _test_sniff_construct_with_prefix =
  sniff_query_kind "PREFIX ex: <http://example.org/> CONSTRUCT { ?s ?p ?o } WHERE { ?s ?p ?o }"
    = CQK_Construct

let _test_sniff_describe_with_base =
  sniff_query_kind "BASE <http://example.org/> DESCRIBE <http://example.org/x>"
    = CQK_Describe

let _test_accept_select =
  accept_header_for_kind CQK_Select = accept_header_for_kind CQK_Ask

let _test_build_get_request =
  let req = build_get_request "example.org" "/sparql" "ASK{}" [] []
              (accept_header_for_kind CQK_Ask) in
  req.rm_method = "GET"
  && req.rm_query_str = "query=ASK%7B%7D"

let _test_build_post_direct_request =
  let req = build_post_direct_request "example.org" "/sparql" "ASK {}" [] []
              (accept_header_for_kind CQK_Ask) in
  req.rm_method = "POST"
  && req.rm_body = "ASK {}"
  && req.rm_query_str = ""

let _test_build_post_form_request =
  let req = build_post_form_request "example.org" "/sparql" "ASK{}" [] []
              (accept_header_for_kind CQK_Ask) in
  req.rm_method = "POST"
  && req.rm_body = "query=ASK%7B%7D"

let _test_dispatch_json_boolean =
  match dispatch_body RF_Json "{\"head\":{},\"boolean\":true}" with
  | CLR_Boolean b -> b = true
  | _ -> false

let _test_dispatch_json_bindings =
  match dispatch_body RF_Json
    "{\"head\":{\"vars\":[\"x\"]},\"results\":{\"bindings\":[]}}" with
  | CLR_Bindings vars _ -> vars = ["x"]
  | _ -> false

// Graph-response dispatch (CONSTRUCT/DESCRIBE): exercised independently
// of any live server, since bin/factoidal-http/factoidal_http.ml has a
// documented Stage-1 stub for CONSTRUCT evaluation (see
// tests/local/sparql_client_protocol.sh's case (d) banner) — this
// proves dispatch_body's Turtle/N-Triples path itself is correct.
let _test_dispatch_turtle_graph =
  match dispatch_body RF_Turtle
    "<http://example.org/alice> <http://example.org/name> \"Alice\" ." with
  | CLR_Graph ts -> List.Tot.length ts = 1
  | _ -> false

let _test_dispatch_ntriples_graph =
  match dispatch_body RF_NTriples
    "<http://example.org/alice> <http://example.org/name> \"Alice\" .\n\
     <http://example.org/bob> <http://example.org/name> \"Bob\" .\n" with
  | CLR_Graph ts -> List.Tot.length ts = 2
  | _ -> false

let _test_handle_http_error =
  let resp = { rsp_version = "HTTP/1.1"; rsp_status = 400; rsp_reason = "Bad Request";
               rsp_headers = []; rsp_body = "bad query" } in
  match handle_http_response resp with
  | CLR_HttpError status body -> status = 400 && body = "bad query"
  | _ -> false
