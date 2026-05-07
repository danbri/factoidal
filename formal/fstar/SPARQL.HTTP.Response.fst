module SPARQL.HTTP.Response

open FStar.List.Tot

// HTTP response helpers migrated from factoidal_http.ml per rule #1
// (F* is the source of truth). Pure data -> string transformations:
//
//   - status_text : map a numeric HTTP status code to its IANA reason
//     phrase, restricted to the codes the SPARQL server actually emits.
//   - cors_headers : compute the list of "Name: value" CORS header lines
//     for a given policy and requesting Origin, byte-for-byte identical
//     to the previous OCaml hand-rolled implementation.
//
// Step 2 of the factoidal_http.ml unwind series; step 1 was json_escape
// in SPARQL.JSON.Escape (PR #126). No assume vals introduced.

// Reason phrase for the status codes the SPARQL HTTP layer emits. Codes
// outside this enumerated set fall back to "Unknown" — that matches the
// previous OCaml behaviour and is fine because every response site picks
// from this fixed list.
val status_text : code:int -> string
let status_text code =
  if code = 200 then "OK"
  else if code = 204 then "No Content"
  else if code = 303 then "See Other"
  else if code = 400 then "Bad Request"
  else if code = 403 then "Forbidden"
  else if code = 404 then "Not Found"
  else if code = 405 then "Method Not Allowed"
  else if code = 413 then "Payload Too Large"
  else if code = 500 then "Internal Server Error"
  else if code = 501 then "Not Implemented"
  else if code = 503 then "Service Unavailable"
  else if code = 504 then "Gateway Timeout"
  else "Unknown"

// CORS policy — how the server responds to cross-origin browser requests.
//   CORS_Off : default, emit no Access-Control-* headers at all.
//   CORS_Any : echo "Access-Control-Allow-Origin: *" unconditionally.
//   CORS_List origins : echo the requesting Origin only if it appears in
//     the allowlist, and add "Vary: Origin".
//
// The F* extractor preserves constructor names verbatim, so the OCaml
// side keeps using CORS_Off / CORS_Any / CORS_List unchanged.
type cors_policy =
  | CORS_Off
  | CORS_Any
  | CORS_List of list string

// The three header lines that are always emitted when CORS is on at all.
// Kept as a let so the F* and OCaml outputs share a single source of
// truth for the values.
let common_cors_headers : list string =
  [ "Access-Control-Allow-Methods: GET, POST, OPTIONS";
    "Access-Control-Allow-Headers: Content-Type, Authorization, Cf-Access-Jwt-Assertion, Cf-Access-Authenticated-User-Email, X-Authid";
    // Timing-Allow-Origin lets cross-origin pages read the
    // Server-Timing response header that factoidal_http emits per query
    // (parse;dur=, eval;dur=, format;dur=, total;dur=). Without this,
    // browsers strip Server-Timing from cross-origin fetch() reads and
    // the demo-page timing breakdown panel comes back empty. Verified
    // F* policy decision — every CORS-enabled response gets it.
    "Timing-Allow-Origin: *";
    "Access-Control-Max-Age: 86400" ]

// Linear membership check on a list of strings; F* doesn't carry an
// Eq.string typeclass at extraction time the way OCaml's polymorphic =
// does, but `=` on strings is total in F*, so a plain mem walk works.
let rec string_mem (x:string) (xs:list string) : bool =
  match xs with
  | [] -> false
  | y :: rest -> if x = y then true else string_mem x rest

val cors_headers : policy:cors_policy -> origin:option string -> list string
let cors_headers policy origin =
  match policy with
  | CORS_Off -> []
  | CORS_Any ->
      "Access-Control-Allow-Origin: *" :: common_cors_headers
  | CORS_List allowed ->
      (match origin with
       | Some o ->
           if string_mem o allowed then
             ("Access-Control-Allow-Origin: " ^ o)
             :: "Vary: Origin"
             :: common_cors_headers
           else []
       | None -> [])

// JSON error-response body templates. The HTTP layer wraps these with
// the corresponding 413 / 504 response_body record (status code,
// content type); only the JSON body itself lives here.

// 413 body: query produced too many rows for the configured cap. The
// hint string is a stable user-facing recommendation matched by the
// /admin demo page; do not edit without coordinating with the UI.
val result_cap_response_body : cap:int -> string
let result_cap_response_body cap =
  String.concat "" [
    "{\"error\":\"result_cardinality_cap_exceeded\",\"cap\":";
    string_of_int cap;
    ",\"hint\":\"Add LIMIT or bind more triple-pattern terms.\"}\n"
  ]

// 504 body: query exceeded its wall-clock budget. Same hint text as
// the cap body so the UI can route both cases through the same panel.
val query_timeout_response_body : secs:int -> string
let query_timeout_response_body secs =
  String.concat "" [
    "{\"error\":\"query_timeout\",\"seconds\":";
    string_of_int secs;
    ",\"hint\":\"Add LIMIT or bind more triple-pattern terms.\"}\n"
  ]

// Compile-time guards: pin both response-body templates and the
// 504 status_text byte-for-byte. assert_norm forces F* to reduce
// the body and check it against the expected string at type-check
// time, so any future drift in the template — extra whitespace, a
// missing comma, a renamed field — fails verification rather than
// silently shipping. (A bare `let _test = expr = "..."` would only
// type-check the boolean; F* is happy if it equals `false`.)
let _ = assert_norm (
  result_cap_response_body 1000
    = "{\"error\":\"result_cardinality_cap_exceeded\",\"cap\":1000,\"hint\":\"Add LIMIT or bind more triple-pattern terms.\"}\n"
)

let _ = assert_norm (
  query_timeout_response_body 30
    = "{\"error\":\"query_timeout\",\"seconds\":30,\"hint\":\"Add LIMIT or bind more triple-pattern terms.\"}\n"
)

// Status_text 504 is a sibling guard: query_timeout_response_body
// produces a 504 body, and the OCaml shim that wraps it pulls the
// reason phrase from this same module's status_text. If those two
// drift apart the wire response would say "HTTP/1.1 504 Unknown"
// with a JSON timeout body — keep them locked together at extract
// time.
let _ = assert_norm (status_text 504 = "Gateway Timeout")
