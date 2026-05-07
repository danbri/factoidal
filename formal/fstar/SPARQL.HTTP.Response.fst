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

// ---------------------------------------------------------------
// CLI parsing: --cors=<value> string -> cors_policy.
//
// Migrated from factoidal_http.ml's parse_cors_value (rule #1 — F* is
// the source of truth for the mapping). Two semantic decisions:
//   - "*" means CORS_Any
//   - otherwise, comma-separated origins (with whitespace trimmed and
//     empty entries dropped); empty list falls back to CORS_Off so a
//     stray "--cors=" or "--cors=," is a no-op rather than rejecting
//     every request silently.
//
// We implement ASCII trim here rather than asking the caller to
// pre-trim because the per-part trim after split(',') makes the
// responsibility-split awkward.
// ---------------------------------------------------------------

let is_ascii_ws (c : FStar.Char.char) : Tot bool =
  let n = FStar.Char.int_of_char c in
  n = 0x20 || n = 0x09 || n = 0x0A || n = 0x0D

let rec drop_leading_ws (cs : list FStar.Char.char)
  : Tot (list FStar.Char.char) (decreases cs) =
  match cs with
  | [] -> []
  | c :: rest -> if is_ascii_ws c then drop_leading_ws rest else cs

let trim_ascii (s : string) : Tot string =
  let cs = FStar.String.list_of_string s in
  let l = drop_leading_ws cs in
  let r = FStar.List.Tot.rev (drop_leading_ws (FStar.List.Tot.rev l)) in
  FStar.String.string_of_list r

let rec map_trim (xs : list string) : Tot (list string) (decreases xs) =
  match xs with
  | [] -> []
  | x :: rest -> trim_ascii x :: map_trim rest

let rec drop_empty (xs : list string) : Tot (list string) (decreases xs) =
  match xs with
  | [] -> []
  | x :: rest -> if x = "" then drop_empty rest else x :: drop_empty rest

let parse_cors_value (raw : string) : Tot cors_policy =
  let v = trim_ascii raw in
  if v = "*" then CORS_Any
  else
    let parts = drop_empty (map_trim (FStar.String.split [','] v)) in
    match parts with
    | [] -> CORS_Off
    | _  -> CORS_List parts

// Human-readable description of the CORS mode, for the startup log.
let rec join_with_comma_space (xs : list string) : Tot string (decreases xs) =
  match xs with
  | [] -> ""
  | [x] -> x
  | x :: rest -> x ^ ", " ^ join_with_comma_space rest

let cors_mode_to_string (p : cors_policy) : Tot string =
  match p with
  | CORS_Off  -> "off (no Access-Control-* headers)"
  | CORS_Any  -> "any origin (Access-Control-Allow-Origin: *)"
  | CORS_List origins ->
      "allowlist (" ^ join_with_comma_space origins ^ ")"

// ---------------------------------------------------------------
// render_response_head
//
// Build the HTTP/1.1 response head — status line + standard
// headers + caller-supplied extras (CORS, Server-Timing, etc.).
// The OCaml caller writes (head + body) to the connection's
// out_channel; the F* function owns the byte template.
//
// Migrated from factoidal_http.ml's write_response template.
// Byte-for-byte identical to the legacy OCaml Printf:
//
//   HTTP/1.1 <status> <reason>\r\n
//   Content-Type: <content_type>\r\n
//   Content-Length: <body_len>\r\n
//   Connection: close\r\n
//   <extras (each followed by CRLF)>
//   \r\n
//
// where <reason> is from status_text and <body_len> is the size
// of the response body in bytes.
// ---------------------------------------------------------------

let rec concat_header_lines (xs : list string) : Tot string (decreases xs) =
  match xs with
  | [] -> ""
  | h :: rest -> h ^ "\r\n" ^ concat_header_lines rest

let render_response_head
    (status        : int)
    (content_type  : string)
    (body_len      : int)
    (extra_headers : list string)
  : Tot string =
  let reason = status_text status in
  "HTTP/1.1 " ^ string_of_int status ^ " " ^ reason ^ "\r\n"
  ^ "Content-Type: " ^ content_type ^ "\r\n"
  ^ "Content-Length: " ^ string_of_int body_len ^ "\r\n"
  ^ "Connection: close\r\n"
  ^ concat_header_lines extra_headers
  ^ "\r\n"
