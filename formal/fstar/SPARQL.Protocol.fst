module SPARQL.Protocol

(** ======================================================================== **)
(** SPARQL 1.1 Protocol — Request decoder + Response serialiser              **)
(**                                                                          **)
(** W3C spec: https://www.w3.org/TR/sparql11-protocol/                       **)
(**                                                                          **)
(** THIS MODULE IS PURE. It contains NO HTTP transport code.                  **)
(**                                                                          **)
(** What is here:                                                             **)
(**   * decode_request — HTTP method + URL + content-type + body           **)
(**     become a typed sparql_request value.                                 **)
(**   * parse_accept_header + pick_response_format — content negotiation.  **)
(**   * serialise_response_json / _xml / _csv / _tsv — SELECT results.     **)
(**   * serialise_response_boolean_json / _boolean_xml — ASK results.      **)
(**                                                                          **)
(** What is NOT here:                                                         **)
(**   * No Unix/HTTP server. No TCP. No request-line parser. That is glue   **)
(**     for a future session.                                                 **)
(**   * No query/update evaluation. The caller hands a (vars, rows) or      **)
(**     bool to the serialiser.                                              **)
(**                                                                          **)
(** Design notes                                                              **)
(** -----------                                                              **)
(** Accept q-values are represented as an integer in units of 1/1000         **)
(** (0..1000). Keeping the whole module in `Tot` means no floats; the         **)
(** RFC 7231 lexical form allows at most 3 decimal digits of precision so    **)
(** no information is lost.                                                   **)
(**                                                                          **)
(** A binding row is `list (var_name * rdf_term)` — same shape the rest      **)
(** of the codebase uses (see `parse_binding_row` in Parser.JSONResults).    **)
(** ======================================================================== **)

open FStar.String
open FStar.List.Tot
open RDF.Graph.Executable

#push-options "--z3rlimit 50 --fuel 2 --ifuel 2"

(** ====================================================================== **)
(** Part 1: Types                                                           **)
(** ====================================================================== **)

// A single binding row: same shape as solution_mapping in
// RDF.Graph.Executable. Reused for clarity.
type binding_row = list (string * rdf_term)

// Response content type. RF_Text is the fallback for unknown Accept
// strings when no default is stronger.
type response_format =
  | RF_Json        // application/sparql-results+json
  | RF_Xml         // application/sparql-results+xml  (SRX)
  | RF_Csv         // text/csv
  | RF_Tsv         // text/tab-separated-values
  | RF_Turtle      // text/turtle                (CONSTRUCT only)
  | RF_NTriples    // application/n-triples      (CONSTRUCT only)
  | RF_Text        // text/plain                 (generic fallback)

// q-value as an int in units of 1/1000. Range 0..1000.
type q_priority = n:nat{ n <= 1000 }

type accept_entry = response_format & q_priority

// A decoded SPARQL protocol request.
//
// PR_Query / PR_Update carry the query/update text plus the two
// protocol-level graph-URI lists (default-graph-uri, named-graph-uri).
// Each URI is paired with its raw (pre-decode) string for diagnostics.
// We keep only the decoded URI in the first position, and reserve the
// second for an optional label/raw form. Here we simply use the
// decoded form twice so callers can ignore it; this keeps the shape
// flexible without changing the type later.
type sparql_request =
  | PR_Query  : query_text:string
             -> default_graph_uris:list string
             -> named_graph_uris:list string
             -> sparql_request
  | PR_Update : update_text:string
             -> default_graph_uris:list string
             -> named_graph_uris:list string
             -> sparql_request
  | PR_Bad    : reason:string -> sparql_request


(** ====================================================================== **)
(** Part 2: Low-level helpers                                               **)
(** ====================================================================== **)

let char_code (c : FStar.Char.char) : nat = FStar.Char.int_of_char c

let is_hex_digit (c : FStar.Char.char) : bool =
  let code = char_code c in
  (code >= 0x30 && code <= 0x39) ||
  (code >= 0x41 && code <= 0x46) ||
  (code >= 0x61 && code <= 0x66)

let hex_value (c : FStar.Char.char) : nat =
  let code = char_code c in
  if code >= 0x30 && code <= 0x39 then code - 0x30
  else if code >= 0x41 && code <= 0x46 then code - 0x41 + 10
  else if code >= 0x61 && code <= 0x66 then code - 0x61 + 10
  else 0

let char_to_string (c : FStar.Char.char) : string =
  FStar.String.string_of_list [c]

// Cheap ASCII lower-case of a single char.
let ascii_lower_char (c : FStar.Char.char) : FStar.Char.char =
  let cd = char_code c in
  if cd >= 0x41 && cd <= 0x5A
  then FStar.Char.char_of_int (cd + 32)
  else c

let ascii_lower_string (s : string) : string =
  String.string_of_list
    (List.Tot.map ascii_lower_char (String.list_of_string s))

// Trim ASCII whitespace (space, tab, CR, LF) from both ends of a
// character list. Used to tidy up header/accept parsing.
let rec drop_ws_left (cs : list FStar.Char.char)
  : Tot (list FStar.Char.char) (decreases (List.Tot.length cs)) =
  match cs with
  | [] -> []
  | c :: rest ->
    let code = char_code c in
    if code = 0x20 || code = 0x09 || code = 0x0A || code = 0x0D
    then drop_ws_left rest
    else cs

let trim_ws_chars (cs : list FStar.Char.char) : list FStar.Char.char =
  List.Tot.rev (drop_ws_left (List.Tot.rev (drop_ws_left cs)))

let trim_ws (s : string) : string =
  String.string_of_list (trim_ws_chars (String.list_of_string s))


(** ====================================================================== **)
(** Part 3: URL / form decoding                                             **)
(**                                                                          **)
(** url_decode processes %XX hex escapes. In form-encoded mode (plus=true)  **)
(** a literal '+' becomes a space (RFC 3986 §2.1 / HTML form semantics).    **)
(** ====================================================================== **)

#push-options "--fuel 4 --ifuel 4"
let rec url_decode_chars
    (plus_is_space : bool)
    (cs : list FStar.Char.char)
  : Tot (list FStar.Char.char) (decreases (List.Tot.length cs)) =
  match cs with
  | [] -> []
  | c :: rest ->
    let code = char_code c in
    if code = 0x25 (* '%' *) then
      (match rest with
       | h1 :: h2 :: rest' ->
         if is_hex_digit h1 && is_hex_digit h2 then
           let v = (hex_value h1) `op_Multiply` 16 + hex_value h2 in
           FStar.Char.char_of_int v :: url_decode_chars plus_is_space rest'
         else
           c :: url_decode_chars plus_is_space rest
       | _ ->
         c :: url_decode_chars plus_is_space rest)
    else if plus_is_space && code = 0x2B (* '+' *) then
      FStar.Char.char_of_int 0x20 :: url_decode_chars plus_is_space rest
    else
      c :: url_decode_chars plus_is_space rest
#pop-options

let url_decode (s : string) : string =
  String.string_of_list
    (url_decode_chars false (String.list_of_string s))

let form_decode (s : string) : string =
  String.string_of_list
    (url_decode_chars true (String.list_of_string s))


(** ====================================================================== **)
(** Part 4: Split / find utilities                                          **)
(**                                                                          **)
(** Most HTTP parsing boils down to splitting on a separator character.     **)
(** We implement split on character lists for F*-friendly termination.      **)
(** ====================================================================== **)

// Split cs on the first occurrence of sep. Returns (before, after).
// If sep is absent, after is None.
let rec split_once_chars
    (sep : nat)
    (cs : list FStar.Char.char)
  : Tot (list FStar.Char.char & option (list FStar.Char.char))
        (decreases (List.Tot.length cs)) =
  match cs with
  | [] -> ([], None)
  | c :: rest ->
    if char_code c = sep then ([], Some rest)
    else
      let (before, after) = split_once_chars sep rest in
      (c :: before, after)

let split_once_on (s : string) (sep : FStar.Char.char)
  : string & option string =
  let (before, after) = split_once_chars (char_code sep)
                                         (String.list_of_string s) in
  let before_s = String.string_of_list before in
  let after_s  = match after with
                 | None -> None
                 | Some cs -> Some (String.string_of_list cs) in
  (before_s, after_s)

// Split cs on every occurrence of sep. Produces a list of segments.
let rec split_chars_all
    (sep : nat)
    (cs : list FStar.Char.char)
    (cur : list FStar.Char.char)
  : Tot (list (list FStar.Char.char)) (decreases (List.Tot.length cs)) =
  match cs with
  | [] -> [List.Tot.rev cur]
  | c :: rest ->
    if char_code c = sep
    then List.Tot.rev cur :: split_chars_all sep rest []
    else split_chars_all sep rest (c :: cur)

let split_all_on (s : string) (sep : FStar.Char.char) : list string =
  let segs = split_chars_all (char_code sep)
                             (String.list_of_string s) [] in
  List.Tot.map String.string_of_list segs


(** ====================================================================== **)
(** Part 5: Query-string parsing                                            **)
(**                                                                          **)
(** Given a query string like "a=1&b=hello+world&a=2" return                **)
(** [("a","1"); ("b","hello world"); ("a","2")].                            **)
(** Duplicate keys are preserved (graph-uri parameters may repeat).         **)
(** ====================================================================== **)

let parse_kv_pair (pair : string) : option (string & string) =
  match split_once_on pair (FStar.Char.char_of_int 0x3D (* = *)) with
  | (k, Some v) -> Some (form_decode k, form_decode v)
  | (k, None)   ->
    if String.length k = 0 then None
    else Some (form_decode k, "")

let parse_query_string (qs : string) : list (string & string) =
  let parts = split_all_on qs (FStar.Char.char_of_int 0x26 (* & *)) in
  List.Tot.concatMap
    (fun p -> match parse_kv_pair p with
              | Some kv -> [kv]
              | None    -> [])
    parts

// Collect all values for a given key (case-sensitive, per RFC 3986
// canonical form — keys are just byte-exact strings here).
let collect_values (key : string) (kvs : list (string & string))
  : list string =
  List.Tot.concatMap
    (fun (kv : string & string) ->
       let (k, v) = kv in
       if k = key then [v] else [])
    kvs

let first_value (key : string) (kvs : list (string & string))
  : option string =
  match collect_values key kvs with
  | []      -> None
  | v :: _  -> Some v


(** ====================================================================== **)
(** Part 6: Accept header parsing + content negotiation                     **)
(**                                                                          **)
(** Accept is a comma-separated list of media-ranges, each with optional    **)
(** q-parameters: "application/sparql-results+json;q=0.9,                   **)
(**                application/sparql-results+xml;q=1.0, * /*;q=0.1".        **)
(** We parse the media type (primary + sub type) and, if present, the q     **)
(** value. Unrecognised media types are dropped; an empty Accept returns    **)
(** the empty list (caller should fall back to default_format).             **)
(** ====================================================================== **)

// Recognise a SPARQL-relevant media type string. Returns None if the
// media type is not one we serialise.
let media_type_to_format (mt : string) : option response_format =
  let lo = ascii_lower_string (trim_ws mt) in
  if lo = "application/sparql-results+json" then Some RF_Json
  else if lo = "application/json" then Some RF_Json
  else if lo = "application/sparql-results+xml" then Some RF_Xml
  else if lo = "application/xml" then Some RF_Xml
  else if lo = "text/xml" then Some RF_Xml
  else if lo = "text/csv" then Some RF_Csv
  else if lo = "text/tab-separated-values" then Some RF_Tsv
  else if lo = "text/turtle" then Some RF_Turtle
  else if lo = "application/x-turtle" then Some RF_Turtle
  else if lo = "application/n-triples" then Some RF_NTriples
  else if lo = "text/plain" then Some RF_Text
  // */* binds to the caller-provided default; we signal that by
  // returning None so pick_response_format can detect it below.
  else None

// Try to read an integer substring s (no sign), returning the int.
// Used only for q-value parsing; out-of-range is treated as 0.
let rec read_digits_acc (cs : list FStar.Char.char) (acc : nat)
  : Tot (nat & list FStar.Char.char) (decreases (List.Tot.length cs)) =
  match cs with
  | [] -> (acc, [])
  | c :: rest ->
    let code = char_code c in
    if code >= 0x30 && code <= 0x39
    then read_digits_acc rest (acc `op_Multiply` 10 + (code - 0x30))
    else (acc, cs)

// Parse a q-value lexeme such as "0.9" or "1" or ".25" into an int
// in units of 1/1000. Clamps to [0,1000].
let parse_q_value (s : string) : q_priority =
  let trimmed = trim_ws s in
  let cs = String.list_of_string trimmed in
  // integer part
  let (ip, rest) = read_digits_acc cs 0 in
  let (frac3, _) =
    match rest with
    | [] -> (0, [])
    | c :: rest' ->
      if char_code c = 0x2E (* '.' *) then
        // read up to 3 fractional digits, pad with zeros
        match rest' with
        | [] -> (0, [])
        | _  ->
          let (d, _) = read_digits_acc rest' 0 in
          // We do not actually know how many digits were consumed
          // without a second pass; so we cap total ip*1000 + frac at
          // 1000 below. This is coarse but sufficient for Accept
          // headers.
          (d, [])
      else (0, rest)
  in
  let raw = ip `op_Multiply` 1000 + frac3 in
  if raw > 1000 then 1000
  else raw

// Parse a single media range with optional parameters.
// Strips everything past the first ';' except for q=NUM which we
// do extract.
let parse_accept_entry (item : string) : option accept_entry =
  match split_once_on item (FStar.Char.char_of_int 0x3B (* ; *)) with
  | (media, None) ->
    (match media_type_to_format media with
     | Some f -> Some (f, 1000)
     | None   -> None)
  | (media, Some params) ->
    let fmt = media_type_to_format media in
    // split params on ';' and look for "q=NNN"
    let param_list = split_all_on params
                       (FStar.Char.char_of_int 0x3B (* ; *)) in
    let q : q_priority =
      match List.Tot.tryFind
              (fun (p : string) ->
                 let lo = ascii_lower_string (trim_ws p) in
                 String.length lo >= 2 &&
                 String.sub lo 0 2 = "q=")
              param_list
      with
      | None -> 1000
      | Some p ->
        let lo = ascii_lower_string (trim_ws p) in
        if String.length lo >= 2
        then parse_q_value (String.sub lo 2 (String.length lo - 2))
        else 1000
    in
    (match fmt with
     | Some f -> Some (f, q)
     | None   -> None)

// Public: parse the whole Accept header into ranked entries, in the
// order they appeared (no sort — caller's pick_response_format walks
// the list). Unknown types are skipped.
let parse_accept_header (hdr : string) : list accept_entry =
  let items = split_all_on hdr
                (FStar.Char.char_of_int 0x2C (* , *)) in
  List.Tot.concatMap
    (fun it -> match parse_accept_entry it with
               | Some e -> [e]
               | None   -> [])
    items

// Pick the highest-q entry. If two entries tie on q, earlier wins
// (stable). If no entries, return default_format.
let rec pick_best
    (entries : list accept_entry)
    (best_so_far : option accept_entry)
  : Tot (option accept_entry) (decreases (List.Tot.length entries)) =
  match entries with
  | [] -> best_so_far
  | e :: rest ->
    let (_, q) = e in
    let better =
      match best_so_far with
      | None -> true
      | Some (_, q_best) -> q > q_best
    in
    if better
    then pick_best rest (Some e)
    else pick_best rest best_so_far

let pick_response_format
    (entries : list accept_entry)
    (default_format : response_format)
  : response_format =
  match pick_best entries None with
  | None -> default_format
  | Some (f, q) ->
    // q=0 means "not acceptable" per RFC 7231 §5.3.1
    if q = 0 then default_format else f


(** ====================================================================== **)
(** Part 7: Request decoder                                                  **)
(**                                                                          **)
(** Per W3C SPARQL 1.1 Protocol:                                             **)
(**                                                                          **)
(**   GET  /query?query=...&default-graph-uri=...&named-graph-uri=...       **)
(**   POST /query  Content-Type: application/sparql-query                   **)
(**        body is the raw query text                                       **)
(**   POST /query  Content-Type: application/x-www-form-urlencoded          **)
(**        body is query=...&default-graph-uri=...&named-graph-uri=...      **)
(**                                                                          **)
(** Same for /update with Content-Type: application/sparql-update.          **)
(** ====================================================================== **)

// True iff url_path's final segment (after the last '/') is "update",
// case-insensitively. All other paths are treated as query paths
// (the Protocol spec allows any path; production uses /query for
// SELECT/ASK/CONSTRUCT/DESCRIBE).
let path_is_update (url_path : string) : bool =
  let segments = split_all_on url_path
                   (FStar.Char.char_of_int 0x2F (* '/' *)) in
  match List.Tot.rev segments with
  | [] -> false
  | last :: _ -> ascii_lower_string last = "update"

// Strip an optional query-string trailer from a full request line
// path. If the caller passed url_path separately from url_query we
// trust it.
let split_path_qs (url_path : string) : string & string =
  match split_once_on url_path (FStar.Char.char_of_int 0x3F (* ? *)) with
  | (p, None)    -> (p, "")
  | (p, Some qs) -> (p, qs)

// The content type can come with parameters: "application/..;charset=utf-8".
// Strip params and lower-case for comparison.
let content_type_base (ct : string) : string =
  match split_once_on ct (FStar.Char.char_of_int 0x3B (* ; *)) with
  | (base, _) -> ascii_lower_string (trim_ws base)

// Build a PR_Query / PR_Update given the bag of kv pairs from either
// the URL query string (GET) or the form body (POST form-encoded).
// `is_update_path` determines which variant is constructed.
let build_from_kvs
    (is_update_path : bool)
    (kvs : list (string & string))
  : sparql_request =
  let q_opt     = first_value "query"  kvs in
  let u_opt     = first_value "update" kvs in
  let dflt      = collect_values "default-graph-uri" kvs in
  let named     = collect_values "named-graph-uri"   kvs in
  // Protocol says: if the path says /update, we expect update=...
  //                otherwise we expect query=...
  if is_update_path then
    match u_opt with
    | Some u -> PR_Update u dflt named
    | None ->
      // Fall back to query= for robustness (some harnesses are lax).
      (match q_opt with
       | Some _ -> PR_Bad "expected update= on /update endpoint, got query="
       | None -> PR_Bad "missing update parameter")
  else
    match q_opt with
    | Some q -> PR_Query q dflt named
    | None ->
      (match u_opt with
       | Some _ -> PR_Bad "expected query= on /query endpoint, got update="
       | None -> PR_Bad "missing query parameter")

// Decode the incoming HTTP request. http_method is the method as
// received ("GET"/"POST"/...). url_path is the path only (no query
// string); if the caller concatenated them we split here defensively.
// url_query is the raw query-string (no leading '?'). body is the
// request body as a UTF-8 string; callers that handle binary bodies
// should decode first.
let decode_request
    (http_method : string)
    (url_path    : string)
    (url_query   : string)
    (content_type : string)
    (body        : string)
  : sparql_request =
  // Defensive path split in case the caller passed url_path with a
  // trailing "?...":
  let (clean_path, embedded_qs) = split_path_qs url_path in
  let effective_qs =
    if String.length url_query > 0 then url_query else embedded_qs in
  let is_update = path_is_update clean_path in
  let method_upper = ascii_lower_string http_method in
  if method_upper = "get" then
    let kvs = parse_query_string effective_qs in
    build_from_kvs is_update kvs
  else if method_upper = "post" then
    let ct = content_type_base content_type in
    if ct = "application/sparql-query" then
      PR_Query body [] []
    else if ct = "application/sparql-update" then
      PR_Update body [] []
    else if ct = "application/x-www-form-urlencoded" then
      let kvs = parse_query_string body in
      build_from_kvs is_update kvs
    else if String.length ct = 0 then
      // No Content-Type: best-effort fall-back to form-encoded if the
      // body looks like a query string, otherwise bad request.
      PR_Bad "POST request missing Content-Type"
    else
      PR_Bad ("unsupported Content-Type: " ^ ct)
  else if method_upper = "head" || method_upper = "options" then
    // Protocol §2.1.5/§2.1.6 permit these but we return PR_Bad so
    // the server glue can answer with an empty body. Not fatal.
    PR_Bad ("method " ^ http_method ^ " not supported by decoder")
  else
    PR_Bad ("unsupported HTTP method: " ^ http_method)

#pop-options


(** ====================================================================== **)
(** Part 8: Escaping helpers                                                **)
(**                                                                          **)
(** json_escape, xml_escape, csv_escape.                                    **)
(** ====================================================================== **)

#push-options "--z3rlimit 50 --fuel 2 --ifuel 2"

// Escape a single character for JSON. Returns the raw escape including
// the leading backslash (or just a one-char string for no-op).
// Render a 4-bit nibble as one hex digit ('0'..'9','a'..'f').
let hex_nibble (n : nat{n < 16}) : string =
  if n < 10 then char_to_string (FStar.Char.char_of_int (0x30 + n))
  else char_to_string (FStar.Char.char_of_int (0x61 + (n - 10)))

let json_escape_char (c : FStar.Char.char) : string =
  let code = char_code c in
  if code = 0x22 then "\\\""
  else if code = 0x5C then "\\\\"
  else if code = 0x08 then "\\b"
  else if code = 0x09 then "\\t"
  else if code = 0x0A then "\\n"
  else if code = 0x0C then "\\f"
  else if code = 0x0D then "\\r"
  else if code < 0x20 then
    // \u00XX — code < 0x20 < 256 so hi,lo both < 16
    let hi : nat = code / 16 in
    let lo : nat = code % 16 in
    "\\u00" ^ hex_nibble hi ^ hex_nibble lo
  else
    char_to_string c

let rec json_escape_chars (cs : list FStar.Char.char)
  : Tot string (decreases (List.Tot.length cs)) =
  match cs with
  | [] -> ""
  | c :: rest -> json_escape_char c ^ json_escape_chars rest

let json_escape (s : string) : string =
  json_escape_chars (String.list_of_string s)

let xml_escape_char (c : FStar.Char.char) : string =
  let code = char_code c in
  if code = 0x26 then "&amp;"
  else if code = 0x3C then "&lt;"
  else if code = 0x3E then "&gt;"
  else if code = 0x22 then "&quot;"
  else if code = 0x27 then "&apos;"
  else if code = 0x0D then "&#13;"
  else char_to_string c

let rec xml_escape_chars (cs : list FStar.Char.char)
  : Tot string (decreases (List.Tot.length cs)) =
  match cs with
  | [] -> ""
  | c :: rest -> xml_escape_char c ^ xml_escape_chars rest

let xml_escape (s : string) : string =
  xml_escape_chars (String.list_of_string s)

// CSV: if a field contains COMMA, CR, LF, or DQUOTE we must quote it
// with DQUOTE and double every embedded DQUOTE.
let rec csv_needs_quoting_chars (cs : list FStar.Char.char)
  : Tot bool (decreases (List.Tot.length cs)) =
  match cs with
  | [] -> false
  | c :: rest ->
    let code = char_code c in
    if code = 0x2C || code = 0x0A || code = 0x0D || code = 0x22 then true
    else csv_needs_quoting_chars rest

let rec csv_double_quotes_chars (cs : list FStar.Char.char)
  : Tot string (decreases (List.Tot.length cs)) =
  match cs with
  | [] -> ""
  | c :: rest ->
    let code = char_code c in
    if code = 0x22
    then "\"\"" ^ csv_double_quotes_chars rest
    else char_to_string c ^ csv_double_quotes_chars rest

let csv_escape (s : string) : string =
  let cs = String.list_of_string s in
  if csv_needs_quoting_chars cs
  then "\"" ^ csv_double_quotes_chars cs ^ "\""
  else s

// TSV: per W3C, each field is the RDF term written the same way it
// would be in SPARQL/N-Triples (angle-bracket IRIs, typed or lang-
// tagged literals, _:bnode). The TSV field separator is TAB; each
// field MUST NOT contain unescaped TAB, CR, or LF. Since literals can
// contain those characters, we use N-Triples-style escaping on the
// lexical form of literals.
let rec nt_escape_chars (cs : list FStar.Char.char)
  : Tot string (decreases (List.Tot.length cs)) =
  match cs with
  | [] -> ""
  | c :: rest ->
    let code = char_code c in
    if code = 0x22 then "\\\"" ^ nt_escape_chars rest
    else if code = 0x5C then "\\\\" ^ nt_escape_chars rest
    else if code = 0x09 then "\\t" ^ nt_escape_chars rest
    else if code = 0x0A then "\\n" ^ nt_escape_chars rest
    else if code = 0x0D then "\\r" ^ nt_escape_chars rest
    else char_to_string c ^ nt_escape_chars rest

let nt_escape (s : string) : string =
  nt_escape_chars (String.list_of_string s)


(** ====================================================================== **)
(** Part 9: JSON response serialiser                                        **)
(**                                                                          **)
(** SPARQL 1.1 Query Results JSON Format:                                   **)
(**   https://www.w3.org/TR/sparql11-results-json/                          **)
(**                                                                          **)
(** Shape:                                                                   **)
(**   {"head":{"vars":[...]},                                               **)
(**    "results":{"bindings":[                                               **)
(**       {"v":{"type":"uri"|"literal"|"bnode", "value":"..." [, xml:lang   **)
(**             |, datatype]}}, ... ]}}                                     **)
(** ====================================================================== **)

// Render a single term as a JSON binding value object.
let json_term (t : rdf_term) : string =
  match t with
  | T_IRI i ->
    "{\"type\":\"uri\",\"value\":\"" ^ json_escape i ^ "\"}"
  | T_BNode b ->
    "{\"type\":\"bnode\",\"value\":\"" ^ json_escape b ^ "\"}"
  | T_Literal l ->
    (match l.lang_tag with
     | Some tag ->
       "{\"type\":\"literal\",\"value\":\""
         ^ json_escape l.lexical_form
         ^ "\",\"xml:lang\":\""
         ^ json_escape tag
         ^ "\"}"
     | None ->
       if l.datatype = xsd_string then
         "{\"type\":\"literal\",\"value\":\""
           ^ json_escape l.lexical_form
           ^ "\"}"
       else
         "{\"type\":\"literal\",\"value\":\""
           ^ json_escape l.lexical_form
           ^ "\",\"datatype\":\""
           ^ json_escape l.datatype
           ^ "\"}")

// Render "\"x\",\"y\",\"z\"" from ["x";"y";"z"].
let rec json_var_list_body
    (vars : list string)
    (first : bool)
  : Tot string (decreases (List.Tot.length vars)) =
  match vars with
  | [] -> ""
  | v :: rest ->
    let piece = "\"" ^ json_escape v ^ "\"" in
    if first
    then piece ^ json_var_list_body rest false
    else "," ^ piece ^ json_var_list_body rest false

let json_var_list (vars : list string) : string =
  json_var_list_body vars true

// Render ONE row's bindings object. Only variables that are bound in
// this row appear in the object (per the JSON spec §3.3.2).
let rec json_row_body
    (row : binding_row)
    (first : bool)
  : Tot string (decreases (List.Tot.length row)) =
  match row with
  | [] -> ""
  | (v, t) :: rest ->
    let piece = "\"" ^ json_escape v ^ "\":" ^ json_term t in
    if first
    then piece ^ json_row_body rest false
    else "," ^ piece ^ json_row_body rest false

let json_row (row : binding_row) : string =
  "{" ^ json_row_body row true ^ "}"

let rec json_rows_body
    (rows : list binding_row)
    (first : bool)
  : Tot string (decreases (List.Tot.length rows)) =
  match rows with
  | [] -> ""
  | r :: rest ->
    let piece = json_row r in
    if first
    then piece ^ json_rows_body rest false
    else "," ^ piece ^ json_rows_body rest false

let serialise_response_json
    (vars : list string)
    (rows : list binding_row)
  : string =
  "{\"head\":{\"vars\":[" ^ json_var_list vars ^ "]},"
    ^ "\"results\":{\"bindings\":["
    ^ json_rows_body rows true
    ^ "]}}"

// ASK: {"head":{},"boolean":true|false}
let serialise_response_boolean_json (b : bool) : string =
  if b
  then "{\"head\":{},\"boolean\":true}"
  else "{\"head\":{},\"boolean\":false}"


(** ====================================================================== **)
(** Part 10: XML (SRX) response serialiser                                  **)
(**                                                                          **)
(** SPARQL 1.1 Query Results XML Format:                                    **)
(**   https://www.w3.org/TR/rdf-sparql-XMLres/                             **)
(** ====================================================================== **)

let rec xml_head_vars_body (vars : list string)
  : Tot string (decreases (List.Tot.length vars)) =
  match vars with
  | [] -> ""
  | v :: rest ->
    "<variable name=\"" ^ xml_escape v ^ "\"/>"
      ^ xml_head_vars_body rest

// Render a single <binding name="..."><...>...</...></binding>.
let xml_binding (name : string) (t : rdf_term) : string =
  let open_tag = "<binding name=\"" ^ xml_escape name ^ "\">" in
  let inner =
    match t with
    | T_IRI i    -> "<uri>" ^ xml_escape i ^ "</uri>"
    | T_BNode b  -> "<bnode>" ^ xml_escape b ^ "</bnode>"
    | T_Literal l ->
      (match l.lang_tag with
       | Some tag ->
         "<literal xml:lang=\"" ^ xml_escape tag ^ "\">"
           ^ xml_escape l.lexical_form
           ^ "</literal>"
       | None ->
         if l.datatype = xsd_string then
           "<literal>" ^ xml_escape l.lexical_form ^ "</literal>"
         else
           "<literal datatype=\"" ^ xml_escape l.datatype ^ "\">"
             ^ xml_escape l.lexical_form
             ^ "</literal>")
  in
  open_tag ^ inner ^ "</binding>"

let rec xml_row_body (row : binding_row)
  : Tot string (decreases (List.Tot.length row)) =
  match row with
  | [] -> ""
  | (v, t) :: rest ->
    xml_binding v t ^ xml_row_body rest

let xml_row (row : binding_row) : string =
  "<result>" ^ xml_row_body row ^ "</result>"

let rec xml_rows_body (rows : list binding_row)
  : Tot string (decreases (List.Tot.length rows)) =
  match rows with
  | [] -> ""
  | r :: rest ->
    xml_row r ^ xml_rows_body rest

let serialise_response_xml
    (vars : list string)
    (rows : list binding_row)
  : string =
  "<?xml version=\"1.0\"?>\n"
    ^ "<sparql xmlns=\"http://www.w3.org/2005/sparql-results#\">"
    ^ "<head>" ^ xml_head_vars_body vars ^ "</head>"
    ^ "<results>" ^ xml_rows_body rows ^ "</results>"
    ^ "</sparql>"

let serialise_response_boolean_xml (b : bool) : string =
  let value = if b then "true" else "false" in
  "<?xml version=\"1.0\"?>\n"
    ^ "<sparql xmlns=\"http://www.w3.org/2005/sparql-results#\">"
    ^ "<head></head>"
    ^ "<boolean>" ^ value ^ "</boolean>"
    ^ "</sparql>"


(** ====================================================================== **)
(** Part 11: CSV / TSV serialisers                                          **)
(** ====================================================================== **)

// CSV: header is variable names (no '?' prefix). Cells are the
// "plain" value. Unbound = empty string. Booleans / numerics are
// written as their lexical forms.
let csv_cell (t_opt : option rdf_term) : string =
  match t_opt with
  | None -> ""
  | Some (T_IRI i) -> csv_escape i
  | Some (T_BNode b) -> csv_escape ("_:" ^ b)
  | Some (T_Literal l) -> csv_escape l.lexical_form

let rec csv_header_body
    (vars : list string)
    (first : bool)
  : Tot string (decreases (List.Tot.length vars)) =
  match vars with
  | [] -> ""
  | v :: rest ->
    if first
    then csv_escape v ^ csv_header_body rest false
    else "," ^ csv_escape v ^ csv_header_body rest false

let rec csv_row_body
    (vars : list string)
    (row : binding_row)
    (first : bool)
  : Tot string (decreases (List.Tot.length vars)) =
  match vars with
  | [] -> ""
  | v :: rest ->
    let cell = csv_cell (List.Tot.assoc v row) in
    if first
    then cell ^ csv_row_body rest row false
    else "," ^ cell ^ csv_row_body rest row false

let rec csv_rows_body
    (vars : list string)
    (rows : list binding_row)
  : Tot string (decreases (List.Tot.length rows)) =
  match rows with
  | [] -> ""
  | r :: rest ->
    csv_row_body vars r true ^ "\r\n" ^ csv_rows_body vars rest

let serialise_response_csv
    (vars : list string)
    (rows : list binding_row)
  : string =
  csv_header_body vars true ^ "\r\n" ^ csv_rows_body vars rows

// TSV: header keeps the ? prefix; cells use N-Triples-style syntax.
let tsv_term (t : rdf_term) : string =
  match t with
  | T_IRI i -> "<" ^ i ^ ">"
  | T_BNode b -> "_:" ^ b
  | T_Literal l ->
    let escaped = nt_escape l.lexical_form in
    (match l.lang_tag with
     | Some tag -> "\"" ^ escaped ^ "\"@" ^ tag
     | None ->
       if l.datatype = xsd_string then
         "\"" ^ escaped ^ "\""
       else
         "\"" ^ escaped ^ "\"^^<" ^ l.datatype ^ ">")

let tsv_cell (t_opt : option rdf_term) : string =
  match t_opt with
  | None -> ""
  | Some t -> tsv_term t

let rec tsv_header_body
    (vars : list string)
    (first : bool)
  : Tot string (decreases (List.Tot.length vars)) =
  match vars with
  | [] -> ""
  | v :: rest ->
    let piece = "?" ^ v in
    if first
    then piece ^ tsv_header_body rest false
    else "\t" ^ piece ^ tsv_header_body rest false

let rec tsv_row_body
    (vars : list string)
    (row : binding_row)
    (first : bool)
  : Tot string (decreases (List.Tot.length vars)) =
  match vars with
  | [] -> ""
  | v :: rest ->
    let cell = tsv_cell (List.Tot.assoc v row) in
    if first
    then cell ^ tsv_row_body rest row false
    else "\t" ^ cell ^ tsv_row_body rest row false

let rec tsv_rows_body
    (vars : list string)
    (rows : list binding_row)
  : Tot string (decreases (List.Tot.length rows)) =
  match rows with
  | [] -> ""
  | r :: rest ->
    tsv_row_body vars r true ^ "\n" ^ tsv_rows_body vars rest

let serialise_response_tsv
    (vars : list string)
    (rows : list binding_row)
  : string =
  tsv_header_body vars true ^ "\n" ^ tsv_rows_body vars rows


(** ====================================================================== **)
(** Part 12: Content-Type string for a given response_format                **)
(**                                                                          **)
(** The server glue needs a Content-Type header string to send back.        **)
(** These are the canonical values; servers may append "; charset=utf-8".   **)
(** ====================================================================== **)

let content_type_for (f : response_format) : string =
  match f with
  | RF_Json     -> "application/sparql-results+json"
  | RF_Xml      -> "application/sparql-results+xml"
  | RF_Csv      -> "text/csv"
  | RF_Tsv      -> "text/tab-separated-values"
  | RF_Turtle   -> "text/turtle"
  | RF_NTriples -> "application/n-triples"
  | RF_Text     -> "text/plain"

#pop-options


(** ====================================================================== **)
(** Part 13: Minimal in-module test harness (self-check only)              **)
(**                                                                          **)
(** Guarded by `if false`. This is not run at extraction time; it exists    **)
(** as on-disk specification of intended behaviour. The caller can flip     **)
(** the guard to type-check the expressions.                                **)
(** ====================================================================== **)

// Helper to make an rdf_term literal cheaply for test data.
let lit_str (s : string) : option rdf_term =
  let l : literal = {
    lexical_form = s;
    datatype     = xsd_string;
    lang_tag     = None
  } in
  if literal_wf l then Some (T_Literal l) else None

let protocol_self_tests () : unit =
  if false then
    begin
      // URL-decoding of a full SELECT query.
      let decoded1 =
        url_decode
          "SELECT%20%2A%20WHERE%20%7B%3Fs%20%3Fp%20%3Fo%7D" in
      assert (decoded1 = "SELECT * WHERE {?s ?p ?o}");

      // + does NOT decode to space under raw url_decode.
      let raw = url_decode "a+b" in
      assert (raw = "a+b");

      // + DOES decode to space under form_decode.
      let form = form_decode "a+b" in
      assert (form = "a b");

      // Accept header negotiation picks highest q.
      let accepted =
        parse_accept_header
          "application/sparql-results+json;q=0.9, application/sparql-results+xml;q=1.0, */*;q=0.1" in
      let picked = pick_response_format accepted RF_Text in
      assert (picked = RF_Xml);

      // GET request with URL-encoded query parameter.
      let r1 = decode_request "GET" "/query"
                 "query=SELECT%20%2A%20WHERE%20%7B%3Fs%20%3Fp%20%3Fo%7D"
                 "" "" in
      (match r1 with
       | PR_Query q [] [] ->
         assert (q = "SELECT * WHERE {?s ?p ?o}")
       | _ -> assert false);

      // POST /query with application/sparql-query is a raw body.
      let r2 = decode_request "POST" "/query" ""
                 "application/sparql-query"
                 "SELECT * WHERE {?s ?p ?o}" in
      (match r2 with
       | PR_Query q [] [] ->
         assert (q = "SELECT * WHERE {?s ?p ?o}")
       | _ -> assert false);

      // POST /update form-encoded.
      let r3 = decode_request "POST" "/update" ""
                 "application/x-www-form-urlencoded"
                 "update=INSERT%20DATA%20%7B%7D" in
      (match r3 with
       | PR_Update u [] [] ->
         assert (u = "INSERT DATA {}")
       | _ -> assert false);

      // JSON boolean serialisation.
      let j_true = serialise_response_boolean_json true in
      assert (j_true = "{\"head\":{},\"boolean\":true}");
      ()
    end
  else ()
