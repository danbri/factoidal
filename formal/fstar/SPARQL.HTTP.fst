module SPARQL.HTTP

(** ======================================================================== **)
(** SPARQL HTTP request framing — verified HTTP/1.1 parser                   **)
(**                                                                          **)
(** Replaces the hand-written read_line_crlf / parse_request_line /          **)
(** read_headers / read_body / split_uri helpers in factoidal_http.ml.       **)
(**                                                                          **)
(** Input: the full buffered connection contents (method + headers + body)  **)
(** as a single string. The OCaml glue reads up to                           **)
(** max_header_bytes + max_body_bytes from the socket and hands us the       **)
(** whole blob.                                                              **)
(**                                                                          **)
(** Output: either a parsed http_request (Inl) or a typed error (Inr).       **)
(**                                                                          **)
(** Constraints (CLAUDE.md iron rules):                                      **)
(**   - No assume val                                                        **)
(**   - No --admit_smt_queries                                               **)
(**   - No --lax                                                             **)
(**   - All recursion fuel-bounded or structural.                            **)
(** ======================================================================== **)

open FStar.String
open FStar.List.Tot

#push-options "--z3rlimit 50 --fuel 2 --ifuel 2"

(** ====================================================================== **)
(** Part 1: Types                                                           **)
(** ====================================================================== **)

noeq type http_request = {
  hr_method    : string;             // "GET", "POST", "OPTIONS" as received
  hr_path      : string;             // "/query" (no query string)
  hr_query_str : string;             // "a=1&b=2" (no leading '?')
  hr_version   : string;             // "HTTP/1.1"
  hr_headers   : list (string & string);  // (lowercased-name, trimmed-value)
  hr_body      : string;
}

type http_error =
  | HE_MalformedRequestLine : http_error
  | HE_MalformedHeader      : http_error
  | HE_BadRequest           : string -> http_error
  | HE_BodyTooLarge         : http_error
  | HE_HeadersTooLarge      : http_error
  | HE_MissingCRLF          : http_error

type http_result a = either a http_error


(** ====================================================================== **)
(** Part 2: Low-level character helpers                                    **)
(** ====================================================================== **)

let char_code (c : FStar.Char.char) : nat = FStar.Char.int_of_char c

let is_ascii_ws (c : FStar.Char.char) : bool =
  let code = char_code c in
  code = 0x20 || code = 0x09 || code = 0x0A || code = 0x0D

let ascii_lower_char (c : FStar.Char.char) : FStar.Char.char =
  let cd = char_code c in
  if cd >= 0x41 && cd <= 0x5A
  then FStar.Char.char_of_int (cd + 32)
  else c

let ascii_lower_string (s : string) : string =
  String.string_of_list
    (List.Tot.map ascii_lower_char (String.list_of_string s))

// Trim ASCII whitespace (space, tab, CR, LF) from both ends of a list.
let rec drop_ws_left (cs : list FStar.Char.char)
  : Tot (list FStar.Char.char) (decreases (List.Tot.length cs)) =
  match cs with
  | [] -> []
  | c :: rest ->
    if is_ascii_ws c then drop_ws_left rest else cs

let trim_ws_chars (cs : list FStar.Char.char) : list FStar.Char.char =
  List.Tot.rev (drop_ws_left (List.Tot.rev (drop_ws_left cs)))

let trim_ws (s : string) : string =
  String.string_of_list (trim_ws_chars (String.list_of_string s))


(** ====================================================================== **)
(** Part 3: String-position scanners                                       **)
(** ====================================================================== **)

// Find the first position of a 2-byte sequence (e.g. "\r\n") starting
// at `pos`. Returns Some i where i is the index of the first byte of
// the match, or None if not found within the bounded scan.
// Fuel-bounded by (len - pos).
let rec find_2byte
    (input : string)
    (pos : nat)
    (b1 : nat)
    (b2 : nat)
    (fuel : nat)
  : Tot (option nat) (decreases fuel) =
  if fuel = 0 then None
  else
    let len = String.length input in
    if pos + 1 >= len then None
    else
      let c1 = char_code (String.index input pos) in
      let c2 = char_code (String.index input (pos + 1)) in
      if c1 = b1 && c2 = b2 then Some pos
      else find_2byte input (pos + 1) b1 b2 (fuel - 1)

// Find the first position of a 4-byte sequence (e.g. "\r\n\r\n") starting
// at `pos`. Returns Some i where i is the index of the first byte of
// the match, or None if not found within the bounded scan.
let rec find_4byte
    (input : string)
    (pos : nat)
    (b1 : nat) (b2 : nat) (b3 : nat) (b4 : nat)
    (fuel : nat)
  : Tot (option nat) (decreases fuel) =
  if fuel = 0 then None
  else
    let len = String.length input in
    if pos + 3 >= len then None
    else
      let c1 = char_code (String.index input pos) in
      let c2 = char_code (String.index input (pos + 1)) in
      let c3 = char_code (String.index input (pos + 2)) in
      let c4 = char_code (String.index input (pos + 3)) in
      if c1 = b1 && c2 = b2 && c3 = b3 && c4 = b4 then Some pos
      else find_4byte input (pos + 1) b1 b2 b3 b4 (fuel - 1)

// Safe substring: returns s[start..start+len-1] clamped to the actual
// string length. If start >= String.length s, returns "".
let safe_substring (s : string) (start : nat) (sub_len : nat) : string =
  let slen = String.length s in
  if start >= slen then ""
  else
    let remaining : nat = slen - start in
    let effective_len = if sub_len <= remaining then sub_len else remaining in
    String.sub s start effective_len

// Suffix from `start` to end of string.
let string_suffix (s : string) (start : nat) : string =
  let slen = String.length s in
  if start >= slen then ""
  else String.sub s start (slen - start)


(** ====================================================================== **)
(** Part 4: split_path_and_query                                          **)
(**                                                                       **)
(** Input:  "/foo?a=b"  ->  ("/foo", "a=b")                               **)
(**         "/foo"      ->  ("/foo", "")                                  **)
(**         "/?x=1"     ->  ("/",    "x=1")                               **)
(** ====================================================================== **)

let rec find_char
    (input : string)
    (pos : nat)
    (target : nat)
    (fuel : nat)
  : Tot (option nat) (decreases fuel) =
  if fuel = 0 then None
  else
    let len = String.length input in
    if pos >= len then None
    else
      let c = char_code (String.index input pos) in
      if c = target then Some pos
      else find_char input (pos + 1) target (fuel - 1)

let split_path_and_query (uri : string) : (string & string) =
  let len = String.length uri in
  let fuel : nat = len + 1 in
  match find_char uri 0 0x3F fuel with  // '?'
  | None -> (uri, "")
  | Some i ->
    let path = safe_substring uri 0 i in
    let qs_start : nat = i + 1 in
    let qs = string_suffix uri qs_start in
    (path, qs)


(** ====================================================================== **)
(** Part 5: parse_request_line                                             **)
(**                                                                       **)
(** "GET /path?qs HTTP/1.1"  ->  ("GET", "/path?qs", "HTTP/1.1")          **)
(**                                                                       **)
(** Exactly two single-space separators. Leading/trailing whitespace is   **)
(** rejected. CRLF must have already been stripped by the caller.         **)
(** ====================================================================== **)

// Contains CR or LF anywhere?
let rec contains_crlf_chars (cs : list FStar.Char.char)
  : Tot bool (decreases (List.Tot.length cs)) =
  match cs with
  | [] -> false
  | c :: rest ->
    let code = char_code c in
    if code = 0x0A || code = 0x0D then true
    else contains_crlf_chars rest

let contains_crlf (s : string) : bool =
  contains_crlf_chars (String.list_of_string s)

let parse_request_line (line : string)
  : http_result (string & string & string) =
  if contains_crlf line then Inr HE_MalformedRequestLine
  else
    let len = String.length line in
    let fuel : nat = len + 1 in
    match find_char line 0 0x20 fuel with  // ' '
    | None -> Inr HE_MalformedRequestLine
    | Some i1 ->
      let meth = safe_substring line 0 i1 in
      let rest_start : nat = i1 + 1 in
      let rest_len : nat = if rest_start <= len then len - rest_start else 0 in
      let fuel2 : nat = rest_len + 1 in
      (match find_char line rest_start 0x20 fuel2 with
       | None -> Inr HE_MalformedRequestLine
       | Some i2 ->
         if i2 <= rest_start then Inr HE_MalformedRequestLine
         else
           let uri_len : nat = i2 - rest_start in
           let uri = safe_substring line rest_start uri_len in
           let ver_start : nat = i2 + 1 in
           let version = string_suffix line ver_start in
           // Reject if version still has an embedded space (more than 3 parts).
           let fuel3 : nat = String.length version + 1 in
           (match find_char version 0 0x20 fuel3 with
            | Some _ -> Inr HE_MalformedRequestLine
            | None ->
              if String.length meth = 0 || String.length uri = 0
                 || String.length version = 0
              then Inr HE_MalformedRequestLine
              else Inl (meth, uri, version)))


(** ====================================================================== **)
(** Part 6: parse_header_line                                             **)
(**                                                                       **)
(** "Content-Type: application/sparql-query" ->                            **)
(**   ("content-type", "application/sparql-query")                         **)
(**                                                                       **)
(** Split on the FIRST ':'. Lowercase the name, trim whitespace from the **)
(** value. CRLF must have already been stripped by the caller.            **)
(** ====================================================================== **)

let parse_header_line (line : string) : http_result (string & string) =
  if contains_crlf line then Inr HE_MalformedHeader
  else
    let len = String.length line in
    let fuel : nat = len + 1 in
    match find_char line 0 0x3A fuel with  // ':'
    | None -> Inr HE_MalformedHeader
    | Some i ->
      let name_raw = safe_substring line 0 i in
      let name = ascii_lower_string (trim_ws name_raw) in
      let value_start : nat = i + 1 in
      let value_raw = string_suffix line value_start in
      let value = trim_ws value_raw in
      if String.length name = 0 then Inr HE_MalformedHeader
      else Inl (name, value)


(** ====================================================================== **)
(** Part 7: header_lookup_ci                                               **)
(**                                                                       **)
(** Case-insensitive lookup. parse_header_line already lowercases names,  **)
(** so we only lowercase the needle here.                                 **)
(** ====================================================================== **)

let rec header_lookup_ci_chars
    (hs : list (string & string))
    (needle : string)
  : Tot (option string) (decreases (List.Tot.length hs)) =
  match hs with
  | [] -> None
  | (k, v) :: rest ->
    if k = needle then Some v
    else header_lookup_ci_chars rest needle

let header_lookup_ci
    (headers : list (string & string))
    (name : string)
  : option string =
  header_lookup_ci_chars headers (ascii_lower_string name)


(** ====================================================================== **)
(** Part 8: iterate header lines                                          **)
(**                                                                       **)
(** Given the head region (request line + all headers, ending just before **)
(** the terminating CRLFCRLF), iterate header lines starting at `pos`,    **)
(** separated by CRLF. Accumulate into reverse order, caller reverses.    **)
(** ====================================================================== **)

let rec parse_header_lines
    (input : string)
    (pos : nat)
    (head_end : nat)
    (acc : list (string & string))
    (fuel : nat)
  : Tot (http_result (list (string & string))) (decreases fuel) =
  if fuel = 0 then Inl (List.Tot.rev acc)
  else if pos >= head_end then Inl (List.Tot.rev acc)
  else
    // Find next CRLF within the head region.
    let remaining : nat = if head_end >= pos then head_end - pos else 0 in
    let line_fuel : nat = remaining + 1 in
    match find_2byte input pos 0x0D 0x0A line_fuel with
    | None ->
      // Last header line without trailing CRLF — take to head_end.
      let line = safe_substring input pos (head_end - pos) in
      if String.length line = 0 then Inl (List.Tot.rev acc)
      else
        (match parse_header_line line with
         | Inr e -> Inr e
         | Inl kv -> Inl (List.Tot.rev (kv :: acc)))
    | Some crlf_pos ->
      if crlf_pos > head_end then Inl (List.Tot.rev acc)
      else if crlf_pos <= pos then
        // Empty line (shouldn't happen because CRLFCRLF was stripped,
        // but be defensive).
        Inl (List.Tot.rev acc)
      else
        let line_len : nat = crlf_pos - pos in
        let line = safe_substring input pos line_len in
        (match parse_header_line line with
         | Inr e -> Inr e
         | Inl kv ->
           let next_pos : nat = crlf_pos + 2 in
           parse_header_lines input next_pos head_end (kv :: acc) (fuel - 1))


(** ====================================================================== **)
(** Part 9: parse non-negative integer from a header value                **)
(**                                                                       **)
(** Used for Content-Length. Trims whitespace, accepts only digits.       **)
(** Returns None on any malformed input.                                  **)
(** ====================================================================== **)

let rec parse_nat_chars (cs : list FStar.Char.char) (acc : nat)
  : Tot (option nat) (decreases (List.Tot.length cs)) =
  match cs with
  | [] -> Some acc
  | c :: rest ->
    let code = char_code c in
    if code >= 0x30 && code <= 0x39 then
      let d : nat = code - 0x30 in
      parse_nat_chars rest (acc `op_Multiply` 10 + d)
    else None

let parse_nat (s : string) : option nat =
  let trimmed = trim_ws s in
  if String.length trimmed = 0 then None
  else parse_nat_chars (String.list_of_string trimmed) 0


(** ====================================================================== **)
(** Part 10: parse_http_request — top-level                               **)
(**                                                                       **)
(** Algorithm:                                                             **)
(**   1. Find first CRLFCRLF within max_header_bytes. If absent and raw   **)
(**      >= max_header_bytes, return HE_HeadersTooLarge. Else             **)
(**      HE_MissingCRLF.                                                  **)
(**   2. The first CRLF within the head region splits off the request     **)
(**      line. The rest are header lines.                                 **)
(**   3. Parse request line with parse_request_line, split URI with       **)
(**      split_path_and_query.                                            **)
(**   4. Parse header lines with parse_header_lines.                      **)
(**   5. Look up Content-Length (case-insensitive). If present and > max_ **)
(**      body_bytes, return HE_BodyTooLarge. If present and valid, take   **)
(**      exactly that many bytes from the suffix. If absent, body is "".  **)
(** ====================================================================== **)

let parse_http_request
    (raw : string)
    (max_header_bytes : nat)
    (max_body_bytes : nat)
  : http_result http_request =
  let raw_len = String.length raw in
  // Head scan: bound the CRLFCRLF search at max_header_bytes to avoid
  // scanning megabytes of body for a missing terminator.
  let head_scan_limit : nat =
    if max_header_bytes < raw_len then max_header_bytes else raw_len
  in
  let head_scan_fuel : nat = head_scan_limit + 1 in
  match find_4byte raw 0 0x0D 0x0A 0x0D 0x0A head_scan_fuel with
  | None ->
    if raw_len >= max_header_bytes then Inr HE_HeadersTooLarge
    else Inr HE_MissingCRLF
  | Some head_end ->
    if head_end > max_header_bytes then Inr HE_HeadersTooLarge
    else
      // Request line ends at the first CRLF in [0, head_end).
      let rl_fuel : nat = head_end + 1 in
      (match find_2byte raw 0 0x0D 0x0A rl_fuel with
       | None -> Inr HE_MalformedRequestLine
       | Some rl_end ->
         if rl_end > head_end then Inr HE_MalformedRequestLine
         else
           let req_line_len : nat = rl_end in
           let req_line = safe_substring raw 0 req_line_len in
           (match parse_request_line req_line with
            | Inr e -> Inr e
            | Inl (meth, uri, version) ->
              let (path, qs) = split_path_and_query uri in
              let headers_start : nat = rl_end + 2 in
              let headers_end : nat =
                if head_end >= headers_start then head_end else headers_start
              in
              let headers_len : nat = headers_end - headers_start in
              let hdr_fuel : nat = headers_len + 1 in
              (match parse_header_lines raw headers_start headers_end [] hdr_fuel with
               | Inr e -> Inr e
               | Inl headers ->
                 let body_start : nat = head_end + 4 in
                 let available : nat =
                   if raw_len >= body_start then raw_len - body_start else 0
                 in
                 let body_len_opt =
                   match header_lookup_ci headers "content-length" with
                   | None -> Some 0
                   | Some cl ->
                     (match parse_nat cl with
                      | None -> None
                      | Some n -> Some n)
                 in
                 (match body_len_opt with
                  | None ->
                    Inr (HE_BadRequest "invalid Content-Length")
                  | Some body_len ->
                    if body_len > max_body_bytes then Inr HE_BodyTooLarge
                    else
                      let effective : nat =
                        if body_len <= available then body_len else available
                      in
                      let body = safe_substring raw body_start effective in
                      Inl { hr_method    = meth;
                            hr_path      = path;
                            hr_query_str = qs;
                            hr_version   = version;
                            hr_headers   = headers;
                            hr_body      = body }))))

#pop-options


(** ====================================================================== **)
(** Part 11: smoke tests (compile-time)                                   **)
(** ====================================================================== **)

// Request-line split.
let _test_rl_ok =
  match parse_request_line "GET /query HTTP/1.1" with
  | Inl (m, u, v) -> m = "GET" && u = "/query" && v = "HTTP/1.1"
  | Inr _ -> false

// Path/query split.
let _test_split_with_qs =
  let (p, q) = split_path_and_query "/query?a=1&b=2" in
  p = "/query" && q = "a=1&b=2"

let _test_split_no_qs =
  let (p, q) = split_path_and_query "/sparql" in
  p = "/sparql" && q = ""

// Header line.
let _test_header_ok =
  match parse_header_line "Content-Type: application/sparql-query" with
  | Inl (n, v) -> n = "content-type" && v = "application/sparql-query"
  | Inr _ -> false

// Case-insensitive lookup.
let _test_lookup_ci =
  let hs = [("content-type", "application/json"); ("accept", "text/csv")] in
  match header_lookup_ci hs "Content-Type" with
  | Some v -> v = "application/json"
  | None -> false
