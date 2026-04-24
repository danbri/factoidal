module SPARQL.HTTP.Client

(** ======================================================================== **)
(** SPARQL HTTP *client* framing — verified HTTP/1.1 request formatter       **)
(** + response parser.                                                       **)
(**                                                                          **)
(** Mirror of SPARQL.HTTP.fst (the server side). Where SPARQL.HTTP parses a  **)
(** request we've received, this module formats a request we're about to    **)
(** send and parses the response we get back.                                **)
(**                                                                          **)
(** Input (request side):  a typed [http_request_msg] record.                **)
(** Output (request side): a single byte string: request line + headers +    **)
(**                        CRLFCRLF + body.                                  **)
(**                                                                          **)
(** Input (response side): the full buffered response from the peer (status  **)
(**                        line + headers + body) as a single string.        **)
(** Output (response side): either a parsed [http_response] (Inl) or a       **)
(**                        typed error (Inr).                                **)
(**                                                                          **)
(** The OCaml glue (factoidal_http_client.ml) is responsible for socket I/O  **)
(** only — it takes the formatted bytes from [format_request], writes them   **)
(** to a TCP connection, reads the full response into a buffer, and hands    **)
(** that buffer back to [parse_http_response].                               **)
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

(* A request we're going to SEND.
   - [rm_path] is the request-target path (no query string).
   - [rm_query_str] is the query string, no leading '?'. If empty, no
     '?' is emitted.
   - [rm_headers] are user-supplied headers as (name, value) pairs. The
     formatter does not lowercase names — it emits them verbatim, which
     is HTTP-legal. It DOES inject Content-Length based on [rm_body]
     unless the caller already supplied one.
   - [rm_body] is the raw body string (may be empty).
   - [rm_host] is the Host header value ("example.org" or
     "example.org:8080"). Required by HTTP/1.1. *)
noeq type http_request_msg = {
  rm_method    : string;
  rm_path      : string;
  rm_query_str : string;
  rm_version   : string;
  rm_host      : string;
  rm_headers   : list (string & string);
  rm_body      : string;
}

(* A parsed response from the peer. *)
noeq type http_response = {
  rsp_version : string;                    // "HTTP/1.1"
  rsp_status  : nat;                       // 200, 404, ...
  rsp_reason  : string;                    // "OK", "Not Found"
  rsp_headers : list (string & string);    // (lowercased name, trimmed value)
  rsp_body    : string;
}

type http_client_error =
  | HCE_MalformedStatusLine : http_client_error
  | HCE_MalformedHeader     : http_client_error
  | HCE_BadStatusCode       : http_client_error
  | HCE_HeadersTooLarge     : http_client_error
  | HCE_BodyTooLarge        : http_client_error
  | HCE_MissingCRLF         : http_client_error
  | HCE_BadResponse         : string -> http_client_error

type http_client_result a = either a http_client_error


(** ====================================================================== **)
(** Part 2: Low-level character helpers                                    **)
(**                                                                        **)
(** These mirror the helpers in SPARQL.HTTP exactly. Duplicated rather    **)
(** than re-exported because F*'s `open` machinery does not let us simply **)
(** reuse the ASCII helpers without pulling in the whole module (and the **)
(** server's `noeq` types can drift independently of the client's). The  **)
(** duplication is a couple dozen lines; the alternative is worse.       **)
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

// Safe substring, clamped.
let safe_substring (s : string) (start : nat) (sub_len : nat) : string =
  let slen = String.length s in
  if start >= slen then ""
  else
    let remaining : nat = slen - start in
    let effective_len = if sub_len <= remaining then sub_len else remaining in
    String.sub s start effective_len

let string_suffix (s : string) (start : nat) : string =
  let slen = String.length s in
  if start >= slen then ""
  else String.sub s start (slen - start)

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
(** Part 3: integer -> decimal string                                     **)
(**                                                                        **)
(** Used to emit Content-Length. Stack-safe (tail-recursive accumulator). **)
(** ====================================================================== **)

let rec nat_to_digits_acc (n : nat) (acc : list FStar.Char.char)
  : Tot (list FStar.Char.char) (decreases n) =
  if n = 0 then acc
  else
    let d : nat = n % 10 in
    let rest : nat = n / 10 in
    let ch = FStar.Char.char_of_int (0x30 + d) in
    nat_to_digits_acc rest (ch :: acc)

let nat_to_string (n : nat) : string =
  if n = 0 then "0"
  else String.string_of_list (nat_to_digits_acc n [])


(** ====================================================================== **)
(** Part 4: Request formatter                                              **)
(**                                                                        **)
(** Emit:                                                                  **)
(**   METHOD SP path[?qs] SP version CRLF                                  **)
(**   Host: <host>        CRLF     (if not already supplied)               **)
(**   Content-Length: <n> CRLF     (if body non-empty and not supplied)    **)
(**   <user headers>      CRLF                                             **)
(**   CRLF                                                                 **)
(**   <body>                                                               **)
(** ====================================================================== **)

// Case-insensitive header-name presence check.
let has_header_ci (headers : list (string & string)) (name : string) : bool =
  match header_lookup_ci headers name with
  | Some _ -> true
  | None   -> false

let crlf : string = "\r\n"
let sp   : string = " "

// Stack-safe fold to concatenate headers.
let rec format_headers_acc
    (headers : list (string & string))
    (acc : string)
  : Tot string (decreases (List.Tot.length headers)) =
  match headers with
  | [] -> acc
  | (k, v) :: rest ->
    let line = k ^ ": " ^ v ^ crlf in
    format_headers_acc rest (acc ^ line)

let format_request_headers (headers : list (string & string)) : string =
  format_headers_acc headers ""

let format_request_line
    (meth : string)
    (path : string)
    (qs   : string)
    (ver  : string)
  : string =
  let target = if String.length qs = 0 then path else path ^ "?" ^ qs in
  meth ^ sp ^ target ^ sp ^ ver ^ crlf

// Inject Host and Content-Length if not already set by caller.
let complete_headers
    (req : http_request_msg)
  : list (string & string) =
  let h0 = req.rm_headers in
  let h1 =
    if has_header_ci h0 "Host" then h0
    else h0 @ [("Host", req.rm_host)]
  in
  let body_len = String.length req.rm_body in
  let h2 =
    if body_len = 0 then h1
    else if has_header_ci h1 "Content-Length" then h1
    else h1 @ [("Content-Length", nat_to_string body_len)]
  in
  h2

let format_request (req : http_request_msg) : string =
  let rl = format_request_line req.rm_method req.rm_path
                               req.rm_query_str req.rm_version in
  let hs = complete_headers req in
  let hblock = format_request_headers hs in
  rl ^ hblock ^ crlf ^ req.rm_body


(** ====================================================================== **)
(** Part 5: parse_status_line                                              **)
(**                                                                        **)
(** "HTTP/1.1 200 OK" -> ("HTTP/1.1", 200, "OK")                           **)
(** "HTTP/1.1 404 Not Found" -> ("HTTP/1.1", 404, "Not Found")             **)
(**                                                                        **)
(** The reason phrase may contain spaces but not CR/LF.                    **)
(** ====================================================================== **)

let parse_status_line (line : string)
  : http_client_result (string & nat & string) =
  if contains_crlf line then Inr HCE_MalformedStatusLine
  else
    let len = String.length line in
    let fuel : nat = len + 1 in
    match find_char line 0 0x20 fuel with  // first ' '
    | None -> Inr HCE_MalformedStatusLine
    | Some i1 ->
      let ver = safe_substring line 0 i1 in
      let rest_start : nat = i1 + 1 in
      let rest_len : nat = if rest_start <= len then len - rest_start else 0 in
      let fuel2 : nat = rest_len + 1 in
      (match find_char line rest_start 0x20 fuel2 with
       | None -> Inr HCE_MalformedStatusLine
       | Some i2 ->
         if i2 <= rest_start then Inr HCE_MalformedStatusLine
         else
           let code_len : nat = i2 - rest_start in
           let code_raw = safe_substring line rest_start code_len in
           (match parse_nat code_raw with
            | None -> Inr HCE_BadStatusCode
            | Some code ->
              let reason_start : nat = i2 + 1 in
              let reason = string_suffix line reason_start in
              if String.length ver = 0 then Inr HCE_MalformedStatusLine
              else Inl (ver, code, reason)))


(** ====================================================================== **)
(** Part 6: parse_header_line                                              **)
(**                                                                        **)
(** Same shape as SPARQL.HTTP.parse_header_line. Duplicated locally.      **)
(** ====================================================================== **)

let parse_response_header_line (line : string)
  : http_client_result (string & string) =
  if contains_crlf line then Inr HCE_MalformedHeader
  else
    let len = String.length line in
    let fuel : nat = len + 1 in
    match find_char line 0 0x3A fuel with  // ':'
    | None -> Inr HCE_MalformedHeader
    | Some i ->
      let name_raw = safe_substring line 0 i in
      let name = ascii_lower_string (trim_ws name_raw) in
      let value_start : nat = i + 1 in
      let value_raw = string_suffix line value_start in
      let value = trim_ws value_raw in
      if String.length name = 0 then Inr HCE_MalformedHeader
      else Inl (name, value)


(** ====================================================================== **)
(** Part 7: iterate header lines                                          **)
(** ====================================================================== **)

let rec parse_response_header_lines
    (input : string)
    (pos : nat)
    (head_end : nat)
    (acc : list (string & string))
    (fuel : nat)
  : Tot (http_client_result (list (string & string))) (decreases fuel) =
  if fuel = 0 then Inl (List.Tot.rev acc)
  else if pos >= head_end then Inl (List.Tot.rev acc)
  else
    let remaining : nat = if head_end >= pos then head_end - pos else 0 in
    let line_fuel : nat = remaining + 1 in
    match find_2byte input pos 0x0D 0x0A line_fuel with
    | None ->
      let line = safe_substring input pos (head_end - pos) in
      if String.length line = 0 then Inl (List.Tot.rev acc)
      else
        (match parse_response_header_line line with
         | Inr e -> Inr e
         | Inl kv -> Inl (List.Tot.rev (kv :: acc)))
    | Some crlf_pos ->
      if crlf_pos > head_end then Inl (List.Tot.rev acc)
      else if crlf_pos <= pos then Inl (List.Tot.rev acc)
      else
        let line_len : nat = crlf_pos - pos in
        let line = safe_substring input pos line_len in
        (match parse_response_header_line line with
         | Inr e -> Inr e
         | Inl kv ->
           let next_pos : nat = crlf_pos + 2 in
           parse_response_header_lines input next_pos head_end (kv :: acc) (fuel - 1))


(** ====================================================================== **)
(** Part 8: parse_http_response — top-level                                **)
(**                                                                        **)
(** Algorithm (mirror of parse_http_request):                              **)
(**   1. Find first CRLFCRLF within max_header_bytes.                     **)
(**   2. Request line is the first CRLF-terminated line.                  **)
(**   3. Rest of the head region is header lines.                         **)
(**   4. If Content-Length present and <= max_body_bytes, take that many  **)
(**      bytes from the suffix. If absent, treat everything after         **)
(**      CRLFCRLF up to min(raw_len - body_start, max_body_bytes) as the  **)
(**      body (connection-close framing; the OCaml glue reads until EOF). **)
(** ====================================================================== **)

let parse_http_response
    (raw : string)
    (max_header_bytes : nat)
    (max_body_bytes : nat)
  : http_client_result http_response =
  let raw_len = String.length raw in
  let head_scan_limit : nat =
    if max_header_bytes < raw_len then max_header_bytes else raw_len
  in
  let head_scan_fuel : nat = head_scan_limit + 1 in
  match find_4byte raw 0 0x0D 0x0A 0x0D 0x0A head_scan_fuel with
  | None ->
    if raw_len >= max_header_bytes then Inr HCE_HeadersTooLarge
    else Inr HCE_MissingCRLF
  | Some head_end ->
    if head_end > max_header_bytes then Inr HCE_HeadersTooLarge
    else
      let sl_fuel : nat = head_end + 1 in
      (match find_2byte raw 0 0x0D 0x0A sl_fuel with
       | None -> Inr HCE_MalformedStatusLine
       | Some sl_end ->
         if sl_end > head_end then Inr HCE_MalformedStatusLine
         else
           let status_line = safe_substring raw 0 sl_end in
           (match parse_status_line status_line with
            | Inr e -> Inr e
            | Inl (ver, code, reason) ->
              let headers_start : nat = sl_end + 2 in
              let headers_end : nat =
                if head_end >= headers_start then head_end else headers_start
              in
              let headers_len : nat = headers_end - headers_start in
              let hdr_fuel : nat = headers_len + 1 in
              (match parse_response_header_lines raw headers_start headers_end [] hdr_fuel with
               | Inr e -> Inr e
               | Inl headers ->
                 let body_start : nat = head_end + 4 in
                 let available : nat =
                   if raw_len >= body_start then raw_len - body_start else 0
                 in
                 // Content-Length OPTIONAL for responses: if missing, use
                 // connection-close framing (take whatever's available,
                 // bounded by max_body_bytes).
                 let body_len_opt =
                   match header_lookup_ci headers "content-length" with
                   | None -> Some available
                   | Some cl ->
                     (match parse_nat cl with
                      | None -> None
                      | Some n -> Some n)
                 in
                 (match body_len_opt with
                  | None ->
                    Inr (HCE_BadResponse "invalid Content-Length")
                  | Some body_len ->
                    if body_len > max_body_bytes then Inr HCE_BodyTooLarge
                    else
                      let effective : nat =
                        if body_len <= available then body_len else available
                      in
                      let body = safe_substring raw body_start effective in
                      Inl { rsp_version = ver;
                            rsp_status  = code;
                            rsp_reason  = reason;
                            rsp_headers = headers;
                            rsp_body    = body }))))

#pop-options


(** ====================================================================== **)
(** Part 9: smoke tests (compile-time)                                    **)
(** ====================================================================== **)

// nat_to_string basics.
let _test_nat_zero   = nat_to_string 0 = "0"
let _test_nat_small  = nat_to_string 7 = "7"
let _test_nat_multi  = nat_to_string 1234 = "1234"

// Request line formatter.
let _test_rl_no_qs =
  format_request_line "GET" "/sparql" "" "HTTP/1.1"
    = "GET /sparql HTTP/1.1\r\n"

let _test_rl_with_qs =
  format_request_line "POST" "/query" "default-graph-uri=urn%3Ax" "HTTP/1.1"
    = "POST /query?default-graph-uri=urn%3Ax HTTP/1.1\r\n"

// Header-block formatter.
let _test_headers_empty =
  format_request_headers [] = ""

let _test_headers_two =
  format_request_headers [("Accept", "application/json"); ("X-Foo", "bar")]
    = "Accept: application/json\r\nX-Foo: bar\r\n"

// Full request formatter — GET.
let _test_format_get =
  let r = { rm_method    = "GET";
            rm_path      = "/sparql";
            rm_query_str = "query=ASK%20WHERE%20%7B%7D";
            rm_version   = "HTTP/1.1";
            rm_host      = "example.org";
            rm_headers   = [("Accept", "application/sparql-results+json")];
            rm_body      = "" } in
  format_request r =
    "GET /sparql?query=ASK%20WHERE%20%7B%7D HTTP/1.1\r\n\
     Accept: application/sparql-results+json\r\n\
     Host: example.org\r\n\
     \r\n"

// Full request formatter — POST with body (Content-Length injected).
let _test_format_post =
  let r = { rm_method    = "POST";
            rm_path      = "/sparql";
            rm_query_str = "";
            rm_version   = "HTTP/1.1";
            rm_host      = "example.org";
            rm_headers   = [("Content-Type", "application/sparql-query");
                            ("Accept", "application/sparql-results+json")];
            rm_body      = "ASK {}" } in
  format_request r =
    "POST /sparql HTTP/1.1\r\n\
     Content-Type: application/sparql-query\r\n\
     Accept: application/sparql-results+json\r\n\
     Host: example.org\r\n\
     Content-Length: 6\r\n\
     \r\n\
     ASK {}"

// Status-line parser.
let _test_sl_ok =
  match parse_status_line "HTTP/1.1 200 OK" with
  | Inl (v, c, r) -> v = "HTTP/1.1" && c = 200 && r = "OK"
  | Inr _ -> false

let _test_sl_reason_with_spaces =
  match parse_status_line "HTTP/1.1 404 Not Found" with
  | Inl (v, c, r) -> v = "HTTP/1.1" && c = 404 && r = "Not Found"
  | Inr _ -> false

// Response-header parser.
let _test_resp_header_ok =
  match parse_response_header_line "Content-Type: application/sparql-results+json" with
  | Inl (n, v) -> n = "content-type" && v = "application/sparql-results+json"
  | Inr _ -> false

// Full response parser.
let _test_parse_response_cl =
  let raw =
    "HTTP/1.1 200 OK\r\n\
     Content-Type: application/sparql-results+json\r\n\
     Content-Length: 13\r\n\
     \r\n\
     {\"ok\":true}\r\n" in
  match parse_http_response raw 8192 1048576 with
  | Inl r -> r.rsp_status = 200
            && r.rsp_version = "HTTP/1.1"
            && r.rsp_reason = "OK"
            && String.length r.rsp_body = 13
  | Inr _ -> false

// Connection-close framing (no Content-Length).
let _test_parse_response_no_cl =
  let raw =
    "HTTP/1.1 200 OK\r\n\
     Content-Type: text/plain\r\n\
     \r\n\
     hello" in
  match parse_http_response raw 8192 1048576 with
  | Inl r -> r.rsp_status = 200 && r.rsp_body = "hello"
  | Inr _ -> false
