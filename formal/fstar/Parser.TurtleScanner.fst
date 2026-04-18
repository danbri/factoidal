module Parser.TurtleScanner

open FStar.String
open FStar.Char
open Parser.Combinators

(* Scanner-first foundation for a future Turtle parser refactor.
   This module keeps the API offset-oriented and streaming-friendly. *)

noeq type scan_mode =
  | SM_Normal
  | SM_Comment
  | SM_IriRef
  | SM_String : char -> bool -> bool -> nat -> scan_mode

noeq type scanner_state = {
  ss_mode: scan_mode;
  ss_carry: string;
}

let empty_scanner_state : scanner_state = {
  ss_mode = SM_Normal;
  ss_carry = "";
}

noeq type span = {
  sp_start: nat;
  sp_end: nat;
}

noeq type prefixed_name_span = {
  pns_prefix: span;
  pns_local: span;
}

noeq type iri_ref_span = {
  irs_span: span;
  irs_has_colon: bool;
}

noeq type short_string_span = {
  sss_quote: char;
  sss_content: span;
}

noeq type token_kind =
  | TK_Dot
  | TK_Semicolon
  | TK_Comma
  | TK_LBracket
  | TK_RBracket
  | TK_LParen
  | TK_RParen
  | TK_IriRef
  | TK_PrefixedName

noeq type scanned_token = {
  st_kind: token_kind;
  st_span: span;
}

let append_carry (st: scanner_state) (chunk: string) : string =
  if String.length st.ss_carry = 0 then chunk
  else String.concat "" [st.ss_carry; chunk]

let clear_carry (st: scanner_state) : scanner_state =
  { st with ss_carry = "" }

let is_ascii_ws (c: char) : bool =
  let code = int_of_char c in
  code = 0x20 || code = 0x09 || code = 0x0A || code = 0x0D

let is_ascii_name_start (c: char) : bool =
  let code = int_of_char c in
  (code >= 0x41 && code <= 0x5A) ||
  (code >= 0x61 && code <= 0x7A) ||
  (code >= 0x30 && code <= 0x39) ||
  code = 0x5F

let is_ascii_name_body (c: char) : bool =
  let code = int_of_char c in
  (code >= 0x41 && code <= 0x5A) ||
  (code >= 0x61 && code <= 0x7A) ||
  (code >= 0x30 && code <= 0x39) ||
  code = 0x5F || code = 0x2D || code = 0x2E || code = 0x3A ||
  code = 0x25 || code = 0x5C

let is_hex_digit (c: char) : bool =
  let code = int_of_char c in
  (code >= 0x30 && code <= 0x39) ||
  (code >= 0x41 && code <= 0x46) ||
  (code >= 0x61 && code <= 0x66)

let hex_digit_value (c: char) : nat =
  let code = int_of_char c in
  if code >= 0x30 && code <= 0x39 then code - 0x30
  else if code >= 0x41 && code <= 0x46 then code - 0x41 + 10
  else if code >= 0x61 && code <= 0x66 then code - 0x61 + 10
  else 0

// F* 2026.03.24 requires bounds preconditions and explicit op_Multiply for nat
let decode_hex4 (input: string) (pos: nat{pos + 4 <= String.length input}) : nat =
  let d0 = hex_digit_value (String.index input pos) in
  let d1 = hex_digit_value (String.index input (pos + 1)) in
  let d2 = hex_digit_value (String.index input (pos + 2)) in
  let d3 = hex_digit_value (String.index input (pos + 3)) in
  op_Multiply d0 4096 + op_Multiply d1 256 + op_Multiply d2 16 + d3

let decode_hex8 (input: string) (pos: nat{pos + 8 <= String.length input}) : nat =
  let d0 = hex_digit_value (String.index input pos) in
  let d1 = hex_digit_value (String.index input (pos + 1)) in
  let d2 = hex_digit_value (String.index input (pos + 2)) in
  let d3 = hex_digit_value (String.index input (pos + 3)) in
  let d4 = hex_digit_value (String.index input (pos + 4)) in
  let d5 = hex_digit_value (String.index input (pos + 5)) in
  let d6 = hex_digit_value (String.index input (pos + 6)) in
  let d7 = hex_digit_value (String.index input (pos + 7)) in
  op_Multiply d0 268435456 + op_Multiply d1 16777216 + op_Multiply d2 1048576 + op_Multiply d3 65536 +
  op_Multiply d4 4096 + op_Multiply d5 256 + op_Multiply d6 16 + d7

let is_iri_forbidden_codepoint (code: nat) : bool =
  code = 0x20 || code = 0x3C || code = 0x3E || code = 0x22 ||
  code = 0x7B || code = 0x7D || code = 0x7C || code = 0x5C ||
  code = 0x5E || code = 0x60

let is_turtle_token_delim (c: char) : bool =
  let code = int_of_char c in
  is_ascii_ws c ||
  code = 0x23 ||  // #
  code = 0x2E ||  // .
  code = 0x3B ||  // ;
  code = 0x2C ||  // ,
  code = 0x5B ||  // [
  code = 0x5D ||  // ]
  code = 0x28 ||  // (
  code = 0x29 ||  // )
  code = 0x3C ||  // <
  code = 0x3E ||  // >
  code = 0x22 ||  // "
  code = 0x27    // '

let rec skip_comment_to_eol (input: string) (pos: nat) (fuel: nat)
  : Tot nat (decreases fuel) =
  if fuel = 0 then pos
  else
    let len = String.length input in
    if pos >= len then pos
    else
      let c = String.index input pos in
      let code = int_of_char c in
      if code = 0x0A || code = 0x0D then pos
      else skip_comment_to_eol input (pos + 1) (fuel - 1)

let rec scan_ws_comments (input: string) (pos: nat) (fuel: nat)
  : Tot nat (decreases fuel) =
  if fuel = 0 then pos
  else
    let len = String.length input in
    if pos >= len then pos
    else
      let c = String.index input pos in
      let code = int_of_char c in
      if is_ascii_ws c then
        scan_ws_comments input (pos + 1) (fuel - 1)
      else if code = 0x23 then
        let pos' = skip_comment_to_eol input (pos + 1) (len - pos) in
        scan_ws_comments input pos' (fuel - 1)
      else
        pos

let skip_ws_comments (input: string) (pos: nat) : nat =
  let len = String.length input in
  let fuel = len - pos + 1 in
  if fuel >= 0 then scan_ws_comments input pos fuel else pos

let rec scan_name_body_end (input: string) (pos: nat) (fuel: nat)
  : Tot nat (decreases fuel) =
  if fuel = 0 then pos
  else
    let len = String.length input in
    if pos >= len then pos
    else
      let c = String.index input pos in
      let code = int_of_char c in
      // PN_LOCAL_ESC: a backslash starts a two-char escape where the
      // second char may be a reserved char (#, !, ~, ., ...) that's not
      // normally in the name body. Consume both so e.g. "foo\#bar" scans
      // as one name token.
      if code = 0x5C && pos + 1 < len then
        scan_name_body_end input (pos + 2) (fuel - 1)
      else if code < 0x80 then
        if is_ascii_name_body c then
          scan_name_body_end input (pos + 1) (fuel - 1)
        else
          pos
      else if is_turtle_token_delim c then
        pos
      else
        scan_name_body_end input (pos + 1) (fuel - 1)

let scan_prefixed_name_span (input: string) (pos: nat)
  : parse_result prefixed_name_span =
  let len = String.length input in
  if pos >= len then ParseFail "expected prefixed name" pos
  else
    let c0 = String.index input pos in
    if int_of_char c0 = 0x3A then
      let body_end = scan_name_body_end input (pos + 1) (len - pos + 1) in
      let prefix = { sp_start = pos; sp_end = pos } in
      let local = { sp_start = pos + 1; sp_end = body_end } in
      ParseOk ({ pns_prefix = prefix; pns_local = local }) body_end
    else if not (is_ascii_name_start c0) then ParseFail "expected prefixed name" pos
    else
      let body_end = scan_name_body_end input pos (len - pos + 1) in
      let rec find_colon (p: nat) (fuel: nat)
        : Tot (option nat) (decreases fuel) =
        if fuel = 0 then None
        else if p >= body_end then None
        else if p >= len then None
        else if int_of_char (String.index input p) = 0x3A then Some p
        else find_colon (p + 1) (fuel - 1)
      in
      let fuel : nat =
        if body_end >= pos then body_end - pos + 1 else 0
      in
      match find_colon pos fuel with
      | None -> ParseFail "expected ':' in prefixed name" body_end
      | Some colon_pos ->
        let prefix = { sp_start = pos; sp_end = colon_pos } in
        let local = { sp_start = colon_pos + 1; sp_end = body_end } in
        ParseOk ({ pns_prefix = prefix; pns_local = local }) body_end

let rec scan_iri_ref_end (input: string) (pos: nat) (has_colon: bool) (fuel: nat)
  : Tot (parse_result (nat & bool)) (decreases fuel) =
  if fuel = 0 then ParseFail "unterminated IRI reference" pos
  else
    let len = String.length input in
    if pos >= len then ParseFail "unterminated IRI reference" pos
    else
      let c = String.index input pos in
      let code = int_of_char c in
      if code = 0x3E then ParseOk (pos, has_colon) (pos + 1)
      else if code = 0x5C then
        if pos + 1 >= len then ParseFail "backslash at end of IRI reference" pos
        else
          let next = String.index input (pos + 1) in
          let ncode = int_of_char next in
          if ncode = 0x75 then
            if pos + 6 > len then ParseFail "incomplete \\u escape in IRI reference" pos
            else if is_hex_digit (String.index input (pos + 2)) &&
                    is_hex_digit (String.index input (pos + 3)) &&
                    is_hex_digit (String.index input (pos + 4)) &&
                    is_hex_digit (String.index input (pos + 5))
            then
              let cp = decode_hex4 input (pos + 2) in
              if cp >= 0xD800 && cp <= 0xDFFF then
                ParseFail "surrogate codepoint in \\u escape" pos
              else
                scan_iri_ref_end input (pos + 6) has_colon (fuel - 1)
            else ParseFail "invalid hex digit in \\u escape" pos
          else if ncode = 0x55 then
            if pos + 10 > len then ParseFail "incomplete \\U escape in IRI reference" pos
            else if is_hex_digit (String.index input (pos + 2)) &&
                    is_hex_digit (String.index input (pos + 3)) &&
                    is_hex_digit (String.index input (pos + 4)) &&
                    is_hex_digit (String.index input (pos + 5)) &&
                    is_hex_digit (String.index input (pos + 6)) &&
                    is_hex_digit (String.index input (pos + 7)) &&
                    is_hex_digit (String.index input (pos + 8)) &&
                    is_hex_digit (String.index input (pos + 9))
            then
              let cp = decode_hex8 input (pos + 2) in
              if (cp >= 0xD800 && cp <= 0xDFFF) || cp > 0x10FFFF then
                ParseFail "invalid codepoint in \\U escape" pos
              else
                scan_iri_ref_end input (pos + 10) has_colon (fuel - 1)
            else ParseFail "invalid hex digit in \\U escape" pos
          else ParseFail "invalid escape in IRI reference" pos
      else if code = 0x0A || code = 0x0D then ParseFail "newline in IRI reference" pos
      else if code <= 0x20 || is_iri_forbidden_codepoint code then
        ParseFail "invalid character in IRI reference" pos
      else scan_iri_ref_end input (pos + 1) (has_colon || code = 0x3A) (fuel - 1)

let scan_iri_ref_span (input: string) (pos: nat) : parse_result iri_ref_span =
  let len = String.length input in
  if pos >= len then ParseFail "expected IRI reference" pos
  else if int_of_char (String.index input pos) <> 0x3C then
    ParseFail "expected '<'" pos
  else
    match scan_iri_ref_end input (pos + 1) false (len - pos + 1) with
    | ParseOk (gt_pos, has_colon) next ->
      ParseOk ({
        irs_span = { sp_start = pos; sp_end = next };
        irs_has_colon = has_colon;
      }) next
    | ParseFail msg fpos -> ParseFail msg fpos

let rec scan_short_string_end (input: string) (pos: nat) (quote_code: nat) (fuel: nat)
  : Tot nat (decreases fuel) =
  if fuel = 0 then pos
  else
    let len = String.length input in
    if pos >= len then pos
    else
      let ch = String.index input pos in
      let code = int_of_char ch in
      if code = quote_code || code = 0x5C || code = 0x0A || code = 0x0D
      then pos
      else scan_short_string_end input (pos + 1) quote_code (fuel - 1)

let scan_short_string_span (input: string) (pos: nat) : parse_result short_string_span =
  let len = String.length input in
  if pos >= len then ParseFail "expected short string literal" pos
  else
    let q = String.index input pos in
    let qcode = int_of_char q in
    if qcode <> 0x22 && qcode <> 0x27 then
      ParseFail "expected short string literal" pos
    else
      let end_pos = scan_short_string_end input (pos + 1) qcode (len - pos + 1) in
      if end_pos < len && int_of_char (String.index input end_pos) = qcode then
        ParseOk ({
          sss_quote = q;
          sss_content = { sp_start = pos + 1; sp_end = end_pos };
        }) (end_pos + 1)
      else
        ParseFail "short string needs slow path" end_pos

let scan_punct (input: string) (pos: nat) : parse_result scanned_token =
  let len = String.length input in
  if pos >= len then ParseFail "expected punctuation" pos
  else
    let code = int_of_char (String.index input pos) in
    let sp = { sp_start = pos; sp_end = pos + 1 } in
    if code = 0x2E then ParseOk ({ st_kind = TK_Dot; st_span = sp }) (pos + 1)
    else if code = 0x3B then ParseOk ({ st_kind = TK_Semicolon; st_span = sp }) (pos + 1)
    else if code = 0x2C then ParseOk ({ st_kind = TK_Comma; st_span = sp }) (pos + 1)
    else if code = 0x5B then ParseOk ({ st_kind = TK_LBracket; st_span = sp }) (pos + 1)
    else if code = 0x5D then ParseOk ({ st_kind = TK_RBracket; st_span = sp }) (pos + 1)
    else if code = 0x28 then ParseOk ({ st_kind = TK_LParen; st_span = sp }) (pos + 1)
    else if code = 0x29 then ParseOk ({ st_kind = TK_RParen; st_span = sp }) (pos + 1)
    else ParseFail "expected Turtle punctuation" pos
