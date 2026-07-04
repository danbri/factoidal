module Parser.JSON

// ============================================================================
// Full RFC 8259 JSON parser — general-purpose JSON value tree.
//
// This module is the JSON foundation for Parser.JSONLD (all phases) and,
// eventually, Parser.JSONResults (SPARQL results JSON). It exists because
// the minimal JSON tokenizer embedded in Parser.JSONResults is NOT a full
// RFC 8259 parser:
//   - unknown escape sequences are accepted leniently (RFC requires reject);
//   - backslash-u escapes do not combine UTF-16 surrogate pairs, and encode
//     non-ASCII codepoints by pushing individual UTF-8 bytes through the
//     codepoint-oriented FStar.String API (double encoding);
//   - numbers are lexed with a take-while over [0-9+-.eE] instead of the
//     RFC grammar, so "1..2", "--3", "1e+" are accepted;
//   - raw control characters inside strings are accepted;
//   - trailing content after the top-level value is ignored.
//
// STRICTNESS CONTRACT of this module:
//   - exactly one top-level value; only JSON whitespace may follow;
//   - strings: the full escape set (quote, backslash, slash, b, f, n, r, t,
//     u followed by four hex digits) and nothing else; backslash-u escapes
//     combine UTF-16 surrogate pairs into supplementary-plane codepoints;
//     lone surrogates are rejected; invalid hex digits are rejected; raw
//     control characters below U+0020 are rejected;
//   - numbers: the exact RFC 8259 grammar
//       minus? ( zero | digit1-9 digit* ) frac? exp?
//     with frac = dot digit+ and exp = (e|E) sign? digit+ ;
//   - whitespace: space, tab, LF, CR only.
//
// INDEXING: byte-indexed via Parser.FastString (see that module's safety
// argument). JSON structural characters and escape introducers are all
// ASCII; multi-byte UTF-8 appears only inside string bodies, where raw
// spans are sliced byte-true with fs_byte_sub. Decoded escapes are emitted
// as byte-transparent strings via json_utf8_of_codepoint (the
// RDF.Bytes.byte_of_int + string_of_list construction from
// SPARQL11.Parser.utf8_of_codepoint, issue #64).
//
// NOT COVERED (follow-on items):
//   - UTF-8 well-formedness validation of raw string content (bytes are
//     passed through as-is);
//   - migrating Parser.JSONResults onto this module.
// ============================================================================

open FStar.String
open FStar.List.Tot
open Parser.FastString
open Parser.Combinators

// ================================================================
// JSON value tree
// ================================================================

type json_val =
  | JNull   : json_val
  | JBool   : bool -> json_val
  | JString : string -> json_val
  | JNumber : string -> json_val   // validated RFC 8259 lexeme, verbatim
  | JArray  : list json_val -> json_val
  | JObject : list (string & json_val) -> json_val

// Size of a JSON value tree: one unit per value, plus one unit per array
// element and object member visited. Used by consumers (e.g. Parser.JSONLD)
// to derive a sufficient fuel bound for fuel-threaded recursion over the
// tree.
let rec json_size (v:json_val) : Tot pos (decreases v) =
  match v with
  | JArray items -> 1 + json_size_items items
  | JObject fields -> 1 + json_size_fields fields
  | _ -> 1

and json_size_items (items:list json_val) : Tot nat (decreases items) =
  match items with
  | [] -> 0
  | hd :: tl -> 1 + json_size hd + json_size_items tl

and json_size_fields (fields:list (string & json_val)) : Tot nat (decreases fields) =
  match fields with
  | [] -> 0
  | (_, v) :: tl -> 1 + json_size v + json_size_fields tl

// ================================================================
// Byte-level helpers
// ================================================================

// Total byte peek: the byte at pos as an int in [0, 255], or -1 when pos
// is out of range. Lets callers scan with plain boolean conjunctions and
// no bounds preconditions.
let jbyte_at (input:string) (pos:nat) : int =
  if pos < fs_byte_length input then fs_byte_at input pos else (-1)

// Skip JSON whitespace: space, tab, LF, CR.
let rec json_skip_ws (input:string) (pos:nat) (fuel:nat) : Tot nat (decreases fuel) =
  if fuel = 0 then pos
  else
    let b = jbyte_at input pos in
    if b = 0x20 || b = 0x09 || b = 0x0A || b = 0x0D
    then json_skip_ws input (pos + 1) (fuel - 1)
    else pos

// Hex digit value, or None for a non-hex-digit byte.
let json_hex_val (b:int) : option (v:nat{v < 16}) =
  if b >= 0x30 && b <= 0x39 then Some (b - 0x30)
  else if b >= 0x41 && b <= 0x46 then Some (b - 0x41 + 10)
  else if b >= 0x61 && b <= 0x66 then Some (b - 0x61 + 10)
  else None

// Read exactly four hex digits starting at pos. None if any is not a hex
// digit (including running off the end of the input).
let json_read_hex4 (input:string) (pos:nat) : option (n:nat{n <= 0xFFFF}) =
  match json_hex_val (jbyte_at input pos),
        json_hex_val (jbyte_at input (pos + 1)),
        json_hex_val (jbyte_at input (pos + 2)),
        json_hex_val (jbyte_at input (pos + 3)) with
  | Some h0, Some h1, Some h2, Some h3 ->
    Some (op_Multiply h0 4096 + op_Multiply h1 256 + op_Multiply h2 16 + h3)
  | _, _, _, _ -> None

// Encode a decoded Unicode codepoint as a one-character string. Do NOT
// assemble UTF-8 bytes by hand here: the extracted string_of_list
// realisation is codepoint-oriented (each list element is re-encoded
// as UTF-8), so a hand-built byte list gets DOUBLE-encoded — "é" from
// a backslash-u escape came out as "Ã©" (issue #271 family, found
// 2026-07-04 via the local_scalars_escapes fixture). Handing the
// codepoint straight to string_of_list yields exactly one encoding,
// matching how the unescaped path preserves raw input bytes. Guard
// mirrors Parser.NTriples.safe_char_of_int: surrogates were already
// rejected by the caller, but keep char_of_int's precondition provable.
let json_utf8_of_codepoint (cp:nat) : Tot string =
  if cp < 0xD7FF || (cp >= 0xE000 && cp <= 0x10FFFF) then
    String.string_of_list [FStar.Char.char_of_int cp]
  else
    // Surrogate-range / out-of-range / the one codepoint (U+D7FF) the
    // char refinement excludes: substitute U+FFFD like
    // Parser.NTriples.safe_char_of_int rather than dropping the char.
    String.string_of_list [FStar.Char.char_of_int 0xFFFD]

// ================================================================
// Strings
// ================================================================

// Decode one escape sequence. pos points AT the backslash. On success the
// ParseOk value is the decoded piece (as a UTF-8 string) and the ParseOk
// position is the first byte after the escape.
let json_escape_piece (input:string) (pos:nat) : parse_result string =
  let esc = jbyte_at input (pos + 1) in
  if esc = 0x22 then ParseOk (json_utf8_of_codepoint 0x22) (pos + 2)
  else if esc = 0x5C then ParseOk (json_utf8_of_codepoint 0x5C) (pos + 2)
  else if esc = 0x2F then ParseOk (json_utf8_of_codepoint 0x2F) (pos + 2)
  else if esc = 0x62 then ParseOk (json_utf8_of_codepoint 0x08) (pos + 2)
  else if esc = 0x66 then ParseOk (json_utf8_of_codepoint 0x0C) (pos + 2)
  else if esc = 0x6E then ParseOk (json_utf8_of_codepoint 0x0A) (pos + 2)
  else if esc = 0x72 then ParseOk (json_utf8_of_codepoint 0x0D) (pos + 2)
  else if esc = 0x74 then ParseOk (json_utf8_of_codepoint 0x09) (pos + 2)
  else if esc = 0x75 then
    match json_read_hex4 input (pos + 2) with
    | None -> ParseFail "invalid hex in unicode escape" pos
    | Some cp ->
      if cp >= 0xD800 && cp <= 0xDBFF then
        // High surrogate: MUST be followed by a backslash-u low surrogate.
        (if jbyte_at input (pos + 6) = 0x5C && jbyte_at input (pos + 7) = 0x75 then
           match json_read_hex4 input (pos + 8) with
           | None -> ParseFail "invalid hex in low surrogate escape" pos
           | Some lo ->
             if lo >= 0xDC00 && lo <= 0xDFFF then
               let combined : nat =
                 0x10000 + op_Multiply (cp - 0xD800) 0x400 + (lo - 0xDC00) in
               ParseOk (json_utf8_of_codepoint combined) (pos + 12)
             else ParseFail "high surrogate not followed by low surrogate" pos
         else ParseFail "unpaired high surrogate" pos)
      else if cp >= 0xDC00 && cp <= 0xDFFF then
        ParseFail "lone low surrogate" pos
      else
        ParseOk (json_utf8_of_codepoint cp) (pos + 6)
  else ParseFail "invalid escape sequence in JSON string" pos

// String body after the opening quote. Accumulates raw byte spans (sliced
// verbatim, preserving multi-byte UTF-8) plus decoded escape pieces, in
// reverse order; joins them at the closing quote.
let rec json_string_segments
    (input:string) (seg_start:nat) (pos:nat{pos >= seg_start})
    (segs:list string) (fuel:nat)
  : Tot (parse_result string) (decreases fuel) =
  if fuel = 0 then ParseFail "unterminated JSON string" pos
  else
    let len = fs_byte_length input in
    if pos >= len then ParseFail "unterminated JSON string" pos
    else
      let b = fs_byte_at input pos in
      if b = 0x22 then
        let segs_done = fs_byte_sub input seg_start (pos - seg_start) :: segs in
        ParseOk (String.concat "" (List.Tot.rev segs_done)) (pos + 1)
      else if b = 0x5C then
        let raw = fs_byte_sub input seg_start (pos - seg_start) in
        (match json_escape_piece input pos with
         | ParseFail msg fpos -> ParseFail msg fpos
         | ParseOk piece npos ->
           json_string_segments input npos npos (piece :: raw :: segs) (fuel - 1))
      else if b < 0x20 then
        ParseFail "raw control character in JSON string" pos
      else
        json_string_segments input seg_start (pos + 1) segs (fuel - 1)

// Parse a JSON string starting at the opening double quote.
let json_parse_string (input:string) (pos:nat) : parse_result string =
  if jbyte_at input pos = 0x22 then
    json_string_segments input (pos + 1) (pos + 1) [] (fs_byte_length input + 1)
  else ParseFail "expected JSON string" pos

// ================================================================
// Numbers (strict RFC 8259 grammar)
// ================================================================

// Position after a run of ASCII digits starting at pos.
let rec json_scan_digits (input:string) (pos:nat) (fuel:nat)
  : Tot (p:nat{p >= pos}) (decreases fuel) =
  if fuel = 0 then pos
  else
    let b = jbyte_at input pos in
    if b >= 0x30 && b <= 0x39 then json_scan_digits input (pos + 1) (fuel - 1)
    else pos

// Optional fraction part: dot digit+. None on a dot with no digit.
let json_number_frac (input:string) (p:nat) : option (q:nat{q >= p}) =
  if jbyte_at input p = 0x2E then
    let b = jbyte_at input (p + 1) in
    if b >= 0x30 && b <= 0x39
    then Some (json_scan_digits input (p + 2) (fs_byte_length input + 1))
    else None
  else Some p

// Optional exponent part: (e|E) sign? digit+. None on a broken exponent.
let json_number_exp (input:string) (p:nat) : option (q:nat{q >= p}) =
  let b = jbyte_at input p in
  if b = 0x65 || b = 0x45 then
    let p1 = p + 1 in
    let p2 = if jbyte_at input p1 = 0x2B || jbyte_at input p1 = 0x2D then p1 + 1 else p1 in
    let d = jbyte_at input p2 in
    if d >= 0x30 && d <= 0x39
    then Some (json_scan_digits input (p2 + 1) (fs_byte_length input + 1))
    else None
  else Some p

// Parse a JSON number starting at pos. The ParseOk value is the verbatim
// lexeme. Note the RFC forbids leading zeros: after an initial '0' the
// integer part ends, so "0123" parses as "0" and the surrounding context
// then rejects the trailing "123".
let json_parse_number (input:string) (pos:nat) : parse_result string =
  let p1 = if jbyte_at input pos = 0x2D then pos + 1 else pos in
  let b1 = jbyte_at input p1 in
  let ipart_end : option (p:nat{p >= pos}) =
    if b1 = 0x30 then Some (p1 + 1)
    else if b1 >= 0x31 && b1 <= 0x39
    then Some (json_scan_digits input (p1 + 1) (fs_byte_length input + 1))
    else None in
  match ipart_end with
  | None -> ParseFail "invalid JSON number" pos
  | Some p2 ->
    match json_number_frac input p2 with
    | None -> ParseFail "invalid fraction in JSON number" pos
    | Some p4 ->
      match json_number_exp input p4 with
      | None -> ParseFail "invalid exponent in JSON number" pos
      | Some p_end ->
        ParseOk (fs_byte_sub input pos (p_end - pos)) p_end

// ================================================================
// Values, objects, arrays
// ================================================================

let rec json_parse_value (input:string) (pos:nat) (fuel:nat)
  : Tot (parse_result json_val) (decreases fuel) =
  if fuel = 0 then ParseFail "JSON nesting too deep" pos
  else
    let p = json_skip_ws input pos (fs_byte_length input + 1) in
    let b = jbyte_at input p in
    if b = 0x22 then
      (match json_parse_string input p with
       | ParseOk s np -> ParseOk (JString s) np
       | ParseFail msg fpos -> ParseFail msg fpos)
    else if b = 0x7B then json_parse_object input (p + 1) (fuel - 1)
    else if b = 0x5B then json_parse_array input (p + 1) (fuel - 1)
    else if b = 0x74 then
      (match pstring "true" input p with
       | ParseOk _ np -> ParseOk (JBool true) np
       | ParseFail msg fpos -> ParseFail msg fpos)
    else if b = 0x66 then
      (match pstring "false" input p with
       | ParseOk _ np -> ParseOk (JBool false) np
       | ParseFail msg fpos -> ParseFail msg fpos)
    else if b = 0x6E then
      (match pstring "null" input p with
       | ParseOk _ np -> ParseOk JNull np
       | ParseFail msg fpos -> ParseFail msg fpos)
    else if b = 0x2D || (b >= 0x30 && b <= 0x39) then
      (match json_parse_number input p with
       | ParseOk s np -> ParseOk (JNumber s) np
       | ParseFail msg fpos -> ParseFail msg fpos)
    else ParseFail "unexpected character in JSON value" p

// Object body after the opening brace.
and json_parse_object (input:string) (pos:nat) (fuel:nat)
  : Tot (parse_result json_val) (decreases fuel) =
  if fuel = 0 then ParseFail "JSON nesting too deep" pos
  else
    let p = json_skip_ws input pos (fs_byte_length input + 1) in
    if jbyte_at input p = 0x7D then ParseOk (JObject []) (p + 1)
    else json_parse_members input p (fuel - 1) []

// One or more key:value members. Strict: a comma must be followed by a
// key string, so trailing commas are rejected. acc is in reverse order.
and json_parse_members (input:string) (pos:nat) (fuel:nat) (acc:list (string & json_val))
  : Tot (parse_result json_val) (decreases fuel) =
  if fuel = 0 then ParseFail "JSON nesting too deep" pos
  else
    let p = json_skip_ws input pos (fs_byte_length input + 1) in
    match json_parse_string input p with
    | ParseFail msg fpos -> ParseFail msg fpos
    | ParseOk key p1 ->
      let p2 = json_skip_ws input p1 (fs_byte_length input + 1) in
      if jbyte_at input p2 <> 0x3A then ParseFail "expected colon in JSON object" p2
      else
        (match json_parse_value input (p2 + 1) (fuel - 1) with
         | ParseFail msg fpos -> ParseFail msg fpos
         | ParseOk v p3 ->
           let acc2 = (key, v) :: acc in
           let p4 = json_skip_ws input p3 (fs_byte_length input + 1) in
           let b = jbyte_at input p4 in
           if b = 0x7D then ParseOk (JObject (List.Tot.rev acc2)) (p4 + 1)
           else if b = 0x2C then json_parse_members input (p4 + 1) (fuel - 1) acc2
           else ParseFail "expected comma or closing brace in JSON object" p4)

// Array body after the opening bracket.
and json_parse_array (input:string) (pos:nat) (fuel:nat)
  : Tot (parse_result json_val) (decreases fuel) =
  if fuel = 0 then ParseFail "JSON nesting too deep" pos
  else
    let p = json_skip_ws input pos (fs_byte_length input + 1) in
    if jbyte_at input p = 0x5D then ParseOk (JArray []) (p + 1)
    else json_parse_items input p (fuel - 1) []

// One or more array items. Strict: a comma must be followed by a value,
// so trailing commas are rejected. acc is in reverse order.
and json_parse_items (input:string) (pos:nat) (fuel:nat) (acc:list json_val)
  : Tot (parse_result json_val) (decreases fuel) =
  if fuel = 0 then ParseFail "JSON nesting too deep" pos
  else
    match json_parse_value input pos (fuel - 1) with
    | ParseFail msg fpos -> ParseFail msg fpos
    | ParseOk v p1 ->
      let acc2 = v :: acc in
      let p2 = json_skip_ws input p1 (fs_byte_length input + 1) in
      let b = jbyte_at input p2 in
      if b = 0x5D then ParseOk (JArray (List.Tot.rev acc2)) (p2 + 1)
      else if b = 0x2C then json_parse_items input (p2 + 1) (fuel - 1) acc2
      else ParseFail "expected comma or closing bracket in JSON array" p2

// ================================================================
// Top level
// ================================================================

// Parse a complete RFC 8259 JSON text: exactly one value, with only JSON
// whitespace before and after. Failure keeps the diagnostic message and
// byte position.
let parse_json_text (input:string) : parse_result json_val =
  let len = fs_byte_length input in
  match json_parse_value input 0 (len + 1) with
  | ParseFail msg fpos -> ParseFail msg fpos
  | ParseOk v p ->
    let p2 = json_skip_ws input p (len + 1) in
    if p2 >= len then ParseOk v p2
    else ParseFail "trailing content after JSON value" p2

// Option-typed convenience wrapper.
let parse_json (input:string) : option json_val =
  match parse_json_text input with
  | ParseOk v _ -> Some v
  | ParseFail _ _ -> None

// ================================================================
// Accessors over object trees
// ================================================================

let json_get_field (key:string) (obj:json_val) : option json_val =
  match obj with
  | JObject fields ->
    (match List.Tot.find (fun (kv:(string & json_val)) -> fst kv = key) fields with
     | Some kv -> Some (snd kv)
     | None -> None)
  | _ -> None

let json_get_string (key:string) (obj:json_val) : option string =
  match json_get_field key obj with
  | Some (JString s) -> Some s
  | _ -> None

let json_get_bool (key:string) (obj:json_val) : option bool =
  match json_get_field key obj with
  | Some (JBool b) -> Some b
  | _ -> None

let json_get_array (key:string) (obj:json_val) : option (list json_val) =
  match json_get_field key obj with
  | Some (JArray items) -> Some items
  | _ -> None
