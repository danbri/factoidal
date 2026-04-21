module Parser.NTriples

open FStar.String
open FStar.List.Tot
open Parser.FastString
open Parser.Combinators
open RDF.Graph.Executable

// Issue #70: swap FStar.fs_byte_length/index/sub to byte-indexed primitives
// on the parser hot path. See Parser.FastString.fst.

(* ================================================================ *)
(* Helper: Unicode code point to UTF-8 string                       *)
(* ================================================================ *)

// Hex digit to int, returning None for non-hex characters.
// Previously returned 0 for non-hex, silently accepting \u00ZZ as \u0000.
let hex_val_opt (c:FStar.Char.char) : option int =
  let code = FStar.Char.int_of_char c in
  if code >= 0x30 && code <= 0x39 then Some (code - 0x30)
  else if code >= 0x41 && code <= 0x46 then Some (code - 0x41 + 10)
  else if code >= 0x61 && code <= 0x66 then Some (code - 0x61 + 10)
  else None

// Backward-compatible wrapper: returns 0 for non-hex (used by Turtle/TriG).
// Prefer hex_val_opt for new code.
let hex_val (c:FStar.Char.char) : int =
  match hex_val_opt c with
  | Some v -> v
  | None -> 0

// Valid codepoint for F*'s char_of_int precondition: i < 0xD7FF.
// NOTE: F*'s char type uses strict < 0xD7FF, excluding U+D7FF itself.
// Unicode allows U+D7FF (surrogates are U+D800..U+DFFF). We patch the
// extracted OCaml to use < 0xD800 via ocaml-patches.sh.
let valid_codepoint (cp:int) : bool =
  cp >= 0 && (cp < 0xD7FF || (cp >= 0xE000 && cp <= 0x10FFFF))

// Safe char_of_int: validates codepoint, returns U+FFFD for invalid
let safe_char_of_int (cp:int) : FStar.Char.char =
  if cp >= 0 && (cp < 0xD7FF || (cp >= 0xE000 && cp <= 0x10FFFF)) then
    let n : nat = cp in
    FStar.Char.char_of_int n
  else
    FStar.Char.char_of_int 0xFFFD

let codepoint_to_string (cp:int) : string =
  String.string_of_char (safe_char_of_int cp)

(* ================================================================ *)
(* N-Triples whitespace (space and tab only, not newline)           *)
(* ================================================================ *)

let is_nt_ws (c:FStar.Char.char) : bool =
  let code = FStar.Char.int_of_char c in
  code = 0x20 || code = 0x09

(* Skip spaces and tabs *)
let pws (input:string) (pos:nat) : parse_result unit =
  match ptake_while is_nt_ws input pos with
  | ParseOk _ pos' -> ParseOk () pos'
  | ParseFail msg fpos -> ParseFail msg fpos

(* ================================================================ *)
(* IRI parser: <iri-content>                                         *)
(* ================================================================ *)

// IRI-forbidden codepoints per RFC 3987 section 2.2:
// space (0x20), < (0x3C), > (0x3E), " (0x22), { (0x7B), } (0x7D),
// | (0x7C), \ (0x5C), ^ (0x5E), ` (0x60)
// These are checked for both literal characters and decoded \u/\U escapes.
let is_iri_forbidden_codepoint (code:int) : bool =
  code = 0x20 || code = 0x3C || code = 0x3E || code = 0x22 ||
  code = 0x7B || code = 0x7D || code = 0x7C || code = 0x5C ||
  code = 0x5E || code = 0x60

// IRI content: everything that's not '>' or whitespace control chars.
// N-Triples IRIs do not contain escape sequences except \uXXXX and \UXXXXXXXX.

// IRI body char: valid in IRI content without escaping (code > 0x20, not forbidden, not > or backslash)
let is_iri_body_char (c:FStar.Char.char) : bool =
  let code = FStar.Char.int_of_char c in
  code > 0x20 && code <> 0x3E && code <> 0x5C &&
  not (is_iri_forbidden_codepoint code)

// Slow path for IRIs containing escapes: accumulates chars
let rec parse_iri_body_acc (input:string) (pos:nat) (acc:list char) (fuel:nat)
  : Tot (parse_result string) (decreases fuel) =
  if fuel = 0 then ParseFail "IRI too long" pos
  else
    let len = fs_byte_length input in
    if pos >= len then ParseFail "unterminated IRI" pos
    else
      let ch = fs_byte_index input pos in
      let code = FStar.Char.int_of_char ch in
      if code = 0x3E then
        ParseOk (String.string_of_list (List.Tot.rev acc)) (pos + 1)
      else if code = 0x5C then
        if pos + 1 >= len then ParseFail "backslash at end of IRI" pos
        else
          let next = fs_byte_index input (pos + 1) in
          let ncode = FStar.Char.int_of_char next in
          if ncode = 0x75 then
            if pos + 6 > len then ParseFail "incomplete \\u escape in IRI" pos
            else
              match hex_val_opt (fs_byte_index input (pos + 2)),
                    hex_val_opt (fs_byte_index input (pos + 3)),
                    hex_val_opt (fs_byte_index input (pos + 4)),
                    hex_val_opt (fs_byte_index input (pos + 5)) with
              | Some h0, Some h1, Some h2, Some h3 ->
                let cp = ((h0 `op_Multiply` 4096) + (h1 `op_Multiply` 256) + (h2 `op_Multiply` 16) + h3) in
                if not (valid_codepoint cp) then ParseFail "surrogate codepoint in \\u escape" pos
                else if is_iri_forbidden_codepoint cp then ParseFail "IRI-forbidden codepoint in \\u escape" pos
                else
                  let c = safe_char_of_int cp in
                  parse_iri_body_acc input (pos + 6) (c :: acc) (fuel - 1)
              | _ -> ParseFail "invalid hex digit in \\u escape" pos
          else if ncode = 0x55 then
            if pos + 10 > len then ParseFail "incomplete \\U escape in IRI" pos
            else
              match hex_val_opt (fs_byte_index input (pos + 2)),
                    hex_val_opt (fs_byte_index input (pos + 3)),
                    hex_val_opt (fs_byte_index input (pos + 4)),
                    hex_val_opt (fs_byte_index input (pos + 5)),
                    hex_val_opt (fs_byte_index input (pos + 6)),
                    hex_val_opt (fs_byte_index input (pos + 7)),
                    hex_val_opt (fs_byte_index input (pos + 8)),
                    hex_val_opt (fs_byte_index input (pos + 9)) with
              | Some h0, Some h1, Some h2, Some h3, Some h4, Some h5, Some h6, Some h7 ->
                let cp = ((h0 `op_Multiply` 268435456) + (h1 `op_Multiply` 16777216) + (h2 `op_Multiply` 1048576) + (h3 `op_Multiply` 65536)
                       + (h4 `op_Multiply` 4096) + (h5 `op_Multiply` 256) + (h6 `op_Multiply` 16) + h7) in
                if not (valid_codepoint cp) then ParseFail "surrogate codepoint in \\U escape" pos
                else if is_iri_forbidden_codepoint cp then ParseFail "IRI-forbidden codepoint in \\U escape" pos
                else
                  let c = safe_char_of_int cp in
                  parse_iri_body_acc input (pos + 10) (c :: acc) (fuel - 1)
              | _ -> ParseFail "invalid hex digit in \\U escape" pos
          else
            ParseFail "invalid escape in IRI" pos
      else if code <= 0x20 || is_iri_forbidden_codepoint code then
        ParseFail "invalid character in IRI" pos
      else
        parse_iri_body_acc input (pos + 1) (ch :: acc) (fuel - 1)

// Fast-path IRI scanner: find position of '>' without building a char list.
// Returns the position of '>' (not past it). Falls back on escape or error.
let rec scan_iri_end (input:string) (pos:nat) (fuel:nat)
  : Tot (parse_result nat) (decreases fuel) =
  if fuel = 0 then ParseFail "IRI too long" pos
  else
    let len = fs_byte_length input in
    if pos >= len then ParseFail "unterminated IRI" pos
    else
      let ch = fs_byte_index input pos in
      let code = FStar.Char.int_of_char ch in
      if code = 0x3E then ParseOk pos pos  // return position OF the '>'
      else if code = 0x5C then ParseFail "has escapes" pos
      else if code <= 0x20 || is_iri_forbidden_codepoint code then
        ParseFail "invalid character in IRI" pos
      else
        scan_iri_end input (pos + 1) (fuel - 1)

let parse_iri_raw : parser iri =
  fun input pos ->
    let len = fs_byte_length input in
    if pos >= len then ParseFail "expected '<'" pos
    else
      let ch = fs_byte_index input pos in
      if FStar.Char.int_of_char ch = 0x3C then
        let start = pos + 1 in
        let fuel = len - pos in
        // Try fast-path first: scan for '>' with no escapes
        match scan_iri_end input start fuel with
        | ParseOk gt_pos _ ->
          // gt_pos is position of '>'; IRI content is [start, gt_pos)
          let iri_len = gt_pos - start in
          if iri_len > 0 && start + iri_len <= len then
            ParseOk (fs_byte_sub input start iri_len) (gt_pos + 1)
          else
            ParseOk "" (gt_pos + 1)
        | ParseFail "has escapes" _ ->
          parse_iri_body_acc input start [] fuel
        | ParseFail msg fpos -> ParseFail msg fpos
      else
        ParseFail "expected '<'" pos

let parse_iri : parser wf_iri =
  fun input pos ->
    match parse_iri_raw input pos with
    | ParseOk i pos' ->
      if is_iri i then ParseOk i pos'
      else ParseFail "invalid IRI" pos
    | ParseFail msg fpos -> ParseFail msg fpos

(* ================================================================ *)
(* Blank node parser: _:label                                       *)
(* ================================================================ *)

// Blank-node label body char (codepoint-aware, Pass-3 issue #89).
// Walks one Unicode codepoint at a time via fs_cp_at so multi-byte
// UTF-8 identifiers (Greek, Han, dieresis-vowels, astral-plane code
// points, etc.) succeed. ASCII byte-fast-path preserved for speed.
let is_bnode_char_cp (cp: nat) : bool =
  if cp < 0x80 then
    (cp >= 0x30 && cp <= 0x39) ||
    (cp >= 0x41 && cp <= 0x5A) ||
    (cp >= 0x61 && cp <= 0x7A) ||
    cp = 0x5F || cp = 0x2D || cp = 0x2E
  else
    cp = 0xB7 ||
    (cp >= 0x00C0 && cp <= 0x00D6) ||
    (cp >= 0x00D8 && cp <= 0x00F6) ||
    (cp >= 0x00F8 && cp <= 0x02FF) ||
    (cp >= 0x0300 && cp <= 0x036F) ||
    (cp >= 0x0370 && cp <= 0x037D) ||
    (cp >= 0x037F && cp <= 0x1FFF) ||
    (cp >= 0x200C && cp <= 0x200D) ||
    (cp >= 0x203F && cp <= 0x2040) ||
    (cp >= 0x2070 && cp <= 0x218F) ||
    (cp >= 0x2C00 && cp <= 0x2FEF) ||
    (cp >= 0x3001 && cp <= 0xD7FF) ||
    (cp >= 0xF900 && cp <= 0xFDCF) ||
    (cp >= 0xFDF0 && cp <= 0xFFFD) ||
    (cp >= 0x10000 && cp <= 0xEFFFF)

// Blank-node label start char (PN_CHARS_U | [0-9]).
let is_bnode_start_cp (cp: nat) : bool =
  if cp < 0x80 then
    (cp >= 0x41 && cp <= 0x5A) ||
    (cp >= 0x61 && cp <= 0x7A) ||
    cp = 0x5F ||
    (cp >= 0x30 && cp <= 0x39)
  else
    (cp >= 0x00C0 && cp <= 0x00D6) ||
    (cp >= 0x00D8 && cp <= 0x00F6) ||
    (cp >= 0x00F8 && cp <= 0x02FF) ||
    (cp >= 0x0370 && cp <= 0x037D) ||
    (cp >= 0x037F && cp <= 0x1FFF) ||
    (cp >= 0x200C && cp <= 0x200D) ||
    (cp >= 0x2070 && cp <= 0x218F) ||
    (cp >= 0x2C00 && cp <= 0x2FEF) ||
    (cp >= 0x3001 && cp <= 0xD7FF) ||
    (cp >= 0xF900 && cp <= 0xFDCF) ||
    (cp >= 0xFDF0 && cp <= 0xFFFD) ||
    (cp >= 0x10000 && cp <= 0xEFFFF)

// Scan a run of bnode body codepoints starting at pos. Returns the end
// byte position. Walks one codepoint at a time via fs_cp_at; each step
// advances by the codepoint's UTF-8 byte length (1..4). `fuel` is
// byte-bounded, so the per-step `fuel - 1` decrement is still adequate
// (the scan can only fire byte_length times total).
let rec scan_bnode_body_cp (input: string) (pos: nat) (fuel: nat)
  : Tot (r:nat{r >= pos}) (decreases fuel) =
  if fuel = 0 then pos
  else
    let len = fs_byte_length input in
    if pos >= len then pos
    else
      let b = fs_byte_at input pos in
      if b < 0x80 then
        if is_bnode_char_cp b then scan_bnode_body_cp input (pos + 1) (fuel - 1)
        else pos
      else
        let (cp, adv) = fs_cp_at input pos in
        let advance : nat = if adv = 0 then 1 else adv in
        if is_bnode_char_cp cp then
          scan_bnode_body_cp input (pos + advance) (fuel - 1)
        else pos

let parse_bnode : parser bnode_id =
  fun input pos ->
    let len = fs_byte_length input in
    (* Match "_:" prefix *)
    if pos + 2 > len then ParseFail "expected '_:'" pos
    else
      let c0 = fs_byte_at input pos in
      let c1 = fs_byte_at input (pos + 1) in
      if c0 = 0x5F && c1 = 0x3A then
        (* Read label: first char must be bnode_start, rest bnode_char *)
        let start_pos = pos + 2 in
        if start_pos >= len then ParseFail "empty blank node label" start_pos
        else
          let b0 = fs_byte_at input start_pos in
          let (start_cp, start_adv) =
            if b0 < 0x80 then (b0, 1)
            else
              let (cp, adv) = fs_cp_at input start_pos in
              let advance : nat = if adv = 0 then 1 else adv in
              (cp, advance)
          in
          if is_bnode_start_cp start_cp then
            (* Scan the remainder of the label as PN_CHARS (+ '.'). *)
            let after_first : nat = start_pos + start_adv in
            let fuel : nat = if len > after_first then len - after_first + 1 else 1 in
            let end_pos = scan_bnode_body_cp input after_first fuel in
            (* Trailing '.' is allowed inside the label but not as the last
               character; trim it if present (matches the historical byte
               implementation). *)
            let final_end =
              if end_pos > start_pos && fs_byte_at input (end_pos - 1) = 0x2E
              then end_pos - 1
              else end_pos
            in
            if final_end > start_pos && final_end <= len then
              ParseOk (fs_byte_sub input start_pos (final_end - start_pos)) final_end
            else
              ParseFail "empty blank node label" start_pos
          else
            ParseFail "invalid blank node label start character" start_pos
      else
        ParseFail "expected '_:'" pos

(* ================================================================ *)
(* String literal parser with escape handling                       *)
(* ================================================================ *)

(* Parse the body of a quoted string, handling N-Triples escapes:
   \t \n \r \\ \" \b \f \uXXXX \UXXXXXXXX *)
let rec parse_string_body (input:string) (pos:nat) (acc:list char) (fuel:nat)
  : Tot (parse_result string) (decreases fuel) =
  if fuel = 0 then ParseFail "string too long" pos
  else
    let len = fs_byte_length input in
    if pos >= len then ParseFail "unterminated string literal" pos
    else
      let ch = fs_byte_index input pos in
      let code = FStar.Char.int_of_char ch in
      if code = 0x22 then (* '"' - end of string *)
        ParseOk (String.string_of_list (List.Tot.rev acc)) (pos + 1)
      else if code = 0x5C then (* backslash *)
        if pos + 1 >= len then ParseFail "backslash at end of string" pos
        else
          let esc = fs_byte_index input (pos + 1) in
          let esc_code = FStar.Char.int_of_char esc in
          if esc_code = 0x74 then (* \t *)
            parse_string_body input (pos + 2) (FStar.Char.char_of_int 0x09 :: acc) (fuel - 1)
          else if esc_code = 0x6E then (* \n *)
            parse_string_body input (pos + 2) (FStar.Char.char_of_int 0x0A :: acc) (fuel - 1)
          else if esc_code = 0x72 then (* \r *)
            parse_string_body input (pos + 2) (FStar.Char.char_of_int 0x0D :: acc) (fuel - 1)
          else if esc_code = 0x5C then (* \\ *)
            parse_string_body input (pos + 2) (FStar.Char.char_of_int 0x5C :: acc) (fuel - 1)
          else if esc_code = 0x22 then (* \" *)
            parse_string_body input (pos + 2) (FStar.Char.char_of_int 0x22 :: acc) (fuel - 1)
          else if esc_code = 0x62 then (* \b - backspace *)
            parse_string_body input (pos + 2) (FStar.Char.char_of_int 0x08 :: acc) (fuel - 1)
          else if esc_code = 0x66 then (* \f - form feed *)
            parse_string_body input (pos + 2) (FStar.Char.char_of_int 0x0C :: acc) (fuel - 1)
          else if esc_code = 0x75 then // \uXXXX
            if pos + 6 > len then ParseFail "incomplete \\u escape" pos
            else
              match hex_val_opt (fs_byte_index input (pos + 2)),
                    hex_val_opt (fs_byte_index input (pos + 3)),
                    hex_val_opt (fs_byte_index input (pos + 4)),
                    hex_val_opt (fs_byte_index input (pos + 5)) with
              | Some h0, Some h1, Some h2, Some h3 ->
                let cp = ((h0 `op_Multiply` 4096) + (h1 `op_Multiply` 256) + (h2 `op_Multiply` 16) + h3) in
                if not (valid_codepoint cp) then ParseFail "surrogate codepoint in \\u escape" pos
                else
                  let c = safe_char_of_int cp in
                  parse_string_body input (pos + 6) (c :: acc) (fuel - 1)
              | _ -> ParseFail "invalid hex digit in \\u escape" pos
          else if esc_code = 0x55 then // \UXXXXXXXX
            if pos + 10 > len then ParseFail "incomplete \\U escape" pos
            else
              match hex_val_opt (fs_byte_index input (pos + 2)),
                    hex_val_opt (fs_byte_index input (pos + 3)),
                    hex_val_opt (fs_byte_index input (pos + 4)),
                    hex_val_opt (fs_byte_index input (pos + 5)),
                    hex_val_opt (fs_byte_index input (pos + 6)),
                    hex_val_opt (fs_byte_index input (pos + 7)),
                    hex_val_opt (fs_byte_index input (pos + 8)),
                    hex_val_opt (fs_byte_index input (pos + 9)) with
              | Some h0, Some h1, Some h2, Some h3, Some h4, Some h5, Some h6, Some h7 ->
                let cp = ((h0 `op_Multiply` 268435456) + (h1 `op_Multiply` 16777216) + (h2 `op_Multiply` 1048576) + (h3 `op_Multiply` 65536)
                       + (h4 `op_Multiply` 4096) + (h5 `op_Multiply` 256) + (h6 `op_Multiply` 16) + h7) in
                if not (valid_codepoint cp) then ParseFail "surrogate codepoint in \\U escape" pos
                else
                  let c = safe_char_of_int cp in
                  parse_string_body input (pos + 10) (c :: acc) (fuel - 1)
              | _ -> ParseFail "invalid hex digit in \\U escape" pos
          else
            ParseFail (String.concat "" ["invalid escape: \\"; String.string_of_char esc]) pos
      else if code = 0x0A || code = 0x0D then
        (* Raw newlines/carriage returns not allowed in N-Triples strings *)
        ParseFail "unescaped newline in string literal" pos
      else if code < 0x80 then
        (* ASCII byte fast path. *)
        parse_string_body input (pos + 1) (ch :: acc) (fuel - 1)
      else
        (* Pass-3 issue #89: decode UTF-8 codepoint so that acc holds one
           char per codepoint, matching String.string_of_list semantics. *)
        let (cp, adv) = fs_cp_at input pos in
        let advance : nat = if adv = 0 then 1 else adv in
        parse_string_body input (pos + advance)
          (safe_char_of_int cp :: acc) (fuel - 1)

// Fast-path string scan: find closing quote with no escapes or raw newlines.
// Returns position after the closing quote, or fails to signal fallback needed.
let rec scan_string_fast (input:string) (pos:nat) (fuel:nat)
  : Tot (parse_result unit) (decreases fuel) =
  if fuel = 0 then ParseFail "string too long" pos
  else
    let len = fs_byte_length input in
    if pos >= len then ParseFail "unterminated string literal" pos
    else
      let ch = fs_byte_index input pos in
      let code = FStar.Char.int_of_char ch in
      if code = 0x22 then ParseOk () (pos + 1)       // closing quote
      else if code = 0x5C then ParseFail "has escapes" pos  // backslash, fall back
      else if code = 0x0A || code = 0x0D then ParseFail "unescaped newline in string literal" pos
      else scan_string_fast input (pos + 1) (fuel - 1)

let parse_string_literal : parser string =
  fun input pos ->
    let len = fs_byte_length input in
    if pos >= len then ParseFail "expected '\"'" pos
    else
      let ch = fs_byte_index input pos in
      if FStar.Char.int_of_char ch = 0x22 then
        let start = pos + 1 in
        let fuel = len - pos in
        // Fast path: scan for closing quote without escapes
        match scan_string_fast input start fuel with
        | ParseOk () end_pos ->
          // end_pos is one past the closing quote; string content is [start, end_pos-1)
          let str_len = end_pos - 1 - start in
          if str_len > 0 && start + str_len <= len then
            ParseOk (fs_byte_sub input start str_len) end_pos
          else
            ParseOk "" end_pos
        | ParseFail "has escapes" _ ->
          parse_string_body input start [] fuel
        | ParseFail msg fpos -> ParseFail msg fpos
      else
        ParseFail "expected '\"'" pos

(* ================================================================ *)
(* Language tag parser: @lang-subtag                                 *)
(* ================================================================ *)

(* Language tag characters: a-zA-Z0-9 and '-' *)
let is_lang_char (c:FStar.Char.char) : bool =
  let code = FStar.Char.int_of_char c in
  (code >= 0x41 && code <= 0x5A) ||  (* A-Z *)
  (code >= 0x61 && code <= 0x7A) ||  (* a-z *)
  (code >= 0x30 && code <= 0x39) ||  (* 0-9 *)
  code = 0x2D                         (* - *)

// BCP 47: language tag must start with a letter (a-zA-Z)
let is_alpha (c:FStar.Char.char) : bool =
  let code = FStar.Char.int_of_char c in
  (code >= 0x41 && code <= 0x5A) || (code >= 0x61 && code <= 0x7A)

let parse_lang_tag : parser string =
  fun input pos ->
    let len = fs_byte_length input in
    if pos >= len then ParseFail "expected '@'" pos
    else
      let ch = fs_byte_index input pos in
      if FStar.Char.int_of_char ch = 0x40 then // '@'
        if pos + 1 >= len then ParseFail "expected language tag after '@'" (pos + 1)
        else if not (is_alpha (fs_byte_index input (pos + 1))) then
          ParseFail "language tag must start with a letter" (pos + 1)
        else
          match ptake_while1_pos is_lang_char input (pos + 1) with
          | ParseOk lang pos' -> ParseOk lang pos'
          | ParseFail _ fpos -> ParseFail "expected language tag after '@'" fpos
      else
        ParseFail "expected '@'" pos

(* ================================================================ *)
(* Datatype parser: ^^<iri>                                         *)
(* ================================================================ *)

let parse_datatype : parser wf_iri =
  fun input pos ->
    let len = fs_byte_length input in
    if pos + 2 > len then ParseFail "expected '^^'" pos
    else
      let c0 = fs_byte_index input pos in
      let c1 = fs_byte_index input (pos + 1) in
      if FStar.Char.int_of_char c0 = 0x5E && FStar.Char.int_of_char c1 = 0x5E then
        parse_iri input (pos + 2)
      else
        ParseFail "expected '^^'" pos

(* ================================================================ *)
(* Literal parser: "string" optionally followed by @lang or ^^<dt>  *)
(* ================================================================ *)

let parse_literal : parser wf_literal =
  fun input pos ->
    match parse_string_literal input pos with
    | ParseOk lexical pos' ->
      let len = fs_byte_length input in
      if pos' >= len then
        (* Plain literal — per RDF 1.1, has datatype xsd:string *)
        let lit = { lexical_form = lexical; datatype = xsd_string; lang_tag = None } in
        if literal_wf lit then ParseOk lit pos'
        else ParseFail "invalid literal" pos
      else
        let next = fs_byte_index input pos' in
        let next_code = FStar.Char.int_of_char next in
        if next_code = 0x40 then (* '@' — language tag *)
          begin match parse_lang_tag input pos' with
          | ParseOk lang pos'' ->
            let lit = { lexical_form = lexical; datatype = rdf_lang_string; lang_tag = Some lang } in
            if literal_wf lit then ParseOk lit pos''
            else ParseFail "invalid literal" pos
          | ParseFail msg fpos -> ParseFail msg fpos
          end
        else if next_code = 0x5E then (* '^' — might be '^^' datatype *)
          begin match parse_datatype input pos' with
          | ParseOk dt pos'' ->
            let lit = { lexical_form = lexical; datatype = dt; lang_tag = None } in
            if literal_wf lit then ParseOk lit pos''
            else ParseFail "invalid literal" pos
          | ParseFail msg fpos -> ParseFail msg fpos
          end
        else
          (* Plain literal *)
          let lit = { lexical_form = lexical; datatype = xsd_string; lang_tag = None } in
          if literal_wf lit then ParseOk lit pos'
          else ParseFail "invalid literal" pos
    | ParseFail msg fpos -> ParseFail msg fpos

(* ================================================================ *)
(* Subject parser: IRI or blank node                                *)
(* ================================================================ *)

let parse_subject : parser subject =
  fun input pos ->
    let len = fs_byte_length input in
    if pos >= len then ParseFail "expected subject" pos
    else
      let ch = fs_byte_index input pos in
      let code = FStar.Char.int_of_char ch in
      if code = 0x3C then (* '<' — IRI *)
        begin match parse_iri input pos with
        | ParseOk i pos' -> ParseOk (S_IRI i) pos'
        | ParseFail msg fpos -> ParseFail msg fpos
        end
      else if code = 0x5F then (* '_' — blank node *)
        begin match parse_bnode input pos with
        | ParseOk b pos' -> ParseOk (S_BNode b) pos'
        | ParseFail msg fpos -> ParseFail msg fpos
        end
      else
        ParseFail "expected '<' or '_:' for subject" pos

(* ================================================================ *)
(* Object parser: IRI, blank node, or literal                       *)
(* ================================================================ *)

let parse_object : parser rdf_term =
  fun input pos ->
    let len = fs_byte_length input in
    if pos >= len then ParseFail "expected object" pos
    else
      let ch = fs_byte_index input pos in
      let code = FStar.Char.int_of_char ch in
      if code = 0x3C then (* '<' — IRI *)
        begin match parse_iri input pos with
        | ParseOk i pos' -> ParseOk (T_IRI i) pos'
        | ParseFail msg fpos -> ParseFail msg fpos
        end
      else if code = 0x5F then (* '_' — blank node *)
        begin match parse_bnode input pos with
        | ParseOk b pos' -> ParseOk (T_BNode b) pos'
        | ParseFail msg fpos -> ParseFail msg fpos
        end
      else if code = 0x22 then (* '"' — literal *)
        begin match parse_literal input pos with
        | ParseOk lit pos' -> ParseOk (T_Literal lit) pos'
        | ParseFail msg fpos -> ParseFail msg fpos
        end
      else
        ParseFail "expected '<', '_:', or '\"' for object" pos

(* ================================================================ *)
(* Triple parser: subject ws+ predicate ws+ object ws* '.' ws*      *)
(* ================================================================ *)

let parse_triple : parser triple =
  fun input pos ->
    (* Skip leading whitespace *)
    match pws input pos with
    | ParseOk () pos1 ->
      begin match parse_subject input pos1 with
      | ParseOk subj pos2 ->
        begin match pws input pos2 with
        | ParseOk () pos3 ->
          begin match parse_iri input pos3 with
          | ParseOk pred pos4 ->
            begin match pws input pos4 with
            | ParseOk () pos5 ->
              begin match parse_object input pos5 with
              | ParseOk obj pos6 ->
                begin match pws input pos6 with
                | ParseOk () pos7 ->
                  (* Expect '.' *)
                  let len = fs_byte_length input in
                  if pos7 >= len then ParseFail "expected '.'" pos7
                  else
                    let dot = fs_byte_index input pos7 in
                    if FStar.Char.int_of_char dot = 0x2E then
                      ParseOk ({ s = subj; p = pred; o = obj }) (pos7 + 1)
                    else
                      ParseFail "expected '.'" pos7
                | ParseFail msg fpos -> ParseFail msg fpos
                end
              | ParseFail msg fpos -> ParseFail msg fpos
              end
            | ParseFail msg fpos -> ParseFail msg fpos
            end
          | ParseFail msg fpos -> ParseFail msg fpos
          end
        | ParseFail msg fpos -> ParseFail msg fpos
        end
      | ParseFail msg fpos -> ParseFail msg fpos
      end
    | ParseFail msg fpos -> ParseFail msg fpos

(* ================================================================ *)
(* Line-by-line document parser                                     *)
(* ================================================================ *)

(* Skip a comment: from '#' to end of line (or end of input) *)
let skip_comment (input:string) (pos:nat) : nat =
  let len = fs_byte_length input in
  if pos >= len then pos
  else
    let ch = fs_byte_index input pos in
    if FStar.Char.int_of_char ch = 0x23 then (* '#' *)
      (* Skip to end of line *)
      let rec skip_to_eol (p:nat) (fuel:nat) : Tot nat (decreases fuel) =
        if fuel = 0 then p
        else if p >= len then p
        else
          let c = fs_byte_index input p in
          let cc = FStar.Char.int_of_char c in
          if cc = 0x0A || cc = 0x0D then p
          else skip_to_eol (p + 1) (fuel - 1)
      in
      skip_to_eol (pos + 1) (len - pos)
    else pos

(* Skip newline characters (LF, CRLF, CR) *)
let skip_eol (input:string) (pos:nat) : nat =
  let len = fs_byte_length input in
  if pos >= len then pos
  else
    let ch = fs_byte_index input pos in
    let code = FStar.Char.int_of_char ch in
    if code = 0x0D then (* CR *)
      if pos + 1 < len then
        let next = fs_byte_index input (pos + 1) in
        if FStar.Char.int_of_char next = 0x0A then pos + 2  (* CRLF *)
        else pos + 1  (* bare CR *)
      else pos + 1
    else if code = 0x0A then pos + 1  (* LF *)
    else pos

(* Parse an entire N-Triples document, returning a list of triples.
   Processes line by line:
   - Skip whitespace
   - If '#', skip comment to end of line
   - If end of line or end of input, skip
   - Otherwise, parse a triple
*)
let rec parse_ntriples_acc (input:string) (pos:nat) (acc:list triple) (fuel:nat)
  : Tot (list triple) (decreases fuel) =
  if fuel = 0 then List.Tot.rev acc
  else
    let len = fs_byte_length input in
    if pos >= len then List.Tot.rev acc
    else
      (* Skip whitespace (space/tab) *)
      let pos1 : nat = match pws input pos with
                       | ParseOk () p -> p
                       | _ -> pos in
      if pos1 >= len then List.Tot.rev acc
      else
        let ch = fs_byte_index input pos1 in
        let code = FStar.Char.int_of_char ch in
        if code = 0x23 then (* '#' — comment line *)
          let pos2 = skip_comment input pos1 in
          let pos3 = skip_eol input pos2 in
          if pos3 = pos1 then List.Tot.rev acc  (* no progress — stop *)
          else parse_ntriples_acc input pos3 acc (fuel - 1)
        else if code = 0x0A || code = 0x0D then (* empty line *)
          let pos2 = skip_eol input pos1 in
          if pos2 = pos1 then List.Tot.rev acc  (* no progress *)
          else parse_ntriples_acc input pos2 acc (fuel - 1)
        else
          (* Try to parse a triple *)
          match parse_triple input pos1 with
          | ParseOk t pos2 ->
            (* After the '.', skip optional whitespace, optional comment, then EOL *)
            let pos3 = match pws input pos2 with
                       | ParseOk () p -> p
                       | _ -> pos2 in
            let pos4 = skip_comment input pos3 in
            let pos5 = skip_eol input pos4 in
            let pos_next = if pos5 > pos1 then pos5
                          else if pos4 > pos1 then pos4
                          else pos2 in
            parse_ntriples_acc input pos_next (t :: acc) (fuel - 1)
          | ParseFail _ _ ->
            (* Skip to next line on parse failure *)
            let rec skip_line (p:nat) (f:nat) : Tot nat (decreases f) =
              if f = 0 then p
              else if p >= len then p
              else
                let c = fs_byte_index input p in
                let cc = FStar.Char.int_of_char c in
                if cc = 0x0A || cc = 0x0D then skip_eol input p
                else skip_line (p + 1) (f - 1)
            in
            let pos2 = skip_line pos1 (len - pos1) in
            if pos2 = pos1 then List.Tot.rev acc  (* no progress *)
            else parse_ntriples_acc input pos2 acc (fuel - 1)

let parse_ntriples (input:string) : list triple =
  let len = fs_byte_length input in
  parse_ntriples_acc input 0 [] (len + 1)

let rec parse_ntriples_strict_acc (input:string) (pos:nat) (acc:list triple) (fuel:nat)
  : Tot (option (list triple)) (decreases fuel) =
  if fuel = 0 then None
  else
    let len = fs_byte_length input in
    if pos >= len then Some (List.Tot.rev acc)
    else
      let pos1 : nat = match pws input pos with
                       | ParseOk () p -> p
                       | _ -> pos in
      if pos1 >= len then Some (List.Tot.rev acc)
      else
        let ch = fs_byte_index input pos1 in
        let code = FStar.Char.int_of_char ch in
        if code = 0x23 then
          let pos2 = skip_comment input pos1 in
          let pos3 = skip_eol input pos2 in
          if pos3 = pos1 then None
          else parse_ntriples_strict_acc input pos3 acc (fuel - 1)
        else if code = 0x0A || code = 0x0D then
          let pos2 = skip_eol input pos1 in
          if pos2 = pos1 then None
          else parse_ntriples_strict_acc input pos2 acc (fuel - 1)
        else
          match parse_triple input pos1 with
          | ParseOk t pos2 ->
            let pos3 = match pws input pos2 with
                       | ParseOk () p -> p
                       | _ -> pos2 in
            let pos4 = skip_comment input pos3 in
            let pos5 = skip_eol input pos4 in
            if pos5 > pos1 then
              parse_ntriples_strict_acc input pos5 (t :: acc) (fuel - 1)
            else if pos2 >= len then
              parse_ntriples_strict_acc input pos2 (t :: acc) (fuel - 1)
            else
              None
          | ParseFail _ _ -> None

let parse_ntriples_strict (input:string) : option (list triple) =
  let len = fs_byte_length input in
  parse_ntriples_strict_acc input 0 [] (len + 1)
