module Parser.Turtle

open FStar.String
open FStar.List.Tot
open FStar.Char
open Parser.Combinators
open Parser.NTriples
open RDF.Graph.Executable

(* ================================================================ *)
(* Turtle parser state                                               *)
(* ================================================================ *)

(* Turtle extends N-Triples with prefixes, base IRIs, and syntactic sugar.
   The parser threads state through all productions. *)
noeq type turtle_state = {
  prefixes: list (string & string);   (* prefix -> IRI base mapping *)
  base_iri: string;                   (* current base IRI for relative resolution *)
  bnode_counter: nat;                 (* counter for generating anonymous blank node IDs *)
}

let empty_turtle_state : turtle_state = {
  prefixes = [];
  base_iri = "";
  bnode_counter = 0;
}

(* Generate a fresh blank node ID and increment counter *)
let fresh_bnode (st: turtle_state) : (bnode_id & turtle_state) =
  let id = String.concat "" ["_anon"; string_of_int st.bnode_counter] in
  (id, { st with bnode_counter = st.bnode_counter + 1 })

(* ================================================================ *)
(* Prefix resolution                                                 *)
(* ================================================================ *)

(* Look up a prefix in the state *)
let rec lookup_prefix (pfx: string) (ps: list (string & string)) : option string =
  match ps with
  | [] -> None
  | (k, v) :: rest -> if k = pfx then Some v else lookup_prefix pfx rest

(* Resolve a prefixed name: prefix:localname -> full IRI *)
let resolve_prefixed_name (st: turtle_state) (prefix: string) (local: string) : option string =
  match lookup_prefix prefix st.prefixes with
  | Some base -> Some (String.concat "" [base; local])
  | None -> None

(* Find the last occurrence of '/' in a string, return index + 1
   (the position after the last slash). Returns 0 if no slash found. *)
let rec find_last_slash (s: string) (pos: nat)
  : Tot (r:nat{r <= pos}) (decreases pos) =
  if pos = 0 then 0
  else
    let idx = pos - 1 in
    if idx < String.length s && FStar.Char.int_of_char (String.index s idx) = 0x2F (* '/' *)
    then pos  (* return position after the slash *)
    else find_last_slash s idx

(* Remove the last path segment from a URI (everything after the last '/') *)
let remove_last_segment (base: string) : string =
  let len = String.length base in
  if len = 0 then ""
  else
    let cut_pos = find_last_slash base len in
    if cut_pos = 0 then base  (* no slash found, return as-is *)
    else String.sub base 0 cut_pos

(* Resolve a relative IRI against the base IRI per RFC 3986 Section 5.
   Handles: absolute IRIs (returned as-is), same-document refs,
   relative paths (resolved by removing last segment of base). *)
let resolve_iri (st: turtle_state) (rel: string) : string =
  if String.length rel = 0 then st.base_iri
  else
    let len = String.length rel in
    (* Check if already absolute: contains ":" in the first part *)
    if string_contains_colon rel then rel
    (* Check if starts with '/' — absolute path reference *)
    else if FStar.Char.int_of_char (String.index rel 0) = 0x2F then
      (* Find scheme+authority in base (everything up to 3rd '/') *)
      (* For simplicity, prepend scheme+authority from base *)
      String.concat "" [st.base_iri; rel]
    (* Check if starts with '#' — fragment-only reference *)
    else if FStar.Char.int_of_char (String.index rel 0) = 0x23 then
      String.concat "" [st.base_iri; rel]
    else
      (* Relative path — remove last segment of base, append relative *)
      let base_dir = remove_last_segment st.base_iri in
      String.concat "" [base_dir; rel]

(* ================================================================ *)
(* Turtle whitespace: spaces, tabs, newlines, and comments           *)
(* ================================================================ *)

let is_turtle_ws (c: char) : bool =
  let code = int_of_char c in
  code = 0x20 || code = 0x09 || code = 0x0A || code = 0x0D

(* Skip a single comment: # to end of line *)
let rec skip_to_eol (input: string) (pos: nat) (fuel: nat) : Tot nat (decreases fuel) =
  if fuel = 0 then pos
  else
    let len = String.length input in
    if pos >= len then pos
    else
      let c = String.index input pos in
      let code = int_of_char c in
      if code = 0x0A || code = 0x0D then pos
      else skip_to_eol input (pos + 1) (fuel - 1)

(* Skip whitespace and comments (which start with # and go to end of line) *)
let rec skip_ws_and_comments (input: string) (pos: nat) (fuel: nat) : Tot nat (decreases fuel) =
  if fuel = 0 then pos
  else
    let len = String.length input in
    if pos >= len then pos
    else
      let c = String.index input pos in
      let code = int_of_char c in
      if is_turtle_ws c then
        skip_ws_and_comments input (pos + 1) (fuel - 1)
      else if code = 0x23 then  (* '#' — comment *)
        let pos' = skip_to_eol input (pos + 1) (len - pos) in
        skip_ws_and_comments input pos' (fuel - 1)
      else
        pos

let turtle_ws (input: string) (pos: nat) : parse_result unit =
  let len = String.length input in
  let fuel = len - pos + 1 in
  if fuel >= 0 then
    ParseOk () (skip_ws_and_comments input pos fuel)
  else
    ParseOk () pos

(* ================================================================ *)
(* PN_CHARS_BASE, PN_CHARS_U, PN_CHARS — per Turtle grammar         *)
(* ================================================================ *)

// Flattened, ASCII-fast-path character predicates.
// For ASCII (code < 0x80) we resolve immediately without checking Unicode ranges.
// This is critical for performance: DBpedia and most RDF data is predominantly ASCII.

let is_pn_chars_base (c: char) : bool =
  let code = int_of_char c in
  if code < 0x80 then
    // ASCII fast path: only A-Z and a-z
    (code >= 0x41 && code <= 0x5A) || (code >= 0x61 && code <= 0x7A)
  else
    // Unicode ranges (only reached for non-ASCII chars)
    (code >= 0x00C0 && code <= 0x00D6) ||
    (code >= 0x00D8 && code <= 0x00F6) ||
    (code >= 0x00F8 && code <= 0x02FF) ||
    (code >= 0x0370 && code <= 0x037D) ||
    (code >= 0x037F && code <= 0x1FFF) ||
    (code >= 0x200C && code <= 0x200D) ||
    (code >= 0x2070 && code <= 0x218F) ||
    (code >= 0x2C00 && code <= 0x2FEF) ||
    (code >= 0x3001 && code <= 0xD7FF) ||
    (code >= 0xF900 && code <= 0xFDCF) ||
    (code >= 0xFDF0 && code <= 0xFFFD)

let is_pn_chars_u (c: char) : bool =
  let code = int_of_char c in
  if code < 0x80 then
    // ASCII fast path: A-Z, a-z, _
    (code >= 0x41 && code <= 0x5A) || (code >= 0x61 && code <= 0x7A) || code = 0x5F
  else
    is_pn_chars_base c

// Flattened is_pn_chars: single function, no call chain.
// For ASCII, resolves in one branch: A-Z, a-z, 0-9, _, -
let is_pn_chars (c: char) : bool =
  let code = int_of_char c in
  if code < 0x80 then
    // ASCII fast path: A-Z, a-z, 0-9, _, -
    (code >= 0x41 && code <= 0x5A) ||
    (code >= 0x61 && code <= 0x7A) ||
    (code >= 0x30 && code <= 0x39) ||
    code = 0x5F || code = 0x2D
  else
    // Unicode: PN_CHARS_BASE ranges + middle dot + combining chars + extenders
    code = 0xB7 ||
    (code >= 0x0300 && code <= 0x036F) ||
    (code >= 0x203F && code <= 0x2040) ||
    is_pn_chars_base c

(* ================================================================ *)
(* Prefixed name parser: prefix:local                                *)
(* ================================================================ *)

// Prefix namespace body char: is_pn_chars or dot
let is_pname_ns_body_char (c: char) : bool =
  let code = int_of_char c in
  if code < 0x80 then
    (code >= 0x41 && code <= 0x5A) ||
    (code >= 0x61 && code <= 0x7A) ||
    (code >= 0x30 && code <= 0x39) ||
    code = 0x5F || code = 0x2D || code = 0x2E
  else
    is_pn_chars c

// Parse prefix namespace using position-scan: find colon, extract substring.
let parse_pname_ns (input: string) (pos: nat) : parse_result string =
  let len = String.length input in
  if pos >= len then ParseFail "expected prefix name" pos
  else
    let c = String.index input pos in
    let code = int_of_char c in
    if code = 0x3A then
      ParseOk "" (pos + 1)
    else if is_pn_chars_base c then
      // Scan body chars, then expect colon
      let end_pos = ptake_while_scan is_pname_ns_body_char input (pos + 1) (len - pos) in
      if end_pos < len then
        let nc = String.index input end_pos in
        if int_of_char nc = 0x3A then
          ParseOk (String.sub input pos (end_pos - pos)) (end_pos + 1)
        else
          ParseFail "expected ':' in prefixed name" end_pos
      else
        ParseFail "expected ':' in prefixed name" end_pos
    else
      ParseFail "expected prefix name" pos

(* Parse local name part (after the colon).
   Local names can contain PN_CHARS, '.', ':', and percent-encoded chars.
   For now we handle the common ASCII subset. *)
// Flattened is_pn_local_char: single function, ASCII fast path
let is_pn_local_char (c: char) : bool =
  let code = int_of_char c in
  if code < 0x80 then
    // ASCII fast path: A-Z, a-z, 0-9, _, -, :, ., %, backslash
    (code >= 0x41 && code <= 0x5A) ||
    (code >= 0x61 && code <= 0x7A) ||
    (code >= 0x30 && code <= 0x39) ||
    code = 0x5F || code = 0x2D || code = 0x3A ||
    code = 0x2E || code = 0x25 || code = 0x5C
  else
    is_pn_chars c

// Flattened is_pn_local_start: single function, ASCII fast path
let is_pn_local_start (c: char) : bool =
  let code = int_of_char c in
  if code < 0x80 then
    // ASCII fast path: A-Z, a-z, 0-9, _, :, %, backslash
    (code >= 0x41 && code <= 0x5A) ||
    (code >= 0x61 && code <= 0x7A) ||
    (code >= 0x30 && code <= 0x39) ||
    code = 0x5F || code = 0x3A || code = 0x25 || code = 0x5C
  else
    is_pn_chars_u c

// Uses ptake_while_pos: scans to find end position, then extracts substring in one shot.
// No char list allocation, no List.rev, no string_of_list.
let parse_pn_local (input: string) (pos: nat) : parse_result string =
  let len = String.length input in
  if pos >= len then ParseOk "" pos
  else
    let c = String.index input pos in
    if is_pn_local_start c then
      match ptake_while_pos is_pn_local_char input pos with
      | ParseOk s pos' ->
        let slen = String.length s in
        if slen > 1 then
          let last = String.index s (slen - 1) in
          if int_of_char last = 0x2E && pos' > 0 then
            ParseOk (String.sub s 0 (slen - 1)) (pos' - 1)
          else
            ParseOk s pos'
        else if slen = 1 then
          let last = String.index s 0 in
          if int_of_char last = 0x2E && pos' > 0 then
            ParseOk "" (pos' - 1)
          else
            ParseOk s pos'
        else
          ParseOk "" pos
      | ParseFail msg fpos -> ParseFail msg fpos
    else
      ParseOk "" pos

(* Full prefixed name: pname_ns + pn_local *)
let parse_prefixed_name (input: string) (pos: nat) : parse_result (string & string) =
  match parse_pname_ns input pos with
  | ParseOk ns pos' ->
    begin match parse_pn_local input pos' with
    | ParseOk local pos'' -> ParseOk (ns, local) pos''
    | ParseFail msg fpos -> ParseFail msg fpos
    end
  | ParseFail msg fpos -> ParseFail msg fpos

(* ================================================================ *)
(* IRI parsing (full IRIs and prefixed names)                        *)
(* ================================================================ *)

(* Parse a Turtle IRI: either <full-iri> or prefix:local *)
let parse_turtle_iri (st: turtle_state) (input: string) (pos: nat) : parse_result iri =
  let len = String.length input in
  if pos >= len then ParseFail "expected IRI" pos
  else
    let c = String.index input pos in
    let code = int_of_char c in
    if code = 0x3C then  (* '<' — full IRI, may be relative like <> *)
      begin match parse_iri_raw input pos with
      | ParseOk i pos' ->
        (* Resolve relative IRI against base — empty string is valid in Turtle *)
        let resolved = resolve_iri st i in
        if is_iri resolved then ParseOk resolved pos'
        else ParseFail "resolved IRI invalid" pos
      | ParseFail msg fpos -> ParseFail msg fpos
      end
    else  (* Try prefixed name *)
      begin match parse_prefixed_name input pos with
      | ParseOk (prefix, local) pos' ->
        begin match resolve_prefixed_name st prefix local with
        | Some resolved -> ParseOk resolved pos'
        | None -> ParseFail (String.concat "" ["undefined prefix: "; prefix]) pos
        end
      | ParseFail msg fpos -> ParseFail msg fpos
      end

(* ================================================================ *)
(* Directive parsers: @prefix, @base, PREFIX, BASE                   *)
(* ================================================================ *)

// Parse @prefix directive: @prefix prefix: <iri> .
// Uses parse_iri_raw + resolve_iri to handle relative IRIs like <#> and <foo/>
let parse_at_prefix (st: turtle_state) (input: string) (pos: nat) : parse_result (string & string) =
  match pstring "@prefix" input pos with
  | ParseOk _ pos1 ->
    begin match turtle_ws input pos1 with
    | ParseOk () pos2 ->
      begin match parse_pname_ns input pos2 with
      | ParseOk ns pos3 ->
        begin match turtle_ws input pos3 with
        | ParseOk () pos4 ->
          begin match parse_iri_raw input pos4 with
          | ParseOk raw_iri pos5 ->
            let iri_val = resolve_iri st raw_iri in
            begin match turtle_ws input pos5 with
            | ParseOk () pos6 ->
              let len = String.length input in
              if pos6 < len then
                let dot = String.index input pos6 in
                if int_of_char dot = 0x2E then
                  ParseOk (ns, iri_val) (pos6 + 1)
                else
                  ParseFail "expected '.' after @prefix directive" pos6
              else
                ParseFail "expected '.' after @prefix directive" pos6
            end
          | ParseFail msg fpos -> ParseFail msg fpos
          end
        end
      | ParseFail msg fpos -> ParseFail msg fpos
      end
    end
  | ParseFail msg fpos -> ParseFail msg fpos

// Parse SPARQL-style PREFIX directive: PREFIX prefix: <iri> (no dot)
let parse_sparql_prefix (st: turtle_state) (input: string) (pos: nat) : parse_result (string & string) =
  match pstring "PREFIX" input pos with
  | ParseOk _ pos1 ->
    begin match turtle_ws input pos1 with
    | ParseOk () pos2 ->
      begin match parse_pname_ns input pos2 with
      | ParseOk ns pos3 ->
        begin match turtle_ws input pos3 with
        | ParseOk () pos4 ->
          begin match parse_iri_raw input pos4 with
          | ParseOk raw_iri pos5 ->
            let iri_val = resolve_iri st raw_iri in
            ParseOk (ns, iri_val) pos5
          | ParseFail msg fpos -> ParseFail msg fpos
          end
        end
      | ParseFail msg fpos -> ParseFail msg fpos
      end
    end
  | ParseFail msg fpos -> ParseFail msg fpos

// Parse @base directive: @base <iri> .
let parse_at_base (st: turtle_state) (input: string) (pos: nat) : parse_result string =
  match pstring "@base" input pos with
  | ParseOk _ pos1 ->
    begin match turtle_ws input pos1 with
    | ParseOk () pos2 ->
      begin match parse_iri_raw input pos2 with
      | ParseOk raw_iri pos3 ->
        let iri_val = resolve_iri st raw_iri in
        begin match turtle_ws input pos3 with
        | ParseOk () pos4 ->
          let len = String.length input in
          if pos4 < len then
            let dot = String.index input pos4 in
            if int_of_char dot = 0x2E then
              ParseOk iri_val (pos4 + 1)
            else
              ParseFail "expected '.' after @base directive" pos4
          else
            ParseFail "expected '.' after @base directive" pos4
        end
      | ParseFail msg fpos -> ParseFail msg fpos
      end
    end
  | ParseFail msg fpos -> ParseFail msg fpos

// Parse SPARQL-style BASE directive: BASE <iri> (no dot)
let parse_sparql_base (st: turtle_state) (input: string) (pos: nat) : parse_result string =
  match pstring "BASE" input pos with
  | ParseOk _ pos1 ->
    begin match turtle_ws input pos1 with
    | ParseOk () pos2 ->
      begin match parse_iri_raw input pos2 with
      | ParseOk raw_iri pos3 ->
        let iri_val = resolve_iri st raw_iri in
        ParseOk iri_val pos3
      | ParseFail msg fpos -> ParseFail msg fpos
      end
    end
  | ParseFail msg fpos -> ParseFail msg fpos

// Parse any prefix directive (@prefix or PREFIX)
let parse_prefix_directive (st: turtle_state) (input: string) (pos: nat) : parse_result (string & string) =
  match parse_at_prefix st input pos with
  | ParseOk v p -> ParseOk v p
  | ParseFail _ _ -> parse_sparql_prefix st input pos

// Parse any base directive (@base or BASE)
let parse_base_directive (st: turtle_state) (input: string) (pos: nat) : parse_result string =
  match parse_at_base st input pos with
  | ParseOk v p -> ParseOk v p
  | ParseFail _ _ -> parse_sparql_base st input pos

(* ================================================================ *)
(* Numeric literal parsers                                           *)
(* ================================================================ *)

let is_digit_char (c: char) : bool =
  let code = int_of_char c in
  code >= 0x30 && code <= 0x39

(* Parse an integer literal: [+-]?[0-9]+ *)
(* Parse a numeric literal: integer, decimal, or double.
   Returns (lexical_form, datatype_iri). *)
let parse_numeric_literal (input: string) (pos: nat) : parse_result (string & wf_iri) =
  let len = String.length input in
  if pos >= len then ParseFail "expected numeric literal" pos
  else
    (* Consume optional sign *)
    let c0 = String.index input pos in
    let code0 = int_of_char c0 in
    let sign_str =
      if code0 = 0x2B then "+"
      else if code0 = 0x2D then "-"
      else ""
    in
    let dpos : nat =
      if code0 = 0x2B then pos + 1
      else if code0 = 0x2D then pos + 1
      else pos
    in
    (* Accumulate the numeric part: digits, dots, e/E *)
    let rec collect_num (p: nat) (acc: list char) (has_dot: bool) (has_e: bool) (fuel: nat)
      : Tot (parse_result (list char & bool & bool)) (decreases fuel) =
      if fuel = 0 then ParseOk (acc, has_dot, has_e) p
      else if p >= len then ParseOk (acc, has_dot, has_e) p
      else
        let ch = String.index input p in
        let cd = int_of_char ch in
        if is_digit_char ch then
          collect_num (p + 1) (ch :: acc) has_dot has_e (fuel - 1)
        else if cd = 0x2E && not has_dot && not has_e then
          (* Check: dot followed by digit means decimal, otherwise it's the statement terminator *)
          if p + 1 < len then
            let next = String.index input (p + 1) in
            if is_digit_char next then
              collect_num (p + 1) (ch :: acc) true has_e (fuel - 1)
            else
              (* Dot but no digit after => might be "123." which in Turtle is integer + dot terminator,
                 OR it could be a decimal like ".1" starting case. We include the dot as part of
                 the number since we already have digits before it. Actually for Turtle "123." is
                 ambiguous. Let's check: if we have digits accumulated, stop before the dot. *)
              ParseOk (acc, has_dot, has_e) p
          else
            (* Dot at end of input — don't consume it *)
            ParseOk (acc, has_dot, has_e) p
        else if (cd = 0x65 || cd = 0x45) && not has_e then  (* 'e' or 'E' *)
          (* Exponent part: optional sign + digits *)
          if p + 1 < len then
            let enext = String.index input (p + 1) in
            let ecode = int_of_char enext in
            if ecode = 0x2B || ecode = 0x2D then  (* sign after e *)
              collect_num (p + 2) (enext :: ch :: acc) has_dot true (fuel - 1)
            else if is_digit_char enext then
              collect_num (p + 1) (ch :: acc) has_dot true (fuel - 1)
            else
              ParseOk (acc, has_dot, has_e) p
          else
            ParseOk (acc, has_dot, has_e) p
        else
          ParseOk (acc, has_dot, has_e) p
    in
    (* Handle case where number starts with '.' (like .5) *)
    if dpos < len && int_of_char (String.index input dpos) = 0x2E then
      (* .DIGITS case => decimal *)
      if dpos + 1 < len && is_digit_char (String.index input (dpos + 1)) then
        let fuel = len - dpos in
        begin match collect_num (dpos + 1) [String.index input dpos] false true fuel with
        | ParseOk (acc, _, has_e) pos' ->
          let num_str = String.string_of_list (List.Tot.rev acc) in
          let lexical = String.concat "" [sign_str; num_str] in
          let dt = if has_e then xsd_double else xsd_decimal in
          ParseOk (lexical, dt) pos'
        | ParseFail msg fpos -> ParseFail msg fpos
        end
      else
        ParseFail "expected digit after '.'" dpos
    else if dpos <= len then
      let fuel = len - dpos in
      begin match collect_num dpos [] false false fuel with
      | ParseOk (acc, has_dot, has_e) pos' ->
        if List.Tot.length acc = 0 then
          ParseFail "expected numeric literal" pos
        else
          let num_str = String.string_of_list (List.Tot.rev acc) in
          let lexical = String.concat "" [sign_str; num_str] in
          let dt =
            if has_e then xsd_double
            else if has_dot then xsd_decimal
            else xsd_integer
          in
          ParseOk (lexical, dt) pos'
      | ParseFail msg fpos -> ParseFail msg fpos
      end
    else
      ParseFail "expected numeric literal" pos

(* ================================================================ *)
(* String literal parsers (single/double, short/long)                *)
(* ================================================================ *)

(* Parse long string body (triple-quoted): """...""" or '''...''' *)
let rec parse_long_string_body (qch: char) (input: string) (pos: nat) (acc: list char) (fuel: nat)
  : Tot (parse_result string) (decreases fuel) =
  if fuel = 0 then ParseFail "unterminated long string" pos
  else
    let len = String.length input in
    if pos >= len then ParseFail "unterminated long string" pos
    else
      let ch = String.index input pos in
      let code = int_of_char ch in
      if ch = qch then
        (* Check for triple quote ending *)
        if pos + 2 < len then
          let c1 = String.index input (pos + 1) in
          let c2 = String.index input (pos + 2) in
          if c1 = qch && c2 = qch then
            ParseOk (String.string_of_list (List.Tot.rev acc)) (pos + 3)
          else
            (* Single quote char — part of content *)
            parse_long_string_body qch input (pos + 1) (ch :: acc) (fuel - 1)
        else
          (* Not enough chars for triple quote — part of content *)
          parse_long_string_body qch input (pos + 1) (ch :: acc) (fuel - 1)
      else if code = 0x5C then  (* backslash — escape *)
        if pos + 1 >= len then ParseFail "backslash at end of long string" pos
        else
          let esc = String.index input (pos + 1) in
          let esc_code = int_of_char esc in
          if esc_code = 0x74 then
            parse_long_string_body qch input (pos + 2) (char_of_int 0x09 :: acc) (fuel - 1)
          else if esc_code = 0x6E then
            parse_long_string_body qch input (pos + 2) (char_of_int 0x0A :: acc) (fuel - 1)
          else if esc_code = 0x72 then
            parse_long_string_body qch input (pos + 2) (char_of_int 0x0D :: acc) (fuel - 1)
          else if esc_code = 0x5C then
            parse_long_string_body qch input (pos + 2) (char_of_int 0x5C :: acc) (fuel - 1)
          else if esc_code = 0x22 then
            parse_long_string_body qch input (pos + 2) (char_of_int 0x22 :: acc) (fuel - 1)
          else if esc_code = 0x27 then
            parse_long_string_body qch input (pos + 2) (char_of_int 0x27 :: acc) (fuel - 1)
          else if esc_code = 0x62 then
            parse_long_string_body qch input (pos + 2) (char_of_int 0x08 :: acc) (fuel - 1)
          else if esc_code = 0x66 then
            parse_long_string_body qch input (pos + 2) (char_of_int 0x0C :: acc) (fuel - 1)
          else if esc_code = 0x75 then  (* \uXXXX *)
            if pos + 6 > len then ParseFail "incomplete \\u escape" pos
            else
              let h0 = hex_val (String.index input (pos + 2)) in
              let h1 = hex_val (String.index input (pos + 3)) in
              let h2 = hex_val (String.index input (pos + 4)) in
              let h3 = hex_val (String.index input (pos + 5)) in
              let cp = ((h0 `op_Multiply` 4096) + (h1 `op_Multiply` 256) + (h2 `op_Multiply` 16) + h3) in
              if not (valid_codepoint cp) then ParseFail "surrogate codepoint in \\u escape" pos
              else
                parse_long_string_body qch input (pos + 6) (safe_char_of_int cp :: acc) (fuel - 1)
          else if esc_code = 0x55 then  (* \UXXXXXXXX *)
            if pos + 10 > len then ParseFail "incomplete \\U escape" pos
            else
              let h0 = hex_val (String.index input (pos + 2)) in
              let h1 = hex_val (String.index input (pos + 3)) in
              let h2 = hex_val (String.index input (pos + 4)) in
              let h3 = hex_val (String.index input (pos + 5)) in
              let h4 = hex_val (String.index input (pos + 6)) in
              let h5 = hex_val (String.index input (pos + 7)) in
              let h6 = hex_val (String.index input (pos + 8)) in
              let h7 = hex_val (String.index input (pos + 9)) in
              let cp = ((h0 `op_Multiply` 268435456) + (h1 `op_Multiply` 16777216) +
                        (h2 `op_Multiply` 1048576) + (h3 `op_Multiply` 65536) +
                        (h4 `op_Multiply` 4096) + (h5 `op_Multiply` 256) +
                        (h6 `op_Multiply` 16) + h7) in
              if not (valid_codepoint cp) then ParseFail "surrogate codepoint in \\U escape" pos
              else
                parse_long_string_body qch input (pos + 10) (safe_char_of_int cp :: acc) (fuel - 1)
          else
            ParseFail (String.concat "" ["invalid escape in long string: \\"; string_of_char esc]) pos
      else
        parse_long_string_body qch input (pos + 1) (ch :: acc) (fuel - 1)

(* Parse single-quoted string body (for 'short' strings) *)
let rec parse_single_string_body (input: string) (pos: nat) (acc: list char) (fuel: nat)
  : Tot (parse_result string) (decreases fuel) =
  if fuel = 0 then ParseFail "string too long" pos
  else
    let len = String.length input in
    if pos >= len then ParseFail "unterminated string literal" pos
    else
      let ch = String.index input pos in
      let code = int_of_char ch in
      if code = 0x27 then  (* single quote — end *)
        ParseOk (String.string_of_list (List.Tot.rev acc)) (pos + 1)
      else if code = 0x5C then  (* backslash *)
        if pos + 1 >= len then ParseFail "backslash at end of string" pos
        else
          let esc = String.index input (pos + 1) in
          let esc_code = int_of_char esc in
          if esc_code = 0x74 then
            parse_single_string_body input (pos + 2) (char_of_int 0x09 :: acc) (fuel - 1)
          else if esc_code = 0x6E then
            parse_single_string_body input (pos + 2) (char_of_int 0x0A :: acc) (fuel - 1)
          else if esc_code = 0x72 then
            parse_single_string_body input (pos + 2) (char_of_int 0x0D :: acc) (fuel - 1)
          else if esc_code = 0x5C then
            parse_single_string_body input (pos + 2) (char_of_int 0x5C :: acc) (fuel - 1)
          else if esc_code = 0x27 then
            parse_single_string_body input (pos + 2) (char_of_int 0x27 :: acc) (fuel - 1)
          else if esc_code = 0x22 then
            parse_single_string_body input (pos + 2) (char_of_int 0x22 :: acc) (fuel - 1)
          else if esc_code = 0x62 then
            parse_single_string_body input (pos + 2) (char_of_int 0x08 :: acc) (fuel - 1)
          else if esc_code = 0x66 then
            parse_single_string_body input (pos + 2) (char_of_int 0x0C :: acc) (fuel - 1)
          else if esc_code = 0x75 then
            if pos + 6 > len then ParseFail "incomplete \\u escape" pos
            else
              let h0 = hex_val (String.index input (pos + 2)) in
              let h1 = hex_val (String.index input (pos + 3)) in
              let h2 = hex_val (String.index input (pos + 4)) in
              let h3 = hex_val (String.index input (pos + 5)) in
              let cp = ((h0 `op_Multiply` 4096) + (h1 `op_Multiply` 256) + (h2 `op_Multiply` 16) + h3) in
              if not (valid_codepoint cp) then ParseFail "surrogate codepoint in \\u escape" pos
              else
                parse_single_string_body input (pos + 6) (safe_char_of_int cp :: acc) (fuel - 1)
          else if esc_code = 0x55 then
            if pos + 10 > len then ParseFail "incomplete \\U escape" pos
            else
              let h0 = hex_val (String.index input (pos + 2)) in
              let h1 = hex_val (String.index input (pos + 3)) in
              let h2 = hex_val (String.index input (pos + 4)) in
              let h3 = hex_val (String.index input (pos + 5)) in
              let h4 = hex_val (String.index input (pos + 6)) in
              let h5 = hex_val (String.index input (pos + 7)) in
              let h6 = hex_val (String.index input (pos + 8)) in
              let h7 = hex_val (String.index input (pos + 9)) in
              let cp = ((h0 `op_Multiply` 268435456) + (h1 `op_Multiply` 16777216) +
                        (h2 `op_Multiply` 1048576) + (h3 `op_Multiply` 65536) +
                        (h4 `op_Multiply` 4096) + (h5 `op_Multiply` 256) +
                        (h6 `op_Multiply` 16) + h7) in
              if not (valid_codepoint cp) then ParseFail "surrogate codepoint in \\U escape" pos
              else
                parse_single_string_body input (pos + 10) (safe_char_of_int cp :: acc) (fuel - 1)
          else
            ParseFail (String.concat "" ["invalid escape: \\"; string_of_char esc]) pos
      else if code = 0x0A || code = 0x0D then
        ParseFail "unescaped newline in short string literal" pos
      else
        parse_single_string_body input (pos + 1) (ch :: acc) (fuel - 1)

(* Parse a Turtle string literal: handles "", '', """""", '''''' variants *)
let parse_turtle_string (input: string) (pos: nat) : parse_result string =
  let len = String.length input in
  if pos >= len then ParseFail "expected string literal" pos
  else
    let c0 = String.index input pos in
    let code0 = int_of_char c0 in
    if code0 = 0x22 then  (* double quote *)
      (* Check for long string """.."""" *)
      if pos + 2 < len then
        let c1 = String.index input (pos + 1) in
        let c2 = String.index input (pos + 2) in
        if int_of_char c1 = 0x22 && int_of_char c2 = 0x22 then
          (* Long double-quoted string *)
          let fuel = len - pos in
          parse_long_string_body (char_of_int 0x22) input (pos + 3) [] fuel
        else
          (* Short double-quoted string — reuse N-Triples string parser *)
          parse_string_literal input pos
      else
        (* Too short for long — try short *)
        parse_string_literal input pos
    else if code0 = 0x27 then  (* single quote *)
      if pos + 2 < len then
        let c1 = String.index input (pos + 1) in
        let c2 = String.index input (pos + 2) in
        if int_of_char c1 = 0x27 && int_of_char c2 = 0x27 then
          (* Long single-quoted string *)
          let fuel = len - pos in
          parse_long_string_body (char_of_int 0x27) input (pos + 3) [] fuel
        else
          (* Short single-quoted string *)
          let fuel = len - pos in
          parse_single_string_body input (pos + 1) [] fuel
      else
        let fuel = len - pos in
        parse_single_string_body input (pos + 1) [] fuel
    else
      ParseFail "expected string literal" pos

(* ================================================================ *)
(* Turtle literal parser with language tag or datatype               *)
(* ================================================================ *)

let parse_turtle_literal (st: turtle_state) (input: string) (pos: nat) : parse_result literal =
  match parse_turtle_string input pos with
  | ParseOk lexical pos' ->
    let len = String.length input in
    if pos' >= len then
      ParseOk ({ lexical_form = lexical; datatype = xsd_string; lang_tag = None }) pos'
    else
      let next = String.index input pos' in
      let next_code = int_of_char next in
      if next_code = 0x40 then  (* '@' — language tag *)
        begin match parse_lang_tag input pos' with
        | ParseOk lang pos'' ->
          ParseOk ({ lexical_form = lexical; datatype = rdf_lang_string; lang_tag = Some lang }) pos''
        | ParseFail msg fpos -> ParseFail msg fpos
        end
      else if next_code = 0x5E then  (* '^' — might be '^^' datatype *)
        if pos' + 1 < len then
          let next2 = String.index input (pos' + 1) in
          if int_of_char next2 = 0x5E then
            (* '^^' followed by IRI or prefixed name *)
            begin match parse_turtle_iri st input (pos' + 2) with
            | ParseOk dt pos'' ->
              if is_iri dt then
                ParseOk ({ lexical_form = lexical; datatype = dt; lang_tag = None }) pos''
              else
                ParseFail "invalid datatype IRI" pos'
            | ParseFail msg fpos -> ParseFail msg fpos
            end
          else
            ParseOk ({ lexical_form = lexical; datatype = xsd_string; lang_tag = None }) pos'
        else
          ParseOk ({ lexical_form = lexical; datatype = xsd_string; lang_tag = None }) pos'
      else
        ParseOk ({ lexical_form = lexical; datatype = xsd_string; lang_tag = None }) pos'
  | ParseFail msg fpos -> ParseFail msg fpos

(* ================================================================ *)
(* Boolean literal parser                                            *)
(* ================================================================ *)

let parse_boolean_literal (input: string) (pos: nat) : parse_result literal =
  match pstring "true" input pos with
  | ParseOk _ pos' ->
    (* Make sure next char is not alphanumeric (not part of a longer token) *)
    let len = String.length input in
    if pos' < len && is_pn_chars (String.index input pos') then
      ParseFail "expected boolean literal" pos
    else
      ParseOk ({ lexical_form = "true"; datatype = xsd_boolean; lang_tag = None }) pos'
  | ParseFail _ _ ->
    begin match pstring "false" input pos with
    | ParseOk _ pos' ->
      let len = String.length input in
      if pos' < len && is_pn_chars (String.index input pos') then
        ParseFail "expected boolean literal" pos
      else
        ParseOk ({ lexical_form = "false"; datatype = xsd_boolean; lang_tag = None }) pos'
    | ParseFail _ _ -> ParseFail "expected boolean literal" pos
    end

(* ================================================================ *)
(* The 'a' keyword (shorthand for rdf:type)                          *)
(* ================================================================ *)

let rdf_type_iri : wf_iri =
  assert_norm (is_iri "http://www.w3.org/1999/02/22-rdf-syntax-ns#type");
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#type"

let parse_a_keyword (input: string) (pos: nat) : parse_result wf_iri =
  let len = String.length input in
  if pos >= len then ParseFail "expected 'a'" pos
  else
    let c = String.index input pos in
    if int_of_char c = 0x61 then  (* 'a' *)
      let next_pos = pos + 1 in
      (* Must be followed by whitespace or end to be a keyword, not part of a prefixed name *)
      if next_pos >= len then
        ParseOk rdf_type_iri next_pos
      else
        let nc = String.index input next_pos in
        if is_turtle_ws nc || int_of_char nc = 0x23 then  (* whitespace or comment *)
          ParseOk rdf_type_iri next_pos
        else
          ParseFail "expected 'a' keyword" pos
    else
      ParseFail "expected 'a'" pos

(* ================================================================ *)
(* RDF collection constants                                          *)
(* ================================================================ *)

let rdf_first_iri : wf_iri =
  assert_norm (is_iri "http://www.w3.org/1999/02/22-rdf-syntax-ns#first");
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#first"

let rdf_rest_iri : wf_iri =
  assert_norm (is_iri "http://www.w3.org/1999/02/22-rdf-syntax-ns#rest");
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#rest"

let rdf_nil_iri : wf_iri =
  assert_norm (is_iri "http://www.w3.org/1999/02/22-rdf-syntax-ns#nil");
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#nil"

(* ================================================================ *)
(* Forward declarations for mutually recursive parsers               *)
(* We use fuel-based recursion with explicit state threading.        *)
(* ================================================================ *)

(* Result type for object parsing: object term + generated triples + updated state *)
noeq type object_result = {
  or_term: rdf_term;
  or_triples: list triple;
  or_state: turtle_state;
}

(* Result type for subject parsing *)
noeq type subject_result = {
  sr_subject: subject;
  sr_triples: list triple;
  sr_state: turtle_state;
}

(* ================================================================ *)
(* Main recursive Turtle parser — all productions in one mutual      *)
(* recursion block using fuel for termination.                       *)
(* ================================================================ *)

(* Parse a Turtle object: IRI, blank node, literal, boolean, numeric,
   anonymous blank node [], blank node property list [p o; ...],
   or collection (...) *)
let rec parse_turtle_object (st: turtle_state) (input: string) (pos: nat) (fuel: nat)
  : Tot (parse_result object_result) (decreases fuel) =
  if fuel = 0 then ParseFail "recursion limit" pos
  else
    let len = String.length input in
    if pos >= len then ParseFail "expected object" pos
    else
      let c = String.index input pos in
      let code = int_of_char c in
      if code = 0x3C then  (* '<' — full IRI *)
        begin match parse_turtle_iri st input pos with
        | ParseOk i pos' ->
          if is_iri i then
            ParseOk ({ or_term = T_IRI i; or_triples = []; or_state = st }) pos'
          else ParseFail "invalid IRI" pos
        | ParseFail msg fpos -> ParseFail msg fpos
        end
      else if code = 0x5F then  (* '_' — blank node *)
        begin match parse_bnode input pos with
        | ParseOk b pos' -> ParseOk ({ or_term = T_BNode b; or_triples = []; or_state = st }) pos'
        | ParseFail msg fpos -> ParseFail msg fpos
        end
      else if code = 0x22 || code = 0x27 then  (* '"' or '\'' — string literal *)
        begin match parse_turtle_literal st input pos with
        | ParseOk lit pos' ->
          if literal_wf lit then
            ParseOk ({ or_term = T_Literal lit; or_triples = []; or_state = st }) pos'
          else ParseFail "invalid literal" pos
        | ParseFail msg fpos -> ParseFail msg fpos
        end
      else if code = 0x5B then  (* '[' — anonymous blank node or blank node property list *)
        let (bnode_id, st1) = fresh_bnode st in
        (* Skip '[' *)
        begin match turtle_ws input (pos + 1) with
        | ParseOk () pos2 ->
          if pos2 < len && int_of_char (String.index input pos2) = 0x5D then
            (* [] — empty anonymous blank node *)
            ParseOk ({ or_term = T_BNode bnode_id; or_triples = []; or_state = st1 }) (pos2 + 1)
          else
            (* [ predicate-object-list ] *)
            begin match parse_predicate_object_list st1 (S_BNode bnode_id) input pos2 (fuel - 1) with
            | ParseOk (triples, st2) pos3 ->
              begin match turtle_ws input pos3 with
              | ParseOk () pos4 ->
                if pos4 < len && int_of_char (String.index input pos4) = 0x5D then
                  ParseOk ({ or_term = T_BNode bnode_id; or_triples = triples; or_state = st2 }) (pos4 + 1)
                else
                  ParseFail "expected ']'" pos4
              end
            | ParseFail msg fpos -> ParseFail msg fpos
            end
        end
      else if code = 0x28 then  (* '(' — collection *)
        parse_collection st input (pos + 1) (fuel - 1)
      else
        (* Try boolean *)
        begin match parse_boolean_literal input pos with
        | ParseOk lit pos' -> ParseOk ({ or_term = T_Literal lit; or_triples = []; or_state = st }) pos'
        | ParseFail _ _ ->
          (* Try numeric literal *)
          begin match parse_numeric_literal input pos with
          | ParseOk (lexical, dt) pos' ->
            let lit : literal = { lexical_form = lexical; datatype = dt; lang_tag = None } in
            if literal_wf lit then
              ParseOk ({ or_term = T_Literal lit; or_triples = []; or_state = st }) pos'
            else
              ParseFail "invalid numeric literal" pos
          | ParseFail _ _ ->
            (* Try prefixed name *)
            begin match parse_prefixed_name input pos with
            | ParseOk (prefix, local) pos' ->
              begin match resolve_prefixed_name st prefix local with
              | Some resolved ->
                if is_iri resolved then
                  ParseOk ({ or_term = T_IRI resolved; or_triples = []; or_state = st }) pos'
                else ParseFail "invalid resolved IRI" pos
              | None -> ParseFail (String.concat "" ["undefined prefix: "; prefix]) pos
              end
            | ParseFail _ _ -> ParseFail "expected object" pos
            end
          end
        end

(* Parse an RDF collection: ( item1 item2 ... ) *)
and parse_collection (st: turtle_state) (input: string) (pos: nat) (fuel: nat)
  : Tot (parse_result object_result) (decreases fuel) =
  if fuel = 0 then ParseFail "recursion limit in collection" pos
  else
    let len = String.length input in
    match turtle_ws input pos with
    | ParseOk () pos1 ->
      if pos1 >= len then ParseFail "unterminated collection" pos1
      else if int_of_char (String.index input pos1) = 0x29 then  (* ')' — empty collection *)
        ParseOk ({ or_term = T_IRI rdf_nil_iri; or_triples = []; or_state = st }) (pos1 + 1)
      else
        (* Parse first item *)
        begin match parse_turtle_object st input pos1 (fuel - 1) with
        | ParseOk first_obj pos2 ->
          let (node_id, st2) = fresh_bnode first_obj.or_state in
          let node_subj = S_BNode node_id in
          let first_triple : triple = { s = node_subj; p = rdf_first_iri; o = first_obj.or_term } in
          (* Parse remaining items *)
          begin match parse_collection_rest st2 node_subj input pos2 (fuel - 1) with
          | ParseOk (rest_triples, rest_term, st3) pos3 ->
            let rest_triple : triple = { s = node_subj; p = rdf_rest_iri; o = rest_term } in
            let all_triples = first_obj.or_triples @ [first_triple; rest_triple] @ rest_triples in
            ParseOk ({ or_term = T_BNode node_id; or_triples = all_triples; or_state = st3 }) pos3
          | ParseFail msg fpos -> ParseFail msg fpos
          end
        | ParseFail msg fpos -> ParseFail msg fpos
        end

(* Parse remaining collection items after the first *)
and parse_collection_rest (st: turtle_state) (prev_subj: subject) (input: string) (pos: nat) (fuel: nat)
  : Tot (parse_result (list triple & rdf_term & turtle_state)) (decreases fuel) =
  if fuel = 0 then ParseFail "recursion limit in collection rest" pos
  else
    let len = String.length input in
    match turtle_ws input pos with
    | ParseOk () pos1 ->
      if pos1 >= len then ParseFail "unterminated collection" pos1
      else if int_of_char (String.index input pos1) = 0x29 then  (* ')' — end *)
        ParseOk ([], T_IRI rdf_nil_iri, st) (pos1 + 1)
      else
        (* Parse next item *)
        begin match parse_turtle_object st input pos1 (fuel - 1) with
        | ParseOk next_obj pos2 ->
          let (node_id, st2) = fresh_bnode next_obj.or_state in
          let node_subj = S_BNode node_id in
          let first_triple : triple = { s = node_subj; p = rdf_first_iri; o = next_obj.or_term } in
          begin match parse_collection_rest st2 node_subj input pos2 (fuel - 1) with
          | ParseOk (rest_triples, rest_term, st3) pos3 ->
            let rest_triple : triple = { s = node_subj; p = rdf_rest_iri; o = rest_term } in
            let all_triples = next_obj.or_triples @ [first_triple; rest_triple] @ rest_triples in
            ParseOk (all_triples, T_BNode node_id, st3) pos3
          | ParseFail msg fpos -> ParseFail msg fpos
          end
        | ParseFail msg fpos -> ParseFail msg fpos
        end

(* Parse object list: object (',' object)* *)
and parse_object_list (st: turtle_state) (subj: subject) (pred: wf_iri) (input: string) (pos: nat) (fuel: nat)
  : Tot (parse_result (list triple & turtle_state)) (decreases fuel) =
  if fuel = 0 then ParseFail "recursion limit in object list" pos
  else
    begin match parse_turtle_object st input pos (fuel - 1) with
    | ParseOk obj_res pos1 ->
      let t : triple = { s = subj; p = pred; o = obj_res.or_term } in
      let triples1 = obj_res.or_triples @ [t] in
      (* Check for comma *)
      begin match turtle_ws input pos1 with
      | ParseOk () pos2 ->
        let len = String.length input in
        if pos2 < len && int_of_char (String.index input pos2) = 0x2C then
          (* More objects *)
          begin match turtle_ws input (pos2 + 1) with
          | ParseOk () pos3 ->
            begin match parse_object_list obj_res.or_state subj pred input pos3 (fuel - 1) with
            | ParseOk (more_triples, st2) pos4 ->
              ParseOk (triples1 @ more_triples, st2) pos4
            | ParseFail msg fpos -> ParseFail msg fpos
            end
          end
        else
          ParseOk (triples1, obj_res.or_state) pos2
      end
    | ParseFail msg fpos -> ParseFail msg fpos
    end

(* Parse a predicate: IRI, prefixed name, or 'a' keyword *)
and parse_turtle_predicate (st: turtle_state) (input: string) (pos: nat) (fuel: nat)
  : Tot (parse_result wf_iri) (decreases fuel) =
  if fuel = 0 then ParseFail "recursion limit" pos
  else
    (* Try 'a' keyword first *)
    match parse_a_keyword input pos with
    | ParseOk iri_val pos' -> ParseOk iri_val pos'
    | ParseFail _ _ ->
      begin match parse_turtle_iri st input pos with
      | ParseOk i pos' ->
        if is_iri i then ParseOk i pos'
        else ParseFail "invalid predicate IRI" pos
      | ParseFail msg fpos -> ParseFail msg fpos
      end

(* Parse predicate-object list: predicate objectList (';' predicate objectList)* ';'? *)
and parse_predicate_object_list (st: turtle_state) (subj: subject) (input: string) (pos: nat) (fuel: nat)
  : Tot (parse_result (list triple & turtle_state)) (decreases fuel) =
  if fuel = 0 then ParseFail "recursion limit in predicate-object list" pos
  else
    begin match parse_turtle_predicate st input pos (fuel - 1) with
    | ParseOk pred pos1 ->
      begin match turtle_ws input pos1 with
      | ParseOk () pos2 ->
        begin match parse_object_list st subj pred input pos2 (fuel - 1) with
        | ParseOk (triples1, st1) pos3 ->
          (* Check for semicolon *)
          begin match turtle_ws input pos3 with
          | ParseOk () pos4 ->
            let len = String.length input in
            if pos4 < len && int_of_char (String.index input pos4) = 0x3B then
              (* Skip semicolon and whitespace *)
              begin match turtle_ws input (pos4 + 1) with
              | ParseOk () pos5 ->
                (* Check if there's another predicate or just trailing semicolons *)
                if pos5 >= len then
                  ParseOk (triples1, st1) pos5
                else
                  let nc = String.index input pos5 in
                  let ncode = int_of_char nc in
                  if ncode = 0x2E || ncode = 0x5D || ncode = 0x3B then
                    (* End of predicate-object list (dot, close bracket, or another semicolon) *)
                    if ncode = 0x3B then
                      (* Skip additional trailing semicolons *)
                      parse_trailing_semicolons st1 triples1 subj input pos5 (fuel - 1)
                    else
                      ParseOk (triples1, st1) pos5
                  else
                    (* Another predicate-object pair *)
                    begin match parse_predicate_object_list st1 subj input pos5 (fuel - 1) with
                    | ParseOk (more_triples, st2) pos6 ->
                      ParseOk (triples1 @ more_triples, st2) pos6
                    | ParseFail msg fpos -> ParseFail msg fpos
                    end
              end
            else
              ParseOk (triples1, st1) pos4
          end
        | ParseFail msg fpos -> ParseFail msg fpos
        end
      end
    | ParseFail msg fpos -> ParseFail msg fpos
    end

(* Skip trailing semicolons: ; ; ; before . or ] *)
and parse_trailing_semicolons (st: turtle_state) (triples: list triple) (subj: subject)
    (input: string) (pos: nat) (fuel: nat)
  : Tot (parse_result (list triple & turtle_state)) (decreases fuel) =
  if fuel = 0 then ParseOk (triples, st) pos
  else
    let len = String.length input in
    if pos >= len then ParseOk (triples, st) pos
    else
      let c = String.index input pos in
      if int_of_char c = 0x3B then
        begin match turtle_ws input (pos + 1) with
        | ParseOk () pos2 ->
          if pos2 >= len then ParseOk (triples, st) pos2
          else
            let nc = String.index input pos2 in
            let ncode = int_of_char nc in
            if ncode = 0x2E || ncode = 0x5D || ncode = 0x3B then
              parse_trailing_semicolons st triples subj input pos2 (fuel - 1)
            else
              (* Another predicate-object pair after semicolons *)
              begin match parse_predicate_object_list st subj input pos2 (fuel - 1) with
              | ParseOk (more_triples, st2) pos3 ->
                ParseOk (triples @ more_triples, st2) pos3
              | ParseFail msg fpos -> ParseFail msg fpos
              end
        end
      else
        ParseOk (triples, st) pos

(* Parse a Turtle subject: IRI, blank node, prefixed name, anonymous [], or collection () *)
let parse_turtle_subject (st: turtle_state) (input: string) (pos: nat) (fuel: nat)
  : Tot (parse_result subject_result) (decreases fuel) =
  if fuel = 0 then ParseFail "recursion limit" pos
  else
    let len = String.length input in
    if pos >= len then ParseFail "expected subject" pos
    else
      let c = String.index input pos in
      let code = int_of_char c in
      if code = 0x3C then  (* '<' — full IRI *)
        begin match parse_turtle_iri st input pos with
        | ParseOk i pos' ->
          if is_iri i then
            ParseOk ({ sr_subject = S_IRI i; sr_triples = []; sr_state = st }) pos'
          else ParseFail "invalid subject IRI" pos
        | ParseFail msg fpos -> ParseFail msg fpos
        end
      else if code = 0x5F then  (* '_' — labeled blank node *)
        begin match parse_bnode input pos with
        | ParseOk b pos' -> ParseOk ({ sr_subject = S_BNode b; sr_triples = []; sr_state = st }) pos'
        | ParseFail msg fpos -> ParseFail msg fpos
        end
      else if code = 0x5B then  (* '[' — anonymous blank node or property list *)
        let (bnode_id, st1) = fresh_bnode st in
        begin match turtle_ws input (pos + 1) with
        | ParseOk () pos2 ->
          if pos2 < len && int_of_char (String.index input pos2) = 0x5D then
            (* [] — empty anonymous blank node *)
            ParseOk ({ sr_subject = S_BNode bnode_id; sr_triples = []; sr_state = st1 }) (pos2 + 1)
          else
            (* [ predicate-object-list ] *)
            begin match parse_predicate_object_list st1 (S_BNode bnode_id) input pos2 (fuel - 1) with
            | ParseOk (triples, st2) pos3 ->
              begin match turtle_ws input pos3 with
              | ParseOk () pos4 ->
                if pos4 < len && int_of_char (String.index input pos4) = 0x5D then
                  ParseOk ({ sr_subject = S_BNode bnode_id; sr_triples = triples; sr_state = st2 }) (pos4 + 1)
                else
                  ParseFail "expected ']'" pos4
              end
            | ParseFail msg fpos -> ParseFail msg fpos
            end
        end
      else if code = 0x28 then  (* '(' — collection as subject *)
        begin match parse_collection st input (pos + 1) (fuel - 1) with
        | ParseOk obj_res pos' ->
          begin match obj_res.or_term with
          | T_IRI i ->
            ParseOk ({ sr_subject = S_IRI i; sr_triples = obj_res.or_triples; sr_state = obj_res.or_state }) pos'
          | T_BNode b ->
            ParseOk ({ sr_subject = S_BNode b; sr_triples = obj_res.or_triples; sr_state = obj_res.or_state }) pos'
          | _ -> ParseFail "collection did not produce a valid subject" pos
          end
        | ParseFail msg fpos -> ParseFail msg fpos
        end
      else
        (* Try prefixed name *)
        begin match parse_prefixed_name input pos with
        | ParseOk (prefix, local) pos' ->
          begin match resolve_prefixed_name st prefix local with
          | Some resolved ->
            if is_iri resolved then
              ParseOk ({ sr_subject = S_IRI resolved; sr_triples = []; sr_state = st }) pos'
            else ParseFail "invalid resolved IRI" pos
          | None -> ParseFail (String.concat "" ["undefined prefix: "; prefix]) pos
          end
        | ParseFail _ _ -> ParseFail "expected subject" pos
        end

(* ================================================================ *)
(* Top-level Turtle document parser                                  *)
(* ================================================================ *)

(* Parse a single Turtle statement: directive or triples statement *)
let parse_turtle_statement (st: turtle_state) (input: string) (pos: nat) (fuel: nat)
  : Tot (parse_result (list triple & turtle_state)) (decreases fuel) =
  if fuel = 0 then ParseFail "recursion limit" pos
  else
    let len = String.length input in
    match turtle_ws input pos with
    | ParseOk () pos1 ->
      if pos1 >= len then ParseOk ([], st) pos1
      else
        (* Try prefix directive *)
        begin match parse_prefix_directive st input pos1 with
        | ParseOk (prefix, iri_val) pos2 ->
          let new_prefixes = (prefix, iri_val) :: st.prefixes in
          ParseOk ([], { st with prefixes = new_prefixes }) pos2
        | ParseFail _ _ ->
          // Try base directive
          begin match parse_base_directive st input pos1 with
          | ParseOk base_val pos2 ->
            ParseOk ([], { st with base_iri = base_val }) pos2
          | ParseFail _ _ ->
            (* Must be a triples statement *)
            begin match parse_turtle_subject st input pos1 fuel with
            | ParseOk subj_res pos2 ->
              begin match turtle_ws input pos2 with
              | ParseOk () pos3 ->
                (* Check if subject has property list (blank node property list as subject
                   can be followed by just '.') *)
                if pos3 >= len then
                  (* Only subject triples, no predicate-object list *)
                  if List.Tot.length subj_res.sr_triples > 0 then
                    ParseOk (subj_res.sr_triples, subj_res.sr_state) pos3
                  else
                    ParseFail "expected predicate after subject" pos3
                else
                  let nc = String.index input pos3 in
                  let ncode = int_of_char nc in
                  if ncode = 0x2E then
                    // Subject followed directly by dot -- valid only if subject generated triples
                    if List.Tot.length subj_res.sr_triples > 0 then
                      ParseOk (subj_res.sr_triples, subj_res.sr_state) (pos3 + 1)
                    else
                      ParseFail "expected predicate after subject" pos3
                  else if ncode = 0x7D && List.Tot.length subj_res.sr_triples > 0 then
                    // Inside a TriG graph block: '}' ends the block.
                    // Blank node property list as sole statement is valid without dot.
                    ParseOk (subj_res.sr_triples, subj_res.sr_state) pos3
                  else
                    begin match parse_predicate_object_list subj_res.sr_state subj_res.sr_subject input pos3 (fuel - 1) with
                    | ParseOk (po_triples, st2) pos4 ->
                      let all_triples = subj_res.sr_triples @ po_triples in
                      // Expect '.'
                      begin match turtle_ws input pos4 with
                      | ParseOk () pos5 ->
                        if pos5 < len && int_of_char (String.index input pos5) = 0x2E then
                          ParseOk (all_triples, st2) (pos5 + 1)
                        else if pos5 < len && int_of_char (String.index input pos5) = 0x7D then
                          // '}' ends a TriG block — accept without dot
                          ParseOk (all_triples, st2) pos5
                        else
                          // Missing dot — fail (strict per Turtle spec)
                          ParseFail "expected '.' after triple" pos5
                      end
                    | ParseFail msg fpos -> ParseFail msg fpos
                    end
              end
            | ParseFail msg fpos -> ParseFail msg fpos
            end
          end
        end

// Parse result with error tracking
noeq type turtle_doc_result = {
  tdr_triples: list triple;
  tdr_state: turtle_state;
  tdr_has_error: bool;
}

// Parse the full Turtle document: sequence of statements
let rec parse_turtle_doc (st: turtle_state) (input: string) (pos: nat)
    (acc: list triple) (has_error: bool) (fuel: nat)
  : Tot turtle_doc_result (decreases fuel) =
  if fuel = 0 then { tdr_triples = List.Tot.rev acc; tdr_state = st; tdr_has_error = has_error }
  else
    let len = String.length input in
    match turtle_ws input pos with
    | ParseOk () pos1 ->
      if pos1 >= len then { tdr_triples = List.Tot.rev acc; tdr_state = st; tdr_has_error = has_error }
      else
        begin match parse_turtle_statement st input pos1 fuel with
        | ParseOk (triples, st') pos2 ->
          if pos2 = pos1 then
            // No progress -- stop
            { tdr_triples = List.Tot.rev ((List.Tot.rev triples) @ acc);
              tdr_state = st'; tdr_has_error = has_error }
          else
            parse_turtle_doc st' input pos2 ((List.Tot.rev triples) @ acc) has_error (fuel - 1)
        | ParseFail _ _ ->
          // Skip to next line on failure, mark error
          let pos2 = skip_to_eol input pos1 (len - pos1) in
          if pos2 = pos1 then
            { tdr_triples = List.Tot.rev acc; tdr_state = st; tdr_has_error = true }
          else
            parse_turtle_doc st input pos2 acc true (fuel - 1)
        end

(* ================================================================ *)
(* Entry point                                                       *)
(* ================================================================ *)

// Lenient: always returns triples (for positive tests, compatibility)
let parse_turtle (input: string) : list triple =
  let len = String.length input in
  let fuel = (len + 1) `op_Multiply` 2 in
  let r = parse_turtle_doc empty_turtle_state input 0 [] false fuel in
  r.tdr_triples

let parse_turtle_with_base (input: string) (base: string) : list triple =
  let len = String.length input in
  let fuel = (len + 1) `op_Multiply` 2 in
  let st = { empty_turtle_state with base_iri = base } in
  let r = parse_turtle_doc st input 0 [] false fuel in
  r.tdr_triples

// Strict: returns None if any parse errors were encountered
let parse_turtle_strict (input: string) : option (list triple) =
  let len = String.length input in
  let fuel = (len + 1) `op_Multiply` 2 in
  let r = parse_turtle_doc empty_turtle_state input 0 [] false fuel in
  if r.tdr_has_error then None else Some r.tdr_triples

let parse_turtle_with_base_strict (input: string) (base: string) : option (list triple) =
  let len = String.length input in
  let fuel = (len + 1) `op_Multiply` 2 in
  let st = { empty_turtle_state with base_iri = base } in
  let r = parse_turtle_doc st input 0 [] false fuel in
  if r.tdr_has_error then None else Some r.tdr_triples
