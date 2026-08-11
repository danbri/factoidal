module Parser.XML

open FStar.String
open FStar.List.Tot
open FStar.Char
open Parser.FastString
open Parser.Combinators

// Issue #89: byte-indexed primitives on the parser hot path.
// XML is ASCII-delimited (tags, attributes, declarations) so byte
// semantics are safe. See Parser.FastString.fst.

(* ================================================================ *)
(* XML AST                                                           *)
(* ================================================================ *)

type xml_attribute = { attr_name: string; attr_value: string }

type xml_node =
  | XText : text:string -> xml_node
  | XElement : tag:string -> attrs:list xml_attribute -> children:list xml_node -> xml_node
  | XComment : text:string -> xml_node
  | XCDATA : text:string -> xml_node
  // Processing instruction (XML 1.0 §2.6): `<?target data?>`. Retained
  // in the tree (rather than skipped) so XPath's processing-instruction()
  // node test and XSLT/Schematron can see it. `data` excludes the target
  // and the single run of whitespace separating it from the target, per
  // the DOM/XPath string-value convention.
  | XPI : target:string -> data:string -> xml_node


(* ================================================================ *)
(* Character classification helpers                                  *)
(* ================================================================ *)

let is_name_start_char (c:char) : bool =
  let code = Char.int_of_char c in
  if code < 0x80 then
    (code >= 0x41 && code <= 0x5A) ||
    (code >= 0x61 && code <= 0x7A) ||
    code = 0x5F || code = 0x3A
  else
    code >= 0xC0

// Flattened: single function, ASCII fast-path.
//
// The non-ASCII arm accepts a UTF-8 LEAD byte and nothing else. That is
// deliberate and it is not the whole Name-body test: a byte-level
// predicate cannot decide a multi-byte codepoint, so the Name BODY scan
// (scan_name_body_end below, issue #325) walks codepoints and consults
// is_name_char_cp instead. This function survives for the ASCII rules it
// states clearly, and its non-ASCII arm is kept identical to what it
// always was so nothing silently shifts.
let is_name_char (c:char) : bool =
  let code = Char.int_of_char c in
  if code < 0x80 then
    (code >= 0x41 && code <= 0x5A) ||
    (code >= 0x61 && code <= 0x7A) ||
    (code >= 0x30 && code <= 0x39) ||
    code = 0x5F || code = 0x3A ||
    code = 0x2D || code = 0x2E
  else
    code >= 0xC0 || code = 0xB7

let is_xml_space (c:char) : bool =
  let code = Char.int_of_char c in
  code = 0x20 || code = 0x09 || code = 0x0A || code = 0x0D

// ASCII-only lowercase helper -- used only for the reserved "xml" PI
// target-name case-insensitive comparison (issue: xmlconf's PI target
// casing cluster). Never used on Name/content chars generally.
let to_lower_ascii (c:char) : char =
  let code = Char.int_of_char c in
  if code >= 0x41 && code <= 0x5A then Char.char_of_int (code + 0x20) else c


(* ================================================================ *)
(* XML Char production (§2.2) -- non-character codepoint rejection   *)
(*                                                                   *)
(* Char ::= #x9 | #xA | #xD | [#x20-#xD7FF] | [#xE000-#xFFFD] |      *)
(*          [#x10000-#x10FFFF]                                      *)
(* Excludes #x0-#x8, #xB, #xC, #xE-#x1F, #xD800-#xDFFF (surrogates), *)
(* #xFFFE, #xFFFF. Applied at both raw-content sites (text, comment, *)
(* CDATA, attribute values, PI bodies) and character-reference       *)
(* resolution (parse_reference), decoded via Parser.FastString's     *)
(* fs_cp_at so multi-byte UTF-8 sequences are checked by codepoint,  *)
(* not by byte. See xmlconf fail-cluster "non-character codepoints". *)
(* ================================================================ *)

let is_valid_xml_char (cp:int) : bool =
  cp = 0x9 || cp = 0xA || cp = 0xD ||
  (cp >= 0x20 && cp <= 0xD7FF) ||
  (cp >= 0xE000 && cp <= 0xFFFD) ||
  (cp >= 0x10000 && cp <= 0x10FFFF)

// fs_cp_at's documented fallback for a byte sequence that is NOT
// valid UTF-8 at this position (a misaligned continuation byte, an
// overlong encoding, a surrogate D800-DFFF encoded via a technically
// well-shaped 3-byte sequence, or a codepoint above 0x10FFFF via a
// well-shaped 4-byte sequence) is to report the replacement
// codepoint 0xFFFD with adv = 1 -- and 0xFFFD is itself a legal XML
// Char, so `is_valid_xml_char` alone can't tell "this really is a
// correctly-encoded U+FFFD" (which decodes with adv = 3, its true
// UTF-8 byte length) apart from "the bytes here aren't valid UTF-8 at
// all" (always adv = 1, and no legitimate 1-byte encoding can ever
// decode to a value >= 0x80). XML requires the document to BE valid
// Unicode text, so the latter must reject -- not-wf-sa-168/169/170
// (surrogates and a 4-byte UCS-4 encoding smuggled in as technically
// well-formed UTF-8 shapes).
let is_valid_decoded_char (cp:int) (adv:nat) : bool =
  if cp = 0xFFFD && adv = 1 then false
  else is_valid_xml_char cp

// A UTF-8 continuation byte (10xxxxxx). Byte-stepping validators
// (parse_comment_body / parse_cdata_body / skip_pi_body, which
// advance one byte per recursive call rather than one codepoint) must
// NOT re-run fs_cp_at/is_valid_decoded_char on a continuation byte:
// probed in isolation it looks like "not valid UTF-8 here" (the same
// (0xFFFD, 1) sentinel a truly invalid byte produces) even when it is
// the tail of a perfectly valid multi-byte sequence whose LEAD byte
// was already checked on the previous step. Skipping continuation
// bytes here is safe precisely because the preceding lead-byte step
// already validated the whole sequence.
let is_utf8_continuation_byte (c:char) : bool =
  let code = Char.int_of_char c in
  code >= 0x80 && code <= 0xBF

// Scan [pos, limit) as a sequence of UTF-8 codepoints (fs_cp_at),
// rejecting if any decoded codepoint fails is_valid_xml_char. A
// continuation byte misread as a lead byte decodes to the standalone
// replacement codepoint 0xFFFD (see fs_cp_at's documented fallback),
// which IS a valid Char, so this never false-rejects legitimate
// multi-byte sequences -- the true offending lead byte is always
// scanned in order and catches the failure first.
let rec scan_chars_valid (input:string) (pos:nat) (limit:nat) (fuel:nat)
  : Tot bool (decreases fuel) =
  if fuel = 0 then true
  else if pos >= limit then true
  else
    let (cp, adv) = fs_cp_at input pos in
    let adv' = if adv = 0 then 1 else adv in
    if is_valid_decoded_char cp adv' then scan_chars_valid input (pos + adv') limit (fuel - 1)
    else false

// Byte-wise scan for a literal "--" anywhere in [0, limit) of a
// (already-decoded) comment-body string -- XML 1.0 §2.5 forbids "--"
// inside a comment other than as the closing delimiter.
let rec bytes_have_double_dash (s:string) (pos:nat) (limit:nat) (fuel:nat)
  : Tot bool (decreases fuel) =
  if fuel = 0 then false
  else if pos + 1 >= limit then false
  else
    let c0 = fs_byte_index s pos in
    let c1 = fs_byte_index s (pos + 1) in
    if c0 = '-' && c1 = '-' then true
    else bytes_have_double_dash s (pos + 1) limit (fuel - 1)

let ends_with_dash (s:string) : bool =
  let len = fs_byte_length s in
  len > 0 && fs_byte_index s (len - 1) = '-'

// Byte-wise scan for the literal "]]>" CDATA-section-close delimiter
// inside a run of raw character data -- XML 1.0 §2.4 forbids it in
// ordinary content (only legal as an actual CDATA section's own
// closer). Scanned on the untouched input bytes of the run, before
// any entity decoding, which is correct here: every failing xmlconf
// case embeds the literal 3-byte sequence directly, with no
// intervening reference.
let rec bytes_have_cdata_close (input:string) (pos:nat) (limit:nat) (fuel:nat)
  : Tot bool (decreases fuel) =
  if fuel = 0 then false
  else if pos + 2 >= limit then false
  else
    if fs_byte_index input pos = ']' &&
       fs_byte_index input (pos + 1) = ']' &&
       fs_byte_index input (pos + 2) = '>'
    then true
    else bytes_have_cdata_close input (pos + 1) limit (fuel - 1)

// The reserved PI target name "xml" (any case combination) is not a
// legal generic processing-instruction target anywhere -- only the
// dedicated parse_xml_declaration (exact lowercase, document-initial
// position) may consume it. xmlconf's PI-target-casing cluster
// (`<?xmL ...?>`, `<?xMl ...?>`) and the "XML declaration may not
// follow document content / be within element content" cases both
// reduce to this one check, since a plain PI walk is what encounters
// those tokens outside the document-initial position.
let is_xml_target_name_ci (s:string) : bool =
  fs_byte_length s = 3 &&
  to_lower_ascii (fs_byte_index s 0) = 'x' &&
  to_lower_ascii (fs_byte_index s 1) = 'm' &&
  to_lower_ascii (fs_byte_index s 2) = 'l'


(* ================================================================ *)
(* XML Name parser                                                   *)
(* ================================================================ *)

// NameStartChar / NameChar above ASCII, at CODEPOINT level (issue #325).
//
// These are the XML 1.1 NameStartChar and NameChar productions
// (https://www.w3.org/TR/xml11/#NT-NameStartChar). The ranges are
// deliberately the SAME table as XML.Wellformedness.is_name_start_char /
// is_name_char, minus that module's exclusion of ':' — Parser.XML is a
// non-namespace XML 1.0 parser, so ':' is an ordinary Name character
// here, and the ASCII arm below keeps it. The table is duplicated rather
// than imported because XML.Wellformedness sits ABOVE Parser.XML in the
// link order (see bin/xml-runner/README.md's build recipe and
// build-ocaml.sh's COMMON_MODULES) and inverting that to share one
// definition is a bigger change than this fix should carry. Hoisting the
// table into its own leaf module is the right cleanup; it is not this
// commit's job. If you edit one copy, edit both.
//
// Getting this class right is what the whole fix turns on. Three
// attempts, measured on xmlconf each time:
//   1. byte test `code >= 0xC0` (the original) — rejects UTF-8
//      CONTINUATION bytes, so a Name scan stops INSIDE the first
//      non-ASCII codepoint. 1428 pass, 0 fail, but <ex:日本語 …> does
//      not parse and its whole document is silently dropped.
//   2. byte test widened to accept every byte >= 0x80 — makes any stray
//      high byte a legal Name character. 1330 pass, 4 fail: 98 lost
//      passes and 4 not-wf documents wrongly accepted.
//   3. codepoint test, "any non-ASCII codepoint" — still far too wide,
//      because plenty of non-ASCII codepoints are legitimately NOT
//      NameChars and xmlconf tests exactly that. 1346 pass, 4 fail.
//   4. this: the actual XML NameChar codepoint table.
let is_name_start_char_nonascii_cp (cp:int) : bool =
  (cp >= 0xC0    && cp <= 0xD6)   ||
  (cp >= 0xD8    && cp <= 0xF6)   ||
  (cp >= 0xF8    && cp <= 0x2FF)  ||
  (cp >= 0x370   && cp <= 0x37D)  ||
  (cp >= 0x37F   && cp <= 0x1FFF) ||
  (cp >= 0x200C  && cp <= 0x200D) ||
  (cp >= 0x2070  && cp <= 0x218F) ||
  (cp >= 0x2C00  && cp <= 0x2FEF) ||
  (cp >= 0x3001  && cp <= 0xD7FF) ||
  (cp >= 0xF900  && cp <= 0xFDCF) ||
  (cp >= 0xFDF0  && cp <= 0xFFFD) ||
  (cp >= 0x10000 && cp <= 0xEFFFF)

let is_name_char_nonascii_cp (cp:int) : bool =
  is_name_start_char_nonascii_cp cp ||
  cp = 0xB7                         ||   // middle dot (Extender)
  (cp >= 0x0300 && cp <= 0x036F)    ||   // combining marks
  (cp >= 0x203F && cp <= 0x2040)

// `adv` — the byte length fs_cp_at consumed — is load-bearing, not
// decoration. fs_cp_at reports invalid UTF-8 at `pos` as (0xFFFD, 1), and
// no legitimate one-byte encoding can ever decode to a value >= 0x80. So
// `cp >= 0x80 && adv = 1` means "these bytes are not valid UTF-8 here" —
// a lone continuation byte, an overlong form, an encoded surrogate — and
// must be rejected even when the codepoint value itself is in the table
// (U+FFFD is, via 0xFDF0-0xFFFD). Same discrimination
// is_valid_decoded_char applies to content; see its comment.
let is_name_char_cp (cp:int) (adv:nat) : bool =
  if cp < 0 then false
  else if cp < 0x80 then
    // Delegate so the ASCII NameChar set has ONE definition.
    let n : nat = cp in
    is_name_char (Char.char_of_int n)
  else
    adv > 1 && is_name_char_nonascii_cp cp

// NameStartChar at codepoint level. The START position never got a
// codepoint test before: parse_xml_name checked the byte with
// is_name_start_char, whose non-ASCII arm accepts ANY lead byte >= 0xC0,
// then special-cased the single codepoint U+00B7 by hand. So every other
// non-NameStartChar codepoint was waved through as a name start, and the
// only reason xmlconf did not notice is that the byte-level BODY scan
// then truncated the name mid-codepoint and the element failed anyway —
// the right verdict for the wrong reason. With the body scan fixed
// (issue #325) that accident is gone, and two xmlconf cases immediately
// exposed the hole: o-p05fail4 (a Name may not start with a
// CombiningChar) and rmt-020 (U+F0000, illegal as a name character in
// BOTH XML 1.0 and 1.1). Testing the start codepoint properly is what
// they were always asking for, and it subsumes the U+00B7 special case:
// U+00B7 is an Extender, a NameChar but not a NameStartChar, so it now
// falls out of the table instead of being named in an `if`.
let is_name_start_cp (cp:int) (adv:nat) : bool =
  if cp < 0 then false
  else if cp < 0x80 then
    (cp >= 0x41 && cp <= 0x5A) ||
    (cp >= 0x61 && cp <= 0x7A) ||
    cp = 0x5F || cp = 0x3A
  else
    adv > 1 && is_name_start_char_nonascii_cp cp

// Scan the Name BODY from `pos`, one CODEPOINT at a time, and return the
// first position that is not a NameChar. Byte-stepping here is what
// truncated `<ex:日本語 …>` to the name "ex:" + 0xE6 (issue #325): the
// byte 0x97 is a continuation byte, the byte-level predicate rejected it,
// the element then failed on the leftover bytes, and the RDF/XML driver
// handed back an EMPTY graph with exit code 0.
let rec scan_name_body_end (input:string) (pos:nat) (fuel:nat)
  : Tot (r:nat{r >= pos}) (decreases fuel) =
  if fuel = 0 then pos
  else
    let len = fs_byte_length input in
    if pos >= len then pos
    else
      let (cp, adv) = fs_cp_at input pos in
      let advn : nat = if adv = 0 then 1 else adv in
      if not (is_name_char_cp cp advn) then pos
      else if pos + advn > len then pos
      else
        let r = scan_name_body_end input (pos + advn) (fuel - 1) in
        if r >= pos then r else pos

let parse_xml_name : parser string =
  fun input pos ->
    let len = fs_byte_length input in
    if pos >= len then ParseFail "expected XML name" pos
    else
      let (cp, adv) = fs_cp_at input pos in
      let advn : nat = if adv = 0 then 1 else adv in
      if not (is_name_start_cp cp advn) then
        ParseFail "expected XML name start character" pos
      else if pos + advn > len then ParseFail "expected XML name" pos
      else
        // The whole Name comes back as ONE fs_byte_sub of the raw input,
        // so it is byte-transparent (issue #325). The old shape,
        // `String.concat "" [string_of_char ch; rest]`, only round-tripped
        // because the start byte was handled byte-wise too — it emitted
        // the LEAD byte alone and let ptake_while_pos slice the rest.
        let body_end = scan_name_body_end input (pos + advn) (len - pos + 1) in
        if body_end <= len then
          ParseOk (fs_byte_sub input pos (body_end - pos)) body_end
        else ParseFail "expected XML name" pos


(* ================================================================ *)
(* Entity and character reference decoding                           *)
(* ================================================================ *)

let hex_digit_value (c:char) : int =
  let code = Char.int_of_char c in
  if code >= 0x30 && code <= 0x39 then code - 0x30
  else if code >= 0x41 && code <= 0x46 then code - 0x41 + 10
  else if code >= 0x61 && code <= 0x66 then code - 0x61 + 10
  else 0

let is_dec_digit_char (c:char) : bool =
  let code = Char.int_of_char c in
  code >= 0x30 && code <= 0x39

let is_hex_digit_char (c:char) : bool =
  let code = Char.int_of_char c in
  (code >= 0x30 && code <= 0x39) ||
  (code >= 0x41 && code <= 0x46) ||
  (code >= 0x61 && code <= 0x66)

// CharRef ::= '&#' [0-9]+ ';' | '&#x' [0-9a-fA-F]+ ';'. Every digit
// character must satisfy `valid_digit`, and at least one digit is
// required -- xmlconf's o-p66fail2 ("&# 65;", a space is not a
// decimal digit), o-p66fail3 ("&#A;", 'A' is not a decimal digit),
// o-p66fail4 ("&#x4G;", 'G' is not a hex digit), and not-wf-sa-009
// ("&#RE;") all reject on the first non-digit character rather than
// silently accumulating it (the previous behaviour: any non-';' byte
// was pushed onto the accumulator unchecked).
let rec parse_ref_digits (valid_digit: char -> bool) (input:string) (pos:nat) (acc:list char) (fuel:nat)
  : Tot (parse_result (list char)) (decreases fuel) =
  if fuel = 0 then ParseFail "character reference too long" pos
  else
    let len = fs_byte_length input in
    if pos >= len then ParseFail "unterminated character reference" pos
    else
      let ch = fs_byte_index input pos in
      if ch = ';' then
        if List.Tot.length acc = 0 then ParseFail "empty character reference" pos
        else ParseOk (List.Tot.rev acc) (pos + 1)
      else if valid_digit ch then
        parse_ref_digits valid_digit input (pos + 1) (ch :: acc) (fuel - 1)
      else ParseFail "invalid character reference digit" pos

let rec pow10 (n:nat) : Tot int (decreases n) =
  if n = 0 then 1 else op_Multiply 10 (pow10 (n - 1))

let rec pow16 (n:nat) : Tot int (decreases n) =
  if n = 0 then 1 else op_Multiply 16 (pow16 (n - 1))

let rec chars_to_dec (cs:list char) : Tot int (decreases cs) =
  match cs with
  | [] -> 0
  | c :: rest ->
    let digit = Char.int_of_char c - 0x30 in
    op_Multiply digit (pow10 (List.Tot.length rest)) + chars_to_dec rest

let rec chars_to_hex (cs:list char) : Tot int (decreases cs) =
  match cs with
  | [] -> 0
  | c :: rest ->
    op_Multiply (hex_digit_value c) (pow16 (List.Tot.length rest)) + chars_to_hex rest

(* UTF-8 encode a codepoint into a string of bytes.
   Previously this returned a single byte (cp mod 256) for all non-ASCII,
   corrupting every `&#xFC;`-style character reference. Tests under
   rdfms-difference-between-ID-and-about and rdf-charmod-literals exercise
   this; the expected N-Triples has the codepoint as UTF-8 (ü → C3 BC).

   We emit each UTF-8 byte by producing a 1-char string whose char is the
   byte value (0..255), then concatenating. Requires `Char.char_of_int`
   to accept byte values, which it does per FStar.Char. *)
let byte_of_int (b:int) : string =
  let b' = if b < 0 then 0 else if b > 255 then 255 else b in
  String.string_of_char (Char.char_of_int b')

let codepoint_to_string (cp:int) : string =
  if cp < 0 then "?"
  else if cp < 0x80 then
    byte_of_int cp
  else if cp < 0x800 then
    let b0 = 0xC0 + (cp / 64) in
    let b1 = 0x80 + (cp - (cp / 64) `op_Multiply` 64) in
    strcat (byte_of_int b0) (byte_of_int b1)
  else if cp < 0x10000 then
    let b0 = 0xE0 + (cp / 4096) in
    let cp' = cp - (cp / 4096) `op_Multiply` 4096 in
    let b1 = 0x80 + (cp' / 64) in
    let b2 = 0x80 + (cp' - (cp' / 64) `op_Multiply` 64) in
    strcat (byte_of_int b0) (strcat (byte_of_int b1) (byte_of_int b2))
  else if cp < 0x110000 then
    let b0 = 0xF0 + (cp / 262144) in
    let r1 = cp - (cp / 262144) `op_Multiply` 262144 in
    let b1 = 0x80 + (r1 / 4096) in
    let r2 = r1 - (r1 / 4096) `op_Multiply` 4096 in
    let b2 = 0x80 + (r2 / 64) in
    let b3 = 0x80 + (r2 - (r2 / 64) `op_Multiply` 64) in
    strcat (byte_of_int b0)
     (strcat (byte_of_int b1)
      (strcat (byte_of_int b2) (byte_of_int b3)))
  else "?"

(* ================================================================ *)
(* DTD general-entity table + reference expansion (Stage A)          *)
(*                                                                   *)
(* A `dtd_entity_table` maps a declared general internal entity's    *)
(* name to its RAW replacement text (the literal characters between  *)
(* the EntityValue quotes, un-expanded). It is collected from the    *)
(* DOCTYPE internal subset (see parse_doctype below) and threaded     *)
(* into the content/attribute reference parsers so that `&name;`      *)
(* resolves against it. Stage A is a non-validating (well-formedness) *)
(* slice: predefined entities first, then the declared table; an      *)
(* undeclared reference is rejected (WFC "Entity Declared"); a self-  *)
(* or mutually-recursive entity is rejected (WFC "No Recursion").     *)
(* Replacement text that itself contains markup ('<') is rejected     *)
(* rather than spliced as elements -- Stage A does not reparse an     *)
(* entity's replacement as content, so a markup-bearing entity is an  *)
(* acknowledged unsupported case (rejected, never wrongly accepted).  *)
(* Char references and predefined entities inside the replacement are *)
(* resolved; a nested DECLARED general entity inside the replacement  *)
(* is expanded through the same path under a visited-set + depth      *)
(* guard so recursion terminates.                                    *)
(* ================================================================ *)

let dtd_entity_table = list (string & string)

let rec mem_str (x:string) (xs:list string) : Tot bool (decreases xs) =
  match xs with
  | [] -> false
  | h :: t -> if h = x then true else mem_str x t

let rec lookup_entity (name:string) (ents:dtd_entity_table)
  : Tot (option string) (decreases ents) =
  match ents with
  | [] -> None
  | (n, v) :: rest -> if n = name then Some v else lookup_entity name rest

let is_predefined_entity (name:string) : bool =
  name = "amp" || name = "lt" || name = "gt" || name = "quot" || name = "apos"

let predefined_value (name:string) : string =
  if name = "amp" then "&"
  else if name = "lt" then "<"
  else if name = "gt" then ">"
  else if name = "quot" then "\""
  else "'"  // apos

// Fully expand a raw entity replacement text `s` into decoded text.
// `visited` holds the names currently being expanded (direct/indirect
// recursion -> reject). `depth` bounds how many nested DECLARED-entity
// expansions may still happen (bounded by the table size at entry, so a
// non-recursive chain always fits); `budget` bounds the scan of the
// current string. The lexicographic measure %[depth; budget] is
// well-founded: diving into a nested entity decrements `depth`;
// scanning forward within one string decrements `budget`.
let rec expand_entity_value (ents:dtd_entity_table) (visited:list string)
                            (s:string) (pos:nat) (depth:nat) (budget:nat) (acc:list string)
  : Tot (parse_result string) (decreases %[depth; budget]) =
  if budget = 0 then ParseFail "entity replacement text too long" pos
  else
    let len = fs_byte_length s in
    if pos >= len then ParseOk (String.concat "" (List.Tot.rev acc)) pos
    else
      let ch = fs_byte_index s pos in
      if ch = '<' then
        // WFC-ish Stage A boundary: an entity whose replacement contains
        // literal markup would have to be reparsed as content, which this
        // slice does not do -- reject rather than accept it as text.
        ParseFail "entity replacement text contains markup ('<'); unsupported in Stage A" pos
      else if ch = '&' then
        if pos + 1 < len && fs_byte_index s (pos + 1) = '#' then
          if pos + 2 >= len then ParseFail "unterminated character reference in entity" pos
          else
            let ch2 = fs_byte_index s (pos + 2) in
            if ch2 = 'x' then
              let cfuel = len - (pos + 3) + 1 in
              match parse_ref_digits is_hex_digit_char s (pos + 3) [] cfuel with
              | ParseOk digits pos' ->
                let cp = chars_to_hex digits in
                if is_valid_xml_char cp then
                  expand_entity_value ents visited s pos' depth (budget - 1)
                    (codepoint_to_string cp :: acc)
                else ParseFail "character reference to a non-Char codepoint" pos'
              | ParseFail msg fpos -> ParseFail msg fpos
            else
              let cfuel = len - (pos + 2) + 1 in
              match parse_ref_digits is_dec_digit_char s (pos + 2) [] cfuel with
              | ParseOk digits pos' ->
                let cp = chars_to_dec digits in
                if is_valid_xml_char cp then
                  expand_entity_value ents visited s pos' depth (budget - 1)
                    (codepoint_to_string cp :: acc)
                else ParseFail "character reference to a non-Char codepoint" pos'
              | ParseFail msg fpos -> ParseFail msg fpos
        else
          match parse_xml_name s (pos + 1) with
          | ParseFail msg fpos -> ParseFail msg fpos
          | ParseOk name pos_n ->
            if pos_n >= len || fs_byte_index s pos_n <> ';' then
              ParseFail "entity reference not terminated by ';'" pos_n
            else
              let pos' = pos_n + 1 in
              if is_predefined_entity name then
                expand_entity_value ents visited s pos' depth (budget - 1)
                  (predefined_value name :: acc)
              else if mem_str name visited then
                ParseFail "recursive entity reference (WFC: No Recursion)" pos
              else begin
                match lookup_entity name ents with
                | None -> ParseFail "reference to undeclared entity" pos
                | Some subval ->
                  if depth = 0 then ParseFail "entity nesting too deep" pos
                  else
                    match expand_entity_value ents (name :: visited) subval 0
                            (depth - 1) (fs_byte_length subval + 1) [] with
                    | ParseFail msg fpos -> ParseFail msg fpos
                    | ParseOk sub _ ->
                      expand_entity_value ents visited s pos' depth (budget - 1) (sub :: acc)
              end
      else
        expand_entity_value ents visited s (pos + 1) depth (budget - 1)
          (String.string_of_char ch :: acc)

// Parse a single reference starting at `pos` (which points at the byte
// AFTER the leading '&'). Returns the decoded replacement string and the
// position after the terminating ';'. Char references and the five
// predefined entities resolve directly; any other name is looked up in
// the DTD general-entity table (`ents`) and its replacement expanded.
let parse_reference (ents:dtd_entity_table) (input:string) (pos:nat) : parse_result string =
  let len = fs_byte_length input in
  if pos >= len then ParseFail "unterminated reference" pos
  else
    let ch = fs_byte_index input pos in
    if ch = '#' then
      if pos + 1 >= len then ParseFail "unterminated character reference" pos
      else
        let ch2 = fs_byte_index input (pos + 1) in
        // Only lowercase 'x' introduces a hex CharRef (CharRef ::=
        // '&#x' ... -- not-wf-sa-093: uppercase 'X' is not the hex
        // marker at all, and must instead fall through to the decimal
        // path, where 'X' is not a decimal digit and rejects).
        if ch2 = 'x' then
          let fuel = len - (pos + 2) + 1 in
          match parse_ref_digits is_hex_digit_char input (pos + 2) [] fuel with
          | ParseOk digits pos' ->
            let cp = chars_to_hex digits in
            if is_valid_xml_char cp then ParseOk (codepoint_to_string cp) pos'
            else ParseFail "character reference to a non-Char codepoint" pos'
          | ParseFail msg fpos -> ParseFail msg fpos
        else
          let fuel = len - (pos + 1) + 1 in
          match parse_ref_digits is_dec_digit_char input (pos + 1) [] fuel with
          | ParseOk digits pos' ->
            let cp = chars_to_dec digits in
            if is_valid_xml_char cp then ParseOk (codepoint_to_string cp) pos'
            else ParseFail "character reference to a non-Char codepoint" pos'
          | ParseFail msg fpos -> ParseFail msg fpos
    else
      match parse_xml_name input pos with
      | ParseFail msg fpos -> ParseFail msg fpos
      | ParseOk name pos_n ->
        if pos_n >= len || fs_byte_index input pos_n <> ';' then
          ParseFail "entity reference not terminated by ';'" pos_n
        else
          let pos' = pos_n + 1 in
          if is_predefined_entity name then ParseOk (predefined_value name) pos'
          else
            match lookup_entity name ents with
            | None -> ParseFail "reference to undeclared entity" pos
            | Some subval ->
              let depth = List.Tot.length ents + 1 in
              match expand_entity_value ents [name] subval 0 depth
                      (fs_byte_length subval + 1) [] with
              | ParseFail msg fpos -> ParseFail msg fpos
              | ParseOk decoded _ -> ParseOk decoded pos'


(* ================================================================ *)
(* Attribute-value normalization (XML 1.0 SS3.3.3)                   *)
(*                                                                    *)
(* "Before the value of an attribute is passed to the application... *)
(* an XML processor MUST... for a white space character (#x20, #xD,  *)
(* #xA, #x9), append a space character (#x20)." This applies only to *)
(* whitespace written LITERALLY in the attribute value's source text *)
(* -- a character reference to one of these same codepoints (&#9;,   *)
(* &#10;, &#13;) is explicitly carved out by the spec ("the           *)
(* normalized value contains the referenced character itself") and   *)
(* MUST NOT be touched. parse_attr_value_body below keeps that        *)
(* distinction by construction: this function is applied only to the *)
(* raw literal runs it slices straight out of `input` (the            *)
(* `ptake_while_pos` branch), never to the `decoded` string that      *)
(* parse_reference returns for `&...;` (char refs and entity refs).   *)
(* By the time this runs, parse_xml_document's line-ending            *)
(* normalization pre-pass has already turned every literal CR into    *)
(* LF, so in practice only '\t' and '\n' remain reachable here -- the *)
(* '\r' arm stays for spec-literal completeness and so this function  *)
(* is correct standalone, independent of caller order.                *)
(* ================================================================ *)

let rec normalize_attr_literal_ws_acc (input:string) (pos:nat) (acc:list string) (fuel:nat)
  : Tot string (decreases fuel) =
  if fuel = 0 then String.concat "" (List.Tot.rev acc)
  else
    let len = fs_byte_length input in
    if pos >= len then String.concat "" (List.Tot.rev acc)
    else
      let ch = fs_byte_index input pos in
      if ch = '\t' || ch = '\n' || ch = '\r' then
        normalize_attr_literal_ws_acc input (pos + 1) (" " :: acc) (fuel - 1)
      else
        match ptake_while_pos (fun c -> c <> '\t' && c <> '\n' && c <> '\r') input pos with
        | ParseOk s pos' ->
          if fs_byte_length s > 0 then
            normalize_attr_literal_ws_acc input pos' (s :: acc) (fuel - 1)
          else
            normalize_attr_literal_ws_acc input (pos + 1) (String.string_of_char ch :: acc) (fuel - 1)
        | ParseFail _ _ ->
          normalize_attr_literal_ws_acc input (pos + 1) (String.string_of_char ch :: acc) (fuel - 1)

// Replace every literal tab/CR/LF in `s` (a raw substring sliced directly
// out of the source document) with a single space. `s` here is always a
// literal run, never entity/char-ref-decoded text -- see the block
// comment above.
let normalize_attr_literal_ws (s:string) : string =
  let len = fs_byte_length s in
  normalize_attr_literal_ws_acc s 0 [] (len + 1)

(* ================================================================ *)
(* Attribute value parser (with entity decoding)                     *)
(* ================================================================ *)

let rec parse_attr_value_body (ents:dtd_entity_table) (qch:char) (input:string) (pos:nat) (acc:list string) (fuel:nat)
  : Tot (parse_result string) (decreases fuel) =
  if fuel = 0 then ParseFail "attribute value too long" pos
  else
    let len = fs_byte_length input in
    if pos >= len then ParseFail "unterminated attribute value" pos
    else
      let ch = fs_byte_index input pos in
      if ch = qch then
        ParseOk (String.concat "" (List.Tot.rev acc)) (pos + 1)
      else if ch = '<' then
        // AttValue excludes '<' unconditionally (XML 1.0 §2.3 [10] /
        // §3.1 -- o-p10fail1, not-wf-sa-014).
        ParseFail "attribute values exclude '<'" pos
      else if ch = '&' then
        match parse_reference ents input (pos + 1) with
        | ParseOk decoded pos' ->
          parse_attr_value_body ents qch input pos' (decoded :: acc) (fuel - 1)
        | ParseFail msg fpos -> ParseFail msg fpos
      else
        match ptake_while_pos (fun c -> c <> qch && c <> '&' && c <> '<') input pos with
        | ParseOk s pos' ->
          if fs_byte_length s > 0 then
            if not (scan_chars_valid input pos pos' (pos' - pos)) then
              ParseFail "invalid character in attribute value" pos
            else
              // XML 1.0 SS3.3.3: literal tab/CR/LF in this raw slice
              // becomes a single space. `s` is sliced straight from
              // `input`, never entity/char-ref-decoded output, so this
              // is exactly the "literal whitespace" case the spec
              // distinguishes from a whitespace character reference.
              parse_attr_value_body ents qch input pos' (normalize_attr_literal_ws s :: acc) (fuel - 1)
          else
            parse_attr_value_body ents qch input (pos + 1)
              (normalize_attr_literal_ws (String.string_of_char ch) :: acc) (fuel - 1)
        | ParseFail msg fpos -> ParseFail msg fpos

let parse_attr_value (ents:dtd_entity_table) (input:string) (pos:nat) : parse_result string =
  let len = fs_byte_length input in
  if pos >= len then ParseFail "expected attribute value" pos
  else
    let qch = fs_byte_index input pos in
    if qch = '"' || qch = '\'' then
      let fuel = len - pos in
      parse_attr_value_body ents qch input (pos + 1) [] fuel
    else ParseFail "expected quote to start attribute value" pos


(* ================================================================ *)
(* XML Attribute parser                                              *)
(* ================================================================ *)

let skip_xml_space (input:string) (pos:nat) : parse_result unit =
  match ptake_while_pos is_xml_space input pos with
  | ParseOk _ pos' -> ParseOk () pos'
  | ParseFail msg fpos -> ParseFail msg fpos

let parse_xml_attribute (ents:dtd_entity_table) (input:string) (pos:nat) : parse_result xml_attribute =
  match parse_xml_name input pos with
  | ParseOk name pos1 ->
    begin match skip_xml_space input pos1 with
    | ParseOk () pos2 ->
      begin match pchar '=' input pos2 with
      | ParseOk _ pos3 ->
        begin match skip_xml_space input pos3 with
        | ParseOk () pos4 ->
          begin match parse_attr_value ents input pos4 with
          | ParseOk value pos5 ->
            ParseOk ({ attr_name = name; attr_value = value }) pos5
          | ParseFail msg fpos -> ParseFail msg fpos
          end
        | ParseFail msg fpos -> ParseFail msg fpos
        end
      | ParseFail msg fpos -> ParseFail msg fpos
      end
    | ParseFail msg fpos -> ParseFail msg fpos
    end
  | ParseFail msg fpos -> ParseFail msg fpos

let rec mem_attr_name (name:string) (attrs:list xml_attribute) : Tot bool (decreases attrs) =
  match attrs with
  | [] -> false
  | a :: rest -> if a.attr_name = name then true else mem_attr_name name rest

let rec parse_attributes (ents:dtd_entity_table) (input:string) (pos:nat) (fuel:nat)
  : Tot (parse_result (list xml_attribute)) (decreases fuel) =
  if fuel = 0 then ParseOk [] pos
  else
    let len = fs_byte_length input in
    if pos >= len then ParseOk [] pos
    else
      match ptake_while1_pos is_xml_space input pos with
      | ParseOk _ pos1 ->
        if pos1 < len then
          let ch = fs_byte_index input pos1 in
          if is_name_start_char ch then
            match parse_xml_attribute ents input pos1 with
            | ParseOk attr pos2 ->
              begin match parse_attributes ents input pos2 (fuel - 1) with
              | ParseOk attrs pos3 ->
                // Attribute uniqueness (XML 1.0 §3.1 [44] / Unique
                // Att Spec WF constraint): no two attributes on the
                // same element may share a name -- o-p44fail5,
                // not-wf-sa-038.
                if mem_attr_name attr.attr_name attrs then
                  ParseFail "duplicate attribute name" pos2
                else
                  ParseOk (attr :: attrs) pos3
              | ParseFail msg fpos -> ParseFail msg fpos
              end
            | ParseFail msg fpos -> ParseFail msg fpos
          else
            ParseOk [] pos1
        else ParseOk [] pos1
      | ParseFail _ _ ->
        ParseOk [] pos


(* ================================================================ *)
(* XML text content parser (with entity decoding)                    *)
(* ================================================================ *)

let rec parse_text_content (ents:dtd_entity_table) (input:string) (pos:nat) (acc:list string) (fuel:nat)
  : Tot (parse_result string) (decreases fuel) =
  if fuel = 0 then ParseOk (String.concat "" (List.Tot.rev acc)) pos
  else
    let len = fs_byte_length input in
    if pos >= len then ParseOk (String.concat "" (List.Tot.rev acc)) pos
    else
      let ch = fs_byte_index input pos in
      if ch = '<' then
        ParseOk (String.concat "" (List.Tot.rev acc)) pos
      else if ch = '&' then
        match parse_reference ents input (pos + 1) with
        | ParseOk decoded pos' ->
          parse_text_content ents input pos' (decoded :: acc) (fuel - 1)
        | ParseFail msg fpos -> ParseFail msg fpos
      else
        match ptake_while_pos (fun c -> c <> '<' && c <> '&') input pos with
        | ParseOk s pos' ->
          if fs_byte_length s > 0 then
            if not (scan_chars_valid input pos pos' (pos' - pos)) then
              ParseFail "invalid character in text content" pos
            else if bytes_have_cdata_close input pos pos' (pos' - pos) then
              // CharData excludes the literal "]]>" sequence (XML 1.0
              // §2.4 [14] -- o-p14fail3, not-wf-sa-025/026/029).
              ParseFail "text may not contain a literal ']]>' sequence" pos
            else
              parse_text_content ents input pos' (s :: acc) (fuel - 1)
          else
            parse_text_content ents input (pos + 1)
              (String.string_of_char ch :: acc) (fuel - 1)
        | ParseFail msg fpos -> ParseFail msg fpos

let parse_xml_text (ents:dtd_entity_table) (input:string) (pos:nat) : parse_result xml_node =
  let len = fs_byte_length input in
  let fuel = len - pos + 1 in
  if fuel >= 0 then
    match parse_text_content ents input pos [] fuel with
    | ParseOk text pos' ->
      if fs_byte_length text > 0 then ParseOk (XText text) pos'
      else ParseFail "empty text node" pos
    | ParseFail msg fpos -> ParseFail msg fpos
  else ParseFail "unexpected position" pos


(* ================================================================ *)
(* XML Comment parser                                                *)
(* ================================================================ *)

// Issue #325 — this walk used to accumulate the raw bytes it stepped over
// into a `list char` and finish with String.string_of_list, whose
// extracted realisation re-encodes each element as a UTF-8 CODEPOINT. A
// byte 0xE6 went in and the bytes 0xC3 0xA6 came out, so every non-ASCII
// comment / CDATA / PI body was returned as mojibake (`日本` -> `æ¥æ¬`).
// CDATA is the one of the three that reaches RDF output, so it was a
// user-visible corruption of literal content.
//
// The accumulator was never inspected — the result is exactly the raw
// byte range [start, pos) — so the fix removes it entirely and slices
// once with fs_byte_sub. That is byte-transparent by construction, keeps
// the per-byte continuation-byte / is_valid_decoded_char validity walk
// untouched, and drops one allocation per byte.
//
// `pos:nat{pos >= start}` is what makes the `pos - start` slice length a
// nat; every recursive call advances pos, so it is maintained.
let rec parse_comment_body (input:string) (start:nat) (pos:nat{pos >= start}) (fuel:nat)
  : Tot (parse_result string) (decreases fuel) =
  if fuel = 0 then ParseFail "unterminated comment" pos
  else
    let len = fs_byte_length input in
    if pos + 2 < len then
      let c0 = fs_byte_index input pos in
      let c1 = fs_byte_index input (pos + 1) in
      let c2 = fs_byte_index input (pos + 2) in
      if c0 = '-' && c1 = '-' && c2 = '>' then
        ParseOk (fs_byte_sub input start (pos - start)) (pos + 3)
      else if is_utf8_continuation_byte c0 then
        parse_comment_body input start (pos + 1) (fuel - 1)
      else
        let (cp, adv) = fs_cp_at input pos in
        if not (is_valid_decoded_char cp adv) then ParseFail "invalid character in comment" pos
        else parse_comment_body input start (pos + 1) (fuel - 1)
    else if pos < len then
      let c0 = fs_byte_index input pos in
      if is_utf8_continuation_byte c0 then
        parse_comment_body input start (pos + 1) (fuel - 1)
      else
        let (cp, adv) = fs_cp_at input pos in
        if not (is_valid_decoded_char cp adv) then ParseFail "invalid character in comment" pos
        else parse_comment_body input start (pos + 1) (fuel - 1)
    else ParseFail "unterminated comment" pos

let parse_xml_comment (input:string) (pos:nat) : parse_result xml_node =
  match pstring "<!--" input pos with
  | ParseOk _ pos1 ->
    let len = fs_byte_length input in
    let fuel = len - pos1 + 1 in
    begin match parse_comment_body input pos1 pos1 fuel with
    | ParseOk text pos2 ->
      // Comment ::= '<!--' ((Char - '-') | ('-' (Char - '-')))* '-->'
      // -- "--" may not occur anywhere in the body, and the body may
      // not end in '-' (else the closing delimiter would itself
      // require a 3rd dash, i.e. the body ends in "-" right before
      // "-->"). o-p15fail1/2/3, not-wf-sa-006/070.
      if bytes_have_double_dash text 0 (fs_byte_length text) (fs_byte_length text)
         || ends_with_dash text
      then ParseFail "comment must not contain '--' or end in '-'" pos1
      else ParseOk (XComment text) pos2
    | ParseFail msg fpos -> ParseFail msg fpos
    end
  | ParseFail msg fpos -> ParseFail msg fpos


(* ================================================================ *)
(* CDATA section parser                                              *)
(* ================================================================ *)

// Issue #325: byte-transparent slice instead of a char accumulator. See
// the comment on parse_comment_body for the double-encoding this fixes;
// CDATA is the variant whose content reaches RDF literals, so this was
// the user-visible one: `<![CDATA[日本 café]]>` produced the literal
// "æ¥æ¬ cafÃ©".
let rec parse_cdata_body (input:string) (start:nat) (pos:nat{pos >= start}) (fuel:nat)
  : Tot (parse_result string) (decreases fuel) =
  if fuel = 0 then ParseFail "unterminated CDATA section" pos
  else
    let len = fs_byte_length input in
    if pos + 2 < len then
      let c0 = fs_byte_index input pos in
      let c1 = fs_byte_index input (pos + 1) in
      let c2 = fs_byte_index input (pos + 2) in
      if c0 = ']' && c1 = ']' && c2 = '>' then
        ParseOk (fs_byte_sub input start (pos - start)) (pos + 3)
      else if is_utf8_continuation_byte c0 then
        parse_cdata_body input start (pos + 1) (fuel - 1)
      else
        let (cp, adv) = fs_cp_at input pos in
        if not (is_valid_decoded_char cp adv) then ParseFail "invalid character in CDATA section" pos
        else parse_cdata_body input start (pos + 1) (fuel - 1)
    else if pos < len then
      let c0 = fs_byte_index input pos in
      if is_utf8_continuation_byte c0 then
        parse_cdata_body input start (pos + 1) (fuel - 1)
      else
        let (cp, adv) = fs_cp_at input pos in
        if not (is_valid_decoded_char cp adv) then ParseFail "invalid character in CDATA section" pos
        else parse_cdata_body input start (pos + 1) (fuel - 1)
    else ParseFail "unterminated CDATA section" pos

let parse_xml_cdata (input:string) (pos:nat) : parse_result xml_node =
  match pstring "<![CDATA[" input pos with
  | ParseOk _ pos1 ->
    let len = fs_byte_length input in
    let fuel = len - pos1 + 1 in
    begin match parse_cdata_body input pos1 pos1 fuel with
    | ParseOk text pos2 -> ParseOk (XCDATA text) pos2
    | ParseFail msg fpos -> ParseFail msg fpos
    end
  | ParseFail msg fpos -> ParseFail msg fpos


(* ================================================================ *)
(* Processing instruction skipper                                    *)
(*                                                                   *)
(* XML 1.0 §2.6 — `<?TARGET … ?>` appears in prolog, content, or     *)
(* epilog. We don't interpret PIs (they're not part of RDF), but     *)
(* we have to skip them cleanly so element parsing doesn't choke.    *)
(* rdfms-empty-property-elements-test016 puts one inside an          *)
(* otherwise-empty property element; test001.rdf puts one in the     *)
(* prolog. Both have to parse. The `<?xml …?>` declaration is a      *)
(* special case already handled by parse_xml_declaration; this       *)
(* skipper is for every other target name.                          *)
(* ================================================================ *)

// Collect the PI data (everything from `start` up to the closing '?>'),
// stepping one byte at a time. Same byte-stepping / continuation-byte /
// character-validity discipline as parse_comment_body and
// parse_cdata_body — including the issue-#325 fix: the data is returned
// as one fs_byte_sub slice of the raw input, never rebuilt from a
// `list char` through String.string_of_list (which would re-encode each
// byte as a codepoint and mojibake every non-ASCII PI body).
let rec collect_pi_body (input:string) (start:nat) (pos:nat{pos >= start}) (fuel:nat)
  : Tot (parse_result string) (decreases fuel) =
  if fuel = 0 then ParseFail "unterminated processing instruction" pos
  else
    let len = fs_byte_length input in
    if pos + 1 < len then
      let c0 = fs_byte_index input pos in
      let c1 = fs_byte_index input (pos + 1) in
      if c0 = '?' && c1 = '>' then
        ParseOk (fs_byte_sub input start (pos - start)) (pos + 2)
      else if is_utf8_continuation_byte c0 then
        collect_pi_body input start (pos + 1) (fuel - 1)
      else
        let (cp, adv) = fs_cp_at input pos in
        if not (is_valid_decoded_char cp adv) then
          ParseFail "invalid character in processing instruction" pos
        else collect_pi_body input start (pos + 1) (fuel - 1)
    else ParseFail "unterminated processing instruction" pos

// PI ::= '<?' PITarget (S (Char* - (Char* '?>' Char*)))? '?>'
// PITarget ::= Name - (('X'|'x')('M'|'m')('L'|'l'))
//
// The target name is required (not-wf-sa-003: `<? ?>` has none) and
// the reserved, case-insensitive "xml" target is forbidden here --
// that token may only be consumed by parse_xml_declaration, at the
// literal start of the document. Any other occurrence (mid-content,
// in the epilog, wrong case) is not a legal generic PI, matching
// xmlconf's PI-target-casing cluster and several "XML declaration
// may not appear here" cases that a plain PI walk encounters.
let parse_xml_pi (input:string) (pos:nat) : parse_result xml_node =
  match pstring "<?" input pos with
  | ParseOk _ pos1 ->
    begin match parse_xml_name input pos1 with
    | ParseFail msg fpos -> ParseFail msg fpos
    | ParseOk target pos2 ->
      if is_xml_target_name_ci target then
        ParseFail "PI target name 'xml' (any case) is reserved" pos1
      else
        let len = fs_byte_length input in
        // PI ::= '<?' PITarget (S (Char* - (Char* '?>' Char*)))? '?>'.
        // Either '?>' follows the target immediately (empty data), or S
        // is REQUIRED between the target and the data. Enforcing the S
        // is what keeps the not-wf "S after PITarget is required"
        // cluster (o-p16fail3 et al.) rejected now that prolog/epilog/
        // content PIs are all parsed through here. The DOM/XPath data
        // string excludes that separating whitespace.
        if pos2 + 1 < len && fs_byte_index input pos2 = '?' && fs_byte_index input (pos2 + 1) = '>' then
          ParseOk (XPI target "") (pos2 + 2)
        else
          begin match ptake_while1_pos is_xml_space input pos2 with
          | ParseFail _ _ -> ParseFail "S after PITarget is required" pos2
          | ParseOk _ pos_data ->
            let fuel = len - pos_data + 1 in
            begin match collect_pi_body input pos_data pos_data fuel with
            | ParseOk data pos3 -> ParseOk (XPI target data) pos3
            | ParseFail msg fpos -> ParseFail msg fpos
            end
          end
    end
  | ParseFail msg fpos -> ParseFail msg fpos


(* ================================================================ *)
(* XML Declaration parser                                            *)
(* ================================================================ *)

// XMLDecl ::= '<?xml' VersionInfo EncodingDecl? SDDecl? S? '?>'
//
// The previous implementation reused the generic (unordered,
// duplicate-tolerant) `parse_attributes` list parser for the whole
// declaration body, so it had no positional grammar and no
// per-attribute value lexicon -- any pseudo-attribute in any order,
// repeated any number of times, with an unchecked value, parsed
// cleanly. This is a strict, ordered, hand-rolled walk instead:
// VersionInfo is mandatory and must come first; EncodingDecl and
// SDDecl are each optional, in that relative order, each attempted
// exactly once; anything left over before '?>' fails the whole
// declaration (an unknown fourth pseudo-attribute, a duplicate, or
// out-of-order EncodingDecl/SDDecl all become unconsumed trailing
// text at that point). Value lexicons (VersionNum / EncName / "yes"
// | "no") are checked explicitly. See xmlconf's "XML declaration
// grammar" fail cluster (18 tests) for the exact cases this covers.

let rec check_bytes_from (pred: char -> bool) (s:string) (pos:nat) (limit:nat) (fuel:nat)
  : Tot bool (decreases fuel) =
  if fuel = 0 then true
  else if pos >= limit then true
  else if pred (fs_byte_index s pos) then check_bytes_from pred s (pos + 1) limit (fuel - 1)
  else false

// VersionNum ::= '1.' [0-9]+ (XML 1.0 5th edition's relaxed lexicon).
let is_version_num (s:string) : bool =
  let len = fs_byte_length s in
  len >= 3 &&
  fs_byte_index s 0 = '1' && fs_byte_index s 1 = '.' &&
  check_bytes_from is_dec_digit_char s 2 len len

let is_enc_name_first_char (c:char) : bool =
  let code = Char.int_of_char c in
  (code >= 0x41 && code <= 0x5A) || (code >= 0x61 && code <= 0x7A)

let is_enc_name_rest_char (c:char) : bool =
  let code = Char.int_of_char c in
  (code >= 0x41 && code <= 0x5A) || (code >= 0x61 && code <= 0x7A) ||
  (code >= 0x30 && code <= 0x39) || code = 0x2E || code = 0x5F || code = 0x2D

// EncName ::= [A-Za-z] ([A-Za-z0-9._] | '-')*
let is_enc_name (s:string) : bool =
  let len = fs_byte_length s in
  len >= 1 &&
  is_enc_name_first_char (fs_byte_index s 0) &&
  check_bytes_from is_enc_name_rest_char s 1 len len

// SDDecl value ::= ('yes' | 'no') -- lowercase only (o-p32fail5,
// not-wf-sa-100: "YES" is rejected).
let is_sd_value (s:string) : bool = s = "yes" || s = "no"

// Attempts "S name = quotedvalue" at `pos`, requiring `name` exactly
// (case-sensitive literal). Returns Some (value, pos') having
// consumed the whole pseudo-attribute on success; None (position
// untouched -- the caller just doesn't advance past `pos`) if the
// mandatory leading whitespace or the literal name doesn't match
// here, so the caller can try the next production in the grammar (or
// treat the pseudo-attribute as absent) from the same starting point.
let try_pseudo_attr (name:string) (input:string) (pos:nat) : option (string & nat) =
  begin match ptake_while1_pos is_xml_space input pos with
  | ParseFail _ _ -> None
  | ParseOk _ pos1 ->
    begin match pstring name input pos1 with
    | ParseFail _ _ -> None
    | ParseOk _ pos2 ->
      begin match skip_xml_space input pos2 with
      | ParseFail _ _ -> None
      | ParseOk () pos3 ->
        begin match pchar '=' input pos3 with
        | ParseFail _ _ -> None
        | ParseOk _ pos4 ->
          begin match skip_xml_space input pos4 with
          | ParseFail _ _ -> None
          | ParseOk () pos5 ->
            begin match parse_attr_value [] input pos5 with
            | ParseFail _ _ -> None
            | ParseOk v pos6 -> Some (v, pos6)
            end
          end
        end
      end
    end
  end

// S? '?>' -- optional trailing whitespace, then the mandatory closer.
// Anything else left over (an unrecognized/duplicate/out-of-order
// pseudo-attribute) makes this fail, rejecting the whole declaration.
let finish_xml_decl (input:string) (pos:nat) (attrs:list xml_attribute)
  : parse_result (list xml_attribute) =
  begin match skip_xml_space input pos with
  | ParseFail msg fpos -> ParseFail msg fpos
  | ParseOk () pos1 ->
    begin match pstring "?>" input pos1 with
    | ParseOk _ pos2 -> ParseOk attrs pos2
    | ParseFail msg fpos -> ParseFail msg fpos
    end
  end

let parse_xml_declaration (input:string) (pos:nat) : parse_result (list xml_attribute) =
  begin match pstring "<?xml" input pos with
  | ParseFail msg fpos -> ParseFail msg fpos
  | ParseOk _ pos0 ->
    // Mandatory S before the mandatory VersionInfo.
    begin match ptake_while1_pos is_xml_space input pos0 with
    | ParseFail msg fpos -> ParseFail msg fpos
    | ParseOk _ pos1 ->
      begin match pstring "version" input pos1 with
      | ParseFail msg fpos -> ParseFail msg fpos
      | ParseOk _ pos2 ->
        begin match skip_xml_space input pos2 with
        | ParseFail msg fpos -> ParseFail msg fpos
        | ParseOk () pos3 ->
          begin match pchar '=' input pos3 with
          | ParseFail msg fpos -> ParseFail msg fpos
          | ParseOk _ pos4 ->
            begin match skip_xml_space input pos4 with
            | ParseFail msg fpos -> ParseFail msg fpos
            | ParseOk () pos5 ->
              begin match parse_attr_value [] input pos5 with
              | ParseFail msg fpos -> ParseFail msg fpos
              | ParseOk vernum pos6 ->
                if not (is_version_num vernum) then
                  ParseFail "illegal VersionNum" pos5
                else
                  begin
                    let version_attr = { attr_name = "version"; attr_value = vernum } in
                    begin match try_pseudo_attr "encoding" input pos6 with
                    | Some (encval, pos7) ->
                      if not (is_enc_name encval) then ParseFail "illegal EncName" pos7
                      else
                        begin
                          let enc_attr = { attr_name = "encoding"; attr_value = encval } in
                          begin match try_pseudo_attr "standalone" input pos7 with
                          | Some (sdval, pos8) ->
                            if not (is_sd_value sdval) then ParseFail "illegal SDDecl value" pos8
                            else
                              begin
                                let sd_attr = { attr_name = "standalone"; attr_value = sdval } in
                                finish_xml_decl input pos8 [version_attr; enc_attr; sd_attr]
                              end
                          | None -> finish_xml_decl input pos7 [version_attr; enc_attr]
                          end
                        end
                    | None ->
                      begin match try_pseudo_attr "standalone" input pos6 with
                      | Some (sdval, pos7) ->
                        if not (is_sd_value sdval) then ParseFail "illegal SDDecl value" pos7
                        else
                          begin
                            let sd_attr = { attr_name = "standalone"; attr_value = sdval } in
                            finish_xml_decl input pos7 [version_attr; sd_attr]
                          end
                      | None -> finish_xml_decl input pos6 [version_attr]
                      end
                    end
                  end
              end
            end
          end
        end
      end
    end
  end


(* ================================================================ *)
(* XML Element parser (recursive, fuel-based)                        *)
(* ================================================================ *)

// 2026-07-04 rewrite (issue #273): every recursive branch used to do
// `match parse_children ... with ParseOk rest pos'' -> ParseOk (x :: rest) pos''`
// — the cons happens after the recursive call returns, so this was
// non-tail with one stack frame per sibling node. On a flat RDF/XML
// document (thousands of same-depth <rdf:Description> siblings, the
// exact shape of tools/bench-parse-serialize.sh's fixture) this blew
// the native stack above roughly 10k elements while N-Triples/Turtle
// on the same triple count parsed fine, since those parsers are
// already accumulator-based. `acc` accumulates children in reverse;
// every ParseOk exit reverses once via List.Tot.rev.
let rec parse_children (ents:dtd_entity_table) (input:string) (pos:nat) (fuel:nat) (acc:list xml_node)
  : Tot (parse_result (list xml_node)) (decreases fuel) =
  if fuel = 0 then ParseOk (List.Tot.rev acc) pos
  else
    let len = fs_byte_length input in
    if pos >= len then ParseOk (List.Tot.rev acc) pos
    else
      let ch = fs_byte_index input pos in
      if ch = '<' then
        if pos + 1 < len then
          let ch2 = fs_byte_index input (pos + 1) in
          if ch2 = '/' then
            ParseOk (List.Tot.rev acc) pos
          else if ch2 = '!' then
            begin match parse_xml_comment input pos with
            | ParseOk comment pos' ->
              parse_children ents input pos' (fuel - 1) (comment :: acc)
            | ParseFail _ _ ->
              begin match parse_xml_cdata input pos with
              | ParseOk cdata pos' ->
                parse_children ents input pos' (fuel - 1) (cdata :: acc)
              | ParseFail msg fpos -> ParseFail msg fpos
              end
            end
          else if ch2 = '?' then
            (* Processing instruction in content position: retain it as
               an XPI child so processing-instruction() and XSLT can see
               it. *)
            begin match parse_xml_pi input pos with
            | ParseOk pi_node pos' -> parse_children ents input pos' (fuel - 1) (pi_node :: acc)
            | ParseFail msg fpos -> ParseFail msg fpos
            end
          else
            begin match parse_xml_element ents input pos (fuel - 1) with
            | ParseOk elem pos' ->
              parse_children ents input pos' (fuel - 1) (elem :: acc)
            | ParseFail msg fpos -> ParseFail msg fpos
            end
        else ParseFail "unexpected end after '<'" pos
      else
        match parse_xml_text ents input pos with
        | ParseOk text_node pos' ->
          if pos' = pos then ParseOk (List.Tot.rev acc) pos
          else
            parse_children ents input pos' (fuel - 1) (text_node :: acc)
        | ParseFail _ _ -> ParseOk (List.Tot.rev acc) pos

and parse_xml_element (ents:dtd_entity_table) (input:string) (pos:nat) (fuel:nat)
  : Tot (parse_result xml_node) (decreases fuel) =
  if fuel = 0 then ParseFail "element nesting too deep (out of fuel)" pos
  else
    match pchar '<' input pos with
    | ParseOk _ pos1 ->
      begin match parse_xml_name input pos1 with
      | ParseOk tag pos2 ->
        let len = fs_byte_length input in
        let attr_fuel = if pos2 <= len then len - pos2 + 1 else 1 in
        begin match parse_attributes ents input pos2 attr_fuel with
        | ParseOk attrs pos3 ->
          begin match skip_xml_space input pos3 with
          | ParseOk () pos4 ->
            begin match pstring "/>" input pos4 with
            | ParseOk _ pos5 ->
              ParseOk (XElement tag attrs []) pos5
            | ParseFail _ _ ->
              begin match pchar '>' input pos4 with
              | ParseOk _ pos5 ->
                begin match parse_children ents input pos5 (fuel - 1) [] with
                | ParseOk children pos6 ->
                  begin match pstring "</" input pos6 with
                  | ParseOk _ pos7 ->
                    begin match parse_xml_name input pos7 with
                    | ParseOk close_tag pos8 ->
                      if close_tag = tag then
                        begin match skip_xml_space input pos8 with
                        | ParseOk () pos9 ->
                          begin match pchar '>' input pos9 with
                          | ParseOk _ pos10 ->
                            ParseOk (XElement tag attrs children) pos10
                          | ParseFail msg fpos -> ParseFail msg fpos
                          end
                        | ParseFail msg fpos -> ParseFail msg fpos
                        end
                      else
                        ParseFail (String.concat "" [
                          "closing tag '</"; close_tag;
                          ">' does not match opening '<"; tag; ">'"])
                          pos7
                    | ParseFail msg fpos -> ParseFail msg fpos
                    end
                  | ParseFail msg fpos -> ParseFail msg fpos
                  end
                | ParseFail msg fpos -> ParseFail msg fpos
                end
              | ParseFail msg fpos -> ParseFail msg fpos
              end
            end
          | ParseFail msg fpos -> ParseFail msg fpos
          end
        | ParseFail msg fpos -> ParseFail msg fpos
        end
      | ParseFail msg fpos -> ParseFail msg fpos
      end
    | ParseFail msg fpos -> ParseFail msg fpos


(* ================================================================ *)
(* DOCTYPE / internal-subset parser (Stage A: WF-only)               *)
(*                                                                   *)
(* doctypedecl ::= '<!DOCTYPE' S Name (S ExternalID)? S?             *)
(*                 ('[' intSubset ']' S?)? '>'                       *)
(*                                                                   *)
(* We recognise the DOCTYPE, collect `<!ENTITY name "value">` GENERAL *)
(* internal entity declarations from the internal subset into a       *)
(* dtd_entity_table, and PARSE-AND-SKIP every other internal-subset   *)
(* construct (`<!ELEMENT>`, `<!ATTLIST>`, `<!NOTATION>`, parameter    *)
(* entities `<!ENTITY % ...>`, external `<!ENTITY name SYSTEM/PUBLIC  *)
(* ...>`, comments, PIs, PEReferences, whitespace) structurally,      *)
(* without acting on them. An ExternalID on the DOCTYPE itself is     *)
(* skipped (respecting its quoted literals) but NOT loaded -- this is *)
(* a non-validating processor that reads nothing external. Validity   *)
(* (content models, ATTLIST enforcement, ID/IDREF), external-subset   *)
(* loading, conditional sections, and full parameter-entity semantics *)
(* are out of scope (Stage B / later).                               *)
(* ================================================================ *)

// Consume a quoted literal ("..." or '...') whose opening quote has
// already been consumed; `q` is the quote char. Returns the position
// after the closing quote.
let rec skip_quoted_literal (input:string) (pos:nat) (q:char) (fuel:nat)
  : Tot (parse_result unit) (decreases fuel) =
  if fuel = 0 then ParseFail "unterminated literal" pos
  else
    let len = fs_byte_length input in
    if pos >= len then ParseFail "unterminated literal" pos
    else if fs_byte_index input pos = q then ParseOk () (pos + 1)
    else skip_quoted_literal input (pos + 1) q (fuel - 1)

// Consume bytes up to and including the next top-level '>', treating
// quoted literals opaquely so a '>' inside a "..."/'...' literal does
// not terminate the declaration. Used to structurally skip markup
// declarations we do not interpret.
let rec skip_decl_to_gt (input:string) (pos:nat) (fuel:nat)
  : Tot (parse_result unit) (decreases fuel) =
  if fuel = 0 then ParseFail "unterminated markup declaration" pos
  else
    let len = fs_byte_length input in
    if pos >= len then ParseFail "unterminated markup declaration" pos
    else
      let ch = fs_byte_index input pos in
      if ch = '>' then ParseOk () (pos + 1)
      else if ch = '"' || ch = '\'' then
        begin match skip_quoted_literal input (pos + 1) ch (fuel - 1) with
        | ParseOk () pos' -> skip_decl_to_gt input pos' (fuel - 1)
        | ParseFail msg fpos -> ParseFail msg fpos
        end
      else skip_decl_to_gt input (pos + 1) (fuel - 1)

// Read the raw characters of an EntityValue up to (not including) the
// closing quote `q`, returning them verbatim (no reference expansion --
// that happens lazily at the reference site). Advances past the closer.
// Issue #325: "verbatim" has to mean byte-for-byte, so the value is one
// fs_byte_sub slice of the raw input. The old `list char` accumulator
// finished by String.string_of_list re-encoded each byte as a codepoint,
// so a DTD internal entity holding non-ASCII text expanded to mojibake.
let rec read_entity_value_raw (input:string) (start:nat) (pos:nat{pos >= start}) (q:char) (fuel:nat)
  : Tot (parse_result string) (decreases fuel) =
  if fuel = 0 then ParseFail "unterminated entity value" pos
  else
    let len = fs_byte_length input in
    if pos >= len then ParseFail "unterminated entity value" pos
    else
      let ch = fs_byte_index input pos in
      if ch = q then ParseOk (fs_byte_sub input start (pos - start)) (pos + 1)
      else read_entity_value_raw input start (pos + 1) q (fuel - 1)

// Consume a PEReference '%' Name ';' inside the internal subset (we do
// not expand it -- Stage A). `pos` points just after the '%'.
let rec skip_pe_reference (input:string) (pos:nat) (fuel:nat)
  : Tot (parse_result unit) (decreases fuel) =
  if fuel = 0 then ParseFail "unterminated parameter-entity reference" pos
  else
    let len = fs_byte_length input in
    if pos >= len then ParseFail "unterminated parameter-entity reference" pos
    else if fs_byte_index input pos = ';' then ParseOk () (pos + 1)
    else skip_pe_reference input (pos + 1) (fuel - 1)

// Parse one `<!ENTITY ...>` declaration (the leading "<!ENTITY" is at
// `pos`). A general internal entity (`<!ENTITY Name "value">`) is added
// to `ents` (first declaration wins; a later duplicate is ignored, per
// XML 1.0 §4.2). Parameter entities (`<!ENTITY % ...>`) and external
// entities (SYSTEM/PUBLIC) are skipped without adding a binding.
let parse_entity_decl (input:string) (pos:nat) (ents:dtd_entity_table)
  : parse_result dtd_entity_table =
  let len = fs_byte_length input in
  match pstring "<!ENTITY" input pos with
  | ParseFail msg fpos -> ParseFail msg fpos
  | ParseOk _ p1 ->
    begin match ptake_while1_pos is_xml_space input p1 with
    | ParseFail msg fpos -> ParseFail msg fpos
    | ParseOk _ p2 ->
      if p2 < len && fs_byte_index input p2 = '%' then
        // Parameter entity -- skip structurally.
        begin match skip_decl_to_gt input p2 (len + 1) with
        | ParseOk () p' -> ParseOk ents p'
        | ParseFail msg fpos -> ParseFail msg fpos
        end
      else
        begin match parse_xml_name input p2 with
        | ParseFail msg fpos -> ParseFail msg fpos
        | ParseOk name p3 ->
          begin match ptake_while1_pos is_xml_space input p3 with
          | ParseFail msg fpos -> ParseFail msg fpos
          | ParseOk _ p4 ->
            if p4 < len && (fs_byte_index input p4 = '"' || fs_byte_index input p4 = '\'') then
              let q = fs_byte_index input p4 in
              begin match read_entity_value_raw input (p4 + 1) (p4 + 1) q (len + 1) with
              | ParseFail msg fpos -> ParseFail msg fpos
              | ParseOk rawval p5 ->
                begin match skip_decl_to_gt input p5 (len + 1) with
                | ParseFail msg fpos -> ParseFail msg fpos
                | ParseOk () p6 ->
                  let ents' =
                    match lookup_entity name ents with
                    | Some _ -> ents
                    | None -> (name, rawval) :: ents
                  in
                  ParseOk ents' p6
                end
              end
            else
              // External entity (SYSTEM/PUBLIC) or otherwise -- skip.
              begin match skip_decl_to_gt input p4 (len + 1) with
              | ParseOk () p' -> ParseOk ents p'
              | ParseFail msg fpos -> ParseFail msg fpos
              end
          end
        end
    end

// ---- ATTLIST ID-type recognition (best-effort, non-failing) --------
// The declared-attributes-of-type-ID table maps (element-name,
// attribute-name) pairs whose ATTLIST AttType keyword is exactly "ID"
// (NOT IDREF/IDREFS). XPath.Eval.id() and XSLT id()-anchored match
// patterns use it to find the element bearing a given unique identifier.
// This scanner runs OVER the region a `<!ATTLIST ... >` declaration
// occupies -- the same span skip_decl_to_gt consumes -- and NEVER moves
// the parser position or changes accept/reject: it only reads out ID
// pairs. Any structural surprise stops it early (fewer pairs), so a
// malformed or exotic ATTLIST can lose IDs but can never corrupt the
// well-formedness parse. Scoped to the internal subset (no external
// DTD, no parameter-entity expansion in ATTLIST bodies).

// Skip XML spaces up to (not past) `gt`.
let rec skip_ws_to (input:string) (pos:nat) (gt:nat) (fuel:nat) : Tot nat (decreases fuel) =
  if fuel = 0 then pos
  else if pos >= gt then pos
  else if is_xml_space (fs_byte_index input pos) then skip_ws_to input (pos + 1) gt (fuel - 1)
  else pos

// From a '(' at `pos`, skip to just after the matching ')'. `depth` 0 at
// entry; bounded by `gt`.
let rec skip_parens_to (input:string) (pos:nat) (gt:nat) (depth:nat) (fuel:nat) : Tot nat (decreases fuel) =
  if fuel = 0 then pos
  else if pos >= gt then pos
  else
    let c = fs_byte_index input pos in
    if c = '(' then skip_parens_to input (pos + 1) gt (depth + 1) (fuel - 1)
    else if c = ')' then (if depth <= 1 then pos + 1 else skip_parens_to input (pos + 1) gt (depth - 1) (fuel - 1))
    else skip_parens_to input (pos + 1) gt depth (fuel - 1)

// From just after an opening quote `q`, skip to just after the closer.
let rec skip_quoted_to (input:string) (pos:nat) (gt:nat) (q:char) (fuel:nat) : Tot nat (decreases fuel) =
  if fuel = 0 then pos
  else if pos >= gt then pos
  else if fs_byte_index input pos = q then pos + 1
  else skip_quoted_to input (pos + 1) gt q (fuel - 1)

// Skip an AttDef DefaultDecl: `#REQUIRED` | `#IMPLIED` | (`#FIXED` S)? AttValue.
let skip_default_decl (input:string) (pos:nat) (gt:nat) : nat =
  if pos >= gt then pos
  else
    let c = fs_byte_index input pos in
    if c = '#' then
      (match parse_xml_name input (pos + 1) with
       | ParseOk kw p2 ->
         if kw = "FIXED" then
           let p3 = skip_ws_to input p2 gt gt in
           if p3 < gt && (let q = fs_byte_index input p3 in q = '"' || q = '\'')
           then skip_quoted_to input (p3 + 1) gt (fs_byte_index input p3) gt
           else p2
         else p2
       | ParseFail _ _ -> pos + 1)
    else if c = '"' || c = '\'' then skip_quoted_to input (pos + 1) gt c gt
    else pos

// Iterate over the AttDefs of one ATTLIST for element `elem`, collecting
// (elem, attr) pairs whose AttType is exactly "ID".
let rec scan_attdefs (input:string) (pos:nat) (gt:nat) (elem:string) (fuel:nat) (acc:list (string & string))
  : Tot (list (string & string)) (decreases fuel) =
  if fuel = 0 then acc
  else
    let pos = skip_ws_to input pos gt gt in
    if pos >= gt || fs_byte_index input pos = '>' then acc
    else
      match parse_xml_name input pos with
      | ParseFail _ _ -> acc
      | ParseOk attr p2 ->
        let p2 = skip_ws_to input p2 gt gt in
        if p2 < gt && fs_byte_index input p2 = '(' then
          // Enumeration type (never ID).
          let p3 = skip_parens_to input p2 gt 0 gt in
          let p4 = skip_default_decl input (skip_ws_to input p3 gt gt) gt in
          scan_attdefs input p4 gt elem (fuel - 1) acc
        else
          match parse_xml_name input p2 with
          | ParseFail _ _ -> acc
          | ParseOk typ p3 ->
            let (p3b, is_id) =
              if typ = "NOTATION" then
                let pn = skip_ws_to input p3 gt gt in
                (if pn < gt && fs_byte_index input pn = '(' then (skip_parens_to input pn gt 0 gt, false) else (p3, false))
              else (p3, typ = "ID")
            in
            let p4 = skip_default_decl input (skip_ws_to input p3b gt gt) gt in
            let acc' = if is_id then (elem, attr) :: acc else acc in
            scan_attdefs input p4 gt elem (fuel - 1) acc'

// Scan a `<!ATTLIST ... >` region [pos, gt). `pos` is just after the
// "<!ATTLIST" keyword; `gt` is the position just after the closing '>'.
let scan_attlist_ids (input:string) (pos:nat) (gt:nat) (acc:list (string & string))
  : list (string & string) =
  let pos = skip_ws_to input pos gt gt in
  match parse_xml_name input pos with
  | ParseFail _ _ -> acc
  | ParseOk elem p1 -> scan_attdefs input p1 gt elem gt acc

// Parse the internal subset body (from just after '[') up to and
// including the ']'. Collects general entity declarations AND the
// (element, attribute) pairs declared with ATTLIST AttType ID; skips the
// rest structurally.
let rec parse_int_subset (input:string) (pos:nat) (ents:dtd_entity_table) (ids:list (string & string)) (fuel:nat)
  : Tot (parse_result (dtd_entity_table & list (string & string))) (decreases fuel) =
  if fuel = 0 then ParseFail "internal subset too long" pos
  else
    let len = fs_byte_length input in
    if pos >= len then ParseFail "unterminated internal subset (missing ']')" pos
    else
      let ch = fs_byte_index input pos in
      if ch = ']' then ParseOk (ents, ids) (pos + 1)
      else if is_xml_space ch then parse_int_subset input (pos + 1) ents ids (fuel - 1)
      else if ch = '%' then
        begin match skip_pe_reference input (pos + 1) (len - pos + 1) with
        | ParseOk () pos' -> parse_int_subset input pos' ents ids (fuel - 1)
        | ParseFail msg fpos -> ParseFail msg fpos
        end
      else if ch = '<' then
        begin match pstring "<!--" input pos with
        | ParseOk _ _ ->
          begin match parse_xml_comment input pos with
          | ParseOk _ pos' -> parse_int_subset input pos' ents ids (fuel - 1)
          | ParseFail msg fpos -> ParseFail msg fpos
          end
        | ParseFail _ _ ->
          begin match pstring "<!ENTITY" input pos with
          | ParseOk _ _ ->
            begin match parse_entity_decl input pos ents with
            | ParseOk ents' pos' -> parse_int_subset input pos' ents' ids (fuel - 1)
            | ParseFail msg fpos -> ParseFail msg fpos
            end
          | ParseFail _ _ ->
            begin match pstring "<?" input pos with
            | ParseOk _ _ ->
              begin match parse_xml_pi input pos with
              | ParseOk _ pos' -> parse_int_subset input pos' ents ids (fuel - 1)
              | ParseFail msg fpos -> ParseFail msg fpos
              end
            | ParseFail _ _ ->
              begin match pstring "<!" input pos with
              | ParseOk _ _ ->
                // <!ELEMENT ...> / <!ATTLIST ...> / <!NOTATION ...> and
                // any other markup declaration -- skip structurally, but
                // read ID-typed attributes out of an ATTLIST first.
                begin match skip_decl_to_gt input pos (len - pos + 1) with
                | ParseOk () pos' ->
                  let ids' =
                    match pstring "<!ATTLIST" input pos with
                    | ParseOk _ p_after -> scan_attlist_ids input p_after pos' ids
                    | ParseFail _ _ -> ids
                  in
                  parse_int_subset input pos' ents ids' (fuel - 1)
                | ParseFail msg fpos -> ParseFail msg fpos
                end
              | ParseFail _ _ -> ParseFail "malformed internal subset declaration" pos
              end
            end
          end
        end
      else ParseFail "unexpected character in internal subset" pos

// Scan (respecting quoted literals) up to the next top-level '[' or '>'
// without consuming it -- used to step over the DOCTYPE's optional
// ExternalID (SYSTEM/PUBLIC + literals) and surrounding whitespace.
let rec skip_to_subset_or_gt (input:string) (pos:nat) (fuel:nat)
  : Tot (parse_result unit) (decreases fuel) =
  if fuel = 0 then ParseFail "unterminated DOCTYPE" pos
  else
    let len = fs_byte_length input in
    if pos >= len then ParseFail "unterminated DOCTYPE" pos
    else
      let ch = fs_byte_index input pos in
      if ch = '[' || ch = '>' then ParseOk () pos
      else if ch = '"' || ch = '\'' then
        begin match skip_quoted_literal input (pos + 1) ch (fuel - 1) with
        | ParseOk () pos' -> skip_to_subset_or_gt input pos' (fuel - 1)
        | ParseFail msg fpos -> ParseFail msg fpos
        end
      else skip_to_subset_or_gt input (pos + 1) (fuel - 1)

// doctypedecl. On success returns the collected general-entity table and
// the position just after the closing '>'. Fails (ParseFail) if there is
// no '<!DOCTYPE' here, or if the DOCTYPE is structurally malformed.
let parse_doctype (input:string) (pos:nat) : parse_result (dtd_entity_table & list (string & string)) =
  let len = fs_byte_length input in
  match pstring "<!DOCTYPE" input pos with
  | ParseFail msg fpos -> ParseFail msg fpos
  | ParseOk _ p1 ->
    begin match ptake_while1_pos is_xml_space input p1 with
    | ParseFail msg fpos -> ParseFail msg fpos
    | ParseOk _ p2 ->
      begin match parse_xml_name input p2 with
      | ParseFail msg fpos -> ParseFail msg fpos
      | ParseOk _root p3 ->
        begin match skip_to_subset_or_gt input p3 (len + 1) with
        | ParseFail msg fpos -> ParseFail msg fpos
        | ParseOk () p4 ->
          if p4 < len && fs_byte_index input p4 = '[' then
            begin match parse_int_subset input (p4 + 1) [] [] (len + 1) with
            | ParseFail msg fpos -> ParseFail msg fpos
            | ParseOk (ents, ids) p5 ->
              begin match skip_xml_space input p5 with
              | ParseFail msg fpos -> ParseFail msg fpos
              | ParseOk () p6 ->
                if p6 < len && fs_byte_index input p6 = '>' then ParseOk (ents, ids) (p6 + 1)
                else ParseFail "DOCTYPE: expected '>' after internal subset" p6
              end
            end
          else if p4 < len && fs_byte_index input p4 = '>' then
            ParseOk ([], []) (p4 + 1)
          else ParseFail "DOCTYPE: expected '[' or '>'" p4
        end
      end
    end


(* ================================================================ *)
(* Misc / Prolog helpers                                             *)
(* ================================================================ *)

// Prolog ::= XMLDecl? Misc* (doctypedecl Misc*)? , Misc ::= Comment | PI | S.
// PIs are legal Misc in the prolog (XML 1.0 §2.1/§2.8), exactly as they
// are in the epilog -- so this mirrors skip_epilog_misc and consumes any
// non-"xml"-target PI here. parse_xml_pi itself rejects the reserved
// "xml" target (any case), so a second XML-declaration-shaped token in
// the prolog fails to parse as Misc and correctly leaves the document to
// be rejected (the "XML declaration may not follow content" cluster).
// The PI is not attached to the returned tree (Parser.XML yields the
// root element, no document node), but consuming it un-skips the XSLT
// stylesheets that open with a `<?xml-stylesheet?>`-style prolog PI and
// stops the parser choking on an unconsumed prolog `<?`.
//
// Profile note: the ibm xml-1.1 restricted-C1-control cluster and the
// eduni rmt-ns10 colon-in-PITarget case used to be rejected here ONLY as
// a side effect of that prolog-`<?` choke -- a wrong-reason rejection.
// Under this parser's declared profile (XML 1.0, non-namespace) those
// documents are genuinely well-formed, so a correct parser accepts them;
// their not-wf verdict holds only under XML 1.1 / Namespaces in XML,
// checked elsewhere (declared-version gating / XML.Namespaces), not by
// silently choking in the prolog.
let rec skip_misc (input:string) (pos:nat) (fuel:nat)
  : Tot (parse_result unit) (decreases fuel) =
  if fuel = 0 then ParseOk () pos
  else
    match skip_xml_space input pos with
    | ParseOk () pos1 ->
      begin match parse_xml_comment input pos1 with
      | ParseOk _ pos2 -> skip_misc input pos2 (fuel - 1)
      | ParseFail _ _ ->
        begin match parse_xml_pi input pos1 with
        | ParseOk _ pos2 -> skip_misc input pos2 (fuel - 1)
        | ParseFail _ _ -> ParseOk () pos1
        end
      end
    | ParseFail msg fpos -> ParseFail msg fpos

// Epilog ::= Misc* , Misc ::= Comment | PI | S. After the document
// element, ONLY whitespace/comments/(non-"xml"-target) PIs may
// appear -- a second root element, stray text, a CDATA section, a
// character reference, or an XML-declaration-shaped token are all
// illegal (xmlconf's "epilog/trailing content" cluster, 11 tests).
// parse_xml_pi already rejects the reserved "xml" target (any case),
// so an XML-declaration-shaped token here correctly fails to parse as
// Misc rather than being silently accepted as a PI.
let rec skip_epilog_misc (input:string) (pos:nat) (fuel:nat)
  : Tot (parse_result unit) (decreases fuel) =
  if fuel = 0 then ParseOk () pos
  else
    match skip_xml_space input pos with
    | ParseOk () pos1 ->
      begin match parse_xml_comment input pos1 with
      | ParseOk _ pos2 -> skip_epilog_misc input pos2 (fuel - 1)
      | ParseFail _ _ ->
        begin match parse_xml_pi input pos1 with
        | ParseOk _ pos2 -> skip_epilog_misc input pos2 (fuel - 1)
        | ParseFail _ _ -> ParseOk () pos1
        end
      end
    | ParseFail msg fpos -> ParseFail msg fpos


// collect_misc / collect_epilog_misc mirror skip_misc / skip_epilog_misc
// EXACTLY -- same sub-parsers (parse_xml_comment / parse_xml_pi), same
// consume decisions, same failure propagation -- so the document-level
// accept/reject verdict (the xml-conformance gate) is byte-for-byte
// unchanged. The only difference is that they REMEMBER the Comment / PI
// nodes they consume (in document order) rather than discarding them.
// Parser.XML has no document node; the XPath/XSLT layer builds one, and
// its children are the prolog/epilog Comment and PI nodes plus the root
// element. Whitespace between them is NOT a node at the document level
// (XML has no document-level text nodes), so only Comment and PI Misc
// are accumulated -- exactly the two Misc kinds skip_misc recognises.
let rec collect_misc (input:string) (pos:nat) (fuel:nat) (acc:list xml_node)
  : Tot (parse_result (list xml_node)) (decreases fuel) =
  if fuel = 0 then ParseOk (rev acc) pos
  else
    match skip_xml_space input pos with
    | ParseOk () pos1 ->
      begin match parse_xml_comment input pos1 with
      | ParseOk node pos2 -> collect_misc input pos2 (fuel - 1) (node :: acc)
      | ParseFail _ _ ->
        begin match parse_xml_pi input pos1 with
        | ParseOk node pos2 -> collect_misc input pos2 (fuel - 1) (node :: acc)
        | ParseFail _ _ -> ParseOk (rev acc) pos1
        end
      end
    | ParseFail msg fpos -> ParseFail msg fpos

let rec collect_epilog_misc (input:string) (pos:nat) (fuel:nat) (acc:list xml_node)
  : Tot (parse_result (list xml_node)) (decreases fuel) =
  if fuel = 0 then ParseOk (rev acc) pos
  else
    match skip_xml_space input pos with
    | ParseOk () pos1 ->
      begin match parse_xml_comment input pos1 with
      | ParseOk node pos2 -> collect_epilog_misc input pos2 (fuel - 1) (node :: acc)
      | ParseFail _ _ ->
        begin match parse_xml_pi input pos1 with
        | ParseOk node pos2 -> collect_epilog_misc input pos2 (fuel - 1) (node :: acc)
        | ParseFail _ _ -> ParseOk (rev acc) pos1
        end
      end
    | ParseFail msg fpos -> ParseFail msg fpos


(* ================================================================ *)
(* Document-level entry point                                        *)
(* ================================================================ *)

// Skip a leading UTF-8 byte-order-mark (the 3-byte sequence EF BB BF)
// at byte offset 0 ONLY. XML 1.0 SS4.3.3 / Appendix F: a UTF-8 entity
// "may but need not" begin with this BOM, and it is not part of the
// document's markup or character data -- a conforming processor
// consumes it before parsing begins. This is checked strictly at
// position 0; the same 3 bytes appearing anywhere else in the input
// are ordinary (non-BOM) character data and are left untouched, so a
// document with no leading BOM parses exactly as before (returns 0,
// identical to the prior hardcoded start position).
let skip_utf8_bom (input:string) : nat =
  if fs_byte_length input >= 3 &&
     fs_byte_at input 0 = 0xEF &&
     fs_byte_at input 1 = 0xBB &&
     fs_byte_at input 2 = 0xBF
  then 3
  else 0

(* ================================================================ *)
(* Line-ending normalization (XML 1.0 SS2.11)                        *)
(*                                                                    *)
(* "To simplify the tasks of applications, the XML processor MUST     *)
(* behave as if it normalized all line breaks in external parsed      *)
(* entities (including the document entity) on input, before parsing, *)
(* by translating both the two-character sequence #xD #xA and any     *)
(* #xD that is not followed by #xA to a single #xA character." This   *)
(* is unconditional -- every processor, every input, not a validation *)
(* or DTD-triggered behavior -- so it is applied once, up front, to    *)
(* the whole input string, before the BOM/declaration/element parsers *)
(* ever see a byte. \r and \n are single-byte ASCII (0x0D / 0x0A), so *)
(* a byte-level scan is safe here -- it can never misidentify a UTF-8 *)
(* continuation or lead byte (0x80+) as one of these (same reasoning  *)
(* Parser.FastString's byte-indexed primitives rely on elsewhere in    *)
(* this module).                                                      *)
(* ================================================================ *)

let rec normalize_line_endings_acc (input:string) (pos:nat) (acc:list string) (fuel:nat)
  : Tot string (decreases fuel) =
  if fuel = 0 then String.concat "" (List.Tot.rev acc)
  else
    let len = fs_byte_length input in
    if pos >= len then String.concat "" (List.Tot.rev acc)
    else
      let ch = fs_byte_index input pos in
      if ch = '\r' then
        // #xD #xA -> single #xA (CRLF collapses, consuming both bytes);
        // any other #xD (including at end of input) -> single #xA.
        if pos + 1 < len && fs_byte_index input (pos + 1) = '\n' then
          normalize_line_endings_acc input (pos + 2) ("\n" :: acc) (fuel - 1)
        else
          normalize_line_endings_acc input (pos + 1) ("\n" :: acc) (fuel - 1)
      else
        match ptake_while_pos (fun c -> c <> '\r') input pos with
        | ParseOk s pos' ->
          if fs_byte_length s > 0 then
            normalize_line_endings_acc input pos' (s :: acc) (fuel - 1)
          else
            normalize_line_endings_acc input (pos + 1) (String.string_of_char ch :: acc) (fuel - 1)
        | ParseFail _ _ ->
          normalize_line_endings_acc input (pos + 1) (String.string_of_char ch :: acc) (fuel - 1)

// Translate every #xD #xA pair and every standalone #xD to a single #xA,
// per XML 1.0 SS2.11. Applied once, to the whole raw document, before any
// other parsing step.
let normalize_line_endings (input:string) : string =
  let len = fs_byte_length input in
  normalize_line_endings_acc input 0 [] (len + 1)

let parse_xml_document (input0:string) : option xml_node =
  // XML 1.0 SS2.11 line-ending normalization MUST happen before parsing,
  // unconditionally, for every input -- see normalize_line_endings above.
  let input = normalize_line_endings input0 in
  let len = fs_byte_length input in
  let fuel = len + 1 in
  // The XML declaration, if present, must be the very first thing in
  // the document -- no leading whitespace is skipped before trying it
  // (XML 1.0 §2.8: "S cannot occur before the prolog" / the decl
  // can't be preceded by anything -- o-p22fail1, not-wf-sa-147). A
  // leading UTF-8 BOM is consumed first (it is not part of the
  // prolog's grammar at all), then the declaration is tried
  // immediately after it. If there is no declaration there, that's
  // simply the common no-decl case; skip_misc below still tolerates
  // leading whitespace and comments before the root element exactly
  // as before.
  let bom_pos = skip_utf8_bom input in
  let pos1 =
    match parse_xml_declaration input bom_pos with
    | ParseOk _attrs pos' -> pos'
    | ParseFail _ _ -> bom_pos
  in
  begin match skip_misc input pos1 fuel with
  | ParseOk () pos2 ->
    // Prolog ::= XMLDecl? Misc* (doctypedecl Misc*)?. At most one
    // doctypedecl may appear here, before the root element. If the
    // DOCTYPE is present and well-formed, collect its general-entity
    // table; if there is no DOCTYPE, parse_doctype fails fast and we
    // continue with an empty table. A DOCTYPE that IS present but
    // structurally malformed leaves pos at the '<!DOCTYPE', where
    // parse_xml_element rejects it (the document is then not-wf).
    let (ents, pos_dt) =
      match parse_doctype input pos2 with
      | ParseOk (e, _ids) p -> (e, p)
      | ParseFail _ _ -> ([], pos2)
    in
    begin match skip_misc input pos_dt fuel with
    | ParseOk () pos3 ->
      begin match parse_xml_element ents input pos3 fuel with
      | ParseOk root pos4 ->
        begin match skip_epilog_misc input pos4 fuel with
        | ParseOk () pos5 ->
          if pos5 >= fs_byte_length input then Some root else None
        | ParseFail _ _ -> None
        end
      | ParseFail _ _ -> None
      end
    | ParseFail _ _ -> None
    end
  | ParseFail _ _ -> None
  end

// Document-node aware entry point. Parses EXACTLY as parse_xml_document
// (identical accept/reject flow -- see collect_misc), but returns the
// full ordered child list of the document node: the prolog Comment/PI
// Misc, then the root element, then the epilog Comment/PI Misc. A caller
// that only wants the root element uses parse_xml_document; a caller that
// needs the document-node model (XPath's `/`, XSLT's `//comment()` over
// prolog/epilog, the identity transform copying a leading comment) uses
// this. `None` on exactly the same inputs parse_xml_document rejects.
let parse_xml_document_children (input0:string) : option (list xml_node) =
  // See normalize_line_endings above parse_xml_document (XML 1.0 SS2.11):
  // applied unconditionally, before any other parsing step.
  let input = normalize_line_endings input0 in
  let len = fs_byte_length input in
  let fuel = len + 1 in
  // See skip_utf8_bom above parse_xml_document: consume a leading
  // UTF-8 BOM (byte offset 0 only) before trying the XML declaration,
  // so this entry point accepts/rejects identically to
  // parse_xml_document on BOM-prefixed input.
  let bom_pos = skip_utf8_bom input in
  let pos1 =
    match parse_xml_declaration input bom_pos with
    | ParseOk _attrs pos' -> pos'
    | ParseFail _ _ -> bom_pos
  in
  begin match collect_misc input pos1 fuel [] with
  | ParseOk pre1 pos2 ->
    let (ents, pos_dt) =
      match parse_doctype input pos2 with
      | ParseOk (e, _ids) p -> (e, p)
      | ParseFail _ _ -> ([], pos2)
    in
    begin match collect_misc input pos_dt fuel [] with
    | ParseOk pre2 pos3 ->
      begin match parse_xml_element ents input pos3 fuel with
      | ParseOk root pos4 ->
        begin match collect_epilog_misc input pos4 fuel [] with
        | ParseOk post pos5 ->
          if pos5 >= fs_byte_length input
          then Some (append pre1 (append pre2 (root :: post)))
          else None
        | ParseFail _ _ -> None
        end
      | ParseFail _ _ -> None
      end
    | ParseFail _ _ -> None
    end
  | ParseFail _ _ -> None
  end

// Document-node aware entry point that ALSO returns the internal-subset
// ATTLIST ID-type declarations as (element-name, attribute-name) pairs.
// Parses identically to parse_xml_document_children (same accept/reject
// flow); the extra component is the id() index substrate. Empty pair list
// when there is no DOCTYPE or no ID-typed attribute.
let parse_xml_document_children_with_ids (input0:string) : option (list xml_node & list (string & string)) =
  // See normalize_line_endings above parse_xml_document (XML 1.0 SS2.11):
  // applied unconditionally, before any other parsing step.
  let input = normalize_line_endings input0 in
  let len = fs_byte_length input in
  let fuel = len + 1 in
  // See skip_utf8_bom above parse_xml_document: consume a leading
  // UTF-8 BOM (byte offset 0 only) before trying the XML declaration,
  // so this entry point accepts/rejects identically to
  // parse_xml_document on BOM-prefixed input.
  let bom_pos = skip_utf8_bom input in
  let pos1 =
    match parse_xml_declaration input bom_pos with
    | ParseOk _attrs pos' -> pos'
    | ParseFail _ _ -> bom_pos
  in
  begin match collect_misc input pos1 fuel [] with
  | ParseOk pre1 pos2 ->
    let (ents, ids, pos_dt) =
      match parse_doctype input pos2 with
      | ParseOk (e, idl) p -> (e, idl, p)
      | ParseFail _ _ -> ([], [], pos2)
    in
    begin match collect_misc input pos_dt fuel [] with
    | ParseOk pre2 pos3 ->
      begin match parse_xml_element ents input pos3 fuel with
      | ParseOk root pos4 ->
        begin match collect_epilog_misc input pos4 fuel [] with
        | ParseOk post pos5 ->
          if pos5 >= fs_byte_length input
          then Some (append pre1 (append pre2 (root :: post)), ids)
          else None
        | ParseFail _ _ -> None
        end
      | ParseFail _ _ -> None
      end
    | ParseFail _ _ -> None
    end
  | ParseFail _ _ -> None
  end


(* ================================================================ *)
(* Convenience accessors                                             *)
(* ================================================================ *)

let element_tag (node:xml_node) : option string =
  match node with
  | XElement tag _ _ -> Some tag
  | _ -> None

let element_attrs (node:xml_node) : list xml_attribute =
  match node with
  | XElement _ attrs _ -> attrs
  | _ -> []

let element_children (node:xml_node) : list xml_node =
  match node with
  | XElement _ _ children -> children
  | _ -> []

let find_attr (name:string) (attrs:list xml_attribute) : option string =
  match List.Tot.find (fun (a:xml_attribute) -> a.attr_name = name) attrs with
  | Some a -> Some a.attr_value
  | None -> None

let rec text_content (node:xml_node) : Tot string (decreases node) =
  match node with
  | XText t -> t
  | XCDATA t -> t
  | XComment _ -> ""
  | XPI _ _ -> ""
  | XElement _ _ children ->
    String.concat "" (text_content_list children)

and text_content_list (nodes:list xml_node) : Tot (list string) (decreases nodes) =
  match nodes with
  | [] -> []
  | hd :: tl -> text_content hd :: text_content_list tl

let child_elements (tag:string) (node:xml_node) : list xml_node =
  match node with
  | XElement _ _ children ->
    List.Tot.filter (fun (child:xml_node) ->
      match child with
      | XElement t _ _ -> t = tag
      | _ -> false) children
  | _ -> []

let child_element (tag:string) (node:xml_node) : option xml_node =
  match child_elements tag node with
  | hd :: _ -> Some hd
  | [] -> None

let all_child_elements (node:xml_node) : list xml_node =
  match node with
  | XElement _ _ children ->
    List.Tot.filter (fun (child:xml_node) ->
      match child with
      | XElement _ _ _ -> true
      | _ -> false) children
  | _ -> []
