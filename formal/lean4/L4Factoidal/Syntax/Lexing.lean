/-
L4Factoidal.Syntax.Lexing — shared lexical primitives for the RDF 1.1 /
RDF 1.2 concrete syntaxes (N-Triples, N-Quads).

Port of the character-level machinery in `formal/fstar/Parser.NTriples.fst`
(hex-digit decoding, `\uXXXX`/`\UXXXXXXXX` codepoint validation, IRIREF /
STRING_LITERAL_QUOTED / LANGTAG / BLANK_NODE_LABEL scanning, whitespace and
comment skipping). The F* source works byte-by-byte over `string` via
`Parser.FastString` (an `assume val` primitive layer realising byte-indexed
access over the OCaml runtime string — see the assumption report in
`PORT_NOTES.md`); this port works CODEPOINT-by-codepoint directly over
`List Char`, because Lean's `Char` already IS a validated Unicode scalar
value and `String.toList` already decodes UTF-8 for us. That collapses the
F* source's separate byte-scan / codepoint-scan code paths
(`is_bnode_char_cp` reading raw bytes via `fs_cp_at`, the ASCII fast-path
vs. slow-path split in `parse_iri_body_acc` / `parse_string_body`) into one
codepoint-level definition each — a genuine simplification available only
because Lean's list-of-Char representation is not byte-oriented.

Grammar productions ported (RDF 1.1 N-Triples, https://www.w3.org/TR/n-triples/,
grammar productions also shared by RDF 1.1 N-Quads):
  [8]    IRIREF
  [9]    STRING_LITERAL_QUOTED
  [10]   LANGTAG
  [141s] BLANK_NODE_LABEL
  [153s] ECHAR   (escaped char: \t \b \n \r \f \" \' \\)
  [26]   UCHAR   (\uXXXX | \UXXXXXXXX)
Plus RDF 1.2 additions (W3C Working Draft, epic #305 in the F* tree):
  the `@lang--dir` directional-literal suffix on LANGTAG (`ltr`/`rtl` only).

NOT ported here (deliberately out of scope for a spec-level lexer):
  - the F* module's FAST-PATH / SLOW-PATH split (`scan_iri_end` /
    `parse_iri_body_acc`, `scan_string_fast` / `parse_string_body`) — a
    perf optimisation over byte buffers; this port has one code path per
    reader.
  - the `validate_*` / `count_*` allocation-free scanners (`--count` mode
    perf machinery) — CLI/performance pragmatics, not semantics.
  - RDF 1.2's inline-whitespace relaxation between a closing quote and a
    following `@lang`/`^^datatype` (W3C c14n suite `extra_whitespace-*`
    tests). Noted as a known gap in `PORT_NOTES.md`; RDF 1.1 literals never
    had this relaxation and it is not exercised by the round-trip theorems.

Every reader below is TOTAL: readers that must recurse do so either by
plain structural recursion on the `List Char` argument (nested constructor
patterns consume a syntactically-provable-shorter suffix, which Lean's
termination checker accepts directly — no fuel needed, unlike the F*
source's byte-position/fuel style) or, for the one genuinely open-ended
recursion (RDF 1.2 triple-term nesting, in `Syntax.NTriples`), an explicit
fuel `Nat` exactly where the F* source also needed one
(`parse_object_12_f`'s `decreases fuel`).
-/

namespace L4Factoidal.Syntax

/-! ## Parse errors — message + position (RFC: W3C negative-syntax tests
exist to check REJECTION, so a reviewer must be able to see WHY and WHERE
a parse failed, not just that it failed). Position is a 0-based codepoint
offset from the start of the document, matching the F* source's `pos:nat`
byte offset (codepoint offset here, since Lean's `List Char` is already
codepoint-indexed). -/

/-- A parse failure: a human-readable reason and the codepoint offset at
which it was detected. -/
structure ParseError where
  msg : String
  pos : Nat
  deriving DecidableEq, Repr

instance : ToString ParseError :=
  ⟨fun e => s!"parse error at offset {e.pos}: {e.msg}"⟩

/-! ## Hex digits -/

/-- Hex-digit value, or `none` for a non-hex character. Port of
`hex_val_opt` — deliberately `Option`, not the "0 for non-hex" fallback
`hex_val` the F* source keeps only for Turtle/TriG backward compatibility;
every caller here treats an invalid hex digit as a parse error, never a
silent 0. -/
def hexVal (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else none

/-! ## Codepoint validity — [26] UCHAR decode target

A Unicode scalar value excludes the UTF-16 surrogate range
`U+D800..U+DFFF` (RDF 1.1 N-Triples §"Escape Sequences" defers to Unicode
scalar values, same bound the F* source's `valid_codepoint` checks:
`cp <= 0xD7FF || (cp >= 0xE000 && cp <= 0x10FFFF)`). Lean core's own
`Nat.isValidChar` (`Init/Prelude.lean`) states the IDENTICAL bound
(`n < 0xd800 ∨ (0xdfff < n ∧ n < 0x110000)`), so `codepointToChar` below
uses it directly instead of re-deriving an equivalent Bool predicate. -/

/-- Decode a validated `\uXXXX` / `\UXXXXXXXX` codepoint into a `Char`.
Port of `safe_char_of_int`, but honest where the F* source was not: F*'s
`safe_char_of_int` substitutes U+FFFD for an out-of-range codepoint
(matching the W3C REPLACEMENT CHARACTER convention for byte-level decode
errors), which is defensible for raw-byte UTF-8 decode but wrong for an
EXPLICIT escape sequence the input author wrote — a malformed `\uD800`
is a SYNTAX ERROR, not a request for U+FFFD. This port therefore returns
`Except.error`, never a silent substitution, for any surrogate or
out-of-range escape. -/
def codepointToChar (cp : Nat) (pos : Nat) : Except ParseError Char :=
  if h : cp.isValidChar then
    .ok (Char.ofNatAux cp h)
  else
    .error ⟨s!"surrogate or out-of-range codepoint U+{String.ofList (Nat.toDigits 16 cp)} in escape", pos⟩

/-! ## IRIREF — [8] IRIREF

`IRIREF ::= '<' ([^#x00-#x20<>"{}|^\`\\] | UCHAR)* '>'` -/

/-- The ten codepoints RFC 3987 §2.2 forbids inside an IRI reference and
that N-Triples additionally forbids escaping AROUND (checked both for
literal characters and for the decoded value of a `\u`/`\U` escape — an
escaped space or `<` is exactly as ill-formed as a literal one). Port of
`is_iri_forbidden_codepoint`. -/
def isIriForbiddenCodepoint (cp : Nat) : Bool :=
  cp = 0x20 || cp = 0x3C || cp = 0x3E || cp = 0x22 ||
  cp = 0x7B || cp = 0x7D || cp = 0x7C || cp = 0x5C ||
  cp = 0x5E || cp = 0x60

/-- IRIREF body: the content between `<` and `>`, decoding `\u`/`\U`
UCHAR escapes and rejecting raw control characters (`<= 0x20`), the
forbidden-codepoint set (both raw and escaped), and any escape other than
`\u`/`\U` (IRIREF admits ONLY UCHAR, never ECHAR — `\"` is not legal
inside `<...>`). Structural recursion on the input list: every branch
either terminates or recurses on a direct constructor-pattern suffix. -/
def readIriRefBody (pos : Nat) : List Char → Except ParseError (String × Nat × List Char)
  | [] => .error ⟨"unterminated IRIREF (expected '>')", pos⟩
  | '>' :: rest => .ok ("", pos + 1, rest)
  | '\\' :: 'u' :: h0 :: h1 :: h2 :: h3 :: rest =>
      match hexVal h0, hexVal h1, hexVal h2, hexVal h3 with
      | some d0, some d1, some d2, some d3 =>
          let cp := d0 * 4096 + d1 * 256 + d2 * 16 + d3
          if isIriForbiddenCodepoint cp then
            .error ⟨"IRI-forbidden codepoint in \\u escape", pos⟩
          else
            match codepointToChar cp pos with
            | .error e => .error e
            | .ok c =>
                (readIriRefBody (pos + 6) rest).map
                  (fun (s, p, r) => (c.toString ++ s, p, r))
      | _, _, _, _ => .error ⟨"invalid hex digit in \\u escape", pos⟩
  | '\\' :: 'u' :: _ => .error ⟨"incomplete \\u escape in IRIREF", pos⟩
  | '\\' :: 'U' :: h0 :: h1 :: h2 :: h3 :: h4 :: h5 :: h6 :: h7 :: rest =>
      match hexVal h0, hexVal h1, hexVal h2, hexVal h3,
            hexVal h4, hexVal h5, hexVal h6, hexVal h7 with
      | some d0, some d1, some d2, some d3, some d4, some d5, some d6, some d7 =>
          let cp := d0 * 268435456 + d1 * 16777216 + d2 * 1048576 + d3 * 65536
                  + d4 * 4096 + d5 * 256 + d6 * 16 + d7
          if isIriForbiddenCodepoint cp then
            .error ⟨"IRI-forbidden codepoint in \\U escape", pos⟩
          else
            match codepointToChar cp pos with
            | .error e => .error e
            | .ok c =>
                (readIriRefBody (pos + 10) rest).map
                  (fun (s, p, r) => (c.toString ++ s, p, r))
      | _, _, _, _, _, _, _, _ => .error ⟨"invalid hex digit in \\U escape", pos⟩
  | '\\' :: 'U' :: _ => .error ⟨"incomplete \\U escape in IRIREF", pos⟩
  | '\\' :: [] => .error ⟨"backslash at end of IRIREF", pos⟩
  | '\\' :: _ :: _ => .error ⟨"invalid escape in IRIREF (only \\u/\\U permitted)", pos⟩
  | c :: rest =>
      let cp := c.toNat
      if cp ≤ 0x20 || isIriForbiddenCodepoint cp then
        .error ⟨"invalid character in IRIREF", pos⟩
      else
        (readIriRefBody (pos + 1) rest).map (fun (s, p, r) => (c.toString ++ s, p, r))

/-- IRIREF: `'<' ... '>'`, `pos` pointing at the opening `<`. Port of
`parse_iri_raw` (well-formedness against `RDF.isIri` is checked one layer
up, in `Syntax.NTriples`, since it needs the RDF term model). -/
def readIriRef (pos : Nat) : List Char → Except ParseError (String × Nat × List Char)
  | '<' :: rest => readIriRefBody (pos + 1) rest
  | _ => .error ⟨"expected '<' (IRIREF)", pos⟩

/-! ## STRING_LITERAL_QUOTED — [9] STRING_LITERAL_QUOTED

`STRING_LITERAL_QUOTED ::= '"' ([^#x22#x5C#xA#xD] | ECHAR | UCHAR)* '"'` -/

/-- The body of a double-quoted string literal, decoding [153s] ECHAR
(`\t \b \n \r \f \" \' \\`) and [26] UCHAR (`\uXXXX`/`\UXXXXXXXX`)
escapes, and rejecting a raw (unescaped) newline or carriage return. -/
def readStringLiteralBody (pos : Nat) : List Char → Except ParseError (String × Nat × List Char)
  | [] => .error ⟨"unterminated string literal (expected '\"')", pos⟩
  | '"' :: rest => .ok ("", pos + 1, rest)
  | '\\' :: 't' :: rest =>
      (readStringLiteralBody (pos + 2) rest).map (fun (s, p, r) => ("\t" ++ s, p, r))
  | '\\' :: 'b' :: rest =>
      (readStringLiteralBody (pos + 2) rest).map
        (fun (s, p, r) => ((Char.ofNat 0x08).toString ++ s, p, r))
  | '\\' :: 'n' :: rest =>
      (readStringLiteralBody (pos + 2) rest).map (fun (s, p, r) => ("\n" ++ s, p, r))
  | '\\' :: 'r' :: rest =>
      (readStringLiteralBody (pos + 2) rest).map (fun (s, p, r) => ("\r" ++ s, p, r))
  | '\\' :: 'f' :: rest =>
      (readStringLiteralBody (pos + 2) rest).map
        (fun (s, p, r) => ((Char.ofNat 0x0C).toString ++ s, p, r))
  | '\\' :: '"' :: rest =>
      (readStringLiteralBody (pos + 2) rest).map (fun (s, p, r) => ("\"" ++ s, p, r))
  | '\\' :: '\'' :: rest =>
      (readStringLiteralBody (pos + 2) rest).map (fun (s, p, r) => ("'" ++ s, p, r))
  | '\\' :: '\\' :: rest =>
      (readStringLiteralBody (pos + 2) rest).map (fun (s, p, r) => ("\\" ++ s, p, r))
  | '\\' :: 'u' :: h0 :: h1 :: h2 :: h3 :: rest =>
      match hexVal h0, hexVal h1, hexVal h2, hexVal h3 with
      | some d0, some d1, some d2, some d3 =>
          let cp := d0 * 4096 + d1 * 256 + d2 * 16 + d3
          match codepointToChar cp pos with
          | .error e => .error e
          | .ok c =>
              (readStringLiteralBody (pos + 6) rest).map
                (fun (s, p, r) => (c.toString ++ s, p, r))
      | _, _, _, _ => .error ⟨"invalid hex digit in \\u escape", pos⟩
  | '\\' :: 'u' :: _ => .error ⟨"incomplete \\u escape", pos⟩
  | '\\' :: 'U' :: h0 :: h1 :: h2 :: h3 :: h4 :: h5 :: h6 :: h7 :: rest =>
      match hexVal h0, hexVal h1, hexVal h2, hexVal h3,
            hexVal h4, hexVal h5, hexVal h6, hexVal h7 with
      | some d0, some d1, some d2, some d3, some d4, some d5, some d6, some d7 =>
          let cp := d0 * 268435456 + d1 * 16777216 + d2 * 1048576 + d3 * 65536
                  + d4 * 4096 + d5 * 256 + d6 * 16 + d7
          match codepointToChar cp pos with
          | .error e => .error e
          | .ok c =>
              (readStringLiteralBody (pos + 10) rest).map
                (fun (s, p, r) => (c.toString ++ s, p, r))
      | _, _, _, _, _, _, _, _ => .error ⟨"invalid hex digit in \\U escape", pos⟩
  | '\\' :: 'U' :: _ => .error ⟨"incomplete \\U escape", pos⟩
  | '\\' :: [] => .error ⟨"backslash at end of string literal", pos⟩
  | '\\' :: c :: _ => .error ⟨s!"invalid escape: \\{c}", pos⟩
  | '\n' :: _ => .error ⟨"unescaped newline in string literal", pos⟩
  | '\r' :: _ => .error ⟨"unescaped carriage return in string literal", pos⟩
  | c :: rest =>
      (readStringLiteralBody (pos + 1) rest).map (fun (s, p, r) => (c.toString ++ s, p, r))

/-- STRING_LITERAL_QUOTED: `'"' ... '"'`, `pos` pointing at the opening
quote. Port of `parse_string_literal`. -/
def readStringLiteralQuoted (pos : Nat) : List Char → Except ParseError (String × Nat × List Char)
  | '"' :: rest => readStringLiteralBody (pos + 1) rest
  | _ => .error ⟨"expected '\"' (STRING_LITERAL_QUOTED)", pos⟩

/-! ## Whitespace, comments, end-of-line — N-Triples/N-Quads document
structure (RDF 1.1 N-Triples §"White space") -/

/-- N-Triples whitespace: space and tab ONLY (not newline — line
structure is handled separately by `skipEol`). Port of `is_nt_ws`. -/
def isNtWs (c : Char) : Bool :=
  c = ' ' || c = '\t'

/-- Skip a run of space/tab. Always succeeds (zero-or-more), so this
returns a plain pair rather than `Except` — port of `pws`. -/
def skipWs (pos : Nat) (cs : List Char) : Nat × List Char :=
  let (ws, rest) := cs.span isNtWs
  (pos + ws.length, rest)

/-- Skip to (but not past) the next line terminator, or to end of input.
Structural recursion on the input list. Port of `nt_skip_to_eol`. -/
def skipToEol (pos : Nat) : List Char → Nat × List Char
  | [] => (pos, [])
  | c :: rest =>
      if c = '\n' || c = '\r' then (pos, c :: rest) else skipToEol (pos + 1) rest

/-- If positioned at `#`, skip to end of line (not consuming the
terminator). Port of `skip_comment`. -/
def skipComment (pos : Nat) (cs : List Char) : Nat × List Char :=
  match cs with
  | '#' :: rest => skipToEol (pos + 1) rest
  | _ => (pos, cs)

/-- Skip one line terminator: LF, CRLF, or bare CR (RDF 1.1 N-Triples
[8] EOL treats `\r\n` as one boundary, not two). Port of `skip_eol`. -/
def skipEol (pos : Nat) : List Char → Nat × List Char
  | '\r' :: '\n' :: rest => (pos + 2, rest)
  | '\r' :: rest => (pos + 1, rest)
  | '\n' :: rest => (pos + 1, rest)
  | cs => (pos, cs)

/-! ## LANGTAG — [10] LANGTAG

`LANGTAG ::= '@' [a-zA-Z]+ ('-' [a-zA-Z0-9]+)*`

RDF 1.2 extends this with an optional `--ltr`/`--rtl` base-direction
suffix on the SAME production (a W3C Working Draft feature, epic #305 in
the F* tree); `readLangDir12` below is the RDF-1.2-aware reader,
`readLangTag` the byte-identical RDF 1.1 one. -/

/-- LANGTAG body characters: ASCII letters, digits, and `-`. Port of
`is_lang_char`. -/
def isLangChar (c : Char) : Bool :=
  ('A' ≤ c ∧ c ≤ 'Z') || ('a' ≤ c ∧ c ≤ 'z') || ('0' ≤ c ∧ c ≤ '9') || c = '-'

/-- BCP 47 requires a language tag to start with a letter. Port of
`is_alpha`. -/
def isLangStart (c : Char) : Bool :=
  ('A' ≤ c ∧ c ≤ 'Z') || ('a' ≤ c ∧ c ≤ 'z')

/-- Consume the maximal run of LANGTAG body characters. Not recursive
(uses `List.span`, itself total). -/
def readLangTagRun (pos : Nat) (cs : List Char) : String × Nat × List Char :=
  let (taken, rest) := cs.span isLangChar
  (String.ofList taken, pos + taken.length, rest)

/-- RDF 1.1 LANGTAG: `'@' letter+ ('-' alnum+)*` — no direction suffix.
Port of `parse_lang_tag`. -/
def readLangTag (pos : Nat) : List Char → Except ParseError (String × Nat × List Char)
  | '@' :: c1 :: rest =>
      if !isLangStart c1 then
        .error ⟨"language tag must start with a letter", pos + 1⟩
      else
        .ok (readLangTagRun (pos + 1) (c1 :: rest))
  | '@' :: [] => .error ⟨"expected language tag after '@'", pos + 1⟩
  | _ => .error ⟨"expected '@'", pos⟩

/-- Split a raw `@`-tag run at the FIRST double hyphen `--`: the left
part is the language tag, the right (if any) the base-direction token. A
well-formed BCP47 tag never contains an empty subtag, so the only `--`
present is the RDF 1.2 direction separator. Port of
`split_on_double_hyphen`; structural recursion (each recursive call's
list argument is the direct cons-tail of the previous one). -/
def splitOnDoubleHyphen : List Char → List Char → List Char × Option (List Char)
  | c1 :: c2 :: rest, acc =>
      if c1 = '-' && c2 = '-' then (acc.reverse, some rest)
      else splitOnDoubleHyphen (c2 :: rest) (c1 :: acc)
  | [c], acc => (acc.reverse ++ [c], none)
  | [], acc => (acc.reverse, none)

/-- BCP47-ish subtag validation: every hyphen-separated subtag is 1..8
characters (rejects `@cantbethislong` and empty subtags like `en-`).
`cur` is the running length of the current subtag. Port of
`valid_lang_subtags`. -/
def validLangSubtags : List Char → Nat → Bool
  | [], cur => cur ≥ 1 && cur ≤ 8
  | '-' :: rest, cur => (cur ≥ 1 && cur ≤ 8) && validLangSubtags rest 0
  | _ :: rest, cur => validLangSubtags rest (cur + 1)

/-- RDF 1.2 LANGTAG with an optional base-direction suffix:
`@lang` or `@lang--ltr` / `@lang--rtl` (lowercase only — `@en--LTR` is
rejected). Port of `parse_lang_dir_12`. `TextDirection` is defined in
`RDF.Core`; this module stays RDF-model-agnostic, so the direction is
returned as a plain two-way tag (`false` = ltr, `true` = rtl) and
`Syntax.NTriples` maps it onto `RDF.TextDirection`. -/
def readLangDir12 (pos : Nat) :
    List Char → Except ParseError ((String × Option Bool) × Nat × List Char)
  | '@' :: c1 :: rest =>
      if !isLangStart c1 then
        .error ⟨"language tag must start with a letter", pos + 1⟩
      else
        let (raw, pos', rest') := readLangTagRun (pos + 1) (c1 :: rest)
        let (ltChars, dirOpt) := splitOnDoubleHyphen raw.toList []
        if !validLangSubtags ltChars 0 then
          .error ⟨"invalid language tag", pos⟩
        else
          let langtag := String.ofList ltChars
          match dirOpt with
          | none => .ok ((langtag, none), pos', rest')
          | some dchars =>
              if dchars = ['l', 't', 'r'] then .ok ((langtag, some false), pos', rest')
              else if dchars = ['r', 't', 'l'] then .ok ((langtag, some true), pos', rest')
              else .error ⟨"invalid base direction (expected ltr or rtl)", pos⟩
  | '@' :: [] => .error ⟨"expected language tag after '@'", pos + 1⟩
  | _ => .error ⟨"expected '@'", pos⟩

/-! ## BLANK_NODE_LABEL — [141s] BLANK_NODE_LABEL

`BLANK_NODE_LABEL ::= '_:' (PN_CHARS_U | [0-9]) ((PN_CHARS | '.')* PN_CHARS)?`

i.e. a label starts with a PN_CHARS_U-or-digit character and may contain
internal dots, but never ENDS on a dot (a trailing dot belongs to the
document, not the label — `_:a. ` is the label `a` followed by `.`). -/

/-- Codepoints legal to START a blank-node label: `PN_CHARS_U` (ASCII
letter, digit 0-9, or `_`) — port of `is_bnode_start_cp`'s ASCII-range
half plus the non-ASCII PN_CHARS_BASE ranges from the Turtle/N-Triples
grammar (unchanged from the F* source; digits ARE legal as a start char
here, unlike Turtle's PN_CHARS_BASE, matching BLANK_NODE_LABEL's own
`(PN_CHARS_U | [0-9])` first-character rule). -/
def isBnodeStartChar (c : Char) : Bool :=
  let cp := c.toNat
  if cp < 0x80 then
    ('A' ≤ c ∧ c ≤ 'Z') || ('a' ≤ c ∧ c ≤ 'z') || c = '_' || ('0' ≤ c ∧ c ≤ '9')
  else
    (0x00C0 ≤ cp && cp ≤ 0x00D6) || (0x00D8 ≤ cp && cp ≤ 0x00F6) ||
    (0x00F8 ≤ cp && cp ≤ 0x02FF) || (0x0370 ≤ cp && cp ≤ 0x037D) ||
    (0x037F ≤ cp && cp ≤ 0x1FFF) || (0x200C ≤ cp && cp ≤ 0x200D) ||
    (0x2070 ≤ cp && cp ≤ 0x218F) || (0x2C00 ≤ cp && cp ≤ 0x2FEF) ||
    (0x3001 ≤ cp && cp ≤ 0xD7FF) || (0xF900 ≤ cp && cp ≤ 0xFDCF) ||
    (0xFDF0 ≤ cp && cp ≤ 0xFFFD) || (0x10000 ≤ cp && cp ≤ 0xEFFFF)

/-- Codepoints legal WITHIN a blank-node label (`PN_CHARS | '.'`, the
`.` filtered out afterwards by trailing-dot trimming below). Port of
`is_bnode_char_cp`. -/
def isBnodeChar (c : Char) : Bool :=
  let cp := c.toNat
  if cp < 0x80 then
    ('0' ≤ c ∧ c ≤ '9') || ('A' ≤ c ∧ c ≤ 'Z') || ('a' ≤ c ∧ c ≤ 'z') ||
    c = '_' || c = '-' || c = '.'
  else
    cp = 0xB7 ||
    (0x00C0 ≤ cp && cp ≤ 0x00D6) || (0x00D8 ≤ cp && cp ≤ 0x00F6) ||
    (0x00F8 ≤ cp && cp ≤ 0x02FF) || (0x0300 ≤ cp && cp ≤ 0x036F) ||
    (0x0370 ≤ cp && cp ≤ 0x037D) || (0x037F ≤ cp && cp ≤ 0x1FFF) ||
    (0x200C ≤ cp && cp ≤ 0x200D) || (0x203F ≤ cp && cp ≤ 0x2040) ||
    (0x2070 ≤ cp && cp ≤ 0x218F) || (0x2C00 ≤ cp && cp ≤ 0x2FEF) ||
    (0x3001 ≤ cp && cp ≤ 0xD7FF) || (0xF900 ≤ cp && cp ≤ 0xFDCF) ||
    (0xFDF0 ≤ cp && cp ≤ 0xFFFD) || (0x10000 ≤ cp && cp ≤ 0xEFFFF)

/-- BLANK_NODE_LABEL: `'_:' start body* `, trimming a trailing `.` back
onto the remaining input (it is not part of the label). Port of
`parse_bnode`. Not recursive: uses `List.span` (total) plus
`List.getLast?`/`List.dropLast` (also total) for the trailing-dot rule. -/
def readBlankNodeLabel (pos : Nat) : List Char → Except ParseError (String × Nat × List Char)
  | '_' :: ':' :: c0 :: rest =>
      if !isBnodeStartChar c0 then
        .error ⟨"invalid blank node label start character", pos + 2⟩
      else
        let (bodyChars, afterBody) := rest.span isBnodeChar
        let labelChars := c0 :: bodyChars
        match labelChars.getLast? with
        | some '.' =>
            let trimmed := labelChars.dropLast
            .ok (String.ofList trimmed, pos + 2 + trimmed.length, '.' :: afterBody)
        | _ =>
            .ok (String.ofList labelChars, pos + 2 + labelChars.length, afterBody)
  | '_' :: ':' :: [] => .error ⟨"empty blank node label", pos + 2⟩
  | _ => .error ⟨"expected '_:' (BLANK_NODE_LABEL)", pos⟩

end L4Factoidal.Syntax
