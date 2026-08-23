/-
L4Factoidal.JSON.Parser — a total RFC 8259 JSON parser.

Port of `formal/fstar/Parser.JSON.fst`. That module's header states its
STRICTNESS CONTRACT (quoted, since this port keeps it verbatim):
  - exactly one top-level value; only JSON whitespace may follow;
  - strings: the full escape set (quote, backslash, slash, b, f, n, r,
    t, u followed by four hex digits) and nothing else; backslash-u
    escapes combine UTF-16 surrogate pairs into supplementary-plane
    codepoints; lone surrogates are rejected; invalid hex digits are
    rejected; raw control characters below U+0020 are rejected;
  - numbers: the exact RFC 8259 grammar
      minus? ( zero | digit1-9 digit* ) frac? exp?
    with frac = dot digit+ and exp = (e|E) sign? digit+ ;
  - whitespace: space, tab, LF, CR only.

RFC 8259, https://www.rfc-editor.org/rfc/rfc8259 :
  §2 (whitespace), §3 (values), §6 (numbers), §7 (strings + escapes).

## Indexing: an `Array Char`, not F*'s raw bytes (and not `String.Pos`)

`Parser.JSON.fst` walks BYTES (`Parser.FastString.fs_byte_at`) because
F*'s `string` is a sequence of Unicode codepoints re-encoded to UTF-8
on every access, so the F* module has to hand-roll byte-true slicing
(`fs_byte_sub`) to avoid a double-encoding bug it documents at
`json_utf8_of_codepoint` (issue #271 family). This port instead
converts the input to an `Array Char` ONCE and indexes it
by plain `Nat` position — a Lean `Char` is already a full Unicode
scalar value (never a UTF-16 code unit and never a raw byte), so this
sidesteps both the F* module's byte-slicing machinery AND `String`'s
own `String.Pos` API (which this toolchain ties to a `String →
Type`-indexed position type unsuitable for the plain-`Nat` position
arithmetic this parser needs — a Lean-version-specific reason, not a
semantic one). One consequence worth flagging honestly: error
positions here are CHARACTER indices, not the UTF-8 BYTE offsets
`Parser.JSON.fst` reports; RFC 8259 does not mandate a position
representation for diagnostics, so this is a presentation difference,
not a conformance one.

`\uXXXX` surrogate-PAIR combination is still hand-written below (RFC
8259 §7's own concession that JSON strings are, textually, a sequence
of UTF-16 code units even though the underlying character set is
Unicode) — Lean's `Char` has no surrogate representation, so a
lone/unpaired surrogate escape is rejected exactly as the F* module
rejects it, and a valid high/low pair is combined into one
supplementary-plane `Char` before use. Raw (unescaped) string content
needs no well-formedness check on this port's side (unlike the F*
module's "NOT COVERED" caveat): a Lean `String`/`List Char` cannot
hold an ill-formed code sequence.

## Fuel, not `termination_by`

Container recursion (`parseValue`/`parseObject`/`parseMembers`/
`parseArray`/`parseItems`) is fuelled exactly as `Parser.JSON.fst` is:
every mutually recursive call passes `fuel - 1` (after the `0`/`n+1`
match, "the same `fuel`" post-destructuring), so the whole mutual block
is structurally decreasing on that one `Nat` argument — no
`termination_by`/`decreasing_by` obligations, and (as in the F*
original) a fuel bound of `cs.size + 1` is always sufficient, since
every recursive step consumes at least one character. Running out of
fuel produces `"JSON nesting too deep"`, matching the F* module's
error text and its safety net (not a real practical limit at this fuel
bound: nesting depth cannot exceed the number of input characters).
-/
import L4Factoidal.JSON.Value

namespace L4Factoidal.JSON

open Json

/-- A parse failure: a diagnostic message plus a character position
into the input (port of the F* module's `ParseFail msg pos` — see the
module header on the byte-vs-character position difference). -/
structure JsonError where
  msg : String
  pos : Nat
  deriving DecidableEq, Repr

instance : ToString JsonError :=
  ⟨fun e => s!"{e.msg} (at character {e.pos})"⟩

/-- `Except` itself carries no `DecidableEq` instance in core (unlike
`Option`); this one is generic over any decidable `ε`/`α`, used below
by `parseJson`'s `Except JsonError Json` results (round-trip `#guard`s
and theorems compare parse results directly). Not a nested-inductive
type — `Except` has exactly two non-recursive constructors — so this
needs none of `Value.lean`'s `decEqJson` machinery. -/
instance [DecidableEq ε] [DecidableEq α] : DecidableEq (Except ε α)
  | .error e1, .error e2 =>
    match decEq e1 e2 with
    | isTrue h => isTrue (by rw [h])
    | isFalse h => isFalse (fun he => h (by injection he))
  | .ok a1, .ok a2 =>
    match decEq a1 a2 with
    | isTrue h => isTrue (by rw [h])
    | isFalse h => isFalse (fun he => h (by injection he))
  | .error _, .ok _ => isFalse (fun he => nomatch he)
  | .ok _, .error _ => isFalse (fun he => nomatch he)

/-! ## Character-position helpers over `Chars`

`Chars` is an `Array Char`, not a `List Char`. That is a CORRECTNESS-
neutral, performance-decisive difference: `List.get?` walks the list,
so indexing by position made the parser quadratic in the input, and a
747 KB manifest (the ShEx validation suite's) did not finish in ten
minutes. An `Array` index is constant time. The XML parser in this
tree already made the same choice, for the same reason, and its header
says so.

Measured 2026-08-23: the ShEx manifest goes from "no result after 600
seconds" to under a second. -/

/-- The document under the cursor, as a codepoint array. -/
abbrev Chars := Array Char

/-- The character at position `pos`, or `none` past the end of `cs`.
Port of `jbyte_at`'s "in range or sentinel" shape, typed `Option Char`
instead of `int`'s `-1` sentinel. -/
def charAt? (cs : Chars) (pos : Nat) : Option Char :=
  cs[pos]?

/-- Skip JSON whitespace: space, tab, LF, CR (RFC 8259 §2). Port of
`json_skip_ws`. -/
def skipWs (cs : Chars) (pos fuel : Nat) : Nat :=
  match fuel with
  | 0 => pos
  | fuel + 1 =>
    match charAt? cs pos with
    | some c =>
      if c = ' ' || c = '\t' || c = '\n' || c = '\r'
      then skipWs cs (pos + 1) fuel
      else pos
    | none => pos

/-- Substring from a character-position span. Used only where the RFC
grammar has already validated the span (a matched number lexeme); not
a general string constructor. -/
def sliceStr (cs : Chars) (start len : Nat) : String :=
  String.ofList (cs.extract start (start + len)).toList

/-- Match a fixed ASCII keyword (`true`/`false`/`null`) character by
character at `pos`. -/
def matchKeyword (cs : Chars) (pos : Nat) (kw : List Char) : Bool :=
  match kw with
  | [] => true
  | c :: rest => charAt? cs pos = some c && matchKeyword cs (pos + 1) rest

/-! ## Strings (RFC 8259 §7) -/

/-- Hex digit value, or `none` for a non-hex-digit character. Port of
`json_hex_val`. -/
def hexVal (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else none

/-- Read exactly four hex digits starting at `pos`; `none` if any of
the four is missing or not a hex digit. Port of `json_read_hex4`. -/
def readHex4 (cs : Chars) (pos : Nat) : Option Nat := do
  let h0 ← (charAt? cs pos).bind hexVal
  let h1 ← (charAt? cs (pos + 1)).bind hexVal
  let h2 ← (charAt? cs (pos + 2)).bind hexVal
  let h3 ← (charAt? cs (pos + 3)).bind hexVal
  some (h0 * 4096 + h1 * 256 + h2 * 16 + h3)

/-- One-character string for a decoded Unicode codepoint. `Char.ofNat`
substitutes U+FFFD for an out-of-range/surrogate input — a safety net
only: every call site below has already validated `cp` is a genuine
scalar value (a non-surrogate `\u` escape, or a combined surrogate
pair) before reaching here, mirroring `json_utf8_of_codepoint`'s own
"guard already applied by the caller" comment. -/
def codepointToString (cp : Nat) : String :=
  String.singleton (Char.ofNat cp)

/-- Decode one escape sequence; `pos` points AT the backslash. On
success, the decoded piece (as a one-character string; two source
`\uXXXX` escapes combine into ONE result character for a surrogate
pair) and the position of the first character after the escape. Port
of `json_escape_piece`, including the surrogate-pair combination (RFC
8259 §7 "\u" escapes are UTF-16 code units; a supplementary-plane
character is written as a high/low surrogate PAIR of consecutive
`\uXXXX` escapes) and its rejection of lone/unpaired surrogates. -/
def escapePiece (cs : Chars) (pos : Nat) : Except JsonError (String × Nat) :=
  match charAt? cs (pos + 1) with
  | some '"'  => .ok ("\"", pos + 2)
  | some '\\' => .ok ("\\", pos + 2)
  | some '/'  => .ok ("/", pos + 2)
  | some 'b'  => .ok ("\x08", pos + 2)
  | some 'f'  => .ok ("\x0C", pos + 2)
  | some 'n'  => .ok ("\n", pos + 2)
  | some 'r'  => .ok ("\r", pos + 2)
  | some 't'  => .ok ("\t", pos + 2)
  | some 'u' =>
    match readHex4 cs (pos + 2) with
    | none => .error ⟨"invalid hex in unicode escape", pos⟩
    | some cp =>
      if cp ≥ 0xD800 && cp ≤ 0xDBFF then
        -- High surrogate: MUST be followed by a `\u` low-surrogate escape.
        match charAt? cs (pos + 6), charAt? cs (pos + 7) with
        | some '\\', some 'u' =>
          match readHex4 cs (pos + 8) with
          | none => .error ⟨"invalid hex in low surrogate escape", pos⟩
          | some lo =>
            if lo ≥ 0xDC00 && lo ≤ 0xDFFF then
              let combined := 0x10000 + (cp - 0xD800) * 0x400 + (lo - 0xDC00)
              .ok (codepointToString combined, pos + 12)
            else .error ⟨"high surrogate not followed by low surrogate", pos⟩
        | _, _ => .error ⟨"unpaired high surrogate", pos⟩
      else if cp ≥ 0xDC00 && cp ≤ 0xDFFF then
        .error ⟨"lone low surrogate", pos⟩
      else
        .ok (codepointToString cp, pos + 6)
  | _ => .error ⟨"invalid escape sequence in JSON string", pos⟩

/-- String body after the opening quote: accumulate raw characters and
decoded escape pieces until the closing quote. Port of
`json_string_segments`. `fuel` decreases by one per character/escape
consumed, so `cs.size + 1` is always sufficient. -/
def stringSegments (cs : Chars) (pos : Nat) (acc : String) (fuel : Nat)
    : Except JsonError (String × Nat) :=
  match fuel with
  | 0 => .error ⟨"unterminated JSON string", pos⟩
  | fuel + 1 =>
    match charAt? cs pos with
    | none => .error ⟨"unterminated JSON string", pos⟩
    | some c =>
      if c = '"' then .ok (acc, pos + 1)
      else if c = '\\' then
        match escapePiece cs pos with
        | .error e => .error e
        | .ok (piece, npos) => stringSegments cs npos (acc ++ piece) fuel
      else if c.toNat < 0x20 then
        .error ⟨"raw control character in JSON string", pos⟩
      else
        stringSegments cs (pos + 1) (acc ++ String.singleton c) fuel

/-- Parse a JSON string starting at the opening double quote. Port of
`json_parse_string`. -/
def parseString (cs : Chars) (pos : Nat) : Except JsonError (String × Nat) :=
  match charAt? cs pos with
  | some '"' => stringSegments cs (pos + 1) "" (cs.size + 1)
  | _ => .error ⟨"expected JSON string", pos⟩

/-! ## Numbers — strict RFC 8259 §6 grammar -/

/-- Position after a run of ASCII digits starting at `pos`. Port of
`json_scan_digits`. -/
def scanDigits (cs : Chars) (pos fuel : Nat) : Nat :=
  match fuel with
  | 0 => pos
  | fuel + 1 =>
    match charAt? cs pos with
    | some c => if c.isDigit then scanDigits cs (pos + 1) fuel else pos
    | none => pos

/-- Optional fraction part: `. digit+`. `none` on a dot with no digit
following (RFC 8259 §6: `frac = decimal-point 1*DIGIT`). Port of
`json_number_frac`. -/
def numberFrac (cs : Chars) (p : Nat) : Option Nat :=
  match charAt? cs p with
  | some '.' =>
    match charAt? cs (p + 1) with
    | some c => if c.isDigit then some (scanDigits cs (p + 2) (cs.size + 1)) else none
    | none => none
  | _ => some p

/-- Optional exponent part: `(e|E) sign? digit+`. `none` on a broken
exponent. Port of `json_number_exp`. -/
def numberExp (cs : Chars) (p : Nat) : Option Nat :=
  match charAt? cs p with
  | some c =>
    if c = 'e' || c = 'E' then
      let p1 := p + 1
      let p2 := match charAt? cs p1 with
        | some c1 => if c1 = '+' || c1 = '-' then p1 + 1 else p1
        | none => p1
      match charAt? cs p2 with
      | some d => if d.isDigit then some (scanDigits cs (p2 + 1) (cs.size + 1)) else none
      | none => none
    else some p
  | none => some p

/-- Parse a JSON number starting at `pos`. The success value is the
verbatim lexeme (RFC 8259 §6, and see `Value.lean`'s module header on
why numbers are kept lexical). Leading zeros are rejected structurally:
after an initial `'0'` the integer part ends, so `"0123"` parses only
`"0"` and the enclosing grammar then rejects the trailing `"123"`.
Port of `json_parse_number`. -/
def parseNumber (cs : Chars) (pos : Nat) : Except JsonError (String × Nat) :=
  let p1 := match charAt? cs pos with | some '-' => pos + 1 | _ => pos
  let ipartEnd : Option Nat :=
    match charAt? cs p1 with
    | some '0' => some (p1 + 1)
    | some c => if c.isDigit then some (scanDigits cs (p1 + 1) (cs.size + 1)) else none
    | none => none
  match ipartEnd with
  | none => .error ⟨"invalid JSON number", pos⟩
  | some p2 =>
    match numberFrac cs p2 with
    | none => .error ⟨"invalid fraction in JSON number", pos⟩
    | some p4 =>
      match numberExp cs p4 with
      | none => .error ⟨"invalid exponent in JSON number", pos⟩
      | some pEnd => .ok (sliceStr cs pos (pEnd - pos), pEnd)

/-! ## Values, objects, arrays -/

mutual

/-- Parse one JSON value at `pos`, skipping leading whitespace. Port of
`json_parse_value`. -/
def parseValue (cs : Chars) (pos fuel : Nat) : Except JsonError (Json × Nat) :=
  match fuel with
  | 0 => .error ⟨"JSON nesting too deep", pos⟩
  | fuel + 1 =>
    let p := skipWs cs pos (cs.size + 1)
    match charAt? cs p with
    | some '"' =>
      match parseString cs p with
      | .ok (str, np) => .ok (.string str, np)
      | .error e => .error e
    | some '{' => parseObject cs (p + 1) fuel
    | some '[' => parseArray cs (p + 1) fuel
    | some 't' =>
      if matchKeyword cs p "true".toList then .ok (.bool true, p + 4)
      else .error ⟨"expected literal true", p⟩
    | some 'f' =>
      if matchKeyword cs p "false".toList then .ok (.bool false, p + 5)
      else .error ⟨"expected literal false", p⟩
    | some 'n' =>
      if matchKeyword cs p "null".toList then .ok (.null, p + 4)
      else .error ⟨"expected literal null", p⟩
    | some c =>
      if c = '-' || c.isDigit then
        match parseNumber cs p with
        | .ok (lex, np) => .ok (.number lex, np)
        | .error e => .error e
      else .error ⟨"unexpected character in JSON value", p⟩
    | none => .error ⟨"unexpected end of input in JSON value", p⟩

/-- Object body after the opening brace. Port of `json_parse_object`. -/
def parseObject (cs : Chars) (pos fuel : Nat) : Except JsonError (Json × Nat) :=
  match fuel with
  | 0 => .error ⟨"JSON nesting too deep", pos⟩
  | fuel + 1 =>
    let p := skipWs cs pos (cs.size + 1)
    match charAt? cs p with
    | some '}' => .ok (.object [], p + 1)
    | _ => parseMembers cs p fuel []

/-- One or more `key : value` members. Strict: a comma must be
followed by another key string, so trailing commas are rejected
(matching `json_parse_members`). `acc` accumulates in FORWARD order
(unlike the F* module's cons-then-reverse; either preserves key order
identically — see `Value.lean`'s module header on why order matters). -/
def parseMembers (cs : Chars) (pos fuel : Nat) (acc : List (String × Json))
    : Except JsonError (Json × Nat) :=
  match fuel with
  | 0 => .error ⟨"JSON nesting too deep", pos⟩
  | fuel + 1 =>
    let p := skipWs cs pos (cs.size + 1)
    match parseString cs p with
    | .error e => .error e
    | .ok (key, p1) =>
      let p2 := skipWs cs p1 (cs.size + 1)
      match charAt? cs p2 with
      | some ':' =>
        match parseValue cs (p2 + 1) fuel with
        | .error e => .error e
        | .ok (v, p3) =>
          let acc2 := acc ++ [(key, v)]
          let p4 := skipWs cs p3 (cs.size + 1)
          match charAt? cs p4 with
          | some '}' => .ok (.object acc2, p4 + 1)
          | some ',' => parseMembers cs (p4 + 1) fuel acc2
          | _ => .error ⟨"expected comma or closing brace in JSON object", p4⟩
      | _ => .error ⟨"expected colon in JSON object", p2⟩

/-- Array body after the opening bracket. Port of `json_parse_array`. -/
def parseArray (cs : Chars) (pos fuel : Nat) : Except JsonError (Json × Nat) :=
  match fuel with
  | 0 => .error ⟨"JSON nesting too deep", pos⟩
  | fuel + 1 =>
    let p := skipWs cs pos (cs.size + 1)
    match charAt? cs p with
    | some ']' => .ok (.array [], p + 1)
    | _ => parseItems cs p fuel []

/-- One or more array items. Strict: a comma must be followed by
another value, so trailing commas are rejected. Port of
`json_parse_items`. -/
def parseItems (cs : Chars) (pos fuel : Nat) (acc : List Json)
    : Except JsonError (Json × Nat) :=
  match fuel with
  | 0 => .error ⟨"JSON nesting too deep", pos⟩
  | fuel + 1 =>
    match parseValue cs pos fuel with
    | .error e => .error e
    | .ok (v, p1) =>
      let acc2 := acc ++ [v]
      let p2 := skipWs cs p1 (cs.size + 1)
      match charAt? cs p2 with
      | some ']' => .ok (.array acc2, p2 + 1)
      | some ',' => parseItems cs (p2 + 1) fuel acc2
      | _ => .error ⟨"expected comma or closing bracket in JSON array", p2⟩

end

/-! ## Top level -/

/-- Parse a complete RFC 8259 JSON text: exactly one value, with only
JSON whitespace before and after. Port of `parse_json_text`; the
success value additionally carries the end position (unused by
`parseJson` below, kept for parity/debugging). -/
def parseJsonTextChars (cs : Chars) : Except JsonError (Json × Nat) :=
  match parseValue cs 0 (cs.size + 1) with
  | .error e => .error e
  | .ok (v, p) =>
    let p2 := skipWs cs p (cs.size + 1)
    if p2 ≥ cs.size then .ok (v, p2)
    else .error ⟨"trailing content after JSON value", p2⟩

/-- Parse a complete RFC 8259 JSON text from a `String`. Port of
`parse_json_text`. -/
def parseJsonText (s : String) : Except JsonError (Json × Nat) :=
  parseJsonTextChars s.toList.toArray

/-- `Except`-typed top-level parse (what `Value.lean`'s theorems build
on; the F* module's `parse_json_text` with the position dropped). -/
def parseJson (s : String) : Except JsonError Json :=
  match parseJsonText s with
  | .ok (v, _) => .ok v
  | .error e => .error e

/-- Option-typed convenience wrapper, port of `parse_json`. -/
def parseJson? (s : String) : Option Json :=
  match parseJsonText s with
  | .ok (v, _) => some v
  | .error _ => none

/-- `true` iff parsing failed. Core `Except` has no `isError` field
(only `Option` does) — a small local convenience for rejection tests. -/
def Except.isError : Except ε α → Bool
  | .error _ => true
  | .ok _    => false

end L4Factoidal.JSON
