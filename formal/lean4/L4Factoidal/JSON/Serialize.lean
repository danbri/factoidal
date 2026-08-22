/-
L4Factoidal.JSON.Serialize — RFC 8259 JSON serialisation.

Port of `formal/fstar/SPARQL.JSON.Escape.fst` (the escaping algorithm)
combined with the compact-writer shape of `Parser.JSONLD.fst`'s
`jcanon_serialize` family — but NOT the latter's canonicalisation
(RFC 8785 / JCS) policy. `Json.toStringCompact` below preserves OBJECT
KEY ORDER as given (no `jcanon_sort_fields`-style sorting) because
`Value.lean`'s `Json.object` is defined to preserve order and
duplicates exactly as parsed; a JCS-style canonical writer, if this
tree needs one later, belongs in its own module built on top of this
one (mirroring how `jcanon_serialize` in the F* tree is a separate
module layered on `Parser.JSON.fst`, not folded into it).

Escaping mirrors `SPARQL.JSON.Escape.fst`'s `json_escape` exactly
(RFC 8259 §7's MANDATORY escape set — the same one RFC 8785 §3.2.2.2
requires for JCS, per that F* module's own comment):
  - `\`  (0x5C) → `\\`
  - `"`  (0x22) → `\"`
  - LF   (0x0A) → `\n`
  - CR   (0x0D) → `\r`
  - TAB  (0x09) → `\t`
  - BS   (0x08) → `\b`
  - FF   (0x0C) → `\f`
  - any other control character (< 0x20) → `\u00XX` (lowercase hex)
  - everything else (including non-ASCII) → passed through UNCHANGED.

RFC 8259 §7 permits (but does not require) escaping `/` and any
non-ASCII character as `\uXXXX`; this port emits neither, matching the
F* source's choice (see that module's byte-for-byte comparison against
the previous `factoidal_http.ml` writer it replaced).

No fuel is threaded here (unlike `Parser.lean` and unlike
`jcanon_serialize`'s explicit fuel parameter): `Json` is a genuinely
finite Lean inductive, and structural (mutual) recursion over it —
same pattern as `Value.lean`'s `Json.size` — is directly accepted by
the equation compiler with no decrease obligations to discharge. F*'s
`jcanon_serialize` uses fuel most likely to sidestep its own
termination checker on the nested `json_val`/`list` shape (see the
"NOT the induction tactic" note in `Value.lean`); Lean's nested
inductive support handles plain structural `def`s over this shape
without that workaround, as already demonstrated by `Json.size`,
`decEqJson`, and this module.
-/
import L4Factoidal.JSON.Value

namespace L4Factoidal.JSON

open Json

/-! ## String escaping — port of `SPARQL.JSON.Escape.fst` -/

/-- One lowercase hex digit (0..15). Out-of-range mapped to `'0'` to
keep the function total — port of `hex_digit_lc`. -/
def hexDigitLc (n : Nat) : Char :=
  if n < 10 then Char.ofNat (0x30 + n)
  else if n < 16 then Char.ofNat (0x61 + (n - 10))
  else '0'

/-- Escape a single character per the RFC 8259 §7 mandatory set (see
module header); non-special characters pass through as a
one-character string. Port of `json_special` + `escape_string_of_byte`
fused into one function (this port walks `Char`s, not bytes — see
`Parser.lean`'s module header on why that is exact for Lean `String`,
unlike F*'s `string`). -/
def escapeChar (c : Char) : String :=
  let n := c.toNat
  if c = '\\' then "\\\\"
  else if c = '"' then "\\\""
  else if n = 0x0A then "\\n"
  else if n = 0x0D then "\\r"
  else if n = 0x09 then "\\t"
  else if n = 0x08 then "\\b"
  else if n = 0x0C then "\\f"
  else if n < 0x20 then
    let n3 := n % 16
    let n2 := (n / 16) % 16
    String.ofList ['\\', 'u', '0', '0', hexDigitLc n2, hexDigitLc n3]
  else String.singleton c

/-- Escape every character of a string per `escapeChar`. Port of
`json_escape` (there realised as a byte-run-splicing walk for
performance under F*'s codegen; this port is the direct per-character
map, since — as `Value.lean` and `Parser.lean` both note — this tree's
Lean side is the SPECIFICATION evaluator, not the performance one). -/
def escapeString (s : String) : String :=
  (s.toList.map escapeChar).foldl (· ++ ·) ""

/-! ## Compact writer

Object key order is exactly as stored (see module header); this is
NOT `jcanon_serialize`'s canonicalisation (`jcanon_sort_fields`) —
compact means "no insignificant whitespace", not "canonical form". -/

mutual

/-- Serialise a `Json` value to its compact (no whitespace) RFC 8259
text. Numbers are emitted VERBATIM (`Value.lean`'s lexical-preservation
choice makes this exact — no reformatting step is needed or wanted). -/
def toStringCompact : Json → String
  | .null      => "null"
  | .bool true  => "true"
  | .bool false => "false"
  | .number lex => lex
  | .string s   => "\"" ++ escapeString s ++ "\""
  | .array items  => "[" ++ toStringItems items ++ "]"
  | .object fields => "{" ++ toStringFields fields ++ "}"

def toStringItems : List Json → String
  | []        => ""
  | [x]       => toStringCompact x
  | x :: rest => toStringCompact x ++ "," ++ toStringItems rest

def toStringFields : List (String × Json) → String
  | []              => ""
  | [(k, v)]        => "\"" ++ escapeString k ++ "\":" ++ toStringCompact v
  | (k, v) :: rest  =>
    "\"" ++ escapeString k ++ "\":" ++ toStringCompact v ++ "," ++ toStringFields rest

end

/-- `j.toString` — the default (compact) serialisation. -/
def Json.toString (j : Json) : String := toStringCompact j

instance : ToString Json := ⟨Json.toString⟩

/-! ## Pretty writer (optional; not present in the F* module) -/

/-- `n` two-space indent levels, as a string. -/
def indentOf (n : Nat) : String :=
  String.ofList (List.replicate (2 * n) ' ')

mutual

/-- Serialise with 2-space indentation and newlines between object
members and array items. Not ported from `Parser.JSON.fst` /
`SPARQL.JSON.Escape.fst` (neither has a pretty-printer); provided as
the "optionally pretty" alternative the port brief allows, built on
the same `escapeString`/number-verbatim rules as the compact writer
so the two never disagree on ESCAPING, only on whitespace. -/
def toStringPrettyAt (depth : Nat) : Json → String
  | .null       => "null"
  | .bool true  => "true"
  | .bool false => "false"
  | .number lex => lex
  | .string s   => "\"" ++ escapeString s ++ "\""
  | .array []    => "[]"
  | .array items => "[\n" ++ toStringItemsPretty (depth + 1) items ++ "\n" ++ indentOf depth ++ "]"
  | .object []     => "{}"
  | .object fields => "{\n" ++ toStringFieldsPretty (depth + 1) fields ++ "\n" ++ indentOf depth ++ "}"

def toStringItemsPretty (depth : Nat) : List Json → String
  | []        => ""
  | [x]       => indentOf depth ++ toStringPrettyAt depth x
  | x :: rest =>
    indentOf depth ++ toStringPrettyAt depth x ++ ",\n" ++ toStringItemsPretty depth rest

def toStringFieldsPretty (depth : Nat) : List (String × Json) → String
  | []             => ""
  | [(k, v)]       =>
    indentOf depth ++ "\"" ++ escapeString k ++ "\": " ++ toStringPrettyAt depth v
  | (k, v) :: rest =>
    indentOf depth ++ "\"" ++ escapeString k ++ "\": " ++ toStringPrettyAt depth v ++ ",\n"
      ++ toStringFieldsPretty depth rest

end

/-- `j.toStringPretty` — 2-space-indented, multi-line serialisation. -/
def Json.toStringPretty (j : Json) : String := toStringPrettyAt 0 j

end L4Factoidal.JSON
