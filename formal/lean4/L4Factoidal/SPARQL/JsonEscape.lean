/-
L4Factoidal.SPARQL.JsonEscape — JSON string escaping, byte for byte.

Port of `formal/fstar/SPARQL.JSON.Escape.fst` (97 lines). Migrated in
the F\* tree out of `factoidal_http.ml`'s hand-written `json_escape` per
iron rule #1.

The table:

| byte | output |
|---|---|
| 0x5C `\` | `\\` |
| 0x22 `"` | `\"` |
| 0x0A | `\n` |
| 0x0D | `\r` |
| 0x09 | `\t` |
| 0x08 | `\b` |
| 0x0C | `\f` |
| other < 0x20 | `\u00XX`, lowercase hex |
| anything else | unchanged |

## The bug this shape exists to prevent

The F\* module's own header records what its first implementation did
wrong, twice, and both failures are about the difference between a BYTE
and a CODEPOINT:

1. It pushed every byte through a char list finished by
   `string_of_list`, with the escape pairs mirrored relative to the
   final `rev` — `"n\"` instead of `"\n"`. The npm bundle was the first
   strict-JSON consumer of the output and crashed on it.
2. Pass-through bytes at or above 0x80 were double-encoded, because the
   walk reads BYTES while the extracted `string_of_list` re-encodes each
   list element as a UTF-8 CODEPOINT. `"café"` became `"cafÃ©"`.

The fix in F\* was to slice maximal runs of non-special bytes with
`fs_byte_sub`, which is byte-transparent, and splice escape strings
between them.

## How Lean avoids the same trap differently

The F\* module reaches bytes through `Parser.FastString`'s `assume val`
primitives, which the Lean tree has no counterpart to by design — Lean's
`String` is a sequence of codepoints and `Char` is a valid scalar value
by construction (`L4Factoidal/XML/Document.lean` states this).

So this walks `String.toUTF8` — a real `ByteArray` — and builds the
result as a `ByteArray`, decoding once at the end. Every byte at or
above 0x80 is copied verbatim into the output buffer and never passes
through `Char`, so failure mode 2 cannot occur. The escape strings are
written as literals, so failure mode 1 cannot occur either. The
`#guard`s below check both cases directly rather than trusting that.
-/

namespace L4Factoidal.SPARQL

/-- One lowercase hex digit. Out of range maps to `'0'` to stay
    total — the callers below pass a nibble. -/
def hexDigitLc (n : Nat) : UInt8 :=
  if n < 10 then UInt8.ofNat (0x30 + n)
  else if n < 16 then UInt8.ofNat (0x61 + (n - 10))
  else 0x30

/-- Is this byte one that JSON escaping must rewrite? Every special is
    ASCII, so no UTF-8 continuation byte is ever special. -/
def jsonSpecial (b : UInt8) : Bool :=
  b < 0x20 || b == 0x22 || b == 0x5C

/-- The escape bytes for one special byte. -/
def escapeBytesOf (b : UInt8) : List UInt8 :=
  if b == 0x5C then [0x5C, 0x5C]
  else if b == 0x22 then [0x5C, 0x22]
  else if b == 0x0A then [0x5C, 0x6E]        -- \n
  else if b == 0x0D then [0x5C, 0x72]        -- \r
  else if b == 0x09 then [0x5C, 0x74]        -- \t
  else if b == 0x08 then [0x5C, 0x62]        -- \b
  else if b == 0x0C then [0x5C, 0x66]        -- \f
  else
    let n := b.toNat
    [0x5C, 0x75, 0x30, 0x30, hexDigitLc ((n / 16) % 16), hexDigitLc (n % 16)]

/-- Fold the input's bytes into the output's, escaping the specials and
    copying everything else verbatim. -/
def escapeBytes (bs : ByteArray) : ByteArray :=
  bs.foldl (fun acc b =>
    if jsonSpecial b then (escapeBytesOf b).foldl ByteArray.push acc
    else acc.push b) ByteArray.empty

/-- Escape a string for embedding in a JSON string literal. -/
def jsonEscape (s : String) : String :=
  match String.fromUTF8? (escapeBytes s.toUTF8) with
  | some out => out
  | none     => s   -- unreachable: escaping never breaks UTF-8 validity

/-! ## Build-time checks

### The seven named escapes -/

#guard jsonEscape "\\" == "\\\\"
#guard jsonEscape "\"" == "\\\""
#guard jsonEscape "\n" == "\\n"
#guard jsonEscape "\r" == "\\r"
#guard jsonEscape "\t" == "\\t"
#guard jsonEscape (String.ofList [Char.ofNat 8]) == "\\b"
#guard jsonEscape (String.ofList [Char.ofNat 12]) == "\\f"

/-! ### The order is not mirrored

Failure mode 1 from the module header: the escape came out as `n\`
instead of `\n`. Checking `length == 2` would not catch it, so the check
is on the exact string, and on its FIRST character. -/

#guard (jsonEscape "\n").toList == ['\\', 'n']
#guard (jsonEscape "\n").toList.head? == some '\\'
#guard (jsonEscape "a\nb") == "a\\nb"

/-! ### Bytes at or above 0x80 pass through unchanged

Failure mode 2: `"café"` became `"cafÃ©"` because the walk read bytes
while the rebuild re-encoded codepoints. The check is on the BYTES, not
on the rendered string, because a double-encoding that round-trips
through `Char` can still print plausibly. -/

#guard jsonEscape "café" == "café"
#guard (jsonEscape "café").toUTF8.size == "café".toUTF8.size
#guard (jsonEscape "日本語").toUTF8.size == "日本語".toUTF8.size
#guard jsonEscape "日本語" == "日本語"

/-! A multi-byte character NEXT TO an escape is where a run-slicing bug
    would show: the run boundary falls inside neither character. -/

#guard jsonEscape "é\né" == "é\\né"
#guard jsonEscape "\"é\"" == "\\\"é\\\""

/-! ### Other control bytes take the `\u00XX` form, lowercase hex -/

#guard jsonEscape (String.ofList [Char.ofNat 1]) == "\\u0001"
#guard jsonEscape (String.ofList [Char.ofNat 0x1F]) == "\\u001f"
#guard jsonEscape (String.ofList [Char.ofNat 0]) == "\\u0000"

/-! 0x7F DEL is NOT a JSON special — it is above 0x1F — so it passes
    through. Checked because "control character" and "byte below 0x20"
    are different sets and only the second one is the rule. -/

#guard jsonEscape (String.ofList [Char.ofNat 0x7F]) == String.ofList [Char.ofNat 0x7F]

/-! ### Nothing to escape means nothing changes -/

#guard jsonEscape "" == ""
#guard jsonEscape "plain text" == "plain text"
#guard jsonEscape "SELECT ?s WHERE { ?s ?p ?o }" == "SELECT ?s WHERE { ?s ?p ?o }"

/-! ### A realistic case: a query body with a quoted literal -/

#guard jsonEscape "SELECT * WHERE { ?s ?p \"a\\b\" }"
        == "SELECT * WHERE { ?s ?p \\\"a\\\\b\\\" }"

end L4Factoidal.SPARQL
