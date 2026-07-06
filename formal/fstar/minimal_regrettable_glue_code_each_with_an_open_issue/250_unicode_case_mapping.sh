#!/bin/bash
# Issue #250: realise SPARQL11.Algebra.string_uppercase_unicode /
# string_lowercase_unicode (rule-#11(a)-adjacent: vendored Unicode
# character-property tables, not a hand-rolled crypto/parser primitive).
# https://github.com/danbri/factoidal/issues/250
#
# SPARQL 1.1's UCASE()/LCASE() (§17.4.3.20/21) are XPath F&O
# fn:upper-case/fn:lower-case, which are Unicode-aware case mappings
# (e.g. "Müller" -> "MÜLLER", "straße" -> "STRASSE"). F*'s own
# `FStar.String.uppercase`/`lowercase` realise (in the F* standard
# library's `FStar_String.ml`) to `BatString.uppercase_ascii` /
# `lowercase_ascii` — ASCII-only; every codepoint outside [A-Za-z]
# passes through unchanged, so "Müller" came back "MüLLER".
#
# Fix: SPARQL11.Algebra.fst now declares two new `assume val`s,
# `string_uppercase_unicode` / `string_lowercase_unicode`, and
# `string_upper`/`string_lower` call them instead of
# `String.uppercase`/`String.lowercase`. This patch realises them
# using the `uucp` opam package (pure-OCaml Unicode character
# property tables, incl. case mappings — no crypto, no vendoring of
# our own tables; version pinned to uucp.17.0.0 as installed into the
# `fstar` opam switch on 2026-07-05: `opam install uucp`).
#
# `Uucp.Case.Map.to_upper`/`to_lower` return the Unicode
# Uppercase_Mapping/Lowercase_Mapping property per character (which,
# per the Unicode Character Database, already folds in the
# unconditional multi-character SpecialCasing.txt entries — this is
# why "straße" correctly maps to "STRASSE", not just "STRAßE").
# Limitation (documented, not silently swallowed): this is *simple*
# per-codepoint case mapping, not the full context-sensitive Unicode
# default case algorithm — capital sigma (Σ) lowercases to regular
# sigma (σ) even at a word boundary where XPath/Unicode's
# context-sensitive rule would produce final sigma (ς). Locale-
# sensitive mappings (e.g. Turkish dotless i) are likewise not
# applied — SPARQL 1.1 does not specify a collation/locale parameter
# for UCASE/LCASE, so this matches the spec's own scope.
#
# IMPORTANT (rule #3 / the #181 lesson): issue #250 stays OPEN after
# this patch lands. It is the acknowledged-gap tracker for these two
# OCaml-realised primitives (dual role: symptom report AND assume-val
# tracker), not something to close once the symptom stops reproducing.

set -euo pipefail

OUTDIR="$1"

# Backward compatibility: if $1 is a .ml file, use its directory
if [[ -f "$OUTDIR" && "$OUTDIR" == *.ml ]]; then
  OUTDIR="$(dirname "$OUTDIR")"
fi

if [[ ! -d "$OUTDIR" ]]; then
  echo "Error: $OUTDIR is not a directory" >&2
  exit 1
fi

FILE="$OUTDIR/SPARQL11_Algebra.ml"
if [[ ! -f "$FILE" ]]; then
  echo "  WARN: $FILE not found; skipping 250_unicode_case_mapping patch."
  echo "         (F* extract may not have produced SPARQL11.Algebra yet.)"
  exit 0
fi

# Idempotency: marker is the Uucp_case_runtime module this patch inserts.
if grep -q 'module Uucp_case_runtime' "$FILE"; then
  echo "  [250_unicode_case_mapping] already applied; skipping."
  exit 0
fi

echo "  Patching $FILE (string_uppercase_unicode/string_lowercase_unicode -> uucp)..."

python3 - "$FILE" <<'PYEOF'
import sys

path = sys.argv[1]
with open(path, "r") as f:
    content = f.read()

runtime_module = '''module Uucp_case_runtime = struct
  (* Issue #250: Unicode-aware UCASE()/LCASE() via `uucp`.
     `cmap_utf_8` is uucp's own documented recipe (uucp.mli,
     "Default case conversion on UTF-8 strings") for applying a
     per-Uchar case map across a UTF-8-encoded OCaml string. Invalid
     UTF-8 byte sequences decode to U+FFFD (replacement character)
     rather than raising -- SPARQL literals are already validated
     UTF-8 by the F*-side lexical-form parser, so this path is a
     defensive fallback, not the common case. *)
  let cmap_utf_8 (cmap : Uchar.t -> [ `Self | `Uchars of Uchar.t list ]) (s : string) : string =
    (* SPARQL11_Algebra.ml opens `Prims` at file scope, which rebinds
       `(+)`/`(-)`/etc. to Z.add/Z.sub (F*'s Prims.int/nat are
       unbounded, extracted via zarith). `String.get_utf_8_uchar`
       and `Buffer`/`Uchar` all need native OCaml `int`, so re-open
       `Stdlib` locally to get the native operators back -- same
       pattern already used in 63_regex_hash_uuid_stubs.sh's glue in
       this same file. *)
    let open Stdlib in
    let rec loop buf s i max =
      if i > max then Buffer.contents buf
      else begin
        let dec = String.get_utf_8_uchar s i in
        let u = Uchar.utf_decode_uchar dec in
        (match cmap u with
         | `Self -> Buffer.add_utf_8_uchar buf u
         | `Uchars us -> List.iter (Buffer.add_utf_8_uchar buf) us);
        loop buf s (i + Uchar.utf_decode_length dec) max
      end
    in
    let buf = Buffer.create (String.length s * 2) in
    if String.length s = 0 then "" else loop buf s 0 (String.length s - 1)

  let uppercase_utf_8 (s : string) : string = cmap_utf_8 Uucp.Case.Map.to_upper s
  let lowercase_utf_8 (s : string) : string = cmap_utf_8 Uucp.Case.Map.to_lower s
end

'''

# F* 2025.12.15 emits two distinct surface forms for a single-arg
# `assume val` (same pattern hit in 202_now_ms.sh):
#   form A:  let string_uppercase_unicode (s : Prims.string) : Prims.string=
#              failwith "Not yet implemented: SPARQL11.Algebra.string_uppercase_unicode"
#   form B:  let (string_uppercase_unicode : Prims.string -> Prims.string) =
#              fun s -> failwith "Not yet implemented: ..."
old_upper_patterns = [
    'let string_uppercase_unicode (s : Prims.string) : Prims.string=\n'
    '  failwith "Not yet implemented: SPARQL11.Algebra.string_uppercase_unicode"',
    'let string_uppercase_unicode (s : Prims.string) : Prims.string=\n'
    '  failwith\n'
    '    "Not yet implemented: SPARQL11.Algebra.string_uppercase_unicode"',
    'let (string_uppercase_unicode : Prims.string -> Prims.string) =\n'
    '  fun s -> failwith "Not yet implemented: SPARQL11.Algebra.string_uppercase_unicode"',
    'let (string_uppercase_unicode : Prims.string -> Prims.string) =\n'
    '  fun s ->\n'
    '    failwith "Not yet implemented: SPARQL11.Algebra.string_uppercase_unicode"',
]
old_lower_patterns = [
    'let string_lowercase_unicode (s : Prims.string) : Prims.string=\n'
    '  failwith "Not yet implemented: SPARQL11.Algebra.string_lowercase_unicode"',
    'let string_lowercase_unicode (s : Prims.string) : Prims.string=\n'
    '  failwith\n'
    '    "Not yet implemented: SPARQL11.Algebra.string_lowercase_unicode"',
    'let (string_lowercase_unicode : Prims.string -> Prims.string) =\n'
    '  fun s -> failwith "Not yet implemented: SPARQL11.Algebra.string_lowercase_unicode"',
    'let (string_lowercase_unicode : Prims.string -> Prims.string) =\n'
    '  fun s ->\n'
    '    failwith "Not yet implemented: SPARQL11.Algebra.string_lowercase_unicode"',
]

new_upper_a = (
    'let string_uppercase_unicode (s : Prims.string) : Prims.string=\n'
    '  Uucp_case_runtime.uppercase_utf_8 s'
)
new_upper_b = (
    'let (string_uppercase_unicode : Prims.string -> Prims.string) =\n'
    '  fun s -> Uucp_case_runtime.uppercase_utf_8 s'
)
new_lower_a = (
    'let string_lowercase_unicode (s : Prims.string) : Prims.string=\n'
    '  Uucp_case_runtime.lowercase_utf_8 s'
)
new_lower_b = (
    'let (string_lowercase_unicode : Prims.string -> Prims.string) =\n'
    '  fun s -> Uucp_case_runtime.lowercase_utf_8 s'
)

def apply_one(content, old_patterns, new_a, new_b, label):
    for i, old in enumerate(old_patterns):
        if old in content:
            new = new_a if i < 2 else new_b
            return content.replace(old, new, 1), True
    return content, False

content, upper_ok = apply_one(content, old_upper_patterns, new_upper_a, new_upper_b, "upper")
content, lower_ok = apply_one(content, old_lower_patterns, new_lower_a, new_lower_b, "lower")

if not (upper_ok and lower_ok):
    missing = []
    if not upper_ok:
        missing.append("string_uppercase_unicode")
    if not lower_ok:
        missing.append("string_lowercase_unicode")
    sys.stderr.write(
        "  ERROR: 250_unicode_case_mapping could not find the failwith stub(s) "
        f"for {', '.join(missing)} in {path}\n"
        "         Has the extraction shape changed? (see 202_now_ms.sh for the\n"
        "         two known surface forms this patch already tries.)\n"
    )
    sys.exit(1)

# Insert the runtime module right before the first patched function so
# it's in scope. Anchor on the (already-rewritten) string_uppercase_unicode
# definition, which is unique in the file.
anchor = "let string_uppercase_unicode (s : Prims.string) : Prims.string=\n  Uucp_case_runtime.uppercase_utf_8 s"
alt_anchor = "let (string_uppercase_unicode : Prims.string -> Prims.string) =\n  fun s -> Uucp_case_runtime.uppercase_utf_8 s"
if anchor in content:
    content = content.replace(anchor, runtime_module + anchor, 1)
elif alt_anchor in content:
    content = content.replace(alt_anchor, runtime_module + alt_anchor, 1)
else:
    sys.stderr.write(
        "  ERROR: 250_unicode_case_mapping could not find an anchor to insert "
        "Uucp_case_runtime\n"
    )
    sys.exit(1)

with open(path, "w") as f:
    f.write(content)
PYEOF

echo "  [250_unicode_case_mapping] applied: string_uppercase_unicode/string_lowercase_unicode -> Uucp_case_runtime (uucp.17.0.0)"
