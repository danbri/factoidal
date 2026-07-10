#!/bin/bash
# Issue #287: realise SPARQL11.Algebra.fx_current_datetime (rule-#11(a)
# pure-I/O assume val) for SPARQL 1.1 NOW().
# https://github.com/danbri/factoidal/issues/287
#
# Replaces the F*-extracted `failwith` stub for
# `SPARQL11_Algebra.fx_current_datetime` with a wall-clock read
# (Unix.gettimeofday) formatted as an ISO-8601 UTC xsd:dateTime lexical.
#
# The value is captured ONCE per process (memoised in a string ref) so
# it is referentially transparent within a process, which matches
# NOW()'s "same value throughout one query execution" requirement and
# keeps the Tot labelling honest for a single short-lived run.
#
# Trust boundary: a wall-clock read is observable I/O (rule #11(a)).
# The ISO-8601 formatting is part of expressing that clock read; no
# RDF/SPARQL semantic logic lives here.

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
  echo "  WARN: $FILE not found; skipping 287_fx_current_datetime patch."
  exit 0
fi

# Idempotency: the memo ref name distinguishes the realised version.
if grep -q 'fx_now_cache' "$FILE"; then
  echo "  [287_fx_current_datetime] already applied; skipping."
  exit 0
fi

echo "  Patching $FILE (fx_current_datetime -> Unix.gettimeofday)..."

python3 - "$FILE" <<'PYEOF'
import sys

path = sys.argv[1]
with open(path, "r") as f:
    content = f.read()

# F* 2025.12.15 emits two surface forms for `assume val` (same as #202).
old_patterns = [
    # form A — single-line failwith
    'let fx_current_datetime (uu___ : unit) : Prims.string=\n'
    '  failwith "Not yet implemented: SPARQL11.Algebra.fx_current_datetime"',
    # form A — multi-line failwith
    'let fx_current_datetime (uu___ : unit) : Prims.string=\n'
    '  failwith\n'
    '    "Not yet implemented: SPARQL11.Algebra.fx_current_datetime"',
    # form B — single-line failwith
    'let (fx_current_datetime : unit -> Prims.string) =\n'
    '  fun uu___ -> failwith "Not yet implemented: SPARQL11.Algebra.fx_current_datetime"',
    # form B — multi-line failwith
    'let (fx_current_datetime : unit -> Prims.string) =\n'
    '  fun uu___ ->\n'
    '    failwith "Not yet implemented: SPARQL11.Algebra.fx_current_datetime"',
]

memo_ref = 'let fx_now_cache : Prims.string ref = ref ""\n'
body_core = (
    # `open Prims` shadows (+), (<>), etc. with Z.t/Prims variants; force
    # Stdlib so the native-int record fields from Unix.tm compute cleanly.
    '  let open Stdlib in\n'
    '  if !fx_now_cache <> "" then !fx_now_cache\n'
    '  else begin\n'
    '    let t = Unix.gmtime (Unix.gettimeofday ()) in\n'
    '    let s = Printf.sprintf "%04d-%02d-%02dT%02d:%02d:%02dZ"\n'
    '      (t.Unix.tm_year + 1900) (t.Unix.tm_mon + 1) t.Unix.tm_mday\n'
    '      t.Unix.tm_hour t.Unix.tm_min t.Unix.tm_sec in\n'
    '    fx_now_cache := s; s\n'
    '  end'
)
new_form_a = (
    memo_ref
    + 'let fx_current_datetime (uu___ : unit) : Prims.string=\n'
    + body_core
)
new_form_b = (
    memo_ref
    + 'let (fx_current_datetime : unit -> Prims.string) =\n'
    + '  fun uu___ ->\n'
    + body_core
)

replaced = False
already = 'fx_now_cache' in content
for i, old in enumerate(old_patterns):
    if old in content:
        content = content.replace(old, (new_form_a if i < 2 else new_form_b), 1)
        replaced = True
        break

if not replaced and not already:
    sys.stderr.write(
        "  ERROR: 287_fx_current_datetime could not find the failwith stub "
        "for fx_current_datetime in " + path + "\n"
        "         Has the extraction shape changed? NOW() will raise.\n"
    )
    sys.exit(1)

with open(path, "w") as f:
    f.write(content)
PYEOF

echo "  [287_fx_current_datetime] applied: fx_current_datetime -> memoised Unix.gmtime ISO-8601."
