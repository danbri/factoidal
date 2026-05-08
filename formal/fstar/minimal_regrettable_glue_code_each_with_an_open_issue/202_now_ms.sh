#!/bin/bash
# Issue #202: realise SPARQL.Eval.TimeBudget.now_ms (rule-#11(a)
# pure-I/O assume val).
# https://github.com/danbri/factoidal/issues/202
#
# Replaces the F*-extracted `failwith` stub for
# `SPARQL_Eval_TimeBudget.now_ms` with `Unix.gettimeofday ()`-based
# millisecond reading. This is the ONLY OCaml realisation needed by
# the cooperative-cancellation infrastructure that retires Heth3
# (per-query timeout) and supports Tav5's row-cap policy modules.
#
# Recovery plan reference:
#   docs/designissues/2026-05-07-query-planning-fstar-recovery.md
#   (Phase 5: Time budget)
#
# Trust boundary: a wallclock read is observable I/O. Millisecond
# precision is sufficient for per-query budget polling. Wallclock
# jumps cause only early/late expiry (both safer than the previous
# SIGALRM scheme).

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

FILE="$OUTDIR/SPARQL_Eval_TimeBudget.ml"
if [[ ! -f "$FILE" ]]; then
  echo "  WARN: $FILE not found; skipping 202_now_ms patch."
  echo "         (F* extract may not have produced SPARQL.Eval.TimeBudget yet.)"
  exit 0
fi

# Idempotency: marker is the Unix.gettimeofday call that distinguishes
# the realised version from the failwith stub.
if grep -q 'Unix.gettimeofday' "$FILE"; then
  echo "  [202_now_ms] already applied; skipping."
  exit 0
fi

echo "  Patching $FILE (now_ms -> Unix.gettimeofday)..."

python3 - "$FILE" <<'PYEOF'
import sys

path = sys.argv[1]
with open(path, "r") as f:
    content = f.read()

# F* 2025.12.15 emits two distinct surface forms for `assume val`:
#   form A:  let now_ms (uu___ : unit) : Prims.int=
#              failwith "Not yet implemented: SPARQL.Eval.TimeBudget.now_ms"
#   form B:  let (now_ms : unit -> Prims.int) =
#              fun uu___ -> failwith "Not yet implemented: ..."
# The determining factor is module-level details, not the assume-val itself
# (same pattern hit hash_sha256 in #228). Patch both forms — the unmatched
# one is a no-op replace.
old_patterns = [
    # form A — single line failwith
    'let now_ms (uu___ : unit) : Prims.int=\n'
    '  failwith "Not yet implemented: SPARQL.Eval.TimeBudget.now_ms"',
    # form A — multi-line failwith
    'let now_ms (uu___ : unit) : Prims.int=\n'
    '  failwith\n'
    '    "Not yet implemented: SPARQL.Eval.TimeBudget.now_ms"',
    # form B — single line failwith
    'let (now_ms : unit -> Prims.int) =\n'
    '  fun uu___ -> failwith "Not yet implemented: SPARQL.Eval.TimeBudget.now_ms"',
    # form B — multi-line failwith
    'let (now_ms : unit -> Prims.int) =\n'
    '  fun uu___ ->\n'
    '    failwith "Not yet implemented: SPARQL.Eval.TimeBudget.now_ms"',
]
new_body_form_a = (
    'let now_ms (uu___ : unit) : Prims.int=\n'
    '  (* Issue #202: rule-#11(a) pure-I/O realisation.\n'
    '     Unix.gettimeofday returns seconds-as-float; multiply to ms,\n'
    '     truncate, and lift to Prims.int (Z.t). Wallclock jumps are\n'
    '     tolerated -- only affects polling cadence, not correctness. *)\n'
    '  Z.of_int (int_of_float (Unix.gettimeofday () *. 1000.0))'
)
new_body_form_b = (
    'let (now_ms : unit -> Prims.int) =\n'
    '  (* Issue #202: rule-#11(a) pure-I/O realisation.\n'
    '     Unix.gettimeofday returns seconds-as-float; multiply to ms,\n'
    '     truncate, and lift to Prims.int (Z.t). Wallclock jumps are\n'
    '     tolerated -- only affects polling cadence, not correctness. *)\n'
    '  fun uu___ ->\n'
    '    Z.of_int (int_of_float (Unix.gettimeofday () *. 1000.0))'
)

replaced = False
already_patched = 'Unix.gettimeofday' in content
# Try each old pattern; first 2 are form A, last 2 are form B.
for i, old in enumerate(old_patterns):
    if old in content:
        new_body = new_body_form_a if i < 2 else new_body_form_b
        content = content.replace(old, new_body, 1)
        replaced = True
        break

if not replaced and not already_patched:
    sys.stderr.write(
        "  ERROR: 202_now_ms could not find the failwith stub for now_ms in "
        + path
        + "\n         Has the extraction shape changed?\n"
    )
    sys.exit(1)

with open(path, "w") as f:
    f.write(content)
PYEOF

echo "  [202_now_ms] applied: now_ms -> Z.of_int (int_of_float (Unix.gettimeofday () *. 1000.0))"
