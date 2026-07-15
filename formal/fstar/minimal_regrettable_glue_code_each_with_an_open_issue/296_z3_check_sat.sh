#!/bin/bash
# Issue #296: realise Tableau.CountingOracle.z3_check_sat (rule-#11
# ASSUME-HOST host-engine call-out -- satisfiability is z3's semantics,
# exactly as regex_match's semantics are the host regex engine's).
# https://github.com/danbri/factoidal/issues/296
#
# PHASE 0 realisation (Z33kr, docs/designissues/2026-07-14-z3-entailment-
# backend.md): return Z3_Unknown UNCONDITIONALLY. z3 is NOT consulted in
# Phase 0 -- the verified counting-fragment encoder + recogniser land
# first, and nothing in any runner calls z3_check_sat yet, so the
# extracted engine's behaviour is byte-for-byte unchanged. This replaces
# the F*-extracted `failwith` stub with a total `Z3_Unknown` so the
# module compiles and links; it NEVER fabricates Z3_Unsat/Z3_Sat (a
# fabricated Unsat is a soundness hole exactly as a fabricated
# verify=true is -- see the throw-on-uninit contract in
# skills/node-crypto-haclstar-vc-wasm-build).
#
# Phase 1 replaces this body with a real native-z3 spawn (stdin SMT-LIB,
# parse sat/unsat/unknown), wired only into the tableau's `None` branch
# behind Tableau_CountingOracle.in_counting_fragment, and validated
# against the build-breaking soundness gate BEFORE any test flips.
#
# Recovery / design reference:
#   docs/designissues/2026-07-14-z3-entailment-backend.md (Phase 0)
#
# Trust boundary: ASSUME-HOST (skills/ocaml-boundary). The Phase-0 body
# is not even a host call-out yet -- it is the safe "oracle absent"
# default (Z3_Unknown), from which the runner falls back to the verified
# tableau/RL verdict.

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

FILE="$OUTDIR/Tableau_CountingOracle.ml"
if [[ ! -f "$FILE" ]]; then
  echo "  WARN: $FILE not found; skipping 296_z3_check_sat patch."
  echo "         (F* extract may not have produced Tableau.CountingOracle yet.)"
  exit 0
fi

# Idempotency: marker is the Phase-0 acknowledgement comment injected
# into the replacement body.
if grep -q 'Issue #296: Phase-0 Z3_Unknown' "$FILE"; then
  echo "  [296_z3_check_sat] already applied; skipping."
  exit 0
fi

echo "  Patching $FILE (z3_check_sat -> Z3_Unknown, Phase 0)..."

python3 - "$FILE" <<'PYEOF'
import sys

path = sys.argv[1]
with open(path, "r") as f:
    content = f.read()

# F* emits two surface forms for a curried `assume val` (same variance
# 202_now_ms.sh / #228 documented). The argument identifiers are
# extraction-mangled (uu___ / uu___0 ...), so match on the failwith
# payload -- the module-qualified name is stable -- and rewrite the
# whole binding to return Z3_Unknown, ignoring both arguments.
marker = (
    '  (* Issue #296: Phase-0 Z3_Unknown -- z3 NOT consulted yet; never\n'
    '     fabricate Z3_Unsat/Z3_Sat. See\n'
    '     minimal_regrettable_glue_code_each_with_an_open_issue/296_z3_check_sat.sh *)\n'
)

payload = 'Not yet implemented: Tableau.CountingOracle.z3_check_sat'

already_patched = 'Issue #296: Phase-0 Z3_Unknown' in content
if payload not in content and not already_patched:
    sys.stderr.write(
        "  ERROR: 296_z3_check_sat: did not find the z3_check_sat failwith "
        "stub in " + path + "; extraction shape changed?\n"
    )
    sys.exit(1)

# Replace every failwith call carrying our payload (covers single-line
# and multi-line failwith, form A and form B) with `Z3_Unknown`, then
# drop the now-dangling string literal on the following line if the
# failwith was split across two lines.
import re

# Form: `failwith "..."` possibly with a newline between failwith and
# the string. Collapse any `failwith[ \n]*"<payload>"` to Z3_Unknown.
pat = re.compile(r'failwith[ \t\n]*"' + re.escape(payload) + r'"')
new_content, n = pat.subn(marker + '  Z3_Unknown', content)

if n == 0 and not already_patched:
    sys.stderr.write(
        "  ERROR: 296_z3_check_sat: failwith payload present but regex did "
        "not match in " + path + "\n"
    )
    sys.exit(1)

with open(path, "w") as f:
    f.write(new_content)
PYEOF

echo "  [296_z3_check_sat] applied: z3_check_sat -> Z3_Unknown (Phase 0)."
