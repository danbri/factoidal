#!/bin/bash
# tools/lean-shacl-scores.sh — score the Lean SHACL validator on every
# vendored SHACL corpus, and print the F* tree's number beside each.
#
# The Lean probe (`l4shacl`) reads a manifest path, so it could always
# have been pointed at the SHACL 1.2 suite. Nothing did: the probe's
# default is the SHACL 1.0 `data-shapes-test-suite`, and the dashboard
# carried only that. This script runs all of them so the numbers exist
# and stay comparable.
#
# ⚠️ The node-expr row reports a DENOMINATOR the probe found, not the
# number of tests in the suite. `sht:EvalNodeExpr` is not recognised by
# the probe, and that suite links its tests with `mf:entries` rather
# than `mf:include`, so the probe walks in and reports "out of 2". A
# denominator that small next to the F* column is the signal that the
# suite is UNREAD, not that it is passing. See
# https://github.com/danbri/factoidal/issues/553.
#
# The rules suite is no longer in that state: `lake exe l4shacl-rules`
# (Harness/ShaclRulesRun.lean) reads all four of its sub-manifests, and
# this script runs it as a separate step below.
#
# Usage: tools/lean-shacl-scores.sh
# Always exits 0 — this reports, it does not gate.

set -uo pipefail
REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$REPO_ROOT" || exit 1

PROBE="formal/lean4/.lake/build/bin/l4shacl"
if [ ! -x "$PROBE" ]; then
  echo "MISSING: $PROBE (run: cd formal/lean4 && lake build l4shacl)"
  exit 1
fi

S12="third_party/testing/shacl/shacl12-test-suite/tests"
S10="third_party/testing/shacl/data-shapes-test-suite/tests"

# label | manifest | F* pass | F* total  (F* numbers from docs/test-results/latest.json)
SUITES="
shacl 1.0 core|$S10/core/manifest.ttl|98|98
shacl 1.2 core|$S12/core/manifest.ttl|138|138
shacl 1.2 node-expr|$S12/node-expr/manifest.ttl|142|142
shacl 1.2 sparql|$S12/sparql/manifest.ttl|25|25
"

printf '%-22s | %-28s | %s\n' "suite" "Lean 4" "F*"
printf '%-22s-+-%-28s-+-%s\n' "----------------------" "----------------------------" "----------"

while IFS='|' read -r label manifest fpass ftotal; do
  [ -z "$label" ] && continue
  if [ ! -f "$manifest" ]; then
    printf '%-22s | %-28s | %s\n' "$label" "manifest missing" "$fpass pass (out of $ftotal)"
    continue
  fi
  LINE=$(timeout 900 "$PROBE" "$manifest" 2>&1 | grep "TOTAL" | tail -1)
  P=$(echo "$LINE" | grep -oP '\d+(?= pass)' || echo "?")
  F=$(echo "$LINE" | grep -oP '\d+(?= fail)' || echo "?")
  T=$(echo "$LINE" | grep -oP '\d+(?=\))' || echo "?")
  printf '%-22s | %-28s | %s\n' "$label" "$P pass, $F fail (out of $T)" "$fpass pass (out of $ftotal)"
done <<< "$SUITES"

echo ""
echo "A Lean denominator far below the F* one means the probe did not READ"
echo "those tests. It is not a pass rate."

# The rules suite has its own runner: the `srt:` test types and the
# `mf:entries` linking are not what `l4shacl` walks.
RULES_PROBE="formal/lean4/.lake/build/bin/l4shacl-rules"
echo ""
if [ -x "$RULES_PROBE" ]; then
  RLINE=$(timeout 900 "$RULES_PROBE" 2>&1 | grep "TOTAL" | tail -1)
  RP=$(echo "$RLINE" | grep -oP '\d+(?= pass)' || echo "?")
  RF=$(echo "$RLINE" | grep -oP '\d+(?= fail)' || echo "?")
  RT=$(echo "$RLINE" | grep -oP '\d+(?=\))' || echo "?")
  printf '%-22s | %-28s | %s\n' "shacl 1.2 rules" "$RP pass, $RF fail (out of $RT)" "88 pass (out of 88)"
  echo ""
  echo "The rules gap is the SPARQL 1.2 reifying-triple and annotation"
  echo "syntax the Lean parser does not accept, measured in"
  echo "https://github.com/danbri/factoidal/issues/556 — not a SHACL Rules gap."
else
  printf '%-22s | %-28s | %s\n' "shacl 1.2 rules" "MISSING l4shacl-rules" "88 pass (out of 88)"
  echo "(run: cd formal/lean4 && lake build l4shacl-rules)"
fi
