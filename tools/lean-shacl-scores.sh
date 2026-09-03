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
# Two suites need their own runner, because `l4shacl` recognises
# neither the `srt:` (rules) nor the `sht:EvalNodeExpr` (node-expr)
# test types: `lake exe l4shacl-rules` and `lake exe l4shacl-nodeexpr`.
# Both run as separate steps below. Neither row is UNREAD any more
# (https://github.com/danbri/factoidal/issues/553).
#
# A Lean denominator far below the F* one still means the probe did not
# READ those tests. It is not a pass rate.
#
# Usage: tools/lean-shacl-scores.sh
#
# EXIT CODE (changed 2026-09-03). This script used to declare "always
# exits 0 — this reports, it does not gate". It also parsed the probe
# output with `grep -P`, which BSD grep rejects, so on macOS every
# number came out `?` and the script still exited 0. Silence read as
# success and the SHACL rows of an audit had to be measured by hand.
# Anti-pattern 30: a measurement tool that walked nothing must SAY so.
# The parse is now `sed -E` (portable), and the script exits 1 if any
# row failed to produce a number. It still does not gate on the SCORES
# themselves — a real failure count is reported, not an error.

set -uo pipefail
REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$REPO_ROOT" || exit 1

UNREAD=0   # rows that produced no number at all

# num <line> <keyword>  -> the integer before " <keyword>", or empty.
num() {
  printf '%s' "$1" | sed -nE "s/.*[^0-9]([0-9]+) $2.*/\1/p" | tail -1
}
# total <line> -> the integer inside "(out of N)", or empty.
total() {
  printf '%s' "$1" | sed -nE 's/.*\(out of ([0-9]+)\).*/\1/p' | tail -1
}

# run_row <label> <F* pass> <F* total> <command...>
run_row() {
  local label="$1" fpass="$2" ftotal="$3"; shift 3
  local line p f t
  line=$(timeout 900 "$@" 2>&1 | grep "TOTAL" | tail -1)
  p=$(num "$line" pass); f=$(num "$line" fail); t=$(total "$line")
  if [ -z "$p" ] || [ -z "$f" ] || [ -z "$t" ]; then
    UNREAD=$((UNREAD + 1))
    printf '%-22s | %-28s | %s\n' "$label" "UNREAD (no TOTAL line)" \
      "$fpass pass (out of $ftotal)"
    echo "  lean-shacl-scores: $label produced no parsable TOTAL line from: $*" >&2
    return
  fi
  printf '%-22s | %-28s | %s\n' "$label" "$p pass, $f fail (out of $t)" \
    "$fpass pass (out of $ftotal)"
}

PROBE="formal/lean4/.lake/build/bin/l4shacl"
if [ ! -x "$PROBE" ]; then
  echo "MISSING: $PROBE (run: cd formal/lean4 && lake build l4shacl)" >&2
  exit 1
fi

S12="third_party/testing/shacl/shacl12-test-suite/tests"
S10="third_party/testing/shacl/data-shapes-test-suite/tests"

# label | manifest | F* pass | F* total  (F* numbers from docs/test-results/latest.json)
SUITES="
shacl 1.0 core|$S10/core/manifest.ttl|98|98
shacl 1.2 core|$S12/core/manifest.ttl|138|138
shacl 1.2 sparql|$S12/sparql/manifest.ttl|25|25
"

printf '%-22s | %-28s | %s\n' "suite" "Lean 4" "F*"
printf '%-22s-+-%-28s-+-%s\n' "----------------------" "----------------------------" "----------"

ROWS=0
while IFS='|' read -r label manifest fpass ftotal; do
  [ -z "$label" ] && continue
  ROWS=$((ROWS + 1))
  if [ ! -f "$manifest" ]; then
    UNREAD=$((UNREAD + 1))
    printf '%-22s | %-28s | %s\n' "$label" "manifest missing" "$fpass pass (out of $ftotal)"
    echo "  lean-shacl-scores: manifest not found: $manifest" >&2
    continue
  fi
  run_row "$label" "$fpass" "$ftotal" "$PROBE" "$manifest"
done <<< "$SUITES"

if [ "$ROWS" -eq 0 ]; then
  echo "lean-shacl-scores: the suite table is empty -- nothing was measured" >&2
  exit 1
fi

echo ""
echo "A Lean denominator far below the F* one means the probe did not READ"
echo "those tests. It is not a pass rate."

# The node-expr and rules suites have their own runners: the `srt:`
# test types and the `sht:EvalNodeExpr` types are not what `l4shacl` walks.
NE_PROBE="formal/lean4/.lake/build/bin/l4shacl-nodeexpr"
echo ""
if [ -x "$NE_PROBE" ]; then
  run_row "shacl 1.2 node-expr" 142 142 "$NE_PROBE"
else
  UNREAD=$((UNREAD + 1))
  printf '%-22s | %-28s | %s\n' "shacl 1.2 node-expr" "MISSING l4shacl-nodeexpr" "142 pass (out of 142)"
  echo "(run: cd formal/lean4 && lake build l4shacl-nodeexpr)" >&2
fi

RULES_PROBE="formal/lean4/.lake/build/bin/l4shacl-rules"
echo ""
if [ -x "$RULES_PROBE" ]; then
  run_row "shacl 1.2 rules" 88 88 "$RULES_PROBE"
  echo ""
  echo "The rules gap is the SPARQL 1.2 reifying-triple and annotation"
  echo "syntax the Lean parser does not accept, measured in"
  echo "https://github.com/danbri/factoidal/issues/556 — not a SHACL Rules gap."
else
  UNREAD=$((UNREAD + 1))
  printf '%-22s | %-28s | %s\n' "shacl 1.2 rules" "MISSING l4shacl-rules" "88 pass (out of 88)"
  echo "(run: cd formal/lean4 && lake build l4shacl-rules)" >&2
fi

if [ "$UNREAD" -gt 0 ]; then
  echo "" >&2
  echo "lean-shacl-scores: $UNREAD of $((ROWS + 2)) rows produced NO number." >&2
  echo "A missing number is not a zero and not a pass. Exit 1." >&2
  exit 1
fi
exit 0
