#!/bin/bash
# tools/hdt-tree-differential.sh — compare the F* and Lean 4 HDT
# readers field by field over the vendored fixtures.
#
# HDT.Container.fst + HDT.Dictionary.fst and their Lean counterparts
# parse the same byte layout. Comparing the two probes' output checks
# the Lean port against a reader that was already measured against the
# reference implementation. A count that matches by luck is possible;
# 42 lines of offsets, CRC values and round-trip scores matching by
# luck is not.
#
# Both probes print the same skeleton and the same three stage-2
# blocks: every control block's byte offsets, format IRI, property
# string and CRC16 (stored AND computed), the header data range, the
# four PFC sections' boundaries and counts, the triples data offset,
# the header triple count, the PFC decode with its four CRCs and
# term-parse counts, the per-section ID round trip, and the role-level
# round trip that exercises the shared-section ID arithmetic.
#
# Two cosmetic differences are normalised rather than left to show up
# every run: the F* probe names its parser module `Parser.NTriples`
# where the Lean probe says "the verified N-Triples parser", and the
# two space their section blocks differently.
#
# Usage: tools/hdt-tree-differential.sh
# Exit 0 iff every field agrees for every fixture.

set -uo pipefail
REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$REPO_ROOT" || exit 1

PLATFORM="$(uname -s | tr '[:upper:]' '[:lower:]')-$(uname -m)"
FSTAR_PROBE="bin/$PLATFORM/hdt_probe"
LEAN_PROBE="formal/lean4/.lake/build/bin/l4hdt"

if [ ! -x "$FSTAR_PROBE" ]; then
  echo "MISSING: $FSTAR_PROBE (build it, or see bin/hdt-probe/check.sh)"
  exit 1
fi
if [ ! -x "$LEAN_PROBE" ]; then
  echo "MISSING: $LEAN_PROBE (run: cd formal/lean4 && lake build l4hdt)"
  exit 1
fi

WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT

# Both probes print the same parser under two names, and they space
# their section blocks differently. Normalise the name and drop blank
# lines; every remaining line is content.
normalise() {
  sed -e 's/(via verified Parser\.NTriples)/(via an N-Triples parser)/' \
      -e 's/(via the verified N-Triples parser)/(via an N-Triples parser)/' \
    | grep -v '^[[:space:]]*$'
}

AGREE=0
DIFFER=0

for f in third_party/testing/hdt/*.hdt; do
  # The F* probe interleaves the parts differently: the skeleton, then
  # the header triples themselves, then the three stage-2 blocks, then
  # stage 3, then a ground-truth comparison that needs a source .nt.
  # Take the skeleton (cut at the summary line the Lean probe stops
  # at) and the three stage-2 blocks, which is what both trees print.
  timeout 600 "$FSTAR_PROBE" "$f" > "$WORK/raw.txt" 2>&1
  FSTAR_RC=$?
  {
    sed -n '1,/^header RDF/p' "$WORK/raw.txt"
    sed -n '/^--- stage 2: PFC dictionary decode ---$/,/^--- stage 3/p' "$WORK/raw.txt" \
      | sed '$d'
  } | normalise > "$WORK/fstar.txt"
  timeout 600 "$LEAN_PROBE" --verbose "$f" 2>&1 \
    | grep -v '^PASS\|^FAIL\|^HDT container\|^$' | normalise > "$WORK/lean.txt"
  LEAN_RC=$?

  if [ "$FSTAR_RC" -ne 0 ] || [ "$LEAN_RC" -ne 0 ]; then
    echo "DIFFER $f: a probe exited non-zero (F* $FSTAR_RC, Lean $LEAN_RC)"
    DIFFER=$((DIFFER + 1))
    continue
  fi

  if diff -u "$WORK/fstar.txt" "$WORK/lean.txt" > "$WORK/d.txt"; then
    LINES=$(wc -l < "$WORK/fstar.txt")
    echo "AGREE  $f: $LINES container and dictionary lines identical"
    AGREE=$((AGREE + 1))
  else
    echo "DIFFER $f:"
    cat "$WORK/d.txt"
    DIFFER=$((DIFFER + 1))
  fi
done

TOTAL=$((AGREE + DIFFER))
echo ""
echo "HDT container, F* vs Lean 4: $AGREE agree, $DIFFER differ (out of $TOTAL)"
[ "$DIFFER" -eq 0 ]
