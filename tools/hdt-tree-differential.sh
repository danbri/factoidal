#!/bin/bash
# tools/hdt-tree-differential.sh — compare the F* and Lean 4 HDT
# container readers field by field over the vendored fixtures.
#
# HDT.Container.fst and L4Factoidal/HDT/Container.lean parse the same
# byte layout. Both probes print the same skeleton: every control
# block's byte offsets, format IRI, property string and CRC16 (stored
# AND computed), the header data range, the four PFC sections'
# boundaries and counts, the triples data offset, and the header
# triple count from each tree's own N-Triples parser.
#
# Comparing the two outputs checks the Lean port against a reader that
# was already measured against the reference implementation. A count
# that matches by luck is possible; 27 lines of offsets and CRC values
# matching by luck is not.
#
# The two probes differ in ONE line of wording: the F* probe names its
# parser module `Parser.NTriples`, the Lean probe says "the verified
# N-Triples parser". That line is normalised below rather than left to
# show up as a difference every run.
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

# Both probes print the same parser under two names. Normalise it.
normalise() {
  sed -e 's/(via verified Parser\.NTriples)/(via an N-Triples parser)/' \
      -e 's/(via the verified N-Triples parser)/(via an N-Triples parser)/'
}

AGREE=0
DIFFER=0

for f in third_party/testing/hdt/*.hdt; do
  # The F* probe follows the skeleton with the header triples
  # themselves; cut at the summary line the Lean probe stops at.
  timeout 600 "$FSTAR_PROBE" "$f" 2>&1 \
    | sed -n '1,/^header RDF/p' | normalise > "$WORK/fstar.txt"
  FSTAR_RC=$?
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
    echo "AGREE  $f: $LINES skeleton lines identical"
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
