#!/bin/bash
# tools/hdt-tree-differential.sh — compare the F* and Lean 4 HDT
# readers field by field over the vendored fixtures.
#
# HDT.Container.fst, HDT.Dictionary.fst and HDT.Triples.fst and their
# Lean counterparts parse the same byte layout. Comparing the two
# probes' output checks the Lean port against a reader that was
# already measured against the reference implementation. A count that
# matches by luck is possible; 54 lines of offsets, CRC values,
# round-trip scores and an enumeration compared with the source
# document matching by luck is not.
#
# Both probes print the same skeleton and the same three stage-2
# blocks: every control block's byte offsets, format IRI, property
# string and CRC16 (stored AND computed), the header data range, the
# four PFC sections' boundaries and counts, the triples data offset,
# the header triple count, the PFC decode with its four CRCs and
# term-parse counts, the per-section ID round trip, the role-level
# round trip that exercises the shared-section ID arithmetic, the
# BitmapTriples counts and CRCs, the rank1/select1 identity over every
# valid index of both bitmaps, and the full enumeration compared with
# the source document as sorted canonical N-Triples.
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

# Each fixture's ground truth: the source document it was built from.
ground_truth_for() {
  case "$1" in
    *rdf-mt-test002.hdt)
      echo "third_party/testing/w3c/rdf/rdf11/rdf-mt/datatypes/test002.nt" ;;
    *rml-core-ontology.hdt)
      echo "third_party/testing/rml-modules/rml-core/ontology/documentation/ontology.nt" ;;
    *) echo "" ;;
  esac
}

for f in third_party/testing/hdt/*.hdt; do
  NT="$(ground_truth_for "$f")"
  if [ -n "$NT" ] && [ ! -f "$NT" ]; then
    echo "DIFFER $f: ground truth $NT is missing (run tools/ensure-test-env.sh)"
    DIFFER=$((DIFFER + 1))
    continue
  fi

  # The F* probe interleaves the parts differently: the skeleton, then
  # the header triples themselves, then the three stage-2 blocks, then
  # stage 3 with a per-subject pair-count listing, then the two
  # ground-truth comparisons. Take the parts both trees print: the
  # skeleton (cut at the summary line the Lean probe stops at), the
  # three stage-2 blocks, the two stage-3 blocks that are not the
  # per-subject listing, and the stage-3 ground-truth block.
  timeout 600 "$FSTAR_PROBE" "$f" $NT > "$WORK/raw.txt" 2>&1
  FSTAR_RC=$?
  {
    sed -n '1,/^header RDF/p' "$WORK/raw.txt"
    sed -n '/^--- stage 2: PFC dictionary decode ---$/,/^--- stage 3: BitmapTriples/p' \
      "$WORK/raw.txt" | sed '$d'
    sed -n '/^--- stage 3: BitmapTriples navigation ---$/,/^--- stage 3: per-subject/p' \
      "$WORK/raw.txt" | sed '$d'
    sed -n '/^--- stage 3: enumeration vs ground truth/,/^--- stage 2: dictionary term set/p' \
      "$WORK/raw.txt" | sed '$d'
  } | normalise > "$WORK/fstar.txt"

  timeout 600 "$LEAN_PROBE" --verbose "$f" $NT 2>&1 \
    | grep -v '^PASS\|^FAIL\|^HDT container' | normalise > "$WORK/lean.txt"
  LEAN_RC=$?

  if [ "$FSTAR_RC" -ne 0 ] || [ "$LEAN_RC" -ne 0 ]; then
    echo "DIFFER $f: a probe exited non-zero (F* $FSTAR_RC, Lean $LEAN_RC)"
    DIFFER=$((DIFFER + 1))
    continue
  fi

  # A run that never reached the strongest check must not be reported
  # as agreement.
  if ! grep -q 'sorted N-Triples compare) -> MATCH' "$WORK/lean.txt"; then
    echo "DIFFER $f: the Lean probe did not report an enumeration MATCH"
    DIFFER=$((DIFFER + 1))
    continue
  fi

  if diff -u "$WORK/fstar.txt" "$WORK/lean.txt" > "$WORK/d.txt"; then
    LINES=$(wc -l < "$WORK/fstar.txt")
    echo "AGREE  $f: $LINES container, dictionary and triples lines identical"
    AGREE=$((AGREE + 1))
  else
    echo "DIFFER $f:"
    cat "$WORK/d.txt"
    DIFFER=$((DIFFER + 1))
  fi
done

TOTAL=$((AGREE + DIFFER))
echo ""
echo "HDT reader, F* vs Lean 4: $AGREE agree, $DIFFER differ (out of $TOTAL)"
[ "$DIFFER" -eq 0 ]
