#!/bin/bash
# bin/hdt-probe/check.sh — stage-1 regression pins for the HDT
# container reader (HDT.Container.fst) over the two real vendored
# fixtures in third_party/testing/hdt/ (reference-implementation-
# generated; provenance in that directory's README.md).
#
# Usage: check.sh [path-to-hdt_probe-binary]
#   Default binary: bin/<platform>/hdt_probe (once build-ocaml.sh
#   registration lands), falling back to ./hdt_probe next to this
#   script. Until the module is registered in build-ocaml.sh, build
#   ad hoc per docs/designissues/2026-07-06-hdt-program-plan.md
#   stage 1 (extract HDT.Container.fst, compile against
#   ocaml-output, link hdt_probe.ml).
#
# Exit 0 iff every pinned assertion holds. Per CLAUDE.md rule #14 no
# failure is swallowed; per rule #25 the summary is worded, not a
# bare ratio.

set -uo pipefail
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
FIXTURES="$REPO_ROOT/third_party/testing/hdt"

PLATFORM_BIN="$REPO_ROOT/bin/$(uname -s | tr '[:upper:]' '[:lower:]')-$(uname -m)/hdt_probe"
PROBE="${1:-}"
if [[ -z "$PROBE" ]]; then
  if [[ -x "$PLATFORM_BIN" ]]; then PROBE="$PLATFORM_BIN";
  elif [[ -x "$SCRIPT_DIR/hdt_probe" ]]; then PROBE="$SCRIPT_DIR/hdt_probe";
  else echo "ERROR: no hdt_probe binary found; pass its path as \$1" >&2; exit 2; fi
fi

PASS=0
FAIL=0

expect () { # expect <logfile> <grep-pattern> <label>
  local log="$1" pat="$2" label="$3"
  if grep -qE "$pat" "$log"; then
    PASS=$((PASS + 1)); echo "  ok    $label"
  else
    FAIL=$((FAIL + 1)); echo "  FAIL  $label (pattern: $pat)"
  fi
}

TMPLOG="$(mktemp)"
trap 'rm -f "$TMPLOG"' EXIT

echo "--- rdf-mt-test002.hdt (input: 1 triple) ---"
RC=0; timeout 120 "$PROBE" "$FIXTURES/rdf-mt-test002.hdt" > "$TMPLOG" 2>&1 || RC=$?
if [[ $RC -ne 0 ]]; then echo "  FAIL  probe exited rc=$RC"; FAIL=$((FAIL + 1)); cat "$TMPLOG"; else
  expect "$TMPLOG" '^file *: .*2040 bytes'                         "file size 2040"
  expect "$TMPLOG" 'global.*'                                      "global CI parsed"
  expect "$TMPLOG" 'format *: <http://purl\.org/HDT/hdt#HDTv1>'    "global format IRI"
  expect "$TMPLOG" 'header data : bytes 69 \.\. 1703 \(1634'       "header data range"
  expect "$TMPLOG" 'shared *: bytes 1777 \.\. 1794 .*strings=0'    "shared section empty"
  expect "$TMPLOG" 'subjects *: bytes 1794 \.\. 1836 .*strings=1'  "subjects section"
  expect "$TMPLOG" 'predicates *: bytes 1836 \.\. 1878 .*strings=1' "predicates section"
  expect "$TMPLOG" 'objects *: bytes 1878 \.\. 1950 .*strings=1'   "objects section"
  expect "$TMPLOG" 'triples data: starts at byte 2006 \(order=1\)' "triples data offset + SPO"
  expect "$TMPLOG" 'header RDF  : 22 triples'                      "header N-Triples decoded"
  expect "$TMPLOG" 'void#triples> "1"'                             "void:triples matches input"
  if grep -q MISMATCH "$TMPLOG"; then
    FAIL=$((FAIL + 1)); echo "  FAIL  a CRC16 mismatch was reported"
  else PASS=$((PASS + 1)); echo "  ok    all CI CRC16s validate"; fi
fi

echo "--- rml-core-ontology.hdt (input: 343 triples) ---"
RC=0; timeout 120 "$PROBE" "$FIXTURES/rml-core-ontology.hdt" > "$TMPLOG" 2>&1 || RC=$?
if [[ $RC -ne 0 ]]; then echo "  FAIL  probe exited rc=$RC"; FAIL=$((FAIL + 1)); cat "$TMPLOG"; else
  expect "$TMPLOG" '^file *: .*9124 bytes'                          "file size 9124"
  expect "$TMPLOG" 'header data : bytes 69 \.\. 1770 \(1701'        "header data range"
  expect "$TMPLOG" 'shared *: bytes 1846 \.\. 2278 .*strings=39'    "shared: 39 strings"
  expect "$TMPLOG" 'subjects *: bytes 2278 \.\. 2886 .*strings=45'  "subjects: 45 strings"
  expect "$TMPLOG" 'predicates *: bytes 2886 \.\. 3268 .*strings=22' "predicates: 22 strings"
  expect "$TMPLOG" 'objects *: bytes 3268 \.\. 8353 .*strings=134'  "objects: 134 strings"
  expect "$TMPLOG" 'triples data: starts at byte 8409 \(order=1\)'  "triples data offset + SPO"
  expect "$TMPLOG" 'void#triples> "343"'                            "void:triples matches input"
  expect "$TMPLOG" 'dictionarynumSharedSubjectObject> "39"'         "header shared-count matches shared section"
  expect "$TMPLOG" 'void#distinctSubjects> "84"'                    "distinctSubjects 84 = 39 shared + 45 subjects"
  expect "$TMPLOG" 'void#distinctObjects> "173"'                    "distinctObjects 173 = 39 shared + 134 objects"
  if grep -q MISMATCH "$TMPLOG"; then
    FAIL=$((FAIL + 1)); echo "  FAIL  a CRC16 mismatch was reported"
  else PASS=$((PASS + 1)); echo "  ok    all CI CRC16s validate"; fi
fi

echo "--- truncated container must fail loudly ---"
TRUNC="$(mktemp --suffix=.hdt)"
head -c 1900 "$FIXTURES/rdf-mt-test002.hdt" > "$TRUNC"   # cuts inside the objects PFC section
RC=0; timeout 120 "$PROBE" "$TRUNC" > "$TMPLOG" 2>&1 || RC=$?
rm -f "$TRUNC"
if [[ $RC -eq 1 ]] && grep -q "PARSE FAILED" "$TMPLOG"; then
  PASS=$((PASS + 1)); echo "  ok    truncation -> loud parse failure (rc=1)"
else
  FAIL=$((FAIL + 1)); echo "  FAIL  truncated file did not fail loudly (rc=$RC)"
fi

echo "============================================================"
TOTAL=$((PASS + FAIL))
echo "hdt-probe stage-1 checks: ${PASS} pass, ${FAIL} fail (out of ${TOTAL})"
[[ $FAIL -eq 0 ]]
