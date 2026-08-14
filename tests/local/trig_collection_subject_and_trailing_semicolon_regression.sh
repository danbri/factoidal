#!/usr/bin/env bash
# Regression for issues #433 and #434 (found by the #429 grading fix
# that made TestTrigPositiveSyntax use the STRICT TriG parse path
# instead of the always-succeeds lenient one -- see
# docs/designissues/2026-08-14-syntax-grading-audit.md).
#
# BUG #433: a collection `( 1 2 3 )` used as an ordinary triple SUBJECT
# in the default graph is wrongly rejected by Parser.TriG.fst's RC3
# guard ("collection cannot be used as graph name or subject in TriG"
# at parse_trig_statement, formal/fstar/Parser.TriG.fst). RC3 is meant
# to forbid a collection as a GRAPH NAME only -- it must not block the
# legal "collection as subject" case.
# Witness: third_party/testing/w3c/rdf/rdf11/rdf-trig/trig-turtle-06.trig
#
# BUG #434: a trailing `;` immediately before `}` (no final `.`) inside
# a graph block is wrongly rejected. The TriG grammar allows the last
# statement in a block to omit the final `.`, and predicateObjectList
# allows a trailing separator with nothing after it
# (Parser.Turtle.fst's parse_predicate_object_list_rev /
# parse_trailing_semicolons_rev only recognised '.', ']', ';', '|' as
# "end of predicate-object list" after a semicolon -- '}' was missing).
# Witness: third_party/testing/w3c/rdf/rdf11/rdf-trig/trig-syntax-struct-07.trig
#
# Reproduced against the strict CLI path (`factoidal --dump --format
# trig --data FILE`, which loads via Parser.TriG's *_diagnostic entry
# points). Before the fix, both witnesses print:
#   "Error: FILE parsed to zero triples but is not an empty document —
#    the parse failed and the result would have been silently empty."
# and exit 1.

set -u

ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
BIN="${FACTOIDAL_BIN:-${ROOT}/bin/linux-x86_64/factoidal}"
WORKDIR="$(mktemp -d)"
trap 'rm -rf "${WORKDIR}"' EXIT

if [[ ! -x "${BIN}" ]]; then
  echo "SKIP: no binary at ${BIN} (build not yet run)"
  exit 0
fi

pass_count=0
fail_count=0

check() {
  local name="$1" expected="$2" actual="$3"
  if [[ "${actual}" == "${expected}" ]]; then
    echo "PASS ${name}"
    pass_count=$((pass_count + 1))
  else
    echo "FAIL ${name}: expected [${expected}] got [${actual}]"
    fail_count=$((fail_count + 1))
  fi
}

run_dump() {
  # run_dump LABEL FIXTURE_CONTENT -> writes stdout/stderr/rc into
  # WORKDIR/${LABEL}-{stdout,stderr,rc}.txt
  local label="$1" content="$2"
  local fixture="${WORKDIR}/${label}.trig"
  printf '%s' "${content}" > "${fixture}"
  local stdout_out="${WORKDIR}/${label}-stdout.txt"
  local stderr_out="${WORKDIR}/${label}-stderr.txt"
  timeout 30 "${BIN}" --dump --format trig --data "${fixture}" \
    >"${stdout_out}" 2>"${stderr_out}"
  echo "$?" > "${WORKDIR}/${label}-rc.txt"
}

count_lines() {
  # Count non-empty stdout lines (== triple count for N-Triples dump).
  grep -c . "$1" 2>/dev/null || true
}

# --- BUG #433: collection as ordinary subject must be ACCEPTED -------

run_dump "collection-subject" \
'( 1 2 3 ) <http://example/p> ( 4 5 6 ) .'
check "433-collection-subject-exit-zero" "0" "$(cat "${WORKDIR}/collection-subject-rc.txt")"
# 3+3 rdf:first/rest-chain triples per list (6 each) + 1 connecting
# triple = 13 triples total.
check "433-collection-subject-triple-count" "13" "$(count_lines "${WORKDIR}/collection-subject-stdout.txt")"

# W3C witness itself, byte-for-byte (trig-turtle-06.trig).
WITNESS_433="${ROOT}/third_party/testing/w3c/rdf/rdf11/rdf-trig/trig-turtle-06.trig"
if [[ -f "${WITNESS_433}" ]]; then
  out433="${WORKDIR}/witness-433-stdout.txt"
  err433="${WORKDIR}/witness-433-stderr.txt"
  timeout 30 "${BIN}" --dump --format trig --data "${WITNESS_433}" \
    >"${out433}" 2>"${err433}"
  check "433-witness-trig-turtle-06-exit-zero" "0" "$?"
else
  echo "SKIP 433-witness-trig-turtle-06: fixture not present (run tools/ensure-test-env.sh)"
fi

# --- BUG #434: trailing ';' immediately before '}' must be ACCEPTED --

run_dump "trailing-semicolon" \
'{<http://example/s> <http://example/p> <http://example/o> ;}'
check "434-trailing-semicolon-exit-zero" "0" "$(cat "${WORKDIR}/trailing-semicolon-rc.txt")"
check "434-trailing-semicolon-triple-count" "1" "$(count_lines "${WORKDIR}/trailing-semicolon-stdout.txt")"

WITNESS_434="${ROOT}/third_party/testing/w3c/rdf/rdf11/rdf-trig/trig-syntax-struct-07.trig"
if [[ -f "${WITNESS_434}" ]]; then
  out434="${WORKDIR}/witness-434-stdout.txt"
  err434="${WORKDIR}/witness-434-stderr.txt"
  timeout 30 "${BIN}" --dump --format trig --data "${WITNESS_434}" \
    >"${out434}" 2>"${err434}"
  check "434-witness-trig-syntax-struct-07-exit-zero" "0" "$?"
else
  echo "SKIP 434-witness-trig-syntax-struct-07: fixture not present (run tools/ensure-test-env.sh)"
fi

# --- Controls that must keep working / keep being rejected -----------

# Control: collection as OBJECT (already worked before this fix; must
# keep working).
run_dump "collection-object" \
'@prefix : <http://example/> .
:s :p ( 1 2 3 ) .'
check "control-collection-object-exit-zero" "0" "$(cat "${WORKDIR}/collection-object-rc.txt")"
# 3-item list: 3 rdf:first + 3 rdf:rest triples + 1 connecting triple = 7.
check "control-collection-object-triple-count" "7" "$(count_lines "${WORKDIR}/collection-object-stdout.txt")"

# Control: collection genuinely used as a GRAPH NAME must still be
# REJECTED -- TriG's grammar has no production for this (a collection
# can only be followed by predicateObjectList '.', never by a
# wrappedGraph). This is the case RC3 was meant to guard.
run_dump "collection-as-graph-name" \
'( 1 2 3 ) { <http://example/s> <http://example/p> <http://example/o> . }'
check "control-collection-as-graph-name-still-rejected" "1" "$(cat "${WORKDIR}/collection-as-graph-name-rc.txt")"

# Control: a normal graph block with the final '.' present must keep
# working.
run_dump "graph-block-with-final-dot" \
'{<http://example/s> <http://example/p> <http://example/o> .}'
check "control-graph-block-final-dot-exit-zero" "0" "$(cat "${WORKDIR}/graph-block-with-final-dot-rc.txt")"
check "control-graph-block-final-dot-triple-count" "1" "$(count_lines "${WORKDIR}/graph-block-with-final-dot-stdout.txt")"

echo ""
echo "trig_collection_subject_and_trailing_semicolon_regression: ${pass_count} pass, ${fail_count} fail (out of $((pass_count + fail_count)))"
if [[ "${fail_count}" -gt 0 ]]; then
  exit 1
fi
exit 0
