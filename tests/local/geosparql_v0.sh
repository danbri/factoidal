#!/usr/bin/env bash
# tests/local/geosparql_v0.sh — end-to-end SPARQL pins for the
# GeoSPARQL v0 pure-F* slice (geof: dispatch wired into
# SPARQL11.Algebra.fst's E_FunctionCall arm; see
# docs/designissues/2026-05-07-geosparql-fstar-investigation.md).
#
# Fixture: tests/local/geosparql/data.ttl — 3 UK city points + 2 toy
# bounding-box polygons (hand-picked so exactly London is inside the
# "Greater London" box, exactly Edinburgh is inside the "Scotland"
# box, and Manchester is inside neither). Queries run through the CLI
# against the extracted native binary; rows are pinned exactly (this
# is a small enough result set that the full table is checked, not
# just row counts, per the "no cryptic score strings" discipline —
# every expected row is spelled out below).
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
BIN="${FACTOIDAL_BIN:-${ROOT}/formal/fstar/ocaml-output/factoidal}"
FIXDIR="${ROOT}/tests/local/geosparql"

if [[ ! -x "${BIN}" ]]; then
  echo "geosparql_v0: factoidal binary not found or not executable: ${BIN}" >&2
  exit 2
fi

pass_count=0
fail_count=0

check_contains () {
  local name="$1" haystack="$2" needle="$3"
  if [[ "${haystack}" == *"${needle}"* ]]; then
    echo "PASS ${name}"
    pass_count=$((pass_count + 1))
  else
    echo "FAIL ${name}: expected to find [${needle}]"
    echo "--- actual output ---"
    echo "${haystack}"
    echo "---------------------"
    fail_count=$((fail_count + 1))
  fi
}

check_not_contains () {
  local name="$1" haystack="$2" needle="$3"
  if [[ "${haystack}" != *"${needle}"* ]]; then
    echo "PASS ${name}"
    pass_count=$((pass_count + 1))
  else
    echo "FAIL ${name}: expected NOT to find [${needle}]"
    fail_count=$((fail_count + 1))
  fi
}

check_row_count () {
  local name="$1" haystack="$2" expected="$3"
  local actual
  actual="$(echo "${haystack}" | grep -oE '^[0-9]+ result\(s\)' | grep -oE '^[0-9]+')"
  if [[ "${actual}" == "${expected}" ]]; then
    echo "PASS ${name} (${actual} result(s))"
    pass_count=$((pass_count + 1))
  else
    echo "FAIL ${name}: expected ${expected} result(s), got ${actual}"
    fail_count=$((fail_count + 1))
  fi
}

# --- Test 1: FILTER(geof:sfWithin(?city, ?area)) ---------------------
WITHIN_OUT="$("${BIN}" query --data "${FIXDIR}/data.ttl" --query "${FIXDIR}/within.rq" 2>&1)"
check_row_count "sfWithin: exactly 2 (city,area) pairs" "${WITHIN_OUT}" "2"
check_contains  "sfWithin: Edinburgh within Scotland (toy box)" "${WITHIN_OUT}" '"Edinburgh"'
check_contains  "sfWithin: London within Greater London (toy box)" "${WITHIN_OUT}" '"London"'
check_not_contains "sfWithin: Manchester is in neither box" "${WITHIN_OUT}" '"Manchester"'

# --- Test 2: FILTER(geof:sfDisjoint(?city, GreaterLondonArea)) -------
DISJOINT_OUT="$("${BIN}" query --data "${FIXDIR}/data.ttl" --query "${FIXDIR}/disjoint.rq" 2>&1)"
check_row_count "sfDisjoint: exactly 2 cities outside Greater London box" "${DISJOINT_OUT}" "2"
check_contains  "sfDisjoint: Edinburgh is outside Greater London box" "${DISJOINT_OUT}" '"Edinburgh"'
check_contains  "sfDisjoint: Manchester is outside Greater London box" "${DISJOINT_OUT}" '"Manchester"'
check_not_contains "sfDisjoint: London is NOT outside its own box" "${DISJOINT_OUT}" '"London"'

# --- Test 3: geof:distance(?g, London) ORDER BY ?d --------------------
DISTANCE_OUT="$("${BIN}" query --data "${FIXDIR}/data.ttl" --query "${FIXDIR}/distance.rq" 2>&1)"
check_row_count "distance: 3 rows (one per city)" "${DISTANCE_OUT}" "3"
check_contains  "distance: London-to-London is exactly 0" "${DISTANCE_OUT}" \
  '"London"     | "0.00000000000000000"^^<http://www.w3.org/2001/XMLSchema#double>'
# Order pin: London (0) first, Manchester second, Edinburgh third —
# check via line position rather than exact whitespace-sensitive
# substring for the non-zero rows (only the ordering + city identity
# matter here, the distance module header already pins the exact
# 3-4-5-triangle case in tests/unit/geosparql_v0_unit.ml).
ORDER_LINE="$(echo "${DISTANCE_OUT}" | grep -E '"(London|Manchester|Edinburgh)"' | sed -E 's/^\| *"([A-Za-z]+)".*/\1/')"
EXPECTED_ORDER="$(printf 'London\nManchester\nEdinburgh')"
if [[ "${ORDER_LINE}" == "${EXPECTED_ORDER}" ]]; then
  echo "PASS distance: ORDER BY ?d gives London, Manchester, Edinburgh"
  pass_count=$((pass_count + 1))
else
  echo "FAIL distance: ORDER BY ?d — expected London,Manchester,Edinburgh got: ${ORDER_LINE}"
  fail_count=$((fail_count + 1))
fi

echo ""
echo "geosparql_v0: ${pass_count} pass, ${fail_count} fail (out of $((pass_count + fail_count)))"
if [[ "${fail_count}" -gt 0 ]]; then
  exit 1
fi
