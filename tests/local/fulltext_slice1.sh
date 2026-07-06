#!/usr/bin/env bash
set -euo pipefail

# Fulltext SPARQL Slice 1 end-to-end regressions.
# Design: docs/designissues/2026-07-05-fulltext-sparql-design.md
# Implementation: formal/fstar/SPARQL.FullText.fst + the dispatch hooks
# in SPARQL11.Algebra.fst/SPARQL11.Store.fst + the text:query object
# grammar in SPARQL11.Parser.fst.
#
# Exercises, against the real `factoidal` binary and a small Turtle
# fixture (tests/local/data/fulltext_sample.ttl):
#   - text:query 2-arity (bare string, no field restriction)
#   - AND (all-tokens) match semantics on a multi-word term
#   - list form with a field restriction: (rdfs:label "term")
#   - list form with a field restriction + limit: (rdfs:label "term" N)
#   - no-match returns zero rows
#   - an ordinary BGP triple pattern composing with text:query in the
#     same group (join semantics unaffected by the dispatch hook)

ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
BIN="${FACTOIDAL_BIN:-${ROOT}/formal/fstar/ocaml-output/factoidal}"
DATA="${ROOT}/tests/local/data/fulltext_sample.ttl"

pass_count=0
fail_count=0

# Runs a SELECT query and asserts the trailing "N result(s)" line
# matches $2 exactly.
assert_result_count() {
  local name="$1"
  local expected_count="$2"
  local query="$3"
  local out
  out="$("${BIN}" query --data "${DATA}" -e "${query}" 2>&1)" || {
    echo "FAIL ${name} (query errored)"
    echo "${out}"
    fail_count=$((fail_count + 1))
    return
  }
  local actual_count
  if [[ "${out}" == "(no results)" ]]; then
    actual_count=0
  else
    actual_count="$(echo "${out}" | rg -o '^[0-9]+ result\(s\)' | awk '{print $1}' || true)"
  fi
  if [[ "${actual_count}" == "${expected_count}" ]]; then
    echo "PASS ${name} (${actual_count} result(s))"
    pass_count=$((pass_count + 1))
  else
    echo "FAIL ${name} (expected ${expected_count} result(s), got '${actual_count}')"
    echo "${out}"
    fail_count=$((fail_count + 1))
  fi
}

# Runs a SELECT query and asserts the output contains/excludes given
# subject-IRI substrings (membership check — dataset order is not a
# ranking claim per design doc §6 Slice 1, so we don't assert row order).
assert_membership() {
  local name="$1"
  local query="$2"
  shift 2
  local out
  out="$("${BIN}" query --data "${DATA}" -e "${query}" 2>&1)" || {
    echo "FAIL ${name} (query errored)"
    echo "${out}"
    fail_count=$((fail_count + 1))
    return
  }
  local ok=1
  for expect in "$@"; do
    case "${expect}" in
      +*)
        if ! echo "${out}" | rg -q "${expect#+}"; then
          ok=0
          echo "  missing expected: ${expect#+}"
        fi
        ;;
      -*)
        if echo "${out}" | rg -q "${expect#-}"; then
          ok=0
          echo "  unexpectedly present: ${expect#-}"
        fi
        ;;
    esac
  done
  if [[ "${ok}" -eq 1 ]]; then
    echo "PASS ${name}"
    pass_count=$((pass_count + 1))
  else
    echo "FAIL ${name}"
    echo "${out}"
    fail_count=$((fail_count + 1))
  fi
}

# --- 2-arity: bare string, no field restriction (design doc §1) -----------
# "panel" appears (case-insensitively) in: panel1/panel2's rdfs:label,
# battery's rdfs:label, and controlpanel's dc:title (NOT its rdfs:label)
# -- 4 distinct subjects, proving the unrestricted scan covers every
# literal regardless of predicate.
assert_result_count "2-arity-bare-string" 4 '
PREFIX text: <http://jena.apache.org/text#>
SELECT ?s WHERE { ?s text:query "panel" }'

# --- AND (all-tokens) match semantics, design doc §7 slice-1 default -------
# Only panel1/panel2's labels contain BOTH "solar" and "panel"; battery's
# label has "panel" but not "solar" and must be excluded.
assert_result_count "and-semantics-multi-token" 2 '
PREFIX text: <http://jena.apache.org/text#>
SELECT ?s WHERE { ?s text:query "solar panel" }'
assert_membership "and-semantics-excludes-partial-match" '
PREFIX text: <http://jena.apache.org/text#>
SELECT ?s WHERE { ?s text:query "solar panel" }' \
  '+example.org/panel1' '+example.org/panel2' '-example.org/battery'

# --- List form with field restriction: (rdfs:label "term") ----------------
# Restricting to rdfs:label excludes controlpanel (whose *label* is
# "Interface unit" -- only its dc:title matches "panel") down to 3.
assert_result_count "list-form-field-restriction" 3 '
PREFIX text: <http://jena.apache.org/text#>
PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>
SELECT ?s WHERE { ?s text:query (rdfs:label "panel") }'
assert_membership "list-form-field-restriction-excludes-title-only-match" '
PREFIX text: <http://jena.apache.org/text#>
PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>
SELECT ?s WHERE { ?s text:query (rdfs:label "panel") }' \
  '+example.org/panel1' '+example.org/panel2' '+example.org/battery' '-example.org/controlpanel'

# --- List form with field restriction + limit: (rdfs:label "term" N) ------
# Slice 1 makes no ranking claim (design doc §6) -- assert the COUNT is
# capped, not which 2 of the 3 candidates come back.
assert_result_count "list-form-field-restriction-and-limit" 2 '
PREFIX text: <http://jena.apache.org/text#>
PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>
SELECT ?s WHERE { ?s text:query (rdfs:label "panel" 2) }'

# --- No-match returns zero rows --------------------------------------------
assert_result_count "no-match-returns-zero-rows" 0 '
PREFIX text: <http://jena.apache.org/text#>
SELECT ?s WHERE { ?s text:query "zzzznonexistentterm" }'

# --- Ordinary BGP pattern composes with text:query in the same group ------
# Unrestricted "panel" matches 4 subjects (see above); joining with
# ex:status "active" drops battery (status "retired"), leaving 3.
assert_result_count "bgp-composition-with-text-query" 3 '
PREFIX text: <http://jena.apache.org/text#>
PREFIX ex: <http://example.org/>
SELECT ?s WHERE { ?s text:query "panel" . ?s ex:status "active" . }'
assert_membership "bgp-composition-excludes-retired-match" '
PREFIX text: <http://jena.apache.org/text#>
PREFIX ex: <http://example.org/>
SELECT ?s WHERE { ?s text:query "panel" . ?s ex:status "active" . }' \
  '+example.org/panel1' '+example.org/panel2' '+example.org/controlpanel' '-example.org/battery'

echo "============================================================"
echo "fulltext_slice1: ${pass_count} pass, ${fail_count} fail (out of $((pass_count + fail_count)))"
if [[ "${fail_count}" -gt 0 ]]; then
  exit 1
fi
