#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
BIN="${ROOT}/formal/fstar/ocaml-output/factoidal"
QUERY_DIR="${ROOT}/tests/local/sparql"
TMPDIR="${TMPDIR:-/tmp}"

pass_count=0
fail_count=0
BERLIN_HDT="${BERLIN_HDT:-/tmp/Corpus3/berlin-dbpedia-page/v1/data.hdt}"
BERLIN_GRAPH_IRI="${BERLIN_GRAPH_IRI:-https://factoidaldb.com/id/graph/berlin}"

run_parser_pass() {
  local name="$1"
  local query_file="$2"
  local output_file="${TMPDIR}/factoidal_sparql_regression_${name}.out"
  shift 2

  if "${BIN}" "$@" --query "${query_file}" >"${output_file}" 2>&1; then
    echo "PASS ${name}"
    cat "${output_file}"
    pass_count=$((pass_count + 1))
  else
    echo "FAIL ${name}"
    cat "${output_file}"
    fail_count=$((fail_count + 1))
  fi
}

run_parser_pass "prefix-a-semicolon" "${QUERY_DIR}/prefix_a_semicolon.rq" \
  --data-hdt "${BERLIN_HDT}"

run_parser_pass "signed-numeric-literals" \
  "${ROOT}/tests/w3c/sparql/sparql10/expr-ops/query-add-literals.rq"

run_parser_pass "named-graph" "${QUERY_DIR}/berlin_named_graph.rq" \
  --named-hdt "${BERLIN_GRAPH_IRI}=${BERLIN_HDT}"

run_parser_pass "bind-values" "${QUERY_DIR}/berlin_bind_values.rq" \
  --data-hdt "${BERLIN_HDT}"

run_parser_pass "named-ask" "${QUERY_DIR}/berlin_named_ask.rq" \
  --named-hdt "${BERLIN_GRAPH_IRI}=${BERLIN_HDT}"

run_parser_pass "named-group" "${QUERY_DIR}/berlin_named_group.rq" \
  --named-hdt "${BERLIN_GRAPH_IRI}=${BERLIN_HDT}"

run_parser_pass "named-subselect" "${QUERY_DIR}/berlin_named_subselect.rq" \
  --named-hdt "${BERLIN_GRAPH_IRI}=${BERLIN_HDT}"

echo "pass=${pass_count} fail=${fail_count}"

if [[ "${fail_count}" -ne 0 ]]; then
  exit 1
fi

exit 0
