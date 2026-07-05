#!/usr/bin/env bash
# Regression: the CLI's parse-stream query fast path (docs/designissues/
# 2026-07-05-disk-backed-db-perf-review.md, roadmap "bound in-memory
# query memory" -- bin/factoidal-cli/factoidal_cli.ml, dispatched via
# SPARQL_Plan_Streamable.streamable_shape) must return output BYTE-
# IDENTICAL to the existing materialise-then-evaluate path, for every
# targeted shape and for shapes that must fall through untouched.
#
# Mechanism: FACTOIDAL_DISABLE_STREAM_FASTPATH=1 forces the CLI to skip
# the fast-path dispatch entirely (see factoidal_cli.ml's gate right
# after SPARQL parsing), so the same binary/fixture/query pair can be
# run twice -- once fast, once slow -- and diffed. A silent divergence
# here means the shape recognizer is over-matching (answering a query
# it doesn't actually have the semantics to answer), which is exactly
# the soundness failure class this suite exists to catch before it
# reaches the W3C suite.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
WORKDIR="$(mktemp -d)"
trap 'rm -rf "${WORKDIR}"' EXIT
BIN="${FACTOIDAL_BIN:-${ROOT}/formal/fstar/ocaml-output/factoidal}"

if [[ ! -x "${BIN}" ]]; then
  echo "FATAL: factoidal binary not found/executable at ${BIN}" >&2
  echo "       (run formal/fstar/build-ocaml.sh extract compile first)" >&2
  exit 2
fi

pass_count=0
fail_count=0

# Runs the query on both paths (fast = default, slow = env-disabled)
# and asserts the JSON output is byte-identical, then (separately)
# checks the value the FAST path returned against an independently
# known expected substring -- so a bug that made both paths agree on
# the same WRONG answer wouldn't slip through as a false pass.
check_query () {
  local name="$1" data_flag="$2" data_file="$3" query="$4" expect_substr="$5"

  local fast_out slow_out
  fast_out="$("${BIN}" "${data_flag}" "${data_file}" -e "${query}" --output json 2>&1)"
  slow_out="$(FACTOIDAL_DISABLE_STREAM_FASTPATH=1 "${BIN}" "${data_flag}" "${data_file}" -e "${query}" --output json 2>&1)"

  if [[ "${fast_out}" != "${slow_out}" ]]; then
    fail_count=$((fail_count + 1))
    echo "FAIL ${name}: fast-path output differs from slow-path output"
    echo "  --- fast ---"; echo "${fast_out}" | sed 's/^/    /'
    echo "  --- slow ---"; echo "${slow_out}" | sed 's/^/    /'
    return
  fi

  if [[ "${fast_out}" != *"${expect_substr}"* ]]; then
    fail_count=$((fail_count + 1))
    echo "FAIL ${name}: output missing expected [${expect_substr}]"
    echo "${fast_out}" | sed 's/^/    /'
    return
  fi

  pass_count=$((pass_count + 1))
  echo "PASS ${name}"
}

# --- Fixtures -----------------------------------------------------------

DEFAULT_TTL="${WORKDIR}/default.ttl"
cat > "${DEFAULT_TTL}" <<'EOF'
<http://ex/a> <http://ex/p1> <http://ex/x> .
<http://ex/b> <http://ex/p1> <http://ex/y> .
<http://ex/c> <http://ex/p2> <http://ex/z> .
<http://ex/d> <http://ex/p1> <http://ex/w> .
<http://ex/e> <http://ex/p3> <http://ex/v> .
EOF
# 5 triples total; predicate http://ex/p1 occurs 3 times.

EMPTY_TTL="${WORKDIR}/empty.ttl"
: > "${EMPTY_TTL}"

MIXED_NQ="${WORKDIR}/mixed.nq"
cat > "${MIXED_NQ}" <<'EOF'
<http://ex/a> <http://ex/p1> <http://ex/x> .
<http://ex/b> <http://ex/p2> <http://ex/y> .
<http://ex/c> <http://ex/p1> <http://ex/z> <http://ex/g1> .
<http://ex/d> <http://ex/p2> <http://ex/w> <http://ex/g1> .
<http://ex/e> <http://ex/p1> <http://ex/v> <http://ex/g2> .
EOF
# 2 default-graph triples (a, b); 3 named-graph quads across g1 (2), g2 (1).

# --- (a) SELECT (COUNT(*) AS ?n) WHERE { ?s ?p ?o } ----------------------

check_query "(a) COUNT(*) over Turtle default graph" \
  --data "${DEFAULT_TTL}" 'SELECT (COUNT(*) AS ?n) WHERE { ?s ?p ?o }' '"value":"5"'

check_query "(a) COUNT(*) over NQuads default graph only" \
  --data "${MIXED_NQ}" 'SELECT (COUNT(*) AS ?n) WHERE { ?s ?p ?o }' '"value":"2"'

check_query "(a) COUNT(*) over empty graph" \
  --data "${EMPTY_TTL}" 'SELECT (COUNT(*) AS ?n) WHERE { ?s ?p ?o }' '"value":"0"'

# --- (b) SELECT (COUNT(*) AS ?n) WHERE { GRAPH ?g { ?s ?p ?o } } ---------

check_query "(b) COUNT(*) over GRAPH ?g wildcard (all named graphs)" \
  --data "${MIXED_NQ}" 'SELECT (COUNT(*) AS ?n) WHERE { GRAPH ?g { ?s ?p ?o } }' '"value":"3"'

# --- (c) ASK { ?s ?p ?o } ------------------------------------------------

check_query "(c) ASK nonempty graph" \
  --data "${DEFAULT_TTL}" 'ASK { ?s ?p ?o }' '"boolean": true'

check_query "(c) ASK empty graph" \
  --data "${EMPTY_TTL}" 'ASK { ?s ?p ?o }' '"boolean": false'

# --- (d) bound predicate, COUNT and ASK ----------------------------------

check_query "(d) COUNT(*) bound predicate matches" \
  --data "${DEFAULT_TTL}" 'SELECT (COUNT(*) AS ?n) WHERE { ?s <http://ex/p1> ?o }' '"value":"3"'

check_query "(d) COUNT(*) bound predicate no matches" \
  --data "${DEFAULT_TTL}" 'SELECT (COUNT(*) AS ?n) WHERE { ?s <http://ex/nope> ?o }' '"value":"0"'

check_query "(d) ASK bound predicate matches" \
  --data "${DEFAULT_TTL}" 'ASK { ?s <http://ex/p1> ?o }' '"boolean": true'

check_query "(d) ASK bound predicate no matches" \
  --data "${DEFAULT_TTL}" 'ASK { ?s <http://ex/nope> ?o }' '"boolean": false'

# --- Non-streamable shapes: must fall through, not just agree by luck ---

check_query "non-streamable: multi-pattern BGP falls through" \
  --data "${DEFAULT_TTL}" \
  'SELECT (COUNT(*) AS ?n) WHERE { ?s ?p ?o . ?s2 ?p2 ?o2 }' '"value":"25"'

check_query "non-streamable: FILTER-wrapped pattern falls through" \
  --data "${DEFAULT_TTL}" \
  'SELECT (COUNT(*) AS ?n) WHERE { ?s ?p ?o . FILTER(?p = <http://ex/p1>) }' '"value":"3"'

check_query "non-streamable: GROUP BY falls through" \
  --data "${DEFAULT_TTL}" \
  'SELECT ?p (COUNT(*) AS ?n) WHERE { ?s ?p ?o } GROUP BY ?p' '"value":"http://ex/p1"'

echo "============================================================"
echo "streamable_fastpath_regressions: ${pass_count} pass, ${fail_count} fail (out of $((pass_count + fail_count)))"

if [[ "${fail_count}" -eq 0 ]]; then
  exit 0
else
  exit 1
fi
