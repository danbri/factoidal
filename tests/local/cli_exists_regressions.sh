#!/usr/bin/env bash
# tests/local/cli_exists_regressions.sh — regression pin for issue #343:
# FILTER EXISTS / NOT EXISTS returned ZERO rows on the backend query
# path (the path `factoidal query`, the npm bundle and the HTTP server
# all use), while the W3C runner — which evaluates through the pure
# eval_select_query path — scored the same queries green. 631 of 631
# W3C SPARQL hid a total EXISTS failure on every user-facing entry.
#
# This script exists so the two evaluation paths can never again
# diverge on EXISTS without a test going red: it runs the W3C suite's
# own exists01 fixture and the original bug report's shape THROUGH THE
# CLI BINARY, not through the runner.
#
# Rule anchors: #14 (no swallowed exit codes), #16 (no truncation),
# #25 (labelled pass/fail counts in words).

set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"

# Same committed-binary resolution the other local scripts use: the
# ocaml-output symlink points at the current platform's bin/ directory.
BIN="${ROOT}/formal/fstar/ocaml-output/factoidal"
if [ ! -x "${BIN}" ]; then
  BIN="${ROOT}/bin/linux-x86_64/factoidal"
fi
if [ ! -x "${BIN}" ]; then
  echo "cli_exists_regressions: no factoidal binary found" >&2
  exit 2
fi

W3C_EXISTS="${ROOT}/third_party/testing/w3c/sparql/sparql11/exists"
TMPDIR="${TMPDIR:-/tmp}"
WORKDIR="$(mktemp -d "${TMPDIR}/factoidal-cli-exists-XXXXXX")"
trap 'rm -rf "${WORKDIR}"' EXIT

PASS=0
FAIL=0

# check NAME EXPECTED_COUNT MUST_CONTAIN MUST_NOT_CONTAIN -- <cli args…>
# Runs the CLI, counts result rows via the "N result(s)" trailer, and
# greps for required / forbidden values. Every failure prints the full
# output (rule #16).
check() {
  local name="$1" expect_n="$2" must="$3" must_not="$4"
  shift 4
  local out rc=0
  out="$("${BIN}" "$@" 2>&1)" || rc=$?
  local ok=1
  if [ "${rc}" -ne 0 ]; then ok=0; fi
  local got_n
  got_n="$(printf '%s\n' "${out}" | sed -n 's/^\([0-9][0-9]*\) result(s)$/\1/p' | tail -1)"
  if [ -z "${got_n}" ]; then got_n=0; fi
  if [ "${got_n}" != "${expect_n}" ]; then ok=0; fi
  if [ -n "${must}" ] && ! printf '%s' "${out}" | grep -q -- "${must}"; then ok=0; fi
  if [ -n "${must_not}" ] && printf '%s' "${out}" | grep -q -- "${must_not}"; then ok=0; fi
  if [ "${ok}" -eq 1 ]; then
    echo "PASS ${name} (${got_n} rows)"
    PASS=$((PASS+1))
  else
    echo "FAIL ${name}: rc=${rc}, rows=${got_n} (expected ${expect_n})"
    echo "----- full output -----"
    printf '%s\n' "${out}"
    echo "-----------------------"
    FAIL=$((FAIL+1))
  fi
}

# 1. The W3C suite's own exists01, through the CLI. Expected: the three
#    :s triples (only :s has some ?p ex:o edge).
check "w3c-exists01-via-cli" 3 "http://www.example.org/s" "" \
  query --data "${W3C_EXISTS}/exists01.ttl" --query "${W3C_EXISTS}/exists01.rq"

# 2. The original bug report's shape: blank-node subjects, correlated
#    EXISTS. Alice knows someone; Bob does not.
cat > "${WORKDIR}/knows.ttl" <<'EOF'
@prefix foaf: <http://xmlns.com/foaf/0.1/> .
_:a foaf:name "Alice" ; foaf:knows _:b .
_:b foaf:name "Bob" .
EOF

check "bnode-filter-exists" 1 "Alice" "Bob" \
  query --data "${WORKDIR}/knows.ttl" \
  -e 'PREFIX foaf: <http://xmlns.com/foaf/0.1/> SELECT ?name WHERE { ?p foaf:name ?name FILTER EXISTS { ?p foaf:knows ?q } }'

check "bnode-filter-not-exists" 1 "Bob" "Alice" \
  query --data "${WORKDIR}/knows.ttl" \
  -e 'PREFIX foaf: <http://xmlns.com/foaf/0.1/> SELECT ?name WHERE { ?p foaf:name ?name FILTER NOT EXISTS { ?p foaf:knows ?q } }'

# 3. EXISTS nested under NOT (exercises substitute_existentials'
#    recursion, not just the top-level constructor).
check "negated-exists-via-not" 1 "Bob" "Alice" \
  query --data "${WORKDIR}/knows.ttl" \
  -e 'PREFIX foaf: <http://xmlns.com/foaf/0.1/> SELECT ?name WHERE { ?p foaf:name ?name FILTER ( ! EXISTS { ?p foaf:knows ?q } ) }'

# 4. EXISTS inside OPTIONAL's filter (the GP_LeftJoin arm, fixed in the
#    same change). Alice's row keeps the friend binding; Bob's row
#    survives with no binding.
check "exists-in-optional-filter" 2 "Alice" "" \
  query --data "${WORKDIR}/knows.ttl" \
  -e 'PREFIX foaf: <http://xmlns.com/foaf/0.1/> SELECT ?name ?fname WHERE { ?p foaf:name ?name OPTIONAL { ?p foaf:knows ?f . ?f foaf:name ?fname FILTER EXISTS { ?f foaf:name ?anyname } } }'

echo
echo "cli_exists_regressions: ${PASS} pass, ${FAIL} fail (out of $((PASS+FAIL)))"
if [ "${FAIL}" -ne 0 ]; then exit 1; fi
exit 0
