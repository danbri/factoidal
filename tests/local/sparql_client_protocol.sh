#!/usr/bin/env bash
# tests/local/sparql_client_protocol.sh
#
# End-to-end acceptance for the SPARQL 1.1 Protocol HTTP CLIENT (the
# "do sparql client NOW" landing): formal/fstar/SPARQL.Protocol.Client.fst
# (request construction + response dispatch, layered on the existing
# formal/fstar/SPARQL.HTTP.Client.fst HTTP/1.1 framing) plus the
# `factoidal query --endpoint URL` CLI subcommand in
# bin/factoidal-cli/factoidal_cli.ml.
#
# Starts our OWN factoidal-http server (bin/<platform>/factoidal serve)
# against a small fixture dataset, then exercises the client:
#   (a) SELECT via GET, JSON response
#   (b) SELECT via POST (direct), XML response forced via --accept
#   (c) ASK (default POST dispatch)
#   (d) CONSTRUCT via POST, Turtle response -> N-Triples printer
#   (e) error case: malformed query -> server 400 -> client reports it
#       cleanly (nonzero exit, no crash/hang)
# then kills the server.
#
# Per CLAUDE.md rule #17 every external process is bounded (curl -m,
# background server capped by a poll-with-timeout wait); rule #14 no
# `|| true` swallowing exit codes where the exit code is actually
# checked; rule #25 the summary spells out pass/fail in words; rule #16
# no truncating tail -N on process output (server log is `cat`-dumped
# in full on failure).

set -uo pipefail

if ! command -v ocamlfind >/dev/null 2>&1; then
  OPAM_ENV_RC=0
  eval "$(opam env --switch=fstar 2>/dev/null)" || OPAM_ENV_RC=$?
  if [[ ${OPAM_ENV_RC} -ne 0 ]]; then
    echo "WARNING: 'opam env --switch=fstar' exited ${OPAM_ENV_RC}; proceeding, the binary check below will fail loudly if the switch isn't active." >&2
  fi
fi

ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
OCAML_OUT="${ROOT}/formal/fstar/ocaml-output"
BIN="${OCAML_OUT}/factoidal"
TMPDIR_BASE="${TMPDIR:-/tmp}"
WORKDIR="$(mktemp -d "${TMPDIR_BASE}/factoidal-sparql-client-protocol-XXXXXX")"

SERVER_PID=""
cleanup() {
  if [[ -n "${SERVER_PID}" ]] && kill -0 "${SERVER_PID}" 2>/dev/null; then
    kill -9 "${SERVER_PID}" 2>/dev/null || true
  fi
  rm -rf "${WORKDIR}"
}
trap cleanup EXIT

FAIL=0
PASS_COUNT=0
FAIL_COUNT=0
pass() { PASS_COUNT=$((PASS_COUNT + 1)); echo "PASS $1"; }
fail() { FAIL_COUNT=$((FAIL_COUNT + 1)); FAIL=1; echo "FAIL $1"; shift; [[ $# -gt 0 ]] && printf '  %s\n' "$@"; }

if [[ ! -x "${BIN}" ]]; then
  echo "ERROR: ${BIN} not found -- run 'cd formal/fstar && ./build-ocaml.sh extract compile' first." >&2
  exit 2
fi

echo "== sparql_client_protocol =="
echo "workdir=${WORKDIR}"
echo

# ------------------------------------------------------------------
# Fixture dataset: a handful of triples covering SELECT/ASK/CONSTRUCT.
# ------------------------------------------------------------------
FIXTURE="${WORKDIR}/fixture.ttl"
cat >"${FIXTURE}" <<'EOF'
@prefix ex: <http://example.org/> .
ex:alice ex:name "Alice" .
ex:alice ex:knows ex:bob .
ex:bob ex:name "Bob" .
EOF

PORT=$((21000 + (RANDOM % 20000)))
BASE="http://127.0.0.1:${PORT}"

"${BIN}" serve -p "${PORT}" --dataset "${FIXTURE}" \
  >"${WORKDIR}/server.log" 2>&1 &
SERVER_PID=$!

wait_for_server() {
  local tries=0
  while [[ ${tries} -lt 100 ]]; do
    if curl -s -o /dev/null -m 2 "${BASE}/backend-info.json"; then
      return 0
    fi
    tries=$((tries + 1))
    sleep 0.2
  done
  return 1
}

if wait_for_server; then
  pass "server-start"
else
  fail "server-start" "$(cat "${WORKDIR}/server.log")"
  echo "sparql_client_protocol summary: ${PASS_COUNT} pass, ${FAIL_COUNT} fail (out of $((PASS_COUNT+FAIL_COUNT)))"
  exit 1
fi

run_client() {
  # Runs `factoidal query --endpoint ... "$@"`, capturing stdout,
  # stderr, and exit code into fixed files (WORKDIR/client_out.txt,
  # client_err.txt) plus a returned exit code via $?.
  timeout 30 "${BIN}" query --endpoint "${BASE}/sparql" "$@" \
    >"${WORKDIR}/client_out.txt" 2>"${WORKDIR}/client_err.txt"
}

# ------------------------------------------------------------------
# (a) SELECT via GET, JSON.
# ------------------------------------------------------------------
if run_client -e 'SELECT ?name WHERE { ?s <http://example.org/name> ?name }' --via get -o json; then
  pass "select-get-json-exit-0"
else
  fail "select-get-json-exit-0" "$(cat "${WORKDIR}/client_err.txt")"
fi
OUT=$(cat "${WORKDIR}/client_out.txt")
if echo "${OUT}" | grep -q '"Alice"' && echo "${OUT}" | grep -q '"Bob"'; then
  pass "select-get-json-content"
else
  fail "select-get-json-content" "${OUT}"
fi

# ------------------------------------------------------------------
# (b) SELECT via POST (direct), XML forced via --accept.
# ------------------------------------------------------------------
if run_client -e 'SELECT ?name WHERE { ?s <http://example.org/name> ?name }' \
     --via post --accept 'application/sparql-results+xml' -o table; then
  pass "select-post-xml-exit-0"
else
  fail "select-post-xml-exit-0" "$(cat "${WORKDIR}/client_err.txt")"
fi
OUT=$(cat "${WORKDIR}/client_out.txt")
if echo "${OUT}" | grep -q 'Alice' && echo "${OUT}" | grep -q 'Bob'; then
  pass "select-post-xml-content"
else
  fail "select-post-xml-content" "${OUT}"
fi

# ------------------------------------------------------------------
# (c) ASK (default dispatch: direct POST).
# ------------------------------------------------------------------
if run_client -e 'ASK { <http://example.org/alice> <http://example.org/knows> <http://example.org/bob> }' -o json; then
  pass "ask-true-exit-0"
else
  fail "ask-true-exit-0" "$(cat "${WORKDIR}/client_err.txt")"
fi
OUT=$(cat "${WORKDIR}/client_out.txt")
if echo "${OUT}" | grep -q '"boolean": true'; then
  pass "ask-true-content"
else
  fail "ask-true-content" "${OUT}"
fi

if run_client -e 'ASK { <http://example.org/bob> <http://example.org/knows> <http://example.org/alice> }' -o json; then
  pass "ask-false-exit-0"
else
  fail "ask-false-exit-0" "$(cat "${WORKDIR}/client_err.txt")"
fi
OUT=$(cat "${WORKDIR}/client_out.txt")
if echo "${OUT}" | grep -q '"boolean": false'; then
  pass "ask-false-content"
else
  fail "ask-false-content" "${OUT}"
fi

# ------------------------------------------------------------------
# (d) CONSTRUCT via POST. Exercises the client's Accept-header
# selection for CONSTRUCT/DESCRIBE (text/turtle preferred) and its
# Content-Type-driven response dispatch.
#
# NOTE: bin/factoidal-http/factoidal_http.ml's own banner documents a
# pre-existing, pre-this-change Stage-1 limitation: "CONSTRUCT/
# DESCRIBE responses are stubbed -- the F* evaluator's
# eval_select_query returns [] for QF_Construct today." Verified by
# direct curl probe during this test's development: our server
# answers a CONSTRUCT query with `{"head":{"vars":[]},"results":
# {"bindings":[]}}` and Content-Type application/sparql-results+json
# REGARDLESS of the client's Accept header. That is a server-side
# gap, not a client bug -- the client's job here is to (a) send an
# Accept header that prefers text/turtle for CONSTRUCT (it does; see
# SPARQL.Protocol.Client.accept_header_for_kind) and (b) dispatch
# whatever Content-Type actually comes back without crashing (it
# does: an empty-bindings JSON response is valid SPARQL_Protocol_Client
# CLR_Bindings, which -o ntriples/table renders as "(no results)").
# When the server's CONSTRUCT stub is retired, this assertion should
# be tightened to check real Turtle/N-Triples graph content (the
# client's Parser.Turtle/Parser.NTriples dispatch path in
# SPARQL.Protocol.Client.fst's dispatch_body is already exercised by
# that module's own compile-time smoke tests independent of this
# server-side gap).
# ------------------------------------------------------------------
if run_client -e 'CONSTRUCT { ?s <http://example.org/name> ?name } WHERE { ?s <http://example.org/name> ?name }' \
     -o ntriples; then
  pass "construct-post-exit-0"
else
  fail "construct-post-exit-0" "$(cat "${WORKDIR}/client_err.txt")"
fi
OUT=$(cat "${WORKDIR}/client_out.txt")
if [[ "${OUT}" == "(no results)" ]]; then
  pass "construct-post-no-crash-on-server-stub (documented Stage-1 gap: CONSTRUCT unevaluated server-side)"
else
  fail "construct-post-no-crash-on-server-stub" "expected the server's known empty-CONSTRUCT-bindings stub, got: ${OUT}"
fi

# ------------------------------------------------------------------
# (e) Error case: malformed query -> server 400 -> client reports it
# cleanly (nonzero exit, error text on stderr, no crash/hang -- the
# `timeout 30` above is the crash/hang guard).
# ------------------------------------------------------------------
if run_client -e 'SELECT ?x WHERE { this is not sparql' -o table; then
  fail "malformed-query-nonzero-exit" "client exited 0 on a malformed query"
else
  RC=$?
  if [[ ${RC} -ge 1 && ${RC} -lt 124 ]]; then
    pass "malformed-query-nonzero-exit (rc=${RC})"
  else
    fail "malformed-query-nonzero-exit" "unexpected rc=${RC} (124 would mean the client hung)"
  fi
fi
ERR=$(cat "${WORKDIR}/client_err.txt")
if echo "${ERR}" | grep -q 'HTTP 400'; then
  pass "malformed-query-reports-http-400"
else
  fail "malformed-query-reports-http-400" "${ERR}"
fi

# ------------------------------------------------------------------
# Kill the server.
# ------------------------------------------------------------------
kill -9 "${SERVER_PID}" 2>/dev/null || true
wait "${SERVER_PID}" 2>/dev/null || true
SERVER_PID=""
pass "server-killed"

echo
echo "sparql_client_protocol summary: ${PASS_COUNT} pass, ${FAIL_COUNT} fail (out of $((PASS_COUNT+FAIL_COUNT)))"
exit ${FAIL}
