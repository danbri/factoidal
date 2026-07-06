#!/usr/bin/env bash
# tests/local/service_wrap_stage12.sh
#
# Acceptance test for virtual-sources Part A, Stages 1-2
# (docs/designissues/2026-07-06-virtual-sources-design.md):
# `SERVICE <wrap+http://...>` wrapping a REST resource, triplifying it
# (default Facade-X-equivalent mapping, or an `rml=` override), and
# joining it as an ordinary graph_store — SPARQL.Service.Wrap.fst,
# wired through the SERVICE resolver hook (57_service_client_bind.sh
# extension + ocaml-output/service_wrap_hook.ml + service_wrap_http.ml).
#
# Starts a tiny purpose-built Python HTTP fixture server (full control
# over Content-Type per path — python3 -m http.server's mimetypes
# guessing is not reliable enough for exact-media-type assertions) that
# serves: a JSON doc, a CSV doc, a Turtle doc, and an RML-mapped JSON
# fixture reused verbatim from third_party/testing/rml-modules/rml-core
# (RMLTC0002a-JSON).
#
# All cases use CONSTRUCT (not SELECT/ASK) because `factoidal`'s CLI
# has TWO evaluators for local `--data` queries: SELECT/ASK take a fast
# "backend executor" path by default (SPARQL11.Store.fst,
# `run_select_query_backend_dataset`) whose `GP_Service` arm is
# unconditionally `[] ` (Issue #57 Phase 3 is explicitly NOT done there
# yet — a pre-existing gap this task did not touch); CONSTRUCT always
# goes through `SPARQL11_Algebra.eval_construct_query`, i.e. the
# `eval_pattern`/`eval_pattern_store` path this feature actually hooks
# into (§0.1 of the design doc). Discovered while writing this test —
# verified directly against a standalone harness linking
# service_wrap_http.cmx before concluding the resolver itself was fine
# and the CLI's SELECT fast path was the gap. See the Report for the
# full note; SELECT users should be aware `wrap+` SERVICE results are
# silently dropped unless the query is CONSTRUCT-shaped or --entail is
# set (which also disables the backend-executor fast path).
#
# Cases (labelled PASS/FAIL, rule #25):
#   (a) default-mapping JSON, joined with a local BGP
#   (b) default-mapping CSV, joined with a local BGP
#   (c) Turtle passthrough (no triplification), joined with a local BGP
#   (d) rml= override — byte-equal (sorted N-Quads) to the vendored
#       fixture's own expected output.nq (the same ground truth
#       bin/rml-runner checks RMLTC0002a-JSON against)
#   (e) opt-in flag unset -> clean empty result, no crash
#   (f) non-http wrap+ scheme (wrap+mcp:) -> clean empty result
#   (g) fetch failure (closed port) -> clean empty result, no crash
#
# Per CLAUDE.md rule #17 every external process is bounded; rule #14 no
# `|| true` swallowing a checked exit code; rule #16 no truncating
# tail -N (full log dumped on failure); rule #25 labelled pass/fail
# counts in the summary line.

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
RML_FIXTURE="${ROOT}/third_party/testing/rml-modules/rml-core/test-cases/RMLTC0002a-JSON"
TMPDIR_BASE="${TMPDIR:-/tmp}"
WORKDIR="$(mktemp -d "${TMPDIR_BASE}/factoidal-service-wrap-XXXXXX")"

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

if [[ ! -f "${RML_FIXTURE}/mapping.ttl" ]]; then
  echo "ERROR: ${RML_FIXTURE}/mapping.ttl missing -- run:" >&2
  echo "  git submodule update --init third_party/testing/rml-modules/rml-core" >&2
  exit 2
fi

echo "== service_wrap_stage12 =="
echo "workdir=${WORKDIR}"
echo

# ------------------------------------------------------------------
# Fixtures.
# ------------------------------------------------------------------
cat >"${WORKDIR}/person.json" <<'EOF'
{"name": "Ada", "age": 36}
EOF

cat >"${WORKDIR}/people.csv" <<'EOF'
name,age
Ada,36
Grace,85
EOF

cat >"${WORKDIR}/data.ttl" <<'EOF'
<http://example.org/a> <http://example.org/b> <http://example.org/c> .
EOF

cp "${RML_FIXTURE}/student.json" "${WORKDIR}/student.json"
cp "${RML_FIXTURE}/mapping.ttl" "${WORKDIR}/rml_mapping.ttl"
cp "${RML_FIXTURE}/output.nq" "${WORKDIR}/rml_expected.nq"

# Local BGP fixture every SERVICE-join case reads (§ "joined with local BGP").
cat >"${WORKDIR}/local.ttl" <<'EOF'
@prefix ex: <http://example.org/> .
ex:marker ex:label "local" .
EOF

# ------------------------------------------------------------------
# Tiny fixture HTTP server: exact Content-Type control per path (a
# stdlib python3 -m http.server guesses Content-Type from the file
# extension via `mimetypes`, which is not reliable enough for an
# exact-media-type assertion -- e.g. .ttl has no registered mapping).
# ------------------------------------------------------------------
PORT=$((23000 + (RANDOM % 15000)))
CLOSED_PORT=$((PORT + 1))  # never bound -- used for the fetch-failure case

cat >"${WORKDIR}/fixture_server.py" <<PYEOF
import http.server
import os

WORKDIR = ${WORKDIR@Q}

ROUTES = {
    "/person.json": ("application/json", "person.json"),
    "/people.csv": ("text/csv", "people.csv"),
    "/data.ttl": ("text/turtle", "data.ttl"),
    "/student.json": ("application/json", "student.json"),
}

class Handler(http.server.BaseHTTPRequestHandler):
    def do_GET(self):
        route = ROUTES.get(self.path)
        if route is None:
            self.send_response(404)
            self.end_headers()
            self.wfile.write(b"not found")
            return
        content_type, fname = route
        with open(os.path.join(WORKDIR, fname), "rb") as f:
            body = f.read()
        self.send_response(200)
        self.send_header("Content-Type", content_type)
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def log_message(self, fmt, *args):
        pass

if __name__ == "__main__":
    server = http.server.HTTPServer(("127.0.0.1", ${PORT}), Handler)
    server.serve_forever()
PYEOF

python3 "${WORKDIR}/fixture_server.py" >"${WORKDIR}/server.log" 2>&1 &
SERVER_PID=$!

wait_for_server() {
  local tries=0
  while [[ ${tries} -lt 100 ]]; do
    if curl -s -o /dev/null -m 2 "http://127.0.0.1:${PORT}/data.ttl"; then
      return 0
    fi
    tries=$((tries + 1))
    sleep 0.2
  done
  return 1
}

if wait_for_server; then
  pass "fixture-server-start"
else
  fail "fixture-server-start" "$(cat "${WORKDIR}/server.log")"
  echo "service_wrap_stage12 summary: ${PASS_COUNT} pass, ${FAIL_COUNT} fail (out of $((PASS_COUNT+FAIL_COUNT)))"
  exit 1
fi

# run_construct QUERY OUTFILE [ENV...] -- CONSTRUCT query -> N-Triples
# text in OUTFILE. Sets FACTOIDAL_SERVICE_HTTP=1 and the allowlist by
# default; extra ENV=VALUE args override/extend that.
run_construct() {
  local query="$1" outfile="$2"; shift 2
  timeout 30 env \
    FACTOIDAL_SERVICE_HTTP=1 \
    FACTOIDAL_SERVICE_HTTP_ALLOWED_HOSTS="127.0.0.1" \
    "$@" \
    "${BIN}" --data "${WORKDIR}/local.ttl" -e "${query}" -o ntriples \
    >"${outfile}" 2>"${WORKDIR}/err.txt"
}

# ------------------------------------------------------------------
# (a) JSON default mapping, joined with a local BGP. CONSTRUCT echoes
# the local triple back too, so its presence in the output proves the
# join actually ran (not just the SERVICE side in isolation).
# ------------------------------------------------------------------
Q_JSON="CONSTRUCT { <http://example.org/marker> <http://example.org/label> ?local . ?s ?p ?o } WHERE { <http://example.org/marker> <http://example.org/label> ?local . SERVICE <wrap+http://127.0.0.1:${PORT}/person.json> { ?s ?p ?o } }"
if run_construct "${Q_JSON}" "${WORKDIR}/json_out.nt"; then
  pass "json-default-mapping-exit-0"
else
  fail "json-default-mapping-exit-0" "$(cat "${WORKDIR}/err.txt")"
fi
OUT=$(cat "${WORKDIR}/json_out.nt")
if echo "${OUT}" | grep -q 'http://example.org/label> "local"' \
   && echo "${OUT}" | grep -q 'http://factoidal.example/ns/wrap#name> "Ada"' \
   && echo "${OUT}" | grep -q 'http://factoidal.example/ns/wrap#age> "36"'; then
  pass "json-default-mapping-shape-and-join"
else
  fail "json-default-mapping-shape-and-join" "${OUT}"
fi

# ------------------------------------------------------------------
# (b) CSV default mapping, joined with a local BGP.
# ------------------------------------------------------------------
Q_CSV="CONSTRUCT { <http://example.org/marker> <http://example.org/label> ?local . ?s ?p ?o } WHERE { <http://example.org/marker> <http://example.org/label> ?local . SERVICE <wrap+http://127.0.0.1:${PORT}/people.csv> { ?s ?p ?o } }"
if run_construct "${Q_CSV}" "${WORKDIR}/csv_out.nt"; then
  pass "csv-default-mapping-exit-0"
else
  fail "csv-default-mapping-exit-0" "$(cat "${WORKDIR}/err.txt")"
fi
OUT=$(cat "${WORKDIR}/csv_out.nt")
if echo "${OUT}" | grep -q 'http://example.org/label> "local"' \
   && echo "${OUT}" | grep -q '"Ada"' && echo "${OUT}" | grep -q '"Grace"' \
   && echo "${OUT}" | grep -q '"36"' && echo "${OUT}" | grep -q '"85"'; then
  pass "csv-default-mapping-shape-and-join"
else
  fail "csv-default-mapping-shape-and-join" "${OUT}"
fi

# ------------------------------------------------------------------
# (c) Turtle passthrough (no triplification), joined with a local BGP.
# ------------------------------------------------------------------
Q_TTL="CONSTRUCT { <http://example.org/marker> <http://example.org/label> ?local . ?s ?p ?o } WHERE { <http://example.org/marker> <http://example.org/label> ?local . SERVICE <wrap+http://127.0.0.1:${PORT}/data.ttl> { ?s ?p ?o } }"
if run_construct "${Q_TTL}" "${WORKDIR}/ttl_out.nt"; then
  pass "turtle-passthrough-exit-0"
else
  fail "turtle-passthrough-exit-0" "$(cat "${WORKDIR}/err.txt")"
fi
OUT=$(cat "${WORKDIR}/ttl_out.nt")
if echo "${OUT}" | grep -q 'http://example.org/label> "local"' \
   && echo "${OUT}" | grep -q 'http://example.org/a> <http://example.org/b> <http://example.org/c>'; then
  pass "turtle-passthrough-content"
else
  fail "turtle-passthrough-content" "${OUT}"
fi

# ------------------------------------------------------------------
# (d) rml= override: byte-equal (sorted N-Quads) to the fixture's own
# expected output.nq -- the SAME ground truth bin/rml-runner checks
# RMLTC0002a-JSON against.
# ------------------------------------------------------------------
Q_RML="CONSTRUCT { ?s ?p ?o } WHERE { SERVICE <wrap+http://127.0.0.1:${PORT}/student.json#rml=${WORKDIR}/rml_mapping.ttl> { ?s ?p ?o } }"
if run_construct "${Q_RML}" "${WORKDIR}/rml_got.nt"; then
  pass "rml-override-exit-0"
else
  fail "rml-override-exit-0" "$(cat "${WORKDIR}/err.txt")"
fi

sort_hash() { grep -v '^$' "$1" | LC_ALL=C sort | sha256sum | awk '{print $1}'; }
GOT_HASH=$(sort_hash "${WORKDIR}/rml_got.nt")
EXP_HASH=$(sort_hash "${WORKDIR}/rml_expected.nq")
if [[ "${GOT_HASH}" == "${EXP_HASH}" ]]; then
  pass "rml-override-byte-equal-sorted-nquads"
else
  fail "rml-override-byte-equal-sorted-nquads" \
    "got sha256=${GOT_HASH} expected sha256=${EXP_HASH}" \
    "--- got (od -c tail) ---" "$(tail -c 80 "${WORKDIR}/rml_got.nt" | od -c | tail -5)" \
    "--- expected (od -c tail) ---" "$(tail -c 80 "${WORKDIR}/rml_expected.nq" | od -c | tail -5)"
fi

# ------------------------------------------------------------------
# (e) Opt-out (FACTOIDAL_SERVICE_HTTP unset): unregistered SERVICE
# endpoint per SPARQL semantics -- clean, empty CONSTRUCT result for
# the SERVICE-only triple, exit 0, no crash/hang.
# ------------------------------------------------------------------
Q_OPTOUT="CONSTRUCT { ?s ?p ?o } WHERE { SERVICE <wrap+http://127.0.0.1:${PORT}/person.json> { ?s ?p ?o } }"
if timeout 30 "${BIN}" --data "${WORKDIR}/local.ttl" -e "${Q_OPTOUT}" -o ntriples \
     >"${WORKDIR}/optout.nt" 2>"${WORKDIR}/optout_err.txt"; then
  pass "opt-out-exit-0"
else
  fail "opt-out-exit-0" "$(cat "${WORKDIR}/optout_err.txt")"
fi
if [[ ! -s "${WORKDIR}/optout.nt" ]]; then
  pass "opt-out-empty-result"
else
  fail "opt-out-empty-result" "$(cat "${WORKDIR}/optout.nt")"
fi

# ------------------------------------------------------------------
# (f) Non-http wrap+ scheme (wrap+mcp: -- out of scope this stage):
# resolves to an unregistered endpoint, clean empty result.
# ------------------------------------------------------------------
Q_MCP="CONSTRUCT { ?s ?p ?o } WHERE { SERVICE <wrap+mcp:geocoder/geocode?x=1> { ?s ?p ?o } }"
if run_construct "${Q_MCP}" "${WORKDIR}/mcp_out.nt"; then
  pass "non-http-scheme-exit-0"
else
  fail "non-http-scheme-exit-0" "$(cat "${WORKDIR}/err.txt")"
fi
if [[ ! -s "${WORKDIR}/mcp_out.nt" ]]; then
  pass "non-http-scheme-empty-result"
else
  fail "non-http-scheme-empty-result" "$(cat "${WORKDIR}/mcp_out.nt")"
fi

# ------------------------------------------------------------------
# (g) Fetch failure (closed port): clean empty result, no crash, no
# hang (bounded by the outer `timeout 30`).
# ------------------------------------------------------------------
Q_CLOSED="CONSTRUCT { ?s ?p ?o } WHERE { SERVICE <wrap+http://127.0.0.1:${CLOSED_PORT}/nothing> { ?s ?p ?o } }"
if run_construct "${Q_CLOSED}" "${WORKDIR}/closed_out.nt"; then
  pass "fetch-failure-exit-0"
else
  fail "fetch-failure-exit-0" "$(cat "${WORKDIR}/err.txt")"
fi
if [[ ! -s "${WORKDIR}/closed_out.nt" ]]; then
  pass "fetch-failure-empty-result"
else
  fail "fetch-failure-empty-result" "$(cat "${WORKDIR}/closed_out.nt")"
fi

echo
echo "service_wrap_stage12 summary: ${PASS_COUNT} pass, ${FAIL_COUNT} fail (out of $((PASS_COUNT+FAIL_COUNT)))"
exit "${FAIL}"
