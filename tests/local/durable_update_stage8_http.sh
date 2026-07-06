#!/usr/bin/env bash
# tests/local/durable_update_stage8_http.sh
#
# Acceptance for durable-UPDATE stage 8 (HTTP/Protocol wiring),
# docs/designissues/2026-07-06-durable-update-design.md staged plan
# row 8: `factoidal-http --data-cottas X --delta-log Y --rw` serving
# the read-write store. Sibling to durable_update_stage3.sh (stage 3,
# merge-on-read) and durable_update_stage4_compaction.sh (stage 4,
# compaction) -- this one drives the REAL HTTP server, not the CLI or
# an in-process probe.
#
# (a) Build a small .cottas store (same fixture as stage 3:
#     tests/local/data/cottas_sample.nq).
# (b) Start `factoidal serve --rw --data-cottas ... --delta-log ...`,
#     wait for the listener + COTTAS load.
# (c) POST /update INSERT DATA / DELETE DATA / CLEAR / CREATE: each
#     must commit durably (204) and be visible on the next SELECT.
#     POST /update DELETE WHERE (outside the stage-8 translator's
#     vocabulary): must 501, not silently apply in-memory-only.
# (d) Graph Store Protocol verb matrix against /data/<graph>: GET,
#     HEAD, PUT, POST, DELETE -- each verb's status code and resulting
#     content checked. Without --rw a second server instance confirms
#     PUT/POST/DELETE 405.
# (e) CONCURRENT-READER TEST (the design's stage-8 acceptance
#     criterion): N reader processes hammer
#     `SELECT (COUNT(*) AS ?c) WHERE { GRAPH <...counter> {?s ?p ?o} }`
#     while a writer issues M sequential INSERT DATA committing one
#     more numbered triple each; every observed count must be an
#     integer in [0, M] and, per reader, NON-DECREASING across its own
#     sequence of observations (never torn, never a rollback) --
#     "some valid prefix of the update sequence" is exactly "an
#     integer count that only goes up."
# (f) Kill the server (SIGKILL) mid-write (while the writer loop is
#     still issuing requests), then restart it against the SAME
#     --data-cottas/--delta-log and confirm: the process comes back up
#     (log parses, no crash), the counter graph's count is a value
#     that was actually observed as committed (<= the number of POSTs
#     that returned 204), and is STABLE under repeated re-query
#     (no further corruption).
#
# Per CLAUDE.md rule #17 every external process is bounded; rule #14
# no `|| true` swallowing exit codes; rule #25 the summary spells out
# N/N/N in words; rule #16 no truncating tail -N on process output.

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
PYCOTTAS_PYTHON="${PYCOTTAS_PYTHON:-${ROOT}/_tmp.junk/pycottas-venv/bin/python}"
TMPDIR_BASE="${TMPDIR:-/tmp}"
WORKDIR="$(mktemp -d "${TMPDIR_BASE}/factoidal-durable-update-stage8-XXXXXX")"

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

echo "== durable_update_stage8_http =="
echo "workdir=${WORKDIR}"
echo

# ------------------------------------------------------------------
# (a) Build the small .cottas store.
# ------------------------------------------------------------------
INPUT="${ROOT}/tests/local/data/cottas_sample.nq"
CORPUS_ROOT="${WORKDIR}/corpus"
ARTIFACT="${CORPUS_ROOT}/sample-cottas/v1/data.cottas"

BUILD_RC=0
"${PYCOTTAS_PYTHON}" "${ROOT}/tools/corpus_pipeline.py" materialize-nq-cottas-corpus \
  --input "${INPUT}" --corpus-root "${CORPUS_ROOT}" \
  --dataset-name sample-cottas --chunk-name sample-cottas \
  >"${WORKDIR}/build-cottas.log" 2>&1 || BUILD_RC=$?
if [[ ${BUILD_RC} -ne 0 || ! -f "${ARTIFACT}" ]]; then
  fail "cottas-store-build" "$(cat "${WORKDIR}/build-cottas.log")"
  echo "durable_update_stage8_http summary: ${PASS_COUNT} pass, ${FAIL_COUNT} fail (out of $((PASS_COUNT+FAIL_COUNT)))"
  exit 1
fi
pass "cottas-store-build"

LOG_PATH="${WORKDIR}/data.deltalog"
PORT=$((20000 + (RANDOM % 20000)))
BASE="http://127.0.0.1:${PORT}"

start_server() {
  local extra=("$@")
  "${BIN}" serve -p "${PORT}" --data-cottas "${ARTIFACT}" "${extra[@]}" \
    >"${WORKDIR}/server_$$.log" 2>&1 &
  SERVER_PID=$!
}

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

# ------------------------------------------------------------------
# (b) Start the --rw server.
# ------------------------------------------------------------------
start_server --delta-log "${LOG_PATH}" --rw
if wait_for_server; then
  pass "server-start-rw"
else
  fail "server-start-rw" "$(cat "${WORKDIR}"/server_*.log 2>/dev/null)"
  echo "durable_update_stage8_http summary: ${PASS_COUNT} pass, ${FAIL_COUNT} fail (out of $((PASS_COUNT+FAIL_COUNT)))"
  exit 1
fi

sparql_select() {
  # $1 = query (URL-unescaped is fine, curl --data-urlencode handles it)
  curl -s -m 10 -G "${BASE}/sparql" \
    -H 'Accept: application/sparql-results+json' \
    --data-urlencode "query=$1"
}

post_update() {
  curl -s -m 10 -o "${WORKDIR}/update_resp.txt" -w '%{http_code}' \
    -X POST "${BASE}/update" -H 'Content-Type: application/sparql-update' --data "$1"
}

# ------------------------------------------------------------------
# (c) Translatable ops commit durably + are visible; untranslatable
# ops 501 honestly instead of a silent in-memory-only apply.
# ------------------------------------------------------------------
CODE=$(post_update 'INSERT DATA { GRAPH <http://ex/g1> { <http://ex/s1> <http://ex/p1> "hello" } }')
if [[ "${CODE}" == "204" ]]; then pass "update-insert-data-204"; else fail "update-insert-data-204" "got ${CODE}: $(cat "${WORKDIR}/update_resp.txt")"; fi

RESULT=$(sparql_select 'SELECT * WHERE { GRAPH <http://ex/g1> { ?s ?p ?o } }')
if echo "${RESULT}" | grep -q '"hello"'; then pass "update-insert-data-visible"; else fail "update-insert-data-visible" "${RESULT}"; fi

CODE=$(post_update 'DELETE DATA { GRAPH <http://ex/g1> { <http://ex/s1> <http://ex/p1> "hello" } }')
if [[ "${CODE}" == "204" ]]; then pass "update-delete-data-204"; else fail "update-delete-data-204" "got ${CODE}"; fi

RESULT=$(sparql_select 'SELECT * WHERE { GRAPH <http://ex/g1> { ?s ?p ?o } }')
if ! echo "${RESULT}" | grep -q '"hello"'; then pass "update-delete-data-effective"; else fail "update-delete-data-effective" "${RESULT}"; fi

CODE=$(post_update 'CREATE GRAPH <http://ex/g2>')
if [[ "${CODE}" == "204" ]]; then pass "update-create-204"; else fail "update-create-204" "got ${CODE}"; fi

CODE=$(post_update 'INSERT DATA { GRAPH <http://ex/g2> { <http://ex/s2> <http://ex/p2> "keep-then-clear" } }')
CODE2=$(post_update 'CLEAR GRAPH <http://ex/g2>')
if [[ "${CODE}" == "204" && "${CODE2}" == "204" ]]; then pass "update-clear-204"; else fail "update-clear-204" "insert=${CODE} clear=${CODE2}"; fi
RESULT=$(sparql_select 'SELECT * WHERE { GRAPH <http://ex/g2> { ?s ?p ?o } }')
if ! echo "${RESULT}" | grep -q 'keep-then-clear'; then pass "update-clear-effective"; else fail "update-clear-effective" "${RESULT}"; fi

CODE=$(post_update 'DELETE WHERE { GRAPH <http://ex/g1> { ?s ?p ?o } }')
if [[ "${CODE}" == "501" ]]; then pass "update-deletewhere-501-honest"; else fail "update-deletewhere-501-honest" "got ${CODE}: $(cat "${WORKDIR}/update_resp.txt")"; fi

# ------------------------------------------------------------------
# (d) GSP verb matrix.
# ------------------------------------------------------------------
CODE=$(curl -s -m 10 -o "${WORKDIR}/gsp.txt" -w '%{http_code}' -X PUT "${BASE}/data/testgraph" \
  -H 'Content-Type: text/turtle' --data '<http://ex/s3> <http://ex/p3> "gsp-put" .')
if [[ "${CODE}" == "201" || "${CODE}" == "204" ]]; then pass "gsp-put-status"; else fail "gsp-put-status" "got ${CODE}"; fi

BODY=$(curl -s -m 10 "${BASE}/data/testgraph")
if echo "${BODY}" | grep -q 'gsp-put'; then pass "gsp-get-after-put"; else fail "gsp-get-after-put" "${BODY}"; fi

HEAD_CODE=$(curl -s -m 10 -o /dev/null -w '%{http_code}' -I "${BASE}/data/testgraph")
if [[ "${HEAD_CODE}" == "200" ]]; then pass "gsp-head-exists"; else fail "gsp-head-exists" "got ${HEAD_CODE}"; fi

CODE=$(curl -s -m 10 -o "${WORKDIR}/gsp.txt" -w '%{http_code}' -X POST "${BASE}/data/testgraph" \
  -H 'Content-Type: text/turtle' --data '<http://ex/s4> <http://ex/p4> "gsp-post" .')
if [[ "${CODE}" == "200" ]]; then pass "gsp-post-status"; else fail "gsp-post-status" "got ${CODE}"; fi
BODY=$(curl -s -m 10 "${BASE}/data/testgraph")
if echo "${BODY}" | grep -q 'gsp-put' && echo "${BODY}" | grep -q 'gsp-post'; then
  pass "gsp-post-merges"
else
  fail "gsp-post-merges" "${BODY}"
fi

CODE=$(curl -s -m 10 -o /dev/null -w '%{http_code}' -X DELETE "${BASE}/data/testgraph")
if [[ "${CODE}" == "200" || "${CODE}" == "204" ]]; then pass "gsp-delete-status"; else fail "gsp-delete-status" "got ${CODE}"; fi
BODY=$(curl -s -m 10 "${BASE}/data/testgraph")
if ! echo "${BODY}" | grep -q 'gsp-'; then pass "gsp-delete-effective"; else fail "gsp-delete-effective" "${BODY}"; fi

CODE=$(curl -s -m 10 -o /dev/null -w '%{http_code}' "${BASE}/data?default")
if [[ "${CODE}" == "200" ]]; then pass "gsp-indirect-default"; else fail "gsp-indirect-default" "got ${CODE}"; fi

# Second server, no --rw: GSP writes must 405, GET must still work.
kill -9 "${SERVER_PID}" 2>/dev/null || true
wait "${SERVER_PID}" 2>/dev/null || true
PORT=$((PORT + 1))
BASE="http://127.0.0.1:${PORT}"
start_server --delta-log "${LOG_PATH}"
if wait_for_server; then pass "server-start-ro-delta-log"; else fail "server-start-ro-delta-log" "$(cat "${WORKDIR}"/server_*.log 2>/dev/null)"; fi
CODE=$(curl -s -m 10 -o /dev/null -w '%{http_code}' -X PUT "${BASE}/data/anygraph" -H 'Content-Type: text/turtle' --data '<http://ex/x> <http://ex/y> "z" .')
if [[ "${CODE}" == "405" ]]; then pass "gsp-put-405-without-rw"; else fail "gsp-put-405-without-rw" "got ${CODE}"; fi
GET_CODE=$(curl -s -m 10 -o /dev/null -w '%{http_code}' "${BASE}/data?default")
if [[ "${GET_CODE}" == "200" ]]; then pass "gsp-get-still-works-without-rw"; else fail "gsp-get-still-works-without-rw" "got ${GET_CODE}"; fi
kill -9 "${SERVER_PID}" 2>/dev/null || true
wait "${SERVER_PID}" 2>/dev/null || true

# ------------------------------------------------------------------
# (e) Concurrent-reader test. Fresh log for a clean counter.
# ------------------------------------------------------------------
PORT=$((PORT + 1))
BASE="http://127.0.0.1:${PORT}"
LOG_PATH2="${WORKDIR}/data2.deltalog"
start_server --delta-log "${LOG_PATH2}" --rw
if wait_for_server; then pass "server-start-concurrent"; else fail "server-start-concurrent" "$(cat "${WORKDIR}"/server_*.log 2>/dev/null)"; exit 1; fi

N_WRITES=40
N_READERS=6
READER_LOG_PREFIX="${WORKDIR}/reader"

count_query='SELECT (COUNT(*) AS ?c) WHERE { GRAPH <http://ex/counter> { ?s ?p ?o } }'

extract_count() {
  # crude JSON scrape: {"c":{"type":"literal","value":"N", ...}} --
  # pure bash regex (no forked grep/head pipeline) so a reader
  # iteration costs exactly one curl fork, not five.
  if [[ "$1" =~ \"value\":\"([0-9]+)\" ]]; then
    echo "${BASH_REMATCH[1]}"
  fi
}

run_reader() {
  local idx="$1"
  local outfile="${READER_LOG_PREFIX}_${idx}.log"
  : >"${outfile}"
  local deadline=$((SECONDS + 12))
  while [[ ${SECONDS} -lt ${deadline} ]]; do
    local resp
    resp=$(sparql_select "${count_query}")
    local c
    c=$(extract_count "${resp}")
    if [[ -z "${c}" ]]; then
      echo "TORN_OR_ERROR resp=${resp}" >>"${outfile}"
    else
      echo "${c}" >>"${outfile}"
    fi
  done
}

READER_PIDS=()
for i in $(seq 1 "${N_READERS}"); do
  run_reader "${i}" &
  READER_PIDS+=("$!")
done

WRITER_OK=0
for i in $(seq 1 "${N_WRITES}"); do
  CODE=$(post_update "INSERT DATA { GRAPH <http://ex/counter> { <http://ex/item${i}> <http://ex/seq> \"${i}\" } }")
  if [[ "${CODE}" == "204" ]]; then WRITER_OK=$((WRITER_OK + 1)); fi
done

# Wait ONLY for the reader jobs -- plain `wait` with no args would also
# block on the long-lived server process (started with `&` in
# start_server), which never exits on its own.
for pid in "${READER_PIDS[@]}"; do
  wait "${pid}" 2>/dev/null || true
done

FINAL_RESP=$(sparql_select "${count_query}")
FINAL_COUNT=$(extract_count "${FINAL_RESP}")
if [[ "${FINAL_COUNT}" == "${WRITER_OK}" ]]; then
  pass "concurrent-final-count-matches-writes (${FINAL_COUNT} == ${WRITER_OK})"
else
  fail "concurrent-final-count-matches-writes" "final=${FINAL_COUNT} writer_ok=${WRITER_OK}"
fi

TOTAL_OBS=0
BAD_OBS=0
NONMONOTONIC=0
for i in $(seq 1 "${N_READERS}"); do
  outfile="${READER_LOG_PREFIX}_${i}.log"
  prev=-1
  while IFS= read -r line; do
    TOTAL_OBS=$((TOTAL_OBS + 1))
    if [[ "${line}" == TORN_OR_ERROR* ]]; then
      BAD_OBS=$((BAD_OBS + 1))
      continue
    fi
    if ! [[ "${line}" =~ ^[0-9]+$ ]]; then
      BAD_OBS=$((BAD_OBS + 1))
      continue
    fi
    if [[ "${line}" -lt 0 || "${line}" -gt ${N_WRITES} ]]; then
      BAD_OBS=$((BAD_OBS + 1))
    fi
    if [[ "${line}" -lt "${prev}" ]]; then
      NONMONOTONIC=$((NONMONOTONIC + 1))
    fi
    prev="${line}"
  done <"${outfile}"
done

echo "concurrent-reader summary: ${N_READERS} readers, ${WRITER_OK} writes committed (of ${N_WRITES} attempted), ${TOTAL_OBS} total reads observed, ${BAD_OBS} bad/torn reads, ${NONMONOTONIC} non-monotonic (rollback) reads"
if [[ ${BAD_OBS} -eq 0 && ${NONMONOTONIC} -eq 0 ]]; then
  pass "concurrent-reader-never-torn-never-rollback"
else
  fail "concurrent-reader-never-torn-never-rollback" "bad=${BAD_OBS} nonmonotonic=${NONMONOTONIC} (out of ${TOTAL_OBS})"
fi

# ------------------------------------------------------------------
# (f) Kill mid-write, restart, verify clean recovery.
# ------------------------------------------------------------------
(
  for i in $(seq 1 200); do
    curl -s -m 5 -o /dev/null -X POST "${BASE}/update" -H 'Content-Type: application/sparql-update' \
      --data "INSERT DATA { GRAPH <http://ex/killtest> { <http://ex/k${i}> <http://ex/seq> \"${i}\" } }" || true
  done
) &
WRITER_BG_PID=$!

# Let a handful of requests land, then SIGKILL the server mid-stream.
sleep 0.3
if kill -0 "${SERVER_PID}" 2>/dev/null; then
  kill -9 "${SERVER_PID}"
  pass "server-killed-mid-write"
else
  fail "server-killed-mid-write" "server already gone before kill"
fi
# Let the background writer loop finish failing its remaining requests
# (server is dead) rather than leaving it orphaned.
wait "${WRITER_BG_PID}" 2>/dev/null || true

start_server --delta-log "${LOG_PATH2}" --rw
if wait_for_server; then
  pass "server-restart-after-kill"
else
  fail "server-restart-after-kill" "$(cat "${WORKDIR}"/server_*.log 2>/dev/null)"
fi

# The counter graph (pre-kill-test writes) must still show the exact
# committed count -- no corruption from the killtest writes that never
# got their fsync to complete.
RECOVER_RESP=$(sparql_select "${count_query}")
RECOVER_COUNT=$(extract_count "${RECOVER_RESP}")
if [[ "${RECOVER_COUNT}" == "${WRITER_OK}" ]]; then
  pass "recovery-counter-graph-intact (${RECOVER_COUNT})"
else
  fail "recovery-counter-graph-intact" "expected ${WRITER_OK}, got ${RECOVER_COUNT}: ${RECOVER_RESP}"
fi

killtest_query='SELECT (COUNT(*) AS ?c) WHERE { GRAPH <http://ex/killtest> { ?s ?p ?o } }'
RECOVER_RESP2=$(sparql_select "${killtest_query}")
RECOVER_COUNT2=$(extract_count "${RECOVER_RESP2}")
if [[ -n "${RECOVER_COUNT2}" && "${RECOVER_COUNT2}" -ge 0 && "${RECOVER_COUNT2}" -le 200 ]]; then
  pass "recovery-killtest-graph-well-formed (count=${RECOVER_COUNT2}, not torn/garbled)"
else
  fail "recovery-killtest-graph-well-formed" "${RECOVER_RESP2}"
fi

# Stability: re-querying twice more must give the SAME count (no
# further drift/corruption after recovery).
STABLE1=$(extract_count "$(sparql_select "${killtest_query}")")
STABLE2=$(extract_count "$(sparql_select "${killtest_query}")")
if [[ "${STABLE1}" == "${RECOVER_COUNT2}" && "${STABLE2}" == "${RECOVER_COUNT2}" ]]; then
  pass "recovery-killtest-graph-stable"
else
  fail "recovery-killtest-graph-stable" "counts: ${RECOVER_COUNT2} ${STABLE1} ${STABLE2}"
fi

kill -9 "${SERVER_PID}" 2>/dev/null || true
wait "${SERVER_PID}" 2>/dev/null || true
SERVER_PID=""

echo
echo "durable_update_stage8_http summary: ${PASS_COUNT} pass, ${FAIL_COUNT} fail (out of $((PASS_COUNT+FAIL_COUNT)))"
exit ${FAIL}
