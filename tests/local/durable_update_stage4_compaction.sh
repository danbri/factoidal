#!/usr/bin/env bash
# tests/local/durable_update_stage4_compaction.sh
#
# Acceptance for durable-UPDATE stage 4 (compaction), sibling to
# tests/local/durable_update_stage3.sh (stage 3, merge-on-read).
# docs/designissues/2026-07-06-durable-update-design.md stage table row
# 4: fold the delta log into a fresh .cottas base via the EXISTING
# corpus_pipeline.py import pipeline, then atomically swap it in
# (bin/factoidal-cli/factoidal_cli.ml's `factoidal compact`, its own
# banner has the full swap-protocol writeup: chunk_dir/current -> vN
# symlink flip, since a compacted base is a SET of files a single
# atomic_rename cannot swap as one step).
#
# (a) Build a small .cottas store (same fixture as stage 3:
#     tests/local/data/cottas_sample.nq) via tools/corpus_pipeline.py.
# (b) Append one delta batch at epoch 0 (probe.ml's scenario-write,
#     unchanged from stage 3's own scenario).
# (c) Query pre-compaction (v1/data.cottas --delta-log LOG) -- record
#     the merged-view tuple.
# (d) Run `factoidal compact --data-cottas v1/data.cottas --delta-log
#     LOG`; parse compacted_through_epoch from its output.
# (e) Re-query the NEW base (chunk_dir/current/data.cottas), with and
#     without --delta-log LOG (now truncated) -- must match (c) exactly.
# (f) Append a SECOND, distinct batch (probe.ml's scenario2-write,
#     "Dave") at epoch = compacted_through_epoch + 1 onto the
#     (truncated) log; re-query current + --delta-log LOG -- must show
#     the compacted content AND Dave together ("layering continues").
# (g) Kill-mid-compaction loop (>=25 iterations): a fresh copy of
#     {v1, one-batch log} per iteration, `factoidal compact` under
#     `setsid`, SIGKILL the whole process group at a random delay.
#     After each kill: `current` must be either absent (pre-compaction
#     state intact: v1 + the ORIGINAL log) or present and fully valid
#     (post-compaction state: current + the SAME log, epoch-filtered to
#     nothing extra) -- the tuple observed must be EXACTLY the
#     pre-compaction tuple or EXACTLY the post-compaction tuple, never
#     a third state, and the store must always open (no query failure).
#
# Per CLAUDE.md rule #17 every external process is bounded; rule #14 no
# `|| true` swallowing exit codes; rule #25 the summary spells out
# N/N/N in words.

set -uo pipefail

# CLAUDE.md rule #12.
if ! command -v ocamlfind >/dev/null 2>&1; then
  OPAM_ENV_RC=0
  eval "$(opam env --switch=fstar 2>/dev/null)" || OPAM_ENV_RC=$?
  if [[ ${OPAM_ENV_RC} -ne 0 ]]; then
    echo "WARNING: 'opam env --switch=fstar' exited ${OPAM_ENV_RC}; proceeding, ocamlfind check below will fail loudly if the switch isn't active." >&2
  fi
fi

ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
OCAML_OUT="${ROOT}/formal/fstar/ocaml-output"
BIN="${OCAML_OUT}/factoidal"
PROBE_ML="${ROOT}/bin/delta-log-probe/probe.ml"
PYCOTTAS_PYTHON="${PYCOTTAS_PYTHON:-${ROOT}/_tmp.junk/pycottas-venv/bin/python}"
TMPDIR_BASE="${TMPDIR:-/tmp}"
WORKDIR="$(mktemp -d "${TMPDIR_BASE}/factoidal-durable-update-stage4-XXXXXX")"
trap 'rm -rf "${WORKDIR}"' EXIT

FAIL=0
PASS_COUNT=0
FAIL_COUNT=0

pass() { PASS_COUNT=$((PASS_COUNT + 1)); echo "PASS $1"; }
fail() { FAIL_COUNT=$((FAIL_COUNT + 1)); FAIL=1; echo "FAIL $1"; shift; [[ $# -gt 0 ]] && printf '  %s\n' "$@"; }

if [[ ! -x "${BIN}" ]]; then
  echo "ERROR: ${BIN} not found -- run 'cd formal/fstar && ./build-ocaml.sh extract compile' first." >&2
  exit 2
fi

echo "== durable_update_stage4_compaction =="
echo "workdir=${WORKDIR}"
echo

# ------------------------------------------------------------------
# (a) Build the small .cottas store, exactly stage 3's recipe.
# ------------------------------------------------------------------
INPUT="${ROOT}/tests/local/data/cottas_sample.nq"
CORPUS_ROOT="${WORKDIR}/corpus"
CHUNK_DIR="${CORPUS_ROOT}/sample-cottas"
ARTIFACT="${CHUNK_DIR}/v1/data.cottas"
LOG_PATH="${WORKDIR}/data.deltalog"

BUILD_RC=0
"${PYCOTTAS_PYTHON}" "${ROOT}/tools/corpus_pipeline.py" materialize-nq-cottas-corpus \
  --input "${INPUT}" --corpus-root "${CORPUS_ROOT}" \
  --dataset-name sample-cottas --chunk-name sample-cottas \
  >"${WORKDIR}/build-cottas.log" 2>&1 || BUILD_RC=$?
if [[ ${BUILD_RC} -ne 0 || ! -f "${ARTIFACT}" ]]; then
  fail "cottas-store-build" "$(cat "${WORKDIR}/build-cottas.log")"
  echo "FATAL: cannot proceed without a base store." >&2
  echo "durable_update_stage4_compaction summary: ${PASS_COUNT} pass, ${FAIL_COUNT} fail (out of $((PASS_COUNT+FAIL_COUNT)))"
  exit 1
fi
pass "cottas-store-build"

# ------------------------------------------------------------------
# (b) Build the probe driver (same COMMON_MODULES prefix as stage 3 --
# probe.ml's stage-4 additions (scenario_batch epoch param,
# scenario2-write) live in the SAME already-listed modules, no new
# .cmx needed).
# ------------------------------------------------------------------
COMMON_MODULES=(
  Util_Log RDF_Format RDF_Vocabulary RDF_Term RDF_Triple RDF_Indexed RDF_Graph
  RDF_Vocabulary_Axioms RDFS_Closure OWL_Closure RDF_Graph_Executable RDF_List_Helpers
  RDF_Bytes RDF_Store_Loader Parquet_Footer OWL_Vocabulary Tableau Parser_FastString
  RDF_IRI RDF_NQuads_Serialize Parser_IRI Parser_Combinators Parser_TurtleScanner
  Parser_NTriples HDT_Container HDT_Dictionary HDT_Triples Parser_Turtle Parser_NQuads
  Parser_TriG Parser_XML Parser_XPath XPath_Eval XML_Wellformedness XML_Namespaces
  Parser_RDFXML Parser_SRX Parser_CSVResults Parser_JSONResults Parser_JSON
  SPARQL11_IRI_Resolve SPARQL_JSON_Escape JSONLD_Loader JSONLD_Context JSONLD_Expand
  Parser_JSONLD SPARQL_Eval_TimeBudget SPARQL_Eval_Limits SPARQL_HTTP_Response
  SPARQL_HTTP_Timing SPARQL_HTTP_BackendInfo SPARQL_HTTP_QueriesIndex
  SPARQL_HTTP_StaticFiles SPARQL_HTTP_Admin SPARQL_HTTP_Routes Parser_Ballyhoo
  Parser_BallyhooBloom Parser_BallyhooHDT Parser_BallyhooHDTQ Parser_BallyhooCOTTAS
  RDF_CottasStore_ColumnSeq RDF_CottasStore_PageCache RDF_CottasStore_OnDiskIndex
  RDF_CottasStore_DictWriter RDF_CottasStore_PresenceBitmap RDF_CottasStore_PresenceWriter
  RDF_CottasStore_CompoundPresenceBitmap RDF_CottasStore_CompoundPresenceWriter
  RDF_CottasStore_OffsetsWriter RDF_CottasStore_LazyDict RDF_CottasStore_LazyDictRegistry
  RDF_Store_LazyTermCache RDF_Store_HDTTermCacheRegistry RDF_Store_Columnar_OffsetIndex
  RDF_Store_Columnar_DeltaLog SPARQL_Plan_Pruning SPARQL_Plan_Estimate SPARQL_Plan_Loader
  SPARQL_Plan_AccessPath RDF_CottasStore RDF_CottasStore_OnDiskRuntime RDF_CottasInMem
  fstar_pure_hashes RDF_Canonical RDF_Canonical_Manifest SPARQL11_Algebra XSD_Datatypes
  RDF_Pretty OWL_QueryRewrite OWL_QueryEval OWL_Tests_Manifest RIF_Core_Syntax
  Parser_RIFXML RIF_Core_Builtins RIF_Core_Translation RIF_Core_Eval RIF_Core_Tests
  RIF_Core_Conformance SPARQL11_Parser SHACL_Validation VC_Credential CSVW_Metadata
  CSVW_URITemplate CSVW_Conversion RDF_Store_Columnar_DeltaMerge
)
CMX_LIST=()
for m in "${COMMON_MODULES[@]}"; do CMX_LIST+=("${OCAML_OUT}/${m}.cmx"); done

ZSTD_LIB_FLAGS=()
for dir in /opt/homebrew/lib /opt/homebrew/opt/zstd/lib \
           /usr/local/lib /usr/lib /usr/lib/x86_64-linux-gnu \
           /usr/lib/aarch64-linux-gnu; do
  if [[ -f "${dir}/libzstd.a" || -f "${dir}/libzstd.so" || -f "${dir}/libzstd.dylib" ]]; then
    ZSTD_LIB_FLAGS=(-cclib "-L${dir}" -cclib -lzstd)
    break
  fi
done

PROBE_BIN="${WORKDIR}/probe"
BUILD_RC=0
BUILD_OUT=$(ocamlfind ocamlopt \
  -package fstar.lib,str,zarith,sha,digestif.c,unix,uucp \
  -linkpkg -w -8-14-26 \
  -I "${OCAML_OUT}" \
  "${CMX_LIST[@]}" \
  "${OCAML_OUT}/parquet_zstd_stubs.o" \
  "${ZSTD_LIB_FLAGS[@]}" \
  "${PROBE_ML}" \
  -o "${PROBE_BIN}" 2>&1) || BUILD_RC=$?
if [[ ${BUILD_RC} -ne 0 ]]; then
  fail "probe-driver-build" "${BUILD_OUT}"
  echo "durable_update_stage4_compaction summary: ${PASS_COUNT} pass, ${FAIL_COUNT} fail (out of $((PASS_COUNT+FAIL_COUNT)))"
  exit 1
fi
pass "probe-driver-build"

# ------------------------------------------------------------------
# (c) Append the stage-3 scenario batch at epoch 0; query pre-compaction.
# ------------------------------------------------------------------
timeout 30 "${PROBE_BIN}" scenario-write "${LOG_PATH}" 0 >"${WORKDIR}/scenario-write.log" 2>&1
WRITE_RC=$?
if [[ ${WRITE_RC} -ne 0 ]] || ! grep -q '^SCENARIO_WRITE_OK' "${WORKDIR}/scenario-write.log"; then
  fail "scenario-write" "$(cat "${WORKDIR}/scenario-write.log")"
else
  pass "scenario-write"
fi

Q_CAROL_ADDED='ASK { <https://example.org/carol> <https://example.org/name> "Carol" }'
Q_ANCHOR_REMOVED='ASK { <https://example.org/default-subject> <https://example.org/status> "default" }'
Q_EVENTS_ADD='ASK { GRAPH <https://example.org/graph/events> { <https://example.org/carol> <https://example.org/attends> <https://example.org/event-x> } }'
Q_DOCS_EMPTY='ASK { GRAPH <https://example.org/graph/docs> { ?s ?p ?o } }'
Q_PEOPLE_INTACT='ASK { GRAPH <https://example.org/graph/people> { <https://example.org/alice> <https://example.org/name> "Alice" } }'
Q_DAVE_ADDED='ASK { <https://example.org/dave> <https://example.org/name> "Dave" }'

ask_query() {
  # ask_query DATA_COTTAS QUERY [LOG_PATH]
  local data="$1" q="$2" log="${3:-}"
  if [[ -n "${log}" ]]; then
    timeout 30 "${BIN}" --data-cottas "${data}" --delta-log "${log}" -e "${q}" 2>/dev/null
  else
    timeout 30 "${BIN}" --data-cottas "${data}" -e "${q}" 2>/dev/null
  fi
}

check_ask() {
  # check_ask LABEL DATA_COTTAS QUERY EXPECTED [LOG_PATH]
  local label="$1" data="$2" q="$3" expected="$4" log="${5:-}"
  local got
  got="$(ask_query "${data}" "${q}" "${log}")"
  if [[ "${got}" == "${expected}" ]]; then
    pass "${label}"
  else
    fail "${label}" "expected=${expected} got=${got}"
  fi
}

echo "-- (c) pre-compaction merged view (v1 + --delta-log) --"
check_ask "pre/carol-added"      "${ARTIFACT}" "${Q_CAROL_ADDED}"    "true"  "${LOG_PATH}"
check_ask "pre/anchor-removed"   "${ARTIFACT}" "${Q_ANCHOR_REMOVED}" "false" "${LOG_PATH}"
check_ask "pre/events-graph-add" "${ARTIFACT}" "${Q_EVENTS_ADD}"     "true"  "${LOG_PATH}"
check_ask "pre/docs-cleared"     "${ARTIFACT}" "${Q_DOCS_EMPTY}"     "false" "${LOG_PATH}"
check_ask "pre/people-intact"    "${ARTIFACT}" "${Q_PEOPLE_INTACT}"  "true"  "${LOG_PATH}"

# ------------------------------------------------------------------
# (d) Compact.
# ------------------------------------------------------------------
echo
echo "-- (d) factoidal compact --"
COMPACT_RC=0
COMPACT_OUT=$(timeout 120 "${BIN}" compact --data-cottas "${ARTIFACT}" --delta-log "${LOG_PATH}" \
  --python "${PYCOTTAS_PYTHON}" 2>&1) || COMPACT_RC=$?
echo "${COMPACT_OUT}" >"${WORKDIR}/compact.log"
if [[ ${COMPACT_RC} -ne 0 ]]; then
  fail "compact-invocation" "${COMPACT_OUT}"
  echo "durable_update_stage4_compaction summary: ${PASS_COUNT} pass, ${FAIL_COUNT} fail (out of $((PASS_COUNT+FAIL_COUNT)))"
  exit 1
fi
pass "compact-invocation"

COMPACTED_EPOCH="$(sed -n 's/.*compacted_through_epoch=\([0-9][0-9]*\).*/\1/p' "${WORKDIR}/compact.log" | tail -1)"
if [[ -z "${COMPACTED_EPOCH}" ]]; then
  fail "compact-reports-epoch" "no compacted_through_epoch= line in: ${COMPACT_OUT}"
  COMPACTED_EPOCH=0
else
  pass "compact-reports-epoch (epoch=${COMPACTED_EPOCH})"
fi

CURRENT_ARTIFACT="${CHUNK_DIR}/current/data.cottas"
if [[ -e "${CURRENT_ARTIFACT}" ]]; then
  pass "compact-current-symlink-live"
else
  fail "compact-current-symlink-live" "missing: ${CURRENT_ARTIFACT}"
fi

# The import pipeline's --build-sidecars must have run against the new
# base (design doc section 4.3: compaction re-runs the eager-sidecar
# import, unchanged): all four .dict + .presence pairs, the Lamed3
# offsets index, the compound (p,o) bitmap (corpus_pipeline.py's
# COTTAS_SIDECAR_SUFFIXES), plus stage 4's own data.compacted-epoch.
SIDECAR_MISSING=""
for suffix in .s.dict .s.presence .p.dict .p.presence .o.dict .o.presence \
              .g.dict .g.presence .p.offsets .po.presence; do
  if [[ ! -f "${CURRENT_ARTIFACT}${suffix}" ]]; then
    SIDECAR_MISSING="${SIDECAR_MISSING} ${suffix}"
  fi
done
if [[ ! -f "${CHUNK_DIR}/current/data.compacted-epoch" ]]; then
  SIDECAR_MISSING="${SIDECAR_MISSING} data.compacted-epoch"
fi
if [[ -z "${SIDECAR_MISSING}" ]]; then
  pass "compact-sidecars-eager-built"
else
  fail "compact-sidecars-eager-built" "missing:${SIDECAR_MISSING}"
fi

# ------------------------------------------------------------------
# (e) Re-query the new base -- must match (c) exactly, with or without
# --delta-log (the log is now truncated to just its header).
# ------------------------------------------------------------------
echo
echo "-- (e) post-compaction: new base alone, and new base + (truncated) log --"
check_ask "post/carol-added-no-log"      "${CURRENT_ARTIFACT}" "${Q_CAROL_ADDED}"    "true"
check_ask "post/anchor-removed-no-log"   "${CURRENT_ARTIFACT}" "${Q_ANCHOR_REMOVED}" "false"
check_ask "post/events-graph-add-no-log" "${CURRENT_ARTIFACT}" "${Q_EVENTS_ADD}"     "true"
check_ask "post/docs-cleared-no-log"     "${CURRENT_ARTIFACT}" "${Q_DOCS_EMPTY}"     "false"
check_ask "post/people-intact-no-log"    "${CURRENT_ARTIFACT}" "${Q_PEOPLE_INTACT}"  "true"

check_ask "post/carol-added-with-log"      "${CURRENT_ARTIFACT}" "${Q_CAROL_ADDED}"    "true"  "${LOG_PATH}"
check_ask "post/anchor-removed-with-log"   "${CURRENT_ARTIFACT}" "${Q_ANCHOR_REMOVED}" "false" "${LOG_PATH}"
check_ask "post/events-graph-add-with-log" "${CURRENT_ARTIFACT}" "${Q_EVENTS_ADD}"     "true"  "${LOG_PATH}"
check_ask "post/docs-cleared-with-log"     "${CURRENT_ARTIFACT}" "${Q_DOCS_EMPTY}"     "false" "${LOG_PATH}"
check_ask "post/people-intact-with-log"    "${CURRENT_ARTIFACT}" "${Q_PEOPLE_INTACT}"  "true"  "${LOG_PATH}"

# ------------------------------------------------------------------
# (f) Layering continues: append a second, distinct batch at
# epoch = compacted_through_epoch + 1 onto the (truncated) log.
# ------------------------------------------------------------------
echo
echo "-- (f) post-compaction append -- layering continues --"
NEXT_EPOCH=$((COMPACTED_EPOCH + 1))
timeout 30 "${PROBE_BIN}" scenario2-write "${LOG_PATH}" "${NEXT_EPOCH}" \
  >"${WORKDIR}/scenario2-write.log" 2>&1
S2_RC=$?
if [[ ${S2_RC} -ne 0 ]] || ! grep -q '^SCENARIO2_WRITE_OK' "${WORKDIR}/scenario2-write.log"; then
  fail "scenario2-write" "$(cat "${WORKDIR}/scenario2-write.log")"
else
  pass "scenario2-write (epoch=${NEXT_EPOCH})"
fi

check_ask "layered/dave-added"       "${CURRENT_ARTIFACT}" "${Q_DAVE_ADDED}"     "true"  "${LOG_PATH}"
check_ask "layered/carol-still-there" "${CURRENT_ARTIFACT}" "${Q_CAROL_ADDED}"   "true"  "${LOG_PATH}"
check_ask "layered/people-still-intact" "${CURRENT_ARTIFACT}" "${Q_PEOPLE_INTACT}" "true" "${LOG_PATH}"
# Without --delta-log the new fact must NOT be visible (it lives only
# in the delta layer, not yet compacted) -- confirms this is a real
# overlay, not an accidental re-compaction.
check_ask "layered/dave-absent-without-log" "${CURRENT_ARTIFACT}" "${Q_DAVE_ADDED}" "false"

# ------------------------------------------------------------------
# (g) Kill-mid-compaction loop.
# ------------------------------------------------------------------
echo
echo "-- (g) kill-mid-compaction harness --"
MASTER_SEED="${DURABLE_STAGE4_HARNESS_SEED:-20260706}"
KILL_ITERATIONS="${DURABLE_STAGE4_HARNESS_ITERS:-25}"
RANDOM="${MASTER_SEED}"

CRASH_CLEAN=0
CRASH_TORN=0
CRASH_UNEXPECTED=0
SEEN_PRE=0
SEEN_POST=0

pre_tuple="true|false|true|false|true"    # carol|anchor(removed=false means present? see below)|events|docs|people
post_tuple="true|false|true|false|true"

# NOTE: the pre- and post-compaction tuples for THIS scenario are
# identical by construction (compaction must not change the answer --
# that is the whole point being tested). What distinguishes "clean
# pre-state" from "clean post-state" here is not the query tuple (both
# give the same five answers) but WHICH PATH answered them without
# error: v1 + the original (untruncated) log, or current + the
# possibly-truncated log. Both are captured below; a torn state is
# either a tuple that disagrees with this fixture's only valid answer,
# or a query that fails/hangs/returns empty.
EXPECTED_TUPLE="true|false|true|false|true"

for ((iter = 1; iter <= KILL_ITERATIONS; iter++)); do
  ITER_DIR="${WORKDIR}/kill_iter_${iter}"
  rm -rf "${ITER_DIR}"
  mkdir -p "${ITER_DIR}"
  cp -r "${CORPUS_ROOT}" "${ITER_DIR}/corpus"
  # Fresh log per iteration (the original CORPUS_ROOT's chunk may
  # already have a `current` symlink from step (d) above -- remove it
  # so each iteration starts from a clean pre-compaction v1-only state).
  rm -f "${ITER_DIR}/corpus/sample-cottas/current"
  ITER_LOG="${ITER_DIR}/data.deltalog"
  timeout 10 "${PROBE_BIN}" scenario-write "${ITER_LOG}" 0 >/dev/null 2>&1
  ITER_ARTIFACT="${ITER_DIR}/corpus/sample-cottas/v1/data.cottas"
  ITER_CURRENT="${ITER_DIR}/corpus/sample-cottas/current/data.cottas"

  setsid "${BIN}" compact --data-cottas "${ITER_ARTIFACT}" --delta-log "${ITER_LOG}" \
    --python "${PYCOTTAS_PYTHON}" \
    >"${ITER_DIR}/compact.log" 2>&1 &
  COMPACT_PID=$!
  ( sleep 15; kill -9 -- "-${COMPACT_PID}" 2>/dev/null ) &
  WATCHDOG_PID=$!

  # A full compact on this fixture measures ~0.7-3s wall (python import
  # warmup dominates; the corpus_pipeline subprocess itself is fast at
  # 5-triple scale). 5ms-2s therefore straddles the base-rename +
  # log-truncate window; the both-states-observed check below fails
  # loudly if the distribution ever drifts to one side.
  DELAY_MS=$(( 5 + (RANDOM % 2000) ))
  DELAY_S=$(awk -v ms="${DELAY_MS}" 'BEGIN{printf "%.3f", ms/1000}')
  sleep "${DELAY_S}"

  # Kill the WHOLE process group (factoidal compact + the corpus_
  # pipeline.py / duckdb / --explain sidecar-build children it may have
  # spawned) -- a real crash of the parent orphans its children the
  # same way; killing the group instead of just the parent keeps this
  # loop's timing tight and avoids leftover python processes racing the
  # NEXT iteration's setup.
  kill -9 -- "-${COMPACT_PID}" 2>/dev/null
  wait "${COMPACT_PID}" 2>/dev/null
  kill "${WATCHDOG_PID}" 2>/dev/null
  wait "${WATCHDOG_PID}" 2>/dev/null

  if [[ -e "${ITER_CURRENT}" ]]; then
    STATE="post"
    a="$(timeout 10 "${BIN}" --data-cottas "${ITER_CURRENT}" --delta-log "${ITER_LOG}" -e "${Q_CAROL_ADDED}" 2>/dev/null)"
    b="$(timeout 10 "${BIN}" --data-cottas "${ITER_CURRENT}" --delta-log "${ITER_LOG}" -e "${Q_ANCHOR_REMOVED}" 2>/dev/null)"
    c="$(timeout 10 "${BIN}" --data-cottas "${ITER_CURRENT}" --delta-log "${ITER_LOG}" -e "${Q_EVENTS_ADD}" 2>/dev/null)"
    d="$(timeout 10 "${BIN}" --data-cottas "${ITER_CURRENT}" --delta-log "${ITER_LOG}" -e "${Q_DOCS_EMPTY}" 2>/dev/null)"
    e="$(timeout 10 "${BIN}" --data-cottas "${ITER_CURRENT}" --delta-log "${ITER_LOG}" -e "${Q_PEOPLE_INTACT}" 2>/dev/null)"
  else
    STATE="pre"
    a="$(timeout 10 "${BIN}" --data-cottas "${ITER_ARTIFACT}" --delta-log "${ITER_LOG}" -e "${Q_CAROL_ADDED}" 2>/dev/null)"
    b="$(timeout 10 "${BIN}" --data-cottas "${ITER_ARTIFACT}" --delta-log "${ITER_LOG}" -e "${Q_ANCHOR_REMOVED}" 2>/dev/null)"
    c="$(timeout 10 "${BIN}" --data-cottas "${ITER_ARTIFACT}" --delta-log "${ITER_LOG}" -e "${Q_EVENTS_ADD}" 2>/dev/null)"
    d="$(timeout 10 "${BIN}" --data-cottas "${ITER_ARTIFACT}" --delta-log "${ITER_LOG}" -e "${Q_DOCS_EMPTY}" 2>/dev/null)"
    e="$(timeout 10 "${BIN}" --data-cottas "${ITER_ARTIFACT}" --delta-log "${ITER_LOG}" -e "${Q_PEOPLE_INTACT}" 2>/dev/null)"
  fi
  tuple="${a}|${b}|${c}|${d}|${e}"

  if [[ "${STATE}" == "pre" ]]; then SEEN_PRE=$((SEEN_PRE + 1)); else SEEN_POST=$((SEEN_POST + 1)); fi
  if [[ "${tuple}" == "${EXPECTED_TUPLE}" ]]; then
    CRASH_CLEAN=$((CRASH_CLEAN + 1))
  elif [[ -z "${a}" || -z "${b}" || -z "${c}" || -z "${d}" || -z "${e}" ]]; then
    echo "  iter ${iter}: query itself failed (state=${STATE} delay=${DELAY_MS}ms) tuple=${tuple}"
    CRASH_UNEXPECTED=$((CRASH_UNEXPECTED + 1))
  else
    echo "  iter ${iter}: TORN STATE (state=${STATE} delay=${DELAY_MS}ms) tuple=${tuple} (expected=${EXPECTED_TUPLE})"
    CRASH_TORN=$((CRASH_TORN + 1))
  fi
  rm -rf "${ITER_DIR}"
done

echo "kill-mid-compaction: ${CRASH_CLEAN} clean recoveries, ${CRASH_TORN} torn states, ${CRASH_UNEXPECTED} unexpected failures (out of ${KILL_ITERATIONS} iterations); observed states: ${SEEN_PRE} pre-compaction, ${SEEN_POST} post-compaction"
# Coverage check: the loop is only meaningful if BOTH sides of the swap
# were actually observed at least once -- all-pre means every kill
# landed before the rename (delays too short), all-post means every
# kill landed after (delays too long); either way the swap moment
# itself went untested.
if [[ ${SEEN_PRE} -gt 0 && ${SEEN_POST} -gt 0 ]]; then
  pass "kill-mid-compaction-both-states-observed"
else
  fail "kill-mid-compaction-both-states-observed" "pre=${SEEN_PRE} post=${SEEN_POST} -- tune DURABLE_STAGE4_HARNESS delays"
fi
if [[ ${CRASH_TORN} -gt 0 || ${CRASH_UNEXPECTED} -gt 0 ]]; then
  fail "kill-mid-compaction-never-torn"
else
  pass "kill-mid-compaction-never-torn"
fi

echo
echo "============================================================"
echo "durable_update_stage4_compaction summary: ${PASS_COUNT} pass, ${FAIL_COUNT} fail (out of $((PASS_COUNT+FAIL_COUNT)))"

exit "${FAIL}"
