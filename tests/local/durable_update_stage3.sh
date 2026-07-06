#!/usr/bin/env bash
# tests/local/durable_update_stage3.sh
#
# End-to-end acceptance for durable-UPDATE stage 3 (merge-on-read),
# docs/designissues/2026-07-06-durable-update-design.md staged plan
# row 3, wired through the D-overlay
# (docs/designissues/2026-07-06-unified-store-architecture.md §3.3).
#
# (a) Builds a small .cottas store from tests/local/data/cottas_sample.nq
#     (the SAME fixture tests/unit/store_capabilities_unit.ml already
#     hardcodes) via tools/corpus_pipeline.py, same recipe as
#     tests/local/cottas_row_order_regressions.sh.
# (b) Appends one delta batch via the stage-2 probe driver
#     (bin/delta-log-probe/probe.ml's new `scenario-write` mode):
#     an ADD + a tombstoning REMOVE on the default graph, a
#     CREATE+ADD into a brand-new named graph, and a CLEAR wiping an
#     existing named graph -- the four op shapes this stage's brief
#     names.
# (c) Queries the store through the CLI's `--delta-log PATH` flag
#     (factoidal_cli.ml -> SPARQL11_Store.cottas_with_delta_dataset_
#     backend -> the GB_CottasOnDiskDelta arm -> RDF.Store.
#     Capabilities.Delta.overlay) and asserts every result matches
#     the SAME ops applied to the in-memory reference
#     (RDF_Store_Columnar_DeltaMerge.apply_entries_ref, the function
#     that module's own proved lemma
#     `lemma_merge_on_read_matches_apply_entries` ties the delta-log/
#     merge-on-read path to -- see that module's own residual note for
#     the honest scope: entry-level, not full SPARQL Update AST).
# (d) Kills the append mid-write (reusing delta_log_crash_harness.sh's
#     slicing pattern) then re-queries: the recovered prefix's results
#     must be EITHER exactly the pre-update state OR exactly the
#     post-update state, never a mix ("no torn writes").
#
# Per CLAUDE.md rule #17 every external process is bounded; rule #14
# no `|| true` swallowing exit codes; rule #25 the summary spells out
# N/N/N in words.

set -uo pipefail

# CLAUDE.md rule #12: activate the F* opam switch before any F*-adjacent
# work (this script compiles OCaml against fstar.lib-extracted .cmx
# files via ocamlfind, which lives in the switch's PATH).
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
WORKDIR="$(mktemp -d "${TMPDIR_BASE}/factoidal-durable-update-stage3-XXXXXX")"
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
if [[ ! -d "${OCAML_OUT}" ]]; then
  echo "ERROR: ${OCAML_OUT} missing." >&2
  exit 2
fi

echo "== durable_update_stage3 =="
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
  echo "FATAL: cannot proceed without a base store." >&2
  echo "durable_update_stage3 summary: ${PASS_COUNT} pass, ${FAIL_COUNT} fail (out of $((PASS_COUNT+FAIL_COUNT)))"
  exit 1
fi
pass "cottas-store-build"

# ------------------------------------------------------------------
# (b) Build the stage-2 probe driver (bin/delta-log-probe/probe.ml),
# extended with this stage's `scenario-write`/`scenario-write-sliced`/
# `scenario-expect` modes. Same ordered .cmx prefix as tests/unit/
# run-all.sh's COMMON_MODULES up through RDF_Store_Columnar_
# DeltaMerge (probe.ml needs DM.apply_entries_ref, which needs
# SPARQL11_Algebra -- more than the crash harness's own minimal
# DeltaLog-only prefix).
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
  fstar_pure_hashes RDF_Canonical RDF_Canonical_Manifest SPARQL_FullText SPARQL11_Algebra XSD_Datatypes
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
  echo "durable_update_stage3 summary: ${PASS_COUNT} pass, ${FAIL_COUNT} fail (out of $((PASS_COUNT+FAIL_COUNT)))"
  exit 1
fi
pass "probe-driver-build"

# ------------------------------------------------------------------
# (c) Write the scenario batch, then query through the CLI with
# --delta-log and compare against the probe's own reference
# (apply_entries_ref over the hardcoded fixture graphs).
# ------------------------------------------------------------------
LOG_PATH="${WORKDIR}/data.deltalog"
timeout 30 "${PROBE_BIN}" scenario-write "${LOG_PATH}" >"${WORKDIR}/scenario-write.log" 2>&1
WRITE_RC=$?
if [[ ${WRITE_RC} -ne 0 ]] || ! grep -q '^SCENARIO_WRITE_OK' "${WORKDIR}/scenario-write.log"; then
  fail "scenario-write" "$(cat "${WORKDIR}/scenario-write.log")"
else
  pass "scenario-write"
fi

ask_query() {
  # ask_query LABEL QUERY [--delta] -> prints true/false (stderr
  # dropped -- the CLI's qof3/bet7 debug traces go there).
  local q="$1"; local use_delta="${2:-}"
  if [[ "${use_delta}" == "--delta" ]]; then
    timeout 30 "${BIN}" --data-cottas "${ARTIFACT}" --delta-log "${LOG_PATH}" -e "${q}" 2>/dev/null
  else
    timeout 30 "${BIN}" --data-cottas "${ARTIFACT}" -e "${q}" 2>/dev/null
  fi
}

Q_CAROL_ADDED='ASK { <https://example.org/carol> <https://example.org/name> "Carol" }'
Q_ANCHOR_REMOVED='ASK { <https://example.org/default-subject> <https://example.org/status> "default" }'
Q_EVENTS_ADD='ASK { GRAPH <https://example.org/graph/events> { <https://example.org/carol> <https://example.org/attends> <https://example.org/event-x> } }'
Q_DOCS_EMPTY='ASK { GRAPH <https://example.org/graph/docs> { ?s ?p ?o } }'
Q_PEOPLE_INTACT='ASK { GRAPH <https://example.org/graph/people> { <https://example.org/alice> <https://example.org/name> "Alice" } }'

check_ask() {
  # check_ask LABEL QUERY EXPECTED USE_DELTA
  local label="$1" q="$2" expected="$3" use_delta="$4"
  local got
  got="$(ask_query "${q}" "${use_delta}")"
  if [[ "${got}" == "${expected}" ]]; then
    pass "${label}"
  else
    fail "${label}" "expected=${expected} got=${got}"
  fi
}

echo "-- pre-update control (no --delta-log; must match the base fixture) --"
check_ask "control/carol-absent"   "${Q_CAROL_ADDED}"    "false" ""
check_ask "control/anchor-present" "${Q_ANCHOR_REMOVED}"  "true"  ""
check_ask "control/docs-nonempty"  "${Q_DOCS_EMPTY}"      "true"  ""

echo "-- post-update via --delta-log (the read-write moment) --"
check_ask "delta/carol-added"      "${Q_CAROL_ADDED}"     "true"  "--delta"
check_ask "delta/anchor-removed"   "${Q_ANCHOR_REMOVED}"  "false" "--delta"
check_ask "delta/events-graph-add" "${Q_EVENTS_ADD}"      "true"  "--delta"
check_ask "delta/docs-cleared"     "${Q_DOCS_EMPTY}"      "false" "--delta"
check_ask "delta/people-intact"    "${Q_PEOPLE_INTACT}"   "true"  "--delta"

# Cross-check against the probe's own in-memory reference
# (apply_entries_ref) -- the SAME F* function this stage's
# correctness lemma (RDF.Store.Columnar.DeltaMerge.fst's
# lemma_merge_on_read_matches_apply_entries) ties merge-on-read to.
EXPECT_DEFAULT="$(timeout 10 "${PROBE_BIN}" scenario-expect default 2>/dev/null | sort)"
EXPECT_EVENTS="$(timeout 10 "${PROBE_BIN}" scenario-expect events 2>/dev/null | sort)"
EXPECT_DOCS="$(timeout 10 "${PROBE_BIN}" scenario-expect docs 2>/dev/null | sort)"
if [[ "${EXPECT_DEFAULT}" == "<https://example.org/carol> <https://example.org/name> \"Carol\"" ]]; then
  pass "reference/apply_entries_ref-default-matches-hand-derivation"
else
  fail "reference/apply_entries_ref-default-matches-hand-derivation" "got: ${EXPECT_DEFAULT}"
fi
if [[ -z "${EXPECT_DOCS}" ]]; then
  pass "reference/apply_entries_ref-docs-empty"
else
  fail "reference/apply_entries_ref-docs-empty" "got: ${EXPECT_DOCS}"
fi
if [[ "${EXPECT_EVENTS}" == "<https://example.org/carol> <https://example.org/attends> <https://example.org/event-x>" ]]; then
  pass "reference/apply_entries_ref-events-matches-hand-derivation"
else
  fail "reference/apply_entries_ref-events-matches-hand-derivation" "got: ${EXPECT_EVENTS}"
fi

# ------------------------------------------------------------------
# (d) Kill-mid-append harness: the SAME scenario batch, sliced across
# small appends (bin/delta-log-probe/probe.ml's scenario-write-sliced,
# reusing append_one_batch's chunking), SIGKILLed at a random delay.
# Re-querying afterward must show EITHER the full pre-update set of
# answers OR the full post-update set -- never a mix.
# ------------------------------------------------------------------
echo
echo "-- kill-mid-append harness --"
MASTER_SEED="${DURABLE_STAGE3_HARNESS_SEED:-20260706}"
KILL_ITERATIONS="${DURABLE_STAGE3_HARNESS_ITERS:-25}"
RANDOM="${MASTER_SEED}"

CRASH_CLEAN=0
CRASH_TORN=0
CRASH_UNEXPECTED=0

pre_tuple="false|true|true"      # carol-absent|anchor-present|docs-nonempty
post_tuple="true|false|false"

for ((iter = 1; iter <= KILL_ITERATIONS; iter++)); do
  ITER_LOG="${WORKDIR}/crash_${iter}.deltalog"
  # NOT wrapped in `timeout` here: `timeout CMD & PID=$!; kill -9 $PID`
  # kills the `timeout` WRAPPER process, not its child -- SIGKILL can't
  # be trapped/relayed, so the wrapped probe process would be orphaned
  # and keep writing after we believe it dead (confirmed directly: a
  # 30ms kill against a `timeout`-wrapped run still produced a
  # complete, untorn 576-byte log). Background the probe binary
  # directly so `${APPEND_PID}` is ITS pid, and rely on a disowned
  # watchdog subshell for the rule-#17 wall-clock cap instead.
  "${PROBE_BIN}" scenario-write-sliced "${ITER_LOG}" 6 \
    >"${WORKDIR}/crash_append_${iter}.log" 2>&1 &
  APPEND_PID=$!
  ( sleep 10; kill -9 "${APPEND_PID}" 2>/dev/null ) &
  WATCHDOG_PID=$!

  DELAY_MS=$(( 2 + (RANDOM % 60) ))
  DELAY_S=$(awk -v ms="${DELAY_MS}" 'BEGIN{printf "%.3f", ms/1000}')
  sleep "${DELAY_S}"

  if kill -0 "${APPEND_PID}" 2>/dev/null; then
    kill -9 "${APPEND_PID}" 2>/dev/null
  fi
  wait "${APPEND_PID}" 2>/dev/null
  kill "${WATCHDOG_PID}" 2>/dev/null
  wait "${WATCHDOG_PID}" 2>/dev/null

  a="$(timeout 10 "${BIN}" --data-cottas "${ARTIFACT}" --delta-log "${ITER_LOG}" -e "${Q_CAROL_ADDED}" 2>/dev/null)"
  b="$(timeout 10 "${BIN}" --data-cottas "${ARTIFACT}" --delta-log "${ITER_LOG}" -e "${Q_ANCHOR_REMOVED}" 2>/dev/null)"
  c="$(timeout 10 "${BIN}" --data-cottas "${ARTIFACT}" --delta-log "${ITER_LOG}" -e "${Q_DOCS_EMPTY}" 2>/dev/null)"
  tuple="${a}|${b}|${c}"

  if [[ "${tuple}" == "${pre_tuple}" || "${tuple}" == "${post_tuple}" ]]; then
    CRASH_CLEAN=$((CRASH_CLEAN + 1))
  elif [[ -z "${a}" || -z "${b}" || -z "${c}" ]]; then
    echo "  iter ${iter}: query itself failed (delay=${DELAY_MS}ms) a=${a} b=${b} c=${c}"
    CRASH_UNEXPECTED=$((CRASH_UNEXPECTED + 1))
  else
    echo "  iter ${iter}: TORN STATE (delay=${DELAY_MS}ms) tuple=${tuple} (neither pre=${pre_tuple} nor post=${post_tuple})"
    CRASH_TORN=$((CRASH_TORN + 1))
  fi
  rm -f "${ITER_LOG}" "${WORKDIR}/crash_append_${iter}.log"
done

echo "kill-mid-append: ${CRASH_CLEAN} clean recoveries, ${CRASH_TORN} torn states, ${CRASH_UNEXPECTED} unexpected failures (out of ${KILL_ITERATIONS} iterations)"
if [[ ${CRASH_TORN} -gt 0 || ${CRASH_UNEXPECTED} -gt 0 ]]; then
  fail "kill-mid-append-never-torn"
else
  pass "kill-mid-append-never-torn"
fi

echo
echo "============================================================"
echo "durable_update_stage3 summary: ${PASS_COUNT} pass, ${FAIL_COUNT} fail (out of $((PASS_COUNT+FAIL_COUNT)))"

exit "${FAIL}"
