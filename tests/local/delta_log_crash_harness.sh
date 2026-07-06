#!/usr/bin/env bash
# tests/local/delta_log_crash_harness.sh
#
# Crash-kill harness for the durable-UPDATE delta-log file, stage 2 of
# docs/designissues/2026-07-06-durable-update-design.md (§3.3's
# fsync/rename protocol, staged-plan Stage 2/3 acceptance test brought
# forward as far as file-level durability goes).
#
# What this proves, empirically, against a REAL killed process (not a
# simulated crash): a `probe append` process is repeatedly SIGKILLed at
# random points -- including mid-batch, because the driver deliberately
# slices each batch's bytes across several small `delta_log_append`
# calls with a tiny pause between them (bin/delta-log-probe/probe.ml) --
# and on every single iteration, `probe verify` (which calls the
# F*-verified, Tot `RDF_Store_Columnar_DeltaLog.parse_log`) must recover
# EXACTLY the batches that were fully appended-and-fsynced before the
# kill, and NEVER accept a torn/corrupt batch as if it were valid data.
#
# Also runs the design doc's own stage-2 acceptance line once, up
# front (no kill involved): "expected_digest batch =
# sha256(read_bytes(path)) after a real append+fsync+read-back cycle,
# on-disk, this sandbox."
#
# Per CLAUDE.md rule #17 every external process this script runs is
# bounded; per rule #25 the summary line spells out N/N/N in words,
# not a cryptic ratio; per rule #14 no `|| true` swallowing -- every
# exit code is captured explicitly.

set -uo pipefail

ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
OCAML_OUT="${ROOT}/formal/fstar/ocaml-output"
PROBE_ML="${ROOT}/bin/delta-log-probe/probe.ml"
TMPDIR_BASE="${TMPDIR:-/tmp}"
WORKDIR="$(mktemp -d "${TMPDIR_BASE}/factoidal-deltalog-crash-XXXXXX")"
trap 'rm -rf "${WORKDIR}"' EXIT

PROBE_BIN="${WORKDIR}/probe"

# --- deterministic master seed --------------------------------------
# Overridable so a specific failing seed can be replayed; logged either
# way so every run is reproducible (rule: "deterministic seed logged").
MASTER_SEED="${DELTA_LOG_HARNESS_SEED:-20260706}"
KILL_ITERATIONS="${DELTA_LOG_HARNESS_ITERS:-120}"
NUM_BATCHES=20
OPS_PER_BATCH=6
CHUNK_SIZE=8

echo "== delta_log_crash_harness =="
echo "master_seed=${MASTER_SEED} kill_iterations=${KILL_ITERATIONS}"
echo "workdir=${WORKDIR}"
echo

if [[ ! -d "${OCAML_OUT}" ]]; then
  echo "ERROR: ${OCAML_OUT} does not exist -- run" >&2
  echo "       'cd formal/fstar && ./build-ocaml.sh extract compile' first." >&2
  exit 2
fi

# --- self-contained build of the probe driver -----------------------
# Same convention as tests/unit/run-all.sh: an explicit, ordered .cmx
# list up through this module's own dependencies, compiled directly
# with ocamlfind (no build-ocaml.sh registration -- probe.ml is a
# throwaway test driver, not a committed consumer binary). This prefix
# MUST stay a subset of tests/unit/run-all.sh's COMMON_MODULES, in the
# same order, up to and including RDF_Store_Columnar_DeltaLog --
# duplicated here (not sourced from run-all.sh) so this script has no
# fragile parse-the-other-script dependency; if that list's ORDER
# changes upstream, this one needs the same edit (same accepted risk
# run-all.sh's own header comment documents for its relationship to
# build-ocaml.sh).
COMMON_MODULES=(
  Util_Log RDF_Format RDF_Vocabulary RDF_Term RDF_Triple RDF_Indexed RDF_Graph
  RDF_Vocabulary_Axioms RDFS_Closure OWL_Closure RDF_Graph_Executable RDF_List_Helpers
  RDF_Bytes RDF_Store_Loader Parquet_Footer OWL_Vocabulary Tableau Parser_FastString
  RDF_IRI RDF_NQuads_Serialize Parser_IRI Parser_Combinators Parser_TurtleScanner
  Parser_NTriples HDT_Container Parser_Turtle Parser_NQuads Parser_TriG Parser_XML
  Parser_XPath XPath_Eval XML_Wellformedness XML_Namespaces Parser_RDFXML Parser_SRX
  Parser_CSVResults Parser_JSONResults Parser_JSON SPARQL11_IRI_Resolve SPARQL_JSON_Escape
  JSONLD_Loader JSONLD_Context JSONLD_Expand Parser_JSONLD SPARQL_Eval_TimeBudget
  SPARQL_Eval_Limits SPARQL_HTTP_Response SPARQL_HTTP_Timing SPARQL_HTTP_BackendInfo
  SPARQL_HTTP_QueriesIndex SPARQL_HTTP_StaticFiles SPARQL_HTTP_Admin SPARQL_HTTP_Routes
  Parser_Ballyhoo Parser_BallyhooBloom Parser_BallyhooHDT Parser_BallyhooHDTQ
  Parser_BallyhooCOTTAS RDF_CottasStore_ColumnSeq RDF_CottasStore_PageCache
  RDF_CottasStore_OnDiskIndex RDF_CottasStore_DictWriter RDF_CottasStore_PresenceBitmap
  RDF_CottasStore_PresenceWriter RDF_CottasStore_CompoundPresenceBitmap
  RDF_CottasStore_CompoundPresenceWriter RDF_CottasStore_OffsetsWriter RDF_CottasStore_LazyDict
  RDF_CottasStore_LazyDictRegistry RDF_Store_LazyTermCache RDF_Store_HDTTermCacheRegistry
  RDF_Store_Columnar_OffsetIndex RDF_Store_Columnar_DeltaLog fstar_pure_hashes
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

echo "-- building probe driver --"
BUILD_RC=0
BUILD_OUT=$(cd "${WORKDIR}" && ocamlfind ocamlopt \
  -package fstar.lib,str,zarith,sha,digestif.c,unix,uucp \
  -linkpkg -w -8-14-26 \
  -I "${OCAML_OUT}" \
  "${CMX_LIST[@]}" \
  "${OCAML_OUT}/parquet_zstd_stubs.o" \
  "${ZSTD_LIB_FLAGS[@]}" \
  "${PROBE_ML}" \
  -o "${PROBE_BIN}" 2>&1) || BUILD_RC=$?

if [[ ${BUILD_RC} -ne 0 ]]; then
  echo "BUILD FAILED (rc=${BUILD_RC})"
  echo "${BUILD_OUT}" | sed 's/^/  /'
  exit 1
fi
echo "  probe driver built: ${PROBE_BIN}"
echo

# --- stage 2 acceptance test: hash-witness, no kill involved --------
echo "-- hash-witness check (design doc stage 2 acceptance line) --"
HASH_LOG_PATH="${WORKDIR}/hashcheck.log"
HASH_OUT=$("${PROBE_BIN}" hashcheck "${HASH_LOG_PATH}" 2>&1)
HASH_RC=$?
echo "${HASH_OUT}" | sed 's/^/  /'
if [[ ${HASH_RC} -ne 0 ]] || ! grep -q '^HASH_WITNESS=PASS' <<<"${HASH_OUT}"; then
  echo "FATAL: hash-witness check failed -- aborting before the kill loop." >&2
  exit 1
fi
echo

# --- the kill loop ----------------------------------------------------
RANDOM="${MASTER_SEED}"   # bash's own PRNG, seeded -- deterministic per run

KILLS=0
CLEAN_RECOVERIES=0
CORRUPT_ACCEPTS=0
UNEXPECTED_FAILURES=0

for ((iter = 1; iter <= KILL_ITERATIONS; iter++)); do
  LOG_PATH="${WORKDIR}/iter_${iter}.log"
  SEED=$(( MASTER_SEED + iter ))

  INIT_RC=0
  timeout 10 "${PROBE_BIN}" init "${LOG_PATH}" >/dev/null 2>&1 || INIT_RC=$?
  if [[ ${INIT_RC} -ne 0 ]]; then
    echo "iter ${iter}: INIT FAILED (rc=${INIT_RC})"
    UNEXPECTED_FAILURES=$((UNEXPECTED_FAILURES + 1))
    continue
  fi

  # Launch the appender in the background, capped by `timeout` so a
  # hung process (should never happen, but rule #17) can't stall the
  # whole harness.
  timeout 10 "${PROBE_BIN}" append "${LOG_PATH}" "${SEED}" \
    "${NUM_BATCHES}" "${OPS_PER_BATCH}" "${CHUNK_SIZE}" \
    >"${WORKDIR}/append_${iter}.log" 2>&1 &
  APPEND_PID=$!

  # Random kill delay in [5, 400] ms -- wide enough to land anywhere
  # from "before the first append call" through "well after the last
  # batch's fsync" (in which case the process exits cleanly on its
  # own and the kill is a no-op against an already-dead pid).
  DELAY_MS=$(( 5 + (RANDOM % 396) ))
  DELAY_S=$(awk -v ms="${DELAY_MS}" 'BEGIN{printf "%.3f", ms/1000}')
  sleep "${DELAY_S}"

  if kill -0 "${APPEND_PID}" 2>/dev/null; then
    kill -9 "${APPEND_PID}" 2>/dev/null
    KILLS=$((KILLS + 1))
  fi
  wait "${APPEND_PID}" 2>/dev/null

  VERIFY_RC=0
  VERIFY_OUT=$(timeout 10 "${PROBE_BIN}" verify "${LOG_PATH}" "${SEED}" \
    "${NUM_BATCHES}" "${OPS_PER_BATCH}" 2>&1) || VERIFY_RC=$?

  if [[ ${VERIFY_RC} -ne 0 ]]; then
    echo "iter ${iter}: VERIFY CRASHED (rc=${VERIFY_RC}, delay=${DELAY_MS}ms): ${VERIFY_OUT}"
    UNEXPECTED_FAILURES=$((UNEXPECTED_FAILURES + 1))
    continue
  fi

  CORRUPT=$(grep -oE 'CORRUPT_ACCEPTS=[0-9]+' <<<"${VERIFY_OUT}" | cut -d= -f2)
  RECOVERED=$(grep -oE 'RECOVERED=[0-9]+' <<<"${VERIFY_OUT}" | cut -d= -f2)

  if [[ -z "${CORRUPT}" ]]; then
    echo "iter ${iter}: VERIFY OUTPUT UNPARSEABLE (delay=${DELAY_MS}ms): ${VERIFY_OUT}"
    UNEXPECTED_FAILURES=$((UNEXPECTED_FAILURES + 1))
    continue
  fi

  if [[ "${CORRUPT}" -gt 0 ]]; then
    echo "iter ${iter}: CORRUPT ACCEPT (delay=${DELAY_MS}ms, recovered=${RECOVERED}, corrupt=${CORRUPT})"
    CORRUPT_ACCEPTS=$((CORRUPT_ACCEPTS + CORRUPT))
  else
    CLEAN_RECOVERIES=$((CLEAN_RECOVERIES + 1))
  fi

  rm -f "${LOG_PATH}" "${WORKDIR}/append_${iter}.log"
done

echo
echo "============================================================"
echo "delta_log_crash_harness summary: ${KILLS} kills, ${CLEAN_RECOVERIES} clean recoveries, ${CORRUPT_ACCEPTS} corrupt accepts (out of ${KILL_ITERATIONS} iterations, ${UNEXPECTED_FAILURES} unexpected failures)"
echo "master_seed=${MASTER_SEED}"

if [[ ${CORRUPT_ACCEPTS} -gt 0 || ${UNEXPECTED_FAILURES} -gt 0 ]]; then
  exit 1
fi
exit 0
