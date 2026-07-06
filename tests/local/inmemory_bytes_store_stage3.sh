#!/usr/bin/env bash
# tests/local/inmemory_bytes_store_stage3.sh
#
# Stage 3 acceptance for docs/designissues/2026-07-06-inmemory-bytes-
# store.md: "wire serialize_cottas -> buffer -> query, native CLI, as
# a new mode" -- `factoidal query --data-cottas-mem FILE` (bin/
# factoidal-cli/factoidal_cli.ml's register_cottas_mem_file, stage 1's
# Parquet_Footer.register_memory_buffer glue underneath it).
#
# Three things this script proves, all against the SAME real .cottas
# artifact (built once, from tests/local/data/cottas_sample.nq via
# tools/corpus_pipeline.py, same recipe as tests/local/
# cottas_row_order_regressions.sh and durable_update_stage3.sh):
#
#   (a) `--data-cottas-mem FILE` gives IDENTICAL query results to
#       `--data-cottas FILE` across SELECT/ASK/GRAPH shapes -- the
#       buffer path and the file path are the SAME reader, different
#       byte source only (design doc §2.1/§2.4's "one reader, verified
#       once" claim, exercised end-to-end through the real CLI binary
#       rather than a unit-test harness).
#   (b) The delta-log overlay (--delta-log) composes with the BUFFER
#       base exactly like it composes with the file base today --
#       design doc §2.4's "the write/delta-overlay story composes
#       unchanged" claim. Reuses bin/delta-log-probe/probe.ml's
#       scenario-write batch (the same one durable_update_stage3.sh
#       drives) so the expected post-update answers are pinned by that
#       stage's own fixture, not re-derived here.
#   (c) `--data-cottas-mem` on a nonexistent file fails loudly (exit
#       nonzero, stderr message) rather than silently registering
#       garbage -- register_cottas_mem_file's own Sys.file_exists
#       guard.
#
# Per CLAUDE.md rule #17 every external process is bounded; rule #14
# no `|| true` swallowing exit codes; rule #25 the summary spells out
# N/N/N in words.

set -uo pipefail

if ! command -v ocamlfind >/dev/null 2>&1; then
  OPAM_ENV_RC=0
  eval "$(opam env --switch=fstar 2>/dev/null)" || OPAM_ENV_RC=$?
  if [[ ${OPAM_ENV_RC} -ne 0 ]]; then
    echo "WARNING: 'opam env --switch=fstar' exited ${OPAM_ENV_RC}; proceeding." >&2
  fi
fi

ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
OCAML_OUT="${ROOT}/formal/fstar/ocaml-output"
BIN="${OCAML_OUT}/factoidal"
PYCOTTAS_PYTHON="${PYCOTTAS_PYTHON:-${ROOT}/_tmp.junk/pycottas-venv/bin/python}"
TMPDIR_BASE="${TMPDIR:-/tmp}"
WORKDIR="$(mktemp -d "${TMPDIR_BASE}/factoidal-inmemory-bytes-stage3-XXXXXX")"
trap 'rm -rf "${WORKDIR}"' EXIT

PASS_COUNT=0
FAIL_COUNT=0
FAIL=0

pass() { PASS_COUNT=$((PASS_COUNT + 1)); echo "PASS $1"; }
fail() { FAIL_COUNT=$((FAIL_COUNT + 1)); FAIL=1; echo "FAIL $1"; shift; [[ $# -gt 0 ]] && printf '  %s\n' "$@"; }

if [[ ! -x "${BIN}" ]]; then
  echo "ERROR: ${BIN} not found -- run 'cd formal/fstar && ./build-ocaml.sh extract compile' first." >&2
  exit 2
fi

echo "== inmemory_bytes_store_stage3 =="
echo "workdir=${WORKDIR}"
echo

# ------------------------------------------------------------------
# Build the fixture .cottas artifact (same fixture as durable_update_
# stage3.sh / cottas_row_order_regressions.sh).
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
  echo "inmemory_bytes_store_stage3 summary: ${PASS_COUNT} pass, ${FAIL_COUNT} fail (out of $((PASS_COUNT+FAIL_COUNT)))"
  exit 1
fi
pass "cottas-store-build"

run_file() { timeout 30 "${BIN}" --data-cottas "${ARTIFACT}" -e "$1" 2>/dev/null; }
run_mem()  { timeout 30 "${BIN}" --data-cottas-mem "${ARTIFACT}" -e "$1" 2>/dev/null; }

# ------------------------------------------------------------------
# (a) file vs buffer, same query, must match byte-for-byte -- across
# SELECT, ASK, GRAPH-scoped, and predicate-bound shapes.
# ------------------------------------------------------------------
echo "-- (a) file vs --data-cottas-mem: identical results --"

QUERIES=(
  "count|SELECT (COUNT(*) AS ?c) WHERE { ?s ?p ?o }"
  "select-all|SELECT ?s ?p ?o WHERE { ?s ?p ?o } ORDER BY ?s ?p ?o"
  "ask-known|ASK { <https://example.org/alice> <https://example.org/name> \"Alice\" }"
  "ask-absent|ASK { <https://example.org/nobody> <https://example.org/name> \"Nobody\" }"
  "graph-named|SELECT ?s ?p ?o WHERE { GRAPH <https://example.org/graph/people> { ?s ?p ?o } } ORDER BY ?s ?p ?o"
  "graph-var|SELECT ?g (COUNT(*) AS ?c) WHERE { GRAPH ?g { ?s ?p ?o } } GROUP BY ?g ORDER BY ?g"
  "bound-p|SELECT ?s ?o WHERE { ?s <https://example.org/name> ?o } ORDER BY ?s"
)

for entry in "${QUERIES[@]}"; do
  label="${entry%%|*}"
  q="${entry#*|}"
  file_out="$(run_file "${q}")"
  mem_out="$(run_mem "${q}")"
  if [[ "${file_out}" == "${mem_out}" ]]; then
    pass "identical/${label}"
  else
    fail "identical/${label}" "file=<<<${file_out}>>>" "mem=<<<${mem_out}>>>"
  fi
done

# ------------------------------------------------------------------
# (b) delta-log overlay composes with the buffer base the same way it
# composes with the file base. Reuses bin/delta-log-probe/probe.ml's
# scenario-write batch (durable_update_stage3.sh's own fixture-derived
# scenario), so the queries + expectations mirror that stage's proof
# rather than re-deriving new ones.
# ------------------------------------------------------------------
echo
echo "-- (b) --delta-log composes with --data-cottas-mem like --data-cottas --"

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
  "${ROOT}/bin/delta-log-probe/probe.ml" \
  -o "${PROBE_BIN}" 2>&1) || BUILD_RC=$?
if [[ ${BUILD_RC} -ne 0 ]]; then
  fail "probe-driver-build" "${BUILD_OUT}"
else
  pass "probe-driver-build"
  LOG_PATH="${WORKDIR}/data.deltalog"
  timeout 30 "${PROBE_BIN}" scenario-write "${LOG_PATH}" >"${WORKDIR}/scenario-write.log" 2>&1
  WRITE_RC=$?
  if [[ ${WRITE_RC} -ne 0 ]] || ! grep -q '^SCENARIO_WRITE_OK' "${WORKDIR}/scenario-write.log"; then
    fail "scenario-write" "$(cat "${WORKDIR}/scenario-write.log")"
  else
    pass "scenario-write"

    Q_CAROL_ADDED='ASK { <https://example.org/carol> <https://example.org/name> "Carol" }'
    Q_ANCHOR_REMOVED='ASK { <https://example.org/default-subject> <https://example.org/status> "default" }'
    Q_EVENTS_ADD='ASK { GRAPH <https://example.org/graph/events> { <https://example.org/carol> <https://example.org/attends> <https://example.org/event-x> } }'
    Q_DOCS_EMPTY='ASK { GRAPH <https://example.org/graph/docs> { ?s ?p ?o } }'

    delta_file() { timeout 30 "${BIN}" --data-cottas "${ARTIFACT}" --delta-log "${LOG_PATH}" -e "$1" 2>/dev/null; }
    delta_mem()  { timeout 30 "${BIN}" --data-cottas-mem "${ARTIFACT}" --delta-log "${LOG_PATH}" -e "$1" 2>/dev/null; }

    for entry in \
      "carol-added|${Q_CAROL_ADDED}|true" \
      "anchor-removed|${Q_ANCHOR_REMOVED}|false" \
      "events-graph-add|${Q_EVENTS_ADD}|true" \
      "docs-cleared|${Q_DOCS_EMPTY}|false"
    do
      IFS='|' read -r label q expected <<< "${entry}"
      got_file="$(delta_file "${q}")"
      got_mem="$(delta_mem "${q}")"
      if [[ "${got_file}" == "${expected}" ]]; then
        pass "delta-file/${label}"
      else
        fail "delta-file/${label}" "expected=${expected} got=${got_file}"
      fi
      if [[ "${got_mem}" == "${expected}" ]]; then
        pass "delta-mem/${label}"
      else
        fail "delta-mem/${label}" "expected=${expected} got=${got_mem}"
      fi
      if [[ "${got_file}" == "${got_mem}" ]]; then
        pass "delta-file-vs-mem/${label}"
      else
        fail "delta-file-vs-mem/${label}" "file=${got_file} mem=${got_mem}"
      fi
    done
  fi
fi

# ------------------------------------------------------------------
# (c) nonexistent file: --data-cottas-mem must fail loudly, not
# silently register garbage bytes under a handle nothing ever reads
# correctly.
# ------------------------------------------------------------------
echo
echo "-- (c) --data-cottas-mem on a missing file fails loudly --"
MISSING="${WORKDIR}/does-not-exist.cottas"
MISSING_RC=0
MISSING_OUT="$(timeout 10 "${BIN}" --data-cottas-mem "${MISSING}" -e 'ASK { ?s ?p ?o }' 2>&1)" || MISSING_RC=$?
if [[ ${MISSING_RC} -ne 0 ]] && printf '%s' "${MISSING_OUT}" | grep -qi "not found"; then
  pass "missing-file-fails-loudly"
else
  fail "missing-file-fails-loudly" "rc=${MISSING_RC} out=${MISSING_OUT}"
fi

echo
echo "============================================================"
echo "inmemory_bytes_store_stage3 summary: ${PASS_COUNT} pass, ${FAIL_COUNT} fail (out of $((PASS_COUNT+FAIL_COUNT)))"

exit "${FAIL}"
