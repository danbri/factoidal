#!/usr/bin/env bash
# tests/local/virtual_rml_stage5.sh
#
# Stage 5 acceptance test (docs/designissues/2026-07-06-virtual-
# sources-design.md, §5's own staged-rollout table) for Part B: the
# virtual (non-materialized) RML backend -- RML.VirtualSource.fst's
# `caps_of_rml_source`, wired as SPARQL11.Store's `GB_VirtualRML` and
# exposed through `factoidal --data-rml MAPPING.ttl`.
#
# Fixture: third_party/testing/rml-modules/rml-core/test-cases/
# RMLTC0012b-JSON (rml-core submodule, initialized below if missing).
# Deliberately chosen -- two TriplesMaps, each over its OWN JSON
# source file (persons.json, lives.json, 3 rows apiece), DISTINCT
# constant predicates (foaf:name vs ex:city), template-shaped
# BlankNode subjects ("{$.fname}{$.lname}") -- so ONE small fixture
# exercises every pushdown dimension the design doc's §3.2 model
# describes:
#   - bound-predicate lookup, exercising STRUCTURAL map narrowing:
#     `?s <...city> ?o` has bp=ex:city, which rules out TriplesMap1
#     entirely (its only predicate is foaf:name, a TMF_Constant
#     mismatch) -- persons.json's 3 rows are never read for this
#     query at all, not merely filtered after the fact.
#   - bound-subject lookup, exercising ROW-LEVEL template pushdown:
#     `?s foaf:name "Bob Smith" . ?s <...city> ?city` first solves
#     `?s foaf:name "Bob Smith"` (bp=foaf:name narrows to TriplesMap1,
#     giving _:BobSmith), then solves the second pattern with
#     bs=_:BobSmith bound; TriplesMap2's subject map is a TMF_Template
#     (not a constant), so it cannot be map-level narrowed -- instead
#     RML.VirtualSource.row_matches_bound_subject (via
#     json_iterate_filtered) evaluates just the subject template per
#     row and drops the "Sue Jones" row from lives.json's 3 BEFORE the
#     full per-row RML.Eval machinery runs, leaving 2.
#   - "a query touching two TriplesMaps": the SAME 2-BGP join query
#     above touches BOTH maps, one per triple pattern.
#   - unbound scan: baseline, `?s ?p ?o` over all 6 source rows (3+3),
#     matching all 4 triples in the fixture's own output.nq.
#   - COUNT: SPARQL's COUNT(*) aggregate over the unbound scan.
#   - ASK: a bound-object/bound-predicate ASK query.
#
# "Materialized" comparison side: the fixture's OWN vendored
# output.nq. bin/rml-runner is MEASURED to reproduce this file
# byte-for-byte (rml-core 76 pass, 0 fail out of 76, including
# RMLTC0012b-JSON -- docs/designissues/2026-07-05-rml-program-plan.md
# Stage 8's own score line) via RML.Eval.eval_triples_map, the exact
# materializing path RML.VirtualSource.fst's OWN banner says
# `sc_solve` must NOT call per query. Loading output.nq directly via
# `--data` is therefore equivalent to materializing via rml-runner,
# with no new OCaml glue needed to re-derive it (per this task's
# brief: reuse the existing seam rather than fork a second
# materializer).
#
# Pushdown evidence ("trace/counter or timing evidence, labeled"):
# tests/local/rml_virtual_pushdown_probe.ml (a throwaway OCaml test
# driver, same ad-hoc-harness-compiled-by-its-own-script convention as
# tests/local/delta_log_crash_harness.sh's probe.ml -- NOT registered
# in build-ocaml.sh) calls RML_VirtualSource.rml_solve_trace directly
# and prints, per candidate TriplesMap, the row count surviving
# pushdown -- a deterministic, Tot-computed number, asserted below.
#
# Per rule #17: every external process here is bounded (`timeout`).
# Per rule #25: pass/fail counts are always labeled, never a bare
# ratio.
set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
FIXTURE="${ROOT}/third_party/testing/rml-modules/rml-core/test-cases/RMLTC0012b-JSON"
BIN="${FACTOIDAL_BIN:-${ROOT}/formal/fstar/ocaml-output/factoidal}"
OCAML_OUT="${ROOT}/formal/fstar/ocaml-output"
PROBE_ML="${ROOT}/tests/local/rml_virtual_pushdown_probe.ml"
WORKDIR="$(mktemp -d "${TMPDIR:-/tmp}/factoidal-virtual-rml-XXXXXX")"
trap 'rm -rf "${WORKDIR}"' EXIT

FAIL=0
PASS=0

note() { echo "== $* =="; }
ok()   { PASS=$((PASS + 1)); echo "PASS: $*"; }
bad()  { FAIL=$((FAIL + 1)); echo "FAIL: $*"; }

# --- preconditions ----------------------------------------------------
if [[ ! -x "${BIN}" ]]; then
  echo "virtual_rml_stage5: factoidal binary not found or not executable: ${BIN}" >&2
  echo "(run 'cd formal/fstar && ./build-ocaml.sh extract compile' first)" >&2
  exit 2
fi

if [[ ! -f "${FIXTURE}/mapping.ttl" ]]; then
  note "initializing rml-core submodule (fixture missing)"
  ( cd "${ROOT}" && timeout 300 git submodule update --init third_party/testing/rml-modules/rml-core )
fi
if [[ ! -f "${FIXTURE}/mapping.ttl" ]]; then
  echo "virtual_rml_stage5: fixture still missing after submodule init: ${FIXTURE}" >&2
  exit 2
fi

MATERIALIZED_NQ="${FIXTURE}/output.nq"
if [[ ! -f "${MATERIALIZED_NQ}" ]]; then
  echo "virtual_rml_stage5: expected fixture output missing: ${MATERIALIZED_NQ}" >&2
  exit 2
fi

# --- sorted-rows-sha256 comparison helper -----------------------------
# CSV output: header line first, then one line per row. Sort only the
# DATA rows (the header must stay first and identical verbatim on both
# sides) before hashing, so row-order differences between backends
# (list-order over candidate TriplesMaps vs. N-Quads parse order) don't
# cause a false mismatch.
# Blank-node canonicalization: a SELECT * that exposes a blank-node
# subject prints its LABEL, and blank-node labels are deliberately not
# stable across serializations -- the virtual backend derives the
# label from the RML subject template's own output (RML.Eval's
# row_seed, e.g. "BobSmith"), while the MATERIALIZED side went through
# canonical N-Quads and back through the N-Quads parser, which renames
# every blank node (e.g. "d0_BobSmith"). The two graphs are
# ISOMORPHIC; only the labels differ. normalize_bnodes relabels every
# `_:token` to `_:b0`, `_:b1`, ... in order of FIRST APPEARANCE across
# the already-sorted rows -- a canonical relabeling that agrees on
# both sides exactly when the non-blank columns disambiguate the blank
# nodes (true for this fixture: each blank subject is uniquely fixed by
# its foaf:name / ex:city object). This is the SELECT-result analogue
# of the RDF.Canonical N-Quads comparison the design doc's stage-2/5
# acceptance lines name.
normalize_bnodes() {
  awk '
    {
      line=$0; out=""
      while (match(line, /_:[A-Za-z0-9_]+/)) {
        tok=substr(line, RSTART, RLENGTH)
        pre=substr(line, 1, RSTART-1)
        if (!(tok in m)) { m[tok]="_:b" n; n++ }
        out=out pre m[tok]
        line=substr(line, RSTART+RLENGTH)
      }
      print out line
    }'
}

sorted_csv_hash() {
  local text="$1"
  {
    printf '%s\n' "${text}" | head -n1
    printf '%s\n' "${text}" | tail -n +2 | sort | normalize_bnodes
  } | sha256sum | awk '{print $1}'
}

run_virtual_csv() {
  local query="$1"
  timeout 60 "${BIN}" query --data-rml "${FIXTURE}/mapping.ttl" -o csv -e "${query}"
}

run_materialized_csv() {
  local query="$1"
  timeout 60 "${BIN}" query --data "${MATERIALIZED_NQ}" -o csv -e "${query}"
}

compare_select() {
  local label="$1" query="$2"
  local v_out m_out v_hash m_hash
  v_out="$(run_virtual_csv "${query}")" || { bad "${label}: --data-rml query failed"; return; }
  m_out="$(run_materialized_csv "${query}")" || { bad "${label}: --data (materialized) query failed"; return; }
  v_hash="$(sorted_csv_hash "${v_out}")"
  m_hash="$(sorted_csv_hash "${m_out}")"
  if [[ "${v_hash}" == "${m_hash}" ]]; then
    ok "${label}: virtual and materialized sorted-rows sha256 match (${v_hash})"
  else
    bad "${label}: sorted-rows sha256 MISMATCH (virtual=${v_hash} materialized=${m_hash})"
    echo "  --- virtual ---"; echo "${v_out}" | sed 's/^/    /'
    echo "  --- materialized ---"; echo "${m_out}" | sed 's/^/    /'
  fi
}

# --- SELECT/two-TriplesMap/bound-predicate/bound-subject/unbound -----
note "unbound scan: SELECT * WHERE { ?s ?p ?o }"
compare_select "unbound-scan" 'SELECT * WHERE { ?s ?p ?o }'

note "bound-predicate lookup: SELECT * WHERE { ?s <http://example.com/city> ?o }"
compare_select "bound-predicate" 'SELECT * WHERE { ?s <http://example.com/city> ?o }'

note "bound-subject lookup via join (touches both TriplesMaps): foaf:name -> ex:city"
compare_select "bound-subject-join" \
  'SELECT ?city WHERE { ?s <http://xmlns.com/foaf/0.1/name> "Bob Smith" . ?s <http://example.com/city> ?city }'

# --- ASK ---------------------------------------------------------------
note "ASK { ?s <http://example.com/city> \"London\" }"
V_ASK="$(timeout 60 "${BIN}" query --data-rml "${FIXTURE}/mapping.ttl" -e 'ASK { ?s <http://example.com/city> "London" }' 2>&1)" || true
M_ASK="$(timeout 60 "${BIN}" query --data "${MATERIALIZED_NQ}" -e 'ASK { ?s <http://example.com/city> "London" }' 2>&1)" || true
if [[ "${V_ASK}" == "${M_ASK}" && "${V_ASK}" == "true" ]]; then
  ok "ASK: virtual and materialized both answer true"
else
  bad "ASK: virtual='${V_ASK}' materialized='${M_ASK}' (expected both 'true')"
fi

# --- COUNT ---------------------------------------------------------------
note "COUNT: SELECT (COUNT(*) AS ?n) WHERE { ?s ?p ?o }"
V_COUNT="$(timeout 60 "${BIN}" query --data-rml "${FIXTURE}/mapping.ttl" -o csv -e 'SELECT (COUNT(*) AS ?n) WHERE { ?s ?p ?o }' | tail -n +2)"
M_COUNT="$(timeout 60 "${BIN}" query --data "${MATERIALIZED_NQ}" -o csv -e 'SELECT (COUNT(*) AS ?n) WHERE { ?s ?p ?o }' | tail -n +2)"
if [[ "${V_COUNT}" == "${M_COUNT}" && "${V_COUNT}" == "4" ]]; then
  ok "COUNT: virtual and materialized both report 4"
else
  bad "COUNT: virtual='${V_COUNT}' materialized='${M_COUNT}' (expected both '4')"
fi

# --- pushdown evidence: fewer rows considered for a bound query -------
note "pushdown evidence: building rml_virtual_pushdown_probe"
# The probe is compiled ad-hoc with ocamlfind (same convention as
# tests/local/delta_log_crash_harness.sh); make sure the F* opam
# switch is on PATH even when the caller didn't activate it (rule #12).
if ! command -v ocamlfind >/dev/null 2>&1; then
  eval "$(opam env --switch=fstar 2>/dev/null)" || true
fi
COMMON_MODULES=(
  Util_Log RDF_Format RDF_Vocabulary RDF_Term RDF_Triple RDF_Indexed RDF_Graph
  RDF_Vocabulary_Axioms RDFS_Closure OWL_Closure RDF_Graph_Executable RDF_List_Helpers
  RDF_Bytes RDF_Store_Loader Parquet_Footer OWL_Vocabulary OWL_DirectMapping_Filter Tableau
  Parser_FastString RDF_IRI SPARQL11_IRI_Resolve Parser_IRI
  RDF_NQuads_Serialize
  Parser_Combinators Parser_TurtleScanner Parser_NTriples Parser_Turtle HDT_Container HDT_Dictionary HDT_Triples
  RDF_Geo_Types RDF_Geo_BBox Parser_WKT RDF_Geo_Topology RDF_Geo_Functions
  Parser_OWLFunctional
  RDF_Turtle_Serialize
  Parser_NQuads Parser_TriG Parser_XML XML_Wellformedness XML_Namespaces Parser_XPath XPath_Eval Parser_RDFXML
  Parser_SRX Parser_CSVResults Parser_JSONResults
  SPARQL_JSON_Escape
  Parser_JSON JSONLD_Loader JSONLD_Context JSONLD_Expand Parser_JSONLD
  SPARQL_Eval_TimeBudget
  SPARQL_Eval_Limits
  SPARQL_HTTP_Response
  SPARQL_HTTP_Timing
  SPARQL_HTTP_BackendInfo
  SPARQL_HTTP_QueriesIndex
  SPARQL_HTTP_StaticFiles
  SPARQL_HTTP_Admin
  SPARQL_HTTP_Routes
  Parser_Ballyhoo Parser_BallyhooBloom
  Parser_BallyhooHDT Parser_BallyhooHDTQ Parser_BallyhooCOTTAS
  RDF_CottasStore_ColumnSeq
  RDF_CottasStore_PageCache
  RDF_CottasStore_OnDiskIndex
  RDF_CottasStore_DictWriter
  RDF_CottasStore_PresenceBitmap
  RDF_CottasStore_PresenceWriter
  RDF_CottasStore_CompoundPresenceBitmap
  RDF_CottasStore_CompoundPresenceWriter
  RDF_CottasStore_OffsetsWriter
  RDF_CottasStore_BaseWriter
  RDF_CottasStore_LazyDict
  RDF_CottasStore_LazyDictRegistry
  RDF_Store_LazyTermCache
  RDF_Store_HDTTermCacheRegistry
  RDF_Store_Columnar_OffsetIndex RDF_Store_Columnar_DeltaLog
  SPARQL_Plan_Pruning
  SPARQL_Plan_Estimate
  SPARQL_Plan_Loader
  SPARQL_Plan_AccessPath
  RDF_CottasStore
  RDF_CottasStore_OnDiskRuntime
  RDF_CottasInMem
  fstar_pure_hashes
  RDF_Dataset_Graphs
  RDF_Canonical
  RDF_Canonical_Manifest
  SPARQL_FullText SPARQL11_Algebra XSD_Datatypes RDF_Pretty OWL_QueryRewrite OWL_QueryEval OWL_Tests_Manifest RIF_Core_Syntax Parser_RIFXML RIF_Core_Translation RIF_Core_Builtins RIF_Core_Conformance RIF_Core_Eval RIF_Core_Tests SPARQL11_Parser SHACL_Validation
  ShEx_Schema ShEx_Validation
  VC_Credential
  RML_Mapping RML_Sources RML_Eval
  CSVW_Metadata CSVW_URITemplate CSVW_Conversion
  RDF_Store_Columnar_DeltaMerge
  SPARQL_Plan_Streamable RDF_Store_Capabilities RDF_Store_Capabilities_Cottas RDF_Store_Capabilities_Delta
  RML_VirtualSource
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

PROBE_BIN="${WORKDIR}/rml_virtual_pushdown_probe"
BUILD_RC=0
BUILD_OUT=$(cd "${WORKDIR}" && timeout 300 ocamlfind ocamlopt \
  -package fstar.lib,str,zarith,sha,digestif.c,unix,uucp \
  -linkpkg -w -8-14-26 \
  -I "${OCAML_OUT}" \
  "${CMX_LIST[@]}" \
  "${OCAML_OUT}/parquet_zstd_stubs.o" \
  "${ZSTD_LIB_FLAGS[@]}" \
  "${PROBE_ML}" \
  -o "${PROBE_BIN}" 2>&1) || BUILD_RC=$?

if [[ ${BUILD_RC} -ne 0 ]]; then
  bad "pushdown-evidence probe failed to build (rc=${BUILD_RC})"
  echo "${BUILD_OUT}" | sed 's/^/  /'
else
  PROBE_OUT="$(timeout 60 "${PROBE_BIN}" "${FIXTURE}")"
  echo "${PROBE_OUT}" | sed 's/^/  /'
  UNBOUND_TOTAL="$(echo "${PROBE_OUT}" | awk '/^UNBOUND/{f=1} f && /TOTAL/{print $2; exit}' | sed 's/.*=//')"
  BOUND_TOTAL="$(echo "${PROBE_OUT}" | awk '/^BOUND bp=<http:\/\/example.com\/city>:$/{f=1} f && /TOTAL/{print $2; exit}' | sed 's/.*=//')"
  BOUND_BOTH_TOTAL="$(echo "${PROBE_OUT}" | awk '/^BOUND bp=<http:\/\/example.com\/city> AND bs=_:BobSmith/{f=1} f && /TOTAL/{print $2; exit}' | sed 's/.*=//')"
  if [[ "${UNBOUND_TOTAL}" == "6" ]]; then
    ok "pushdown evidence: unbound scan considers 6 rows (3 persons.json + 3 lives.json)"
  else
    bad "pushdown evidence: unbound scan considered ${UNBOUND_TOTAL} rows, expected 6"
  fi
  if [[ -n "${BOUND_TOTAL}" && "${BOUND_TOTAL}" -lt "${UNBOUND_TOTAL:-999}" && "${BOUND_TOTAL}" == "3" ]]; then
    ok "pushdown evidence: bp=ex:city considers 3 rows (persons.json's 3 skipped via map narrowing) vs 6 unbound"
  else
    bad "pushdown evidence: bp=ex:city considered '${BOUND_TOTAL}' rows, expected 3 (< 6 unbound)"
  fi
  if [[ -n "${BOUND_BOTH_TOTAL}" && "${BOUND_BOTH_TOTAL}" == "2" ]]; then
    ok "pushdown evidence: bp=ex:city AND bs=_:BobSmith considers 2 rows (Sue Jones row excluded via template pushdown) vs 3 for bp alone"
  else
    bad "pushdown evidence: bp+bs considered '${BOUND_BOTH_TOTAL}' rows, expected 2"
  fi
fi

# --- summary -----------------------------------------------------------
echo
echo "virtual_rml_stage5: ${PASS} pass, ${FAIL} fail (out of $((PASS + FAIL)))"
[[ "${FAIL}" -eq 0 ]]
