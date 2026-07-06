#!/bin/bash
# tests/local/cottas_native_import_regressions.sh — regression pins for
# the native (zero-Python) COTTAS store creation path:
#
#   factoidal import --nq FILE --out DIR
#     (RDF.CottasStore.BaseWriter.serialize_cottas, 2026-07-06 — the
#      "why is Python still needed to write it" gap)
#
# Checks, three-way per the landing brief:
#   (1) import a real fixture and every query agrees with the in-memory
#       engine on the same data (COUNT, GRAPH count, point lookup);
#   (2) our reader's own walk passes against the imported store
#       (COUNT via the on-disk COTTAS backend IS that walk; sidecars
#       eagerly present);
#   (3) CROSS-IMPLEMENTATION: DuckDB parquet_scan reads the file and
#       row count + schema match (skipped with a loud SKIP line if the
#       pycottas venv is absent — the unit-level byte pins in
#       tests/unit/cottas_base_writer_roundtrip.ml still run everywhere).
#   (4) compaction --native-writer produces a queryable new version with
#       all 10 sidecars and a flipped `current` symlink.
#
# Rule anchors: #14 (no `|| true`), #16 (no truncation), #25 (scores in
# words).

set -uo pipefail

ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
BIN="${ROOT}/formal/fstar/ocaml-output/factoidal"
PYCOTTAS_PYTHON="${PYCOTTAS_PYTHON:-${ROOT}/_tmp.junk/pycottas-venv/bin/python}"
TMPDIR_BASE="${TMPDIR:-/tmp}"
WORKDIR="$(mktemp -d "${TMPDIR_BASE}/factoidal-native-import-XXXXXX")"
trap 'rm -rf "${WORKDIR}"' EXIT

PASS_COUNT=0
FAIL_COUNT=0
pass() { PASS_COUNT=$((PASS_COUNT + 1)); echo "PASS $1"; }
fail() { FAIL_COUNT=$((FAIL_COUNT + 1)); echo "FAIL $1"; shift; [[ $# -gt 0 ]] && printf '  %s\n' "$@"; }

if [[ ! -x "${BIN}" ]]; then
  echo "ERROR: ${BIN} not found — run 'cd formal/fstar && ./build-ocaml.sh compile' first." >&2
  exit 2
fi

INPUT="${ROOT}/tests/local/data/cottas_sample.nq"
STORE="${WORKDIR}/store"

echo "== cottas_native_import_regressions =="
echo "workdir=${WORKDIR}"

# ------------------------------------------------------------------
# (0) Import.
# ------------------------------------------------------------------
IMPORT_RC=0
IMPORT_OUT=$(timeout 120 "${BIN}" import --nq "${INPUT}" --out "${STORE}" 2>&1) || IMPORT_RC=$?
if [[ ${IMPORT_RC} -ne 0 ]]; then
  fail "import-invocation" "${IMPORT_OUT}"
  echo "cottas_native_import_regressions: ${PASS_COUNT} pass, $((FAIL_COUNT)) fail"
  exit 1
fi
pass "import-invocation"

ARTIFACT="${STORE}/data.cottas"
[[ -f "${ARTIFACT}" ]] && pass "base-file-written" || fail "base-file-written"

# All 10 eager sidecars + epoch marker + initialized delta log.
SIDECAR_MISSING=""
for sfx in .s.dict .s.presence .p.dict .p.presence .o.dict .o.presence \
           .g.dict .g.presence .p.offsets .po.presence; do
  [[ -f "${ARTIFACT}${sfx}" ]] || SIDECAR_MISSING="${SIDECAR_MISSING} ${sfx}"
done
if [[ -z "${SIDECAR_MISSING}" ]]; then
  pass "sidecars-eager-built (all 10)"
else
  fail "sidecars-eager-built" "missing:${SIDECAR_MISSING}"
fi
[[ -f "${STORE}/data.compacted-epoch" ]] && pass "epoch-marker-written" || fail "epoch-marker-written"
[[ -f "${STORE}/data.deltalog" ]] && pass "deltalog-initialized" || fail "deltalog-initialized"

# ------------------------------------------------------------------
# (1)+(2) Query agreement: in-memory vs the on-disk COTTAS walk.
# ------------------------------------------------------------------
row4() { sed -n '4p'; }

compare_query() {
  local name="$1" q="$2"
  local mem cot
  mem=$(timeout 60 "${BIN}" query --data "${INPUT}" -e "${q}" 2>/dev/null | row4)
  cot=$(timeout 60 "${BIN}" query --data-cottas "${ARTIFACT}" -e "${q}" 2>/dev/null | row4)
  if [[ -n "${mem}" && "${mem}" == "${cot}" ]]; then
    pass "query-parity/${name}"
  else
    fail "query-parity/${name}" "mem=${mem}" "cottas=${cot}"
  fi
}

compare_query "default-graph-count" 'SELECT (COUNT(*) AS ?c) WHERE { ?s ?p ?o }'
compare_query "named-graph-count"   'SELECT (COUNT(*) AS ?c) WHERE { GRAPH ?g { ?s ?p ?o } }'
compare_query "point-lookup" 'SELECT ?o WHERE { GRAPH <https://example.org/graph/people> { <https://example.org/alice> <https://example.org/name> ?o } }'
compare_query "distinct-graphs" 'SELECT (COUNT(DISTINCT ?g) AS ?c) WHERE { GRAPH ?g { ?s ?p ?o } }'

# ------------------------------------------------------------------
# (3) DuckDB parquet_scan cross-implementation check.
# ------------------------------------------------------------------
if [[ -x "${PYCOTTAS_PYTHON}" ]] && "${PYCOTTAS_PYTHON}" -c "import duckdb" 2>/dev/null; then
  DUCK_RC=0
  DUCK_OUT=$("${PYCOTTAS_PYTHON}" - "${ARTIFACT}" <<'EOF'
import sys, duckdb
con = duckdb.connect(":memory:")
n = con.execute(f"SELECT COUNT(*) FROM parquet_scan('{sys.argv[1]}')").fetchone()[0]
cols = [c[0] + ":" + c[1] for c in con.execute(f"DESCRIBE SELECT * FROM parquet_scan('{sys.argv[1]}')").fetchall()]
g = con.execute(f"SELECT COUNT(*) FROM parquet_scan('{sys.argv[1]}') WHERE g = 'DEFAULT'").fetchone()[0]
print(f"rows={n} default_g={g} schema={','.join(cols)}")
EOF
  ) || DUCK_RC=$?
  if [[ ${DUCK_RC} -ne 0 ]]; then
    fail "duckdb-parquet-scan" "${DUCK_OUT}"
  else
    echo "  duckdb: ${DUCK_OUT}"
    [[ "${DUCK_OUT}" == *"rows=5"* ]] && pass "duckdb-row-count" || fail "duckdb-row-count" "${DUCK_OUT}"
    [[ "${DUCK_OUT}" == *"default_g=1"* ]] && pass "duckdb-default-graph-sentinel" || fail "duckdb-default-graph-sentinel" "${DUCK_OUT}"
    [[ "${DUCK_OUT}" == *"schema=s:VARCHAR,p:VARCHAR,o:VARCHAR,g:VARCHAR"* ]] \
      && pass "duckdb-schema-varchar" || fail "duckdb-schema-varchar" "${DUCK_OUT}"
  fi
else
  echo "SKIP duckdb-parquet-scan (pycottas venv or duckdb module not available at ${PYCOTTAS_PYTHON})"
fi

# ------------------------------------------------------------------
# (4) Native compaction: chunk-layout store, compact --native-writer.
# ------------------------------------------------------------------
CHUNK="${WORKDIR}/chunk/sample"
mkdir -p "${CHUNK}"
NAT_RC=0
timeout 120 "${BIN}" import --nq "${INPUT}" --out "${CHUNK}/v1" >/dev/null 2>&1 || NAT_RC=$?
mv "${CHUNK}/v1/data.deltalog" "${CHUNK}/data.deltalog"
COMPACT_RC=0
COMPACT_OUT=$(timeout 120 "${BIN}" compact --data-cottas "${CHUNK}/v1/data.cottas" \
  --delta-log "${CHUNK}/data.deltalog" --native-writer 2>&1) || COMPACT_RC=$?
if [[ ${COMPACT_RC} -ne 0 ]]; then
  fail "native-compact-invocation" "${COMPACT_OUT}"
else
  pass "native-compact-invocation"
  [[ "${COMPACT_OUT}" == *"native writer (RDF.CottasStore.BaseWriter)"* ]] \
    && pass "native-compact-uses-native-writer" \
    || fail "native-compact-uses-native-writer" "${COMPACT_OUT}"
  CUR="${CHUNK}/current/data.cottas"
  [[ -f "${CUR}" ]] && pass "native-compact-current-live" || fail "native-compact-current-live"
  POST=$(timeout 60 "${BIN}" query --data-cottas "${CUR}" \
    -e 'SELECT (COUNT(*) AS ?c) WHERE { GRAPH ?g { ?s ?p ?o } }' 2>/dev/null | row4)
  [[ "${POST}" == *'"4"'* ]] && pass "native-compact-post-query" || fail "native-compact-post-query" "got: ${POST}"
  MISSING2=""
  for sfx in .s.dict .s.presence .p.dict .p.presence .o.dict .o.presence \
             .g.dict .g.presence .p.offsets .po.presence; do
    [[ -f "${CUR}${sfx}" ]] || MISSING2="${MISSING2} ${sfx}"
  done
  [[ -z "${MISSING2}" ]] && pass "native-compact-sidecars (all 10)" \
    || fail "native-compact-sidecars" "missing:${MISSING2}"
fi

echo
echo "cottas_native_import_regressions: ${PASS_COUNT} pass, ${FAIL_COUNT} fail"
[[ ${FAIL_COUNT} -eq 0 ]] || exit 1
