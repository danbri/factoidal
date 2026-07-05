#!/usr/bin/env bash
# Regression pin for docs/designissues/2026-07-05-disk-backed-db-perf-review.md
# roadmap item 3: characteristic-set row clustering (--row-order cs) +
# eager sidecar build (--build-sidecars) in tools/corpus_pipeline.py must
# not change query answers versus the unmodified producer/SPOG path (row
# order is semantically free per docs/cottas-format-v1.md §3), and the
# sidecar files must exist on disk right after import when requested.
#
# Builds two COTTAS artifacts from the same small fixture
# (tests/local/data/cottas_sample.nq, already used by
# cottas_corpus_regressions.sh): one with today's default behaviour
# (--row-order producer, no eager sidecars) and one with the new
# characteristic-set-clustered + eager-sidecar path, then diffs four
# query results (named-graph SELECT, default-graph ASK, COUNT(*), and
# GRAPH ?g GROUP BY count) across them.
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
BIN="${ROOT}/formal/fstar/ocaml-output/factoidal"
TMPDIR="${TMPDIR:-/tmp}"
WORKDIR="$(mktemp -d "${TMPDIR}/factoidal-cottas-roworder-XXXXXX")"
trap 'rm -rf "${WORKDIR}"' EXIT

INPUT="${ROOT}/tests/local/data/cottas_sample.nq"
PYCOTTAS_PYTHON="${PYCOTTAS_PYTHON:-${ROOT}/_tmp.junk/pycottas-venv/bin/python}"

UNCLUSTERED_ROOT="${WORKDIR}/unclustered"
CLUSTERED_ROOT="${WORKDIR}/clustered"
UNCLUSTERED_ARTIFACT="${UNCLUSTERED_ROOT}/sample-cottas/v1/data.cottas"
CLUSTERED_ARTIFACT="${CLUSTERED_ROOT}/sample-cottas/v1/data.cottas"

FAIL=0

"${PYCOTTAS_PYTHON}" "${ROOT}/tools/corpus_pipeline.py" materialize-nq-cottas-corpus \
  --input "${INPUT}" \
  --corpus-root "${UNCLUSTERED_ROOT}" \
  --dataset-name sample-cottas \
  --chunk-name sample-cottas \
  >"${WORKDIR}/build-unclustered.log" 2>&1

"${PYCOTTAS_PYTHON}" "${ROOT}/tools/corpus_pipeline.py" materialize-nq-cottas-corpus \
  --input "${INPUT}" \
  --corpus-root "${CLUSTERED_ROOT}" \
  --dataset-name sample-cottas \
  --chunk-name sample-cottas \
  --row-order cs \
  --build-sidecars \
  >"${WORKDIR}/build-clustered.log" 2>&1

if [[ ! -f "${UNCLUSTERED_ARTIFACT}" || ! -f "${CLUSTERED_ARTIFACT}" ]]; then
  echo "FAIL cottas-roworder-artifacts"
  cat "${WORKDIR}/build-unclustered.log" "${WORKDIR}/build-clustered.log"
  exit 1
fi
echo "PASS cottas-roworder-artifacts"

# Sidecars must exist next to the clustered artifact (eager import-time
# build), and must NOT be required to exist next to the unclustered one
# (today's default stays lazy -- only asserting the clustered path here).
SIDECAR_SUFFIXES=(.s.dict .s.presence .p.dict .p.presence .o.dict .o.presence .g.dict .g.presence .p.offsets .po.presence)
missing=0
for suf in "${SIDECAR_SUFFIXES[@]}"; do
  if [[ ! -f "${CLUSTERED_ARTIFACT}${suf}" ]]; then
    echo "  missing sidecar: ${CLUSTERED_ARTIFACT}${suf}"
    missing=1
  fi
done
if [[ "${missing}" -ne 0 ]]; then
  echo "FAIL cottas-roworder-sidecars-built"
  FAIL=1
else
  echo "PASS cottas-roworder-sidecars-built"
fi

run_query() {
  # run_query ARTIFACT QUERY_TEXT OUT_FILE
  FACTOIDAL_COTTAS_BRIDGE=/definitely/missing PYCOTTAS_PYTHON=/definitely/missing \
    "${BIN}" --data-cottas "$1" -e "$2" -o csv >"$3" 2>"${3}.err"
}

check_same() {
  # check_same NAME UNCLUSTERED_OUT CLUSTERED_OUT
  if ! diff -q <(sort "$2") <(sort "$3") >/dev/null; then
    echo "FAIL cottas-roworder-$1"
    echo "  --- unclustered ---"; cat "$2"
    echo "  --- clustered ---"; cat "$3"
    FAIL=1
  else
    echo "PASS cottas-roworder-$1"
  fi
}

# (a) named-graph SELECT
run_query "${UNCLUSTERED_ARTIFACT}" \
  "SELECT ?g ?s ?o WHERE { GRAPH ?g { ?s <https://example.org/name> ?o } }" \
  "${WORKDIR}/unclustered.named.csv"
run_query "${CLUSTERED_ARTIFACT}" \
  "SELECT ?g ?s ?o WHERE { GRAPH ?g { ?s <https://example.org/name> ?o } }" \
  "${WORKDIR}/clustered.named.csv"
check_same "named-graph-select" "${WORKDIR}/unclustered.named.csv" "${WORKDIR}/clustered.named.csv"

# (b) default-graph ASK
run_query "${UNCLUSTERED_ARTIFACT}" \
  "ASK { <https://example.org/default-subject> <https://example.org/status> \"default\" }" \
  "${WORKDIR}/unclustered.ask.csv"
run_query "${CLUSTERED_ARTIFACT}" \
  "ASK { <https://example.org/default-subject> <https://example.org/status> \"default\" }" \
  "${WORKDIR}/clustered.ask.csv"
check_same "default-graph-ask" "${WORKDIR}/unclustered.ask.csv" "${WORKDIR}/clustered.ask.csv"

# (c) COUNT(*) over the default graph -- correctness proof that
# clustering didn't drop/duplicate rows in the SPARQL-visible slice.
# (Only 1 quad is in the default graph in this fixture; { ?s ?p ?o }
# with no GRAPH clause queries the default graph only, per SPARQL 1.1
# dataset semantics -- this is not a full-corpus row count.)
run_query "${UNCLUSTERED_ARTIFACT}" \
  "SELECT (COUNT(*) AS ?n) WHERE { ?s ?p ?o }" \
  "${WORKDIR}/unclustered.count.csv"
run_query "${CLUSTERED_ARTIFACT}" \
  "SELECT (COUNT(*) AS ?n) WHERE { ?s ?p ?o }" \
  "${WORKDIR}/clustered.count.csv"
check_same "count-star" "${WORKDIR}/unclustered.count.csv" "${WORKDIR}/clustered.count.csv"

# Full-corpus row-count proof (all 5 quads, default + both named
# graphs) that CS clustering is a pure permutation: raw Parquet row
# count via DuckDB on both artifacts must equal the 5-quad input.
for pair in "unclustered:${UNCLUSTERED_ARTIFACT}" "clustered:${CLUSTERED_ARTIFACT}"; do
  tag="${pair%%:*}"; artifact="${pair#*:}"
  rowcount="$("${PYCOTTAS_PYTHON}" - "${artifact}" <<'PY'
import sys
import duckdb
print(duckdb.sql(f"SELECT COUNT(*) FROM read_parquet('{sys.argv[1]}')").fetchone()[0])
PY
)"
  if [[ "${rowcount}" != "5" ]]; then
    echo "FAIL cottas-roworder-full-row-count-${tag} (expected 5, got ${rowcount})"
    FAIL=1
  else
    echo "PASS cottas-roworder-full-row-count-${tag}"
  fi
done

# (d) GRAPH ?g GROUP BY count
run_query "${UNCLUSTERED_ARTIFACT}" \
  "SELECT ?g (COUNT(*) AS ?n) WHERE { GRAPH ?g { ?s ?p ?o } } GROUP BY ?g" \
  "${WORKDIR}/unclustered.gcount.csv"
run_query "${CLUSTERED_ARTIFACT}" \
  "SELECT ?g (COUNT(*) AS ?n) WHERE { GRAPH ?g { ?s ?p ?o } } GROUP BY ?g" \
  "${WORKDIR}/clustered.gcount.csv"
check_same "graph-groupby-count" "${WORKDIR}/unclustered.gcount.csv" "${WORKDIR}/clustered.gcount.csv"

exit "${FAIL}"
