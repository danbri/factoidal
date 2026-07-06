#!/usr/bin/env bash
# Regression pin for docs/designissues/2026-07-05-disk-backed-db-perf-review.md
# roadmap item 2's residual (Tsade2 Phase E, 2026-07-06): the cross-query
# per-row-group DICTIONARY cache (`RDF.CottasStore.PageCache.dict_page_cache`
# + the `dpcache_probe_dict_in_row_group_global_from_table` storage cell in
# experimental_ocaml_glue/cottas_pagecache_global_runtime.sh) must not
# change any query answer: output with the cache enabled (default) must be
# BYTE-IDENTICAL to output with FACTOIDAL_DISABLE_DICT_GLOBAL_CACHE=1
# (which bypasses the cache entirely and takes the pre-change per-query
# decode path). Same kill-switch-diff pattern as
# streamable_fastpath_regressions.sh / FACTOIDAL_DISABLE_STREAM_FASTPATH.
#
# Builds one CS-clustered + eager-sidecar COTTAS artifact from the shared
# 5-quad fixture (tests/local/data/cottas_sample.nq) and runs each query
# TWICE per mode in one process-per-run CLI invocation. The planner's
# dictionary probes fire on every bound-s/p/o/g query, so even this small
# store exercises the populate -> hit path; the multi-row-group decode
# equivalences are pinned separately (and more sharply) in
# tests/unit/parquet_rle_dictionary_multi_row_group.ml section 8.
set -uo pipefail

ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
BIN="${ROOT}/formal/fstar/ocaml-output/factoidal"
TMPDIR="${TMPDIR:-/tmp}"
WORKDIR="$(mktemp -d "${TMPDIR}/factoidal-dictcache-parity-XXXXXX")"
trap 'rm -rf "${WORKDIR}"' EXIT

INPUT="${ROOT}/tests/local/data/cottas_sample.nq"
PYCOTTAS_PYTHON="${PYCOTTAS_PYTHON:-${ROOT}/_tmp.junk/pycottas-venv/bin/python}"
ARTIFACT_ROOT="${WORKDIR}/store"
ARTIFACT="${ARTIFACT_ROOT}/sample-cottas/v1/data.cottas"

FAIL=0

"${PYCOTTAS_PYTHON}" "${ROOT}/tools/corpus_pipeline.py" materialize-nq-cottas-corpus \
  --input "${INPUT}" \
  --corpus-root "${ARTIFACT_ROOT}" \
  --dataset-name sample-cottas \
  --chunk-name sample-cottas \
  --row-order cs \
  --build-sidecars \
  >"${WORKDIR}/build.log" 2>&1

if [[ ! -f "${ARTIFACT}" ]]; then
  echo "FAIL dictcache-parity-artifact"
  cat "${WORKDIR}/build.log"
  exit 1
fi
echo "PASS dictcache-parity-artifact"

run_query() {
  # run_query MODE ARTIFACT QUERY_TEXT OUT_FILE
  # MODE: on (cache enabled, default) | off (kill switch set)
  local mode="$1" artifact="$2" query="$3" out="$4"
  local envs=(FACTOIDAL_COTTAS_BRIDGE=/definitely/missing PYCOTTAS_PYTHON=/definitely/missing)
  if [[ "${mode}" == "off" ]]; then
    envs+=(FACTOIDAL_DISABLE_DICT_GLOBAL_CACHE=1)
  fi
  env "${envs[@]}" "${BIN}" --data-cottas "${artifact}" -e "${query}" -o csv \
    >"${out}" 2>"${out}.err"
}

check_pair() {
  # check_pair NAME QUERY_TEXT — run under both modes, diff bytes.
  local name="$1" query="$2"
  run_query on  "${ARTIFACT}" "${query}" "${WORKDIR}/${name}.on.csv"
  run_query off "${ARTIFACT}" "${query}" "${WORKDIR}/${name}.off.csv"
  if ! cmp -s "${WORKDIR}/${name}.on.csv" "${WORKDIR}/${name}.off.csv"; then
    echo "FAIL dictcache-parity-${name}"
    echo "  --- cache on ---";  cat "${WORKDIR}/${name}.on.csv"
    echo "  --- cache off ---"; cat "${WORKDIR}/${name}.off.csv"
    FAIL=1
  else
    echo "PASS dictcache-parity-${name}"
  fi
}

# Bound predicate (planner populates the p-column dict): the shape the
# cache accelerates on real corpora.
check_pair "bound-predicate" \
  "SELECT ?g ?s ?o WHERE { GRAPH ?g { ?s <https://example.org/name> ?o } }"

# Bound subject + predicate + object (ASK; planner intersects candidate
# sets from multiple bound columns, all through the dict probes).
check_pair "ask-fully-bound" \
  "ASK { <https://example.org/default-subject> <https://example.org/status> \"default\" }"

# No bound term (planner takes the all_rgs path; dict cache must not
# perturb the full-walk answer).
check_pair "count-star" \
  "SELECT (COUNT(*) AS ?n) WHERE { ?s ?p ?o }"

# Bound graph via GRAPH ?g GROUP BY (graph-column dict probes).
check_pair "graph-groupby" \
  "SELECT ?g (COUNT(*) AS ?n) WHERE { GRAPH ?g { ?s ?p ?o } } GROUP BY ?g"

# Bound predicate that does NOT exist in the store: with the cache on,
# the planner prunes every row group from the (cached) dictionaries; the
# answer must still be the same empty result as the uncached path.
check_pair "absent-predicate" \
  "SELECT ?s ?o WHERE { ?s <https://example.org/no-such-predicate> ?o }"

if [[ "${FAIL}" -ne 0 ]]; then
  echo "dict_global_cache_parity: FAIL"
  exit 1
fi
echo "dict_global_cache_parity: 6 checks, 6 pass, 0 fail"
