#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
BIN="${ROOT}/formal/fstar/ocaml-output/factoidal"
TMPDIR="${TMPDIR:-/tmp}"
WORKDIR="$(mktemp -d "${TMPDIR}/factoidal-cottas-regression-XXXXXX")"
trap 'rm -rf "${WORKDIR}"' EXIT

INPUT="${ROOT}/tests/local/data/cottas_sample.nq"
CORPUS_ROOT="${WORKDIR}/CorpusCOTTA"
ARTIFACT_DIR="${CORPUS_ROOT}/sample-cottas/v1"
ARTIFACT_FILE="${ARTIFACT_DIR}/data.cottas"
PYCOTTAS_PYTHON="${PYCOTTAS_PYTHON:-${ROOT}/_tmp.junk/pycottas-venv/bin/python}"

"${PYCOTTAS_PYTHON}" "${ROOT}/tools/corpus_pipeline.py" materialize-nq-cottas-corpus \
  --input "${INPUT}" \
  --corpus-root "${CORPUS_ROOT}" \
  --dataset-name sample-cottas \
  --chunk-name sample-cottas \
  >/dev/null

if [[ ! -f "${ARTIFACT_FILE}" || ! -f "${ARTIFACT_DIR}/data.factbin" || ! -f "${ARTIFACT_DIR}/data.nq" || ! -f "${ARTIFACT_DIR}/summary.json" ]]; then
  echo "FAIL cottas-artifact-files"
  exit 1
fi

if ! "${PYCOTTAS_PYTHON}" - <<PY >/dev/null
import pycottas
assert pycottas.verify(r"${ARTIFACT_FILE}")
PY
then
  echo "FAIL cottas-upstream-verify"
  exit 1
fi

named_out="${WORKDIR}/named.out"
default_out="${WORKDIR}/default.out"
mv "${ARTIFACT_DIR}/data.nq" "${ARTIFACT_DIR}/data.nq.hidden"

FACTOIDAL_COTTAS_BRIDGE=/definitely/missing PYCOTTAS_PYTHON=/definitely/missing \
  "${BIN}" --data-cottas "${ARTIFACT_FILE}" --query "${ROOT}/tests/local/sparql/cottas_dataset_named_graph.rq" >"${named_out}" 2>&1
FACTOIDAL_COTTAS_BRIDGE=/definitely/missing PYCOTTAS_PYTHON=/definitely/missing \
  "${BIN}" --data-cottas "${ARTIFACT_FILE}" --query "${ROOT}/tests/local/sparql/cottas_dataset_default_graph.rq" >"${default_out}" 2>&1

if ! rg -q '<https://example.org/graph/people>' "${named_out}"; then
  echo "FAIL cottas-named-graph-query"
  cat "${named_out}"
  exit 1
fi

if ! rg -q '^true$' "${default_out}"; then
  echo "FAIL cottas-default-graph-query"
  cat "${default_out}"
  exit 1
fi

echo "PASS cottas-artifact-files"
echo "PASS cottas-upstream-verify"
echo "PASS cottas-named-graph-query"
echo "PASS cottas-default-graph-query"
