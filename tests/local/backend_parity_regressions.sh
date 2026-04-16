#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
BIN="${ROOT}/formal/fstar/ocaml-output/factoidal"
TMPDIR="${TMPDIR:-/tmp}"
WORKDIR="$(mktemp -d "${TMPDIR}/factoidal-backend-parity-XXXXXX")"
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

mv "${ARTIFACT_DIR}/data.nq" "${ARTIFACT_DIR}/data.nq.hidden"

run_pair() {
  local name="$1"
  local query="$2"
  local plain_out="${WORKDIR}/${name}.plain.out"
  local cottas_out="${WORKDIR}/${name}.cottas.out"

  "${BIN}" --data "${INPUT}" --query "${query}" >"${plain_out}" 2>&1
  "${BIN}" --data-cottas "${ARTIFACT_FILE}" --query "${query}" >"${cottas_out}" 2>&1

  if ! cmp -s "${plain_out}" "${cottas_out}"; then
    echo "FAIL ${name}"
    echo "--- plain ---"
    cat "${plain_out}"
    echo "--- cottas ---"
    cat "${cottas_out}"
    exit 1
  fi

  echo "PASS ${name}"
}

run_pair backend-default-ask "${ROOT}/tests/local/sparql/cottas_dataset_default_graph.rq"
run_pair backend-default-select "${ROOT}/tests/local/sparql/backend_default_select.rq"
run_pair backend-named-select "${ROOT}/tests/local/sparql/cottas_dataset_named_graph.rq"

