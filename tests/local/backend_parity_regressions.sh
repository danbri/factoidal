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
  local plain_err="${WORKDIR}/${name}.plain.err"
  local cottas_err="${WORKDIR}/${name}.cottas.err"

  # Capture stdout (the user-visible answer) and stderr (traces +
  # diagnostics) separately. The COTTAS backend currently emits
  # `[bet7-trace]` / `[qof3-trace]` debug lines on stderr from the
  # cottas_ondisk_runtime / lazy-open patches; those legitimately
  # differ between the in-memory backend (silent) and COTTAS (chatty)
  # without indicating an answer divergence. Compare stdout only.
  "${BIN}" --data "${INPUT}" --query "${query}" >"${plain_out}" 2>"${plain_err}"
  "${BIN}" --data-cottas "${ARTIFACT_FILE}" --query "${query}" >"${cottas_out}" 2>"${cottas_err}"

  if ! cmp -s "${plain_out}" "${cottas_out}"; then
    echo "FAIL ${name}"
    echo "--- plain stdout ---"
    cat "${plain_out}"
    echo "--- cottas stdout ---"
    cat "${cottas_out}"
    echo "--- cottas stderr (trace lines, not compared) ---"
    cat "${cottas_err}"
    exit 1
  fi

  echo "PASS ${name}"
}

run_pair backend-default-ask "${ROOT}/tests/local/sparql/cottas_dataset_default_graph.rq"
run_pair backend-default-select "${ROOT}/tests/local/sparql/backend_default_select.rq"
run_pair backend-named-select "${ROOT}/tests/local/sparql/cottas_dataset_named_graph.rq"

