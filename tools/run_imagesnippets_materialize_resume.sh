#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
LOG_ROOT="${1:-/mnt/t/IS_Corpus_v2}"
LOG_FILE="${LOG_ROOT}/materialize-run.log"

mkdir -p "${LOG_ROOT}"

cd "${ROOT}"
echo "START $(date -Is)" > "${LOG_FILE}"

python3 -u tools/corpus_pipeline.py materialize-graph-hdt-corpus \
  --input examples/data/third_party/imagesnippets.nq \
  --partition-root /mnt/t/IS_Partition_v2 \
  --corpus-root /mnt/t/IS_Corpus_v2 \
  --dataset-name imagesnippets \
  --version v1 \
  --hdt-command rdf2hdt \
  >> "${LOG_FILE}" 2>&1
