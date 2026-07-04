#!/usr/bin/env bash
# Corpus-driven cross-backend SPARQL parity: run every query in
# tests/parity/queries.json on the in-memory (--data) AND COTTAS
# (--data-cottas) backends and diff the results. Owner directive
# (2026-07-04): semantic compliance is claimed PER BACKEND; a fully
# compliant in-memory engine says nothing about the on-disk variant.
#
# Overrides:
#   FACTOIDAL_BIN     — binary under test (default: committed platform binary
#                       via the ocaml-output symlink)
#   PYCOTTAS_PYTHON   — python with duckdb, used to build .cottas artifacts
#                       AND to run the (stdlib-only) harness itself
#   PARITY_WORKDIR    — persistent cache dir for built .cottas artifacts
#                       (default: fresh temp dir, removed on exit)
#
# Exit: non-zero on any NEW divergence, expect failure, or backend error.
# KNOWN-DIVERGENT entries (manifest known_divergent, issue-referenced)
# are reported but do not fail the run.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
BIN="${FACTOIDAL_BIN:-${ROOT}/formal/fstar/ocaml-output/factoidal}"
PYCOTTAS_PYTHON="${PYCOTTAS_PYTHON:-${ROOT}/_tmp.junk/pycottas-venv/bin/python}"

if [[ ! -x "${BIN}" ]]; then
  echo "backend_parity_full: factoidal binary not found or not executable: ${BIN}" >&2
  exit 2
fi
if [[ ! -x "${PYCOTTAS_PYTHON}" ]]; then
  echo "backend_parity_full: pycottas venv python not found: ${PYCOTTAS_PYTHON}" >&2
  echo "(the session bootstrap hook provisions _tmp.junk/pycottas-venv)" >&2
  exit 2
fi

CLEANUP_DIR=""
if [[ -n "${PARITY_WORKDIR:-}" ]]; then
  WORKDIR="${PARITY_WORKDIR}"
  mkdir -p "${WORKDIR}"
else
  WORKDIR="$(mktemp -d "${TMPDIR:-/tmp}/factoidal-backend-parity-XXXXXX")"
  CLEANUP_DIR="${WORKDIR}"
fi
trap '[[ -n "${CLEANUP_DIR}" ]] && rm -rf "${CLEANUP_DIR}"' EXIT

exec "${PYCOTTAS_PYTHON}" "${ROOT}/tests/parity/run_backend_parity.py" \
  --manifest "${ROOT}/tests/parity/queries.json" \
  --bin "${BIN}" \
  --pycottas-python "${PYCOTTAS_PYTHON}" \
  --workdir "${WORKDIR}"
