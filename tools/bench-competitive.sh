#!/usr/bin/env bash
# Rerunnable entry point for the competitive RDF/SPARQL benchmark
# (factoidal vs Apache Jena vs pyoxigraph vs rdflib on identical
# in-tree data + identical SPARQL text).
#
# What this wrapper does that tools/bench_competitive.py doesn't:
#   1. Resolves/fetches Apache Jena (a real store's CLI tools --
#      arq, tdb2.tdbloader, tdb2.tdbquery), caching the binary
#      distribution so reruns don't re-download.
#   2. Activates the pycottas venv path the COTTAS-import row needs.
#   3. Tees everything to .claude-runs/ with a timestamp (anti-pattern
#      #19/#20).
#
# Usage:
#   tools/bench-competitive.sh                  # full run, both corpora
#   tools/bench-competitive.sh --skip-lifesci-all-load
#   tools/bench-competitive.sh --only-phase query
#   JENA_HOME=/path/to/apache-jena-5.2.0 tools/bench-competitive.sh
#
# Any extra args are forwarded verbatim to bench_competitive.py.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "${ROOT}"

RUN_LOG_DIR="${ROOT}/.claude-runs"
mkdir -p "${RUN_LOG_DIR}"
TS="$(date -u +%Y%m%dT%H%M%SZ)"
LOG_FILE="${RUN_LOG_DIR}/bench-competitive-${TS}.log"

JENA_VERSION="${JENA_VERSION:-5.2.0}"
JENA_CACHE_ROOT="${JENA_CACHE_ROOT:-${HOME}/.cache/factoidal-bench}"
JENA_HOME_DEFAULT="${JENA_CACHE_ROOT}/apache-jena-${JENA_VERSION}"

if [[ -z "${JENA_HOME:-}" ]]; then
  if [[ -x "${JENA_HOME_DEFAULT}/bin/arq" ]]; then
    JENA_HOME="${JENA_HOME_DEFAULT}"
    echo "[bench-competitive.sh] using cached Jena at ${JENA_HOME}" | tee -a "${LOG_FILE}"
  else
    echo "[bench-competitive.sh] fetching Apache Jena ${JENA_VERSION} from Maven Central (binary distribution, no build)" | tee -a "${LOG_FILE}"
    mkdir -p "${JENA_CACHE_ROOT}"
    TARBALL="${JENA_CACHE_ROOT}/apache-jena-${JENA_VERSION}.tar.gz"
    if [[ ! -f "${TARBALL}" ]]; then
      if ! curl -fsSL -o "${TARBALL}" \
        "https://repo1.maven.org/maven2/org/apache/jena/apache-jena/${JENA_VERSION}/apache-jena-${JENA_VERSION}.tar.gz"; then
        echo "[bench-competitive.sh] Jena download failed -- continuing without it (Jena rows will be SKIPPED, not fabricated)" | tee -a "${LOG_FILE}"
        rm -f "${TARBALL}"
      fi
    fi
    if [[ -f "${TARBALL}" ]]; then
      tar xzf "${TARBALL}" -C "${JENA_CACHE_ROOT}"
      JENA_HOME="${JENA_HOME_DEFAULT}"
    fi
  fi
fi

if [[ -n "${JENA_HOME:-}" && -x "${JENA_HOME}/bin/arq" ]]; then
  export PATH="${JENA_HOME}/bin:${PATH}"
  echo "[bench-competitive.sh] JENA_HOME=${JENA_HOME}" | tee -a "${LOG_FILE}"
  JENA_ARGS=(--jena-home "${JENA_HOME}")
else
  echo "[bench-competitive.sh] Jena unavailable -- bench_competitive.py will mark it SKIPPED, not fake a version" | tee -a "${LOG_FILE}"
  JENA_ARGS=()
fi

PYCOTTAS_VENV="${ROOT}/_tmp.junk/pycottas-venv"
if [[ -x "${PYCOTTAS_VENV}/bin/python" ]]; then
  echo "[bench-competitive.sh] pycottas venv found at ${PYCOTTAS_VENV} -- COTTAS-import row enabled" | tee -a "${LOG_FILE}"
else
  echo "[bench-competitive.sh] pycottas venv NOT found -- COTTAS-import LOAD row will be SKIPPED" | tee -a "${LOG_FILE}"
fi

echo "[bench-competitive.sh] python: pyoxigraph/rdflib availability is probed by bench_competitive.py itself" | tee -a "${LOG_FILE}"

echo "[bench-competitive.sh] starting bench_competitive.py, log: ${LOG_FILE}" | tee -a "${LOG_FILE}"
python3 "${ROOT}/tools/bench_competitive.py" "${JENA_ARGS[@]}" "$@" 2>&1 | tee -a "${LOG_FILE}"
STATUS="${PIPESTATUS[0]}"

echo "[bench-competitive.sh] exit=${STATUS}, log=${LOG_FILE}" | tee -a "${LOG_FILE}"
exit "${STATUS}"
