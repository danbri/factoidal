#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
BIN="${ROOT}/formal/fstar/ocaml-output/factoidal"
JENA_ROOT="${1:-/tmp/jena/jena-arq/testing/DAWG-Final}"

if [[ ! -x "${BIN}" ]]; then
  echo "factoidal binary not found at ${BIN}" >&2
  exit 1
fi

if [[ ! -d "${JENA_ROOT}" ]]; then
  echo "Jena ARQ test root not found at ${JENA_ROOT}" >&2
  exit 1
fi

probe_suite() {
  local suite="$1"
  local dir="${JENA_ROOT}/${suite}"
  local pos=0
  local pos_pass=0
  local pos_fail=0
  local neg=0
  local neg_pass=0
  local neg_fail=0

  if [[ ! -d "${dir}" ]]; then
    echo "suite=${suite} missing"
    return 0
  fi

  while IFS= read -r -d '' q; do
    local base
    base="$(basename "${q}")"
    if [[ "${base}" == syn-bad-* ]] || [[ "${base}" == *-bad-* ]] || [[ "${base}" == *-bad.rq ]]; then
      neg=$((neg + 1))
      if "${BIN}" --query "${q}" >/dev/null 2>&1; then
        neg_fail=$((neg_fail + 1))
        echo "NEG_FAIL ${suite} ${base}"
      else
        neg_pass=$((neg_pass + 1))
      fi
    else
      pos=$((pos + 1))
      if "${BIN}" --query "${q}" >/dev/null 2>&1; then
        pos_pass=$((pos_pass + 1))
      else
        pos_fail=$((pos_fail + 1))
        echo "POS_FAIL ${suite} ${base}"
      fi
    fi
  done < <(find "${dir}" -maxdepth 1 -type f -name '*.rq' -print0 | sort -z)

  echo "suite=${suite} pos=${pos_pass}/${pos} neg=${neg_pass}/${neg} pos_fail=${pos_fail} neg_fail=${neg_fail}"
}

probe_suite "syntax-sparql3"
probe_suite "syntax-sparql4"
probe_suite "syntax-sparql5"
