#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
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

CASES=(
  "syntax-sparql3/syn-bad-02.rq"
  "syntax-sparql3/syn-bad-03.rq"
  "syntax-sparql3/syn-bad-08.rq"
  "syntax-sparql3/syn-bad-09.rq"
  "syntax-sparql3/syn-bad-10.rq"
  "syntax-sparql3/syn-bad-11.rq"
  "syntax-sparql3/syn-bad-12.rq"
  "syntax-sparql3/syn-bad-13.rq"
  "syntax-sparql3/syn-bad-26.rq"
  "syntax-sparql3/syn-bad-filter-missing-parens.rq"
  "syntax-sparql3/syn-bad-lone-list.rq"
  "syntax-sparql3/syn-bad-bnode-dot.rq"
  "syntax-sparql4/syn-bad-34.rq"
  "syntax-sparql4/syn-bad-35.rq"
  "syntax-sparql4/syn-bad-GRAPH-breaks-BGP.rq"
  "syntax-sparql4/syn-bad-OPT-breaks-BGP.rq"
)

pass=0
fail=0

for rel in "${CASES[@]}"; do
  q="${JENA_ROOT}/${rel}"
  if [[ ! -f "${q}" ]]; then
    echo "SKIP missing ${rel}"
    continue
  fi
  if "${BIN}" --query "${q}" >/dev/null 2>&1; then
    echo "FAIL accepted ${rel}"
    fail=$((fail + 1))
  else
    echo "PASS rejected ${rel}"
    pass=$((pass + 1))
  fi
done

echo "pass=${pass} fail=${fail}"
if [[ ${fail} -ne 0 ]]; then
  exit 1
fi
