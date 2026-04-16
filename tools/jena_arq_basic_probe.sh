#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
BIN="${ROOT}/formal/fstar/ocaml-output/factoidal"
BASIC_ROOT="${1:-/tmp/jena/jena-arq/testing/DAWG-Final/basic}"
TMPDIR="${TMPDIR:-/tmp}"
LIMIT="${LIMIT:-0}"

if [[ ! -x "${BIN}" ]]; then
  echo "factoidal binary not found at ${BIN}" >&2
  exit 1
fi

if [[ ! -d "${BASIC_ROOT}" ]]; then
  echo "Jena ARQ basic root not found at ${BASIC_ROOT}" >&2
  exit 1
fi

manifest_rows() {
  python3 - "$BASIC_ROOT/manifest.ttl" <<'PY'
import sys
from pathlib import Path
from rdflib import Graph, Namespace
from rdflib.namespace import RDF

manifest = Path(sys.argv[1])
g = Graph()
g.parse(manifest)
MF = Namespace("http://www.w3.org/2001/sw/DataAccess/tests/test-manifest#")
QT = Namespace("http://www.w3.org/2001/sw/DataAccess/tests/test-query#")

rows = []
for test in sorted(g.subjects(RDF.type, MF.QueryEvaluationTest), key=lambda t: str(t)):
    action = g.value(test, MF.action)
    query = g.value(action, QT.query)
    data = g.value(action, QT.data)
    result = g.value(test, MF.result)
    if query and data and result and str(result).endswith(".srx"):
        rows.append((Path(str(query)).name, Path(str(data)).name, Path(str(result)).name))

for row in rows:
    print("\t".join(row))
PY
}

expected_count() {
  local result_file="$1"
  grep -c '<result>' "${result_file}" || true
}

actual_count() {
  local output_file="$1"
  if rg -q '^\(no results\)$' "${output_file}"; then
    printf '0\n'
  else
    sed -n 's/^\([0-9][0-9]*\) result(s)$/\1/p' "${output_file}" | tail -n 1
  fi
}

pass=0
fail=0
seen=0

while IFS=$'\t' read -r query_file data_file result_file; do
  [[ -n "${query_file}" ]] || continue
  seen=$((seen + 1))
  if [[ "${LIMIT}" -gt 0 && "${seen}" -gt "${LIMIT}" ]]; then
    break
  fi

  query_path="${BASIC_ROOT}/${query_file}"
  data_path="${BASIC_ROOT}/${data_file}"
  result_path="${BASIC_ROOT}/${result_file}"
  name="${query_file%.rq}"

  output_file="${TMPDIR}/factoidal_jena_basic_${name}.out"
  err_file="${TMPDIR}/factoidal_jena_basic_${name}.err"
  expected="$(expected_count "${result_path}")"

  if "${BIN}" --data "${data_path}" --query "${query_path}" >"${output_file}" 2>"${err_file}"; then
    actual="$(actual_count "${output_file}")"
    if [[ "${actual}" == "${expected}" ]]; then
      echo "PASS ${name} rows=${actual}"
      pass=$((pass + 1))
    else
      echo "FAIL ${name} expected_rows=${expected} actual_rows=${actual:-unknown}"
      sed -n '1,20p' "${query_path}"
      sed -n '1,20p' "${err_file}"
      fail=$((fail + 1))
    fi
  else
    echo "FAIL ${name} execution"
    sed -n '1,20p' "${query_path}"
    sed -n '1,40p' "${err_file}"
    fail=$((fail + 1))
  fi
done < <(manifest_rows)

echo "pass=${pass} fail=${fail}"

if [[ "${fail}" -ne 0 ]]; then
  exit 1
fi
