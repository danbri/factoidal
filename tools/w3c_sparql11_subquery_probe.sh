#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
BIN="${ROOT}/formal/fstar/ocaml-output/factoidal"
SUITE_ROOT="${1:-${ROOT}/tests/w3c/sparql/sparql11/subquery}"
TMPDIR="${TMPDIR:-/tmp}"
LIMIT="${LIMIT:-0}"

if [[ ! -x "${BIN}" ]]; then
  echo "factoidal binary not found at ${BIN}" >&2
  exit 1
fi

if [[ ! -d "${SUITE_ROOT}" ]]; then
  echo "SPARQL 1.1 subquery root not found at ${SUITE_ROOT}" >&2
  exit 1
fi

manifest_rows() {
  python3 - "$SUITE_ROOT/manifest.ttl" <<'PY'
import sys
from pathlib import Path
from rdflib import Graph, Namespace
from rdflib.namespace import RDF

manifest = Path(sys.argv[1])
g = Graph()
g.parse(manifest)
MF = Namespace("http://www.w3.org/2001/sw/DataAccess/tests/test-manifest#")
QT = Namespace("http://www.w3.org/2001/sw/DataAccess/tests/test-query#")
DAWGT = Namespace("http://www.w3.org/2001/sw/DataAccess/tests/test-dawg#")

rows = []
for test in sorted(g.subjects(RDF.type, MF.QueryEvaluationTest), key=lambda t: str(t)):
    approval = g.value(test, DAWGT.approval)
    if approval is not None and str(approval).endswith("Withdrawn"):
        continue
    name = g.value(test, MF.name)
    action = g.value(test, MF.action)
    if action is None:
        continue
    query = g.value(action, QT.query)
    data = g.value(action, QT.data)
    result = g.value(test, MF.result)
    graph_data = [Path(str(o)).name for o in g.objects(action, QT.graphData)]
    if query and result and str(result).endswith(".srx"):
        rows.append((
            str(name) if name else Path(str(query)).stem,
            Path(str(query)).name,
            Path(str(data)).name if data else "-",
            Path(str(result)).name,
            ",".join(graph_data) if graph_data else "-",
        ))

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

file_uri() {
  python3 - "$1" <<'PY'
import sys
from pathlib import Path
print(Path(sys.argv[1]).resolve().as_uri())
PY
}

pass=0
fail=0
seen=0

while IFS=$'\t' read -r test_name query_file data_file result_file graph_files; do
  [[ -n "${query_file}" ]] || continue
  seen=$((seen + 1))
  if [[ "${LIMIT}" -gt 0 && "${seen}" -gt "${LIMIT}" ]]; then
    break
  fi

  query_path="${SUITE_ROOT}/${query_file}"
  result_path="${SUITE_ROOT}/${result_file}"
  output_file="${TMPDIR}/factoidal_w3c_subquery_${query_file%.rq}.out"
  err_file="${TMPDIR}/factoidal_w3c_subquery_${query_file%.rq}.err"
  expected="$(expected_count "${result_path}")"

  args=(--query "${query_path}")
  if [[ "${data_file}" != "-" ]]; then
    args+=(--data "${SUITE_ROOT}/${data_file}")
  fi

  if [[ "${graph_files}" != "-" ]]; then
    IFS=',' read -r -a named_graphs <<< "${graph_files}"
    for graph_file in "${named_graphs[@]}"; do
      [[ -n "${graph_file}" ]] || continue
      abs_graph="${SUITE_ROOT}/${graph_file}"
      iri="$(file_uri "${abs_graph}")"
      args+=(--named "${iri}=${abs_graph}")
    done
  fi

  if "${BIN}" "${args[@]}" >"${output_file}" 2>"${err_file}"; then
    actual="$(actual_count "${output_file}")"
    if [[ "${actual}" == "${expected}" ]]; then
      echo "PASS ${test_name} rows=${actual}"
      pass=$((pass + 1))
    else
      echo "FAIL ${test_name} expected_rows=${expected} actual_rows=${actual:-unknown}"
      sed -n '1,30p' "${query_path}"
      sed -n '1,60p' "${err_file}"
      fail=$((fail + 1))
    fi
  else
    echo "FAIL ${test_name} execution"
    sed -n '1,30p' "${query_path}"
    sed -n '1,60p' "${err_file}"
    fail=$((fail + 1))
  fi
done < <(manifest_rows)

echo "pass=${pass} fail=${fail}"

if [[ "${fail}" -ne 0 ]]; then
  exit 1
fi
