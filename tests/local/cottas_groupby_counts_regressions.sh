#!/usr/bin/env bash
# Regression: on-disk COTTAS GROUP BY ?g and COUNT(*) must return EXACT
# counts, not join-order-optimiser estimates. Guards the E1-found
# soundness bug (standing priority item; the Bet5/Aleph6 streaming
# count fast paths once consumed cottas_ondisk_estimate's
# candidate-rgs x avg approximation as the query result, reporting
# near-total row counts for every named graph).
#
# Builds a 4-graph fixture with known counts via DuckDB (Parquet V2 +
# DICTIONARY_SIZE_LIMIT 1 forces DLBA, the v1 SHOULD encoding our
# reader fully supports; plain pycottas output can hit the
# RLE_DICTIONARY multi-row-group reader gap tracked separately).
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
WORKDIR="$(mktemp -d)"
trap 'rm -rf "${WORKDIR}"' EXIT
BIN="${FACTOIDAL_BIN:-${ROOT}/formal/fstar/ocaml-output/factoidal}"
PYCOTTAS_PYTHON="${PYCOTTAS_PYTHON:-${ROOT}/_tmp.junk/pycottas-venv/bin/python}"

pass_count=0
fail_count=0
check () {
  local name="$1" expected="$2" actual="$3"
  if [[ "${actual}" == "${expected}" ]]; then
    echo "PASS ${name}"
    pass_count=$((pass_count + 1))
  else
    echo "FAIL ${name}: expected [${expected}] got [${actual}]"
    fail_count=$((fail_count + 1))
  fi
}

# Fixture: g1=500, g2=300, g3=7 named-graph quads + 11 default-graph.
python3 - "${WORKDIR}" <<'PY'
import sys
from pathlib import Path
w = Path(sys.argv[1])
with (w / "multi.nq").open("w") as f:
    for g, n in [("g1", 500), ("g2", 300), ("g3", 7)]:
        for i in range(n):
            f.write(f"<http://x.org/{g}/s{i}> <http://x.org/p{i%5}> \"v{i}\" <http://x.org/graph/{g}> .\n")
    for i in range(11):
        f.write(f"<http://x.org/d/s{i}> <http://x.org/p> \"d{i}\" .\n")
PY

"${PYCOTTAS_PYTHON}" - "${WORKDIR}" <<'PY'
import sys, re, pathlib, duckdb
w = pathlib.Path(sys.argv[1])
pat = re.compile(r'^(\S+)\s+(\S+)\s+(".*?"(?:\^\^\S+|@\S+)?|\S+)\s+(\S+)?\s*\.$')
rows = []
for line in (w / "multi.nq").read_text().splitlines():
    m = pat.match(line.strip())
    rows.append((m.group(1), m.group(2), m.group(3), m.group(4) or "DEFAULT"))
con = duckdb.connect()
con.execute("CREATE TABLE t (s VARCHAR, p VARCHAR, o VARCHAR, g VARCHAR)")
con.executemany("INSERT INTO t VALUES (?,?,?,?)", rows)
con.execute(f"COPY t TO '{w}/data.cottas' (FORMAT PARQUET, COMPRESSION ZSTD, DICTIONARY_SIZE_LIMIT 1, PARQUET_VERSION V2)")
PY

Q_GROUP='SELECT ?g (COUNT(*) AS ?n) WHERE { GRAPH ?g { ?s ?p ?o } } GROUP BY ?g ORDER BY DESC(?n)'
# issue #267: a bare BGP matches the DEFAULT GRAPH ONLY (11 rows here);
# the pre-#267 expectation of 818 encoded the union bug this suite now
# guards against. The union query preserves issue #21's exact-count
# coverage (818 = 11 default + 500 + 300 + 7 named).
Q_TOTAL='SELECT (COUNT(*) AS ?n) WHERE { ?s ?p ?o }'
Q_TOTAL_UNION='SELECT (COUNT(*) AS ?n) WHERE { { ?s ?p ?o } UNION { GRAPH ?g { ?s ?p ?o } } }'

group_out="$("${BIN}" query --data-cottas "${WORKDIR}/data.cottas" -e "${Q_GROUP}" 2>/dev/null \
  | grep -oE 'graph/g[0-9]> \| "[0-9]+"' | tr -d '|"' | tr -s ' ' | paste -sd, -)"
check "cottas-groupby-exact" "graph/g1> 500,graph/g2> 300,graph/g3> 7" "${group_out}"

total_out="$("${BIN}" query --data-cottas "${WORKDIR}/data.cottas" -e "${Q_TOTAL}" 2>/dev/null \
  | grep -oE '"[0-9]+"' | head -1 | tr -d '"')"
check "cottas-count-star-default-only" "11" "${total_out}"

total_union_out="$("${BIN}" query --data-cottas "${WORKDIR}/data.cottas" -e "${Q_TOTAL_UNION}" 2>/dev/null \
  | grep -oE '"[0-9]+"' | head -1 | tr -d '"')"
check "cottas-count-star-union-exact" "818" "${total_union_out}"

mem_total_out="$("${BIN}" query --data "${WORKDIR}/multi.nq" -e "${Q_TOTAL}" 2>/dev/null \
  | grep -oE '"[0-9]+"' | head -1 | tr -d '"')"
check "inmem-count-star-parity" "${total_out}" "${mem_total_out}"

# In-memory answers must agree (cross-backend parity on counts).
mem_out="$("${BIN}" query --data "${WORKDIR}/multi.nq" -e "${Q_GROUP}" 2>/dev/null \
  | grep -oE 'graph/g[0-9]> \| "[0-9]+"' | tr -d '|"' | tr -s ' ' | paste -sd, -)"
check "inmem-groupby-parity" "${group_out}" "${mem_out}"

echo "pass=${pass_count} fail=${fail_count}"
if [[ "${fail_count}" -ne 0 ]]; then
  exit 1
fi
