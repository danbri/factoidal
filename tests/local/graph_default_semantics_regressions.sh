#!/usr/bin/env bash
# Regression: SPARQL dataset semantics for GRAPH vs default-graph
# matching, with the default graph empty and non-empty, on BOTH the
# in-memory and COTTAS backends. A classic interop divergence area:
# per SPARQL 1.1 (RDF dataset semantics, no union-default option), a
# plain BGP matches ONLY the default graph — never named graphs — and
# GRAPH ?g matches ONLY named graphs. Engines that silently
# union-default (or leak named triples into the default) break
# cross-engine result parity.
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

# Fixture A: default graph EMPTY, two named graphs (3 + 2 quads).
cat > "${WORKDIR}/empty_default.nq" <<'EOF'
<http://x.org/a1> <http://x.org/p> "1" <http://x.org/g/one> .
<http://x.org/a2> <http://x.org/p> "2" <http://x.org/g/one> .
<http://x.org/a3> <http://x.org/p> "3" <http://x.org/g/one> .
<http://x.org/b1> <http://x.org/p> "4" <http://x.org/g/two> .
<http://x.org/b2> <http://x.org/p> "5" <http://x.org/g/two> .
EOF

# Fixture B: default graph NON-empty (4 triples) + same named graphs.
cat "${WORKDIR}/empty_default.nq" > "${WORKDIR}/mixed.nq"
cat >> "${WORKDIR}/mixed.nq" <<'EOF'
<http://x.org/d1> <http://x.org/p> "d1" .
<http://x.org/d2> <http://x.org/p> "d2" .
<http://x.org/d3> <http://x.org/p> "d3" .
<http://x.org/d4> <http://x.org/p> "d4" .
EOF

Q_DEFAULT='SELECT (COUNT(*) AS ?n) WHERE { ?s ?p ?o }'
Q_NAMED='SELECT (COUNT(*) AS ?n) WHERE { GRAPH ?g { ?s ?p ?o } }'
Q_ASK_DEFAULT='ASK { ?s ?p ?o }'
Q_ASK_NAMED='ASK { GRAPH ?g { ?s ?p ?o } }'

count_of () { grep -oE '"[0-9]+"' | head -1 | tr -d '"'; }
ask_of ()   { grep -oE '^(true|false)$' | head -1; }

run_backend_checks () {
  local label="$1" data_flag="$2" data_a="$3" data_b="$4"

  check "${label}-emptydefault-bgp-count" "0" \
    "$("${BIN}" query ${data_flag} "${data_a}" -e "${Q_DEFAULT}" 2>/dev/null | count_of)"
  check "${label}-emptydefault-graph-count" "5" \
    "$("${BIN}" query ${data_flag} "${data_a}" -e "${Q_NAMED}" 2>/dev/null | count_of)"
  check "${label}-emptydefault-bgp-ask" "false" \
    "$("${BIN}" query ${data_flag} "${data_a}" -e "${Q_ASK_DEFAULT}" 2>/dev/null | ask_of)"
  check "${label}-emptydefault-graph-ask" "true" \
    "$("${BIN}" query ${data_flag} "${data_a}" -e "${Q_ASK_NAMED}" 2>/dev/null | ask_of)"

  check "${label}-mixed-bgp-count" "4" \
    "$("${BIN}" query ${data_flag} "${data_b}" -e "${Q_DEFAULT}" 2>/dev/null | count_of)"
  check "${label}-mixed-graph-count" "5" \
    "$("${BIN}" query ${data_flag} "${data_b}" -e "${Q_NAMED}" 2>/dev/null | count_of)"
  check "${label}-mixed-bgp-ask" "true" \
    "$("${BIN}" query ${data_flag} "${data_b}" -e "${Q_ASK_DEFAULT}" 2>/dev/null | ask_of)"
}

# In-memory backend.
run_backend_checks "inmem" "--data" "${WORKDIR}/empty_default.nq" "${WORKDIR}/mixed.nq"

# COTTAS backend (Parquet V2 + forced DLBA, per
# cottas_groupby_counts_regressions.sh).
for nq in empty_default mixed; do
  "${PYCOTTAS_PYTHON}" - "${WORKDIR}" "${nq}" <<'PY'
import sys, re, pathlib, duckdb
w = pathlib.Path(sys.argv[1]); name = sys.argv[2]
pat = re.compile(r'^(\S+)\s+(\S+)\s+(".*?"(?:\^\^\S+|@\S+)?|\S+)\s+(\S+)?\s*\.$')
rows = []
for line in (w / f"{name}.nq").read_text().splitlines():
    m = pat.match(line.strip())
    rows.append((m.group(1), m.group(2), m.group(3), m.group(4) or "DEFAULT"))
con = duckdb.connect()
con.execute("CREATE TABLE t (s VARCHAR, p VARCHAR, o VARCHAR, g VARCHAR)")
con.executemany("INSERT INTO t VALUES (?,?,?,?)", rows)
con.execute(f"COPY t TO '{w}/{name}.cottas' (FORMAT PARQUET, COMPRESSION ZSTD, DICTIONARY_SIZE_LIMIT 0, PARQUET_VERSION V2)")
PY
done
# issue #267 landed 2026-07-04: the COTTAS backend now enforces the
# same dataset semantics as the in-memory path, so these are hard
# checks (they were KNOWN-FAIL while the fix was pending).
run_backend_checks "cottas" "--data-cottas" "${WORKDIR}/empty_default.cottas" "${WORKDIR}/mixed.cottas"

echo "pass=${pass_count} fail=${fail_count}"
if [[ "${fail_count}" -ne 0 ]]; then
  exit 1
fi
