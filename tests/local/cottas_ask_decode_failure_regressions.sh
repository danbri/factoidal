#!/usr/bin/env bash
# Regression for issue #269: ASK must not answer `false` when a COTTAS
# on-disk column fails to decode. A bound term / row-group whose column
# can't be decoded (e.g. an RLE_DICTIONARY page the F*-verified reader
# doesn't support) is silently treated as "contributes zero rows" by the
# row-group walkers (`walk_row_groups_search` et al., by design — sound
# for callers that only consume the rows they COULD read). ASK reads
# "zero rows matched" as the query answer `false`; before the fix that
# conflated "genuinely no match" with "couldn't tell," producing a wrong
# answer with a clean exit 0 instead of a diagnostic.
#
# Fixture: a COTTAS artifact with 3 default-graph triples sharing one
# predicate (forces the predicate column into a single-distinct-value
# dictionary page under DICTIONARY_SIZE_LIMIT 1) plus 1 triple in a named
# graph (so the graph-name dictionary itself has >1 distinct value and
# builds cleanly at open time — isolating the decode failure to the
# predicate column's row-group walk, not the open()-time eager graph
# load). `ASK { ?s ?p ?o }` (default-graph BGP) has a true answer (the 3
# default triples exist) but the pre-fix binary silently answers `false`.
#
# Post-fix expected behaviour: ASK reports a query-evaluation error
# (non-zero exit, diagnostic on stderr) rather than `false`.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
WORKDIR="$(mktemp -d)"
trap 'rm -rf "${WORKDIR}"' EXIT
BIN="${FACTOIDAL_BIN:-${ROOT}/formal/fstar/ocaml-output/factoidal}"
PYCOTTAS_PYTHON="${PYCOTTAS_PYTHON:-${ROOT}/_tmp.junk/pycottas-venv/bin/python}"

if [[ ! -x "${BIN}" ]]; then
  echo "cottas_ask_decode_failure_regressions: factoidal binary not found or not executable: ${BIN}" >&2
  exit 2
fi
if [[ ! -x "${PYCOTTAS_PYTHON}" ]]; then
  echo "cottas_ask_decode_failure_regressions: pycottas venv python not found: ${PYCOTTAS_PYTHON}" >&2
  echo "(the session bootstrap hook provisions _tmp.junk/pycottas-venv)" >&2
  exit 2
fi

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

cat > "${WORKDIR}/undecodable.nq" <<'EOF'
<http://x.org/a1> <http://x.org/samePred> "1" .
<http://x.org/a2> <http://x.org/samePred> "2" .
<http://x.org/a3> <http://x.org/samePred> "3" .
<http://x.org/a4> <http://x.org/samePred> "4" <http://x.org/g1> .
EOF

"${PYCOTTAS_PYTHON}" - "${WORKDIR}" <<'PY'
import sys, re, pathlib, duckdb
w = pathlib.Path(sys.argv[1])
pat = re.compile(r'^(\S+)\s+(\S+)\s+(".*?"(?:\^\^\S+|@\S+)?|\S+)\s+(\S+)?\s*\.$')
rows = []
for line in (w / "undecodable.nq").read_text().splitlines():
    m = pat.match(line.strip())
    rows.append((m.group(1), m.group(2), m.group(3), m.group(4) or "DEFAULT"))
con = duckdb.connect()
con.execute("CREATE TABLE t (s VARCHAR, p VARCHAR, o VARCHAR, g VARCHAR)")
con.executemany("INSERT INTO t VALUES (?,?,?,?)", rows)
# DICTIONARY_SIZE_LIMIT 1: low-cardinality columns (the single-valued
# predicate here) stay dictionary-encoded (RLE_DICTIONARY) even at this
# tiny row count; see docs/designissues/2026-07-04-backend-parity-harness.md
# ("What the first run found", item 3) for the corpus-scale discovery.
con.execute(f"COPY t TO '{w}/undecodable.cottas' (FORMAT PARQUET, COMPRESSION ZSTD, DICTIONARY_SIZE_LIMIT 1, PARQUET_VERSION V2)")
PY

ARTIFACT="${WORKDIR}/undecodable.cottas"

# Sanity: the artifact actually reproduces an undecodable column via this
# reader (if this ever stops reproducing — e.g. the RLE_DICTIONARY
# decoder gains the missing bit-width-0 case tracked under #22 — the
# `false`/error checks below become vacuous, not wrong; SKIP loudly
# instead of silently passing on a fixture that no longer exercises the
# bug).
SELECT_RC=0
select_stdout="$("${BIN}" query --data-cottas "${ARTIFACT}" -e 'SELECT * WHERE { ?s ?p ?o }' 2>/dev/null)" || SELECT_RC=$?
if [[ "${select_stdout}" != *"(no results)"* ]]; then
  echo "SKIP cottas-ask-decode-failure (fixture no longer reproduces the undecodable-column shape; SELECT rc=${SELECT_RC} returned: ${select_stdout})"
  exit 0
fi

ASK_RC=0
ask_stdout="$("${BIN}" query --data-cottas "${ARTIFACT}" -e 'ASK { ?s ?p ?o }' 2>/dev/null)" || ASK_RC=$?

check "ask-default-graph-not-false" "1" "$([[ "${ask_stdout}" == "false" ]] && echo 0 || echo 1)"
check "ask-default-graph-nonzero-exit" "1" "$([[ ${ASK_RC} -ne 0 ]] && echo 1 || echo 0)"

echo "pass=${pass_count} fail=${fail_count}"
if [[ "${fail_count}" -ne 0 ]]; then
  exit 1
fi
