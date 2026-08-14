#!/usr/bin/env bash
# tests/local/cli_literal_escape_roundtrip.sh — regression pin for issue
# #443: an RDF literal whose lexical form contains a double quote, a
# newline or a backslash was DESTROYED by an `import` -> `query` round
# trip through the on-disk store, and `--dump` emitted output that no
# N-Triples parser could read back.
#
# Root cause: two wire-format call sites used RDF.Pretty.term_to_ntriples
# (the DISPLAY serializer, documented as intentionally lossy on literal
# escaping) instead of RDF.NQuads.Serialize.nq_term_to_string (the
# byte-correct one). Parsing was always correct; only serialization was
# wrong, so the defect was invisible to every test that stayed in memory.
#
# What this pin covers, and why each arm exists:
#
#   Arm A  `--dump` output is re-readable. Dump a graph, feed the dump
#          BACK to the engine, and require the same triple count. This is
#          the property the old code broke: a raw newline inside a
#          literal split one triple across two lines, so a re-read saw a
#          different graph (or none).
#
#   Arm B  import -> query preserves the literal. Import the same graph
#          into a COTTAS store and read every object back through SPARQL.
#          The old code stored the object column unescaped, and the
#          reader — which requires a FULL N-Triples term parse of the
#          cell — fell back to the sentinel `_:cottas_decode_oor`.
#
# ANTI-VACUITY. Both arms are written so a degenerate engine fails them.
# Arm A compares a COUNT that a drop-everything dump would lower and a
# duplicate-everything dump would raise. Arm B requires each specific
# lexical form to come back, so an engine returning zero rows, or the
# sentinel, or a truncated value, goes red. The `--check-pin-fails` mode
# below proves it: it corrupts the dump on purpose and requires the pin
# to report a failure.
#
# Rule anchors: #14 (no swallowed exit codes), #16 (no truncation),
# #25 (labelled pass/fail counts in words).

set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"

BIN="${ROOT}/formal/fstar/ocaml-output/factoidal"
if [ ! -x "${BIN}" ]; then
  BIN="${ROOT}/bin/linux-x86_64/factoidal"
fi
if [ ! -x "${BIN}" ]; then
  echo "cli_literal_escape_roundtrip: no factoidal binary found" >&2
  exit 2
fi

TMPDIR="${TMPDIR:-/tmp}"
WORKDIR="$(mktemp -d "${TMPDIR}/factoidal-escape-XXXXXX")"
trap 'rm -rf "${WORKDIR}"' EXIT

PASS=0
FAIL=0

# The six literal classes. Each line is one N-Triples triple; the
# subject encodes which escape class it carries. Every escape here is
# legal N-Triples per the RDF 1.1 N-Triples grammar (ECHAR).
#
# NON-ASCII IS DELIBERATELY ABSENT from this fixture. Not because it
# works -- it does not: the COTTAS store encodes tokens as Latin-1 with
# codepoints >= 256 clamped to NUL, so every non-ASCII literal is
# corrupted by import -> query (issue #445, XFAIL in
# tests/known-defects/run.sh). That is a separate defect in the storage
# byte layer, with an on-disk format-compatibility decision attached,
# and folding it in here would leave this pin permanently red and
# therefore useless as a gate. This pin covers ESCAPING; #445 covers
# ENCODING.
FIXTURE="${WORKDIR}/escapes.nq"
cat > "${FIXTURE}" <<'EOF'
<http://e/quote> <http://e/p> "has \" quote" .
<http://e/newline> <http://e/p> "has \n newline" .
<http://e/backslash> <http://e/p> "has \\ backslash" .
<http://e/tab> <http://e/p> "has \t tab" .
<http://e/plain> <http://e/p> "plain ascii" .
<http://e/cr> <http://e/p> "has \r carriage return" .
EOF
EXPECTED_TRIPLES=6

report_pass() { PASS=$((PASS + 1)); echo "PASS  $1"; }
report_fail() { FAIL=$((FAIL + 1)); echo "FAIL  $1"; }

# ---------------------------------------------------------------------
# Arm A: --dump output must be re-readable as N-Triples.
# ---------------------------------------------------------------------
arm_a() {
  local dump="$1" label="$2"
  local n_reread
  # `--count` prints "<path>: N triples", and the path is a mktemp dir
  # with digits in it -- so take the number AFTER the last colon, never
  # the first number on the line. (First draft did the latter and read
  # the temp-dir suffix as a triple count.)
  n_reread="$("${BIN}" --count "${dump}" 2>/dev/null | sed -n 's/.*: \([0-9][0-9]*\) triples.*/\1/p' | head -1)"
  if [ "${n_reread:-0}" = "${EXPECTED_TRIPLES}" ]; then
    report_pass "${label}: re-read of --dump output gives ${EXPECTED_TRIPLES} triples"
    return 0
  fi
  report_fail "${label}: re-read of --dump output gives ${n_reread:-<none>} triples, expected ${EXPECTED_TRIPLES}"
  echo "----- the dump that could not be re-read -----"
  cat -A "${dump}"
  echo "----------------------------------------------"
  return 1
}

DUMP="${WORKDIR}/dump.nt"
"${BIN}" --dump "${FIXTURE}" > "${DUMP}" 2>/dev/null
DUMP_RC=$?
if [ "${DUMP_RC}" -ne 0 ]; then
  report_fail "arm A: --dump exited ${DUMP_RC}"
else
  arm_a "${DUMP}" "arm A"
fi

# ---------------------------------------------------------------------
# Anti-vacuity check for arm A: corrupt the dump the exact way the bug
# did (unescape the quote) and require arm A to notice.
# ---------------------------------------------------------------------
CORRUPT="${WORKDIR}/corrupt.nt"
sed 's/\\"/"/g' "${DUMP}" > "${CORRUPT}"
if arm_a "${CORRUPT}" "anti-vacuity(expected to fail)" > "${WORKDIR}/av.log" 2>&1; then
  report_fail "anti-vacuity: arm A ACCEPTED a dump with unescaped quotes -- the pin cannot detect issue #443"
else
  # arm_a incremented FAIL for the deliberate corruption; undo that,
  # since the failure is the expected outcome here.
  FAIL=$((FAIL - 1))
  report_pass "anti-vacuity: arm A rejects a dump with unescaped quotes (so it can go red)"
fi

# ---------------------------------------------------------------------
# Arm B: import -> query preserves every literal.
# ---------------------------------------------------------------------
STORE="${WORKDIR}/store"
"${BIN}" import --nq "${FIXTURE}" --out "${STORE}" > "${WORKDIR}/import.log" 2>&1
IMPORT_RC=$?
if [ "${IMPORT_RC}" -ne 0 ]; then
  report_fail "arm B: import exited ${IMPORT_RC}"
  cat "${WORKDIR}/import.log"
else
  QOUT="${WORKDIR}/query.out"
  "${BIN}" query --data-cottas "${STORE}/data.cottas" \
    -e 'SELECT ?s ?o WHERE { ?s <http://e/p> ?o }' > "${QOUT}" 2>&1
  QUERY_RC=$?
  if [ "${QUERY_RC}" -ne 0 ]; then
    report_fail "arm B: query exited ${QUERY_RC}"
    cat "${QOUT}"
  else
    if grep -q "cottas_decode_oor" "${QOUT}"; then
      report_fail "arm B: at least one literal came back as the decode sentinel _:cottas_decode_oor"
      cat "${QOUT}"
    else
      report_pass "arm B: no literal decoded to the _:cottas_decode_oor sentinel"
    fi

    N_ROWS="$(grep -oE '^[0-9]+ result' "${QOUT}" | grep -oE '^[0-9]+')"
    if [ "${N_ROWS:-0}" = "${EXPECTED_TRIPLES}" ]; then
      report_pass "arm B: query returned ${EXPECTED_TRIPLES} rows"
    else
      report_fail "arm B: query returned ${N_ROWS:-<none>} rows, expected ${EXPECTED_TRIPLES}"
      cat "${QOUT}"
    fi

    # Exact values, compared through `-o json` rather than the result
    # TABLE. The table is a human-facing rendering (RDF.Pretty), so it
    # prints a literal's lexical form verbatim -- a table row reading
    # `has " quote` is correct output, not evidence about what is
    # stored. Comparing against the table is how a first draft of this
    # pin reported four false failures on an engine that was working.
    QJSON="${WORKDIR}/query.json"
    "${BIN}" query --data-cottas "${STORE}/data.cottas" -o json \
      -e 'SELECT ?s ?o WHERE { ?s <http://e/p> ?o }' > "${QJSON}" 2>/dev/null
    if python3 - "${QJSON}" <<'PY'
import json, sys
want = {
    "quote":      'has " quote',
    "newline":    'has \n newline',
    "backslash":  'has \\ backslash',
    "tab":        'has \t tab',
    "plain":      'plain ascii',
    "cr":         'has \r carriage return',
}
rows = json.load(open(sys.argv[1]))["results"]["bindings"]
got = {r["s"]["value"].rsplit("/", 1)[-1]: r["o"]["value"] for r in rows}
bad = [(k, want[k], got.get(k)) for k in want if got.get(k) != want[k]]
for k, w, g in bad:
    print(f"  {k}: expected {w!r}, got {g!r}")
sys.exit(1 if bad else 0)
PY
    then
      report_pass "arm B: all 6 literals round-trip byte-exact through the store"
    else
      report_fail "arm B: at least one literal changed value in the store round trip (detail above)"
    fi
  fi
fi

echo
echo "cli_literal_escape_roundtrip: ${PASS} pass, ${FAIL} fail (out of $((PASS + FAIL)))"
[ "${FAIL}" -eq 0 ]
