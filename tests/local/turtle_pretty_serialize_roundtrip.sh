#!/usr/bin/env bash
# tests/local/turtle_pretty_serialize_roundtrip.sh — CLI pin for issue
# #448 assurance triage, module 3 (RDF.Turtle.Serialize.fst).
#
# What this pin covers, and why it is SEPARATE from
# tests/local/cli_literal_escape_roundtrip.sh: that pin exercises
# `--dump` (RDF.NQuads.Serialize, the plain N-Triples wire path) and
# the COTTAS store round trip. This pin exercises `--dump-turtle`
# (RDF.Turtle.Serialize.fst's prefix-compacted, subject-grouped
# renderer) specifically, re-reading its output through the SAME
# fixture's literal classes (quote / newline / backslash / tab / CR /
# plain / four non-ASCII widths — reused verbatim from
# cli_literal_escape_roundtrip.sh so both pins are testing the same
# ten literals through their own wire path, per the issue #448 brief).
#
# RDF.Turtle.Serialize's literal branch reuses
# RDF.NQuads.Serialize.nq_escape_literal (confirmed by reading the
# source, not inherited from issue #339's table) — the SAME escaper
# arm A of cli_literal_escape_roundtrip.sh already exercises. This
# pin is not redundant with that fact: it separately confirms the
# TURTLE-SPECIFIC wrapping (`@prefix` header abbreviation, `a` for
# rdf:type, `;`/`,` grouping, `<<( )>>` triple-term syntax where
# applicable) does not itself corrupt a literal on the way out, and
# that Parser.Turtle (not Parser.NTriples) reads the escaped form back
# correctly.
#
# Arm A: --dump-turtle output re-read gives back the same triple count.
# Arm B: every literal's exact lexical form survives, checked through
#        `-o json` (never the human-facing TABLE renderer -- a table
#        row printing a literal's raw content verbatim is correct
#        output, not evidence about the stored/re-parsed value; see
#        cli_literal_escape_roundtrip.sh's own note on this).
# ANTI-VACUITY: corrupt the --dump-turtle output the same way issue
# #443 corrupted --dump (unescape the quote) and require Arm A to
# notice -- a degenerate "always pass" pin would not catch this.
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
  echo "turtle_pretty_serialize_roundtrip: no factoidal binary found" >&2
  exit 2
fi

TMPDIR="${TMPDIR:-/tmp}"
WORKDIR="$(mktemp -d "${TMPDIR}/factoidal-ttl-roundtrip-XXXXXX")"
trap 'rm -rf "${WORKDIR}"' EXIT

PASS=0
FAIL=0
report_pass() { PASS=$((PASS + 1)); echo "PASS  $1"; }
report_fail() { FAIL=$((FAIL + 1)); echo "FAIL  $1"; }

# Same ten literals as cli_literal_escape_roundtrip.sh (kept byte-
# identical on purpose -- both pins exercise the same classes through
# their own wire path).
FIXTURE="${WORKDIR}/escapes.nq"
cat > "${FIXTURE}" <<'EOF'
<http://e/quote> <http://e/p> "has \" quote" .
<http://e/newline> <http://e/p> "has \n newline" .
<http://e/backslash> <http://e/p> "has \\ backslash" .
<http://e/tab> <http://e/p> "has \t tab" .
<http://e/plain> <http://e/p> "plain ascii" .
<http://e/cr> <http://e/p> "has \r carriage return" .
<http://e/cafe> <http://e/p> "café" .
<http://e/greek> <http://e/p> "λόγος" .
<http://e/cjk> <http://e/p> "日本語" .
<http://e/emoji> <http://e/p> "hi 🎉 there" .
EOF
EXPECTED_TRIPLES=10

# ---------------------------------------------------------------------
# Produce --dump-turtle output.
# ---------------------------------------------------------------------
PRETTY="${WORKDIR}/pretty.ttl"
"${BIN}" --dump-turtle "${FIXTURE}" > "${PRETTY}" 2>"${WORKDIR}/dump.err"
DUMP_RC=$?
if [ "${DUMP_RC}" -ne 0 ]; then
  report_fail "dump-turtle exited ${DUMP_RC}"
  cat "${WORKDIR}/dump.err"
else
  report_pass "dump-turtle exited 0"
fi

# ---------------------------------------------------------------------
# Arm A: re-read count.
# ---------------------------------------------------------------------
arm_a() {
  local ttl="$1" label="$2"
  local n_reread
  # `--count` prints "<path>: N triples" -- the path is a mktemp dir
  # with digits in it, so take the number AFTER the last colon (same
  # sed-anchoring lesson cli_literal_escape_roundtrip.sh's own comment
  # records: taking the first number on the line reads the temp-dir
  # suffix instead of the triple count).
  n_reread="$("${BIN}" --count "${ttl}" 2>/dev/null | sed -n 's/.*: \([0-9][0-9]*\) triples.*/\1/p' | head -1)"
  if [ "${n_reread:-0}" = "${EXPECTED_TRIPLES}" ]; then
    report_pass "${label}: re-read of --dump-turtle output gives ${EXPECTED_TRIPLES} triples"
    return 0
  fi
  report_fail "${label}: re-read of --dump-turtle output gives ${n_reread:-<none>} triples, expected ${EXPECTED_TRIPLES}"
  echo "----- the dump-turtle output that could not be re-read -----"
  cat -A "${ttl}"
  echo "--------------------------------------------------------------"
  return 1
}

if [ "${DUMP_RC}" -eq 0 ]; then
  arm_a "${PRETTY}" "arm A"
fi

# ---------------------------------------------------------------------
# Anti-vacuity for arm A: corrupt the same way issue #443 corrupted
# --dump (unescape the quote) and require arm A to notice.
# ---------------------------------------------------------------------
if [ "${DUMP_RC}" -eq 0 ]; then
  CORRUPT="${WORKDIR}/corrupt.ttl"
  sed 's/\\"/"/g' "${PRETTY}" > "${CORRUPT}"
  if arm_a "${CORRUPT}" "anti-vacuity(expected to fail)" > "${WORKDIR}/av.log" 2>&1; then
    report_fail "anti-vacuity: arm A ACCEPTED a dump-turtle output with unescaped quotes -- this pin cannot detect a #443-shaped regression"
  else
    FAIL=$((FAIL - 1))
    report_pass "anti-vacuity: arm A rejects a dump-turtle output with unescaped quotes (so it can go red)"
  fi
fi

# ---------------------------------------------------------------------
# Arm B: every literal survives byte-exact, queried directly against
# the re-parsed .ttl file (no store import needed -- --data reads
# Turtle by file extension via RDF_Format.detect_format_or_default).
# ---------------------------------------------------------------------
if [ "${DUMP_RC}" -eq 0 ]; then
  QJSON="${WORKDIR}/query.json"
  "${BIN}" --data "${PRETTY}" -o json \
    -e 'SELECT ?s ?o WHERE { ?s <http://e/p> ?o }' > "${QJSON}" 2>"${WORKDIR}/query.err"
  QUERY_RC=$?
  if [ "${QUERY_RC}" -ne 0 ]; then
    report_fail "arm B: query against re-parsed dump-turtle output exited ${QUERY_RC}"
    cat "${WORKDIR}/query.err"
  else
    if python3 - "${QJSON}" <<'PY'
import json, sys
want = {
    "quote":      'has " quote',
    "newline":    'has \n newline',
    "backslash":  'has \\ backslash',
    "tab":        'has \t tab',
    "plain":      'plain ascii',
    "cr":         'has \r carriage return',
    "cafe":       'café',
    "greek":      'λόγος',
    "cjk":        '日本語',
    "emoji":      'hi 🎉 there',
}
try:
    doc = json.load(open(sys.argv[1]))
except Exception as e:
    print(f"  could not parse query output as JSON: {e}")
    sys.exit(1)
rows = doc.get("results", {}).get("bindings", [])
got = {r["s"]["value"].rsplit("/", 1)[-1]: r["o"]["value"] for r in rows if "s" in r and "o" in r}
bad = [(k, want[k], got.get(k)) for k in want if got.get(k) != want[k]]
for k, w, g in bad:
    print(f"  {k}: expected {w!r}, got {g!r}")
sys.exit(1 if bad else 0)
PY
    then
      report_pass "arm B: all ${EXPECTED_TRIPLES} literals round-trip byte-exact through dump-turtle -> Parser.Turtle"
    else
      report_fail "arm B: at least one literal changed value through dump-turtle -> Parser.Turtle (detail above)"
      cat "${QJSON}"
    fi
  fi
fi

echo
echo "turtle_pretty_serialize_roundtrip: ${PASS} pass, ${FAIL} fail (out of $((PASS + FAIL)))"
[ "${FAIL}" -eq 0 ]
