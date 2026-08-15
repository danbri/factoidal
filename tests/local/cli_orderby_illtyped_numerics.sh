#!/usr/bin/env bash
# tests/local/cli_orderby_illtyped_numerics.sh — regression pin for
# issue #362 (SR-4): `sparql_order`'s numeric branch read
# `numeric_compare`'s undifferentiated `None` as an unconditional TIE
# regardless of WHICH side failed to parse, so a single ill-typed
# numeric literal (e.g. "abc"^^xsd:integer) acted as a spurious
# tie-bridge and misordered the VALID numeric rows around it —
# non-transitive: A ties B, B ties C, but A > C.
#
# Fix (owner-approved 2026-08-14): order valid numerics numerically,
# sort any operand whose numeric literal fails to parse AFTER every
# valid numeric, and break ties among unparseable operands by
# comparing their raw lexical form (datatype plays NO role) — measured
# to match Apache Jena 6.2.0 exactly. SPARQL 1.1 §15.1 requires only
# that the ordering be CONSISTENT for operands with no defined `<`; it
# does not mandate a specific rule.
#
# This asserts the FULL expected row order (not just where the bad
# literals land) because the bug's real damage was to the ordering of
# the VALID rows, not just the placement of the invalid ones. It also
# runs THROUGH THE CLI BINARY (the path `factoidal query`, the npm
# bundle, and the HTTP server all use), per the project's CLI-path
# pinning convention (cli_exists_regressions.sh,
# cli_literal_escape_roundtrip.sh).
#
# Rule anchors: #14 (no swallowed exit codes), #16 (no truncation),
# #25 (labelled pass/fail counts in words).

set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"

# Same committed-binary resolution the other local scripts use: the
# ocaml-output symlink points at the current platform's bin/ directory.
BIN="${ROOT}/formal/fstar/ocaml-output/factoidal"
if [ ! -x "${BIN}" ]; then
  BIN="${ROOT}/bin/linux-x86_64/factoidal"
fi
if [ ! -x "${BIN}" ]; then
  echo "cli_orderby_illtyped_numerics: no factoidal binary found" >&2
  exit 2
fi

TMPDIR="${TMPDIR:-/tmp}"
WORKDIR="$(mktemp -d "${TMPDIR}/factoidal-cli-orderby-XXXXXX")"
trap 'rm -rf "${WORKDIR}"' EXIT

PASS=0
FAIL=0

# check NAME DATA_FILE QUERY EXPECTED_LINE...
# Runs the CLI, extracts the ordered ?v column values (the second
# quoted/angle-bracketed field on each result row, in row order), and
# compares the FULL sequence against the expected list. Prints the
# full CLI output on failure (rule #16).
check() {
  local name="$1" data="$2" query="$3"
  shift 3
  local expected=("$@")
  local out rc=0
  out="$("${BIN}" query --data "${data}" -e "${query}" 2>&1)" || rc=$?
  # Pull the ?v column: the table body lines look like
  # | <http://example.org/e> | "10"^^<...#integer>  |
  # Extract everything between the SECOND pair of '| ... |' delimiters,
  # trimmed, skipping header/separator rows.
  local got
  got="$(printf '%s\n' "${out}" \
    | awk -F'|' 'NR>3 && NF>=3 && $0 !~ /^\+/ { gsub(/^[ \t]+|[ \t]+$/, "", $3); print $3 }')"
  local got_arr=()
  while IFS= read -r line; do
    [ -n "${line}" ] && got_arr+=("${line}")
  done <<< "${got}"

  local ok=1
  if [ "${rc}" -ne 0 ]; then ok=0; fi
  if [ "${#got_arr[@]}" -ne "${#expected[@]}" ]; then ok=0; fi
  if [ "${ok}" -eq 1 ]; then
    local i=0
    while [ "${i}" -lt "${#expected[@]}" ]; do
      if [ "${got_arr[$i]}" != "${expected[$i]}" ]; then ok=0; fi
      i=$((i+1))
    done
  fi

  if [ "${ok}" -eq 1 ]; then
    echo "PASS ${name} (${#got_arr[@]} rows, order matched)"
    PASS=$((PASS+1))
  else
    echo "FAIL ${name}: rc=${rc}"
    echo "  expected: ${expected[*]}"
    echo "  got:      ${got_arr[*]}"
    echo "----- full CLI output -----"
    printf '%s\n' "${out}"
    echo "----------------------------"
    FAIL=$((FAIL+1))
  fi
}

# ---------------------------------------------------------------------
# 1. The issue's own witness: three valid numerics (5, 3, 10), two
#    ill-typed numeric literals ("abc"^^xsd:integer, "zzz"^^xsd:decimal),
#    one plain string. Expected (owner decision / Jena 6.2.0 measured):
#    valid numerics ascending (3, 5, 10), THEN the two unparseable
#    numerics compared lexically on raw lexical form ("abc" < "zzz"),
#    then the plain string (rank 7, after all numerics — unaffected by
#    this fix, included so the pin also catches a rank regression).
# ---------------------------------------------------------------------
cat > "${WORKDIR}/witness.ttl" <<'EOF'
@prefix : <http://example.org/> .
:a :v 5 .
:b :v "abc"^^<http://www.w3.org/2001/XMLSchema#integer> .
:c :v 3 .
:d :v "zzz"^^<http://www.w3.org/2001/XMLSchema#decimal> .
:e :v 10 .
:f :v "plain" .
EOF

check "orderby-illtyped-numerics-witness" \
  "${WORKDIR}/witness.ttl" \
  'SELECT ?s ?v WHERE { ?s <http://example.org/v> ?v } ORDER BY ?v' \
  '"3"^^<http://www.w3.org/2001/XMLSchema#integer>' \
  '"5"^^<http://www.w3.org/2001/XMLSchema#integer>' \
  '"10"^^<http://www.w3.org/2001/XMLSchema#integer>' \
  '"abc"^^<http://www.w3.org/2001/XMLSchema#integer>' \
  '"zzz"^^<http://www.w3.org/2001/XMLSchema#decimal>' \
  '"plain"'

# ---------------------------------------------------------------------
# 2. Remove the two ill-typed literals: the valid numerics alone must
#    still come out 3, 5, 10 (guards against a fix that "fixes" the
#    witness by accident while breaking the plain valid-numeric case).
# ---------------------------------------------------------------------
cat > "${WORKDIR}/valid_only.ttl" <<'EOF'
@prefix : <http://example.org/> .
:a :v 5 .
:c :v 3 .
:e :v 10 .
EOF

check "orderby-valid-numerics-only" \
  "${WORKDIR}/valid_only.ttl" \
  'SELECT ?s ?v WHERE { ?s <http://example.org/v> ?v } ORDER BY ?v' \
  '"3"^^<http://www.w3.org/2001/XMLSchema#integer>' \
  '"5"^^<http://www.w3.org/2001/XMLSchema#integer>' \
  '"10"^^<http://www.w3.org/2001/XMLSchema#integer>'

# ---------------------------------------------------------------------
# 3. Anti-vacuity arm: feed `check` a DELIBERATELY WRONG expected order
#    (the pre-fix bug's own output: 10, zzz, 3, 5, abc, plain) for the
#    SAME witness query, and confirm `check` reports FAIL for it. This
#    proves the comparison logic can actually go red — a pin that
#    "passes" no matter what `check` is fed would be worthless. The
#    expected FAIL from this sub-check is caught and converted into a
#    PASS of the meta-check below; only an UNEXPECTED pass (proving
#    `check` never compares anything) is a hard failure of the pin.
# ---------------------------------------------------------------------
FAIL_BEFORE_ANTIVAC=${FAIL}
check "orderby-anti-vacuity-INTENTIONALLY-WRONG" \
  "${WORKDIR}/witness.ttl" \
  'SELECT ?s ?v WHERE { ?s <http://example.org/v> ?v } ORDER BY ?v' \
  '"10"^^<http://www.w3.org/2001/XMLSchema#integer>' \
  '"zzz"^^<http://www.w3.org/2001/XMLSchema#decimal>' \
  '"3"^^<http://www.w3.org/2001/XMLSchema#integer>' \
  '"5"^^<http://www.w3.org/2001/XMLSchema#integer>' \
  '"abc"^^<http://www.w3.org/2001/XMLSchema#integer>' \
  '"plain"'
if [ "${FAIL}" -gt "${FAIL_BEFORE_ANTIVAC}" ]; then
  # Expected: the deliberately-wrong order was correctly rejected.
  # Undo the FAIL it just recorded (it was supposed to happen) and
  # count the meta-check itself as a PASS instead.
  FAIL=$((FAIL-1))
  PASS=$((PASS+1))
  echo "PASS orderby-anti-vacuity-meta (deliberately-wrong order was correctly rejected)"
else
  echo "FAIL orderby-anti-vacuity-meta: check() accepted a deliberately WRONG order — pin cannot go red, INVALID"
  FAIL=$((FAIL+1))
fi

echo
echo "cli_orderby_illtyped_numerics: ${PASS} pass, ${FAIL} fail (out of $((PASS+FAIL)))"
if [ "${FAIL}" -ne 0 ]; then exit 1; fi
exit 0
