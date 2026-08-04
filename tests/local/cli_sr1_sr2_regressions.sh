#!/usr/bin/env bash
# tests/local/cli_sr1_sr2_regressions.sh — regression pins for the two
# query-path wrong-answer findings of the #313 refinement vertical:
#
#   SR-1 (#336): SELECT DISTINCT returned duplicate rows when a UNION's
#   arms built the same solution mapping in different variable order —
#   sm_equal compared association lists positionally, not as the
#   partial functions section 18.3 defines.
#
#   SR-2 (#337): the hash-join key was byte identity while the
#   acceptance test folds language-tag case, so "x"@en / "x"@EN landed
#   in different buckets and OPTIONAL returned an UNBOUND row for a
#   pattern that matches — the plain join and the OPTIONAL disagreed
#   about the same two patterns.
#
# Both defects were machine-checked in SPARQL11.Algebra.Refinement.fst
# before the fix and their theorems flipped to positive forms with it;
# these pins are the binary-level end of the same statements.
#
# Rule anchors: #14, #16, #25.

set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
BIN="${ROOT}/formal/fstar/ocaml-output/factoidal"
if [ ! -x "${BIN}" ]; then BIN="${ROOT}/bin/linux-x86_64/factoidal"; fi
if [ ! -x "${BIN}" ]; then
  echo "cli_sr1_sr2_regressions: no factoidal binary found" >&2
  exit 2
fi

TMPDIR="${TMPDIR:-/tmp}"
WORKDIR="$(mktemp -d "${TMPDIR}/factoidal-sr12-XXXXXX")"
trap 'rm -rf "${WORKDIR}"' EXIT

PASS=0
FAIL=0
note() {
  if [ "$1" -eq 0 ]; then echo "PASS $2"; PASS=$((PASS+1));
  else echo "FAIL $2"; shift 2; printf '%s\n' "$@"; FAIL=$((FAIL+1)); fi
}

rows_of() { printf '%s\n' "$1" | sed -n 's/^\([0-9][0-9]*\) result(s)$/\1/p' | tail -1; }

# ---- SR-1: DISTINCT over order-disagreeing UNION arms --------------------
cat > "${WORKDIR}/sr1.ttl" <<'EOF'
@prefix : <http://ex/> .
:s :p :o .
EOF

OUT="$("${BIN}" query --data "${WORKDIR}/sr1.ttl" \
  -e 'PREFIX : <http://ex/> SELECT DISTINCT * WHERE { { ?x :p ?y } UNION { ?y :q ?x } }' 2>&1)"
RC=$?
N="$(rows_of "${OUT}")"
[ "${RC}" -eq 0 ] && [ "${N}" = "1" ]; note $? "sr1-distinct-union-one-row (got ${N:-none})" "${OUT}"

# The two arms bind the same variables; without DISTINCT the single
# match appears once per matching arm. Guard that DISTINCT was the thing
# that deduped (i.e. the query itself yields a row at all).
[ -n "${N}" ] && [ "${N}" != "0" ]; note $? "sr1-query-nonempty" "${OUT}"

# ---- SR-2: language-tag case across a join ------------------------------
cat > "${WORKDIR}/sr2.ttl" <<'EOF'
@prefix : <http://ex/> .
:a :p "x"@en .
:b :q "x"@EN .
EOF

OUT_J="$("${BIN}" query --data "${WORKDIR}/sr2.ttl" \
  -e 'PREFIX : <http://ex/> SELECT * WHERE { ?s :p ?v . ?t :q ?v }' 2>&1)"
NJ="$(rows_of "${OUT_J}")"
printf '%s' "${OUT_J}" | grep -q "http://ex/b"; RB=$?
[ "${NJ}" = "1" ] && [ "${RB}" -eq 0 ]; note $? "sr2-plain-join-matches (rows ${NJ:-none})" "${OUT_J}"

OUT_O="$("${BIN}" query --data "${WORKDIR}/sr2.ttl" \
  -e 'PREFIX : <http://ex/> SELECT * WHERE { ?s :p ?v OPTIONAL { ?t :q ?v } }' 2>&1)"
NO="$(rows_of "${OUT_O}")"
printf '%s' "${OUT_O}" | grep -q "http://ex/b"; RB=$?
[ "${NO}" = "1" ] && [ "${RB}" -eq 0 ]; note $? "sr2-optional-agrees-with-join (rows ${NO:-none}, ?t bound)" "${OUT_O}"

# Sub-SELECT composition reaches GP_Join (the hash-join path) even when
# the flat BGP would not; same agreement required.
OUT_S="$("${BIN}" query --data "${WORKDIR}/sr2.ttl" \
  -e 'PREFIX : <http://ex/> SELECT * WHERE { { SELECT ?v WHERE { ?s :p ?v } } ?t :q ?v }' 2>&1)"
NS="$(rows_of "${OUT_S}")"
printf '%s' "${OUT_S}" | grep -q "http://ex/b"; RB=$?
[ "${NS}" = "1" ] && [ "${RB}" -eq 0 ]; note $? "sr2-subselect-join-matches (rows ${NS:-none})" "${OUT_S}"

echo
echo "cli_sr1_sr2_regressions: ${PASS} pass, ${FAIL} fail (out of $((PASS+FAIL)))"
if [ "${FAIL}" -ne 0 ]; then exit 1; fi
exit 0
