#!/usr/bin/env bash
# tests/local/cli_owlrl_witness_strip.sh — regression pin for issue #346:
# entailed QUERY results must never expose the closure's internal
# comprehension-witness individuals (bnodes with the reserved "__rl_"
# label prefix). Before the fix, `--entail OWL-RL` queries returned rows
# like `?t = _:__rl_svf_<p>__on__<C>`, which label-shortening display
# code collapses into apparent named-class facts — an external reviewer
# read one as the unsound `doc1 a :Person` and filed it as a soundness
# bug (#345).
#
# The `entail` DUMP subcommand deliberately KEEPS the witnesses (the
# rewrite machinery joins on them, #236, and a dump is the honest record
# of the materialisation) — this script pins BOTH behaviours so neither
# regresses toward the other.
#
# Rule anchors: #14 (no swallowed exit codes), #16 (no truncation),
# #25 (labelled pass/fail counts in words).

set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
BIN="${ROOT}/formal/fstar/ocaml-output/factoidal"
if [ ! -x "${BIN}" ]; then BIN="${ROOT}/bin/linux-x86_64/factoidal"; fi
if [ ! -x "${BIN}" ]; then
  echo "cli_owlrl_witness_strip: no factoidal binary found" >&2
  exit 2
fi

TMPDIR="${TMPDIR:-/tmp}"
WORKDIR="$(mktemp -d "${TMPDIR}/factoidal-witness-strip-XXXXXX")"
trap 'rm -rf "${WORKDIR}"' EXIT

cat > "${WORKDIR}/range.ttl" <<'EOF'
@prefix : <http://ex/> .
@prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .
:alice a :Person .
:doc1 :maker :alice .
:Person a rdfs:Class .
:Document a rdfs:Class .
:maker rdfs:range :Person .
EOF

PASS=0
FAIL=0
note() {
  if [ "$1" -eq 0 ]; then echo "PASS $2"; PASS=$((PASS+1));
  else echo "FAIL $2"; shift 2; printf '%s\n' "$@"; FAIL=$((FAIL+1)); fi
}

Q='SELECT ?s ?t WHERE { ?s a ?t }'

# 1. No witness bnode reaches an OWL-RL entailed QUERY result.
OUT="$("${BIN}" query --data "${WORKDIR}/range.ttl" --entail OWL-RL -e "${Q}" 2>&1)"
RC=$?
N_WITNESS="$(printf '%s' "${OUT}" | grep -c "__rl_")"
[ "${RC}" -eq 0 ] && [ "${N_WITNESS}" -eq 0 ]; note $? "no-witness-rows-in-owlrl-query (found ${N_WITNESS})" "${OUT}"

# 2. The sound derivation survives the strip: alice a Person.
printf '%s' "${OUT}" | grep -q "alice>.*<http://ex/Person>"; note $? "alice-a-person-survives" "${OUT}"

# 3. The unsound-looking fact is genuinely absent: no doc1 a Person.
! printf '%s' "${OUT}" | grep -q "doc1>.*<http://ex/Person>"; note $? "no-doc1-a-person" "${OUT}"

# 4. RDFS entailed queries are untouched by the strip (identity there).
OUT_R="$("${BIN}" query --data "${WORKDIR}/range.ttl" --entail RDFS -e "${Q}" 2>&1)"
RC=$?
[ "${RC}" -eq 0 ] && printf '%s' "${OUT_R}" | grep -q "alice>.*<http://ex/Person>" \
  && ! printf '%s' "${OUT_R}" | grep -q "__rl_"; note $? "rdfs-path-unchanged" "${OUT_R}"

# 5. The entail DUMP keeps the full materialisation, witnesses included.
OUT_D="$("${BIN}" entail --data "${WORKDIR}/range.ttl" --regime OWL-RL 2>&1)"
RC=$?
N_DUMP="$(printf '%s' "${OUT_D}" | grep -c "__rl_")"
[ "${RC}" -eq 0 ] && [ "${N_DUMP}" -gt 0 ]; note $? "dump-keeps-witnesses (${N_DUMP} witness triples)" "${OUT_D}"

echo
echo "cli_owlrl_witness_strip: ${PASS} pass, ${FAIL} fail (out of $((PASS+FAIL)))"
if [ "${FAIL}" -ne 0 ]; then exit 1; fi
exit 0
