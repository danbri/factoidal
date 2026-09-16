#!/usr/bin/env bash
# Turtle pretty-printer round-trip gate (owner directive: "ensure
# serializers are not gratuitously ugly").
#
# formal/fstar/RDF.Turtle.Serialize.fst adds a prefix-compacted,
# subject-grouped Turtle serializer, wired up as `factoidal dump-turtle
# FILE` (bin/factoidal-cli/factoidal_cli.ml). The correctness anchor is
# round-trip: parse(turtle_of_graph(g)) must be isomorphic to g. This
# script exercises that for four fixtures via the committed binary:
#
#   1. non-ASCII literals + escaped quote/newline/tab
#   2. blank nodes (including a comma-grouped multi-object predicate)
#   3. 1000 triples (200 subjects x 5 predicates) — smoke perf ceiling
#   4. numeric/boolean literal shorthand round trip (issue #681)
#
# For each fixture: canonicalize the original, dump-turtle it, then
# canonicalize the dump-turtle output and byte-compare against the
# original's canonical form (RDFC-1.0 canonicalization is bnode-label-
# independent, so this is a real isomorphism check, not a string diff
# of labels that happen to match). Also asserts the pretty output
# actually looks pretty: contains "@prefix" and ";" predicate-list
# grouping.
#
# NOTE (2026-07-04): written against the FIXED behaviour of
# RDF.Turtle.Serialize.fst / the --dump-turtle CLI wiring landed the
# same day. A build cycle (extract + compile) was in flight when this
# script was written, so `dump-turtle` may not exist in the committed
# binary yet — this script WILL fail with "unknown option '--dump-
# turtle'" until the orchestrator's next build-ocaml.sh run picks up
# RDF.Turtle.Serialize.fst and bin/factoidal-cli/factoidal_cli.ml.
set -u

ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
BIN="${FACTOIDAL_BIN:-${ROOT}/formal/fstar/ocaml-output/factoidal}"
WORKDIR="$(mktemp -d)"
trap 'rm -rf "${WORKDIR}"' EXIT

if [[ ! -x "${BIN}" ]]; then
  echo "SKIP: no binary at ${BIN} (build not yet run)"
  exit 0
fi

pass_count=0
fail_count=0

check() {
  local name="$1" expected="$2" actual="$3"
  if [[ "${actual}" == "${expected}" ]]; then
    echo "PASS ${name}"
    pass_count=$((pass_count + 1))
  else
    echo "FAIL ${name}: expected [${expected}] got [${actual}]"
    fail_count=$((fail_count + 1))
  fi
}

check_contains() {
  local name="$1" needle="$2" file="$3"
  if grep -qF "${needle}" "${file}"; then
    echo "PASS ${name}"
    pass_count=$((pass_count + 1))
  else
    echo "FAIL ${name}: '${needle}' not found in ${file}"
    fail_count=$((fail_count + 1))
  fi
}

# Round-trip one fixture file through: canonicalize (baseline) ->
# dump-turtle -> canonicalize again -> compare. Also runs the
# "not gratuitously ugly" smoke assertions on the dump-turtle output.
roundtrip_check() {
  local name="$1" src="$2"
  local pretty="${WORKDIR}/${name}.pretty.ttl"

  local orig_canon rc_orig
  orig_canon="$(timeout 60 "${BIN}" canonicalize "${src}" 2>&1)"; rc_orig=$?
  check "${name}-orig-canonicalize-rc" "0" "${rc_orig}"

  local rc_dump
  timeout 60 "${BIN}" dump-turtle "${src}" > "${pretty}" 2>"${WORKDIR}/${name}.dump.err"
  rc_dump=$?
  check "${name}-dump-turtle-rc" "0" "${rc_dump}"

  check_contains "${name}-has-prefix" "@prefix" "${pretty}"
  # Semicolon grouping only appears when some subject has more than
  # one predicate; single-predicate fixtures legitimately have none.
  if [[ "${3:-check-semicolons}" != "no-semicolons" ]]; then
    check_contains "${name}-has-semicolon-grouping" ";" "${pretty}"
  fi

  local reparsed_canon rc_reparse
  reparsed_canon="$(timeout 60 "${BIN}" canonicalize "${pretty}" 2>&1)"; rc_reparse=$?
  check "${name}-reparse-canonicalize-rc" "0" "${rc_reparse}"
  check "${name}-roundtrip-isomorphic" "${orig_canon}" "${reparsed_canon}"
}

# --- Fixture 1: non-ASCII literals + escaped quote/newline/tab -------
# café (2-byte UTF-8), em-dash (3-byte), grinning-face emoji (4-byte,
# astral plane — the historical crash case per issue #271), plus an
# escaped quote, newline, and tab inside the same literal.
printf '<http://ex.example/s1> <http://ex.example/p1> "caf\xc3\xa9 \xe2\x80\x94 \xf0\x9f\x98\x80 quote\\"here newline\\nhere tab\\there" .\n' \
  > "${WORKDIR}/fixture1_unicode.nt"
roundtrip_check "unicode" "${WORKDIR}/fixture1_unicode.nt" no-semicolons

# --- Fixture 2: blank nodes, incl. a comma-grouped multi-object case -
cat > "${WORKDIR}/fixture2_bnodes.nt" <<'EOF'
_:b1 <http://ex.example/p> _:b2 .
_:b1 <http://ex.example/p> "also here" .
_:b2 <http://ex.example/p2> "hello" .
<http://ex.example/s> <http://ex.example/p> _:b1 .
<http://ex.example/s> <http://ex.example/p2> "world" .
EOF
roundtrip_check "bnodes" "${WORKDIR}/fixture2_bnodes.nt"

# --- Fixture 3: 1000 triples (200 subjects x 5 predicates) — perf ceiling
{
  for s in $(seq 1 200); do
    for p in a b c d e; do
      echo "<http://ex.example/s${s}> <http://ex.example/p${p}> \"v${s}_${p}\" ."
    done
  done
} > "${WORKDIR}/fixture3_1k.nt"
FIXTURE3_START=$(date +%s)
roundtrip_check "1k" "${WORKDIR}/fixture3_1k.nt"
FIXTURE3_END=$(date +%s)
echo "INFO 1k-roundtrip-wall-seconds=$((FIXTURE3_END - FIXTURE3_START))"

# --- Fixture 4: literal-shorthand round trip (issue #681) ------------
# dump-turtle calls RDF_Turtle_Serialize.turtle_of_graph_auto, which as
# of #681 defaults to bare INTEGER/DECIMAL/DOUBLE/BooleanLiteral
# shorthand whenever the lexical form matches the matching Turtle
# grammar terminal. Covers both directions: the shorthand cases (01,
# +5, .5, 1.0E3, 1e3, true) and the stays-quoted cases (5. has no
# fraction digit; "1e3"^^xsd:decimal is not a DECIMAL; a leading or
# trailing space; a non-numeric lexical form typed xsd:integer).
# This script runs against the COMMITTED native binary, which predates
# #681, so this fixture is exercised only after the next
# build-ocaml.sh extract+compile cycle picks up
# formal/fstar/RDF.Turtle.Serialize.fst. See
# https://github.com/danbri/factoidal/issues/681.
cat > "${WORKDIR}/fixture4_literal_shorthand.nt" <<'EOF'
<http://ex.example/s> <http://ex.example/p> "220.0"^^<http://www.w3.org/2001/XMLSchema#decimal> .
<http://ex.example/s> <http://ex.example/p> "01"^^<http://www.w3.org/2001/XMLSchema#integer> .
<http://ex.example/s> <http://ex.example/p> "+5"^^<http://www.w3.org/2001/XMLSchema#integer> .
<http://ex.example/s> <http://ex.example/p> ".5"^^<http://www.w3.org/2001/XMLSchema#decimal> .
<http://ex.example/s> <http://ex.example/p> "5."^^<http://www.w3.org/2001/XMLSchema#decimal> .
<http://ex.example/s> <http://ex.example/p> "1e3"^^<http://www.w3.org/2001/XMLSchema#decimal> .
<http://ex.example/s> <http://ex.example/p> "1.0E3"^^<http://www.w3.org/2001/XMLSchema#double> .
<http://ex.example/s> <http://ex.example/p> "1e3"^^<http://www.w3.org/2001/XMLSchema#double> .
<http://ex.example/s> <http://ex.example/p> "true"^^<http://www.w3.org/2001/XMLSchema#boolean> .
<http://ex.example/s> <http://ex.example/p> "1"^^<http://www.w3.org/2001/XMLSchema#boolean> .
<http://ex.example/s> <http://ex.example/p> " 7"^^<http://www.w3.org/2001/XMLSchema#integer> .
<http://ex.example/s> <http://ex.example/p> "7 "^^<http://www.w3.org/2001/XMLSchema#integer> .
<http://ex.example/s> <http://ex.example/p> "abc"^^<http://www.w3.org/2001/XMLSchema#integer> .
EOF
roundtrip_check "literal-shorthand" "${WORKDIR}/fixture4_literal_shorthand.nt" no-semicolons

echo "pass=${pass_count} fail=${fail_count}"
if [[ "${fail_count}" -ne 0 ]]; then
  exit 1
fi
