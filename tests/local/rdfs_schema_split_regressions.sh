#!/usr/bin/env bash
# tests/local/rdfs_schema_split_regressions.sh
#
# Regression pin for the schema/data separation fast path
# (formal/fstar/RDFS.SchemaSplit.fst, Phase 1a of
# docs/designissues/2026-07-31-rdfs-performance-scalability.md).
#
# WHAT THIS PINS. The fast path closes the rdfs:subClassOf /
# rdfs:subPropertyOf sub-graph ONCE, before the loop, and then runs the
# instance rules with rdfs11 and rdfs5 removed. That is only correct
# while nothing INJECTS a new schema edge during the loop, and RDFS is
# reflective, so injection is possible: a graph may assert
#
#     :p rdfs:subPropertyOf rdfs:subClassOf .
#     :A :p :B .
#
# after which rdfs7 turns an ordinary instance triple into a schema
# edge, which rdfs11 must then compose with the rest of the hierarchy.
#
# The DANGEROUS cases are therefore the ones where the fast path is
# WRONG and the dispatcher has to notice and fall back. Nothing else in
# the tree tests that: every W3C suite this project runs stays green
# whether or not the fallback works, because none of them contains a
# reflective graph. Cases B, C and D below are that test. Each asserts a
# triple that exists ONLY because rdfs11 or rdfs5 ran AFTER an injected
# schema edge appeared -- exactly the derivation a fast path without a
# working fallback would drop.
#
# Case A is the complementary direction: an ordinary hierarchy that
# SATISFIES the side condition, so the fast path is taken, must still
# produce the full transitive closure. A side condition nothing
# satisfies would make the whole phase worthless and would keep every
# other case in this file green (the anti-vacuity concern of
# formal/fstar/RDF.Semantics.HypothesisWitness.fst).
#
# Per rule #17 every external process is bounded with `timeout`.
# Per rule #25 counts are labelled, never a bare ratio.
set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
FACTOIDAL="${FACTOIDAL_BIN:-${ROOT}/bin/linux-x86_64/factoidal}"
WORKDIR="$(mktemp -d "${TMPDIR:-/tmp}/factoidal-rdfs-schema-split-XXXXXX")"
trap 'rm -rf "${WORKDIR}"' EXIT

RDF="http://www.w3.org/1999/02/22-rdf-syntax-ns#"
RDFS="http://www.w3.org/2000/01/rdf-schema#"
EX="http://ex.org/"

if [[ ! -x "${FACTOIDAL}" ]]; then
  echo "rdfs_schema_split_regressions: factoidal binary not found or not executable: ${FACTOIDAL}" >&2
  echo "(set FACTOIDAL_BIN, or run 'cd formal/fstar && ./build-ocaml.sh' first)" >&2
  exit 2
fi

PASS=0
FAIL=0
TOTAL=0

# run_case <name> <graph-file> <expected-triple-line> <why>
run_case() {
  local name="$1" graph="$2" expected="$3" why="$4"
  TOTAL=$((TOTAL + 1))
  local out="${WORKDIR}/${name}.nq"
  local rc=0
  timeout 120 "${FACTOIDAL}" entail --data "${graph}" --regime RDFS > "${out}" 2>"${WORKDIR}/${name}.err" || rc=$?
  if [[ "${rc}" -ne 0 ]]; then
    echo "FAIL ${name}: factoidal entail exited ${rc}"
    sed -e 's/^/       /' "${WORKDIR}/${name}.err"
    FAIL=$((FAIL + 1))
    return
  fi
  if grep -qxF "${expected}" "${out}"; then
    echo "ok   ${name}  (${why})"
    PASS=$((PASS + 1))
  else
    echo "FAIL ${name}: closure is missing the derivation this case pins"
    echo "       why      : ${why}"
    echo "       expected : ${expected}"
    echo "       closure had $(wc -l < "${out}") triples; premise graph:"
    sed -e 's/^/         /' "${graph}"
    FAIL=$((FAIL + 1))
  fi
}

echo "== rdfs schema/data split regression pin =="
echo "   binary: ${FACTOIDAL}"

# ---- case A: the fast path is reachable and complete ----------------
# A plain four-link subClassOf chain with one typed individual. It
# satisfies `schema_stable`, so the dispatcher takes the fast path. The
# far end of the chain must still be derived, which is the whole point
# of closing the hierarchy separately.
cat > "${WORKDIR}/a.nt" <<EOF
<${EX}C0> <${RDFS}subClassOf> <${EX}C1> .
<${EX}C1> <${RDFS}subClassOf> <${EX}C2> .
<${EX}C2> <${RDFS}subClassOf> <${EX}C3> .
<${EX}C3> <${RDFS}subClassOf> <${EX}C4> .
<${EX}i> <${RDF}type> <${EX}C0> .
EOF
run_case "chain-transitive-far-end" "${WORKDIR}/a.nt" \
  "<${EX}C0> <${RDFS}subClassOf> <${EX}C4> ." \
  "fast path taken; rdfs11 closure across four links"
run_case "chain-instance-far-end" "${WORKDIR}/a.nt" \
  "<${EX}i> <${RDF}type> <${EX}C4> ." \
  "fast path taken; rdfs9 against the closed hierarchy"

# ---- case B: THE TRAP -- rdfs7 injects a subClassOf edge ------------
# `:p rdfs:subPropertyOf rdfs:subClassOf` makes the ordinary instance
# triple `:A :p :B` derive `:A rdfs:subClassOf :B` (rdfs7). Only THEN
# can rdfs11 compose it with `:B rdfs:subClassOf :C`. The fast path
# computed its schema closure before that edge existed, so it cannot
# have `:A rdfs:subClassOf :C` -- the dispatcher must detect the
# injection and fall back to the general loop.
cat > "${WORKDIR}/b.nt" <<EOF
<${EX}p> <${RDFS}subPropertyOf> <${RDFS}subClassOf> .
<${EX}A> <${EX}p> <${EX}B> .
<${EX}B> <${RDFS}subClassOf> <${EX}C> .
<${EX}x> <${RDF}type> <${EX}A> .
EOF
run_case "reflective-rdfs7-injects-edge" "${WORKDIR}/b.nt" \
  "<${EX}A> <${RDFS}subClassOf> <${EX}B> ." \
  "FALLBACK: rdfs7 turns an instance triple into a schema edge"
run_case "reflective-rdfs7-then-rdfs11" "${WORKDIR}/b.nt" \
  "<${EX}A> <${RDFS}subClassOf> <${EX}C> ." \
  "FALLBACK: rdfs11 composes the INJECTED edge with the hierarchy"
run_case "reflective-rdfs7-then-rdfs9" "${WORKDIR}/b.nt" \
  "<${EX}x> <${RDF}type> <${EX}C> ." \
  "FALLBACK: rdfs9 against the post-injection hierarchy"

# ---- case C: rdfs7 injects a subPropertyOf edge (rdfs5 dual) --------
# The same trap one rung over: an alias for rdfs:subPropertyOf itself,
# so the injected edge has to be composed by rdfs5, not rdfs11.
cat > "${WORKDIR}/c.nt" <<EOF
<${EX}q> <${RDFS}subPropertyOf> <${RDFS}subPropertyOf> .
<${EX}r1> <${EX}q> <${EX}r2> .
<${EX}r2> <${RDFS}subPropertyOf> <${EX}r3> .
<${EX}s> <${EX}r1> <${EX}o> .
EOF
run_case "reflective-rdfs7-then-rdfs5" "${WORKDIR}/c.nt" \
  "<${EX}r1> <${RDFS}subPropertyOf> <${EX}r3> ." \
  "FALLBACK: rdfs5 composes an INJECTED subPropertyOf edge"
run_case "reflective-subprop-reaches-data" "${WORKDIR}/c.nt" \
  "<${EX}s> <${EX}r3> <${EX}o> ." \
  "FALLBACK: rdfs7 against the post-injection property hierarchy"

# ---- case D: metamodelling -- rdfs9 mints an rdfs:Class membership --
# `:AgentClass rdfs:subClassOf rdfs:Class` is real, shipped
# metamodelling: Dublin Core Terms asserts exactly this triple. It makes
# rdfs9 derive `:Person rdf:type rdfs:Class`, which rdfs8 turns into
# `:Person rdfs:subClassOf rdfs:Resource` -- a schema edge minted inside
# the loop -- which rdfs11 must then compose with `:Q rdfs:subClassOf
# :Person`. Injection route R2c of the RDFS.SchemaSplit banner.
cat > "${WORKDIR}/d.nt" <<EOF
<${EX}AgentClass> <${RDFS}subClassOf> <${RDFS}Class> .
<${EX}Person> <${RDF}type> <${EX}AgentClass> .
<${EX}Q> <${RDFS}subClassOf> <${EX}Person> .
EOF
run_case "metamodel-rdfs9-mints-class" "${WORKDIR}/d.nt" \
  "<${EX}Person> <${RDF}type> <${RDFS}Class> ." \
  "FALLBACK: rdfs9 lifts an individual into rdfs:Class"
run_case "metamodel-rdfs8-then-rdfs11" "${WORKDIR}/d.nt" \
  "<${EX}Q> <${RDFS}subClassOf> <${RDFS}Resource> ." \
  "FALLBACK: rdfs11 composes rdfs8's INJECTED edge down the hierarchy"

echo ""
echo "rdfs_schema_split_regressions: ${PASS} pass, ${FAIL} fail (out of ${TOTAL})"
if [[ "${FAIL}" -ne 0 ]]; then
  exit 1
fi
exit 0
