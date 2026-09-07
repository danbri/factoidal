#!/usr/bin/env bash
# tests/local/owl/equivalentclass_not_sameas.sh — regression pin for the
# 2026-09-07 removal of `owl_rule_named_equivClass_to_sameAs`
# (docs/designissues/2026-09-07-fstar-owl-soundness-audit.md).
#
# The removed rule emitted `C owl:sameAs D` and `D owl:sameAs C` from
# `C owl:equivalentClass D` whenever both were named classes and one
# carried an extra property assertion. That is unsound under both OWL 2
# semantics: `EquivalentClasses(C D)` states that the two class
# EXPRESSIONS have the same extension, and `owl:sameAs` / SameIndividual
# states that the two RESOURCES are identical. Coextension of class
# extensions does not entail identity of resources — under the Direct
# Semantics punning keeps the class and individual readings of one IRI
# independent (Structural Specification section 5.8), and under the
# RDF-Based Semantics owl:equivalentClass is a condition on ICEXT while
# owl:sameAs is a condition on S (RDF-Based Semantics section 5.8).
#
# Once `C owl:sameAs D` existed, eq-rep-s copied EVERY assertion about C
# onto D. That is what this script checks is gone: the fabricated
# identity, and the annotation and non-annotation facts it carried over.
#
# The SOUND converse — `owl_rule_named_sameAs_to_equivClass`, sameAs
# resources have equal class extensions — is unaffected and is pinned
# here too, so the removal cannot be over-applied.
#
# Rule anchors: #14 (no swallowed exit codes), #16 (no truncation),
# #25 (labelled pass/fail counts in words).

set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd)"
# Pick a binary that actually RUNS on this host. `ocaml-output/factoidal`
# is a committed symlink into one platform's bin/ directory, so an -x
# test on it succeeds on every platform and then fails with "Exec format
# error" on all but one. Probe with --version instead of trusting -x.
BIN=""
for cand in "${ROOT}/bin/$(uname -s | tr 'A-Z' 'a-z')-$(uname -m)/factoidal" \
            "${ROOT}/formal/fstar/ocaml-output/factoidal" \
            "${ROOT}/bin/darwin-arm64/factoidal" \
            "${ROOT}/bin/linux-x86_64/factoidal"; do
  if [ -x "${cand}" ] && "${cand}" --version >/dev/null 2>&1; then
    BIN="${cand}"; break
  fi
done
if [ -z "${BIN}" ]; then
  echo "equivalentclass_not_sameas: no factoidal binary found" >&2
  exit 2
fi

TMPDIR="${TMPDIR:-/tmp}"
WORKDIR="$(mktemp -d "${TMPDIR}/factoidal-eqc-sameas-XXXXXX")"
trap 'rm -rf "${WORKDIR}"' EXIT

# C1 and C2 are named classes, coextensive by axiom. C1 carries an
# annotation (rdfs:comment) and a non-annotation assertion
# (dc:creator), so the removed rule's `has_extra_property` guard would
# have been satisfied and the rule would have fired.
cat > "${WORKDIR}/eqc.ttl" <<'TTL'
@prefix :     <http://ex/> .
@prefix owl:  <http://www.w3.org/2002/07/owl#> .
@prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .
@prefix dc:   <http://purl.org/dc/elements/1.1/> .
:C1 a owl:Class .
:C2 a owl:Class .
:C1 owl:equivalentClass :C2 .
:C1 rdfs:comment "An example class." .
:C1 dc:creator "Alice" .
TTL

# The sound converse: two individuals asserted the same, both typed as
# classes, must yield owl:equivalentClass between them.
cat > "${WORKDIR}/sameas.ttl" <<'TTL'
@prefix :    <http://ex/> .
@prefix owl: <http://www.w3.org/2002/07/owl#> .
:D1 a owl:Class .
:D2 a owl:Class .
:D1 owl:sameAs :D2 .
TTL

PASS=0
FAIL=0
note() {
  if [ "$1" -eq 0 ]; then echo "PASS $2"; PASS=$((PASS+1));
  else echo "FAIL $2"; shift 2; printf '%s\n' "$@"; FAIL=$((FAIL+1)); fi
}

OUT="$("${BIN}" entail --data "${WORKDIR}/eqc.ttl" --regime OWL-RL 2>&1)"
RC=$?
[ "${RC}" -eq 0 ]; note $? "eqc-closure-runs" "${OUT}"

# 1. No fabricated identity between the two coextensive named classes.
!(printf '%s\n' "${OUT}" | grep -E '<http://ex/C1>[^\n]*owl#sameAs[^\n]*<http://ex/C2>' -q) \
  && !(printf '%s\n' "${OUT}" | grep -E '<http://ex/C2>[^\n]*owl#sameAs[^\n]*<http://ex/C1>' -q)
note $? "no-C1-sameAs-C2" "${OUT}"

# 2. The annotation is NOT copied across. It was, via eq-rep-s, and that
#    copy is what made WebOnt-I4.6-005-Direct pass on the unsound route.
! printf '%s\n' "${OUT}" | grep -E '<http://ex/C2>[^\n]*rdf-schema#comment' -q
note $? "no-comment-copied-to-C2" "${OUT}"

# 3. The non-annotation assertion is NOT copied across either. This one
#    matters more: an annotation is at least without Direct-Semantics
#    content, whereas dc:creator on C2 is a manufactured ordinary fact.
! printf '%s\n' "${OUT}" | grep -E '<http://ex/C2>[^\n]*dc/elements/1.1/creator' -q
note $? "no-creator-copied-to-C2" "${OUT}"

# 4. The licensed derivations survive: cls-eqc1 still turns
#    equivalentClass into the two subClassOf conclusions.
printf '%s\n' "${OUT}" | grep -E '<http://ex/C1>[^\n]*subClassOf[^\n]*<http://ex/C2>' -q \
  && printf '%s\n' "${OUT}" | grep -E '<http://ex/C2>[^\n]*subClassOf[^\n]*<http://ex/C1>' -q
note $? "eqc-still-gives-both-subClassOf" "${OUT}"

# 5. The SOUND converse is untouched: sameAs classes are equivalentClass.
OUT_S="$("${BIN}" entail --data "${WORKDIR}/sameas.ttl" --regime OWL-RL 2>&1)"
RC=$?
[ "${RC}" -eq 0 ] \
  && printf '%s\n' "${OUT_S}" | grep -E '<http://ex/D1>[^\n]*equivalentClass[^\n]*<http://ex/D2>' -q
note $? "sameAs-to-equivalentClass-survives" "${OUT_S}"

echo
echo "equivalentclass_not_sameas: ${PASS} pass, ${FAIL} fail (out of $((PASS+FAIL)))"
if [ "${FAIL}" -ne 0 ]; then exit 1; fi
exit 0
