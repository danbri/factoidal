#!/usr/bin/env bash
# tests/rdf-mt-generated/run.sh — executable generated tests for the
# proved closure rules named in docs/theorem-registry.md (adoption
# item A2, docs/designissues/2026-08-05-semantics-proposal-adoption.md).
#
# Exercises the EXTRACTION/IMPLEMENTATION boundary the pure F* theorems
# do not cover: each test runs a small premise graph through the
# COMMITTED NATIVE BINARY's `entail` subcommand (not the F* proof, not
# the w3c_runner harness) and checks the shipping closure produces (or
# correctly withholds) the conclusion triple.
#
# Standalone: does NOT modify w3c-tests.sh or any existing test wiring.
# See WIRING.md (one directory up) for the one-line orchestrator hook.
#
# Rule anchors: #14 (no swallowed exit codes), #16 (no truncation —
# every failure prints full output), #25 (labelled pass/fail/total).

set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

# Same committed-binary resolution tests/local/*.sh uses: the
# ocaml-output symlink points at the current platform's bin/ directory,
# with a direct bin/linux-x86_64 fallback.
BIN="${ROOT}/formal/fstar/ocaml-output/factoidal"
if [ ! -x "${BIN}" ]; then
  BIN="${ROOT}/bin/linux-x86_64/factoidal"
fi
if [ ! -x "${BIN}" ]; then
  echo "rdf-mt-generated/run.sh: no factoidal binary found (tried" \
       "formal/fstar/ocaml-output/factoidal and bin/linux-x86_64/factoidal)" >&2
  exit 2
fi

echo "rdf-mt-generated: using binary ${BIN}"
echo "rdf-mt-generated: CLI invocation is \`factoidal entail --data FILE --regime RDFS|OWL-RL\`"

"${HERE}/generate.sh" || { echo "rdf-mt-generated: generate.sh failed" >&2; exit 2; }

FIX="${HERE}/fixtures"
TMPDIR="${TMPDIR:-/tmp}"
WORKDIR="$(mktemp -d "${TMPDIR}/factoidal-rdf-mt-generated-XXXXXX")"
trap 'rm -rf "${WORKDIR}"' EXIT

PASS=0
FAIL=0

# entail_out REGIME FILE  -- run the binary, print the closure to
# stdout, or print a diagnostic and return nonzero on a CLI error.
entail_out() {
  local regime="$1" file="$2"
  "${BIN}" entail --data "${file}" --regime "${regime}"
}

# check_present NAME REGIME FILE PATTERN
# Passes if entail exits 0 AND the (fixed-string) PATTERN appears at
# least once in the closure.
check_present() {
  local name="$1" regime="$2" file="$3" pattern="$4"
  local out rc=0
  out="$(entail_out "${regime}" "${file}" 2>&1)" || rc=$?
  if [ "${rc}" -eq 0 ] && printf '%s\n' "${out}" | grep -qF -- "${pattern}"; then
    echo "PASS ${name}"
    PASS=$((PASS+1))
  else
    echo "FAIL ${name}: rc=${rc}, expected to find: ${pattern}"
    echo "----- full output (${file}, regime ${regime}) -----"
    printf '%s\n' "${out}"
    echo "----------------------------------------------------"
    FAIL=$((FAIL+1))
  fi
}

# check_absent NAME REGIME FILE PATTERN
# Passes if entail exits 0 AND PATTERN does NOT appear anywhere.
check_absent() {
  local name="$1" regime="$2" file="$3" pattern="$4"
  local out rc=0
  out="$(entail_out "${regime}" "${file}" 2>&1)" || rc=$?
  if [ "${rc}" -eq 0 ] && ! printf '%s\n' "${out}" | grep -qF -- "${pattern}"; then
    echo "PASS ${name}"
    PASS=$((PASS+1))
  else
    echo "FAIL ${name}: rc=${rc}, expected NOT to find: ${pattern}"
    echo "----- full output (${file}, regime ${regime}) -----"
    printf '%s\n' "${out}"
    echo "----------------------------------------------------"
    FAIL=$((FAIL+1))
  fi
}

# check_count NAME REGIME FILE PATTERN EXPECTED_COUNT
# Passes if entail exits 0 AND PATTERN appears EXACTLY EXPECTED_COUNT
# times. Used to pin "exactly one conclusion, not a promoted-literal
# duplicate" shapes.
check_count() {
  local name="$1" regime="$2" file="$3" pattern="$4" expect="$5"
  local out rc=0 got
  out="$(entail_out "${regime}" "${file}" 2>&1)" || rc=$?
  got="$(printf '%s\n' "${out}" | grep -cF -- "${pattern}")"
  if [ "${rc}" -eq 0 ] && [ "${got}" = "${expect}" ]; then
    echo "PASS ${name} (count=${got})"
    PASS=$((PASS+1))
  else
    echo "FAIL ${name}: rc=${rc}, count=${got} (expected ${expect}) for pattern: ${pattern}"
    echo "----- full output (${file}, regime ${regime}) -----"
    printf '%s\n' "${out}"
    echo "----------------------------------------------------"
    FAIL=$((FAIL+1))
  fi
}

# check_same_closure NAME REGIME FILE_A FILE_B
# Passes if both fixtures entail exit 0 AND their SORTED closures are
# byte-identical. Used for both:
#   - order independence: FILE_B is FILE_A with premise lines swapped
#   - duplicate-premise set-equivalence: FILE_B repeats a premise triple
check_same_closure() {
  local name="$1" regime="$2" file_a="$3" file_b="$4"
  local out_a out_b rc_a=0 rc_b=0
  out_a="$(entail_out "${regime}" "${file_a}" 2>&1 | sort)" || rc_a=$?
  out_b="$(entail_out "${regime}" "${file_b}" 2>&1 | sort)" || rc_b=$?
  if [ "${rc_a}" -eq 0 ] && [ "${rc_b}" -eq 0 ] && [ "${out_a}" = "${out_b}" ]; then
    echo "PASS ${name}"
    PASS=$((PASS+1))
  else
    echo "FAIL ${name}: rc_a=${rc_a} rc_b=${rc_b}"
    echo "----- diff (sorted closures of ${file_a} vs ${file_b}) -----"
    diff <(printf '%s\n' "${out_a}") <(printf '%s\n' "${out_b}")
    echo "--------------------------------------------------------------"
    FAIL=$((FAIL+1))
  fi
}

# =======================================================================
# rdfs2 -- domain. Registry: docs/theorem-registry.md line 196
# (rdfs2 | rdfs2_derives | rdfs_rule_domain | PROVED/PROVED).
# =======================================================================

check_present "rdfs2-domain-template" RDFS "${FIX}/rdfs2_base.ttl" \
  '<http://example.org/rdfs2/x> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://example.org/rdfs2/C> .'

check_same_closure "rdfs2-order-independent" RDFS \
  "${FIX}/rdfs2_base.ttl" "${FIX}/rdfs2_reordered.ttl"

check_same_closure "rdfs2-duplicate-premises-set-equivalent" RDFS \
  "${FIX}/rdfs2_base.ttl" "${FIX}/rdfs2_duplicate.ttl"

# =======================================================================
# rdfs3 -- range. Registry: docs/theorem-registry.md line 197
# (rdfs3 | rdfs3_derives | rdfs_rule_range | PROVED/PROVED; finding
# RS-3 notes the literal/triple-term-object case is silently dropped
# because a literal can never become an N-Triples subject).
# =======================================================================

check_present "rdfs3-range-template" RDFS "${FIX}/rdfs3_base.ttl" \
  '<http://example.org/rdfs3/y> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://example.org/rdfs3/C> .'

check_same_closure "rdfs3-order-independent" RDFS \
  "${FIX}/rdfs3_base.ttl" "${FIX}/rdfs3_reordered.ttl"

# Soundness boundary (proposal + registry finding RS-3): a literal
# object must NOT become a subject. rdfs3_literal_boundary.ttl has
# BOTH an IRI-object premise (ex:x1 ex:p ex:y1, should fire) and a
# literal-object premise (ex:x2 ex:p "literal value", must not fire —
# and structurally cannot, since N-Triples subjects are IRI/bnode
# only). We assert exactly ONE rdf:type-ex:C conclusion total, proving
# the literal premise contributed none.
check_present "rdfs3-literal-boundary-iri-branch-fires" RDFS \
  "${FIX}/rdfs3_literal_boundary.ttl" \
  '<http://example.org/rdfs3/y1> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://example.org/rdfs3/C> .'

check_count "rdfs3-literal-boundary-literal-does-not-become-subject" RDFS \
  "${FIX}/rdfs3_literal_boundary.ttl" \
  'rdf-syntax-ns#type> <http://example.org/rdfs3/C> .' 1

# =======================================================================
# rdfs7 -- subPropertyOf. Registry: docs/theorem-registry.md line 202
# (rdfs7 | rdfs7_derives | rdfs_rule_subPropertyOf | PROVED/PROVED).
# =======================================================================

check_present "rdfs7-subPropertyOf-template" RDFS "${FIX}/rdfs7_base.ttl" \
  '<http://example.org/rdfs7/x> <http://example.org/rdfs7/q> <http://example.org/rdfs7/y> .'

check_same_closure "rdfs7-order-independent" RDFS \
  "${FIX}/rdfs7_base.ttl" "${FIX}/rdfs7_reordered.ttl"

check_same_closure "rdfs7-duplicate-premises-set-equivalent" RDFS \
  "${FIX}/rdfs7_base.ttl" "${FIX}/rdfs7_duplicate.ttl"

# =======================================================================
# rdfs9 -- subClassOf. Registry: docs/theorem-registry.md line 204
# (rdfs9 | rdfs9_derives (rdfs9_derives2 two-source form) |
# rdfs_rule_subClassOf | PROVED/PROVED).
# =======================================================================

check_present "rdfs9-subClassOf-template" RDFS "${FIX}/rdfs9_base.ttl" \
  '<http://example.org/rdfs9/x> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://example.org/rdfs9/D> .'

check_same_closure "rdfs9-order-independent" RDFS \
  "${FIX}/rdfs9_base.ttl" "${FIX}/rdfs9_reordered.ttl"

check_same_closure "rdfs9-duplicate-premises-set-equivalent" RDFS \
  "${FIX}/rdfs9_base.ttl" "${FIX}/rdfs9_duplicate.ttl"

# =======================================================================
# prp-fp -- functional property. Registry: docs/theorem-registry.md
# line 102 (prp-fp | prp_fp_derives | functional | PROVED (licensing),
# UNATTEMPTED (truth)).
# =======================================================================

check_present "prp-fp-functional-template-fwd" OWL-RL "${FIX}/prpfp_base.ttl" \
  '<http://example.org/prpfp/mom1> <http://www.w3.org/2002/07/owl#sameAs> <http://example.org/prpfp/mom2> .'

check_present "prp-fp-functional-template-rev" OWL-RL "${FIX}/prpfp_base.ttl" \
  '<http://example.org/prpfp/mom2> <http://www.w3.org/2002/07/owl#sameAs> <http://example.org/prpfp/mom1> .'

check_same_closure "prp-fp-duplicate-premises-set-equivalent" OWL-RL \
  "${FIX}/prpfp_base.ttl" "${FIX}/prpfp_duplicate.ttl"

# =======================================================================
# prp-ifp -- inverse-functional property. Registry:
# docs/theorem-registry.md line 103 (prp-ifp | prp_ifp_derives |
# inverse_functional | PROVED (licensing), UNATTEMPTED (truth)).
# =======================================================================

check_present "prp-ifp-inverse-functional-template" OWL-RL "${FIX}/prpifp_base.ttl" \
  '<http://example.org/prpifp/alice> <http://www.w3.org/2002/07/owl#sameAs> <http://example.org/prpifp/bob> .'

# =======================================================================
# prp-key -- WEAKENED-ROW pin. Registry: docs/theorem-registry.md
# line 140 (prp-key | prp_key_derives (row) / prp_key_derives_approx
# (proved against) | prp_key | PROVED, WEAKENED ROW, commit c600646).
# The row's `shares_key_values` uses plain `==`; the shipping engine's
# `agree_on_property` uses `rdf_term_eq` (RDF-1.1 value equality,
# case-insensitive lang tags per #337) -- an OVER-approximation that
# accepts MORE value pairs as "shared" than the literal row licenses.
# This test documents ACTUAL shipping behavior (the engine DOES unify
# "Alice"@en and "Alice"@EN), matching the registry's own machine-
# checked counterexample -- it is not a regression to fix.
# =======================================================================

check_present "prp-key-weakened-row-unifies-case-differing-lang-tags" OWL-RL \
  "${FIX}/prpkey_base.ttl" \
  '<http://example.org/prpkey/p1> <http://www.w3.org/2002/07/owl#sameAs> <http://example.org/prpkey/p2> .'

# =======================================================================

echo
echo "rdf-mt-generated: ${PASS} pass, ${FAIL} fail (out of $((PASS+FAIL)))"
if [ "${FAIL}" -ne 0 ]; then exit 1; fi
exit 0
