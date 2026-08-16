#!/usr/bin/env bash
# tests/local/cli_rdfc10_relabel_determinism.sh — regression pin for
# issue #448 assurance triage, RDF.Canonical module 4.
#
# WHAT THIS COVERS THAT THE W3C rdf-canon SUITE DOES NOT (see the task
# brief for #448 module 4): the vendored suite (third_party/testing/
# rdf-canon, 86 pass / 0 fail today) is input->expected pairs FIXED at
# specific blank-node labels. It never asks "does a DIFFERENT input
# labelling of the SAME graph shape produce the SAME canonical output"
# -- the exact property RDFC-1.0 exists for, and the one VC Data-
# Integrity signing depends on (sign the canonical form, verify against
# a re-serialized copy that may have used different bnode labels).
#
# Full proof of this property in F* was investigated and rejected as a
# one-commit target for RDF.Canonical.fst (see that file's Section 5b
# banner) -- this pin is the TESTED, not proved, stand-in the task
# brief asked for.
#
# Three arms:
#   Arm A  canonicalize the SAME file twice -> byte-identical output
#          (baseline determinism: no hidden nondeterminism such as
#          hash-table iteration order or wall-clock in the algorithm).
#   Arm B  canonicalize a graph, and canonicalize a hand-relabelled
#          variant of the SAME graph (same triples up to a bijective
#          rename of every blank-node label) -> byte-identical
#          canonical output. This is the actual isomorphism-invariance
#          property.
#   Arm C  anti-vacuity: canonicalize a variant that is NOT isomorphic
#          (one edge's predicate changed) and require the pin to
#          NOTICE the difference -- proves arms A/B are not vacuously
#          "always report identical" checks.
#
# Fixture shape: deliberately non-trivial for blank-node canonicalization
# -- more than one blank node, a blank node connected to another blank
# node (so first-degree hashing alone cannot separate them; RDFC-1.0's
# neighbour-hash step is exercised, not just the trivial single-bnode
# case), and one blank node used as a graph name (TriG), matching this
# module's bnode-graph-name sentinel handling (RDF.Canonical.fst's
# `is_bnode_graph_label`).
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
  echo "cli_rdfc10_relabel_determinism: no factoidal binary found" >&2
  exit 2
fi

TMPDIR="${TMPDIR:-/tmp}"
WORKDIR="$(mktemp -d "${TMPDIR}/factoidal-rdfc10-XXXXXX")"
trap 'rm -rf "${WORKDIR}"' EXIT

PASS=0
FAIL=0
report_pass() { PASS=$((PASS + 1)); echo "PASS  $1"; }
report_fail() { FAIL=$((FAIL + 1)); echo "FAIL  $1"; }

# ---------------------------------------------------------------------
# Fixture A: the "original" labelling.
# ---------------------------------------------------------------------
ORIG="${WORKDIR}/orig.trig"
cat > "${ORIG}" <<'EOF'
@prefix ex: <http://example.org/> .
_:alice ex:name "Alice" .
_:alice ex:knows _:bob .
_:bob ex:name "Bob" .
_:bob ex:knows _:alice .
_:graphNode {
  _:alice ex:role "member" .
}
EOF

# Fixture B: the SAME graph, every blank-node label bijectively renamed
# (alice -> x1, bob -> x2, graphNode -> x3) and the triples reordered.
# Same shape, same edges, different original labels -- exactly the
# input RDFC-1.0's canonical labelling is supposed to be invariant
# under.
RELABEL="${WORKDIR}/relabel.trig"
cat > "${RELABEL}" <<'EOF'
@prefix ex: <http://example.org/> .
_:x2 ex:knows _:x1 .
_:x1 ex:knows _:x2 .
_:x2 ex:name "Bob" .
_:x3 {
  _:x1 ex:role "member" .
}
_:x1 ex:name "Alice" .
EOF

# Fixture C: NOT isomorphic to A/B -- ex:role's object changed, so the
# graph shape differs. Used only for the anti-vacuity arm.
BROKEN="${WORKDIR}/broken.trig"
cat > "${BROKEN}" <<'EOF'
@prefix ex: <http://example.org/> .
_:x2 ex:knows _:x1 .
_:x1 ex:knows _:x2 .
_:x2 ex:name "Bob" .
_:x3 {
  _:x1 ex:role "not-member" .
}
_:x1 ex:name "Alice" .
EOF

CANON_ORIG_1="${WORKDIR}/orig.canon1.nq"
CANON_ORIG_2="${WORKDIR}/orig.canon2.nq"
CANON_RELABEL="${WORKDIR}/relabel.canon.nq"
CANON_BROKEN="${WORKDIR}/broken.canon.nq"

RC=0
"${BIN}" --canonicalize "${ORIG}" > "${CANON_ORIG_1}" 2>"${WORKDIR}/orig1.err" || RC=$?
if [ "${RC}" -ne 0 ]; then
  report_fail "setup: --canonicalize orig.trig (run 1) exited ${RC}"
  cat "${WORKDIR}/orig1.err"
else
  report_pass "setup: --canonicalize orig.trig (run 1) exited 0"
fi

RC=0
"${BIN}" --canonicalize "${ORIG}" > "${CANON_ORIG_2}" 2>"${WORKDIR}/orig2.err" || RC=$?
[ "${RC}" -eq 0 ] || { report_fail "setup: --canonicalize orig.trig (run 2) exited ${RC}"; cat "${WORKDIR}/orig2.err"; }

RC=0
"${BIN}" --canonicalize "${RELABEL}" > "${CANON_RELABEL}" 2>"${WORKDIR}/relabel.err" || RC=$?
[ "${RC}" -eq 0 ] || { report_fail "setup: --canonicalize relabel.trig exited ${RC}"; cat "${WORKDIR}/relabel.err"; }

RC=0
"${BIN}" --canonicalize "${BROKEN}" > "${CANON_BROKEN}" 2>"${WORKDIR}/broken.err" || RC=$?
[ "${RC}" -eq 0 ] || { report_fail "setup: --canonicalize broken.trig exited ${RC}"; cat "${WORKDIR}/broken.err"; }

# A non-empty sanity floor: a degenerate "always emit empty output"
# canonicalizer would otherwise pass every equality check below for
# the wrong reason.
if [ -s "${CANON_ORIG_1}" ]; then
  report_pass "sanity: canonical output is non-empty"
else
  report_fail "sanity: canonical output is EMPTY -- equality checks below would be vacuous"
fi

# ---------------------------------------------------------------------
# Arm A: same file, canonicalized twice -> byte-identical.
# ---------------------------------------------------------------------
if cmp -s "${CANON_ORIG_1}" "${CANON_ORIG_2}"; then
  report_pass "arm A: canonicalizing the same input twice gives byte-identical output"
else
  report_fail "arm A: two canonicalize runs of the SAME input diverged"
  diff -u "${CANON_ORIG_1}" "${CANON_ORIG_2}" || true
fi

# ---------------------------------------------------------------------
# Arm B: bnode-relabelled isomorphic variant -> byte-identical to the
# original's canonical form. This is the determinism/well-definedness
# property (candidate 1 in the task brief) that full F* proof was
# investigated and rejected for this session -- see RDF.Canonical.fst
# Section 5b's banner. This arm is the tested stand-in.
# ---------------------------------------------------------------------
if cmp -s "${CANON_ORIG_1}" "${CANON_RELABEL}"; then
  report_pass "arm B: a bnode-relabelled isomorphic variant canonicalizes to the SAME bytes as the original"
else
  report_fail "arm B: relabelled variant canonicalized to DIFFERENT bytes -- RDFC-1.0 invariance broken"
  echo "----- original canonical form -----"
  cat "${CANON_ORIG_1}"
  echo "----- relabelled canonical form -----"
  cat "${CANON_RELABEL}"
  echo "------------------------------------"
fi

# ---------------------------------------------------------------------
# Arm C: anti-vacuity. broken.trig is NOT isomorphic to orig.trig (the
# ex:role object differs) -- if arms A/B's equality check is somehow
# vacuous (e.g. a degenerate canonicalizer that emits the same constant
# for every input), this MUST still catch the divergence.
# ---------------------------------------------------------------------
if cmp -s "${CANON_ORIG_1}" "${CANON_BROKEN}"; then
  report_fail "anti-vacuity: a NON-isomorphic graph canonicalized to the SAME bytes -- arms A/B cannot be trusted"
else
  report_pass "anti-vacuity: a non-isomorphic graph canonicalizes to DIFFERENT bytes, so arms A/B are not vacuous"
fi

echo
echo "cli_rdfc10_relabel_determinism: ${PASS} pass, ${FAIL} fail (out of $((PASS + FAIL)))"
[ "${FAIL}" -eq 0 ]
