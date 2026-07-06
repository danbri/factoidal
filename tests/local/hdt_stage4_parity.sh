#!/usr/bin/env bash
# HDT program plan stage 4 (docs/designissues/2026-07-06-hdt-program-
# plan.md) parity regression: `factoidal --data-hdt FIXTURE.hdt`
# answers byte-identically to the same query over the fixture's
# ground-truth .nt loaded in-memory via plain `--data`.
#
# Fixture: third_party/testing/hdt/rml-core-ontology.hdt (343
# triples), the same vendored fixture bin/hdt-probe/check.sh pins
# stages 1-3 against; ground truth is the rml-core ontology submodule
# source .nt that generated it (see third_party/testing/hdt/README.md
# for fixture provenance).
#
# Coverage (per the stage 4 acceptance criteria): unbound scan,
# bound-S, bound-P, bound-O, ASK, COUNT. Query text lives in
# tests/local/sparql/hdt_stage4_*.rq so this script stays a thin
# runner, same shape as backend_parity_regressions.sh.
#
# Per CLAUDE.md rule #14, no failure is swallowed; per rule #25 the
# summary is worded, not a bare ratio.

set -uo pipefail

ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
BIN="${ROOT}/formal/fstar/ocaml-output/factoidal"
FIXTURE="${ROOT}/third_party/testing/hdt/rml-core-ontology.hdt"
GROUND_TRUTH="${ROOT}/third_party/testing/rml-modules/rml-core/ontology/documentation/ontology.nt"
SPARQL_DIR="${ROOT}/tests/local/sparql"

if [[ ! -x "${BIN}" ]]; then
  echo "ERROR: factoidal binary not found at ${BIN} (build it first: formal/fstar/build-ocaml.sh compile)" >&2
  exit 2
fi
if [[ ! -f "${FIXTURE}" ]]; then
  echo "ERROR: HDT fixture not found: ${FIXTURE}" >&2
  exit 2
fi
if [[ ! -f "${GROUND_TRUTH}" ]]; then
  echo "ERROR: ground-truth .nt not found: ${GROUND_TRUTH} (rml-modules/rml-core submodule not initialized? git submodule update --init third_party/testing/rml-modules/rml-core)" >&2
  exit 2
fi

PASS=0
FAIL=0

# The one non-semantic difference between the two backends: the
# in-memory dataset loader renames every file's blank-node labels
# with a per-file prefix ("d0_" for the first --data file, see
# factoidal_cli.ml's load path) to prevent cross-file label
# collisions, while the HDT dictionary carries the fixture's original
# labels ("_:genid1"). Blank-node labels are arbitrary identifiers
# per RDF 1.1 Concepts section 3.4, so parity here is byte-identity
# AFTER stripping that documented loader prefix from the in-memory
# side; every IRI, literal, and row order stays compared
# byte-for-byte. Output format is CSV (-o csv) rather than the padded
# table, because the table pads columns to the widest cell and the
# pre-normalization "_:d0_" labels would leave a two-space width
# artifact behind in an otherwise identical answer.
normalize_bnodes() {
  sed 's/_:d0_/_:/g' "$1"
}

run_pair() { # run_pair <name> <query-file>
  local name="$1" query="$2"
  local plain_out hdt_out plain_err hdt_err
  plain_out="$(mktemp)"; hdt_out="$(mktemp)"
  plain_err="$(mktemp)"; hdt_err="$(mktemp)"

  timeout 120 "${BIN}" --data "${GROUND_TRUTH}" -o csv --query "${query}" >"${plain_out}.raw" 2>"${plain_err}"
  local plain_rc=$?
  timeout 120 "${BIN}" --data-hdt "${FIXTURE}" -o csv --query "${query}" >"${hdt_out}" 2>"${hdt_err}"
  local hdt_rc=$?
  normalize_bnodes "${plain_out}.raw" >"${plain_out}"
  rm -f "${plain_out}.raw"

  if [[ $plain_rc -ne 0 ]]; then
    echo "  FAIL  ${name} (in-memory backend exited rc=${plain_rc})"
    cat "${plain_err}"
    FAIL=$((FAIL + 1))
  elif [[ $hdt_rc -ne 0 ]]; then
    echo "  FAIL  ${name} (HDT backend exited rc=${hdt_rc})"
    cat "${hdt_err}"
    FAIL=$((FAIL + 1))
  elif ! cmp -s "${plain_out}" "${hdt_out}"; then
    echo "  FAIL  ${name} (stdout differs)"
    echo "  --- in-memory stdout ---"
    sed 's/^/    /' "${plain_out}"
    echo "  --- HDT stdout ---"
    sed 's/^/    /' "${hdt_out}"
    FAIL=$((FAIL + 1))
  else
    echo "  ok    ${name}"
    PASS=$((PASS + 1))
  fi

  rm -f "${plain_out}" "${hdt_out}" "${plain_err}" "${hdt_err}"
}

echo "--- HDT stage 4 backend parity: rml-core-ontology.hdt vs ontology.nt ---"
run_pair "unbound scan"  "${SPARQL_DIR}/hdt_stage4_unbound.rq"
run_pair "bound-S"       "${SPARQL_DIR}/hdt_stage4_bound_s.rq"
run_pair "bound-P"       "${SPARQL_DIR}/hdt_stage4_bound_p.rq"
run_pair "bound-O"       "${SPARQL_DIR}/hdt_stage4_bound_o.rq"
run_pair "ASK"           "${SPARQL_DIR}/hdt_stage4_ask.rq"
run_pair "COUNT"         "${SPARQL_DIR}/hdt_stage4_count.rq"

echo "============================================================"
TOTAL=$((PASS + FAIL))
echo "hdt-stage4 parity: ${PASS} pass, ${FAIL} fail (out of ${TOTAL})"
[[ $FAIL -eq 0 ]]
