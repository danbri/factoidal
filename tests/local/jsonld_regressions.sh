#!/usr/bin/env bash
# JSON-LD (expanded form, Phase 1) regression suite.
#
# Fixtures live in tests/local/data/jsonld/. The w3c_toRdf_NNNN.jsonld
# files are verbatim copies of context-free inputs from the vendored W3C
# suite (third_party/testing/json-ld/tests/toRdf/NNNN-in.jsonld) with
# their NNNN-out.nq siblings (sorted) as .expected.nq; the local_*.jsonld
# fixtures are locally authored to cover scalar typing, empty lists, and
# RFC 8259 string escapes (incl. surrogate pairs).
#
# Comparison is dataset ISOMORPHISM, not textual: both the .jsonld input
# and the .expected.nq sibling are run through `factoidal --canonicalize`
# (RDFC-1.0) and the canonical N-Quads are diffed. That makes the
# comparison independent of blank-node label choices on either side.
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
BIN="${FACTOIDAL_BIN:-${ROOT}/formal/fstar/ocaml-output/factoidal}"
DATA="${ROOT}/tests/local/data/jsonld"
TMPDIR="${TMPDIR:-/tmp}"
WORKDIR="$(mktemp -d "${TMPDIR}/factoidal-jsonld-regression-XXXXXX")"
trap 'rm -rf "${WORKDIR}"' EXIT

if [[ ! -x "${BIN}" ]]; then
  echo "ERROR: factoidal binary not found or not executable: ${BIN}" >&2
  echo "       (build it, or set FACTOIDAL_BIN=/path/to/factoidal)" >&2
  exit 2
fi

pass_count=0
fail_count=0
case_count=0

for input in "${DATA}"/*.jsonld; do
  name="$(basename "${input}" .jsonld)"
  expected="${DATA}/${name}.expected.nq"
  case_count=$((case_count + 1))

  if [[ ! -f "${expected}" ]]; then
    echo "FAIL ${name} (missing expected file: ${expected})"
    fail_count=$((fail_count + 1))
    continue
  fi

  got_canon="${WORKDIR}/${name}.got.nq"
  want_canon="${WORKDIR}/${name}.want.nq"

  GOT_RC=0
  timeout 600 "${BIN}" --canonicalize "${input}" >"${got_canon}" 2>"${WORKDIR}/${name}.got.err" || GOT_RC=$?
  if [[ "${GOT_RC}" -ne 0 ]]; then
    echo "FAIL ${name} (parse/canonicalize of JSON-LD input exited ${GOT_RC})"
    cat "${WORKDIR}/${name}.got.err"
    fail_count=$((fail_count + 1))
    continue
  fi

  WANT_RC=0
  timeout 600 "${BIN}" --canonicalize "${expected}" >"${want_canon}" 2>"${WORKDIR}/${name}.want.err" || WANT_RC=$?
  if [[ "${WANT_RC}" -ne 0 ]]; then
    echo "FAIL ${name} (canonicalize of expected N-Quads exited ${WANT_RC})"
    cat "${WORKDIR}/${name}.want.err"
    fail_count=$((fail_count + 1))
    continue
  fi

  if diff -u "${want_canon}" "${got_canon}" >"${WORKDIR}/${name}.diff"; then
    echo "PASS ${name}"
    pass_count=$((pass_count + 1))
  else
    echo "FAIL ${name} (canonical N-Quads differ; - expected, + got)"
    cat "${WORKDIR}/${name}.diff"
    fail_count=$((fail_count + 1))
  fi
done

echo ""
echo "jsonld regressions: ${pass_count} pass, ${fail_count} fail (out of ${case_count})"
if [[ "${fail_count}" -ne 0 ]]; then
  exit 1
fi
