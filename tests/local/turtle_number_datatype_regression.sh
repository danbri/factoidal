#!/usr/bin/env bash
# Regression for issue #425: two real bugs in the Turtle number-literal
# classifier (Parser.Turtle.fst parse_numeric_literal), found by the
# Jena differential harness (PR #427).
#
# BUG A — wrong datatype: a number with a leading dot and NO exponent
# (".1", "+.7") was tagged xsd:double. Per the Turtle grammar, a number
# with a dot and no exponent is DECIMAL. Root cause: the leading-dot
# branch of parse_numeric_literal called collect_num with the has_dot
# and has_e accumulator arguments swapped (has_e primed to true before
# any exponent had been seen), so every leading-dot number came out
# DOUBLE regardless of whether an exponent was present.
# Witnesses: turtle-syntax-number-05.ttl, turtle-syntax-number-13.ttl.
#
# BUG B — wrong rejection: "123.E+1" and "-.2e3" were REJECTED as
# invalid syntax. Both are legal DOUBLE per the grammar (DOUBLE allows
# digits '.' digits* EXPONENT — zero fractional digits before the
# exponent is fine — and '.' digits+ EXPONENT). Root cause: (1) the
# digit-dot-EXPONENT case never looked past the dot when the next
# character was 'e'/'E' rather than a digit, so "123." stopped short
# and left "E+1" dangling; (2) the has_e/has_dot swap from Bug A also
# meant a leading-dot number's real exponent character was never
# recognized as an exponent (has_e was already — wrongly — true).
# Witnesses: turtle-syntax-number-11.ttl, turtle-syntax-number-12.ttl.
#
# THE THIRD THING (why the W3C suite reported 100% anyway): these four
# files are rdft:TestTurtlePositiveSyntax entries in
# third_party/testing/w3c/rdf/rdf11/rdf-turtle/manifest.ttl. That test
# type has no mf:result / expected-output file — the manifest only
# asserts the input parses successfully, never what datatype comes
# out. Worse, bin/w3c-runner/w3c_runner.ml grades
# "TestTurtlePositiveSyntax" by calling parse_turtle_fstar — the
# LENIENT wrapper (Parser_Turtle.parse_turtle_with_base), documented
# in the runner itself as "always-succeeds" — not the strict parser
# the `factoidal dump` CLI uses. So Bug A produced no failure (lenient
# parse always "succeeds", and the test never inspects the datatype),
# and Bug B also produced no failure: the lenient entry point recovers
# from the same dead end differently than the strict one and still
# returns a result, so `ignore (parse_turtle_fstar ...); Pass` never
# throws. The 100% score was real for "does not crash" and silent for
# "produces the right term" — a harness-coverage gap, not evidence the
# classifier was correct.
#
# This regression checks resulting datatype directly via `factoidal
# dump`, which goes through the strict/diagnostic parser path.

set -u

ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
BIN="${FACTOIDAL_BIN:-${ROOT}/bin/linux-x86_64/factoidal}"
WORKDIR="$(mktemp -d)"
trap 'rm -rf "${WORKDIR}"' EXIT

if [[ ! -x "${BIN}" ]]; then
  echo "SKIP: no binary at ${BIN} (build not yet run)"
  exit 0
fi

pass_count=0
fail_count=0

check_contains() {
  local name="$1" needle="$2" haystack="$3"
  if [[ "${haystack}" == *"${needle}"* ]]; then
    echo "PASS ${name}"
    pass_count=$((pass_count + 1))
  else
    echo "FAIL ${name}: '${needle}' not found in: ${haystack}"
    fail_count=$((fail_count + 1))
  fi
}

check_exit_zero() {
  local name="$1" rc="$2" out="$3"
  if [[ "${rc}" == "0" ]]; then
    echo "PASS ${name}"
    pass_count=$((pass_count + 1))
  else
    echo "FAIL ${name}: expected exit 0, got ${rc}; output: ${out}"
    fail_count=$((fail_count + 1))
  fi
}

# run_case NAME TTL_BODY EXPECTED_DATATYPE_SUFFIX
run_case() {
  local name="$1" body="$2" expected_dt="$3"
  local fixture="${WORKDIR}/${name}.ttl"
  printf '%s\n' "${body}" > "${fixture}"
  local out err rc
  out="${WORKDIR}/${name}.out"
  err="${WORKDIR}/${name}.err"
  timeout 30 "${BIN}" dump "${fixture}" >"${out}" 2>"${err}"
  rc=$?
  local stdout_content
  stdout_content="$(cat "${out}")"
  local stderr_content
  stderr_content="$(cat "${err}")"
  check_exit_zero "${name}-parses" "${rc}" "${stderr_content}"
  check_contains "${name}-datatype-${expected_dt}" "^^<http://www.w3.org/2001/XMLSchema#${expected_dt}>" "${stdout_content}"
}

# --- Bug A: leading dot, no exponent => DECIMAL, not DOUBLE ---------
run_case "bug-a-dot-1" '<http://example/s> <http://example/p> .1 .' "decimal"
run_case "bug-a-plus-dot-7" '<http://example/s> <http://example/p> +.7 .' "decimal"

# --- Bug B: digit-dot-EXPONENT and dot-digit-EXPONENT => DOUBLE, accepted
run_case "bug-b-123-dot-e-plus-1" '<http://example/s> <http://example/p> 123.E+1 .' "double"
run_case "bug-b-minus-dot-2-e-3" '<http://example/s> <http://example/p> -.2e3 .' "double"

# --- Controls: must not change ---------------------------------------
run_case "control-integer-1" '<http://example/s> <http://example/p> 1 .' "integer"
run_case "control-decimal-1-0" '<http://example/s> <http://example/p> 1.0 .' "decimal"
run_case "control-double-1e0" '<http://example/s> <http://example/p> 1e0 .' "double"
run_case "control-negative-integer" '<http://example/s> <http://example/p> -5 .' "integer"
run_case "control-plus-decimal" '<http://example/s> <http://example/p> +3.14 .' "decimal"
run_case "control-decimal-with-exp" '<http://example/s> <http://example/p> 1.0e10 .' "double"

echo ""
echo "turtle_number_datatype_regression: ${pass_count} pass, ${fail_count} fail (out of $((pass_count + fail_count)))"
if [[ "${fail_count}" -gt 0 ]]; then
  exit 1
fi
exit 0
