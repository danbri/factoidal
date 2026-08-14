#!/usr/bin/env bash
# Regression for issue #334's manifest-loader follow-up: w3c_runner's
# read_manifest() used to call ONLY the always-succeeds parse_turtle_fstar
# (lenient), so a manifest.ttl with a statement-level parse error (e.g.
# an undeclared prefix) had that statement silently dropped -- no
# diagnostic anywhere, exit 0, the manifest just looked well-formed and
# quietly discovered fewer test cases than it should have.
#
# Real-world confirmation: third_party/testing/w3c/rdf/rdf12/rdf-semantics/
# manifest.ttl line 247 has exactly this defect -- an undeclared `test:`
# prefix (a typo for `rdft:`, per the identical `rdft:approval
# rdft:NotClassified` lines earlier in the same file) that silently drops
# one metadata triple with no signal at all.
#
# Policy choice: LENIENT-WITH-REPORT, not strict-with-report. Made
# strict, that one-line vendored-fixture typo would zero out an entire
# manifest's test cases over a defect we do not control upstream -- the
# harness's job is to surface OUR engine's defects, not amplify a
# fixture typo into "N tests vanished". So the fix prints the error
# (message + byte position) to stderr UNCONDITIONALLY (not just
# --verbose) and continues with the well-formed subset, same as before.
#
# This regression uses a throwaway suite directory placed under the
# real third_party/testing/w3c/rdf/rdf11 search root (w3c_runner's
# suite-name argument bypasses the fixed suite whitelist, so an
# arbitrary directory name works) -- created and removed by this
# script, never committed.

set -u

ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
RUNNER="${W3C_RUNNER_BIN:-${ROOT}/bin/linux-x86_64/w3c_runner}"
SCRATCH_NAME="rdf11-scratch-334-manifest-regression"
SCRATCH_DIR="${ROOT}/third_party/testing/w3c/rdf/rdf11/${SCRATCH_NAME}"
cleanup() { rm -rf "${SCRATCH_DIR}"; }
trap cleanup EXIT

if [[ ! -x "${RUNNER}" ]]; then
  echo "SKIP: no binary at ${RUNNER} (build not yet run)"
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
  local name="$1" needle="$2" haystack="$3"
  if [[ "${haystack}" == *"${needle}"* ]]; then
    echo "PASS ${name}"
    pass_count=$((pass_count + 1))
  else
    echo "FAIL ${name}: '${needle}' not found in: ${haystack}"
    fail_count=$((fail_count + 1))
  fi
}

# --- Fixture: a manifest with one well-formed test entry PLUS an
#     unrelated statement that uses an undeclared prefix -----------
cleanup
mkdir -p "${SCRATCH_DIR}"
cat > "${SCRATCH_DIR}/manifest.ttl" <<'EOF'
@prefix rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#> .
@prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .
@prefix mf:   <http://www.w3.org/2001/sw/DataAccess/tests/test-manifest#> .
@prefix rdft: <http://www.w3.org/ns/rdftest#> .

<> rdf:type mf:Manifest ;
   rdfs:label "Regression scratch manifest (#334)" ;
   mf:assumedTestBase <https://example.org/scratch-334/> ;
   mf:entries
   ( <#good_test> ) .

<#good_test> rdf:type rdft:TestTurtleEval ;
   mf:name "good_test" ;
   rdfs:comment "well-formed test entry, should still be discovered" ;
   rdft:approval rdft:Approved ;
   mf:action <good_test.ttl> ;
   mf:result <good_test.nt> ;
   .

bad:unrelated_undeclared_prefix_statement rdf:type mf:Manifest .
EOF
cat > "${SCRATCH_DIR}/good_test.ttl" <<'EOF'
@prefix ex: <http://example.org/> .
ex:s ex:p "o" .
EOF
cat > "${SCRATCH_DIR}/good_test.nt" <<'EOF'
<http://example.org/s> <http://example.org/p> "o" .
EOF

stdout_out="$(mktemp)"
stderr_out="$(mktemp)"
trap 'cleanup; rm -f "${stdout_out}" "${stderr_out}"' EXIT
( cd "${ROOT}" && timeout 30 "${RUNNER}" --rdf "${SCRATCH_NAME}" >"${stdout_out}" 2>"${stderr_out}" )
rc=$?
stdout_content="$(cat "${stdout_out}")"
stderr_content="$(cat "${stderr_out}")"

# Contract: the loader must REPORT the error -- not swallow it.
check_contains "manifest-warning-names-bad-prefix" "bad" "${stderr_content}"
check_contains "manifest-warning-has-position" "byte offset" "${stderr_content}"
check_contains "manifest-warning-names-the-file" "manifest.ttl" "${stderr_content}"

# Contract: LENIENT -- the well-formed test entry is still discovered
# and still passes; one bad unrelated statement must not zero out the
# whole manifest.
check "well-formed-entry-still-discovered" "0" "${rc}"
check_contains "well-formed-entry-still-passes" "PASS: good_test" "${stdout_content}"
check_contains "well-formed-entry-total-is-one" "TOTAL: 1 pass, 0 fail" "${stdout_content}"

echo ""
echo "manifest_loader_undeclared_prefix_regression: ${pass_count} pass, ${fail_count} fail (out of $((pass_count + fail_count)))"
if [[ "${fail_count}" -gt 0 ]]; then
  exit 1
fi
exit 0
