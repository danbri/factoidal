#!/usr/bin/env bash
# Regression for issue #334's Turtle Mode 1.2 follow-up: the --rdf12
# Turtle load path silently drops a statement that uses an undeclared
# prefix, instead of reporting a parse error. Same defect class as
# #424 (which fixed the RDF 1.1 path via parse_turtle_diagnostic /
# parse_turtle_with_base_diagnostic) but the CLI's rdf12_mode branch
# in load_dataset still calls the always-succeeds parse_turtle_12 /
# parse_turtle_with_base_12, which has no error channel at all.
#
# Repro (same three-statement shape as #424's fixture): a Turtle
# document where the middle statement uses a prefix ("bad:") that was
# never declared via @prefix. Before this fix, `factoidal --rdf12
# --dump` silently dropped the middle statement and exited 0 with the
# other two triples printed -- no diagnostic anywhere.

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

check_not_contains() {
  local name="$1" needle="$2" haystack="$3"
  if [[ "${haystack}" != *"${needle}"* ]]; then
    echo "PASS ${name}"
    pass_count=$((pass_count + 1))
  else
    echo "FAIL ${name}: '${needle}' unexpectedly found in: ${haystack}"
    fail_count=$((fail_count + 1))
  fi
}

# --- Fixture: undeclared prefix mid-document (RDF 1.2 mode) --------
fixture="${WORKDIR}/undeclared-prefix-mid-doc-12.ttl"
cat > "${fixture}" <<'EOF'
@prefix ex: <http://example.org/> .
ex:s1 ex:p1 "ok-before" .
bad:s2 ex:p2 "should-error-undeclared-prefix" .
ex:s3 ex:p3 "ok-after" .
EOF

stdout_out="${WORKDIR}/stdout.txt"
stderr_out="${WORKDIR}/stderr.txt"
timeout 30 "${BIN}" --rdf12 --dump --data "${fixture}" >"${stdout_out}" 2>"${stderr_out}"
rc=$?
stdout_content="$(cat "${stdout_out}")"
stderr_content="$(cat "${stderr_out}")"

# Contract: the document must FAIL outright (undeclared prefix is a
# syntax error per Turtle 1.1/1.2 Sec 6), not silently succeed with
# the offending statement dropped.
check "rdf12-undeclared-prefix-nonzero-exit" "1" "${rc}"

# The error must name the bad prefix and carry position information.
check_contains "rdf12-undeclared-prefix-error-names-prefix" "bad" "${stderr_content}"
check_contains "rdf12-undeclared-prefix-error-has-position" "byte" "${stderr_content}"

# Must not silently emit a partial/successful-looking triple stream.
check_not_contains "rdf12-undeclared-prefix-no-silent-partial-output" "ok-before" "${stdout_content}"

# --- Control: well-formed document must still parse cleanly (1.2) --
good_fixture="${WORKDIR}/well-formed-12.ttl"
cat > "${good_fixture}" <<'EOF'
@prefix ex: <http://example.org/> .
ex:s1 ex:p1 "ok-1" .
ex:s2 ex:p2 "ok-2" .
EOF
good_stdout="${WORKDIR}/good-stdout.txt"
timeout 30 "${BIN}" --rdf12 --dump --data "${good_fixture}" >"${good_stdout}" 2>"${WORKDIR}/good-stderr.txt"
good_rc=$?
check "rdf12-well-formed-still-exits-zero" "0" "${good_rc}"
check_contains "rdf12-well-formed-still-emits-both-triples" "ok-2" "$(cat "${good_stdout}")"

echo ""
echo "turtle_rdf12_undeclared_prefix_regression: ${pass_count} pass, ${fail_count} fail (out of $((pass_count + fail_count)))"
if [[ "${fail_count}" -gt 0 ]]; then
  exit 1
fi
exit 0
