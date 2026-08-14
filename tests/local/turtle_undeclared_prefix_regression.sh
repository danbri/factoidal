#!/usr/bin/env bash
# Regression for issue #334: Turtle parser silently drops a statement
# that uses an undeclared prefix, instead of reporting a parse error.
#
# Repro (verbatim from the issue): a three-statement Turtle document
# where the middle statement uses a prefix ("bad:") that was never
# declared via @prefix. Before this fix, `factoidal dump` silently
# dropped the middle statement and exited 0 with the other two
# triples printed — no diagnostic anywhere. Turtle 1.1 Sec 6 makes an
# undeclared prefix a syntax error; a document containing one must
# fail, not partially succeed (iron rule #2: RDF semantics/parsing
# are not optional; parsers must not silently drop data).
#
# The W3C turtle-syntax-bad-prefix-* negatives are all single-statement
# files, so a dropped statement there just empties the whole document
# and the negative test still passes for the wrong reason. There is no
# multi-statement fixture in the W3C corpus for this shape, hence this
# local regression (per issue #334's "pin a multi-statement regression
# fixture" task).

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

# --- Fixture: undeclared prefix mid-document -----------------------
fixture="${WORKDIR}/undeclared-prefix-mid-doc.ttl"
cat > "${fixture}" <<'EOF'
@prefix ex: <http://example.org/> .
ex:s1 ex:p1 "ok-before" .
bad:s2 ex:p2 "should-error-undeclared-prefix" .
ex:s3 ex:p3 "ok-after" .
EOF

stdout_out="${WORKDIR}/stdout.txt"
stderr_out="${WORKDIR}/stderr.txt"
timeout 30 "${BIN}" dump "${fixture}" >"${stdout_out}" 2>"${stderr_out}"
rc=$?
stdout_content="$(cat "${stdout_out}")"
stderr_content="$(cat "${stderr_out}")"

# Contract: the document must FAIL outright (undeclared prefix is a
# syntax error per Turtle 1.1 Sec 6), not silently succeed with the
# offending statement dropped.
check "undeclared-prefix-nonzero-exit" "1" "${rc}"

# The error must name the bad prefix and carry position information —
# not just a bare "parse failed".
check_contains "undeclared-prefix-error-names-prefix" "bad" "${stderr_content}"
check_contains "undeclared-prefix-error-has-position" "byte" "${stderr_content}"

# Must not silently emit a partial/successful-looking triple stream —
# the old bug: two triples on stdout, exit 0, nothing on stderr.
check_not_contains "undeclared-prefix-no-silent-partial-output" "ok-before" "${stdout_content}"

# --- Control: well-formed document must still parse cleanly --------
good_fixture="${WORKDIR}/well-formed.ttl"
cat > "${good_fixture}" <<'EOF'
@prefix ex: <http://example.org/> .
ex:s1 ex:p1 "ok-1" .
ex:s2 ex:p2 "ok-2" .
EOF
good_stdout="${WORKDIR}/good-stdout.txt"
timeout 30 "${BIN}" dump "${good_fixture}" >"${good_stdout}" 2>"${WORKDIR}/good-stderr.txt"
good_rc=$?
check "well-formed-still-exits-zero" "0" "${good_rc}"
check_contains "well-formed-still-emits-both-triples" "ok-2" "$(cat "${good_stdout}")"

echo ""
echo "turtle_undeclared_prefix_regression: ${pass_count} pass, ${fail_count} fail (out of $((pass_count + fail_count)))"
if [[ "${fail_count}" -gt 0 ]]; then
  exit 1
fi
exit 0
