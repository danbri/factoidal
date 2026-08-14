#!/usr/bin/env bash
# Regression for issue #334's TriG follow-up: the TriG load path (both
# RDF 1.1 and --rdf12) silently drops a statement that uses an
# undeclared prefix, instead of reporting a parse error. Same defect
# class as #424 (which fixed the Turtle RDF 1.1 path) but the CLI's
# TriG branch in load_dataset called the always-succeeds
# parse_trig_with_base_lenient(_12) / parse_trig_lenient, which never
# even looked at trig_parse_state.has_error, let alone a position.
#
# Repro (same three-statement shape as #424's fixture): a TriG document
# where the middle statement uses a prefix ("bad:") that was never
# declared via @prefix. Before this fix, `factoidal --dump` on this
# file silently dropped the middle statement and exited 0 with the
# other two triples printed -- no diagnostic anywhere, in EITHER mode.

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

run_case() {
  local label="$1" extra_flag="$2"

  local fixture="${WORKDIR}/undeclared-prefix-mid-doc-${label}.trig"
  cat > "${fixture}" <<'EOF'
@prefix ex: <http://example.org/> .
ex:s1 ex:p1 "ok-before" .
bad:s2 ex:p2 "should-error-undeclared-prefix" .
ex:s3 ex:p3 "ok-after" .
EOF

  local stdout_out="${WORKDIR}/${label}-stdout.txt"
  local stderr_out="${WORKDIR}/${label}-stderr.txt"
  if [[ -n "${extra_flag}" ]]; then
    timeout 30 "${BIN}" ${extra_flag} --dump --data "${fixture}" >"${stdout_out}" 2>"${stderr_out}"
  else
    timeout 30 "${BIN}" --dump --data "${fixture}" >"${stdout_out}" 2>"${stderr_out}"
  fi
  local rc=$?
  local stdout_content="$(cat "${stdout_out}")"
  local stderr_content="$(cat "${stderr_out}")"

  check "${label}-undeclared-prefix-nonzero-exit" "1" "${rc}"
  check_contains "${label}-undeclared-prefix-error-names-prefix" "bad" "${stderr_content}"
  check_contains "${label}-undeclared-prefix-error-has-position" "byte" "${stderr_content}"
  check_not_contains "${label}-undeclared-prefix-no-silent-partial-output" "ok-before" "${stdout_content}"

  # Control: well-formed TriG document must still parse cleanly.
  local good_fixture="${WORKDIR}/well-formed-${label}.trig"
  cat > "${good_fixture}" <<'EOF'
@prefix ex: <http://example.org/> .
ex:s1 ex:p1 "ok-1" .
ex:s2 ex:p2 "ok-2" .
EOF
  local good_stdout="${WORKDIR}/${label}-good-stdout.txt"
  if [[ -n "${extra_flag}" ]]; then
    timeout 30 "${BIN}" ${extra_flag} --dump --data "${good_fixture}" >"${good_stdout}" 2>"${WORKDIR}/${label}-good-stderr.txt"
  else
    timeout 30 "${BIN}" --dump --data "${good_fixture}" >"${good_stdout}" 2>"${WORKDIR}/${label}-good-stderr.txt"
  fi
  local good_rc=$?
  check "${label}-well-formed-still-exits-zero" "0" "${good_rc}"
  check_contains "${label}-well-formed-still-emits-both-triples" "ok-2" "$(cat "${good_stdout}")"
}

run_case "trig11" ""
run_case "trig12" "--rdf12"

echo ""
echo "trig_undeclared_prefix_regression: ${pass_count} pass, ${fail_count} fail (out of $((pass_count + fail_count)))"
if [[ "${fail_count}" -gt 0 ]]; then
  exit 1
fi
exit 0
