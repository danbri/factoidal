#!/usr/bin/env bash
# Regression: `factoidal graphs list|get|hash|diff` (the slice-1
# graphs-first CLI surface, in-memory only).
# docs/designissues/2026-07-05-graphs-api-design.md section 4.
#
# NOTE: this exercises the FIXED subcommand ("graphs") added to
# bin/factoidal-cli/factoidal_cli.ml plus RDF.Dataset.Graphs.fst /
# RDF.Canonical.canonicalize_named_graph. It only passes once the
# committed `factoidal` binary has been rebuilt from those sources
# (formal/fstar/build-ocaml.sh extract && compile) — running it
# against a pre-existing binary that predates this change will FAIL
# with "unknown subcommand" or similar, which is expected until the
# rebuild lands.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
BIN="${FACTOIDAL_BIN:-${ROOT}/formal/fstar/ocaml-output/factoidal}"
WORKDIR="$(mktemp -d)"
trap 'rm -rf "${WORKDIR}"' EXIT

pass_count=0
fail_count=0
check () {
  local name="$1" expected="$2" actual="$3"
  if [[ "${actual}" == "${expected}" ]]; then
    echo "PASS ${name}"
    pass_count=$((pass_count + 1))
  else
    echo "FAIL ${name}: expected [${expected}] got [${actual}]"
    fail_count=$((fail_count + 1))
  fi
}

# Fixture: default graph (1 triple) + two named graphs (2 + 1 triples).
cat > "${WORKDIR}/data.nq" <<'EOF'
<http://x.org/a1> <http://x.org/p> "1" <http://x.org/g/one> .
<http://x.org/a2> <http://x.org/p> "2" <http://x.org/g/one> .
<http://x.org/b1> <http://x.org/p> "3" <http://x.org/g/two> .
<http://x.org/d1> <http://x.org/p> "4" .
EOF

# g/one's triples alone, as a standalone default-graph document — the
# by-hand equivalent of `component_of dataset "http://x.org/g/one"`.
cat > "${WORKDIR}/g_one_extracted.nq" <<'EOF'
<http://x.org/a1> <http://x.org/p> "1" .
<http://x.org/a2> <http://x.org/p> "2" .
EOF

# --- graphs list: both named graphs, default graph excluded ---
list_out="$("${BIN}" graphs list "${WORKDIR}/data.nq")"
list_sorted="$(printf '%s\n' "${list_out}" | sort | paste -sd, -)"
check "list-both-named-graphs" "http://x.org/g/one,http://x.org/g/two" "${list_sorted}"

# --- graphs get: round-trips the right triple count ---
get_out="$("${BIN}" graphs get "${WORKDIR}/data.nq" "http://x.org/g/one")"
# awk (not grep -c) so a zero-match count doesn't trip `set -e` via a
# non-zero exit code — the count itself, not the exit status, is the
# assertion here.
get_count="$(printf '%s\n' "${get_out}" | awk '/^</{c++} END{print c+0}')"
check "get-triple-count" "2" "${get_count}"

get_unknown_rc=0
"${BIN}" graphs get "${WORKDIR}/data.nq" "http://x.org/no-such-graph" \
  >"${WORKDIR}/get_unknown.out" 2>&1 || get_unknown_rc=$?
check "get-unknown-graph-exits-nonzero" "1" "${get_unknown_rc}"

# --- graphs hash: equals `canonicalize` of the graph extracted by hand ---
hash_out="$("${BIN}" graphs hash "${WORKDIR}/data.nq" "http://x.org/g/one")"
canon_extracted="$("${BIN}" canonicalize "${WORKDIR}/g_one_extracted.nq")"
check "hash-equals-canonicalize-of-extracted-graph" "${canon_extracted}" "${hash_out}"

# --- graphs hash: stable under blank-node relabeling (content-addressing) ---
cat > "${WORKDIR}/bnodeA.nq" <<'EOF'
_:x <http://x.org/p> _:y <http://x.org/g/bn> .
_:y <http://x.org/p> "leaf" <http://x.org/g/bn> .
EOF
cat > "${WORKDIR}/bnodeB.nq" <<'EOF'
_:n1 <http://x.org/p> _:n2 <http://x.org/g/bn> .
_:n2 <http://x.org/p> "leaf" <http://x.org/g/bn> .
EOF
hash_bn_a="$("${BIN}" graphs hash "${WORKDIR}/bnodeA.nq" "http://x.org/g/bn")"
hash_bn_b="$("${BIN}" graphs hash "${WORKDIR}/bnodeB.nq" "http://x.org/g/bn")"
check "hash-stable-under-bnode-relabeling" "${hash_bn_a}" "${hash_bn_b}"

# --- graphs diff: a dataset against itself is empty ---
diff_self="$("${BIN}" graphs diff "${WORKDIR}/data.nq" "${WORKDIR}/data.nq")"
check "diff-self-is-empty" "" "${diff_self}"

# --- graphs diff: detects an added graph and a changed graph ---
cat > "${WORKDIR}/data_modified.nq" <<'EOF'
<http://x.org/a1> <http://x.org/p> "1" <http://x.org/g/one> .
<http://x.org/a2> <http://x.org/p> "2-changed" <http://x.org/g/one> .
<http://x.org/b1> <http://x.org/p> "3" <http://x.org/g/two> .
<http://x.org/c1> <http://x.org/p> "5" <http://x.org/g/three> .
<http://x.org/d1> <http://x.org/p> "4" .
EOF
diff_out="$("${BIN}" graphs diff "${WORKDIR}/data.nq" "${WORKDIR}/data_modified.nq")"
check "diff-reports-added-graph" "true" \
  "$(printf '%s\n' "${diff_out}" | grep -qxF '+ http://x.org/g/three' && echo true || echo false)"
check "diff-reports-changed-graph" "true" \
  "$(printf '%s\n' "${diff_out}" | grep -qxF '~ http://x.org/g/one' && echo true || echo false)"
check "diff-does-not-report-unchanged-graph" "false" \
  "$(printf '%s\n' "${diff_out}" | grep -qF 'http://x.org/g/two' && echo true || echo false)"

echo "pass=${pass_count} fail=${fail_count}"
if [[ "${fail_count}" -ne 0 ]]; then
  exit 1
fi
