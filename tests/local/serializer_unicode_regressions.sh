#!/usr/bin/env bash
# Issue #271: canonicalize + dump-nq must pass non-ASCII literal content
# through as raw UTF-8 (canonical N-Quads does not \u-escape non-ASCII).
# The bug: RDF.Canonical.escape_lit_char / RDF.NQuads.Serialize.escape_char
# emitted pass-through codepoints via string_of_char, whose extracted
# realisation is byte-oriented (Char.chr) — crash above U+00FF, Latin-1
# mojibake for U+0080–U+00FF. Fixture covers both ranges plus an astral
# codepoint (emoji), on both the canonicalize and dump-nq serializers.
set -u

ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
BIN="${FACTOIDAL_BIN:-${ROOT}/formal/fstar/ocaml-output/factoidal}"
DUMP_BIN="${FACTOIDAL_DUMP_NQ_BIN:-${ROOT}/formal/fstar/ocaml-output/factoidal-dump-nq}"
WORKDIR="$(mktemp -d)"
trap 'rm -rf "${WORKDIR}"' EXIT

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

# Literal exercising U+00E9 (2-byte UTF-8), U+2014 (3-byte), U+1F600
# (4-byte, astral — the crash case), plus the chars that MUST be escaped.
printf '<http://ex/s> <http://ex/p> "caf\xc3\xa9 \xe2\x80\x94 \xf0\x9f\x98\x80 tab\\there" .\n' \
  > "${WORKDIR}/uni.nt"
EXPECTED_QUAD='<http://ex/s> <http://ex/p> "café — 😀 tab\there" .'

canon_out="$("${BIN}" canonicalize "${WORKDIR}/uni.nt" 2>&1)"
canon_rc=$?
check "canonicalize-utf8-rc" "0" "${canon_rc}"
check "canonicalize-utf8-passthrough" "${EXPECTED_QUAD}" "${canon_out}"

if [[ -x "${DUMP_BIN}" ]]; then
  dump_out="$("${DUMP_BIN}" "${WORKDIR}/uni.nt" 2>&1)"
  dump_rc=$?
  check "dump-nq-utf8-rc" "0" "${dump_rc}"
  check "dump-nq-utf8-passthrough" "${EXPECTED_QUAD}" "${dump_out}"
else
  echo "SKIP dump-nq checks (no binary at ${DUMP_BIN})"
fi

echo "pass=${pass_count} fail=${fail_count}"
if [[ "${fail_count}" -ne 0 ]]; then
  exit 1
fi
