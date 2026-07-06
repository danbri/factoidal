#!/usr/bin/env bash
# tests/local/cottas_wasm_parity_regressions.sh
#
# Pins the fix for the wasm_of_ocaml COTTAS/Parquet gap: until
# 2026-07-06, EVERY on-disk `factoidal query --data-cottas FILE` under
# wasm_of_ocaml (docs/fstar-extracted/factoidal.wasm.js) failed with
# `Invalid_argument("Uint32.of_string")` -- FStar_UInt32's OCaml
# realization is Stdint.Uint32, and wasm_of_ocaml had no Wasm-level
# binding for the `uint32_*` primitives Stdint's C stubs (native) /
# ../fstar_int_stubs.js (js_of_ocaml) realize. Fixed by
# formal/fstar/ocaml-output/wasm_runtime/stdint_uint32_runtime.wat
# (hand-written, mirrors how zarith_runtime.wat already closes the
# same class of gap for Zarith's `ml_z_*`) -- see that file's header
# for the full rationale.
#
# This script proves the fix on the REAL on-disk `--data-cottas` path
# (not just the in-memory bytes-store ABI npm/factoidal/test/cottas-
# bytes-store-wasm.test.js already pins): builds a small COTTAS
# artifact via the npm package's own toCottas writer (no pycottas/
# DuckDB dependency -- same on-disk format, lighter to stand up here),
# writes it to a real file, then runs SELECT/GRAPH/ASK queries through
# BOTH the native `factoidal` binary and the wasm_of_ocaml
# `factoidal.wasm.js` bundle against that SAME file and diffs the JSON
# output byte-for-byte.
#
# Note: the pre-existing checked-in fixture
# tests/unit/fixtures/store_capabilities_sample.cottas has Zstd-
# compressed pages and hits a SEPARATE, still-open wasm_of_ocaml gap
# (`caml_parquet_zstd_decompress_hex` is also identity-shimmed, same
# family as the documented SHA/digestif gap in build-ocaml.sh's own
# header) -- see npm/factoidal/test/cottas-bytes-store-wasm.test.js's
# header comment. This script's freshly-written artifact is
# uncompressed, so it exercises the now-fixed Stdint/u32 path without
# tripping over that separate gap.
#
# Per CLAUDE.md rule #17 every external process is bounded; rule #14
# no `|| true` swallowing exit codes; rule #25 the summary spells out
# N/N/N in words.

set -uo pipefail

ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
cd "${ROOT}"

if ! command -v node >/dev/null 2>&1; then
  echo "SKIP cottas-wasm-parity: node not on PATH"
  exit 0
fi

NODE_MAJOR="$(node -e 'console.log(process.versions.node.split(".")[0])')"
if [[ "${NODE_MAJOR}" -lt 22 ]]; then
  echo "SKIP cottas-wasm-parity: Node ${NODE_MAJOR} < 22 (WasmGC needed)"
  exit 0
fi

NATIVE_BIN="${ROOT}/formal/fstar/ocaml-output/factoidal"
WASM_BUNDLE="${ROOT}/docs/fstar-extracted/factoidal.wasm.js"
NPM_ENTRY="${ROOT}/npm/factoidal/factoidal-npm-entry.js"

if [[ ! -x "${NATIVE_BIN}" ]]; then
  echo "SKIP cottas-wasm-parity: native binary missing at ${NATIVE_BIN}"
  exit 0
fi
if [[ ! -f "${WASM_BUNDLE}" ]]; then
  echo "SKIP cottas-wasm-parity: ${WASM_BUNDLE} missing (run 'build-ocaml.sh wasm-factoidal')"
  exit 0
fi
if [[ ! -f "${NPM_ENTRY}" ]]; then
  echo "SKIP cottas-wasm-parity: ${NPM_ENTRY} missing (run 'build-ocaml.sh npm')"
  exit 0
fi

TMPDIR="${TMPDIR:-/tmp}"
WORKDIR="$(mktemp -d "${TMPDIR}/factoidal-cottas-wasm-parity-XXXXXX")"
trap 'rm -rf "${WORKDIR}"' EXIT

INPUT_NQ="${ROOT}/tests/local/data/cottas_sample.nq"
ARTIFACT_FILE="${WORKDIR}/sample.cottas"

BUILD_RC=0
node -e "
const fs = require('fs');
const abi = require('${NPM_ENTRY}').factoidalNpmEntry;
const nq = fs.readFileSync('${INPUT_NQ}', 'utf8');
const written = JSON.parse(abi.toCottas(nq));
if (!written.ok) { console.error('toCottas failed: ' + JSON.stringify(written)); process.exit(1); }
if (written.quadCount !== 5) { console.error('unexpected quadCount ' + written.quadCount); process.exit(1); }
fs.writeFileSync('${ARTIFACT_FILE}', Buffer.from(written.cottasHex, 'hex'));
" || BUILD_RC=$?
if [[ ${BUILD_RC} -ne 0 ]]; then
  echo "FAIL cottas-wasm-parity-build-artifact"
  exit 1
fi
if [[ ! -s "${ARTIFACT_FILE}" ]]; then
  echo "FAIL cottas-wasm-parity-build-artifact (empty file)"
  exit 1
fi

run_query() {
  # $1 = engine label (native|wasm), $2 = query
  local engine="$1" query="$2" out rc=0
  if [[ "${engine}" == "native" ]]; then
    out="$(timeout 60 "${NATIVE_BIN}" query --data-cottas "${ARTIFACT_FILE}" -e "${query}" -o json 2>/dev/null)" || rc=$?
  else
    out="$(timeout 60 node "${WASM_BUNDLE}" query --data-cottas "${ARTIFACT_FILE}" -e "${query}" -o json 2>/dev/null)" || rc=$?
  fi
  if [[ ${rc} -ne 0 ]]; then
    echo "FAIL cottas-wasm-parity-${engine}-exit (query: ${query})" >&2
    exit 1
  fi
  printf '%s' "${out}"
}

FAIL_COUNT=0
PASS_COUNT=0

check_pin() {
  # $1 = test name, $2 = query, $3 = expected substring in the native
  # AND wasm output (a value pin, so both backends agreeing on a WRONG
  # answer doesn't slip through as "parity").
  local name="$1" query="$2" expect="$3"
  local native_out wasm_out
  native_out="$(run_query native "${query}")"
  wasm_out="$(run_query wasm "${query}")"
  if [[ "${native_out}" != *"${expect}"* ]]; then
    echo "FAIL cottas-wasm-parity-${name} (native did not contain expected '${expect}')"
    echo "${native_out}"
    FAIL_COUNT=$((FAIL_COUNT + 1))
    return
  fi
  if [[ "${wasm_out}" != *"${expect}"* ]]; then
    echo "FAIL cottas-wasm-parity-${name} (wasm did not contain expected '${expect}')"
    echo "${wasm_out}"
    FAIL_COUNT=$((FAIL_COUNT + 1))
    return
  fi
  if [[ "${native_out}" != "${wasm_out}" ]]; then
    echo "FAIL cottas-wasm-parity-${name} (native/wasm JSON differ)"
    diff <(printf '%s\n' "${native_out}") <(printf '%s\n' "${wasm_out}") || true
    FAIL_COUNT=$((FAIL_COUNT + 1))
    return
  fi
  echo "PASS cottas-wasm-parity-${name}"
  PASS_COUNT=$((PASS_COUNT + 1))
}

check_pin "count-default-graph" \
  'SELECT (COUNT(*) AS ?c) WHERE { ?s ?p ?o }' \
  '"value":"1"'

check_pin "count-named-graphs" \
  'SELECT (COUNT(*) AS ?c) WHERE { GRAPH ?g { ?s ?p ?o } }' \
  '"value":"4"'

check_pin "ask-default-subject" \
  'ASK { <https://example.org/default-subject> <https://example.org/status> "default" }' \
  '"boolean": true'

echo ""
if [[ ${FAIL_COUNT} -ne 0 ]]; then
  echo "cottas-wasm-parity: ${PASS_COUNT} pass, ${FAIL_COUNT} fail (out of $((PASS_COUNT + FAIL_COUNT)))"
  exit 1
fi
echo "cottas-wasm-parity: ${PASS_COUNT} pass, 0 fail (out of ${PASS_COUNT})"
