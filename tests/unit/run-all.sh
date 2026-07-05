#!/bin/bash
# tests/unit/run-all.sh — builds and runs every *.ml test file under
# tests/unit/ against the F*-extracted modules in
# formal/fstar/ocaml-output/.
#
# This suite is distinct from the W3C conformance runner
# (formal/fstar/ocaml-output/w3c_runner) and from the ad-hoc scripts
# in tests/local/. It is intentionally fast: every assertion runs
# natively against the already-extracted .cmx artifacts.
#
# Usage:
#   ./run-all.sh                  # run everything
#   ./run-all.sh utf8_roundtrip   # run a single test (no .ml suffix)
#
# Exit code is 0 iff every assertion in every test file matches its
# expected outcome (PASS or documented expected-FAIL).
#
# Rule anchors:
#   * CLAUDE.md rule #14 — we never use `|| true` to swallow failures;
#     we capture exit codes explicitly so the summary is truthful.
#   * CLAUDE.md rule #16 — we never truncate runner output with tail/head;
#     every per-assertion line is streamed, and the summary goes AT THE
#     END after the full run.
#   * CLAUDE.md rule #25 — the final summary line spells out
#     "N pass, N fail" in words, not a cryptic ratio.

set -uo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
OCAML_OUT="$REPO_ROOT/formal/fstar/ocaml-output"
BUILD_DIR="$SCRIPT_DIR/_build"

if [[ ! -d "$OCAML_OUT" ]]; then
  echo "ERROR: $OCAML_OUT does not exist — run" >&2
  echo "       'cd formal/fstar && ./build-ocaml.sh extract compile' first." >&2
  exit 2
fi

mkdir -p "$BUILD_DIR"

# COMMON_MODULES matches formal/fstar/build-ocaml.sh's list for the
# native binaries. If that list drifts, this one must drift with it.
# Keep them in the same order — some modules (e.g. fstar_pure_hashes
# before SPARQL11_Algebra) have link-order constraints encoded in
# the build script.
COMMON_MODULES=(
  Util_Log
  RDF_Format
  RDF_Graph_Executable
  RDF_List_Helpers
  RDF_Bytes
  RDF_Store_Loader
  Parquet_Footer
  OWL_Vocabulary
  Tableau
  Parser_FastString
  RDF_NQuads_Serialize
  Parser_IRI
  Parser_Combinators
  Parser_TurtleScanner
  Parser_NTriples
  Parser_Turtle
  Parser_NQuads
  Parser_TriG
  Parser_XML
  XML_Wellformedness
  Parser_RDFXML
  Parser_SRX
  Parser_CSVResults
  Parser_JSONResults
  Parser_JSON
  SPARQL11_IRI_Resolve
  SPARQL_JSON_Escape
  JSONLD_Loader
  JSONLD_Context
  JSONLD_Expand
  Parser_JSONLD
  SPARQL_Eval_TimeBudget
  SPARQL_Eval_Limits
  SPARQL_HTTP_Response
  SPARQL_HTTP_Timing
  SPARQL_HTTP_BackendInfo
  SPARQL_HTTP_QueriesIndex
  SPARQL_HTTP_StaticFiles
  SPARQL_HTTP_Admin
  SPARQL_HTTP_Routes
  Parser_Ballyhoo
  Parser_BallyhooBloom
  Parser_BallyhooHDT
  Parser_BallyhooHDTQ
  Parser_BallyhooCOTTAS
  RDF_CottasStore_ColumnSeq
  RDF_CottasStore_PageCache
  RDF_CottasStore_OnDiskIndex
  RDF_CottasStore_DictWriter
  RDF_CottasStore_PresenceBitmap
  RDF_CottasStore_PresenceWriter
  RDF_CottasStore_CompoundPresenceBitmap
  RDF_CottasStore_CompoundPresenceWriter
  RDF_CottasStore_OffsetsWriter
  RDF_CottasStore_LazyDict
  RDF_CottasStore_LazyDictRegistry
  RDF_Store_LazyTermCache
  RDF_Store_HDTTermCacheRegistry
  RDF_Store_Columnar_OffsetIndex
  SPARQL_Plan_Pruning
  SPARQL_Plan_Estimate
  SPARQL_Plan_Loader
  SPARQL_Plan_AccessPath
  RDF_CottasStore
  RDF_CottasStore_OnDiskRuntime
  RDF_CottasInMem
  fstar_pure_hashes
  RDF_Canonical
  RDF_Canonical_Manifest
  SPARQL11_Algebra
  XSD_Datatypes
  RDF_Pretty
  OWL_QueryRewrite
  OWL_QueryEval
  OWL_Tests_Manifest
  RIF_Core_Syntax
  Parser_RIFXML
  RIF_Core_Builtins
  RIF_Core_Translation
  RIF_Core_Eval
  RIF_Core_Tests
  RIF_Core_Conformance
  SPARQL11_Parser
  SHACL_Validation
  SPARQL11_Store
  RDF_Store_Combine
  SPARQL_Protocol
  SPARQL_HTTP_RunQuery
  SPARQL_Update_Sandbox
  SPARQL_Update_Analysis
  SPARQL_Diagnostics
  SPARQL_Explain
  SPARQL_Query_Analysis
  SPARQL_Plan_Explain
  SPARQL_HTTP
  SPARQL_HTTP_Client
  SPARQL_ServiceDescription
  SPARQL_GraphStore
)

# Build the list of .cmx paths + the C stub object (needed to resolve
# caml_parquet_zstd_decompress_hex from Parquet_Footer).
CMX_LIST=()
for m in "${COMMON_MODULES[@]}"; do
  CMX_LIST+=("$OCAML_OUT/$m.cmx")
done
PARQUET_STUB_OBJ="$OCAML_OUT/parquet_zstd_stubs.o"

# Detect libzstd on the host so we can pass -cclib -lzstd if present.
# If zstd is unavailable we still try, since the parquet_zstd_stubs
# object contains only a thin wrapper; the symbol is referenced but
# not executed from our tests.
ZSTD_LIB_FLAGS=()
for dir in /opt/homebrew/lib /opt/homebrew/opt/zstd/lib \
           /usr/local/lib /usr/lib /usr/lib/x86_64-linux-gnu \
           /usr/lib/aarch64-linux-gnu; do
  if [[ -f "$dir/libzstd.a" || -f "$dir/libzstd.so" || -f "$dir/libzstd.dylib" ]]; then
    ZSTD_LIB_FLAGS=(-cclib "-L$dir" -cclib -lzstd)
    break
  fi
done

# Collect test files. Optional filter arg.
FILTER="${1:-}"
shopt -s nullglob
ALL_TESTS=()
for ml in "$SCRIPT_DIR"/*.ml; do
  name="$(basename "$ml" .ml)"
  if [[ -z "$FILTER" || "$name" == "$FILTER" ]]; then
    ALL_TESTS+=("$name")
  fi
done
shopt -u nullglob

if [[ ${#ALL_TESTS[@]} -eq 0 ]]; then
  echo "No unit tests matched filter '${FILTER}'." >&2
  exit 2
fi

TOTAL_FILES=${#ALL_TESTS[@]}
PASS_FILES=0
FAIL_FILES=0

echo "tests/unit runner: ${TOTAL_FILES} file(s) under $SCRIPT_DIR"
echo "                   ocaml-output at $OCAML_OUT"
echo

for name in "${ALL_TESTS[@]}"; do
  ml_file="$SCRIPT_DIR/$name.ml"
  bin_file="$BUILD_DIR/$name"

  echo "--- $name ---"

  # Compile. We use the same ocamlfind + package list as build-ocaml.sh's
  # native binaries. -I $OCAML_OUT so .cmi files are discoverable.
  BUILD_RC=0
  BUILD_OUT=$(ocamlfind ocamlopt \
    -package fstar.lib,str,zarith,sha,digestif.c,unix \
    -linkpkg -w -8-14-26 \
    -I "$OCAML_OUT" \
    "${CMX_LIST[@]}" \
    "$PARQUET_STUB_OBJ" \
    "${ZSTD_LIB_FLAGS[@]}" \
    "$ml_file" \
    -o "$bin_file" 2>&1) || BUILD_RC=$?

  if [[ $BUILD_RC -ne 0 ]]; then
    echo "  BUILD FAILED (rc=$BUILD_RC)"
    echo "$BUILD_OUT" | sed 's/^/    /'
    FAIL_FILES=$((FAIL_FILES + 1))
    echo "$name: FAIL (build)"
    echo
    continue
  fi

  # Run. The test binary itself exits 0 on clean, 1 on any unexpected
  # failure. Stream its output directly — no tail/head truncation.
  RUN_RC=0
  "$bin_file" || RUN_RC=$?

  if [[ $RUN_RC -eq 0 ]]; then
    PASS_FILES=$((PASS_FILES + 1))
    echo "$name: PASS"
  else
    FAIL_FILES=$((FAIL_FILES + 1))
    echo "$name: FAIL (rc=$RUN_RC)"
  fi
  echo
done

echo "============================================================"
echo "tests/unit summary: ${PASS_FILES} file(s) pass, ${FAIL_FILES} file(s) fail (out of ${TOTAL_FILES})"

if [[ $FAIL_FILES -eq 0 ]]; then
  exit 0
else
  exit 1
fi
