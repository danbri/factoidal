#!/bin/bash
# Build a bytecode executable for ocamldebug without changing the normal
# extract/compile pipeline.
#
# Usage:
#   cd formal/fstar
#   ./build-ocaml-debug.sh
#   ./build-ocaml-debug.sh factoidal
#   ./build-ocaml-debug.sh factoidal-http
#
# Notes:
# - Assumes extraction has already happened into ocaml-output/.
# - Produces bytecode executables with -g for source-level debugging.
# - Uses the real Parquet/Zstd C stub so COTTAS paths can execute under
#   ocamldebug; this is intentionally different from the js_of_ocaml stub.
# - Default target is the CLI/query path. It deliberately stubs out the
#   `serve` subcommand so the HTTP daemon does not become part of the
#   default debug loop.

set -euo pipefail
cd "$(dirname "$0")"
ROOT_DIR="$(pwd)/../.."

OUTDIR=ocaml-output
TARGET="${1:-factoidal}"

if [[ ! -d "$OUTDIR" ]]; then
  echo "error: $OUTDIR/ is missing. Run './build-ocaml.sh extract' first." >&2
  exit 1
fi

run_with_heartbeat() {
  local label="$1"; shift
  local log="$1"; shift
  if [[ "${1:-}" != "--" ]]; then
    echo "run_with_heartbeat: expected '--' before command" >&2
    return 2
  fi
  shift
  : > "$log"
  "$@" > "$log" 2>&1 &
  local pid=$!
  local t0=$(date +%s)
  while kill -0 "$pid" 2>/dev/null; do
    sleep 30
    kill -0 "$pid" 2>/dev/null || break
    local now=$(date +%s)
    local elapsed=$(( now - t0 ))
    local lines=$(wc -l < "$log" 2>/dev/null | tr -d ' ')
    echo "      …${label} still running (${elapsed}s elapsed, ${lines} log lines)"
  done
  local rc=0
  wait "$pid" || rc=$?
  return "$rc"
}

UNAME_S="$(uname -s)"
UNAME_M="$(uname -m)"
if [[ "$UNAME_S" == "Darwin" && "$UNAME_M" == "arm64" ]]; then
  PLATFORM="darwin-arm64"
elif [[ "$UNAME_S" == "Darwin" && "$UNAME_M" == "x86_64" ]]; then
  PLATFORM="darwin-x86_64"
elif [[ "$UNAME_S" == "Linux" && "$UNAME_M" == "x86_64" ]]; then
  PLATFORM="linux-x86_64"
elif [[ "$UNAME_S" == "Linux" && "$UNAME_M" == "aarch64" ]]; then
  PLATFORM="linux-arm64"
else
  PLATFORM="${UNAME_S,,}-${UNAME_M}"
fi

BINDIR="${ROOT_DIR}/bin/${PLATFORM}"
mkdir -p "$BINDIR"

cd "$OUTDIR"

COMMON_MODULES="RDF_Graph_Executable.ml Parquet_Footer.ml Tableau.ml \
  Parser_FastString.ml Parser_IRI.ml \
  Parser_Combinators.ml Parser_TurtleScanner.ml Parser_NTriples.ml Parser_Turtle.ml \
  Parser_NQuads.ml Parser_TriG.ml Parser_XML.ml Parser_RDFXML.ml \
  Parser_SRX.ml Parser_CSVResults.ml Parser_JSONResults.ml \
  Parser_Ballyhoo.ml Parser_BallyhooBloom.ml \
  Parser_BallyhooHDT.ml Parser_BallyhooHDTQ.ml Parser_BallyhooCOTTAS.ml \
  RDF_CottasStore_PageCache.ml \
  RDF_CottasStore_OnDiskIndex.ml \
  RDF_CottasStore.ml \
  fstar_pure_hashes.ml \
  RDF_Canonical.ml \
  SPARQL11_Algebra.ml OWL_QueryRewrite.ml OWL_QueryEval.ml SPARQL11_Parser.ml SPARQL11_Store.ml SPARQL_Protocol.ml \
  SPARQL_Diagnostics.ml \
  SPARQL_Explain.ml \
  SPARQL_HTTP.ml SPARQL_HTTP_Client.ml SPARQL_ServiceDescription.ml \
  SPARQL_GraphStore.ml"

PARQUET_BYTECODE_STUBS=""
if [[ "${FACTOIDAL_NO_ZSTD:-0}" == "1" ]]; then
  echo "  FACTOIDAL_NO_ZSTD=1 — skipping Parquet/Zstd C stub (COTTAS read limited)"
else
  ZSTD_INC=""
  ZSTD_LIB=""
  for dir in /opt/homebrew/include /opt/homebrew/opt/zstd/include \
             /usr/local/include /usr/include; do
    if [[ -f "$dir/zstd.h" ]]; then ZSTD_INC="-ccopt -I$dir"; break; fi
  done
  for dir in /opt/homebrew/lib /opt/homebrew/opt/zstd/lib \
             /usr/local/lib /usr/lib /usr/lib/x86_64-linux-gnu \
             /usr/lib/aarch64-linux-gnu; do
    if [[ -f "$dir/libzstd.a" || -f "$dir/libzstd.so" || -f "$dir/libzstd.dylib" ]]; then
      ZSTD_LIB="-cclib -L$dir"; break
    fi
  done
  if [[ -n "$ZSTD_INC" ]]; then
    PARQUET_BYTECODE_STUBS="-custom $ZSTD_INC ../experimental_ocaml_glue/parquet_zstd_stubs.c $ZSTD_LIB -cclib -lzstd"
    echo "  Parquet/Zstd bytecode stub: enabled ($ZSTD_INC $ZSTD_LIB -lzstd)"
  else
    echo "  Parquet/Zstd bytecode stub: DISABLED (libzstd headers not found)"
  fi
fi

case "$TARGET" in
  factoidal)
    LOG="_ocamlc_factoidal_debug.log"
    OUT="$BINDIR/factoidal.byte"
    echo "--- Building debug bytecode: factoidal.byte ---"
    # Phase 8 (#200 D, 2026-05-08): factoidal_serve* sources live in
    # bin/factoidal-serve/. Stage the debug variant as factoidal_serve.ml
    # in cwd (so the OCaml `Factoidal_serve` module name matches), then
    # clean up regardless of compile outcome.
    cp ../../../bin/factoidal-serve/factoidal_serve_debug.ml factoidal_serve.ml
    FACTOIDAL_DEBUG_RC=0
    run_with_heartbeat "ocamlc factoidal.byte" "$LOG" -- \
      ocamlfind ocamlc -g -thread -package fstar.lib,str,zarith,sha,digestif.c,unix,threads.posix -linkpkg -w -8-14-26 \
      $PARQUET_BYTECODE_STUBS \
      -I ../../../bin/factoidal-explain \
      $COMMON_MODULES \
      factoidal_serve.ml \
      ../../../bin/factoidal-explain/factoidal_explain.ml \
      ../../../bin/factoidal-cli/factoidal_cli.ml \
      -o "$OUT" || FACTOIDAL_DEBUG_RC=$?
    rm -f factoidal_serve.ml
    if [[ "$FACTOIDAL_DEBUG_RC" -ne 0 ]]; then
      exit "$FACTOIDAL_DEBUG_RC"
    fi
    ;;
  factoidal-http)
    LOG="_ocamlc_factoidal_http_debug.log"
    OUT="$BINDIR/factoidal-http.byte"
    echo "--- Building debug bytecode: factoidal-http.byte ---"
    run_with_heartbeat "ocamlc factoidal-http.byte" "$LOG" -- \
      ocamlfind ocamlc -g -thread -package fstar.lib,str,zarith,sha,digestif.c,unix,threads.posix -linkpkg -w -8-14-26 \
      $PARQUET_BYTECODE_STUBS \
      $COMMON_MODULES \
      factoidal_http.ml \
      factoidal_http_main.ml \
      -o "$OUT"
    ;;
  *)
    echo "error: unknown target '$TARGET' (expected 'factoidal' or 'factoidal-http')" >&2
    exit 2
    ;;
esac

cat "$LOG"
echo "  Built: $OUT"
echo "  Run with: ~/.opam/fstar/bin/ocamldebug $OUT"
