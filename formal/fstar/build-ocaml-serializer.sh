#!/bin/bash
# Build the minimal F*-based RDF -> canonical N-Quads serializer.
#
# Usage:
#   cd formal/fstar
#   ./build-ocaml-serializer.sh
#
# Produces:
#   bin/<platform>/factoidal-dump-nq
#   bin/<platform>/factoidal-dump-nq.byte

set -euo pipefail
cd "$(dirname "$0")"
ROOT_DIR="$(pwd)/../.."
OUTDIR=ocaml-output

if [[ ! -d "$OUTDIR" ]]; then
  echo "error: $OUTDIR/ is missing. Run './build-ocaml.sh extract' first." >&2
  exit 1
fi

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

COMMON_MODULES="RDF_Graph_Executable.ml \
  Parser_FastString.ml Parser_IRI.ml \
  Parser_Combinators.ml Parser_TurtleScanner.ml Parser_NTriples.ml Parser_Turtle.ml \
  Parser_NQuads.ml Parser_TriG.ml Parser_XML.ml Parser_RDFXML.ml \
  fstar_pure_hashes.ml RDF_Canonical.ml"

NATIVE_LOG="_ocamlopt_factoidal_dump_nq.log"
NATIVE_OUT="$BINDIR/factoidal-dump-nq"
BYTECODE_LOG="_ocamlc_factoidal_dump_nq.log"
BYTECODE_OUT="$BINDIR/factoidal-dump-nq.byte"

ocamlfind ocamlopt -g -package fstar.lib,str,zarith,sha,digestif.c -linkpkg -w -8-14-26 \
  $COMMON_MODULES \
  factoidal_dump_nq.ml \
  -o "$NATIVE_OUT" > "$NATIVE_LOG" 2>&1

ocamlfind ocamlc -g -package fstar.lib,str,zarith,sha,digestif.c -linkpkg -w -8-14-26 \
  $COMMON_MODULES \
  factoidal_dump_nq.ml \
  -o "$BYTECODE_OUT" > "$BYTECODE_LOG" 2>&1

cat "$NATIVE_LOG"
cat "$BYTECODE_LOG"
echo "Built: $NATIVE_OUT"
echo "Built: $BYTECODE_OUT"
