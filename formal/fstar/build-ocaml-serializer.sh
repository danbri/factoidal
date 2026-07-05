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

COMMON_MODULES="RDF_Format.ml RDF_Vocabulary.ml RDF_Term.ml RDF_Triple.ml RDF_Indexed.ml RDF_Graph.ml RDF_Vocabulary_Axioms.ml RDFS_Closure.ml OWL_Closure.ml RDF_Graph_Executable.ml \
  Parser_FastString.ml RDF_IRI.ml Parser_IRI.ml \
  RDF_NQuads_Serialize.ml \
  Parser_Combinators.ml Parser_TurtleScanner.ml Parser_NTriples.ml Parser_Turtle.ml \
  RDF_Turtle_Serialize.ml \
  Parser_NQuads.ml Parser_TriG.ml Parser_XML.ml XML_Wellformedness.ml Parser_RDFXML.ml \
  RDF_List_Helpers.ml SPARQL11_IRI_Resolve.ml \
  SPARQL_JSON_Escape.ml \
  Parser_JSON.ml JSONLD_Loader.ml JSONLD_Context.ml JSONLD_Expand.ml Parser_JSONLD.ml \
  RDF_Dataset_Graphs.ml \
  fstar_pure_hashes.ml RDF_Canonical.ml"

NATIVE_LOG="_ocamlopt_factoidal_dump_nq.log"
NATIVE_OUT="$BINDIR/factoidal-dump-nq"
BYTECODE_LOG="_ocamlc_factoidal_dump_nq.log"
BYTECODE_OUT="$BINDIR/factoidal-dump-nq.byte"

# Phase 8 (#200 D, 2026-05-08): factoidal_dump_nq.ml relocated out of
# formal/fstar/ocaml-output/ into bin/factoidal-dump-nq/ per iron rule
# #11 (consumer code is not part of the verified library).
DUMP_NQ_SRC="$ROOT_DIR/bin/factoidal-dump-nq/factoidal_dump_nq.ml"

# Compile in an isolated scratch dir (2026-07-04): compiling in
# $OUTDIR overwrote .cmi/.cmx artifacts that build-ocaml.sh's compile
# step had produced for the SAME modules, and the two invocations'
# artifacts make "inconsistent assumptions" — every later ocamlopt in
# $OUTDIR (tests/unit/run-all.sh) then fails until a full recompile.
BUILDDIR="$(mktemp -d)"
trap 'rm -rf "$BUILDDIR"' EXIT
for m in $COMMON_MODULES; do cp "$m" "$BUILDDIR/"; done
cd "$BUILDDIR"

# Capture rc explicitly (anti-pattern #14) so a compile failure still
# prints its log before the scratch-dir EXIT trap deletes it.
NATIVE_RC=0
ocamlfind ocamlopt -g -package fstar.lib,str,zarith,sha,digestif.c -linkpkg -w -8-14-26 \
  $COMMON_MODULES \
  "$DUMP_NQ_SRC" \
  -o "$NATIVE_OUT" > "$NATIVE_LOG" 2>&1 || NATIVE_RC=$?
cat "$NATIVE_LOG"
if [[ "$NATIVE_RC" -ne 0 ]]; then
  echo "ERROR: factoidal-dump-nq native build failed (rc=$NATIVE_RC)" >&2
  exit "$NATIVE_RC"
fi

BYTECODE_RC=0
ocamlfind ocamlc -g -package fstar.lib,str,zarith,sha,digestif.c -linkpkg -w -8-14-26 \
  $COMMON_MODULES \
  "$DUMP_NQ_SRC" \
  -o "$BYTECODE_OUT" > "$BYTECODE_LOG" 2>&1 || BYTECODE_RC=$?
cat "$BYTECODE_LOG"
if [[ "$BYTECODE_RC" -ne 0 ]]; then
  echo "ERROR: factoidal-dump-nq bytecode build failed (rc=$BYTECODE_RC)" >&2
  exit "$BYTECODE_RC"
fi
echo "Built: $NATIVE_OUT"
echo "Built: $BYTECODE_OUT"
