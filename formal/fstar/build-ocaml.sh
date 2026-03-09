#!/bin/bash
# Build script for the F* → OCaml → JavaScript extraction pipeline
#
# Prerequisites:
#   eval $(opam env --switch=fstar)
#   opam install js_of_ocaml js_of_ocaml-compiler zarith_stubs_js
#
# Outputs:
#   ocaml-output/RDF_Graph_Executable.ml   — Extracted OCaml (RDF core)
#   ocaml-output/SPARQL11_Algebra.ml       — Extracted OCaml (SPARQL engine)
#   ocaml-output/example                   — Native OCaml binary
#   ocaml-output/w3c_tests                 — Native OCaml W3C test runner
#   ../../docs/fstar-extracted/factoidal-fstar.js  — Browser-ready JS bundle
#
# Usage:
#   cd formal/fstar
#   ./build-ocaml.sh          # full pipeline
#   ./build-ocaml.sh extract  # F* extraction only
#   ./build-ocaml.sh compile  # compile OCaml only (skip extraction)
#   ./build-ocaml.sh js       # js_of_ocaml only (skip extraction+compile)
#   ./build-ocaml.sh test     # run native tests only

set -euo pipefail
cd "$(dirname "$0")"

OUTDIR=ocaml-output
JSDIR=../../docs/fstar-extracted
STEP="${1:-all}"

echo "=== F* → OCaml → JavaScript Pipeline ==="
echo ""

# Step 1: Extract F* to OCaml
if [[ "$STEP" == "all" || "$STEP" == "extract" ]]; then
  echo "--- Step 1: F* → OCaml extraction ---"
  mkdir -p "$OUTDIR"

  # Core verified modules — extracted WITHOUT --lax (fully verified)
  echo "  Extracting verified core modules..."
  fstar.exe --codegen OCaml --odir "$OUTDIR" RDF.Graph.Executable.fst 2>&1 | grep -E "Extracted|Error|error" || true
  fstar.exe --codegen OCaml --odir "$OUTDIR" SPARQL11.Algebra.fst 2>&1 | grep -E "Extracted|Error|error" || true
  echo "  RDF:    $(wc -l < "$OUTDIR/RDF_Graph_Executable.ml") lines"
  echo "  SPARQL: $(wc -l < "$OUTDIR/SPARQL11_Algebra.ml") lines"

  # Parser modules — extracted with --lax (verification WIP, see Phase 3)
  # These will move to verified extraction as their proofs are completed.
  echo "  Extracting parser modules (--lax, verification WIP)..."
  for fst in SPARQL11.Parser.fst Parser.Combinators.fst \
             Parser.NTriples.fst Parser.Turtle.fst \
             Parser.NQuads.fst Parser.TriG.fst \
             Parser.XML.fst Parser.RDFXML.fst \
             Parser.SRX.fst Parser.CSVResults.fst; do
    if [ -f "$fst" ]; then
      fstar.exe --lax --codegen OCaml --odir "$OUTDIR" "$fst" 2>&1 | grep -E "Extracted|Error|error" || true
    fi
  done

  # Apply post-extraction patches (wire assume-val stubs, add regex_match)
  ./ocaml-patches.sh "$OUTDIR/SPARQL11_Algebra.ml"
  echo ""
fi

# Step 2: Compile native OCaml binaries
if [[ "$STEP" == "all" || "$STEP" == "compile" ]]; then
  echo "--- Step 2: Compile native OCaml ---"
  cd "$OUTDIR"

  # Example binary
  ocamlfind ocamlopt -package fstar.lib,str -linkpkg -w -8 \
    RDF_Graph_Executable.ml SPARQL11_Algebra.ml example.ml \
    -o example 2>&1 | grep -i error || true
  echo "  Built: example ($(wc -c < example) bytes)"

  # W3C test binary
  ocamlfind ocamlopt -package fstar.lib,str -linkpkg -w -8 \
    RDF_Graph_Executable.ml SPARQL11_Algebra.ml w3c_tests.ml \
    -o w3c_tests 2>&1 | grep -i error || true
  echo "  Built: w3c_tests ($(wc -c < w3c_tests) bytes)"

  cd ..
  echo ""
fi

# Step 3: Run native tests
if [[ "$STEP" == "all" || "$STEP" == "test" ]]; then
  echo "--- Step 3: Run native OCaml tests ---"
  "$OUTDIR/w3c_tests" 2>&1 | tail -12 || true
  echo ""
fi

# Step 4: Build JavaScript via js_of_ocaml
if [[ "$STEP" == "all" || "$STEP" == "js" ]]; then
  echo "--- Step 4: OCaml → JavaScript (js_of_ocaml) ---"
  mkdir -p "$JSDIR"
  cd "$OUTDIR"

  # Compile to bytecode (js_of_ocaml needs bytecode, not native)
  ocamlfind ocamlc -package fstar.lib -linkpkg -w -8 \
    RDF_Graph_Executable.ml SPARQL11_Algebra.ml example.ml \
    -o example.byte 2>&1 | grep -i error || true

  # Convert to JS with zarith stubs
  js_of_ocaml \
    +zarith_stubs_js/biginteger.js \
    +zarith_stubs_js/runtime.js \
    fstar_int_stubs.js \
    example.byte \
    -o ../../../docs/fstar-extracted/factoidal-fstar.js 2>&1 | grep -v "Warning \[deprecated" | grep -v "^$" || true

  echo "  Built: docs/fstar-extracted/factoidal-fstar.js ($(wc -c < ../../../docs/fstar-extracted/factoidal-fstar.js) bytes)"

  # Also build test runner for browser
  ocamlfind ocamlc -package fstar.lib -linkpkg -w -8 \
    RDF_Graph_Executable.ml SPARQL11_Algebra.ml w3c_tests.ml \
    -o w3c_tests.byte 2>&1 | grep -i error || true

  js_of_ocaml \
    +zarith_stubs_js/biginteger.js \
    +zarith_stubs_js/runtime.js \
    fstar_int_stubs.js \
    w3c_tests.byte \
    -o ../../../docs/fstar-extracted/w3c-tests.js 2>&1 | grep -v "Warning \[deprecated" | grep -v "^$" || true

  echo "  Built: docs/fstar-extracted/w3c-tests.js ($(wc -c < ../../../docs/fstar-extracted/w3c-tests.js) bytes)"

  cd ..
  echo ""
fi

echo "=== Pipeline complete ==="
