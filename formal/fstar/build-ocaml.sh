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
#   ocaml-output/w3c_runner                — Native OCaml W3C test runner
#   ../../docs/fstar-extracted/factoidal-fstar.js  — Browser-ready JS bundle
#
# Usage:
#   cd formal/fstar
#   ./build-ocaml.sh          # full pipeline
#   ./build-ocaml.sh extract  # F* extraction only
#   ./build-ocaml.sh compile  # compile OCaml only (skip extraction)
#   ./build-ocaml.sh js       # js_of_ocaml only (skip extraction+compile)
#   ./build-ocaml.sh wasm     # wasm_of_ocaml only (experimental; needs stubs)
#   ./build-ocaml.sh test     # run native tests only
#
# The wasm target produces a working .wasm + loader .js under
# docs/fstar-extracted/w3c-runner.wasm.{js,assets}/. The artifact compiles
# but does not yet run: fstar.lib transitively depends on stdint, sha,
# digestif, and zarith, whose C primitives (int40_of_int, ml_z_*,
# caml_digestif_*, stub_sha*, ~60 in total) have no JS shim in the
# wasm_of_ocaml runtime. wasm_of_ocaml emits throwing stubs for them, and
# initialization calls int40_of_int almost immediately. To get a running
# wasm binary we need to write JS shims for those primitives (or narrow the
# OCaml linkage so they aren't pulled in).

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

  # All modules extracted with full verification (no --lax)
  # Extraction MUST succeed for every module — no silent failures
  echo "  Extracting all F* modules (verified)..."
  EXTRACT_FAILED=0
  for fst in RDF.Graph.Executable.fst SPARQL11.Algebra.fst \
             Parser.Combinators.fst Parser.TurtleScanner.fst SPARQL11.Parser.fst \
             Parser.NTriples.fst Parser.Turtle.fst \
             Parser.NQuads.fst Parser.TriG.fst \
             Parser.XML.fst Parser.RDFXML.fst \
             Parser.SRX.fst Parser.CSVResults.fst \
             Parser.JSONResults.fst; do
    if [ -f "$fst" ]; then
      echo "    $fst"
      FSTAR_RC=0
      FSTAR_OUT=$(fstar.exe --codegen OCaml --odir "$OUTDIR" "$fst" 2>&1) || FSTAR_RC=$?
      echo "$FSTAR_OUT" | grep -E "Extracted|Error|error" || true
      if ! echo "$FSTAR_OUT" | grep -q "^Extracted module"; then
        echo "  ERROR: $fst failed to extract! (exit code $FSTAR_RC)"
        EXTRACT_FAILED=1
      fi
    fi
  done
  if [ "$EXTRACT_FAILED" -ne 0 ]; then
    echo ""
    echo "FATAL: One or more F* modules failed extraction. Fix errors before proceeding."
    exit 1
  fi
  echo "  RDF:    $(wc -l < "$OUTDIR/RDF_Graph_Executable.ml") lines"
  echo "  SPARQL: $(wc -l < "$OUTDIR/SPARQL11_Algebra.ml") lines"

  # Apply post-extraction patches (assume-val stubs, IRI resolution, validation, etc.)
  ./ocaml-patches.sh "$OUTDIR"
  echo ""
fi

# Step 2: Compile native OCaml binaries
if [[ "$STEP" == "all" || "$STEP" == "compile" ]]; then
  echo "--- Step 2: Compile native OCaml ---"
  # Clean stale compilation artifacts to avoid signature mismatches
  rm -f "$OUTDIR"/*.cmi "$OUTDIR"/*.cmx "$OUTDIR"/*.cmo "$OUTDIR"/*.o
  cd "$OUTDIR"

  # Common modules for all binaries
  COMMON_MODULES="RDF_Graph_Executable.ml \
    Parser_Combinators.ml Parser_TurtleScanner.ml Parser_NTriples.ml Parser_Turtle.ml \
    Parser_NQuads.ml Parser_TriG.ml Parser_XML.ml Parser_RDFXML.ml \
    Parser_SRX.ml Parser_CSVResults.ml Parser_JSONResults.ml \
    SPARQL11_Algebra.ml SPARQL11_Parser.ml"

  # Determine platform for binary output directory
  UNAME_S="$(uname -s)"
  UNAME_M="$(uname -m)"
  if [[ "$UNAME_S" == "Darwin" && "$UNAME_M" == "arm64" ]]; then
    PLATFORM="darwin-arm64"
    STATIC_FLAGS=""
  elif [[ "$UNAME_S" == "Darwin" && "$UNAME_M" == "x86_64" ]]; then
    PLATFORM="darwin-x86_64"
    STATIC_FLAGS=""
  elif [[ "$UNAME_S" == "Linux" && "$UNAME_M" == "x86_64" ]]; then
    PLATFORM="linux-x86_64"
    STATIC_FLAGS="-ccopt -static"
  elif [[ "$UNAME_S" == "Linux" && "$UNAME_M" == "aarch64" ]]; then
    PLATFORM="linux-arm64"
    STATIC_FLAGS="-ccopt -static"
  else
    PLATFORM="${UNAME_S,,}-${UNAME_M}"
    STATIC_FLAGS=""
  fi
  # BINDIR relative to ocaml-output/ (cd "$OUTDIR" already happened above)
  BINDIR="../../../bin/${PLATFORM}"
  mkdir -p "$BINDIR"
  echo "  Platform: ${PLATFORM}"

  # W3C test runner (reads real W3C manifests, calls F*-extracted code)
  ocamlfind ocamlopt -package fstar.lib,str,zarith,sha,digestif.c -linkpkg -w -8-14-26 \
    $STATIC_FLAGS \
    $COMMON_MODULES \
    w3c_runner.ml \
    -o "$BINDIR/w3c_runner"
  echo "  Built: bin/${PLATFORM}/w3c_runner ($(wc -c < "$BINDIR/w3c_runner") bytes)"

  # factoidal CLI (SPARQL query + RDF parsing tool)
  ocamlfind ocamlopt -package fstar.lib,str,zarith,sha,digestif.c -linkpkg -w -8-14-26 \
    $STATIC_FLAGS \
    $COMMON_MODULES \
    factoidal_cli.ml \
    -o "$BINDIR/factoidal"
  echo "  Built: bin/${PLATFORM}/factoidal ($(wc -c < "$BINDIR/factoidal") bytes)"

  # Symlink current platform binaries for convenience (relative from ocaml-output/)
  ln -sf "../../../bin/${PLATFORM}/w3c_runner" w3c_runner
  ln -sf "../../../bin/${PLATFORM}/factoidal" factoidal

  cd ..
  echo ""
fi

# Step 3: Run native tests
if [[ "$STEP" == "all" || "$STEP" == "test" ]]; then
  echo "--- Step 3: Run native OCaml tests ---"
  W3C_RC=0; "$OUTDIR/w3c_runner" --all 2>&1 | tee "$OUTDIR/w3c_results.log" || W3C_RC=$?
  echo "  Full results: $OUTDIR/w3c_results.log ($(wc -l < "$OUTDIR/w3c_results.log") lines)"
  echo ""
fi

# Step 4: Build JavaScript via js_of_ocaml
if [[ "$STEP" == "all" || "$STEP" == "js" ]]; then
  echo "--- Step 4: OCaml → JavaScript (js_of_ocaml) ---"
  mkdir -p "$JSDIR"
  cd "$OUTDIR"

  # Build w3c_runner bytecode for js_of_ocaml
  ocamlfind ocamlc -package fstar.lib,str,zarith,sha,digestif.c -linkpkg -w -8-14-26 \
    RDF_Graph_Executable.ml \
    Parser_Combinators.ml Parser_TurtleScanner.ml Parser_NTriples.ml Parser_Turtle.ml \
    Parser_NQuads.ml Parser_TriG.ml Parser_XML.ml Parser_RDFXML.ml \
    Parser_SRX.ml Parser_CSVResults.ml Parser_JSONResults.ml \
    SPARQL11_Algebra.ml SPARQL11_Parser.ml \
    w3c_runner.ml \
    -o w3c_runner.byte 2>&1 | grep -i error || true

  # Convert to JS with zarith stubs
  js_of_ocaml \
    +zarith_stubs_js/biginteger.js \
    +zarith_stubs_js/runtime.js \
    fstar_int_stubs.js \
    w3c_runner.byte \
    -o ../../../docs/fstar-extracted/w3c-runner.js 2>&1 | grep -v "Warning \[deprecated" | grep -v "^$" || true

  echo "  Built: docs/fstar-extracted/w3c-runner.js ($(wc -c < ../../../docs/fstar-extracted/w3c-runner.js) bytes)"

  cd ..
  echo ""
fi

# Step 5: Build WebAssembly via wasm_of_ocaml (experimental)
# Produces an artifact even though it won't run without extra JS stubs —
# see the header comment for the list of missing primitives.
if [[ "$STEP" == "wasm" ]]; then
  echo "--- Step 5: OCaml → WebAssembly (wasm_of_ocaml, experimental) ---"
  if ! command -v wasm_of_ocaml >/dev/null 2>&1; then
    echo "  wasm_of_ocaml not on PATH; install with 'opam install wasm_of_ocaml-compiler'"
    exit 1
  fi
  mkdir -p "$JSDIR"
  cd "$OUTDIR"
  if [[ ! -f w3c_runner.byte ]]; then
    echo "  w3c_runner.byte missing — run './build-ocaml.sh js' first to build bytecode."
    exit 1
  fi
  WASM_RC=0
  wasm_of_ocaml compile \
    +zarith_stubs_js/biginteger.js \
    +zarith_stubs_js/runtime.js \
    fstar_int_stubs.js \
    w3c_runner.byte \
    -o ../../../docs/fstar-extracted/w3c-runner.wasm.js 2>&1 \
    | grep -v "Warning \[deprecated" | grep -v "^$" || WASM_RC=$?
  if [[ -f ../../../docs/fstar-extracted/w3c-runner.wasm.js ]]; then
    LOADER_BYTES=$(wc -c < ../../../docs/fstar-extracted/w3c-runner.wasm.js)
    WASM_FILE=$(ls -1 ../../../docs/fstar-extracted/w3c-runner.wasm.assets/*.wasm 2>/dev/null | head -n 1 || true)
    if [[ -n "$WASM_FILE" ]]; then
      WASM_BYTES=$(wc -c < "$WASM_FILE")
      echo "  Built: docs/fstar-extracted/w3c-runner.wasm.js ($LOADER_BYTES bytes) + $(basename "$WASM_FILE") ($WASM_BYTES bytes)"
    else
      echo "  Built: docs/fstar-extracted/w3c-runner.wasm.js ($LOADER_BYTES bytes) — no .wasm asset"
    fi
    echo "  NOTE: binary will throw at startup — see build-ocaml.sh header for missing primitives."
  fi
  cd ..
  echo ""
fi

echo "=== Pipeline complete ==="
