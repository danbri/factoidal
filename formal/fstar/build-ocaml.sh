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
#   ./build-ocaml.sh wasm-factoidal
#                             # wasm_of_ocaml build of the factoidal CLI
#                             # (experimental; same stub caveats as wasm)
#   ./build-ocaml.sh npm      # populate npm/factoidal/ from existing
#                             # extraction output (copies factoidal.js
#                             # + wasm assets, writes version.json).
#                             # Does NOT re-extract or recompile.
#   ./build-ocaml.sh test     # run native tests only
#
# The wasm target produces a .wasm + loader .js under
# docs/fstar-extracted/w3c-runner.wasm.{js,assets}/.
#
# For the wasm build to actually *run*, wasm_of_ocaml needs JS+WAT
# bindings for the external C primitives that fstar.lib transitively
# pulls in (stdint, zarith, sha, digestif). js_of_ocaml's JS stubs are
# not enough: wasm_of_ocaml-specific primitives live in .wat +
# runtime_wasm.js files (see janestreet/zarith_stubs_js's dune stanza
# `(wasm_of_ocaml (wasm_files runtime_wasm.js runtime.wat))`). Our
# installed opam zarith_stubs_js v0.16.1 doesn't ship those yet — they
# arrived in v0.17 — so we vendor them under
# ocaml-output/wasm_runtime/ and link them explicitly here.
#
# Status after the wasm_runtime link + wasm_stub_shims.py post-processor:
# most SPARQL suites run identically to the native binary (bind 10/10,
# bindings 10/10, aggregates 46/46, exists 6/6, property-path ~29/33,
# syntax-query 93/94, subquery 12/14, etc.). Suites that invoke
# SHA/MD5 (the `functions` suite's hash tests) still crash with
# "illegal cast" because stub_sha*/caml_digestif_* have no real
# binding — fix is to vendor or write wasm-side shims for those too.

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
  # Dependency order:
  #   RDF.Graph.Executable  -> (no deps other than Prims/Stdlib)
  #   Parquet.Footer        -> RDF.Graph.Executable
  #   Tableau               -> RDF.Graph.Executable
  #   SPARQL11.Algebra      -> RDF.Graph.Executable, Tableau
  #   Parser.*              -> RDF.Graph.Executable (combinators, individual formats)
  #   Parser.Ballyhoo*      -> RDF.Graph.Executable (+ Parquet.Footer for COTTAS)
  #   SPARQL11.Parser       -> SPARQL11.Algebra
  #   SPARQL11.Store        -> SPARQL11.Algebra, Parser.BallyhooHDT, Parser.BallyhooCOTTAS
  #   SPARQL.Protocol       -> SPARQL11.Algebra, Parser.CSVResults, Parser.JSONResults
  for fst in RDF.Graph.Executable.fst Parquet.Footer.fst \
             Tableau.fst SPARQL11.Algebra.fst \
             Parser.Combinators.fst Parser.TurtleScanner.fst SPARQL11.Parser.fst \
             Parser.NTriples.fst Parser.Turtle.fst \
             Parser.NQuads.fst Parser.TriG.fst \
             Parser.XML.fst Parser.RDFXML.fst \
             Parser.SRX.fst Parser.CSVResults.fst \
             Parser.JSONResults.fst \
             Parser.Ballyhoo.fst Parser.BallyhooBloom.fst \
             Parser.BallyhooHDT.fst Parser.BallyhooHDTQ.fst \
             Parser.BallyhooCOTTAS.fst \
             SPARQL11.Store.fst \
             SPARQL.Protocol.fst \
             SPARQL.HTTP.fst; do
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

  # Common modules for all binaries. fstar_pure_hashes.ml must precede
  # SPARQL11_Algebra.ml because the post-extraction patch wires the
  # hash_* assume-vals to Fstar_pure_hashes.{md5,sha1,sha256,sha384,sha512}.
  #
  # Ballyhoo/Parquet ordering: Parquet_Footer before Parser_BallyhooCOTTAS
  # (COTTAS runtime glue calls Parquet_Footer.probe_*). SPARQL11_Store
  # depends on Parser_BallyhooHDT and Parser_BallyhooCOTTAS. See
  # docs/designissues/2026-04-19-cottas-parquet-wiring-plan.md §Phase 1.
  COMMON_MODULES="RDF_Graph_Executable.ml Parquet_Footer.ml Tableau.ml \
    Parser_Combinators.ml Parser_TurtleScanner.ml Parser_NTriples.ml Parser_Turtle.ml \
    Parser_NQuads.ml Parser_TriG.ml Parser_XML.ml Parser_RDFXML.ml \
    Parser_SRX.ml Parser_CSVResults.ml Parser_JSONResults.ml \
    Parser_Ballyhoo.ml Parser_BallyhooBloom.ml \
    Parser_BallyhooHDT.ml Parser_BallyhooHDTQ.ml Parser_BallyhooCOTTAS.ml \
    fstar_pure_hashes.ml \
    SPARQL11_Algebra.ml SPARQL11_Parser.ml SPARQL11_Store.ml SPARQL_Protocol.ml \
    SPARQL_HTTP.ml"

  # Parquet/Zstd C stub — compiled and linked into native binaries when the
  # system libzstd is available. If libzstd is missing, FACTOIDAL_NO_ZSTD=1
  # can be set to skip (but then parquet_zstd_decompress_hex will fall back
  # to failwith at runtime, so COTTAS won't work on Parquet with Zstd-
  # compressed data pages). Header check: we look for the header in common
  # locations; if found, link the stub + libzstd. See
  # experimental_ocaml_glue/parquet_zstd_stubs.c.
  PARQUET_NATIVE_STUBS=""
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
        ZSTD_LIB="-cclib -L$dir"; break;
      fi
    done
    if [[ -n "$ZSTD_INC" ]]; then
      PARQUET_NATIVE_STUBS="$ZSTD_INC ../experimental_ocaml_glue/parquet_zstd_stubs.c $ZSTD_LIB -cclib -lzstd"
      echo "  Parquet/Zstd stub: enabled ($ZSTD_INC $ZSTD_LIB -lzstd)"
    else
      echo "  Parquet/Zstd stub: DISABLED (libzstd headers not found; set FACTOIDAL_NO_ZSTD=0 after installing zstd to enable)"
    fi
  fi

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

  # W3C test runner (reads real W3C manifests, calls F*-extracted code).
  # The Ballyhoo HDT/COTTAS runtime glue pulls in Unix (Unix.open_process_full,
  # etc.), so we now always link -package unix.
  ocamlfind ocamlopt -package fstar.lib,str,zarith,sha,digestif.c,unix -linkpkg -w -8-14-26 \
    $STATIC_FLAGS \
    $COMMON_MODULES \
    $PARQUET_NATIVE_STUBS \
    w3c_runner.ml \
    -o "$BINDIR/w3c_runner"
  echo "  Built: bin/${PLATFORM}/w3c_runner ($(wc -c < "$BINDIR/w3c_runner") bytes)"

  # factoidal CLI (SPARQL query + RDF parsing tool)
  ocamlfind ocamlopt -package fstar.lib,str,zarith,sha,digestif.c,unix -linkpkg -w -8-14-26 \
    $STATIC_FLAGS \
    $COMMON_MODULES \
    $PARQUET_NATIVE_STUBS \
    factoidal_cli.ml \
    -o "$BINDIR/factoidal"
  echo "  Built: bin/${PLATFORM}/factoidal ($(wc -c < "$BINDIR/factoidal") bytes)"

  # factoidal-http — SPARQL 1.1 Protocol server (native only; needs Unix)
  ocamlfind ocamlopt -package fstar.lib,str,zarith,sha,digestif.c,unix -linkpkg -w -8-14-26 \
    $STATIC_FLAGS \
    $COMMON_MODULES \
    $PARQUET_NATIVE_STUBS \
    factoidal_http.ml \
    -o "$BINDIR/factoidal-http"
  echo "  Built: bin/${PLATFORM}/factoidal-http ($(wc -c < "$BINDIR/factoidal-http") bytes)"

  # Symlink current platform binaries for convenience (relative from ocaml-output/)
  ln -sf "../../../bin/${PLATFORM}/w3c_runner" w3c_runner
  ln -sf "../../../bin/${PLATFORM}/factoidal" factoidal
  ln -sf "../../../bin/${PLATFORM}/factoidal-http" factoidal-http

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

  # Shared F*-extracted modules used by both the W3C runner and the
  # factoidal query CLI.
  #
  # Phase 2 (2026-04-20): Parquet_Footer + Parser_Ballyhoo{,Bloom,COTTAS}
  # are now included. The js_of_ocaml build can open COTTAS/Parquet
  # artifacts in the browser via:
  #   * the Zstd JS shim (vendor/fzstd.umd.js + parquet_zstd_stubs.js)
  #   * the js_of_ocaml pseudo-FS for /-rooted local paths
  # Parser_BallyhooHDT{,Q} and SPARQL11_Store stay out of the JS build:
  # HDT shells out via Unix.open_process_full which has no JS equivalent.
  # factoidal_cli.ml only uses Parser_BallyhooCOTTAS directly for the
  # --data-cottas path, so omitting HDT doesn't regress the CLI's JS
  # build. Phase 3 (wasm_of_ocaml) with Zstd is a follow-on commit.
  # See docs/designissues/2026-04-19-cottas-parquet-wiring-plan.md.
  FSTAR_MODULES=(
    RDF_Graph_Executable.ml Parquet_Footer.ml Tableau.ml
    Parser_Combinators.ml Parser_TurtleScanner.ml Parser_NTriples.ml Parser_Turtle.ml
    Parser_NQuads.ml Parser_TriG.ml Parser_XML.ml Parser_RDFXML.ml
    Parser_SRX.ml Parser_CSVResults.ml Parser_JSONResults.ml
    Parser_Ballyhoo.ml Parser_BallyhooBloom.ml Parser_BallyhooCOTTAS.ml
    fstar_pure_hashes.ml
    SPARQL11_Algebra.ml SPARQL11_Parser.ml SPARQL_Protocol.ml
    SPARQL_HTTP.ml
  )

  # Build w3c_runner bytecode for js_of_ocaml. We pass -custom + a tiny
  # C stub (parquet_zstd_stubs_jsoo.c) to satisfy the bytecode linker:
  # Parquet_Footer's `external caml_parquet_zstd_decompress_hex` must
  # resolve to *some* symbol, even though js_of_ocaml replaces it with
  # the JS shim at bundle time. The stub returns None and is never
  # actually executed in the JS build path.
  ocamlfind ocamlc -package fstar.lib,str,zarith,sha,digestif.c -linkpkg -w -8-14-26 \
    -custom parquet_zstd_stubs_jsoo.c \
    "${FSTAR_MODULES[@]}" \
    w3c_runner.ml \
    -o w3c_runner.byte 2>&1 | grep -i error || true

  # Build factoidal (query + parse CLI) bytecode for js_of_ocaml
  ocamlfind ocamlc -package fstar.lib,str,zarith,sha,digestif.c -linkpkg -w -8-14-26 \
    -custom parquet_zstd_stubs_jsoo.c \
    "${FSTAR_MODULES[@]}" \
    factoidal_cli.ml \
    -o factoidal.byte 2>&1 | grep -i error || true

  # Convert both to JS with zarith stubs. vendor/fzstd.umd.js is a
  # vendored MIT-licensed Zstandard decompressor (~8 KB) that registers
  # itself as globalThis.fzstd; parquet_zstd_stubs.js is our thin shim
  # that implements caml_parquet_zstd_decompress_hex on top of it. Both
  # are concatenated into the output by js_of_ocaml. Order matters:
  # fzstd.umd.js must come before parquet_zstd_stubs.js so the global
  # is defined when our shim's Requires: checks run at bundle load.
  js_of_ocaml \
    +zarith_stubs_js/biginteger.js \
    +zarith_stubs_js/runtime.js \
    fstar_int_stubs.js \
    fstar_hash_stubs.js \
    vendor/fzstd.umd.js \
    parquet_zstd_stubs.js \
    w3c_runner.byte \
    -o ../../../docs/fstar-extracted/w3c-runner.js 2>&1 | grep -v "Warning \[deprecated" | grep -v "^$" || true

  js_of_ocaml \
    +zarith_stubs_js/biginteger.js \
    +zarith_stubs_js/runtime.js \
    fstar_int_stubs.js \
    fstar_hash_stubs.js \
    vendor/fzstd.umd.js \
    parquet_zstd_stubs.js \
    factoidal.byte \
    -o ../../../docs/fstar-extracted/factoidal.js 2>&1 | grep -v "Warning \[deprecated" | grep -v "^$" || true

  echo "  Built: docs/fstar-extracted/w3c-runner.js ($(wc -c < ../../../docs/fstar-extracted/w3c-runner.js) bytes)"
  echo "  Built: docs/fstar-extracted/factoidal.js   ($(wc -c < ../../../docs/fstar-extracted/factoidal.js) bytes)"

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
    wasm_runtime/zarith_runtime_wasm.js \
    wasm_runtime/zarith_runtime.wat \
    fstar_int_stubs.js \
    w3c_runner.byte \
    -o ../../../docs/fstar-extracted/w3c-runner.wasm.js 2>&1 \
    | grep -v "Warning \[deprecated" | grep -v "^$" || WASM_RC=$?
  if [[ -f ../../../docs/fstar-extracted/w3c-runner.wasm.js ]]; then
    # Patch the throwing stubs so init survives.
    python3 wasm_stub_shims.py ../../../docs/fstar-extracted/w3c-runner.wasm.js

    LOADER_BYTES=$(wc -c < ../../../docs/fstar-extracted/w3c-runner.wasm.js)
    WASM_FILE=$(ls -1 ../../../docs/fstar-extracted/w3c-runner.wasm.assets/*.wasm 2>/dev/null | head -n 1 || true)
    if [[ -n "$WASM_FILE" ]]; then
      WASM_BYTES=$(wc -c < "$WASM_FILE")
      echo "  Built: docs/fstar-extracted/w3c-runner.wasm.js ($LOADER_BYTES bytes) + $(basename "$WASM_FILE") ($WASM_BYTES bytes)"
    else
      echo "  Built: docs/fstar-extracted/w3c-runner.wasm.js ($LOADER_BYTES bytes) — no .wasm asset"
    fi
    echo "  Smoke test: cd into docs/fstar-extracted and run 'node w3c-runner.wasm.js bind' — expect 10/10 pass."
  fi
  cd ..
  echo ""
fi

# Step 5b: Build WebAssembly for the factoidal CLI (experimental).
# Same caveats as Step 5. Produces docs/fstar-extracted/factoidal.wasm.js
# plus factoidal.wasm.assets/ so the browser can load a wasm build of
# factoidal the same way it already loads w3c-runner.wasm.js.
if [[ "$STEP" == "wasm-factoidal" ]]; then
  echo "--- Step 5b: factoidal CLI → WebAssembly (wasm_of_ocaml, experimental) ---"
  if ! command -v wasm_of_ocaml >/dev/null 2>&1; then
    echo "  wasm_of_ocaml not on PATH; install with 'opam install wasm_of_ocaml-compiler'"
    exit 1
  fi
  mkdir -p "$JSDIR"
  cd "$OUTDIR"
  if [[ ! -f factoidal.byte ]]; then
    echo "  factoidal.byte missing — run './build-ocaml.sh js' first to build bytecode."
    exit 1
  fi
  WASM_RC=0
  wasm_of_ocaml compile \
    +zarith_stubs_js/biginteger.js \
    +zarith_stubs_js/runtime.js \
    wasm_runtime/zarith_runtime_wasm.js \
    wasm_runtime/zarith_runtime.wat \
    fstar_int_stubs.js \
    factoidal.byte \
    -o ../../../docs/fstar-extracted/factoidal.wasm.js 2>&1 \
    | grep -v "Warning \[deprecated" | grep -v "^$" || WASM_RC=$?
  if [[ -f ../../../docs/fstar-extracted/factoidal.wasm.js ]]; then
    # Patch the throwing stubs so init survives.
    python3 wasm_stub_shims.py ../../../docs/fstar-extracted/factoidal.wasm.js

    LOADER_BYTES=$(wc -c < ../../../docs/fstar-extracted/factoidal.wasm.js)
    WASM_FILE=$(ls -1 ../../../docs/fstar-extracted/factoidal.wasm.assets/*.wasm 2>/dev/null | head -n 1 || true)
    if [[ -n "$WASM_FILE" ]]; then
      WASM_BYTES=$(wc -c < "$WASM_FILE")
      echo "  Built: docs/fstar-extracted/factoidal.wasm.js ($LOADER_BYTES bytes) + $(basename "$WASM_FILE") ($WASM_BYTES bytes)"
    else
      echo "  Built: docs/fstar-extracted/factoidal.wasm.js ($LOADER_BYTES bytes) — no .wasm asset"
    fi
  fi
  cd ..
  echo ""
fi

# Step 6: Populate the npm/factoidal/ package from the existing
# extraction output. Does NOT re-extract or recompile. Copies the JS
# bundle (and wasm assets if they exist) in-place so that `npm pack`
# from npm/factoidal/ produces a usable tarball. Also writes a
# version.json with the current git SHA for traceability.
if [[ "$STEP" == "npm" ]]; then
  echo "--- Step 6: populate npm/factoidal/ ---"
  NPMDIR="../../npm/factoidal"
  if [[ ! -d "$NPMDIR" ]]; then
    echo "  npm/factoidal/ missing — expected at $NPMDIR"
    exit 1
  fi
  if [[ ! -f "$JSDIR/factoidal.js" ]]; then
    echo "  $JSDIR/factoidal.js missing — run './build-ocaml.sh js' first."
    exit 1
  fi

  # If a symlink is in place (scaffolding state), drop it first so we
  # copy a real file into the package.
  if [[ -L "$NPMDIR/factoidal.js" ]]; then rm "$NPMDIR/factoidal.js"; fi
  cp "$JSDIR/factoidal.js" "$NPMDIR/factoidal.js"
  echo "  Copied: $JSDIR/factoidal.js → $NPMDIR/factoidal.js ($(wc -c < "$NPMDIR/factoidal.js") bytes)"

  # Phase 2 COTTAS/Parquet support: the Zstd JS library + our shim are
  # already inlined into factoidal.js by the js step above, so the npm
  # package doesn't need separate files at runtime. We still copy the
  # raw shim + vendored fzstd as reference material so downstream
  # consumers can audit what landed in the bundle without grepping the
  # minified output.
  if [[ -f "$OUTDIR/parquet_zstd_stubs.js" ]]; then
    cp "$OUTDIR/parquet_zstd_stubs.js" "$NPMDIR/parquet_zstd_stubs.js"
    echo "  Copied: $OUTDIR/parquet_zstd_stubs.js → $NPMDIR/parquet_zstd_stubs.js (reference only)"
  fi
  if [[ -f "$OUTDIR/vendor/fzstd.umd.js" ]]; then
    mkdir -p "$NPMDIR/vendor"
    cp "$OUTDIR/vendor/fzstd.umd.js" "$NPMDIR/vendor/fzstd.umd.js"
    echo "  Copied: $OUTDIR/vendor/fzstd.umd.js → $NPMDIR/vendor/fzstd.umd.js (reference only)"
  fi

  # Wasm artifacts are optional — skip silently if they don't exist yet.
  # Needed by npm/factoidal/browser-wasm.js (the wasm_of_ocaml browser
  # entry) and by its Node smoke test (test/smoke-wasm.js).
  if [[ -f "$JSDIR/factoidal.wasm.js" ]]; then
    cp "$JSDIR/factoidal.wasm.js" "$NPMDIR/factoidal.wasm.js"
    echo "  Copied: $JSDIR/factoidal.wasm.js → $NPMDIR/factoidal.wasm.js ($(wc -c < "$NPMDIR/factoidal.wasm.js") bytes)"
  fi
  if [[ -d "$JSDIR/factoidal.wasm.assets" ]]; then
    rm -rf "$NPMDIR/factoidal.wasm.assets"
    cp -R "$JSDIR/factoidal.wasm.assets" "$NPMDIR/factoidal.wasm.assets"
    echo "  Copied: $JSDIR/factoidal.wasm.assets/ → $NPMDIR/factoidal.wasm.assets/ ($(ls -1 "$NPMDIR/factoidal.wasm.assets" | wc -l | tr -d ' ') file(s))"
  fi

  # Provenance stamp.
  GITSHA=$(git -C ../.. rev-parse HEAD 2>/dev/null || echo "unknown")
  BUILDTIME=$(date -u +%Y-%m-%dT%H:%M:%SZ)
  cat > "$NPMDIR/version.json" <<EOF
{
  "version": "0.1.0-alpha.0",
  "gitSha": "$GITSHA",
  "builtAt": "$BUILDTIME"
}
EOF
  echo "  Wrote:  $NPMDIR/version.json (git=$GITSHA)"
  echo ""
fi

echo "=== Pipeline complete ==="
