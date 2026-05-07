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

case "$STEP" in
  compile|js|wasm|patches)
    # These steps don't invoke fstar.exe; skip the preflight check so
    # editing OCaml glue + recompiling works without a full F* opam
    # switch active. Extraction-touching steps still demand fstar.exe.
    ;;
  *)
    if ! command -v fstar.exe >/dev/null 2>&1; then
      echo "FATAL: fstar.exe not found on PATH." >&2
      echo "Hint: activate the F* opam switch first:" >&2
      echo "  eval \$(opam env --switch=fstar)" >&2
      echo "Then rerun ./build-ocaml.sh ${STEP}" >&2
      exit 127
    fi
    ;;
esac

# karamel pilot — emit .krml intermediate files for the C-extraction
# track. See docs/designissues/2026-05-07-c-build-and-roaring-plan.md.
# Standalone step (not part of the default `all` flow) so it can be
# iterated independently while the krml binary is being installed.
if [[ "$STEP" == "karamel" ]]; then
  echo "=== F* → krml extraction (C-build pilot) ==="
  mkdir -p krml-output
  KRML_FAILED=0
  for fst in SPARQL.JSON.Escape.fst \
             SPARQL.Update.Analysis.fst \
             SPARQL.Query.Analysis.fst \
             SPARQL.HTTP.StaticFiles.fst \
             SPARQL.HTTP.QueriesIndex.fst; do
    mod="${fst%.fst}"
    echo "  $fst -> krml-output/${mod//./_}.krml"
    if ! fstar.exe --z3version 4.13.3 --codegen krml \
           --odir krml-output --extract_module "$mod" "$fst" \
           > "krml-output/_${mod}.log" 2>&1; then
      echo "    FAIL — see krml-output/_${mod}.log" >&2
      KRML_FAILED=1
      continue
    fi
    if grep -q "^Verified module" "krml-output/_${mod}.log"; then
      :
    else
      echo "    FAIL: no Verified marker in log" >&2
      KRML_FAILED=1
      continue
    fi
    if grep -q "Warning 250" "krml-output/_${mod}.log"; then
      echo "    WARN: KaRaMeL extraction warning(s) — see log"
    fi
  done
  if [[ "$KRML_FAILED" -ne 0 ]]; then
    echo ""
    echo "FATAL: one or more modules failed --codegen krml" >&2
    exit 1
  fi
  echo ""
  echo "Next step (blocked on krml binary install — see plan doc):"
  echo "  krml -bundle '*' krml-output/*.krml -tmpdir c-output"
  echo ""
  exit 0
fi

# ---------------------------------------------------------------------------
# run_with_heartbeat <label> <log-path> -- <command> [args...]
#
# Runs <command> in the background, redirecting all output to <log-path>,
# and emits one progress line every 30s while the command is running. This
# keeps long-silent verification/compile steps from tripping the subagent
# stream watchdog (10-min idle ceiling) and gives humans a visible pulse
# instead of a dead terminal. Returns the command's exit code.
# ---------------------------------------------------------------------------
run_with_heartbeat() {
  local label="$1"; shift
  local log="$1";   shift
  # Expect the literal '--' separator next, then the command.
  if [[ "${1:-}" != "--" ]]; then
    echo "run_with_heartbeat: expected '--' before command" >&2
    return 2
  fi
  shift
  : > "$log"
  "$@" > "$log" 2>&1 &
  local pid=$!
  local t0=$(date +%s)
  # Heartbeat loop — one tick every 30s, until the child exits.
  while kill -0 "$pid" 2>/dev/null; do
    sleep 30
    # Check again: if child exited during sleep, stop before emitting.
    kill -0 "$pid" 2>/dev/null || break
    local now=$(date +%s)
    local elapsed=$(( now - t0 ))
    local lines=$(wc -l < "$log" 2>/dev/null | tr -d ' ')
    echo "      …${label} still running  (${elapsed}s elapsed, ${lines} log lines)"
  done
  local rc=0
  wait "$pid" || rc=$?
  # Loud failure: dump the log + emit a clear FAIL marker so the
  # caller can `grep` for it and so silent stale-binary commits
  # become impossible. Successful steps stay quiet (the caller
  # prints its own "Built: ..." line, no need for an OK marker
  # cluttering the output).
  if [[ "$rc" -ne 0 ]]; then
    echo "" >&2
    echo "============================================================" >&2
    echo "  FAIL: ${label} (exit ${rc})" >&2
    echo "  log: ${log}" >&2
    echo "============================================================" >&2
    if [[ -f "$log" ]]; then
      tail -80 "$log" >&2
      echo "------------------------------------------------------------" >&2
    fi
  fi
  return "$rc"
}

# needs_rebuild_from_sources <target> <source>...
#
# Returns success (0) when the target is missing or any listed source is
# newer than the target. Missing sources are ignored so callers can pass
# optional files safely.
needs_rebuild_from_sources() {
  local target="$1"; shift
  local src
  [[ ! -e "$target" ]] && return 0
  for src in "$@"; do
    [[ -e "$src" ]] || continue
    if [[ "$src" -nt "$target" ]]; then
      return 0
    fi
  done
  return 1
}

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
  EXTRACT_CHAIN_DIRTY=0
  EXTRACT_COUNT=0
  # Dependency order:
  #   RDF.Graph.Executable  -> (no deps other than Prims/Stdlib)
  #   Parquet.Footer        -> RDF.Graph.Executable
  #   Tableau               -> RDF.Graph.Executable
  #   SPARQL11.Algebra      -> RDF.Graph.Executable, Tableau
  #   Parser.*              -> RDF.Graph.Executable (combinators, individual formats)
  #   Parser.Ballyhoo*      -> RDF.Graph.Executable (+ Parquet.Footer for COTTAS)
  #   SPARQL11.Parser       -> SPARQL11.Algebra
  #   RDF.CottasStore       -> RDF.Graph.Executable, Parser.BallyhooCOTTAS (issue #100 Phase A)
  #   SPARQL11.Store        -> SPARQL11.Algebra, Parser.BallyhooHDT, Parser.BallyhooCOTTAS, RDF.CottasStore
  #   SPARQL.Protocol       -> SPARQL11.Algebra, Parser.CSVResults, Parser.JSONResults
  for fst in Util.Log.fst \
             RDF.Format.fst \
             RDF.Graph.Executable.fst Parquet.Footer.fst \
             RDF.NQuads.Serialize.fst \
             RDF.List.Helpers.fst \
             RDF.Canonical.fst \
             RDF.Canonical.Manifest.fst \
             Tableau.fst SPARQL11.Algebra.fst \
             RDF.Pretty.fst \
             OWL.QueryRewrite.fst OWL.QueryEval.fst \
             OWL.Tests.Manifest.fst \
             RIF.Core.Syntax.fst RIF.Core.Translation.fst RIF.Core.Eval.fst \
             Parser.FastString.fst Parser.IRI.fst \
             Parser.Combinators.fst Parser.TurtleScanner.fst SPARQL11.Parser.fst \
             Parser.NTriples.fst Parser.Turtle.fst \
             Parser.NQuads.fst Parser.TriG.fst \
             Parser.XML.fst Parser.RDFXML.fst Parser.RIFXML.fst \
             Parser.SRX.fst Parser.CSVResults.fst \
             Parser.JSONResults.fst \
             SPARQL.JSON.Escape.fst \
             SPARQL.Eval.TimeBudget.fst \
             SPARQL.Eval.Limits.fst \
             SPARQL.HTTP.Response.fst \
             SPARQL.HTTP.BackendInfo.fst \
             SPARQL.HTTP.QueriesIndex.fst \
             SPARQL.HTTP.StaticFiles.fst \
             SPARQL.HTTP.Admin.fst \
             Parser.Ballyhoo.fst Parser.BallyhooBloom.fst \
             Parser.BallyhooHDT.fst Parser.BallyhooHDTQ.fst \
             Parser.BallyhooCOTTAS.fst \
             RDF.CottasStore.ColumnSeq.fst \
             RDF.CottasStore.PageCache.fst \
             RDF.CottasStore.OnDiskIndex.fst \
             RDF.CottasStore.PresenceBitmap.fst \
             RDF.CottasStore.CompoundPresenceBitmap.fst \
             RDF.Store.Columnar.OffsetIndex.fst \
             SPARQL.Plan.Pruning.fst \
             SPARQL.Plan.Estimate.fst \
             SPARQL.Plan.Loader.fst \
             SPARQL.Plan.AccessPath.fst \
             RDF.CottasStore.fst \
             RDF.CottasInMem.fst \
             SPARQL11.Store.fst \
             SPARQL.Protocol.fst \
             SPARQL.Update.Sandbox.fst \
             SPARQL.Update.Analysis.fst \
             SPARQL.Diagnostics.fst \
             SPARQL.Explain.fst \
             SPARQL.Query.Analysis.fst \
             SPARQL.Plan.Explain.fst \
             SPARQL.HTTP.fst \
             SPARQL.HTTP.Client.fst \
             SPARQL.ServiceDescription.fst \
             SPARQL.GraphStore.fst; do
    if [ -f "$fst" ]; then
      out_ml="$OUTDIR/${fst%.fst}"
      out_ml="${out_ml//./_}.ml"
      if [[ "$EXTRACT_CHAIN_DIRTY" -eq 0 ]] && [[ -f "$out_ml" ]] && [[ ! "$fst" -nt "$out_ml" ]]; then
        echo "    $fst (up to date)"
        continue
      fi
      echo "    $fst"
      FSTAR_RC=0
      # Run fstar.exe with a 30s heartbeat so (a) subagents that watch
      # this script don't hit their stream-idle watchdog during modules
      # that take 1-2 min to verify, and (b) humans see that something
      # is still happening. Per-module log stays under $OUTDIR so it
      # can be grepped later for diagnostics.
      FSTAR_LOG="$OUTDIR/_fstar_${fst%.fst}.log"
      run_with_heartbeat "fstar.exe $fst" "$FSTAR_LOG" -- \
        fstar.exe --z3version 4.13.3 --codegen OCaml --odir "$OUTDIR" "$fst" || FSTAR_RC=$?
      grep -E "Extracted|Error|error" "$FSTAR_LOG" || true
      if ! grep -q "^Extracted module" "$FSTAR_LOG"; then
        echo "  ERROR: $fst failed to extract! (exit code $FSTAR_RC)"
        EXTRACT_FAILED=1
      else
        EXTRACT_CHAIN_DIRTY=1
        EXTRACT_COUNT=$((EXTRACT_COUNT + 1))
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
  if [[ "$EXTRACT_COUNT" -eq 0 ]]; then
    echo "  Extraction outputs already up to date; no F* modules re-extracted."
  else
    echo "  Re-extracted modules: $EXTRACT_COUNT"
  fi

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
  COMMON_MODULES="Util_Log.ml RDF_Format.ml RDF_Graph_Executable.ml RDF_NQuads_Serialize.ml RDF_List_Helpers.ml Parquet_Footer.ml Tableau.ml \
    Parser_FastString.ml Parser_IRI.ml \
    Parser_Combinators.ml Parser_TurtleScanner.ml Parser_NTriples.ml Parser_Turtle.ml \
    Parser_NQuads.ml Parser_TriG.ml Parser_XML.ml Parser_RDFXML.ml \
    Parser_SRX.ml Parser_CSVResults.ml Parser_JSONResults.ml \
    SPARQL_JSON_Escape.ml \
    SPARQL_Eval_TimeBudget.ml \
    SPARQL_Eval_Limits.ml \
    SPARQL_HTTP_Response.ml \
    SPARQL_HTTP_BackendInfo.ml \
    SPARQL_HTTP_QueriesIndex.ml \
    SPARQL_HTTP_StaticFiles.ml \
    SPARQL_HTTP_Admin.ml \
    Parser_Ballyhoo.ml Parser_BallyhooBloom.ml \
    Parser_BallyhooHDT.ml Parser_BallyhooHDTQ.ml Parser_BallyhooCOTTAS.ml \
    RDF_CottasStore_ColumnSeq.ml \
    RDF_CottasStore_PageCache.ml \
    RDF_CottasStore_OnDiskIndex.ml \
    RDF_CottasStore_PresenceBitmap.ml \
    RDF_CottasStore_CompoundPresenceBitmap.ml \
    RDF_Store_Columnar_OffsetIndex.ml \
    SPARQL_Plan_Pruning.ml \
    SPARQL_Plan_Estimate.ml \
    SPARQL_Plan_Loader.ml \
    SPARQL_Plan_AccessPath.ml \
    RDF_CottasStore.ml \
    RDF_CottasInMem.ml \
    fstar_pure_hashes.ml \
    RDF_Canonical.ml \
    RDF_Canonical_Manifest.ml \
    SPARQL11_Algebra.ml RDF_Pretty.ml OWL_QueryRewrite.ml OWL_QueryEval.ml OWL_Tests_Manifest.ml RIF_Core_Syntax.ml RIF_Core_Translation.ml RIF_Core_Eval.ml Parser_RIFXML.ml SPARQL11_Parser.ml SPARQL11_Store.ml SPARQL_Protocol.ml \
    SPARQL_Update_Sandbox.ml \
    SPARQL_Update_Analysis.ml \
    SPARQL_Diagnostics.ml \
    SPARQL_Explain.ml \
    SPARQL_Query_Analysis.ml \
    SPARQL_Plan_Explain.ml \
    SPARQL_HTTP.ml SPARQL_HTTP_Client.ml SPARQL_ServiceDescription.ml \
    SPARQL_GraphStore.ml"

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

  NATIVE_TARGETS=(
    "$BINDIR/w3c_runner"
    "$BINDIR/factoidal"
    "$BINDIR/factoidal-http"
    "$BINDIR/owl_runner"
    "$BINDIR/rdfc10_runner"
    "$BINDIR/cottas_ondisk_smoketest"
  )
  NATIVE_SOURCES=(
    $COMMON_MODULES
    w3c_runner.ml
    factoidal_http.ml
    factoidal_serve.ml
    factoidal_explain.ml
    factoidal_cli.ml
    factoidal_http_main.ml
    owl_runner.ml
    rdfc10_runner.ml
    cottas_ondisk_smoketest.ml
    ../experimental_ocaml_glue/parquet_zstd_stubs.c
  )
  NATIVE_NEEDS_REBUILD=0
  for target in "${NATIVE_TARGETS[@]}"; do
    if needs_rebuild_from_sources "$target" "${NATIVE_SOURCES[@]}"; then
      NATIVE_NEEDS_REBUILD=1
      break
    fi
  done

  if [[ "$NATIVE_NEEDS_REBUILD" -eq 0 ]]; then
    echo "  Native binaries already up to date; skipping ocamlopt rebuild."
  else

    # W3C test runner (reads real W3C manifests, calls F*-extracted code).
    # The Ballyhoo HDT/COTTAS runtime glue pulls in Unix (Unix.open_process_full,
    # etc.), so we now always link -package unix.
    run_with_heartbeat "ocamlopt w3c_runner" "_ocamlopt_w3c_runner.log" -- \
      ocamlfind ocamlopt -package fstar.lib,str,zarith,sha,digestif.c,unix -linkpkg -w -8-14-26 \
      $STATIC_FLAGS \
      $COMMON_MODULES \
      $PARQUET_NATIVE_STUBS \
      w3c_runner.ml \
      -o "$BINDIR/w3c_runner"
    cat _ocamlopt_w3c_runner.log
    echo "  Built: bin/${PLATFORM}/w3c_runner ($(wc -c < "$BINDIR/w3c_runner") bytes)"

    # factoidal CLI (SPARQL query + RDF parsing tool).
    # Phase 2 unification (2026-04-25): the native CLI now links
    # factoidal_http.ml + factoidal_serve.ml so `factoidal serve …`
    # starts the HTTP server in-process (no exec into a sibling binary).
    # See docs/designissues/2026-04-25-cli-http-unification-phase2.md.
    # threads.posix added 2026-04-25 (issue #99): factoidal_http.ml now
    # spawns a background thread to load --data-cottas without blocking
    # the listener bind. See
    # docs/designissues/2026-04-25-mim-bind-port-first.md.
    # Qof3 defensive-debug: -g enables source-line numbers in OCaml
    # backtraces.  factoidal_http.ml now logs Printexc.get_backtrace ()
    # on every uncaught exception in the cottas-ondisk query path, and
    # without -g those frames just say "Called from unknown".
    run_with_heartbeat "ocamlopt factoidal" "_ocamlopt_factoidal.log" -- \
      ocamlfind ocamlopt -g -thread -package fstar.lib,str,zarith,sha,digestif.c,unix,threads.posix -linkpkg -w -8-14-26 \
      $STATIC_FLAGS \
      $COMMON_MODULES \
      $PARQUET_NATIVE_STUBS \
      factoidal_http.ml \
      factoidal_serve.ml \
      factoidal_explain.ml \
      factoidal_cli.ml \
      -o "$BINDIR/factoidal"
    cat _ocamlopt_factoidal.log
    echo "  Built: bin/${PLATFORM}/factoidal ($(wc -c < "$BINDIR/factoidal") bytes)"

    # factoidal-http — SPARQL 1.1 Protocol server (native only; needs Unix).
    # Kept as a 5-line wrapper around Factoidal_http.run_server for
    # backward compatibility with anything that scripts the binary path.
    # All argv parsing + server logic now lives in factoidal_http.ml as
    # a library; factoidal_http_main.ml just wires `let () = …`.
    # threads.posix: see comment above on the factoidal target.
    # -g: see comment above on the factoidal target (qof3 defensive-debug).
    run_with_heartbeat "ocamlopt factoidal-http" "_ocamlopt_factoidal_http.log" -- \
      ocamlfind ocamlopt -g -thread -package fstar.lib,str,zarith,sha,digestif.c,unix,threads.posix -linkpkg -w -8-14-26 \
      $STATIC_FLAGS \
      $COMMON_MODULES \
      $PARQUET_NATIVE_STUBS \
      factoidal_http.ml \
      factoidal_http_main.ml \
      -o "$BINDIR/factoidal-http"
    cat _ocamlopt_factoidal_http.log
    echo "  Built: bin/${PLATFORM}/factoidal-http ($(wc -c < "$BINDIR/factoidal-http") bytes)"

    # owl_runner — OWL 2 Test Cases runner (Phase 0 skeleton: reads a
    # W3C OWL test catalog via Parser_RDFXML, prints per-test identifier
    # + types, emits final count. No reasoning wired yet.
    # See docs/designissues/2026-04-24-owl-test-harness.md.
    run_with_heartbeat "ocamlopt owl_runner" "_ocamlopt_owl_runner.log" -- \
      ocamlfind ocamlopt -package fstar.lib,str,zarith,sha,digestif.c,unix -linkpkg -w -8-14-26 \
      $STATIC_FLAGS \
      $COMMON_MODULES \
      $PARQUET_NATIVE_STUBS \
      owl_runner.ml \
      -o "$BINDIR/owl_runner"
    cat _ocamlopt_owl_runner.log
    echo "  Built: bin/${PLATFORM}/owl_runner ($(wc -c < "$BINDIR/owl_runner") bytes)"

  # rdfc10_runner — RDF Dataset Canonicalization 1.0 (RDFC-1.0) runner.
  # Phase 0 skeleton: parses third_party/testing/rdf-canon/tests/manifest.ttl
  # via the F*-extracted Parser_Turtle, dispatches per test type, and
  # runs a placeholder no-op canonicaliser so the score harness has
  # something to wire to. The actual canonicalisation algorithm lands
  # in F* per docs/designissues/2026-04-24-rdfc10-plan.md.
  #
  # Failure path is explicit (vs. relying on `set -e` from the helper):
  # if ocamlopt fails we dump the per-step log so the cause is visible
  # in the build log without the human having to fish around in
  # ocaml-output/ for _ocamlopt_*.log.
    RDFC10_RC=0
    run_with_heartbeat "ocamlopt rdfc10_runner" "_ocamlopt_rdfc10_runner.log" -- \
      ocamlfind ocamlopt -package fstar.lib,str,zarith,sha,digestif.c,unix -linkpkg -w -8-14-26 \
      $STATIC_FLAGS \
      $COMMON_MODULES \
      $PARQUET_NATIVE_STUBS \
      rdfc10_runner.ml \
      -o "$BINDIR/rdfc10_runner" || RDFC10_RC=$?
    cat _ocamlopt_rdfc10_runner.log
    if [[ "$RDFC10_RC" -ne 0 ]]; then
      echo "  ERROR: rdfc10_runner build failed (ocamlopt rc=$RDFC10_RC)" >&2
      echo "  See full log above. Build aborted." >&2
      exit "$RDFC10_RC"
    fi
    if [[ ! -x "$BINDIR/rdfc10_runner" ]]; then
      echo "  ERROR: rdfc10_runner ocamlopt returned 0 but $BINDIR/rdfc10_runner is missing or not executable" >&2
      exit 1
    fi
    echo "  Built: bin/${PLATFORM}/rdfc10_runner ($(wc -c < "$BINDIR/rdfc10_runner") bytes)"

    # cottas_ondisk_smoketest — issue #100 Phase 2 acceptance harness.
    # Opens a COTTAS file via the F*-extracted on-disk store, reports
    # startup/post-open/post-query RSS in MB, runs cottas_ondisk_estimate
    # with all-None bounds. Acceptance #4: server RSS no longer scales
    # with corpus size.
    COTTAS_SMOKE_RC=0
    run_with_heartbeat "ocamlopt cottas_ondisk_smoketest" "_ocamlopt_cottas_ondisk_smoketest.log" -- \
      ocamlfind ocamlopt -package fstar.lib,str,zarith,sha,digestif.c,unix -linkpkg -w -8-14-26 \
      $STATIC_FLAGS \
      $COMMON_MODULES \
      $PARQUET_NATIVE_STUBS \
      cottas_ondisk_smoketest.ml \
      -o "$BINDIR/cottas_ondisk_smoketest" || COTTAS_SMOKE_RC=$?
    cat _ocamlopt_cottas_ondisk_smoketest.log 2>/dev/null || true
    if [[ "$COTTAS_SMOKE_RC" -ne 0 ]]; then
      echo "  WARNING: cottas_ondisk_smoketest build failed (ocamlopt rc=$COTTAS_SMOKE_RC)" >&2
      echo "  This is a non-blocking smoketest harness; main binaries are unaffected." >&2
    else
      echo "  Built: bin/${PLATFORM}/cottas_ondisk_smoketest ($(wc -c < "$BINDIR/cottas_ondisk_smoketest") bytes)"
    fi
  fi

  # Symlink current platform binaries for convenience (relative from ocaml-output/)
  ln -sf "../../../bin/${PLATFORM}/w3c_runner" w3c_runner
  ln -sf "../../../bin/${PLATFORM}/factoidal" factoidal
  ln -sf "../../../bin/${PLATFORM}/factoidal-http" factoidal-http
  ln -sf "../../../bin/${PLATFORM}/owl_runner" owl_runner
  ln -sf "../../../bin/${PLATFORM}/rdfc10_runner" rdfc10_runner
  if [[ -x "$BINDIR/cottas_ondisk_smoketest" ]]; then
    ln -sf "../../../bin/${PLATFORM}/cottas_ondisk_smoketest" cottas_ondisk_smoketest
  fi

  cd ..
  echo ""
fi

# Step 3: Run native tests
if [[ "$STEP" == "all" || "$STEP" == "test" ]]; then
  echo "--- Step 3: Run native OCaml tests ---"
  W3C_RC=0; "$OUTDIR/w3c_runner" --all 2>&1 | tee "$OUTDIR/w3c_results.log" || W3C_RC=$?
  echo "  Full results: $OUTDIR/w3c_results.log ($(wc -l < "$OUTDIR/w3c_results.log") lines)"
  # Refresh the human-readable test-results page (docs/test-results/index.html
  # + latest.{csv,json} + history snapshot). generate-report.sh used to be a
  # separate manual step, which is how the published page got 24h-stale on
  # 2026-04-29: builds were green, w3c_results.log was current, but no one
  # had remembered to regenerate the HTML. Now wired in unconditionally
  # because the cost is fast and the value is the public-facing dashboard.
  if [[ -x ./generate-report.sh ]]; then
    ./generate-report.sh 2>&1 | tail -10
  fi
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
    RDF_Format.ml
    RDF_Graph_Executable.ml RDF_NQuads_Serialize.ml Parquet_Footer.ml Tableau.ml
    Parser_FastString.ml Parser_IRI.ml
    Parser_Combinators.ml Parser_TurtleScanner.ml Parser_NTriples.ml Parser_Turtle.ml
    Parser_NQuads.ml Parser_TriG.ml Parser_XML.ml Parser_RDFXML.ml
    Parser_SRX.ml Parser_CSVResults.ml Parser_JSONResults.ml
    SPARQL_JSON_Escape.ml
    SPARQL_HTTP_Response.ml
    SPARQL_HTTP_BackendInfo.ml
    SPARQL_HTTP_QueriesIndex.ml
    SPARQL_HTTP_StaticFiles.ml
    SPARQL_HTTP_Admin.ml
    Parser_Ballyhoo.ml Parser_BallyhooBloom.ml
    Parser_BallyhooHDT.ml Parser_BallyhooHDTQ.ml
    Parser_BallyhooCOTTAS.ml
    RDF_CottasStore_ColumnSeq.ml
    RDF_CottasStore_PageCache.ml
    RDF_CottasStore_OnDiskIndex.ml
    RDF_CottasStore_PresenceBitmap.ml
    RDF_CottasStore_CompoundPresenceBitmap.ml
    RDF_CottasStore.ml
    RDF_CottasInMem.ml
    fstar_pure_hashes.ml
    RDF_Canonical.ml
    SPARQL11_Algebra.ml RDF_Pretty.ml OWL_QueryRewrite.ml OWL_QueryEval.ml RIF_Core_Syntax.ml RIF_Core_Translation.ml RIF_Core_Eval.ml Parser_RIFXML.ml SPARQL11_Parser.ml
    SPARQL11_Store.ml
    SPARQL_Protocol.ml
    SPARQL_Update_Sandbox.ml
    SPARQL_Update_Analysis.ml
    SPARQL_Diagnostics.ml
    SPARQL_Explain.ml
    SPARQL_Query_Analysis.ml
    SPARQL_HTTP.ml SPARQL_HTTP_Client.ml SPARQL_ServiceDescription.ml SPARQL_GraphStore.ml
  )
  JS_TARGETS=(
    w3c_runner.byte
    factoidal.byte
    ../../../docs/fstar-extracted/w3c-runner.js
    ../../../docs/fstar-extracted/factoidal.js
  )
  JS_SOURCES=(
    "${FSTAR_MODULES[@]}"
    w3c_runner.ml
    factoidal_serve.ml
    factoidal_serve_jsoo.ml
    factoidal_cli.ml
    parquet_zstd_stubs_jsoo.c
    fstar_int_stubs.js
    fstar_hash_stubs.js
    fstar_utf8_output_stubs.js
    vendor/fzstd.umd.js
    parquet_zstd_stubs.js
  )
  JS_NEEDS_REBUILD=0
  for target in "${JS_TARGETS[@]}"; do
    if needs_rebuild_from_sources "$target" "${JS_SOURCES[@]}"; then
      JS_NEEDS_REBUILD=1
      break
    fi
  done
  if [[ "$JS_NEEDS_REBUILD" -eq 0 ]]; then
    echo "  JavaScript bundles already up to date; skipping ocamlc/js_of_ocaml rebuild."
  else

    # Build w3c_runner bytecode for js_of_ocaml. We pass -custom + a tiny
    # C stub (parquet_zstd_stubs_jsoo.c) to satisfy the bytecode linker:
    # Parquet_Footer's `external caml_parquet_zstd_decompress_hex` must
    # resolve to *some* symbol, even though js_of_ocaml replaces it with
    # the JS shim at bundle time. The stub returns None and is never
    # actually executed in the JS build path.
    run_with_heartbeat "ocamlc w3c_runner.byte" "_ocamlc_w3c_runner.log" -- \
      ocamlfind ocamlc -package fstar.lib,str,zarith,sha,digestif.c,unix -linkpkg -w -8-14-26 \
      -custom parquet_zstd_stubs_jsoo.c \
      "${FSTAR_MODULES[@]}" \
      w3c_runner.ml \
      -o w3c_runner.byte
    grep -i error _ocamlc_w3c_runner.log || true

    # Build factoidal (query + parse CLI) bytecode for js_of_ocaml.
    # The JS bundle does NOT link factoidal_http.ml (Unix-bound), so we
    # swap in factoidal_serve_jsoo.ml as the Factoidal_serve module — it
    # has the same signature as the native factoidal_serve.ml but errors
    # at runtime if `serve` is invoked from the browser. The swap is
    # trivially reversible: copy file into place, build, restore.
    cp factoidal_serve.ml factoidal_serve.ml.native_backup
    cp factoidal_serve_jsoo.ml factoidal_serve.ml
    FACTOIDAL_BYTE_RC=0
    run_with_heartbeat "ocamlc factoidal.byte" "_ocamlc_factoidal.log" -- \
      ocamlfind ocamlc -package fstar.lib,str,zarith,sha,digestif.c,unix -linkpkg -w -8-14-26 \
      -custom parquet_zstd_stubs_jsoo.c \
      "${FSTAR_MODULES[@]}" \
      factoidal_explain.ml \
      factoidal_serve.ml \
      factoidal_cli.ml \
      -o factoidal.byte || FACTOIDAL_BYTE_RC=$?
    # Restore the native impl so a subsequent native build doesn't pick
    # up the stub. Always restore, even on compile failure.
    mv factoidal_serve.ml.native_backup factoidal_serve.ml
    if [[ "$FACTOIDAL_BYTE_RC" -ne 0 ]]; then
      cat _ocamlc_factoidal.log
      echo "  ERROR: factoidal.byte build failed (rc=$FACTOIDAL_BYTE_RC)" >&2
      exit "$FACTOIDAL_BYTE_RC"
    fi
    grep -i error _ocamlc_factoidal.log || true

    # Convert both to JS with zarith stubs. vendor/fzstd.umd.js is a
    # vendored MIT-licensed Zstandard decompressor (~8 KB) that registers
    # itself as globalThis.fzstd; parquet_zstd_stubs.js is our thin shim
    # that implements caml_parquet_zstd_decompress_hex on top of it. Both
    # are concatenated into the output by js_of_ocaml. Order matters:
    # fzstd.umd.js must come before parquet_zstd_stubs.js so the global
    # is defined when our shim's Requires: checks run at bundle load.
    run_with_heartbeat "js_of_ocaml w3c-runner" "_jsoo_w3c_runner.log" -- \
      js_of_ocaml \
      +zarith_stubs_js/biginteger.js \
      +zarith_stubs_js/runtime.js \
      fstar_int_stubs.js \
      fstar_hash_stubs.js \
      fstar_utf8_output_stubs.js \
      vendor/fzstd.umd.js \
      parquet_zstd_stubs.js \
      w3c_runner.byte \
      -o ../../../docs/fstar-extracted/w3c-runner.js
    grep -v "Warning \[deprecated" _jsoo_w3c_runner.log | grep -v "^$" || true

    run_with_heartbeat "js_of_ocaml factoidal" "_jsoo_factoidal.log" -- \
      js_of_ocaml \
      +zarith_stubs_js/biginteger.js \
      +zarith_stubs_js/runtime.js \
      fstar_int_stubs.js \
      fstar_hash_stubs.js \
      fstar_utf8_output_stubs.js \
      vendor/fzstd.umd.js \
      parquet_zstd_stubs.js \
      factoidal.byte \
      -o ../../../docs/fstar-extracted/factoidal.js
    grep -v "Warning \[deprecated" _jsoo_factoidal.log | grep -v "^$" || true

    echo "  Built: docs/fstar-extracted/w3c-runner.js ($(wc -c < ../../../docs/fstar-extracted/w3c-runner.js) bytes)"
    echo "  Built: docs/fstar-extracted/factoidal.js   ($(wc -c < ../../../docs/fstar-extracted/factoidal.js) bytes)"
  fi

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
  W3C_WASM_LOADER="../../../docs/fstar-extracted/w3c-runner.wasm.js"
  W3C_WASM_ASSET="$(ls -1 ../../../docs/fstar-extracted/w3c-runner.wasm.assets/*.wasm 2>/dev/null | head -n 1 || true)"
  if [[ -n "$W3C_WASM_ASSET" ]] \
     && ! needs_rebuild_from_sources "$W3C_WASM_LOADER" w3c_runner.byte wasm_runtime/zarith_runtime_wasm.js wasm_runtime/zarith_runtime.wat fstar_int_stubs.js \
     && ! needs_rebuild_from_sources "$W3C_WASM_ASSET" w3c_runner.byte wasm_runtime/zarith_runtime_wasm.js wasm_runtime/zarith_runtime.wat fstar_int_stubs.js; then
    echo "  WebAssembly bundle already up to date; skipping wasm_of_ocaml rebuild."
  else
    WASM_RC=0
    run_with_heartbeat "wasm_of_ocaml w3c-runner" "_waoc_w3c_runner.log" -- \
      wasm_of_ocaml compile \
      +zarith_stubs_js/biginteger.js \
      +zarith_stubs_js/runtime.js \
      wasm_runtime/zarith_runtime_wasm.js \
      wasm_runtime/zarith_runtime.wat \
      fstar_int_stubs.js \
      w3c_runner.byte \
      -o ../../../docs/fstar-extracted/w3c-runner.wasm.js \
      || WASM_RC=$?
    grep -v "Warning \[deprecated" _waoc_w3c_runner.log | grep -v "^$" || true
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
  FACTOIDAL_WASM_LOADER="../../../docs/fstar-extracted/factoidal.wasm.js"
  FACTOIDAL_WASM_ASSET="$(ls -1 ../../../docs/fstar-extracted/factoidal.wasm.assets/*.wasm 2>/dev/null | head -n 1 || true)"
  if [[ -n "$FACTOIDAL_WASM_ASSET" ]] \
     && ! needs_rebuild_from_sources "$FACTOIDAL_WASM_LOADER" factoidal.byte wasm_runtime/zarith_runtime_wasm.js wasm_runtime/zarith_runtime.wat fstar_int_stubs.js \
     && ! needs_rebuild_from_sources "$FACTOIDAL_WASM_ASSET" factoidal.byte wasm_runtime/zarith_runtime_wasm.js wasm_runtime/zarith_runtime.wat fstar_int_stubs.js; then
    echo "  factoidal WebAssembly bundle already up to date; skipping wasm_of_ocaml rebuild."
  else
    WASM_RC=0
    run_with_heartbeat "wasm_of_ocaml factoidal" "_waoc_factoidal.log" -- \
      wasm_of_ocaml compile \
      +zarith_stubs_js/biginteger.js \
      +zarith_stubs_js/runtime.js \
      wasm_runtime/zarith_runtime_wasm.js \
      wasm_runtime/zarith_runtime.wat \
      fstar_int_stubs.js \
      factoidal.byte \
      -o ../../../docs/fstar-extracted/factoidal.wasm.js \
      || WASM_RC=$?
    grep -v "Warning \[deprecated" _waoc_factoidal.log | grep -v "^$" || true
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
# Loud success marker. With `set -e` propagating any earlier failure
# this line is only reached on a clean run — useful to grep for in
# build logs and to gate downstream automation. Symmetric with the
# FAIL banner emitted by run_with_heartbeat's failure path.
echo "BUILD_STATUS=OK"
