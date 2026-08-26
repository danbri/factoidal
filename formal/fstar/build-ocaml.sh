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
# Stdint.Uint32 (FStar_UInt32's OCaml realization — Parquet.Footer's
# u32 magic numbers/lengths, HDT's CRC32c) needed the same treatment:
# ocaml-output/wasm_runtime/stdint_uint32_runtime.wat is a hand-written
# (not vendored) Wasm module giving wasm_of_ocaml real `uint32_*`
# bindings — see that file's header for why the existing
# `fstar_int_stubs.js` (js_of_ocaml's JS stubs, same primitive names)
# doesn't cover wasm_of_ocaml too. Wider stdint fixed-width types
# (Uint64/Int40/48/56/128/…) are unused for real arithmetic anywhere in
# this project and stay identity-shimmed by wasm_stub_shims.py.
#
# Status after the wasm_runtime link + wasm_stub_shims.py post-processor:
# most SPARQL suites run identically to the native binary (bind 10/10,
# bindings 10/10, aggregates 46/46, exists 6/6, property-path ~29/33,
# syntax-query 93/94, subquery 12/14, etc.), and COTTAS/Parquet opens
# (previously `Invalid_argument("Uint32.of_string")` on every wasm
# COTTAS open) now work. Suites that invoke SHA/MD5 (the `functions`
# suite's hash tests) still crash with "illegal cast" because
# stub_sha*/caml_digestif_* have no real binding — fix is to vendor or
# write wasm-side shims for those too.

set -euo pipefail
cd "$(dirname "$0")"

OUTDIR=ocaml-output
JSDIR=../../docs/fstar-extracted

# ---------------------------------------------------------------------------
# Multi-step invocation. `./build-ocaml.sh extract compile` runs BOTH steps,
# in order, each as its own locked sub-invocation.
#
# 2026-08-15: it used to run only `extract`. `STEP="${1:-all}"` read the first
# argument and every later one was silently discarded -- so the caller got an
# extraction, no compile, a zero exit code, and a stale binary that then
# "measured" whatever the previous build left behind.
#
# That form is not an agent's invention: it is what the repo's OWN instructions
# tell people to type. It appears in tests/unit/README.md, in run-all.sh's own
# error message, and in ~10 tests/local/*.sh "run this first" hints. Every one
# of them was asking for half a build.
#
# Fixing the script rather than the twelve call sites: the documented command
# should do what it says, and silently ignoring an argument is the same
# silent-failure class this repo keeps removing from its engine (anti-pattern
# #14 -- never let a failure pass unnoticed).
# ---------------------------------------------------------------------------
# 2026-08-26: the loop above used to iterate "$@" verbatim, so it read a
# FLAG as if it were a step. `./build-ocaml.sh extract --force-full` --
# the form npm-publish.yml and this file's own comments prescribe -- ran
# `"$0" extract` (no flag, so FORCE_FULL stayed 0 and the manifest skip
# stayed live) and then `"$0" --force-full`, which matched no step block
# and exited 0. --force-full had been a silent no-op since the multi-step
# change landed on 2026-08-15. Arguments are now partitioned: flags go to
# every step sub-invocation, steps are validated, and an unrecognised
# argument of either kind is fatal instead of silently discarded.
BUILD_FLAGS=()
BUILD_STEPS=()
for _arg in "$@"; do
  case "$_arg" in
    -*) BUILD_FLAGS+=("$_arg") ;;
    *)  BUILD_STEPS+=("$_arg") ;;
  esac
done

for _flag in ${BUILD_FLAGS[@]+"${BUILD_FLAGS[@]}"}; do
  case "$_flag" in
    --force-full) ;;
    *)
      echo "FATAL: unknown flag '${_flag}'." >&2
      echo "       Known flags: --force-full" >&2
      exit 2
      ;;
  esac
done

VALID_STEPS="all extract compile test js npm wasm wasm-factoidal karamel patches"
for _step in ${BUILD_STEPS[@]+"${BUILD_STEPS[@]}"}; do
  case " $VALID_STEPS " in
    *" $_step "*) ;;
    *)
      echo "FATAL: unknown step '${_step}'." >&2
      echo "       Known steps: $VALID_STEPS" >&2
      exit 2
      ;;
  esac
done

if [ "${#BUILD_STEPS[@]}" -eq 0 ] && [ "$#" -gt 0 ]; then
  echo "FATAL: flags given with no step: $*" >&2
  echo "       Known steps: $VALID_STEPS" >&2
  exit 2
fi

if [ "${#BUILD_STEPS[@]}" -gt 1 ]; then
  for _step in "${BUILD_STEPS[@]}"; do
    echo "=== build-ocaml.sh: step '${_step}' ==="
    "$0" "$_step" ${BUILD_FLAGS[@]+"${BUILD_FLAGS[@]}"} || exit $?
  done
  exit 0
fi

STEP="${BUILD_STEPS[0]:-all}"

FORCE_FULL=0
for _flag in ${BUILD_FLAGS[@]+"${BUILD_FLAGS[@]}"}; do
  [ "$_flag" = "--force-full" ] && FORCE_FULL=1
done

# ---------------------------------------------------------------------------
# Single-runner lock + build-running marker.
#
# Concurrent extract/compile invocations in the same worktree are a recurring
# hazard — multiple fstar.exe processes corrupt each other's .checked.lax cache
# entries; concurrent ocamlopt runs race on .cmi/.cmx files. This lock makes
# build-ocaml.sh refuse to run if another instance is already in flight in the
# same worktree.
#
# The build-running marker (.build-running) records that a build is rewriting
# .ml and binary files. See skills/workflow-gotchas-debugging/SKILL.md
# sections 2 and 5.
#
# ⚠️ 2026-08-15: this comment used to claim the marker "is consumed by the stop
# hook to silence 'uncommitted changes' warnings". That is NOT true of the stop
# hook in this environment. Checked directly: ~/.claude/stop-hook-git-check.sh
# contains ZERO occurrences of "build", "marker" or "running" -- it runs a bare
# `git diff --quiet`. So the marker is written by every build and read by
# nobody, while the hook fires throughout a long compile.
#
# The hook is harness-global (~/.claude/), not repo-shipped -- .claude/ here
# carries only session-start.sh -- so this repo cannot fix it, and the marker is
# left in place because a repo-local or future hook may still want it. What is
# fixed is the CLAIM: an unconsumed marker described as consumed is the same
# shape as hazard #19 (a step that can silently no-op is a lie), and it costs
# the next reader a debugging round to discover the mechanism was never wired.
#
# The lock is per-worktree: each worktree has its own .build.lock, so parallel
# agent worktrees don't block each other. Only same-worktree concurrency is
# refused.
# ---------------------------------------------------------------------------
LOCK_FILE=".build.lock"
if command -v flock >/dev/null 2>&1; then
  exec 200>"$LOCK_FILE"
  if ! flock -n 200; then
    echo "FATAL: another build-ocaml.sh is already running in this worktree." >&2
    echo "       (lock file: $(pwd)/$LOCK_FILE)" >&2
    echo "       Wait for it to finish, or kill it:" >&2
    echo "         pkill -f 'build-ocaml.sh'" >&2
    exit 75
  fi
else
  # macOS ships no flock(1). Fall back to the .build-running marker
  # (written below with our PID): refuse only when it names a PID that
  # is still alive. 2026-08-22: without this, `flock` exited 127 and
  # every macOS build aborted as "another build running" with no build
  # running at all.
  if [ -f ".build-running" ]; then
    other_pid="$(cut -d: -f1 ".build-running" 2>/dev/null)"
    if [ -n "$other_pid" ] && kill -0 "$other_pid" 2>/dev/null; then
      echo "FATAL: another build-ocaml.sh is already running in this worktree (pid $other_pid)." >&2
      echo "       Wait for it to finish, or kill it: pkill -f 'build-ocaml.sh'" >&2
      exit 75
    fi
  fi
fi

# Build-running marker, removed on any exit (success, failure, signal).
MARKER_FILE=".build-running"
echo "$$:$STEP:$(date -u +%Y-%m-%dT%H:%M:%SZ)" > "$MARKER_FILE"
trap 'rm -f "$MARKER_FILE"' EXIT

case "$STEP" in
  compile|js|wasm|patches|npm)
    # These steps don't invoke fstar.exe; skip the preflight check so
    # editing OCaml glue + recompiling works without a full F* opam
    # switch active. Extraction-touching steps still demand fstar.exe.
    # `npm` is pure file-copying from existing extraction output (see
    # Step 6 below) — it never shells out to fstar.exe either.
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
           --odir krml-output --cache_checked_modules \
           --extract_module "$mod" "$fst" \
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
  # Heartbeat loop — poll at 0.2s granularity, EMIT at most every ~30s.
  # The earlier `sleep 30; kill -0 || break` shape charged a flat 30s to
  # every invocation whose child finished quickly: the work was already
  # done but the loop could not notice until its sleep expired. Silent,
  # so it never appeared in any log. This is the same bug as the
  # extract-layer barrier below and it was NOT fixed when that one was —
  # measured 2026-07-29 after landing #320: warm no-op extract still
  # 472s wall. Keep the two loops in the same shape.
  local hb_last=$t0
  while kill -0 "$pid" 2>/dev/null; do
    sleep 0.2
    kill -0 "$pid" 2>/dev/null || break
    local now=$(date +%s)
    if [ $(( now - hb_last )) -ge 30 ]; then
      hb_last=$now
      local lines=$(wc -l < "$log" 2>/dev/null | tr -d ' ')
      echo "      …${label} still running  ($(( now - t0 ))s elapsed, ${lines} log lines)"
    fi
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

# ---------------------------------------------------------------------------
# Per-phase wall-clock timing.
#
# Every fix in this project pays the full verify+extract+compile+test loop,
# and until now nobody could say *which phase* dominated a given run without
# eyeballing terminal scrollback. record_phase_timing() appends one CSV line
# per phase to .claude-runs/build-timings.csv (created with a header on
# first use) and echoes a summary line. changed_modules carries EXTRACT_COUNT
# so a slow compile/js/wasm phase can be correlated with how many modules
# were actually re-extracted in the same run (0 for a pure `compile`/`js`/
# `wasm` invocation that didn't touch extract this time).
# ---------------------------------------------------------------------------
TIMING_CSV=".claude-runs/build-timings.csv"
mkdir -p .claude-runs
if [[ ! -f "$TIMING_CSV" ]]; then
  echo "timestamp,phase,seconds,changed_modules" > "$TIMING_CSV"
fi
EXTRACT_COUNT=0   # global default; the extract step below overwrites it

record_phase_timing() {
  local phase="$1" start_epoch="$2" changed="${3:-0}"
  local end_epoch elapsed ts
  end_epoch=$(date +%s)
  elapsed=$(( end_epoch - start_epoch ))
  ts=$(date -u +%Y-%m-%dT%H:%M:%SZ)
  echo "${ts},${phase},${elapsed},${changed}" >> "$TIMING_CSV"
  echo "  [timing] phase=${phase} seconds=${elapsed} changed_modules=${changed}"
}

echo "=== F* → OCaml → JavaScript Pipeline ==="
echo ""

# Step 1: Extract F* to OCaml
if [[ "$STEP" == "all" || "$STEP" == "extract" ]]; then
  echo "--- Step 1: F* → OCaml extraction ---"
  PHASE_START_EXTRACT=$(date +%s)
  mkdir -p "$OUTDIR"

  # ---------------------------------------------------------------------
  # Incremental-extract manifest (2026-07-04, build-speed P0).
  #
  # Skips invoking fstar.exe entirely for a module whose DEPENDENCY-CLOSURE
  # digest is unchanged since the last successful extract AND whose .ml is
  # already present in $OUTDIR. Replaces the old EXTRACT_CHAIN_DIRTY flag,
  # which forced every module *positioned after* any re-extracted module
  # in this hand-ordered list to re-run fstar.exe regardless of whether it
  # actually depended on the change (see fast-verify-extract SKILL.md P2).
  #
  # The digest and the reasoning behind it live at the closure-digest loop
  # further down (search: "Dependency-closure digests"). Read that before
  # touching the skip predicate.
  #
  # SUPERSEDED SAFETY ARGUMENT, kept because this comment stated it as
  # settled fact and it was wrong (issue #320). It ran: a dependency-only
  # change (Parser.FastString.fst edited, Parser.IRI.fst untouched)
  # changes Parser.IRI.fst.checked's hash (F* embeds dependency digests)
  # but leaves the extracted Parser_IRI.ml BYTE-IDENTICAL, so skipping on
  # the DEPENDENT's own .fst hash is safe; and the residual risk — a
  # dependency changing its OCaml-level signature incompatibly — is caught
  # loudly at ocamlopt compile time.
  #
  # Both observations are true and the conclusion still does not follow.
  # The argument is about EXTRACTION OUTPUT, but the skip also suppresses
  # VERIFICATION. A dependency can change semantically while its extracted
  # signature stays identical; that invalidates any theorem an unchanged
  # dependent states about it, and precisely because the .ml is
  # byte-identical, ocamlopt has nothing to catch. The developer sees
  # green. Confirmed experimentally 2026-07-29 — transcript in the
  # closure-digest comment below.
  #
  # `--force-full` remains the escape hatch for anyone who wants to bypass
  # the manifest and reprocess every module regardless.
  # ---------------------------------------------------------------------
  EXTRACT_STATE_DIR="$OUTDIR/.extract-state"
  mkdir -p "$EXTRACT_STATE_DIR"
  MANIFEST_FILE="$EXTRACT_STATE_DIR/manifest.tsv"
  touch "$MANIFEST_FILE"

  # FORCE_FULL is parsed at the top of this script from the flag
  # partition, not from "$2" -- reading "$2" broke the moment the
  # multi-step loop started re-invoking each step on its own.
  if [[ "$FORCE_FULL" -eq 1 ]]; then
    echo "  --force-full: ignoring incremental-extract manifest; re-extracting every module."
  fi

  declare -A CURRENT_HASH=()

  # All modules extracted with full verification (no --lax)
  # Extraction MUST succeed for every module — no silent failures
  echo "  Extracting all F* modules (verified)..."
  EXTRACT_COUNT=0
  EXTRACT_SKIPPED=0

  # ---------------------------------------------------------------------
  # Layered parallel verify + extract (2026-07-04, build-speed P1).
  #
  # ALL_MODULES below is still the enumeration + manifest-cleanup order —
  # a module removed from it is dropped from the manifest, same
  # "self-cleaning manifest" behavior as before. Actual scheduling no
  # longer follows this hand order: fstar.exe --dep full computes the
  # real dependency DAG among these modules ONCE per invocation (~0.3s
  # measured on the full 96-module list, 2026-07-04 -- cheap enough that
  # a no-op run still finishes in ~1s), the DAG is Kahn-layered, and each
  # layer's modules run through a bounded parallel pool (BUILD_JOBS,
  # default nproc, capped at nproc). A barrier separates layers: modules
  # in one layer depend only on modules that an earlier layer has already
  # fully processed, so no two concurrent fstar.exe invocations ever race
  # on writing the same .checked file (the 2026-05-07 hazard documented
  # in skills/fast-verify-extract/SKILL.md -- concurrent ad-hoc fstar.exe
  # over overlapping modules corrupts .checked). Modules within a layer
  # are mutually independent given everything below them is verified, so
  # concurrent writers never target the same .checked target.
  #
  # Failure semantics: a layer runs to completion even if one of its
  # modules fails (xargs does not stop early on a failing item -- it
  # keeps launching the rest of the layer's queue), so every failure in
  # that layer is reported together; the NEXT layer never starts once any
  # failure is recorded (fail-fast at LAYER granularity, not module
  # granularity -- a downstream layer may depend on the failed module's
  # .checked, so proceeding would just cascade confusing secondary
  # failures).
  #
  # The incremental-extract manifest above is untouched: a module whose
  # source hash matches its manifest entry (and whose .ml already exists)
  # still skips fstar.exe entirely, inline in the worker, before any
  # process is spawned for it -- the DAG/layering only changes how the
  # modules that DO need real work get scheduled.
  #
  # Dependency order (informational -- kept from the pre-P1 comment; the
  # real schedule now comes from --dep full, not this hand annotation):
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
  # ---------------------------------------------------------------------
  ALL_MODULES=(
    Dep.Reachability.fst
    Regex.Syntax.fst Regex.Derivative.fst Regex.Exec.fst Regex.XSDPattern.fst
    RDF.Format.fst
    RDF.Vocabulary.fst
    RDF.Term.fst
    RDF.Triple.fst
    RDF.Indexed.fst
    RDF.Graph.fst
    RDF.Vocabulary.Axioms.fst
    RDFS.Closure.fst
    RDFS.Closure.SemiNaive.fst
    RDFS.SchemaSplit.fst
    OWL.Closure.fst
    OWL.Semantics.fst
    OWL.Semantics.MemLemmas.fst
    OWL.Semantics.Soundness.fst
    RDF.Indexed.KeyInjectivity.fst
    RDF.Graph.Executable.fst Parquet.Footer.fst
    RDF.IRI.fst
    RDF.NQuads.Serialize.fst
    RDF.Entailment.Simple.fst
    RDF.Entailment.Simple.Spec.fst
    RDF.Entailment.Simple.Refinement.fst
    RDF.Entailment.Simple.ModelTheory.fst
    RDF.Entailment.Simple.Boundary.fst
    RDF.Entailment.RDF.Spec.fst
    RDF.Entailment.RDFS.Spec.fst
    OWL.RL.Spec.fst
    OWL.RL.Refinement.fst
    RDF.Entailment.RDFS.Refinement.fst
    RDF.Entailment.RDFS.SepFree.fst
    RDF.Entailment.RDFS.ModelTheory.fst
    RDF.Entailment.RDFS.ChainWf.fst
    RDF.Entailment.RDFS.RhoDFClosure.fst
    RDF.Entailment.RDFSPlus.fst
    RDF.Entailment.RegimeDispatch.fst
    SPARQL.Protocol.RoundTrip.fst
    RDF.List.Helpers.fst
    RDF.Bytes.fst
    RDF.Store.Loader.fst
    RDF.Dataset.Graphs.fst
    RDF.Canonical.fst
    RDF.Canonical.Manifest.fst
    RDF.GraphIsomorphism.fst
    OWL.Vocabulary.fst
    OWL.DirectMapping.Filter.fst
    XSD.Facets.fst
    Tableau.fst Tableau.Refute.fst Tableau.CountingOracle.fst SPARQL11.IRI.Resolve.fst SPARQL.FullText.fst SPARQL11.Algebra.fst
    SPARQL11.Algebra.Spec.fst
    SPARQL11.Algebra.Refinement.fst
    RDF.Semantics.HypothesisWitness.fst
    XSD.Datatypes.fst
    RDF.Entailment.RDFS.DatatypeClash.fst
    XSD.IEEE754.fst
    RDF.Entailment.Regime.fst
    RDF.Pretty.fst
    OWL.QueryRewrite.fst OWL.QueryEval.fst
    OWL.Tests.Manifest.fst OWL2.SyntaxDL.fst
    RIF.Core.Syntax.fst RIF.Core.Translation.fst
    SHACL.Validation.fst
    SHACL.NodeExpr.fst
    SHACL.Rules.fst
    RDF.Geo.Types.fst RDF.Geo.BBox.fst RDF.Geo.Topology.fst RDF.Geo.Functions.fst
    Parser.FastString.Spec.fst Parser.FastString.CharBoundary.fst Parser.FastString.fst Parser.FastString.ConcatSpec.fst Parser.IRI.fst
    Parser.Combinators.fst Parser.TurtleScanner.fst SPARQL11.Parser.fst Parser.WKT.fst
    Parser.NTriples.fst Parser.Turtle.fst HDT.Container.fst HDT.Dictionary.fst HDT.Triples.fst
    Parser.OWLFunctional.fst
    RDF.Turtle.Serialize.fst
    Parser.NQuads.fst Parser.TriG.fst
    Parser.XML.fst XML.Wellformedness.fst XML.Namespaces.fst Parser.XPath.fst XPath.Eval.fst XSLT.Transform.fst Schematron.Validate.fst Parser.RDFXML.fst Parser.RIFXML.fst
    GRDDL.Discovery.fst
    Math.Expr.fst Math.Subst.fst Math.Diff.fst Math.Simplify.fst Math.Matrix.fst MathML.Content.fst Math.Series.fst MathML.Present.fst Math.Sigmoid.fst XForms.Bind.fst
    RIF.Core.Builtins.fst RIF.Core.Conformance.fst
    RIF.Core.Eval.fst RIF.Core.Tests.fst
    Parser.SRX.fst Parser.CSVResults.fst
    Parser.JSONResults.fst
    SPARQL.JSON.Escape.fst
    Parser.JSON.fst JSONLD.Loader.fst JSONLD.Context.fst JSONLD.Expand.fst Parser.JSONLD.fst Parser.JSONLD.Html.fst JSONLD.Compact.fst JSONLD.Flatten.fst JSONLD.FromRdf.fst JSONLD.Frame.fst JSONSchema.Validate.fst
    ShEx.Schema.fst Parser.ShExC.fst ShEx.SchemaEq.fst ShEx.Validation.fst
    VC.Context.fst
    VC.Credential.fst
    VC.Multibase.fst
    DID.Key.fst
    VC.DataIntegrity.fst
    RML.Mapping.fst RML.Sources.fst RML.Eval.fst
    CSVW.Metadata.fst CSVW.URITemplate.fst CSVW.Formats.fst CSVW.Conversion.fst CSVW.Json.fst CSVW.Validate.fst
    SPARQL.Eval.TimeBudget.fst
    SPARQL.Eval.Limits.fst
    SPARQL.HTTP.Response.fst
    SPARQL.HTTP.BackendInfo.fst
    SPARQL.HTTP.QueriesIndex.fst
    SPARQL.HTTP.StaticFiles.fst
    SPARQL.HTTP.Admin.fst
    SPARQL.HTTP.Routes.fst
    Parser.BallyhooHDT.fst
    Parser.BallyhooCOTTAS.fst
    RDF.CottasStore.ColumnSeq.fst
    RDF.CottasStore.PageCache.fst
    RDF.CottasStore.OnDiskIndex.fst
    RDF.CottasStore.DictWriter.fst
    RDF.CottasStore.PresenceBitmap.fst
    RDF.CottasStore.PresenceWriter.fst
    RDF.CottasStore.CompoundPresenceBitmap.fst
    RDF.CottasStore.CompoundPresenceWriter.fst
    RDF.CottasStore.OffsetsWriter.fst
    RDF.CottasStore.SubjectOffsetsWriter.fst
    RDF.CottasStore.BaseWriter.fst
    RDF.CottasStore.LazyDict.fst
    RDF.CottasStore.LazyDictRegistry.fst
    RDF.Store.LazyTermCache.fst
    RDF.Store.Columnar.OffsetIndex.fst
    RDF.Store.Columnar.SubjectOffsetIndex.fst
    RDF.Store.Columnar.DeltaLog.fst
    SPARQL.Plan.Pruning.fst
    SPARQL.Plan.AccessPath.fst
    RDF.CottasStore.fst
    RDF.CottasStore.PageCache.Bounds.fst
    RDF.Store.Columnar.DeltaMerge.fst
    RDF.Store.Capabilities.fst RDF.Store.Capabilities.Cottas.fst RDF.Store.Capabilities.Delta.fst
    SPARQL.Plan.Streamable.fst
    RML.VirtualSource.fst
    SPARQL11.Store.fst
    RDF.Store.Combine.fst
    RDF.Dataset.Merge.fst
    SPARQL.Protocol.fst
    SPARQL.HTTP.RunQuery.fst
    SPARQL.Update.Sandbox.fst
    SPARQL.Update.Analysis.fst
    SPARQL.Diagnostics.fst
    SPARQL.Explain.fst
    SPARQL.Query.Analysis.fst
    SPARQL.HTTP.fst
    SPARQL.HTTP.Client.fst
    SPARQL.Protocol.Client.fst
    SPARQL.ServiceDescription.fst
    SPARQL.GraphStore.fst
  )

  # Only modules actually present on disk are scheduled (mirrors the old
  # per-module `if [ -f "$fst" ]` guard).
  PRESENT_MODULES=()
  for fst in "${ALL_MODULES[@]}"; do
    [[ -f "$fst" ]] && PRESENT_MODULES+=("$fst")
  done

  # ---------------------------------------------------------------------
  # .fsti pre-check (2026-07-05, RDF.Vocabulary — the tree's FIRST .fsti;
  # see docs/designissues/2026-07-05-foundational-core-refactor.md §2.9).
  #
  # The Kahn-layering below parses `fstar.exe --dep full`'s output for
  # `*.fst.checked:` target lines and follows only `*.fst.checked` tokens
  # in their prerequisite lists (see the DEPS[] loop just below). When a
  # module has an adjacent `.fsti`, F* instead makes every dependent's
  # `.fst.checked` depend on the interface's `.fsti.checked` -- a token
  # shape the DEPS[] parser does not recognise, so it is silently dropped
  # from the DAG (confirmed experimentally, 2026-07-05: `--dep full` on an
  # .fsti-backed module emits `Consumer.fst.checked: Consumer.fst
  # Vocab.fsti.checked`, never `Vocab.fst.checked`). Left unhandled, a
  # module that opens RDF.Vocabulary could be scheduled in an earlier
  # layer than RDF.Vocabulary.fsti itself, and find no checked interface
  # to load.
  #
  # Fix: check every `.fsti` in the tree, synchronously, before the DAG is
  # even computed -- so `*.fsti.checked` already exists by the time ANY
  # layer's fstar.exe invocations start, regardless of what the (interface-
  # blind) layering below decides. This is a deliberately narrow, low-risk
  # fix (a few lines, run once, cheap -- a pure-constant interface checks
  # in well under a second) rather than teaching the DEPS[] parser a new
  # token shape; revisit only if a second `.fsti` lands and this becomes a
  # recurring cost.
  shopt -s nullglob
  FSTI_FILES=(*.fsti)
  shopt -u nullglob
  for fsti in "${FSTI_FILES[@]}"; do
    echo "  [.fsti pre-check] $fsti"
    fstar.exe --z3version 4.13.3 --cache_checked_modules "$fsti" \
      > "$OUTDIR/_fstar_${fsti%.fsti}_fsti.log" 2>&1 \
      || { echo "FATAL: .fsti pre-check failed for $fsti -- see $OUTDIR/_fstar_${fsti%.fsti}_fsti.log" >&2; exit 1; }
  done

  # BUILD_JOBS: parallel fstar.exe invocations per layer. Defaults to the
  # container's core count; an explicit override higher than nproc is
  # clamped down to it (more workers than cores doesn't help a CPU-bound
  # SMT workload, it just adds context-switch overhead).
  NPROC="$(nproc 2>/dev/null || echo 4)"
  BUILD_JOBS="${BUILD_JOBS:-$NPROC}"
  if (( BUILD_JOBS > NPROC )); then BUILD_JOBS="$NPROC"; fi
  if (( BUILD_JOBS < 1 )); then BUILD_JOBS=1; fi
  echo "  BUILD_JOBS=$BUILD_JOBS (nproc=$NPROC)"

  # Compute the dependency DAG once via --dep full (make-format rules),
  # restricted to edges between modules in our own list -- ulib/Prims/
  # FStar.* deps are dropped from the graph; F* resolves those from the
  # pre-checked stdlib regardless of our layering.
  DEPEND_FILE="$EXTRACT_STATE_DIR/depend.make"
  fstar.exe --dep full "${PRESENT_MODULES[@]}" > "$DEPEND_FILE" 2> "$EXTRACT_STATE_DIR/depend.log" \
    || { echo "FATAL: fstar.exe --dep full failed -- see $EXTRACT_STATE_DIR/depend.log" >&2; exit 1; }

  declare -A MOD_SET=()
  for m in "${PRESENT_MODULES[@]}"; do MOD_SET["$m"]=1; done

  JOINED_DEPEND="$EXTRACT_STATE_DIR/depend-joined.make"
  awk '{
    if (sub(/\\$/, "")) { buf = buf $0 " "; next }
    else { print buf $0; buf="" }
  }' "$DEPEND_FILE" > "$JOINED_DEPEND"

  declare -A DEPS=()
  while IFS= read -r line; do
    [[ "$line" == *".fst.checked:"* ]] || continue
    target="${line%%:*}"
    target="${target%.checked}"
    target="${target##*/}"
    [[ -n "${MOD_SET[$target]:-}" ]] || continue
    rest="${line#*:}"
    deps=""
    for tok in $rest; do
      case "$tok" in
        *.fst.checked)
          dep="${tok%.checked}"
          dep="${dep##*/}"
          [[ -n "${MOD_SET[$dep]:-}" ]] && deps+="$dep "
          ;;
        *.fsti.checked)
          # Interface-backed dependency. When a module has an adjacent
          # .fsti, --dep full makes every dependent's .fst.checked depend
          # on the INTERFACE's .fsti.checked and never on the
          # implementation's .fst.checked, so this token shape is the only
          # evidence of the edge. Dropping it (as this parser did until
          # 2026-07-29) loses real dependencies on the eight .fsti-backed
          # modules: RDF.Term, RDF.Triple, RDF.Graph, RDF.Indexed,
          # RDF.Vocabulary, RDF.IRI, OWL.Closure, RDFS.Closure. Measured on
          # the real graph: 441 edges without this case, 503 with it, and
          # RDF.Entailment.Simple's transitive closure goes from 1 module
          # to 9 -- RDF.Term among them.
          #
          # That was survivable while layering was the only consumer (the
          # synchronous .fsti pre-check above makes every .fsti.checked
          # exist before any layer starts, which is why the old comment
          # called teaching this parser a new token shape unnecessary). It
          # is NOT survivable now that the same DEPS map feeds the
          # dependency-closure digest (issue #320): without this case,
          # editing RDF.Term.fst would not invalidate anything that
          # consumes it through RDF.Term.fsti.
          #
          # Self-edges are excluded: a module's own .fst.checked depends on
          # its own .fsti.checked, which would be read as a cycle.
          dep="${tok%.checked}"
          dep="${dep##*/}"
          dep="${dep%i}"
          [[ "$dep" != "$target" ]] && [[ -n "${MOD_SET[$dep]:-}" ]] && deps+="$dep "
          ;;
      esac
    done
    DEPS["$target"]="$deps"
  done < "$JOINED_DEPEND"

  # Kahn-layer the DAG: layer 0 = modules with no in-list deps; layer k+1
  # = modules whose in-list deps are all already placed in layers <= k.
  declare -A PLACED=()
  remaining=("${PRESENT_MODULES[@]}")
  LAYERS=()
  while [[ ${#remaining[@]} -gt 0 ]]; do
    this_layer=()
    next_remaining=()
    for m in "${remaining[@]}"; do
      ready=1
      for d in ${DEPS[$m]:-}; do
        [[ -n "${PLACED[$d]:-}" ]] || { ready=0; break; }
      done
      if [[ "$ready" -eq 1 ]]; then this_layer+=("$m"); else next_remaining+=("$m"); fi
    done
    if [[ ${#this_layer[@]} -eq 0 ]]; then
      echo "FATAL: dependency cycle detected among: ${next_remaining[*]}" >&2
      exit 1
    fi
    for m in "${this_layer[@]}"; do PLACED["$m"]=1; done
    LAYERS+=("${this_layer[*]}")
    remaining=("${next_remaining[@]}")
  done
  echo "  Dependency DAG: ${#PRESENT_MODULES[@]} modules in ${#LAYERS[@]} layer(s)"

  # ---------------------------------------------------------------------
  # Dependency-closure digests (2026-07-29, issue #320).
  #
  # WHAT WAS WRONG. The manifest used to key its skip decision on a
  # module's OWN source hash, justified by an experiment showing that an
  # interface-preserving edit to a dependency leaves the dependent's
  # extracted .ml byte-identical, with incompatible signature changes
  # caught at ocamlopt link time. That argument is sound for EXTRACTION
  # and unsound for PROOFS. A dependency can change SEMANTICALLY while
  # its extracted OCaml signature stays identical; that invalidates any
  # theorem an unchanged dependent states about it, and neither the
  # dependent's own hash nor the OCaml compiler can see it.
  #
  # This is not hypothetical. Demonstrated end-to-end on 2026-07-29 in a
  # scratch copy of this tree, against this script:
  #   ZZGap.Dep.fst   let bump (x:nat) : nat = x + 1
  #   ZZGap.Thm.fst   let lemma_bump_increases (x:nat) : Lemma (bump x > x) = ()
  # Changing bump to `if x = 0 then 0 else x - 1` -- same extracted type
  # Prims.nat -> Prims.nat -- and re-running `./build-ocaml.sh extract`
  # gave: "ZZGap.Thm.fst (up to date, skipped)", "Re-extracted modules: 1
  # (190 skipped)", BUILD_STATUS=OK, exit 0. ZZGap_Thm.ml was
  # byte-identical, so ocamlopt had nothing to catch. Verifying
  # ZZGap.Thm.fst by hand: "Error 19 ... Could not prove post-condition".
  # A green build over a false theorem.
  #
  # The gap matters more now than when the manifest was written. Modules
  # then mostly carried totality and refinements; OWL.Semantics.Soundness
  # and friends now state theorems ABOUT OTHER MODULES' functions, which
  # is exactly the case the own-hash skip mishandles.
  #
  # THE FIX. Key the skip on the module's DEPENDENCY-CLOSURE digest
  # instead: sha256 over the module's own source hash plus the closure
  # digests of every in-list dependency. LAYERS is already in topological
  # order, so one pass computes them all -- a dependency's digest is
  # always final before any dependent needs it. Any change anywhere in a
  # module's transitive dependencies now changes its digest and forces
  # real re-verification, whether or not the change was visible to OCaml.
  #
  # Digests go in closure.tsv rather than being recomputed per worker:
  # workers are forked processes that cannot read the parent's arrays,
  # and a worker cannot compute its own closure without walking the DAG
  # again anyway.
  #
  # COST, honestly. Editing a wide-fanout hub module (RDF.Graph.Executable,
  # SPARQL11.Algebra) now re-verifies its dependents instead of silently
  # skipping them. That is real correctness work, not the waste the
  # manifest was built to remove: the previous behaviour bought its speed
  # by not checking things that needed checking. Edits to leaf modules --
  # most format/parser modules depend on nothing else in the list -- are
  # unaffected, and the layered parallel scheduler above is what absorbs
  # the hub case. `--force-full` remains the "reprocess everything"
  # escape hatch.
  #
  # WHAT THIS STILL DOES NOT COVER (do not read the digest as a proof of
  # currency): a changed patch script under ocaml-patches.sh does not
  # move any .fst hash, so an already-patched .ml is still left alone --
  # see the P2 write-up in skills/fast-verify-extract/SKILL.md for the
  # invalidate-and-delete recipe. Nor does it cover an F* or z3 version
  # change; .checked digests handle that separately.
  #
  # Manifests written before this change hold bare source hashes, which
  # no longer match any closure digest, so the first run after it
  # re-extracts everything once and then self-heals.
  # ---------------------------------------------------------------------
  declare -A OWN_HASH=()
  for m in "${PRESENT_MODULES[@]}"; do
    # Issue #293: the digest must cover the sibling .fsti too -- interface
    # files carry real definitions, so a .fsti-only edit must invalidate.
    if [[ -f "${m}i" ]]; then
      OWN_HASH["$m"]="$(cat "$m" "${m}i" | sha256sum | awk '{print $1}')"
    else
      OWN_HASH["$m"]="$(sha256sum "$m" | awk '{print $1}')"
    fi
  done

  declare -A CLOSURE_HASH=()
  CLOSURE_FILE="$EXTRACT_STATE_DIR/closure.tsv"
  : > "$CLOSURE_FILE"
  for layer in "${LAYERS[@]}"; do
    read -ra closure_layer_mods <<< "$layer"
    for m in "${closure_layer_mods[@]}"; do
      dep_digest=""
      if [[ -n "${DEPS[$m]:-}" ]]; then
        # Sorted, so the digest does not depend on --dep full's ordering.
        while IFS= read -r d; do
          [[ -n "$d" ]] || continue
          dep_digest+="${CLOSURE_HASH[$d]:-UNRESOLVED} "
        done < <(printf '%s\n' ${DEPS[$m]} | sort -u)
      fi
      CLOSURE_HASH["$m"]="$(printf '%s|%s' "${OWN_HASH[$m]}" "$dep_digest" | sha256sum | awk '{print $1}')"
      printf '%s\t%s\n' "$m" "${CLOSURE_HASH[$m]}" >> "$CLOSURE_FILE"
    done
  done

  # Per-module worker: inline manifest skip-check, then fstar.exe if
  # needed. This runs as a forked `bash -c` under xargs -P, so it cannot
  # share the parent's associative arrays -- it reads the manifest file
  # directly for its own previous hash and drops its result in a
  # per-module status file for the parent to collect after the layer's
  # barrier (parent-side bookkeeping: EXTRACT_COUNT/EXTRACT_SKIPPED/
  # CURRENT_HASH/MANIFEST_FILE, all unchanged in shape from before P1).
  EXTRACT_STATUS_DIR="$EXTRACT_STATE_DIR/status"
  mkdir -p "$EXTRACT_STATUS_DIR"

  extract_worker() {
    local fst="$1"
    local out_ml="$OUTDIR/${fst%.fst}"
    out_ml="${out_ml//./_}.ml"
    local status_file="$EXTRACT_STATUS_DIR/${fst//./_}.status"
    local fst_hash
    # The staleness key is the DEPENDENCY-CLOSURE digest the parent
    # computed into $CLOSURE_FILE (issue #320 -- see the long comment at
    # the closure-digest loop for why the module's own hash was unsound
    # for proof-carrying modules). It already folds in the sibling .fsti
    # (issue #293) and every transitive in-list dependency.
    fst_hash="$(awk -F'\t' -v m="$fst" '$1==m{h=$2} END{print h}' "$CLOSURE_FILE")"
    if [[ -z "$fst_hash" ]]; then
      # No digest for this module means the parent could not place it in
      # the DAG. Never skip on missing information -- fall through to a
      # real fstar.exe run, and use a value that cannot match a manifest
      # entry so the skip test below is guaranteed to fail.
      echo "    [$fst] no closure digest available -- verifying rather than skipping"
      fst_hash="no-closure-digest"
    fi
    local prev_hash
    prev_hash="$(awk -F'\t' -v m="$fst" '$1==m{h=$2} END{print h}' "$MANIFEST_FILE")"

    if [[ "$FORCE_FULL" -eq 0 ]] && [[ -f "$out_ml" ]] \
       && [[ -n "$prev_hash" ]] && [[ "$prev_hash" == "$fst_hash" ]]; then
      echo "    $fst (up to date, skipped -- module and its whole dependency closure unchanged)"
      printf '%s\tSKIP\t%s\n' "$fst" "$fst_hash" > "$status_file"
      return 0
    fi

    echo "    [$fst]"
    local fstar_rc=0
    local fstar_log="$OUTDIR/_fstar_${fst%.fst}.log"
    fstar.exe --z3version 4.13.3 --codegen OCaml --odir "$OUTDIR" \
      --cache_checked_modules "$fst" > "$fstar_log" 2>&1 || fstar_rc=$?
    grep -E "Extracted|Error|error" "$fstar_log" | sed "s/^/    [$fst] /" || true
    # The EXIT CODE is the authority, not the presence of an "Extracted
    # module" line (issue #320, found 2026-07-29). F* emits that line even
    # when verification FAILED: a module whose proof obligation Z3 could
    # not discharge exits 1, prints "Error 19 ... Could not prove
    # post-condition", and still prints "Extracted module <M>" and writes
    # the .ml. The old test grepped only for that line, so a module that
    # failed to verify was recorded OK and the build reported
    # BUILD_STATUS=OK -- exactly the "no silent failures" property this
    # step's header claims. Demonstrated with a deliberately false lemma;
    # fstar.exe exited 1 while the extract loop went green.
    if [[ "$fstar_rc" -ne 0 ]] || ! grep -q "^Extracted module" "$fstar_log"; then
      echo "    [$fst] ERROR: verification or extraction FAILED (fstar.exe exit code $fstar_rc) -- see $fstar_log"
      printf '%s\tFAIL\t%s\n' "$fst" "$fst_hash" > "$status_file"
      return 1
    fi
    printf '%s\tOK\t%s\n' "$fst" "$fst_hash" > "$status_file"
    return 0
  }
  export -f extract_worker
  export OUTDIR MANIFEST_FILE FORCE_FULL EXTRACT_STATUS_DIR CLOSURE_FILE

  FAILED_MODULES=()
  layer_idx=0
  for layer in "${LAYERS[@]}"; do
    read -ra layer_mods <<< "$layer"
    echo "  -- layer $layer_idx: ${#layer_mods[@]} module(s)"
    rm -f "$EXTRACT_STATUS_DIR"/*.status 2>/dev/null || true

    # Layer heartbeat: worker output streams straight to the terminal
    # (each line already prefixed with its module name), while a 30s
    # pulse fires if the layer's long pole is still silent -- same
    # watchdog rationale as run_with_heartbeat, adapted for a whole
    # parallel layer instead of a single fstar.exe invocation.
    LAYER_LOG="$OUTDIR/_layer_${layer_idx}.log"
    : > "$LAYER_LOG"
    set +e
    ( printf '%s\n' "${layer_mods[@]}" \
        | xargs -P "$BUILD_JOBS" -I{} bash -c 'extract_worker "$@"' _ {} \
        2>&1 | tee -a "$LAYER_LOG" ) &
    layer_pid=$!
    t0=$(date +%s)
    # Poll at 0.2s granularity and only EMIT a heartbeat every ~30s. The
    # earlier `sleep 30; kill -0 || break` shape cost a flat 30s per layer
    # even when every module skipped, because the layer's work finished
    # during the first sleep and the loop still had to wake before
    # noticing. Silent, so it never showed in a log: 7 layers x 30s =
    # 3m30s of pure sleep on a no-op run. (That is also the true cause of
    # the 3m30s no-op recorded in fast-verify-extract P1, which blamed an
    # unrelated CPU-bound process -- see the 2026-07-29 correction there.
    # The sibling fix at the run_with_heartbeat loop above landed with
    # #320; this is the same bug at the extract-layer barrier, which is
    # the site that actually dominates a warm no-op.)
    hb_last=$t0
    while kill -0 "$layer_pid" 2>/dev/null; do
      sleep 0.2
      kill -0 "$layer_pid" 2>/dev/null || break
      now=$(date +%s)
      if [ $(( now - hb_last )) -ge 30 ]; then
        hb_last=$now
        echo "      …layer ${layer_idx} still running ($(( now - t0 ))s elapsed)"
      fi
    done
    wait "$layer_pid"
    set -e

    layer_failed=0
    for m in "${layer_mods[@]}"; do
      status_file="$EXTRACT_STATUS_DIR/${m//./_}.status"
      if [[ ! -f "$status_file" ]]; then
        echo "  MISSING STATUS for $m (worker crashed before writing status)" >&2
        layer_failed=1
        FAILED_MODULES+=("$m")
        continue
      fi
      IFS=$'\t' read -r smod sstatus shash < "$status_file"
      case "$sstatus" in
        SKIP)
          EXTRACT_SKIPPED=$((EXTRACT_SKIPPED + 1))
          CURRENT_HASH["$m"]="$shash"
          ;;
        OK)
          EXTRACT_COUNT=$((EXTRACT_COUNT + 1))
          CURRENT_HASH["$m"]="$shash"
          printf '%s\t%s\n' "$m" "$shash" >> "$MANIFEST_FILE"
          ;;
        FAIL)
          layer_failed=1
          FAILED_MODULES+=("$m")
          ;;
      esac
    done

    if [[ "$layer_failed" -ne 0 ]]; then
      echo ""
      echo "FATAL: layer ${layer_idx} had failures: ${FAILED_MODULES[*]}" >&2
      echo "       (later layers not started -- they may depend on the failed module(s))" >&2
      exit 1
    fi
    layer_idx=$((layer_idx + 1))
  done

  # Compact the manifest to one line per module (the loop above appends,
  # so a module reprocessed across retries could have duplicate lines).
  # Only reached on full success, so CURRENT_HASH covers every module in
  # the extract list — reprocessed ones (fresh hash) and skipped ones
  # (hash carried over unchanged) alike. Any module removed from the list
  # entirely is naturally dropped here (self-cleaning manifest).
  {
    for manifest_mod in "${!CURRENT_HASH[@]}"; do
      printf '%s\t%s\n' "$manifest_mod" "${CURRENT_HASH[$manifest_mod]}"
    done
  } > "$MANIFEST_FILE.tmp"
  mv "$MANIFEST_FILE.tmp" "$MANIFEST_FILE"

  echo "  RDF:    $(wc -l < "$OUTDIR/RDF_Graph_Executable.ml") lines"
  echo "  SPARQL: $(wc -l < "$OUTDIR/SPARQL11_Algebra.ml") lines"
  if [[ "$EXTRACT_COUNT" -eq 0 ]]; then
    echo "  Extraction outputs already up to date; no F* modules re-extracted (${EXTRACT_SKIPPED} skipped)."
  else
    echo "  Re-extracted modules: $EXTRACT_COUNT (${EXTRACT_SKIPPED} skipped as unchanged)"
  fi
  record_phase_timing "extract-loop" "$PHASE_START_EXTRACT" "$EXTRACT_COUNT"

  # Step-5 OCaml compatibility shim (docs/designissues/2026-07-05-
  # foundational-core-refactor.md §2.1/§2.2/§3.3 step 5), extended at
  # step 6 (§2.3/§2.4/§3.3) for RDF.Indexed/RDFS.Closure/OWL.Closure.
  # RDF.Term/RDF.Triple/RDF.Graph hold the core term/triple/graph
  # types; RDF.Indexed holds the indexed_graph acceleration structure
  # (folded in fully at step 6); RDFS.Closure/OWL.Closure hold the
  # RDFS/OWL-RL closure rules moved out of RDF.Graph.Executable.fst at
  # step 6. RDF.Graph.Executable.fst re-exports all six via F* `include`
  # so its own remaining code and all 53 `open RDF.Graph.Executable`
  # dependents (plus Tableau.fst/SHACL.Validation.fst/
  # RDF.Vocabulary.Axioms.fst/OWL.QueryRewrite.fst/
  # Parser.OWLFunctional.fst's direct closure-function callers) keep
  # resolving T_IRI/wf_iri/triple/indexed_graph/rdfs_closure/
  # entailment_closure/owl_rule_*/etc. unqualified.
  # F*'s `include` has no OCaml-extraction artifact of its own (a
  # module that only `include`s another extracts to an empty `.ml`
  # beyond `open Prims` -- confirmed empirically before relying on
  # this), so the *qualified* OCaml references this tree's hand-
  # written glue makes (`RDF_Graph_Executable.T_IRI`, `.wf_iri`,
  # `.rdf_graph`, `.indexed_graph`, `.entailment_closure`, etc., in
  # experimental_ocaml_glue/*.sh, w3c_runner.ml/factoidal_cli.ml/
  # rif_runner.ml, and the other bin/<consumer>/*.ml files) would
  # otherwise go unbound. A real OCaml `include` -- unlike F*'s --
  # DOES re-export constructors and record field labels under the
  # includer's namespace, so prepending one restores exactly that
  # compatibility with zero edits to any consumer. Order matches
  # COMMON_MODULES' compile order (RDF_Term/RDF_Triple/RDF_Graph before
  # RDF_Indexed before RDFS_Closure/OWL_Closure) so each named module's
  # .cmi/.cmx already exists when RDF_Graph_Executable.ml compiles.
  # Idempotent (checked via the marker line) so re-running extract on
  # an already-patched file is a no-op. Retire this block at design-doc
  # step 7, once every consumer's qualified reference is updated to
  # name RDF_Term/RDF_Triple/RDF_Graph/RDF_Indexed/RDFS_Closure/
  # OWL_Closure directly.
  RGE_ML="$OUTDIR/RDF_Graph_Executable.ml"
  if [[ -f "$RGE_ML" ]] && ! grep -q '^include RDF_Term$' "$RGE_ML"; then
    { printf 'include RDF_Term\ninclude RDF_Triple\ninclude RDF_Graph\ninclude RDF_Indexed\ninclude RDFS_Closure\ninclude RDFS_Closure_SemiNaive\ninclude RDFS_SchemaSplit\ninclude OWL_Closure\n'; cat "$RGE_ML"; } > "$RGE_ML.tmp"
    mv "$RGE_ML.tmp" "$RGE_ML"
  fi

  # Apply post-extraction patches (assume-val stubs, IRI resolution, validation, etc.)
  PHASE_START_PATCHES=$(date +%s)
  ./ocaml-patches.sh "$OUTDIR"
  record_phase_timing "patches" "$PHASE_START_PATCHES" "$EXTRACT_COUNT"
  echo ""
fi

# Step 2: Compile native OCaml binaries
if [[ "$STEP" == "all" || "$STEP" == "compile" ]]; then
  echo "--- Step 2: Compile native OCaml ---"
  PHASE_START_COMPILE=$(date +%s)
  # NOTE (2026-07-29): the stale-artifact purge used to live HERE, before
  # the needs_rebuild check ~250 lines below. That made a NO-OP compile
  # destructive: it deleted all 184 committed *.cmi/*.cmx/*.o, printed
  # "already up to date; skipping ocamlopt rebuild", and exited
  # BUILD_STATUS=OK — leaving 184 deletions in the working tree and, worse,
  # destroying the artifacts `tools/repo-hygiene.sh` uses as its LIVENESS
  # ORACLE ("a module is either LIVE (has a .cmx) or DEAD (no .cmx)" — the
  # check that identified the dead PageCache.Bounds module, #327). The purge
  # is now inside the rebuild branch, so it only runs when a rebuild will
  # actually regenerate what it removed. Do not hoist it back out.
  cd "$OUTDIR"

  # Common modules for all binaries. fstar_pure_hashes.ml must precede
  # SPARQL11_Algebra.ml because the post-extraction patch wires the
  # hash_* assume-vals to Fstar_pure_hashes.{md5,sha1,sha256,sha384,sha512}.
  #
  # Ballyhoo/Parquet ordering: Parquet_Footer before Parser_BallyhooCOTTAS
  # (COTTAS runtime glue calls Parquet_Footer.probe_*). SPARQL11_Store
  # depends on Parser_BallyhooHDT and Parser_BallyhooCOTTAS. See
  # docs/designissues/2026-04-19-cottas-parquet-wiring-plan.md §Phase 1.
  # Parser_FastString_Spec.ml precedes RDF_Bytes.ml (issue #445): RDF.Bytes.fst
  # now calls Parser.FastString.Spec's UTF-8 codec (utf8_bytes/utf8_decode_all)
  # from bytes_of_string/bytes_to_string, so the extracted .ml must compile in
  # that order. Parser.FastString.Spec has zero project-module dependencies
  # (only opens FStar.Mul/FStar.List.Tot), so moving it here introduces no
  # cycle -- confirmed by reading its `open`s directly, not assumed.
  COMMON_MODULES="Dep_Reachability.ml Regex_Syntax.ml Regex_Derivative.ml Regex_Exec.ml Regex_XSDPattern.ml RDF_Format.ml RDF_Vocabulary.ml RDF_Term.ml RDF_Triple.ml RDF_Indexed.ml RDF_Graph.ml RDF_Vocabulary_Axioms.ml RDFS_Closure.ml RDFS_Closure_SemiNaive.ml RDFS_SchemaSplit.ml OWL_Closure.ml RDF_Graph_Executable.ml RDF_List_Helpers.ml Parser_FastString_Spec.ml RDF_Bytes.ml RDF_Store_Loader.ml Parquet_Footer.ml OWL_Vocabulary.ml OWL_DirectMapping_Filter.ml XSD_Facets.ml Tableau.ml Tableau_Refute.ml Tableau_CountingOracle.ml \
    Parser_FastString_CharBoundary.ml Parser_FastString.ml Parser_FastString_ConcatSpec.ml RDF_IRI.ml SPARQL11_IRI_Resolve.ml Parser_IRI.ml \
    Parser_Combinators.ml Parser_TurtleScanner.ml Parser_NTriples.ml \
    RDF_NQuads_Serialize.ml RDF_Entailment_Simple.ml \
    RDF_Entailment_RDFS_RhoDFClosure.ml RDF_Entailment_RDFSPlus.ml RDF_Entailment_RegimeDispatch.ml \
    Parser_Turtle.ml HDT_Container.ml HDT_Dictionary.ml HDT_Triples.ml \
    RDF_Geo_Types.ml RDF_Geo_BBox.ml Parser_WKT.ml RDF_Geo_Topology.ml RDF_Geo_Functions.ml \
    Parser_OWLFunctional.ml \
    RDF_Turtle_Serialize.ml \
    Parser_NQuads.ml Parser_TriG.ml Parser_XML.ml XML_Wellformedness.ml XML_Namespaces.ml Parser_XPath.ml XPath_Eval.ml XSLT_Transform.ml Schematron_Validate.ml Parser_RDFXML.ml Math_Expr.ml Math_Subst.ml Math_Diff.ml Math_Simplify.ml Math_Matrix.ml MathML_Content.ml Math_Series.ml MathML_Present.ml Math_Sigmoid.ml \
    Parser_SRX.ml Parser_CSVResults.ml \
    SPARQL_JSON_Escape.ml \
    Parser_JSON.ml Parser_JSONResults.ml JSONLD_Loader.ml JSONLD_Context.ml JSONLD_Expand.ml Parser_JSONLD.ml Parser_JSONLD_Html.ml JSONLD_Compact.ml JSONLD_Flatten.ml JSONLD_FromRdf.ml JSONLD_Frame.ml JSONSchema_Validate.ml \
    SPARQL_Eval_TimeBudget.ml \
    SPARQL_Eval_Limits.ml \
    SPARQL_HTTP_Response.ml \
    \
    SPARQL_HTTP_BackendInfo.ml \
    SPARQL_HTTP_QueriesIndex.ml \
    SPARQL_HTTP_StaticFiles.ml \
    SPARQL_HTTP_Admin.ml \
    SPARQL_HTTP_Routes.ml \
    \
    Parser_BallyhooHDT.ml Parser_BallyhooCOTTAS.ml \
    RDF_CottasStore_ColumnSeq.ml \
    RDF_CottasStore_PageCache.ml \
    RDF_CottasStore_OnDiskIndex.ml \
    RDF_CottasStore_DictWriter.ml \
    RDF_CottasStore_PresenceBitmap.ml \
    RDF_CottasStore_PresenceWriter.ml \
    RDF_CottasStore_CompoundPresenceBitmap.ml \
    RDF_CottasStore_CompoundPresenceWriter.ml \
    RDF_CottasStore_OffsetsWriter.ml \
    RDF_CottasStore_SubjectOffsetsWriter.ml \
    RDF_CottasStore_BaseWriter.ml \
    RDF_CottasStore_LazyDict.ml \
    RDF_CottasStore_LazyDictRegistry.ml \
    RDF_Store_LazyTermCache.ml \
    RDF_Store_Columnar_OffsetIndex.ml RDF_Store_Columnar_SubjectOffsetIndex.ml RDF_Store_Columnar_DeltaLog.ml \
    SPARQL_Plan_Pruning.ml \
    \
    \
    SPARQL_Plan_AccessPath.ml \
    RDF_CottasStore.ml \
    \
    fstar_pure_hashes.ml \
    RDF_Dataset_Graphs.ml \
    RDF_Canonical.ml \
    RDF_Canonical_Manifest.ml \
    RDF_GraphIsomorphism.ml \
    GRDDL_Discovery.ml \
    service_wrap_hook.ml \
    SPARQL_FullText.ml SPARQL11_Algebra.ml XSD_Datatypes.ml RDF_Entailment_RDFS_DatatypeClash.ml XSD_IEEE754.ml RDF_Entailment_Regime.ml XForms_Bind.ml RDF_Pretty.ml OWL_QueryRewrite.ml OWL_QueryEval.ml OWL_Tests_Manifest.ml OWL2_SyntaxDL.ml RIF_Core_Syntax.ml Parser_RIFXML.ml RIF_Core_Translation.ml RIF_Core_Builtins.ml RIF_Core_Conformance.ml RIF_Core_Eval.ml RIF_Core_Tests.ml SPARQL11_Parser.ml SHACL_Validation.ml SHACL_NodeExpr.ml SHACL_Rules.ml \
    ShEx_Schema.ml Parser_ShExC.ml ShEx_SchemaEq.ml ShEx_Validation.ml \
    VC_Context.ml \
    VC_Multibase.ml \
    VC_Credential.ml \
    DID_Key.ml \
    fstar_hacl_crypto.ml \
    VC_DataIntegrity.ml \
    RML_Mapping.ml RML_Sources.ml RML_Eval.ml \
    CSVW_Metadata.ml CSVW_URITemplate.ml CSVW_Formats.ml CSVW_Conversion.ml CSVW_Json.ml CSVW_Validate.ml \
    RDF_Store_Columnar_DeltaMerge.ml \
    SPARQL_Plan_Streamable.ml RDF_Store_Capabilities.ml RDF_Store_Capabilities_Cottas.ml RDF_Store_Capabilities_Delta.ml \
    RML_VirtualSource.ml \
    SPARQL11_Store.ml RDF_Store_Combine.ml RDF_Dataset_Merge.ml SPARQL_Protocol.ml SPARQL_HTTP_RunQuery.ml \
    SPARQL_Update_Sandbox.ml \
    SPARQL_Update_Analysis.ml \
    SPARQL_Diagnostics.ml \
    SPARQL_Explain.ml \
    SPARQL_Query_Analysis.ml \
    \
    SPARQL_HTTP.ml SPARQL_HTTP_Client.ml SPARQL_Protocol_Client.ml SPARQL_ServiceDescription.ml \
    SPARQL_GraphStore.ml \
   "

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

  # HACL* vendored crypto stubs (Ed25519 sign/verify + SHA-256) for the VC
  # Data Integrity eddsa-rdfc-2022 native path. Compiled once from the
  # vendored, F*/Low*-verified extracted C (third_party/hacl/, Apache-2.0)
  # plus the CAMLprim FFI (experimental_ocaml_glue/hacl_stubs.c), then linked
  # into every native binary (VC_DataIntegrity is in COMMON_MODULES).
  # Crypto sourcing policy: skills/crypto-policy/SKILL.md. NATIVE-ONLY —
  # vendored HACL* C does not link under wasm_of_ocaml (GitHub #286), so
  # VC.DataIntegrity is excluded from the js/wasm bundle. cwd is $OUTDIR.
  HACL_NATIVE_STUBS=""
  HACL_DIR="../../../third_party/hacl"
  if [[ -d "$HACL_DIR/src" ]]; then
    HACL_OBJ_DIR="hacl-obj"
    mkdir -p "$HACL_OBJ_DIR"
    OCAML_WHERE="$(ocamlfind ocamlc -where)"
    HACL_CC="${CC:-cc}"
    HACL_SRCS=(
      "$HACL_DIR/src/Hacl_Ed25519.c"
      "$HACL_DIR/src/Hacl_Curve25519_51.c"
      "$HACL_DIR/src/Hacl_Hash_SHA2.c"
      "../experimental_ocaml_glue/hacl_stubs.c"
    )
    HACL_OBJS=()
    for c in "${HACL_SRCS[@]}"; do
      o="$HACL_OBJ_DIR/$(basename "${c%.c}").o"
      HACL_OBJS+=("$o")
      if [[ ! -f "$o" || "$c" -nt "$o" ]]; then
        "$HACL_CC" -O2 -fPIC -I"$HACL_DIR/include" -I"$OCAML_WHERE" \
          -c "$c" -o "$o"
      fi
    done
    HACL_NATIVE_STUBS="${HACL_OBJS[*]}"
    echo "  HACL* crypto stubs: enabled (Ed25519 + SHA-256, vendored C)"
  else
    echo "  HACL* crypto stubs: DISABLED (third_party/hacl not found — VC crypto will failwith)"
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
    "$BINDIR/grddl_runner"
    "$BINDIR/jsonld_runner"
    "$BINDIR/jsonld_fromrdf_runner"
    "$BINDIR/jsonld_expand_runner"
    "$BINDIR/jsonld_compact_runner"
    "$BINDIR/jsonld_flatten_runner"
    "$BINDIR/jsonld_frame_runner"
    "$BINDIR/jsonld_html_runner"
    "$BINDIR/shacl_runner"
    "$BINDIR/qudt_runner"
    "$BINDIR/rml_runner"
    "$BINDIR/csvw_runner"
    "$BINDIR/vc_runner"
    "$BINDIR/did_runner"
    "$BINDIR/cottas_ondisk_smoketest"
    # Consumer runners that are built in the block below but were missing
    # from this change-detection list: a change to their bin/<name>/*.ml
    # source would stale-skip the whole native rebuild (the sources ARE in
    # NATIVE_SOURCES, but with no matching target the mtime check never
    # fires). Adding them keeps consumer-runner edits from silently landing
    # a stale binary. See workflow-gotchas-debugging hazard on this.
    "$BINDIR/xslt_runner"
    "$BINDIR/schematron_runner"
    "$BINDIR/jsonschema_runner"
    "$BINDIR/mathml_runner"
    "$BINDIR/shex_runner"
    "$BINDIR/rif_runner"
    # #330 (2026-07-30): xml_runner had no build path in this script at
    # all — target AND source both missing. Both are added.
    "$BINDIR/xml_runner"
  )
  NATIVE_SOURCES=(
    $COMMON_MODULES
    ../../../bin/w3c-runner/w3c_runner.ml
    ../../../bin/factoidal-http/factoidal_http.ml
    ../../../bin/factoidal-serve/factoidal_serve.ml
    ../../../bin/factoidal-explain/factoidal_explain.ml
    ../../../bin/factoidal-http-client/factoidal_http_client.ml
    ../../../bin/factoidal-cli/factoidal_cli.ml
    ../../../bin/factoidal-http/factoidal_http_main.ml
    ../../../bin/owl-runner/owl_runner.ml
    ../../../bin/shacl-runner/shacl_runner.ml
    ../../../bin/qudt-runner/qudt_runner.ml
    ../../../bin/rdfc10-runner/rdfc10_runner.ml
    ../../../bin/grddl-runner/grddl_runner.ml
    ../../../bin/jsonld-runner/jsonld_runner.ml
    ../../../bin/jsonld-fromrdf-runner/jsonld_fromrdf_runner.ml
    ../../../bin/jsonld-expand-runner/jsonld_expand_runner.ml
    ../../../bin/jsonld-compact-runner/jsonld_compact_runner.ml
    ../../../bin/jsonld-flatten-runner/jsonld_flatten_runner.ml
    ../../../bin/jsonld-frame-runner/jsonld_frame_runner.ml
    ../../../bin/jsonld-html-runner/jsonld_html_runner.ml
    ../../../bin/rml-runner/rml_runner.ml
    ../../../bin/csvw-runner/csvw_runner.ml
    ../../../bin/vc-runner/vc_runner.ml
    ../../../bin/did-runner/did_runner.ml
    ../../../bin/cottas-ondisk-smoketest/cottas_ondisk_smoketest.ml
    ../../../bin/xml-runner/xml_runner.ml
    ../experimental_ocaml_glue/parquet_zstd_stubs.c
    ../experimental_ocaml_glue/hacl_stubs.c
    fstar_hacl_crypto.ml
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

    # Clean stale compilation artifacts to avoid signature mismatches.
    # Deliberately inside this branch — see the note at the top of Step 2.
    #
    # PATH BUG FIXED 2026-08-03: the 2026-07-29 refactor moved this line
    # inside the rebuild branch, BELOW the `cd "$OUTDIR"` at the top of
    # Step 2 — so `"$OUTDIR"/*.cmi` globbed ocaml-output/ocaml-output/*,
    # matched nothing, and `rm -f` silently no-opped. The purge has been
    # DEAD since that refactor; the "inconsistent assumptions over
    # interface Factoidal_serve" link failures of 2026-08-02/03 were the
    # symptom. cwd here is $OUTDIR itself, so the correct globs are bare.
    rm -f ./*.cmi ./*.cmx ./*.cmo ./*.o
    # CONSUMER-DIR artifacts too (bin/factoidal-cli, bin/factoidal-serve,
    # ...): ocamlopt reuses an existing consumer .cmx when its .ml is
    # unchanged, so after an extract that moved any shared interface the
    # kept .cmx disagrees with the freshly compiled ones and the link
    # dies. bin/<platform>/ holds finished binaries only, no .cm*, so
    # the sweep is safe.
    CONSUMER_CLEAN_RC=0
    find ../../../bin -maxdepth 2 \( -name '*.cmi' -o -name '*.cmx' -o -name '*.cmo' -o -name '*.o' \) -delete 2>/dev/null || CONSUMER_CLEAN_RC=$?
    if [ "$CONSUMER_CLEAN_RC" -ne 0 ]; then
      echo "  WARNING: consumer-dir artifact sweep exited $CONSUMER_CLEAN_RC (continuing; a stale-interface link failure would surface it)"
    fi

    # W3C test runner (reads real W3C manifests, calls F*-extracted code).
    # The Ballyhoo HDT/COTTAS runtime glue pulls in Unix (Unix.open_process_full,
    # etc.), so we now always link -package unix.
    run_with_heartbeat "ocamlopt w3c_runner" "_ocamlopt_w3c_runner.log" -- \
      ocamlfind ocamlopt -package fstar.lib,str,zarith,sha,digestif.c,unix,uucp -linkpkg -w -8-14-26 \
      $STATIC_FLAGS \
      $COMMON_MODULES \
      $PARQUET_NATIVE_STUBS \
      $HACL_NATIVE_STUBS \
      ../../../bin/w3c-runner/w3c_runner.ml \
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
      ocamlfind ocamlopt -g -thread -package fstar.lib,str,zarith,sha,digestif.c,unix,uucp,threads.posix -linkpkg -w -8-14-26 \
      $STATIC_FLAGS \
      -I ../../../bin/factoidal-serve \
      -I ../../../bin/factoidal-explain \
      -I ../../../bin/factoidal-http \
      -I ../../../bin/factoidal-http-client \
      $COMMON_MODULES \
      $PARQUET_NATIVE_STUBS \
      $HACL_NATIVE_STUBS \
      ../../../bin/factoidal-http/factoidal_http.ml \
      ../../../bin/factoidal-serve/factoidal_serve.ml \
      ../../../bin/factoidal-explain/factoidal_explain.ml \
      ../../../bin/factoidal-http-client/factoidal_http_client.ml \
      ../../../bin/factoidal-cli/factoidal_cli.ml \
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
      ocamlfind ocamlopt -g -thread -package fstar.lib,str,zarith,sha,digestif.c,unix,uucp,threads.posix -linkpkg -w -8-14-26 \
      $STATIC_FLAGS \
      -I ../../../bin/factoidal-http \
      $COMMON_MODULES \
      $PARQUET_NATIVE_STUBS \
      $HACL_NATIVE_STUBS \
      ../../../bin/factoidal-http/factoidal_http.ml \
      ../../../bin/factoidal-http/factoidal_http_main.ml \
      -o "$BINDIR/factoidal-http"
    cat _ocamlopt_factoidal_http.log
    echo "  Built: bin/${PLATFORM}/factoidal-http ($(wc -c < "$BINDIR/factoidal-http") bytes)"

    # owl_runner — OWL 2 Test Cases runner (Phase 0 skeleton: reads a
    # W3C OWL test catalog via Parser_RDFXML, prints per-test identifier
    # + types, emits final count. No reasoning wired yet.
    # See docs/designissues/2026-04-24-owl-test-harness.md.
    run_with_heartbeat "ocamlopt owl_runner" "_ocamlopt_owl_runner.log" -- \
      ocamlfind ocamlopt -package fstar.lib,str,zarith,sha,digestif.c,unix,uucp -linkpkg -w -8-14-26 \
      $STATIC_FLAGS \
      $COMMON_MODULES \
      $PARQUET_NATIVE_STUBS \
      $HACL_NATIVE_STUBS \
      ../../../bin/owl-runner/owl_runner.ml \
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
      ocamlfind ocamlopt -package fstar.lib,str,zarith,sha,digestif.c,unix,uucp -linkpkg -w -8-14-26 \
      $STATIC_FLAGS \
      $COMMON_MODULES \
      $PARQUET_NATIVE_STUBS \
      $HACL_NATIVE_STUBS \
      ../../../bin/rdfc10-runner/rdfc10_runner.ml \
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

    # grddl_runner — GRDDL Stage 1 (local subset, no network) runner.
    # Reads third_party/testing/grddl/grddl-tests-normative.rdf (RDF/XML)
    # via Parser_RDFXML, discovers same-document transformation refs with
    # the F*-extracted GRDDL_Discovery (paths a+b), applies XSLT_Transform
    # + re-parses via Parser_RDFXML, and compares result graphs with
    # GRDDL_Discovery.graphs_isomorphic (RDFC-1.0 canonicalization). All
    # discovery/transform/compare logic is in F*
    # (formal/fstar/GRDDL.Discovery.fst); the runner is I/O glue only
    # (rule #11). See docs/designissues/2026-07-08-grddl-scoping.md.
    GRDDL_RC=0
    run_with_heartbeat "ocamlopt grddl_runner" "_ocamlopt_grddl_runner.log" -- \
      ocamlfind ocamlopt -package fstar.lib,str,zarith,sha,digestif.c,unix,uucp -linkpkg -w -8-14-26 \
      $STATIC_FLAGS \
      $COMMON_MODULES \
      $PARQUET_NATIVE_STUBS \
      $HACL_NATIVE_STUBS \
      ../../../bin/grddl-runner/grddl_runner.ml \
      -o "$BINDIR/grddl_runner" || GRDDL_RC=$?
    cat _ocamlopt_grddl_runner.log
    if [[ "$GRDDL_RC" -ne 0 ]]; then
      echo "  ERROR: grddl_runner build failed (ocamlopt rc=$GRDDL_RC)" >&2
      echo "  See full log above. Build aborted." >&2
      exit "$GRDDL_RC"
    fi
    if [[ ! -x "$BINDIR/grddl_runner" ]]; then
      echo "  ERROR: grddl_runner ocamlopt returned 0 but $BINDIR/grddl_runner is missing or not executable" >&2
      exit 1
    fi
    echo "  Built: bin/${PLATFORM}/grddl_runner ($(wc -c < "$BINDIR/grddl_runner") bytes)"

    # jsonld_runner — JSON-LD 1.1 toRdf manifest runner (Phase 2 of
    # the JSON-LD program). Reads
    # third_party/testing/json-ld/tests/toRdf-manifest.jsonld via the
    # F*-extracted Parser_JSON, calls Parser_JSONLD.parse_jsonld
    # (expanded-form only), and compares against expected .nq fixtures
    # via RDF_Canonical.canonicalize_to_nquads. See
    # docs/designissues/2026-07-05-jsonld-phase2-runner.md.
    JSONLD_RUNNER_RC=0
    run_with_heartbeat "ocamlopt jsonld_runner" "_ocamlopt_jsonld_runner.log" -- \
      ocamlfind ocamlopt -package fstar.lib,str,zarith,sha,digestif.c,unix,uucp -linkpkg -w -8-14-26 \
      $STATIC_FLAGS \
      $COMMON_MODULES \
      $PARQUET_NATIVE_STUBS \
      $HACL_NATIVE_STUBS \
      ../../../bin/jsonld-runner/jsonld_runner.ml \
      -o "$BINDIR/jsonld_runner" || JSONLD_RUNNER_RC=$?
    cat _ocamlopt_jsonld_runner.log
    if [[ "$JSONLD_RUNNER_RC" -ne 0 ]]; then
      echo "  ERROR: jsonld_runner build failed (ocamlopt rc=$JSONLD_RUNNER_RC)" >&2
      echo "  See full log above. Build aborted." >&2
      exit "$JSONLD_RUNNER_RC"
    fi
    if [[ ! -x "$BINDIR/jsonld_runner" ]]; then
      echo "  ERROR: jsonld_runner ocamlopt returned 0 but $BINDIR/jsonld_runner is missing or not executable" >&2
      exit 1
    fi
    echo "  Built: bin/${PLATFORM}/jsonld_runner ($(wc -c < "$BINDIR/jsonld_runner") bytes)"

    # jsonld_html_runner — JSON-LD 1.1 HTML manifest runner. Reads
    # third_party/testing/json-ld/tests/html-manifest.jsonld, extracts the
    # embedded JSON-LD from each .html input via the F*-extracted
    # Parser_JSONLD_Html.extract_jsonld_from_html, then dispatches Expand /
    # ToRDF tests to the same F* algorithms the other jsonld runners use.
    JSONLD_HTML_RUNNER_RC=0
    run_with_heartbeat "ocamlopt jsonld_html_runner" "_ocamlopt_jsonld_html_runner.log" -- \
      ocamlfind ocamlopt -package fstar.lib,str,zarith,sha,digestif.c,unix,uucp -linkpkg -w -8-14-26 \
      $STATIC_FLAGS \
      $COMMON_MODULES \
      $PARQUET_NATIVE_STUBS \
      $HACL_NATIVE_STUBS \
      ../../../bin/jsonld-html-runner/jsonld_html_runner.ml \
      -o "$BINDIR/jsonld_html_runner" || JSONLD_HTML_RUNNER_RC=$?
    cat _ocamlopt_jsonld_html_runner.log
    if [[ "$JSONLD_HTML_RUNNER_RC" -ne 0 ]]; then
      echo "  ERROR: jsonld_html_runner build failed (ocamlopt rc=$JSONLD_HTML_RUNNER_RC)" >&2
      exit "$JSONLD_HTML_RUNNER_RC"
    fi
    echo "  Built: bin/${PLATFORM}/jsonld_html_runner ($(wc -c < "$BINDIR/jsonld_html_runner") bytes)"

    # jsonld_fromrdf_runner — JSON-LD 1.1 fromRdf ("Serialize RDF as
    # JSON-LD") manifest runner. Reads
    # third_party/testing/json-ld/tests/fromRdf-manifest.jsonld via the
    # F*-extracted Parser_JSON, parses each -in.nq with
    # Parser_NQuads.parse_nquads, calls JSONLD_FromRdf.from_rdf, and
    # compares against the expected -out.jsonld via
    # Parser_JSONLD.jcanon_document (JCS canonical JSON string equality).
    JSONLD_FROMRDF_RUNNER_RC=0
    run_with_heartbeat "ocamlopt jsonld_fromrdf_runner" "_ocamlopt_jsonld_fromrdf_runner.log" -- \
      ocamlfind ocamlopt -package fstar.lib,str,zarith,sha,digestif.c,unix,uucp -linkpkg -w -8-14-26 \
      $STATIC_FLAGS \
      $COMMON_MODULES \
      $PARQUET_NATIVE_STUBS \
      $HACL_NATIVE_STUBS \
      ../../../bin/jsonld-fromrdf-runner/jsonld_fromrdf_runner.ml \
      -o "$BINDIR/jsonld_fromrdf_runner" || JSONLD_FROMRDF_RUNNER_RC=$?
    cat _ocamlopt_jsonld_fromrdf_runner.log
    if [[ "$JSONLD_FROMRDF_RUNNER_RC" -ne 0 ]]; then
      echo "  ERROR: jsonld_fromrdf_runner build failed (ocamlopt rc=$JSONLD_FROMRDF_RUNNER_RC)" >&2
      echo "  See full log above. Build aborted." >&2
      exit "$JSONLD_FROMRDF_RUNNER_RC"
    fi
    if [[ ! -x "$BINDIR/jsonld_fromrdf_runner" ]]; then
      echo "  ERROR: jsonld_fromrdf_runner ocamlopt returned 0 but $BINDIR/jsonld_fromrdf_runner is missing or not executable" >&2
      exit 1
    fi
    echo "  Built: bin/${PLATFORM}/jsonld_fromrdf_runner ($(wc -c < "$BINDIR/jsonld_fromrdf_runner") bytes)"

    # jsonld_expand_runner — JSON-LD 1.1 Expansion Algorithm manifest
    # runner. Reads
    # third_party/testing/json-ld/tests/expand-manifest.jsonld via the
    # F*-extracted Parser_JSON, calls Parser_JSONLD.expand_document (the
    # Expansion Algorithm, stopping before RDF conversion), and compares
    # the expanded JSON against the expected -out.jsonld via
    # Parser_JSONLD.jsonld_expanded_equal (JCS-canonical structural
    # equality). Semantics live in JSONLD.Expand/JSONLD.Context/
    # Parser.JSONLD; this .ml is I/O + compare only (iron rule #7 / #11).
    JSONLD_EXPAND_RUNNER_RC=0
    run_with_heartbeat "ocamlopt jsonld_expand_runner" "_ocamlopt_jsonld_expand_runner.log" -- \
      ocamlfind ocamlopt -package fstar.lib,str,zarith,sha,digestif.c,unix,uucp -linkpkg -w -8-14-26 \
      $STATIC_FLAGS \
      $COMMON_MODULES \
      $PARQUET_NATIVE_STUBS \
      $HACL_NATIVE_STUBS \
      ../../../bin/jsonld-expand-runner/jsonld_expand_runner.ml \
      -o "$BINDIR/jsonld_expand_runner" || JSONLD_EXPAND_RUNNER_RC=$?
    cat _ocamlopt_jsonld_expand_runner.log
    if [[ "$JSONLD_EXPAND_RUNNER_RC" -ne 0 ]]; then
      echo "  ERROR: jsonld_expand_runner build failed (ocamlopt rc=$JSONLD_EXPAND_RUNNER_RC)" >&2
      echo "  See full log above. Build aborted." >&2
      exit "$JSONLD_EXPAND_RUNNER_RC"
    fi
    if [[ ! -x "$BINDIR/jsonld_expand_runner" ]]; then
      echo "  ERROR: jsonld_expand_runner ocamlopt returned 0 but $BINDIR/jsonld_expand_runner is missing or not executable" >&2
      exit 1
    fi
    echo "  Built: bin/${PLATFORM}/jsonld_expand_runner ($(wc -c < "$BINDIR/jsonld_expand_runner") bytes)"

    # jsonld_compact_runner — JSON-LD 1.1 Compaction API manifest runner.
    # Reads third_party/testing/json-ld/tests/compact-manifest.jsonld via
    # the F*-extracted Parser_JSON, calls JSONLD_Compact.compact_document
    # (expand via Parser_JSONLD.expand_document, process the supplied
    # context, run the Compaction Algorithm, re-attach the original
    # context), and compares the compacted JSON against the expected
    # -out.jsonld via Parser_JSONLD.jsonld_expanded_equal (JCS-canonical
    # structural equality). Semantics live in JSONLD.Compact/JSONLD.
    # Context/JSONLD.Expand/Parser.JSONLD; this .ml is I/O + compare only
    # (iron rule #7 / #11).
    JSONLD_COMPACT_RUNNER_RC=0
    run_with_heartbeat "ocamlopt jsonld_compact_runner" "_ocamlopt_jsonld_compact_runner.log" -- \
      ocamlfind ocamlopt -package fstar.lib,str,zarith,sha,digestif.c,unix,uucp -linkpkg -w -8-14-26 \
      $STATIC_FLAGS \
      $COMMON_MODULES \
      $PARQUET_NATIVE_STUBS \
      $HACL_NATIVE_STUBS \
      ../../../bin/jsonld-compact-runner/jsonld_compact_runner.ml \
      -o "$BINDIR/jsonld_compact_runner" || JSONLD_COMPACT_RUNNER_RC=$?
    cat _ocamlopt_jsonld_compact_runner.log
    if [[ "$JSONLD_COMPACT_RUNNER_RC" -ne 0 ]]; then
      echo "  ERROR: jsonld_compact_runner build failed (ocamlopt rc=$JSONLD_COMPACT_RUNNER_RC)" >&2
      echo "  See full log above. Build aborted." >&2
      exit "$JSONLD_COMPACT_RUNNER_RC"
    fi
    if [[ ! -x "$BINDIR/jsonld_compact_runner" ]]; then
      echo "  ERROR: jsonld_compact_runner ocamlopt returned 0 but $BINDIR/jsonld_compact_runner is missing or not executable" >&2
      exit 1
    fi
    echo "  Built: bin/${PLATFORM}/jsonld_compact_runner ($(wc -c < "$BINDIR/jsonld_compact_runner") bytes)"

    # jsonld_flatten_runner — JSON-LD 1.1 Flattening API manifest runner.
    # Reads third_party/testing/json-ld/tests/flatten-manifest.jsonld via
    # the F*-extracted Parser_JSON, calls JSONLD_Flatten.flatten_document
    # (expand via Parser_JSONLD.expand_document, Node Map Generation +
    # the Flattening Algorithm, optional compaction of the flattened
    # array via the JSONLD.Compact machinery), and compares the flattened
    # JSON against the expected -out.jsonld via
    # Parser_JSONLD.jsonld_expanded_equal (JCS-canonical structural
    # equality). Semantics live in JSONLD.Flatten/JSONLD.Compact/JSONLD.
    # Context/JSONLD.Expand/Parser.JSONLD; this .ml is I/O + compare only
    # (iron rule #7 / #11).
    JSONLD_FLATTEN_RUNNER_RC=0
    run_with_heartbeat "ocamlopt jsonld_flatten_runner" "_ocamlopt_jsonld_flatten_runner.log" -- \
      ocamlfind ocamlopt -package fstar.lib,str,zarith,sha,digestif.c,unix,uucp -linkpkg -w -8-14-26 \
      $STATIC_FLAGS \
      $COMMON_MODULES \
      $PARQUET_NATIVE_STUBS \
      $HACL_NATIVE_STUBS \
      ../../../bin/jsonld-flatten-runner/jsonld_flatten_runner.ml \
      -o "$BINDIR/jsonld_flatten_runner" || JSONLD_FLATTEN_RUNNER_RC=$?
    cat _ocamlopt_jsonld_flatten_runner.log
    if [[ "$JSONLD_FLATTEN_RUNNER_RC" -ne 0 ]]; then
      echo "  ERROR: jsonld_flatten_runner build failed (ocamlopt rc=$JSONLD_FLATTEN_RUNNER_RC)" >&2
      echo "  See full log above. Build aborted." >&2
      exit "$JSONLD_FLATTEN_RUNNER_RC"
    fi
    if [[ ! -x "$BINDIR/jsonld_flatten_runner" ]]; then
      echo "  ERROR: jsonld_flatten_runner ocamlopt returned 0 but $BINDIR/jsonld_flatten_runner is missing or not executable" >&2
      exit 1
    fi
    echo "  Built: bin/${PLATFORM}/jsonld_flatten_runner ($(wc -c < "$BINDIR/jsonld_flatten_runner") bytes)"

    # jsonld_frame_runner — JSON-LD 1.1 Framing manifest runner. Reads
    # third_party/testing/json-ld-framing/tests/frame-manifest.jsonld,
    # calls the F*-extracted JSONLD_Frame.frame_document (expand+flatten+
    # match/embed+compact), compares against the -out.jsonld oracle.
    JSONLD_FRAME_RUNNER_RC=0
    run_with_heartbeat "ocamlopt jsonld_frame_runner" "_ocamlopt_jsonld_frame_runner.log" -- \
      ocamlfind ocamlopt -package fstar.lib,str,zarith,sha,digestif.c,unix,uucp -linkpkg -w -8-14-26 \
      $STATIC_FLAGS \
      $COMMON_MODULES \
      $PARQUET_NATIVE_STUBS \
      $HACL_NATIVE_STUBS \
      ../../../bin/jsonld-frame-runner/jsonld_frame_runner.ml \
      -o "$BINDIR/jsonld_frame_runner" || JSONLD_FRAME_RUNNER_RC=$?
    cat _ocamlopt_jsonld_frame_runner.log
    if [[ "$JSONLD_FRAME_RUNNER_RC" -ne 0 ]]; then
      echo "  ERROR: jsonld_frame_runner build failed (ocamlopt rc=$JSONLD_FRAME_RUNNER_RC)" >&2
      exit "$JSONLD_FRAME_RUNNER_RC"
    fi
    echo "  Built: bin/${PLATFORM}/jsonld_frame_runner ($(wc -c < "$BINDIR/jsonld_frame_runner") bytes)"

    # mathml_runner — Content MathML evaluation corpus runner. Reads
    # third_party/testing/mathml/manifest.json via the F*-extracted
    # Parser_JSON, parses each input with Parser_XML.parse_xml_document,
    # calls MathML_Content.eval_doc_env, and compares
    # MathML_Content.value_to_string against expectedValue. All math /
    # number parsing / canonicalisation lives in MathML.Content.fst
    # (extracted to MathML_Content, in COMMON_MODULES above); this .ml is
    # I/O + compare only (iron rule #7 / #11).
    MATHML_RUNNER_RC=0
    run_with_heartbeat "ocamlopt mathml_runner" "_ocamlopt_mathml_runner.log" -- \
      ocamlfind ocamlopt -package fstar.lib,str,zarith,sha,digestif.c,unix,uucp -linkpkg -w -8-14-26 \
      $STATIC_FLAGS \
      $COMMON_MODULES \
      $PARQUET_NATIVE_STUBS \
      $HACL_NATIVE_STUBS \
      ../../../bin/mathml-runner/mathml_runner.ml \
      -o "$BINDIR/mathml_runner" || MATHML_RUNNER_RC=$?
    cat _ocamlopt_mathml_runner.log
    if [[ "$MATHML_RUNNER_RC" -ne 0 ]]; then
      echo "  ERROR: mathml_runner build failed (ocamlopt rc=$MATHML_RUNNER_RC)" >&2
      echo "  See full log above. Build aborted." >&2
      exit "$MATHML_RUNNER_RC"
    fi
    if [[ ! -x "$BINDIR/mathml_runner" ]]; then
      echo "  ERROR: mathml_runner ocamlopt returned 0 but $BINDIR/mathml_runner is missing or not executable" >&2
      exit 1
    fi
    echo "  Built: bin/${PLATFORM}/mathml_runner ($(wc -c < "$BINDIR/mathml_runner") bytes)"

    # jsonschema_runner — JSON Schema draft-07 conformance runner. Reads the
    # vendored subset of the official JSON Schema Test Suite under
    # third_party/testing/jsonschema/tests/draft7/*.json via the F*-extracted
    # Parser_JSON, calls JSONSchema_Validate.validate on each {schema, data},
    # and compares its three-valued result to the expected `valid`. All
    # validation semantics live in formal/fstar/JSONSchema.Validate.fst; this
    # .ml is I/O + compare only (iron rule #7 / #11).
    JSONSCHEMA_RUNNER_RC=0
    run_with_heartbeat "ocamlopt jsonschema_runner" "_ocamlopt_jsonschema_runner.log" -- \
      ocamlfind ocamlopt -package fstar.lib,str,zarith,sha,digestif.c,unix,uucp -linkpkg -w -8-14-26 \
      $STATIC_FLAGS \
      $COMMON_MODULES \
      $PARQUET_NATIVE_STUBS \
      $HACL_NATIVE_STUBS \
      ../../../bin/jsonschema-runner/jsonschema_runner.ml \
      -o "$BINDIR/jsonschema_runner" || JSONSCHEMA_RUNNER_RC=$?
    cat _ocamlopt_jsonschema_runner.log
    if [[ "$JSONSCHEMA_RUNNER_RC" -ne 0 ]]; then
      echo "  ERROR: jsonschema_runner build failed (ocamlopt rc=$JSONSCHEMA_RUNNER_RC)" >&2
      echo "  See full log above. Build aborted." >&2
      exit "$JSONSCHEMA_RUNNER_RC"
    fi
    if [[ ! -x "$BINDIR/jsonschema_runner" ]]; then
      echo "  ERROR: jsonschema_runner ocamlopt returned 0 but $BINDIR/jsonschema_runner is missing or not executable" >&2
      exit 1
    fi
    echo "  Built: bin/${PLATFORM}/jsonschema_runner ($(wc -c < "$BINDIR/jsonschema_runner") bytes)"

    # schematron_runner — ISO/IEC 19757-3 (Schematron) validator runner,
    # XSLT-1 / XPath-1 query binding. Reads the spec-cited corpus under
    # third_party/testing/schematron/ (see that dir's README.md for
    # provenance: the reference repo ships no expected-report triples, so
    # the corpus is authored from ISO/IEC 19757-3 + the schematron.com
    # tutorial and cited per case). Parses each schema + instance via the
    # F*-extracted Parser_XML.parse_xml_document, runs
    # Schematron_Validate.validate (formal/fstar/Schematron.Validate.fst),
    # and compares the produced findings (assert-fail / report-hit /
    # indeterminate) to the manifest's expected multiset. Manifest parsed
    # via the F*-extracted Parser_JSON. I/O + compare only (iron rule #11).
    SCHEMATRON_RUNNER_RC=0
    run_with_heartbeat "ocamlopt schematron_runner" "_ocamlopt_schematron_runner.log" -- \
      ocamlfind ocamlopt -package fstar.lib,str,zarith,sha,digestif.c,unix,uucp -linkpkg -w -8-14-26 \
      $STATIC_FLAGS \
      $COMMON_MODULES \
      $PARQUET_NATIVE_STUBS \
      $HACL_NATIVE_STUBS \
      ../../../bin/schematron-runner/schematron_runner.ml \
      -o "$BINDIR/schematron_runner" || SCHEMATRON_RUNNER_RC=$?
    cat _ocamlopt_schematron_runner.log
    if [[ "$SCHEMATRON_RUNNER_RC" -ne 0 ]]; then
      echo "  ERROR: schematron_runner build failed (ocamlopt rc=$SCHEMATRON_RUNNER_RC)" >&2
      echo "  See full log above. Build aborted." >&2
      exit "$SCHEMATRON_RUNNER_RC"
    fi
    if [[ ! -x "$BINDIR/schematron_runner" ]]; then
      echo "  ERROR: schematron_runner ocamlopt returned 0 but $BINDIR/schematron_runner is missing or not executable" >&2
      exit 1
    fi
    echo "  Built: bin/${PLATFORM}/schematron_runner ($(wc -c < "$BINDIR/schematron_runner") bytes)"

    # xslt_runner — XSLT 1.0 transform conformance runner (first wave of
    # the XSLT -> MathML -> XForms program). Reads the curated,
    # W3C-sourced XSLT-1.0-expressible subset vendored under
    # third_party/testing/xslt/ (selected from w3c/xslt30-test; see that
    # dir's README.md for provenance), parses each stylesheet + source
    # via the F*-extracted Parser_XML.parse_xml_document, runs
    # XSLT_Transform.transform (formal/fstar/XSLT.Transform.fst), and
    # compares the serialized result to the expected assert-xml file
    # (exact or whitespace-collapsed). Manifest parsed via the
    # F*-extracted Parser_JSON. I/O + compare only (iron rule #11).
    XSLT_RUNNER_RC=0
    run_with_heartbeat "ocamlopt xslt_runner" "_ocamlopt_xslt_runner.log" -- \
      ocamlfind ocamlopt -package fstar.lib,str,zarith,sha,digestif.c,unix,uucp -linkpkg -w -8-14-26 \
      $STATIC_FLAGS \
      $COMMON_MODULES \
      $PARQUET_NATIVE_STUBS \
      $HACL_NATIVE_STUBS \
      ../../../bin/xslt-runner/xslt_runner.ml \
      -o "$BINDIR/xslt_runner" || XSLT_RUNNER_RC=$?
    cat _ocamlopt_xslt_runner.log
    if [[ "$XSLT_RUNNER_RC" -ne 0 ]]; then
      echo "  ERROR: xslt_runner build failed (ocamlopt rc=$XSLT_RUNNER_RC)" >&2
      echo "  See full log above. Build aborted." >&2
      exit "$XSLT_RUNNER_RC"
    fi
    if [[ ! -x "$BINDIR/xslt_runner" ]]; then
      echo "  ERROR: xslt_runner ocamlopt returned 0 but $BINDIR/xslt_runner is missing or not executable" >&2
      exit 1
    fi
    echo "  Built: bin/${PLATFORM}/xslt_runner ($(wc -c < "$BINDIR/xslt_runner") bytes)"

    # vc_runner — Verifiable Credentials Data Model 2.0 structural
    # fixture runner, Stage 1 of the VC program
    # (docs/designissues/2026-07-05-vc-program-plan.md). Walks the
    # vendored w3c/vc-data-model-2.0-test-suite's tests/input/*.json
    # fixtures (120 files, -ok/-fail filename-suffixed; no manifest —
    # the upstream mocha suite assumes a live HTTP issue/verify
    # endpoint this offline runner does not have), calls the
    # F*-extracted VC_Credential.vc_check_from_string (required-
    # property + type-membership checks over Parser_JSON, the @context
    # sentinel check, plus VC_Context JSON-LD type-value resolution —
    # protected-term redefinition, non-URL-mapped and @vocab-nullified
    # unmapped type terms — see VC.Credential.fst's + VC.Context.fst's
    # headers for the exact rule set), and scores the result against
    # each filename's own -ok/-fail suffix. The runner parses the
    # vendored third_party/contexts/credentials-v2.jsonld once (I/O glue,
    # rule #11) and passes it into the pure F* checker as v2ctx.
    VC_RUNNER_RC=0
    run_with_heartbeat "ocamlopt vc_runner" "_ocamlopt_vc_runner.log" -- \
      ocamlfind ocamlopt -package fstar.lib,str,zarith,sha,digestif.c,unix,uucp -linkpkg -w -8-14-26 \
      $STATIC_FLAGS \
      $COMMON_MODULES \
      $PARQUET_NATIVE_STUBS \
      $HACL_NATIVE_STUBS \
      ../../../bin/vc-runner/vc_runner.ml \
      -o "$BINDIR/vc_runner" || VC_RUNNER_RC=$?
    cat _ocamlopt_vc_runner.log
    if [[ "$VC_RUNNER_RC" -ne 0 ]]; then
      echo "  ERROR: vc_runner build failed (ocamlopt rc=$VC_RUNNER_RC)" >&2
      echo "  See full log above. Build aborted." >&2
      exit "$VC_RUNNER_RC"
    fi
    if [[ ! -x "$BINDIR/vc_runner" ]]; then
      echo "  ERROR: vc_runner ocamlopt returned 0 but $BINDIR/vc_runner is missing or not executable" >&2
      exit 1
    fi
    echo "  Built: bin/${PLATFORM}/vc_runner ($(wc -c < "$BINDIR/vc_runner") bytes)"

    # did_runner — did:key DID method resolution vector runner
    # (Factoidal's first Decentralized Identifiers capability). Walks
    # tests/did/*.did / *.nt vector pairs, calls the F*-extracted
    # DID_Key.did_key_document (formal/fstar/DID.Key.fst) on each did:key
    # string, serializes the resulting triples via
    # RDF_NQuads_Serialize.nq_line_for_triple_default_graph, and compares
    # the sorted line set against the vector's hand-transcribed expected
    # DID Document. Also self-checks DID_Key.parse_did_key's rejection
    # paths. See tests/did/README.md for vector provenance.
    DID_RUNNER_RC=0
    run_with_heartbeat "ocamlopt did_runner" "_ocamlopt_did_runner.log" -- \
      ocamlfind ocamlopt -package fstar.lib,str,zarith,sha,digestif.c,unix,uucp -linkpkg -w -8-14-26 \
      $STATIC_FLAGS \
      $COMMON_MODULES \
      $PARQUET_NATIVE_STUBS \
      $HACL_NATIVE_STUBS \
      ../../../bin/did-runner/did_runner.ml \
      -o "$BINDIR/did_runner" || DID_RUNNER_RC=$?
    cat _ocamlopt_did_runner.log
    if [[ "$DID_RUNNER_RC" -ne 0 ]]; then
      echo "  ERROR: did_runner build failed (ocamlopt rc=$DID_RUNNER_RC)" >&2
      echo "  See full log above. Build aborted." >&2
      exit "$DID_RUNNER_RC"
    fi
    if [[ ! -x "$BINDIR/did_runner" ]]; then
      echo "  ERROR: did_runner ocamlopt returned 0 but $BINDIR/did_runner is missing or not executable" >&2
      exit 1
    fi
    echo "  Built: bin/${PLATFORM}/did_runner ($(wc -c < "$BINDIR/did_runner") bytes)"

    # shacl_runner — SHACL Core W3C data-shapes-test-suite runner
    # (slice 1, issue #181). Walks
    # third_party/testing/shacl/data-shapes-test-suite/tests/core/manifest.ttl
    # via the F*-extracted Parser_Turtle, calls
    # SHACL_Validation.parse_shape_from_graph + SHACL_Validation.validate,
    # and compares only the report's sh:conforms flag against each
    # manifest entry's expected mf:result (full report-detail
    # isomorphism is Phase 2 follow-up). See
    # formal/fstar/SHACL.Validation.fst section 11 for constraint
    # coverage and what is deferred.
    SHACL_RUNNER_RC=0
    run_with_heartbeat "ocamlopt shacl_runner" "_ocamlopt_shacl_runner.log" -- \
      ocamlfind ocamlopt -package fstar.lib,str,zarith,sha,digestif.c,unix,uucp -linkpkg -w -8-14-26 \
      $STATIC_FLAGS \
      $COMMON_MODULES \
      $PARQUET_NATIVE_STUBS \
      $HACL_NATIVE_STUBS \
      ../../../bin/shacl-runner/shacl_runner.ml \
      -o "$BINDIR/shacl_runner" || SHACL_RUNNER_RC=$?
    cat _ocamlopt_shacl_runner.log
    if [[ "$SHACL_RUNNER_RC" -ne 0 ]]; then
      echo "  ERROR: shacl_runner build failed (ocamlopt rc=$SHACL_RUNNER_RC)" >&2
      echo "  See full log above. Build aborted." >&2
      exit "$SHACL_RUNNER_RC"
    fi
    if [[ ! -x "$BINDIR/shacl_runner" ]]; then
      echo "  ERROR: shacl_runner ocamlopt returned 0 but $BINDIR/shacl_runner is missing or not executable" >&2
      exit 1
    fi
    echo "  Built: bin/${PLATFORM}/shacl_runner ($(wc -c < "$BINDIR/shacl_runner") bytes)"

    # qudt_runner — QUDT v3.4.0 SHACL suite runner (Layer A of
    # docs/designissues/2026-07-10-qudt-scoping.md). Runs QUDT's own
    # shipped SHACL rulesets (third_party/qudt/) through the
    # F*-extracted SHACL_Validation entry points: the contributor
    # integrity ruleset against the vendored all-in-one distribution
    # (one scored entry per ruleset shape, wall-clock budgeted) and
    # the user-facing deprecation/consistency ruleset against the
    # authored fixtures in tests/qudt/fixtures/. I/O + slicing +
    # score-printing glue only (iron rule #11) — see the .ml header.
    QUDT_RUNNER_RC=0
    run_with_heartbeat "ocamlopt qudt_runner" "_ocamlopt_qudt_runner.log" -- \
      ocamlfind ocamlopt -package fstar.lib,str,zarith,sha,digestif.c,unix,uucp -linkpkg -w -8-14-26 \
      $STATIC_FLAGS \
      $COMMON_MODULES \
      $PARQUET_NATIVE_STUBS \
      $HACL_NATIVE_STUBS \
      ../../../bin/qudt-runner/qudt_runner.ml \
      -o "$BINDIR/qudt_runner" || QUDT_RUNNER_RC=$?
    cat _ocamlopt_qudt_runner.log
    if [[ "$QUDT_RUNNER_RC" -ne 0 ]]; then
      echo "  ERROR: qudt_runner build failed (ocamlopt rc=$QUDT_RUNNER_RC)" >&2
      echo "  See full log above. Build aborted." >&2
      exit "$QUDT_RUNNER_RC"
    fi
    if [[ ! -x "$BINDIR/qudt_runner" ]]; then
      echo "  ERROR: qudt_runner ocamlopt returned 0 but $BINDIR/qudt_runner is missing or not executable" >&2
      exit 1
    fi
    echo "  Built: bin/${PLATFORM}/qudt_runner ($(wc -c < "$BINDIR/qudt_runner") bytes)"

    # rml_runner — RML (RDF Mapping Language) rml-core/rml-io test-suite
    # runner, Stage 8 of the RML program
    # (docs/designissues/2026-07-05-rml-program-plan.md). Walks each
    # module's metadata.csv (via the F*-extracted RML_Sources.
    # csv_parse_rows), loads mapping.ttl via the F*-extracted
    # Parser_Turtle, decodes it with RML_Mapping.decode_mapping_document,
    # resolves logical-source rows (JSON/CSV) and evaluates non-join +
    # join (RefObjectMap/joinCondition) triples via RML_Eval, comparing
    # against each fixture's expected output.nq via
    # RDF_Canonical.canonicalize_to_nquads. See
    # bin/rml-runner/rml_runner.ml's header comment for the error=true
    # / N-Quads-sanitizing details.
    RML_RUNNER_RC=0
    run_with_heartbeat "ocamlopt rml_runner" "_ocamlopt_rml_runner.log" -- \
      ocamlfind ocamlopt -package fstar.lib,str,zarith,sha,digestif.c,unix,uucp -linkpkg -w -8-14-26 \
      $STATIC_FLAGS \
      $COMMON_MODULES \
      $PARQUET_NATIVE_STUBS \
      $HACL_NATIVE_STUBS \
      ../../../bin/rml-runner/rml_runner.ml \
      -o "$BINDIR/rml_runner" || RML_RUNNER_RC=$?
    cat _ocamlopt_rml_runner.log
    if [[ "$RML_RUNNER_RC" -ne 0 ]]; then
      echo "  ERROR: rml_runner build failed (ocamlopt rc=$RML_RUNNER_RC)" >&2
      echo "  See full log above. Build aborted." >&2
      exit "$RML_RUNNER_RC"
    fi
    if [[ ! -x "$BINDIR/rml_runner" ]]; then
      echo "  ERROR: rml_runner ocamlopt returned 0 but $BINDIR/rml_runner is missing or not executable" >&2
      exit 1
    fi
    echo "  Built: bin/${PLATFORM}/rml_runner ($(wc -c < "$BINDIR/rml_runner") bytes)"

    # csvw_runner — CSVW (CSV on the Web) csv2rdf manifest runner, Stage
    # 10 of the CSVW program (docs/designissues/2026-07-05-csvw-program-
    # plan.md). Walks third_party/testing/csvw/tests/manifest-rdf.ttl via
    # the F*-extracted Parser_Turtle, loads each test's metadata document
    # via CSVW_Metadata.csvw_decode_metadata_text, reads the referenced
    # CSV via RML_Sources.csv_parse_rows, runs CSVW_Conversion.
    # csvw_convert_document_{standard,minimal}, and compares against each
    # fixture's expected .ttl via RDF_Canonical.canonicalize_to_nquads.
    # See bin/csvw-runner/csvw_runner.ml's header for the I/O-glue-only
    # boundary (rule #11 / anti-pattern #15).
    CSVW_RUNNER_RC=0
    run_with_heartbeat "ocamlopt csvw_runner" "_ocamlopt_csvw_runner.log" -- \
      ocamlfind ocamlopt -package fstar.lib,str,zarith,sha,digestif.c,unix,uucp -linkpkg -w -8-14-26 \
      $STATIC_FLAGS \
      $COMMON_MODULES \
      $PARQUET_NATIVE_STUBS \
      $HACL_NATIVE_STUBS \
      ../../../bin/csvw-runner/csvw_runner.ml \
      -o "$BINDIR/csvw_runner" || CSVW_RUNNER_RC=$?
    cat _ocamlopt_csvw_runner.log
    if [[ "$CSVW_RUNNER_RC" -ne 0 ]]; then
      echo "  ERROR: csvw_runner build failed (ocamlopt rc=$CSVW_RUNNER_RC)" >&2
      echo "  See full log above. Build aborted." >&2
      exit "$CSVW_RUNNER_RC"
    fi
    if [[ ! -x "$BINDIR/csvw_runner" ]]; then
      echo "  ERROR: csvw_runner ocamlopt returned 0 but $BINDIR/csvw_runner is missing or not executable" >&2
      exit 1
    fi
    echo "  Built: bin/${PLATFORM}/csvw_runner ($(wc -c < "$BINDIR/csvw_runner") bytes)"

    # shex_runner — ShEx (Shape Expressions) validation manifest runner,
    # stage 8 of the ShEx program
    # (docs/designissues/2026-07-05-shex-program-plan.md). Walks
    # third_party/testing/shex/validation/manifest.ttl via the
    # F*-extracted Parser_Turtle, loads each test's ShExJ schema twin
    # (schemas/<name>.json in place of the manifest's canonical
    # ShExC .shex reference — see the plan's "ShExC vs ShExJ" scope
    # cut) via ShEx_Schema.decode_shex_schema, and calls
    # ShEx_Validation.validate_focus. See bin/shex-runner/shex_runner.ml's
    # header comment for the PASS/MISMATCH/DEFERRED/SKIP classification.
    SHEX_RUNNER_RC=0
    run_with_heartbeat "ocamlopt shex_runner" "_ocamlopt_shex_runner.log" -- \
      ocamlfind ocamlopt -package fstar.lib,str,zarith,sha,digestif.c,unix,uucp -linkpkg -w -8-14-26 \
      $STATIC_FLAGS \
      $COMMON_MODULES \
      $PARQUET_NATIVE_STUBS \
      $HACL_NATIVE_STUBS \
      ../../../bin/shex-runner/shex_runner.ml \
      -o "$BINDIR/shex_runner" || SHEX_RUNNER_RC=$?
    cat _ocamlopt_shex_runner.log
    if [[ "$SHEX_RUNNER_RC" -ne 0 ]]; then
      echo "  ERROR: shex_runner build failed (ocamlopt rc=$SHEX_RUNNER_RC)" >&2
      echo "  See full log above. Build aborted." >&2
      exit "$SHEX_RUNNER_RC"
    fi
    if [[ ! -x "$BINDIR/shex_runner" ]]; then
      echo "  ERROR: shex_runner ocamlopt returned 0 but $BINDIR/shex_runner is missing or not executable" >&2
      exit 1
    fi
    echo "  Built: bin/${PLATFORM}/shex_runner ($(wc -c < "$BINDIR/shex_runner") bytes)"

    # rif_runner — W3C RIF Core runner: the 4 vendored SPARQL-manifest
    # cases (third_party/testing/rif/tc/) plus the official Core_v1.22
    # corpus walker (third_party/testing/rif-core-suite/). Previously
    # had no stanza here, so chain rebuilds silently reverted manual
    # installs (caught 2026-07-05 when a concurrent agent's artifact
    # revert restored a pre-fix binary). See bin/rif-runner/README.md.
    RIF_RUNNER_RC=0
    run_with_heartbeat "ocamlopt rif_runner" "_ocamlopt_rif_runner.log" -- \
      ocamlfind ocamlopt -package fstar.lib,str,zarith,sha,digestif.c,unix,uucp -linkpkg -w -8-14-26 \
      $STATIC_FLAGS \
      $COMMON_MODULES \
      $PARQUET_NATIVE_STUBS \
      $HACL_NATIVE_STUBS \
      ../../../bin/rif-runner/rif_runner.ml \
      -o "$BINDIR/rif_runner" || RIF_RUNNER_RC=$?
    cat _ocamlopt_rif_runner.log
    if [[ "$RIF_RUNNER_RC" -ne 0 ]]; then
      echo "  ERROR: rif_runner build failed (ocamlopt rc=$RIF_RUNNER_RC)" >&2
      exit "$RIF_RUNNER_RC"
    fi
    echo "  Built: bin/${PLATFORM}/rif_runner ($(wc -c < "$BINDIR/rif_runner") bytes)"

    # xml_runner — W3C/OASIS XML conformance (xmlconf) runner for
    # Parser.XML.fst + XML.Wellformedness.fst + XML.Namespaces.fst.
    # Wired in 2026-07-30 for issue #330: this binary is committed under
    # iron rule #9 but was produced ONLY by the hand-run mktemp-scratch
    # recipe in bin/xml-runner/README.md, so nothing in the main build
    # refreshed it and BUILD_STATUS=OK said nothing about whether it
    # matched its source. Same shape as anti-pattern #27 / hazard #3, and
    # the exact trap that let factoidal-dump-nq ship a pre-#325 parser.
    # Its three modules are already in COMMON_MODULES, so no special
    # module list is needed — the scratch recipe existed only to avoid
    # poisoning ocaml-output/'s .cmi/.cmx from a SECONDARY script
    # (hazard #8), which does not apply here: this IS the main compile.
    XML_RUNNER_RC=0
    run_with_heartbeat "ocamlopt xml_runner" "_ocamlopt_xml_runner.log" -- \
      ocamlfind ocamlopt -package fstar.lib,str,zarith,sha,digestif.c,unix,uucp -linkpkg -w -8-14-26 \
      $STATIC_FLAGS \
      $COMMON_MODULES \
      $PARQUET_NATIVE_STUBS \
      $HACL_NATIVE_STUBS \
      ../../../bin/xml-runner/xml_runner.ml \
      -o "$BINDIR/xml_runner" || XML_RUNNER_RC=$?
    cat _ocamlopt_xml_runner.log
    if [[ "$XML_RUNNER_RC" -ne 0 ]]; then
      echo "  ERROR: xml_runner build failed (ocamlopt rc=$XML_RUNNER_RC)" >&2
      echo "  See full log above. Build aborted." >&2
      exit "$XML_RUNNER_RC"
    fi
    if [[ ! -x "$BINDIR/xml_runner" ]]; then
      echo "  ERROR: xml_runner ocamlopt returned 0 but $BINDIR/xml_runner is missing or not executable" >&2
      exit 1
    fi
    echo "  Built: bin/${PLATFORM}/xml_runner ($(wc -c < "$BINDIR/xml_runner") bytes)"

    # factoidal_http_client — minimal HTTP/1.1 client I/O glue around
    # the F*-extracted SPARQL.HTTP.Client module. Has a module-init
    # smoke-test hook gated on FACTOIDAL_HTTP_CLIENT_SMOKE=1 in the
    # env. Source lives in bin/factoidal-http-client/ per #200 PR5
    # (relocated 2026-05-08).
    FACTOIDAL_HTTP_CLIENT_RC=0
    run_with_heartbeat "ocamlopt factoidal_http_client" "_ocamlopt_factoidal_http_client.log" -- \
      ocamlfind ocamlopt -package fstar.lib,str,zarith,sha,digestif.c,unix,uucp -linkpkg -w -8-14-26 \
      $STATIC_FLAGS \
      $COMMON_MODULES \
      $PARQUET_NATIVE_STUBS \
      $HACL_NATIVE_STUBS \
      ../../../bin/factoidal-http-client/factoidal_http_client.ml \
      -o "$BINDIR/factoidal_http_client" || FACTOIDAL_HTTP_CLIENT_RC=$?
    cat _ocamlopt_factoidal_http_client.log 2>/dev/null || true
    if [[ "$FACTOIDAL_HTTP_CLIENT_RC" -ne 0 ]]; then
      echo "  WARNING: factoidal_http_client build failed (ocamlopt rc=$FACTOIDAL_HTTP_CLIENT_RC)" >&2
    else
      echo "  Built: bin/${PLATFORM}/factoidal_http_client ($(wc -c < "$BINDIR/factoidal_http_client") bytes)"
    fi

    # parquet_probe — diagnostic CLI for poking at parquet metadata
    # headers (magic, row groups, columns, page offsets). Built
    # against the F*-extracted Parquet.Footer module. Source lives
    # in bin/parquet-probe/ per #200 D Phase 8 (relocated 2026-05-08).
    PARQUET_PROBE_RC=0
    run_with_heartbeat "ocamlopt parquet_probe" "_ocamlopt_parquet_probe.log" -- \
      ocamlfind ocamlopt -package fstar.lib,str,zarith,sha,digestif.c,unix,uucp -linkpkg -w -8-14-26 \
      $STATIC_FLAGS \
      $COMMON_MODULES \
      $PARQUET_NATIVE_STUBS \
      $HACL_NATIVE_STUBS \
      ../../../bin/parquet-probe/parquet_probe.ml \
      -o "$BINDIR/parquet_probe" || PARQUET_PROBE_RC=$?
    cat _ocamlopt_parquet_probe.log 2>/dev/null || true
    if [[ "$PARQUET_PROBE_RC" -ne 0 ]]; then
      echo "  WARNING: parquet_probe build failed (ocamlopt rc=$PARQUET_PROBE_RC)" >&2
      echo "  This is a diagnostic CLI; main binaries are unaffected." >&2
    else
      echo "  Built: bin/${PLATFORM}/parquet_probe ($(wc -c < "$BINDIR/parquet_probe") bytes)"
    fi

    # cottas_ondisk_smoketest — issue #100 Phase 2 acceptance harness.
    # Opens a COTTAS file via the F*-extracted on-disk store, reports
    # startup/post-open/post-query RSS in MB, runs cottas_ondisk_estimate
    # with all-None bounds. Acceptance #4: server RSS no longer scales
    # with corpus size.
    #
    # Phase 8 relocation (#200 D, 2026-05-08): source moved out of
    # formal/fstar/ocaml-output/ into bin/cottas-ondisk-smoketest/ per
    # iron rule #11 (consumer code is not part of the verified library).
    COTTAS_SMOKE_RC=0
    run_with_heartbeat "ocamlopt cottas_ondisk_smoketest" "_ocamlopt_cottas_ondisk_smoketest.log" -- \
      ocamlfind ocamlopt -package fstar.lib,str,zarith,sha,digestif.c,unix,uucp -linkpkg -w -8-14-26 \
      $STATIC_FLAGS \
      $COMMON_MODULES \
      $PARQUET_NATIVE_STUBS \
      $HACL_NATIVE_STUBS \
      ../../../bin/cottas-ondisk-smoketest/cottas_ondisk_smoketest.ml \
      -o "$BINDIR/cottas_ondisk_smoketest" || COTTAS_SMOKE_RC=$?
    cat _ocamlopt_cottas_ondisk_smoketest.log 2>/dev/null || true
    if [[ "$COTTAS_SMOKE_RC" -ne 0 ]]; then
      echo "  WARNING: cottas_ondisk_smoketest build failed (ocamlopt rc=$COTTAS_SMOKE_RC)" >&2
      echo "  This is a non-blocking smoketest harness; main binaries are unaffected." >&2
    else
      echo "  Built: bin/${PLATFORM}/cottas_ondisk_smoketest ($(wc -c < "$BINDIR/cottas_ondisk_smoketest") bytes)"
    fi

    # depcheck — #448 Part 2 consumer for the verified Dep.Reachability
    # core. Reads an edge file + roots file, calls the EXTRACTED
    # Dep_Reachability.reachable, then re-checks is_closed/all_mem on
    # the actual output and refuses (exit 2) if either fails — see
    # bin/depcheck/depcheck.ml. tools/module-liveness.py v3 shells out
    # to this instead of trusting an unverified Python BFS.
    DEPCHECK_RC=0
    run_with_heartbeat "ocamlopt depcheck" "_ocamlopt_depcheck.log" -- \
      ocamlfind ocamlopt -package fstar.lib,str,zarith,sha,digestif.c,unix,uucp -linkpkg -w -8-14-26 \
      $STATIC_FLAGS \
      $COMMON_MODULES \
      $PARQUET_NATIVE_STUBS \
      $HACL_NATIVE_STUBS \
      ../../../bin/depcheck/depcheck.ml \
      -o "$BINDIR/depcheck" || DEPCHECK_RC=$?
    cat _ocamlopt_depcheck.log 2>/dev/null || true
    if [[ "$DEPCHECK_RC" -ne 0 ]]; then
      echo "  ERROR: depcheck build failed (ocamlopt rc=$DEPCHECK_RC)" >&2
      echo "  See full log above. Build aborted." >&2
      exit "$DEPCHECK_RC"
    fi
    if [[ ! -x "$BINDIR/depcheck" ]]; then
      echo "  ERROR: depcheck ocamlopt returned 0 but $BINDIR/depcheck is missing or not executable" >&2
      exit 1
    fi
    echo "  Built: bin/${PLATFORM}/depcheck ($(wc -c < "$BINDIR/depcheck") bytes)"
  fi

  # Symlink current platform binaries for convenience (relative from ocaml-output/)
  ln -sf "../../../bin/${PLATFORM}/w3c_runner" w3c_runner
  ln -sf "../../../bin/${PLATFORM}/factoidal" factoidal
  ln -sf "../../../bin/${PLATFORM}/factoidal-http" factoidal-http
  ln -sf "../../../bin/${PLATFORM}/owl_runner" owl_runner
  ln -sf "../../../bin/${PLATFORM}/rdfc10_runner" rdfc10_runner
  ln -sf "../../../bin/${PLATFORM}/grddl_runner" grddl_runner
  ln -sf "../../../bin/${PLATFORM}/xml_runner" xml_runner
  if [[ -x "$BINDIR/parquet_probe" ]]; then
    ln -sf "../../../bin/${PLATFORM}/parquet_probe" parquet_probe
  fi
  if [[ -x "$BINDIR/cottas_ondisk_smoketest" ]]; then
    ln -sf "../../../bin/${PLATFORM}/cottas_ondisk_smoketest" cottas_ondisk_smoketest
  fi
  if [[ -x "$BINDIR/depcheck" ]]; then
    ln -sf "../../../bin/${PLATFORM}/depcheck" depcheck
  fi

  cd ..
  record_phase_timing "compile" "$PHASE_START_COMPILE" "$EXTRACT_COUNT"
  echo ""
fi

# Step 3: Run native tests
if [[ "$STEP" == "all" || "$STEP" == "test" ]]; then
  echo "--- Step 3: Run native OCaml tests ---"
  PHASE_START_TEST=$(date +%s)
  # Run the suite from the REPO ROOT, not formal/fstar: the runner's
  # RIF entailment dispatch resolves third_party/testing/rif/tc/ paths
  # relative to its CWD (bin/w3c-runner/w3c_runner.ml,
  # rif_rules_path_for), so running from here false-fails the four
  # SPARQL RIF-regime tests on every full build (627 pass, 4 fail
  # instead of 631 pass, 0 fail — cost a regression investigation on
  # 2026-08-06). generate-report.sh already does this for the same
  # reason.
  W3C_RC=0
  _RUNNER_ABS="$(pwd)/$OUTDIR/w3c_runner"
  _W3C_LOG_ABS="$(pwd)/$OUTDIR/w3c_results.log"
  ( cd ../.. && "$_RUNNER_ABS" --all ) 2>&1 | tee "$_W3C_LOG_ABS" || W3C_RC=$?
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
  record_phase_timing "test" "$PHASE_START_TEST" "$EXTRACT_COUNT"
  echo ""
fi

# Step 4: Build JavaScript via js_of_ocaml
if [[ "$STEP" == "all" || "$STEP" == "js" ]]; then
  echo "--- Step 4: OCaml → JavaScript (js_of_ocaml) ---"
  PHASE_START_JS=$(date +%s)
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
    Dep_Reachability.ml
    Regex_Syntax.ml Regex_Derivative.ml Regex_Exec.ml Regex_XSDPattern.ml
    RDF_Format.ml RDF_Vocabulary.ml
    RDF_Term.ml RDF_Triple.ml
    RDF_Indexed.ml RDF_Graph.ml
    RDF_Vocabulary_Axioms.ml RDFS_Closure.ml RDFS_Closure_SemiNaive.ml RDFS_SchemaSplit.ml OWL_Closure.ml
    RDF_Graph_Executable.ml RDF_List_Helpers.ml Parser_FastString_Spec.ml RDF_Bytes.ml RDF_Store_Loader.ml Parquet_Footer.ml OWL_Vocabulary.ml OWL_DirectMapping_Filter.ml XSD_Facets.ml Tableau.ml Tableau_Refute.ml Tableau_CountingOracle.ml
    Parser_FastString_CharBoundary.ml Parser_FastString.ml Parser_FastString_ConcatSpec.ml RDF_IRI.ml SPARQL11_IRI_Resolve.ml Parser_IRI.ml
    Parser_Combinators.ml Parser_TurtleScanner.ml Parser_NTriples.ml
    RDF_NQuads_Serialize.ml RDF_Entailment_Simple.ml
    Parser_Turtle.ml HDT_Container.ml HDT_Dictionary.ml HDT_Triples.ml
    RDF_Geo_Types.ml RDF_Geo_BBox.ml Parser_WKT.ml RDF_Geo_Topology.ml RDF_Geo_Functions.ml
    Parser_OWLFunctional.ml
    RDF_Turtle_Serialize.ml
    Parser_NQuads.ml Parser_TriG.ml Parser_XML.ml XML_Wellformedness.ml XML_Namespaces.ml Parser_XPath.ml XPath_Eval.ml XSLT_Transform.ml Schematron_Validate.ml Parser_RDFXML.ml Math_Expr.ml Math_Subst.ml Math_Diff.ml Math_Simplify.ml Math_Matrix.ml MathML_Content.ml Math_Series.ml MathML_Present.ml Math_Sigmoid.ml
    Parser_SRX.ml Parser_CSVResults.ml
    SPARQL_JSON_Escape.ml
    Parser_JSON.ml Parser_JSONResults.ml JSONLD_Loader.ml JSONLD_Context.ml JSONLD_Expand.ml Parser_JSONLD.ml Parser_JSONLD_Html.ml JSONLD_Compact.ml JSONLD_Flatten.ml JSONLD_FromRdf.ml JSONLD_Frame.ml JSONSchema_Validate.ml
    SPARQL_Eval_TimeBudget.ml
    SPARQL_Eval_Limits.ml
    SPARQL_HTTP_Response.ml
   
    SPARQL_HTTP_BackendInfo.ml
    SPARQL_HTTP_QueriesIndex.ml
    SPARQL_HTTP_StaticFiles.ml
    SPARQL_HTTP_Admin.ml
    SPARQL_HTTP_Routes.ml
   
    Parser_BallyhooHDT.ml
    Parser_BallyhooCOTTAS.ml
    RDF_CottasStore_ColumnSeq.ml
    RDF_CottasStore_PageCache.ml
    RDF_CottasStore_OnDiskIndex.ml
    RDF_CottasStore_DictWriter.ml
    RDF_CottasStore_PresenceBitmap.ml
    RDF_CottasStore_PresenceWriter.ml
    RDF_CottasStore_CompoundPresenceBitmap.ml
    RDF_CottasStore_CompoundPresenceWriter.ml
    RDF_CottasStore_OffsetsWriter.ml
    RDF_CottasStore_SubjectOffsetsWriter.ml
    RDF_CottasStore_BaseWriter.ml
    RDF_CottasStore_LazyDict.ml
    RDF_CottasStore_LazyDictRegistry.ml
    RDF_Store_LazyTermCache.ml
    RDF_Store_Columnar_OffsetIndex.ml
    RDF_Store_Columnar_SubjectOffsetIndex.ml
    RDF_Store_Columnar_DeltaLog.ml
    SPARQL_Plan_Pruning.ml
   
   
    SPARQL_Plan_AccessPath.ml
    RDF_CottasStore.ml
   
    fstar_pure_hashes.ml
    RDF_Dataset_Graphs.ml
    RDF_Canonical.ml
    RDF_Canonical_Manifest.ml
    RDF_GraphIsomorphism.ml
    GRDDL_Discovery.ml
    service_wrap_hook.ml
    SPARQL_FullText.ml SPARQL11_Algebra.ml XSD_Datatypes.ml RDF_Entailment_RDFS_DatatypeClash.ml XSD_IEEE754.ml RDF_Entailment_Regime.ml RDF_Entailment_RDFS_RhoDFClosure.ml RDF_Entailment_RDFSPlus.ml RDF_Entailment_RegimeDispatch.ml XForms_Bind.ml RDF_Pretty.ml OWL_QueryRewrite.ml OWL_QueryEval.ml OWL_Tests_Manifest.ml OWL2_SyntaxDL.ml RIF_Core_Syntax.ml Parser_RIFXML.ml RIF_Core_Translation.ml RIF_Core_Builtins.ml RIF_Core_Conformance.ml RIF_Core_Eval.ml RIF_Core_Tests.ml SPARQL11_Parser.ml SHACL_Validation.ml SHACL_NodeExpr.ml SHACL_Rules.ml
    ShEx_Schema.ml Parser_ShExC.ml ShEx_SchemaEq.ml ShEx_Validation.ml
    RML_Mapping.ml RML_Sources.ml RML_Eval.ml
    CSVW_Metadata.ml CSVW_URITemplate.ml CSVW_Formats.ml CSVW_Conversion.ml CSVW_Json.ml CSVW_Validate.ml
    VC_Context.ml
    VC_Multibase.ml
    VC_Credential.ml
    DID_Key.ml
    fstar_hacl_crypto.ml
    VC_DataIntegrity.ml
    RDF_Store_Columnar_DeltaMerge.ml
    SPARQL_Plan_Streamable.ml RDF_Store_Capabilities.ml RDF_Store_Capabilities_Cottas.ml RDF_Store_Capabilities_Delta.ml
    RML_VirtualSource.ml
    SPARQL11_Store.ml
    RDF_Store_Combine.ml
    RDF_Dataset_Merge.ml
    SPARQL_Protocol.ml
    SPARQL_HTTP_RunQuery.ml
    SPARQL_Update_Sandbox.ml
    SPARQL_Update_Analysis.ml
    SPARQL_Diagnostics.ml
    SPARQL_Explain.ml
    SPARQL_Query_Analysis.ml
    SPARQL_HTTP.ml SPARQL_HTTP_Client.ml SPARQL_Protocol_Client.ml SPARQL_ServiceDescription.ml SPARQL_GraphStore.ml
  )
  JS_TARGETS=(
    w3c_runner.byte
    factoidal.byte
    npm_entry.byte
    ../../../docs/fstar-extracted/w3c-runner.js
    ../../../docs/fstar-extracted/factoidal.js
    ../../../docs/fstar-extracted/factoidal-npm-entry.js
  )
  JS_SOURCES=(
    "${FSTAR_MODULES[@]}"
    ../../../bin/w3c-runner/w3c_runner.ml
    ../../../bin/factoidal-serve/factoidal_serve.ml
    ../../../bin/factoidal-serve/factoidal_serve_jsoo.ml
    ../../../bin/factoidal-http-client/factoidal_http_client_jsoo.ml
    ../../../bin/factoidal-cli/factoidal_cli.ml
    ../../../bin/npm-entry/entry_jsoo.ml
    parquet_zstd_stubs_jsoo.c
    hacl_stubs_jsoo.c
    fstar_int_stubs.js
    fstar_hash_stubs.js
    fstar_utf8_output_stubs.js
    vendor/fzstd.umd.js
    parquet_zstd_stubs.js
    hacl_stubs.js
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
      ocamlfind ocamlc -package fstar.lib,str,zarith,sha,digestif.c,unix,uucp -linkpkg -w -8-14-26 \
      -custom parquet_zstd_stubs_jsoo.c hacl_stubs_jsoo.c \
      "${FSTAR_MODULES[@]}" \
      ../../../bin/w3c-runner/w3c_runner.ml \
      -o w3c_runner.byte
    grep -i error _ocamlc_w3c_runner.log || true

    # Build factoidal (query + parse CLI) bytecode for js_of_ocaml.
    # The JS bundle does NOT link factoidal_http.ml (Unix-bound), so we
    # swap in factoidal_serve_jsoo.ml as the Factoidal_serve module — it
    # has the same signature as the native factoidal_serve.ml but errors
    # at runtime if `serve` is invoked from the browser.
    #
    # Phase 8 (#200 D, 2026-05-08): factoidal_serve* sources moved to
    # bin/factoidal-serve/. Stage a stub factoidal_serve.ml in cwd
    # (which becomes the OCaml `Factoidal_serve` module name), pointed
    # at the jsoo variant; clean up after the build.
    cp ../../../bin/factoidal-serve/factoidal_serve_jsoo.ml factoidal_serve.ml
    # Same staging trick for the query --endpoint remote-client path:
    # stage the JS stub as `factoidal_http_client.ml` in cwd so it
    # resolves to the OCaml module name factoidal_cli.ml expects
    # (Factoidal_http_client), without linking the native Unix-socket
    # glue (js_of_ocaml has no raw-TCP primitive).
    cp ../../../bin/factoidal-http-client/factoidal_http_client_jsoo.ml factoidal_http_client.ml
    FACTOIDAL_BYTE_RC=0
    run_with_heartbeat "ocamlc factoidal.byte" "_ocamlc_factoidal.log" -- \
      ocamlfind ocamlc -package fstar.lib,str,zarith,sha,digestif.c,unix,uucp -linkpkg -w -8-14-26 \
      -custom parquet_zstd_stubs_jsoo.c hacl_stubs_jsoo.c \
      -I ../../../bin/factoidal-explain \
      "${FSTAR_MODULES[@]}" \
      ../../../bin/factoidal-explain/factoidal_explain.ml \
      factoidal_serve.ml \
      factoidal_http_client.ml \
      ../../../bin/factoidal-cli/factoidal_cli.ml \
      -o factoidal.byte || FACTOIDAL_BYTE_RC=$?
    # Clean up the staged stubs so a subsequent native build doesn't
    # pick them up. Always clean, even on compile failure.
    rm -f factoidal_serve.ml factoidal_http_client.ml
    if [[ "$FACTOIDAL_BYTE_RC" -ne 0 ]]; then
      cat _ocamlc_factoidal.log
      echo "  ERROR: factoidal.byte build failed (rc=$FACTOIDAL_BYTE_RC)" >&2
      exit "$FACTOIDAL_BYTE_RC"
    fi
    grep -i error _ocamlc_factoidal.log || true

    # Build npm-entry bytecode (bin/npm-entry/entry_jsoo.ml): the
    # persistent string/JSON ABI for the npm package. Needs the
    # js_of_ocaml library for Js.export / Js.wrap_callback.
    run_with_heartbeat "ocamlc npm_entry.byte" "_ocamlc_npm_entry.log" -- \
      ocamlfind ocamlc -package fstar.lib,str,zarith,sha,digestif.c,unix,uucp,js_of_ocaml -linkpkg -w -8-14-26 \
      -custom parquet_zstd_stubs_jsoo.c hacl_stubs_jsoo.c \
      "${FSTAR_MODULES[@]}" \
      ../../../bin/npm-entry/entry_jsoo.ml \
      -o npm_entry.byte
    grep -i error _ocamlc_npm_entry.log || true

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
      hacl_stubs.js \
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
      hacl_stubs.js \
      factoidal.byte \
      -o ../../../docs/fstar-extracted/factoidal.js
    grep -v "Warning \[deprecated" _jsoo_factoidal.log | grep -v "^$" || true

    run_with_heartbeat "js_of_ocaml npm-entry" "_jsoo_npm_entry.log" -- \
      js_of_ocaml \
      +zarith_stubs_js/biginteger.js \
      +zarith_stubs_js/runtime.js \
      fstar_int_stubs.js \
      fstar_hash_stubs.js \
      fstar_utf8_output_stubs.js \
      vendor/fzstd.umd.js \
      parquet_zstd_stubs.js \
      hacl_stubs.js \
      npm_entry.byte \
      -o ../../../docs/fstar-extracted/factoidal-npm-entry.js
    grep -v "Warning \[deprecated" _jsoo_npm_entry.log | grep -v "^$" || true
    echo "  Built: docs/fstar-extracted/factoidal-npm-entry.js ($(wc -c < ../../../docs/fstar-extracted/factoidal-npm-entry.js) bytes)"

    echo "  Built: docs/fstar-extracted/w3c-runner.js ($(wc -c < ../../../docs/fstar-extracted/w3c-runner.js) bytes)"
    echo "  Built: docs/fstar-extracted/factoidal.js   ($(wc -c < ../../../docs/fstar-extracted/factoidal.js) bytes)"
  fi

  cd ..
  record_phase_timing "js" "$PHASE_START_JS" "$EXTRACT_COUNT"
  echo ""
fi

# Step 5: Build WebAssembly via wasm_of_ocaml (experimental)
# Produces an artifact even though it won't run without extra JS stubs —
# see the header comment for the list of missing primitives.
if [[ "$STEP" == "wasm" ]]; then
  echo "--- Step 5: OCaml → WebAssembly (wasm_of_ocaml, experimental) ---"
  PHASE_START_WASM=$(date +%s)
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
     && ! needs_rebuild_from_sources "$W3C_WASM_LOADER" w3c_runner.byte wasm_runtime/zarith_runtime_wasm.js wasm_runtime/zarith_runtime.wat wasm_runtime/stdint_uint32_runtime.wat fstar_int_stubs.js \
     && ! needs_rebuild_from_sources "$W3C_WASM_ASSET" w3c_runner.byte wasm_runtime/zarith_runtime_wasm.js wasm_runtime/zarith_runtime.wat wasm_runtime/stdint_uint32_runtime.wat fstar_int_stubs.js; then
    echo "  WebAssembly bundle already up to date; skipping wasm_of_ocaml rebuild."
  else
    WASM_RC=0
    run_with_heartbeat "wasm_of_ocaml w3c-runner" "_waoc_w3c_runner.log" -- \
      wasm_of_ocaml compile \
      +zarith_stubs_js/biginteger.js \
      +zarith_stubs_js/runtime.js \
      wasm_runtime/zarith_runtime_wasm.js \
      wasm_runtime/zarith_runtime.wat \
      wasm_runtime/stdint_uint32_runtime.wat \
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
  record_phase_timing "wasm" "$PHASE_START_WASM" "$EXTRACT_COUNT"
  echo ""
fi

# Step 5b: Build WebAssembly for the factoidal CLI (experimental).
# Same caveats as Step 5. Produces docs/fstar-extracted/factoidal.wasm.js
# plus factoidal.wasm.assets/ so the browser can load a wasm build of
# factoidal the same way it already loads w3c-runner.wasm.js.
if [[ "$STEP" == "wasm-factoidal" ]]; then
  echo "--- Step 5b: factoidal CLI → WebAssembly (wasm_of_ocaml, experimental) ---"
  PHASE_START_WASM_FACTOIDAL=$(date +%s)
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
     && ! needs_rebuild_from_sources "$FACTOIDAL_WASM_LOADER" factoidal.byte wasm_runtime/zarith_runtime_wasm.js wasm_runtime/zarith_runtime.wat wasm_runtime/stdint_uint32_runtime.wat fstar_int_stubs.js \
     && ! needs_rebuild_from_sources "$FACTOIDAL_WASM_ASSET" factoidal.byte wasm_runtime/zarith_runtime_wasm.js wasm_runtime/zarith_runtime.wat wasm_runtime/stdint_uint32_runtime.wat fstar_int_stubs.js; then
    echo "  factoidal WebAssembly bundle already up to date; skipping wasm_of_ocaml rebuild."
  else
    WASM_RC=0
    run_with_heartbeat "wasm_of_ocaml factoidal" "_waoc_factoidal.log" -- \
      wasm_of_ocaml compile \
      +zarith_stubs_js/biginteger.js \
      +zarith_stubs_js/runtime.js \
      wasm_runtime/zarith_runtime_wasm.js \
      wasm_runtime/zarith_runtime.wat \
      wasm_runtime/stdint_uint32_runtime.wat \
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

  if [[ -f npm_entry.byte ]]; then
    run_with_heartbeat "wasm_of_ocaml npm-entry" "_waoc_npm_entry.log" -- \
      wasm_of_ocaml compile \
      +zarith_stubs_js/biginteger.js \
      +zarith_stubs_js/runtime.js \
      wasm_runtime/zarith_runtime_wasm.js \
      wasm_runtime/zarith_runtime.wat \
      wasm_runtime/stdint_uint32_runtime.wat \
      fstar_int_stubs.js \
      hacl_stubs.js \
      npm_entry.byte \
      -o ../../../docs/fstar-extracted/factoidal-npm-entry.wasm.js
    python3 wasm_stub_shims.py ../../../docs/fstar-extracted/factoidal-npm-entry.wasm.js
  fi
  cd ..
  record_phase_timing "wasm-factoidal" "$PHASE_START_WASM_FACTOIDAL" "$EXTRACT_COUNT"
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

  # npm-entry engine bundles: the persistent string/JSON ABI that
  # powers CONSTRUCT / UPDATE / canonicalize through the package's
  # capabilities() probe. Listed in package.json "files" from day one,
  # but the copy was missing until 2026-07-04 -- the unit suite passed
  # via lib/engine-js.js's repo-tree fallback path, which a published
  # consumer does not have (found by npm pack --dry-run: the tarball
  # shipped without them and the API silently degraded).
  if [[ -f "$JSDIR/factoidal-npm-entry.js" ]]; then
    cp "$JSDIR/factoidal-npm-entry.js" "$NPMDIR/factoidal-npm-entry.js"
    echo "  Copied: $JSDIR/factoidal-npm-entry.js -> $NPMDIR/factoidal-npm-entry.js ($(wc -c < "$NPMDIR/factoidal-npm-entry.js") bytes)"
  fi
  if [[ -f "$JSDIR/factoidal-npm-entry.wasm.js" ]]; then
    cp "$JSDIR/factoidal-npm-entry.wasm.js" "$NPMDIR/factoidal-npm-entry.wasm.js"
    echo "  Copied: $JSDIR/factoidal-npm-entry.wasm.js -> $NPMDIR/factoidal-npm-entry.wasm.js ($(wc -c < "$NPMDIR/factoidal-npm-entry.wasm.js") bytes)"
  fi
  if [[ -d "$JSDIR/factoidal-npm-entry.wasm.assets" ]]; then
    rm -rf "$NPMDIR/factoidal-npm-entry.wasm.assets"
    cp -R "$JSDIR/factoidal-npm-entry.wasm.assets" "$NPMDIR/factoidal-npm-entry.wasm.assets"
    echo "  Copied: $JSDIR/factoidal-npm-entry.wasm.assets/ -> $NPMDIR/factoidal-npm-entry.wasm.assets/ ($(ls -1 "$NPMDIR/factoidal-npm-entry.wasm.assets" | wc -l | tr -d ' ') file(s))"
  fi

  # Packaging invariant: every entry in package.json "files" must
  # exist, or a published tarball silently ships a degraded API.
  MISSING_PKG_FILES=$(cd "$NPMDIR" && node -e '
    const fs = require("fs");
    const files = JSON.parse(fs.readFileSync("package.json", "utf8")).files || [];
    const missing = files.filter(f => !fs.existsSync(f.replace(/\/$/, "")));
    if (missing.length) { console.log(missing.join(" ")); }
  ')
  if [[ -n "$MISSING_PKG_FILES" ]]; then
    echo "  ERROR: package.json files entries missing from npm/factoidal/: $MISSING_PKG_FILES" >&2
    exit 1
  fi
  echo "  Packaging invariant OK: all package.json files entries exist."

  if [[ -f "$JSDIR/factoidal-npm-entry.js" ]]; then
    cp "$JSDIR/factoidal-npm-entry.js" "$NPMDIR/factoidal-npm-entry.js"
  fi
  if [[ -f "$JSDIR/factoidal-npm-entry.wasm.js" ]]; then
    cp "$JSDIR/factoidal-npm-entry.wasm.js" "$NPMDIR/factoidal-npm-entry.wasm.js"
  fi
  if [[ -d "$JSDIR/factoidal-npm-entry.wasm.assets" ]]; then
    rm -rf "$NPMDIR/factoidal-npm-entry.wasm.assets"
    cp -R "$JSDIR/factoidal-npm-entry.wasm.assets" "$NPMDIR/factoidal-npm-entry.wasm.assets"
  fi

  # Provenance stamp + claims block. The "claims" key (machine-readable
  # theorem-backed-claims summary citing docs/theorem-registry.md
  # sections, issue #403's G2 item) is hand-authored/audited content,
  # not generated here -- this step PRESERVES whatever "claims" object
  # is already in the on-disk version.json (if any) while refreshing
  # version/gitSha/builtAt. To update the claims content itself, edit
  # npm/factoidal/version.json's "claims" key directly (source of
  # truth), then this step carries it forward on every future build.
  GITSHA=$(git -C ../.. rev-parse HEAD 2>/dev/null || echo "unknown")
  BUILDTIME=$(date -u +%Y-%m-%dT%H:%M:%SZ)
  node -e '
    const fs = require("fs");
    const path = process.argv[3];
    let claims;
    try { claims = JSON.parse(fs.readFileSync(path, "utf8")).claims; }
    catch (_) { claims = undefined; }
    const pkg = JSON.parse(fs.readFileSync(require("path").join(require("path").dirname(path), "package.json"), "utf8"));
    const out = { version: pkg.version, gitSha: process.argv[1], builtAt: process.argv[2] };
    if (claims !== undefined) out.claims = claims;
    fs.writeFileSync(path, JSON.stringify(out, null, 2) + "\n");
  ' "$GITSHA" "$BUILDTIME" "$NPMDIR/version.json"
  echo "  Wrote:  $NPMDIR/version.json (git=$GITSHA, claims preserved if present)"
  echo ""

  # Mirror the package into the GitHub Pages tree so it is loadable
  # directly by a <script type="module"> tag with no npm install and
  # no CDN dependency -- raw.githubusercontent.com serves text/plain,
  # which browsers refuse to execute as an ES module, so the Pages
  # copy is the only same-origin path that works. This mirror is
  # regenerated on every `./build-ocaml.sh npm` run (this step), so it
  # never drifts from npm/factoidal/ — do not hand-edit anything under
  # docs/npm/factoidal/.
  PAGESDIR="../../docs/npm/factoidal"
  echo "  Mirroring $NPMDIR -> $PAGESDIR (Pages, no-npm-install browser load) ..."
  rm -rf "$PAGESDIR"
  mkdir -p "$PAGESDIR"
  rsync -a --exclude 'test' --exclude 'node_modules' "$NPMDIR/" "$PAGESDIR/"
  MIRROR_COUNT=$(find "$PAGESDIR" -type f | wc -l | tr -d ' ')
  echo "  Mirrored: $PAGESDIR ($MIRROR_COUNT files)"
fi

echo "=== Pipeline complete ==="
# Loud success marker. With `set -e` propagating any earlier failure
# this line is only reached on a clean run — useful to grep for in
# build logs and to gate downstream automation. Symmetric with the
# FAIL banner emitted by run_with_heartbeat's failure path.
echo "BUILD_STATUS=OK"
