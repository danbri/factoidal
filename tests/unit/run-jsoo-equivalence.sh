#!/bin/bash
# tests/unit/run-jsoo-equivalence.sh
#
# Runs the SAME F*-extracted OCaml equivalence harness that run-all.sh
# runs natively (tests/unit/parser_fast_string_equivalence.ml), but
# compiled with js_of_ocaml and executed under Node — closing the
# "jsoo UTF-16 convention" risk named in
# docs/designissues/2026-08-10-faststring-refounding-plan.md's Decisions
# and Risks sections (task #47, migration step 6, last outstanding item).
#
# This is NOT a JS reimplementation of the test (CLAUDE.md iron rule
# #7 forbids that): it is the identical committed .ml file
# (parser_fast_string_equivalence.ml) plus the identical committed
# F*-extracted Parser_FastString{,_Spec,_CharBoundary}.ml from
# formal/fstar/ocaml-output/, compiled to OCaml bytecode and converted
# to JavaScript by js_of_ocaml, then run with `node`. Any PASS/FAIL
# divergence from the native run is therefore a real js_of_ocaml
# runtime-representation divergence, not a test-authoring difference.
#
# Build recipe mirrors formal/fstar/build-ocaml.sh's Step 4 (JS build)
# exactly: same package set, same zarith_stubs_js + fstar_*_stubs.js
# runtime files, same default js_of_ocaml flags (no --enable/--disable
# overrides) — so this measures the SAME string representation the
# production docs/fstar-extracted/factoidal.js bundle ships with.
#
# Usage:
#   ./run-jsoo-equivalence.sh
#
# Exit code: 0 iff the corpus reports "0 unexpected fail" AND the node
# process itself exits 0 (parser_fast_string_equivalence.ml's own
# `if !failed > 0 then exit 1` convention). Non-zero otherwise.
#
# Rule anchors: CLAUDE.md rule #14 (no `|| true` swallowing), rule #16
# (no tail/head truncation of output), rule #25 (labelled score line).

set -uo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
OCAML_OUT="$REPO_ROOT/formal/fstar/ocaml-output"
BUILD_DIR="$SCRIPT_DIR/_build_jsoo"
TEST_ML="$SCRIPT_DIR/parser_fast_string_equivalence.ml"

if [[ ! -f "$TEST_ML" ]]; then
  echo "ERROR: $TEST_ML not found" >&2
  exit 2
fi

for req in Parser_FastString_Spec.ml Parser_FastString_CharBoundary.ml Parser_FastString.ml \
           fstar_int_stubs.js fstar_hash_stubs.js fstar_utf8_output_stubs.js; do
  if [[ ! -f "$OCAML_OUT/$req" ]]; then
    echo "ERROR: $OCAML_OUT/$req not found — run" >&2
    echo "       'cd formal/fstar && ./build-ocaml.sh extract' first." >&2
    exit 2
  fi
done

command -v ocamlfind >/dev/null || { echo "ERROR: ocamlfind not found — activate the F* opam switch (eval \$(opam env --switch=fstar))" >&2; exit 2; }
command -v js_of_ocaml >/dev/null || { echo "ERROR: js_of_ocaml not found — opam install js_of_ocaml js_of_ocaml-compiler zarith_stubs_js" >&2; exit 2; }
command -v node >/dev/null || { echo "ERROR: node not found on PATH" >&2; exit 2; }

rm -rf "$BUILD_DIR"
mkdir -p "$BUILD_DIR"

# Stage the exact committed extraction outputs + the exact committed
# test file. No edits, no reimplementation — see file banner above.
cp "$OCAML_OUT/Parser_FastString_Spec.ml" "$BUILD_DIR/"
cp "$OCAML_OUT/Parser_FastString_CharBoundary.ml" "$BUILD_DIR/"
cp "$OCAML_OUT/Parser_FastString.ml" "$BUILD_DIR/"
cp "$OCAML_OUT/fstar_int_stubs.js" "$OCAML_OUT/fstar_hash_stubs.js" "$OCAML_OUT/fstar_utf8_output_stubs.js" "$BUILD_DIR/"
cp "$TEST_ML" "$BUILD_DIR/"

echo "--- ocamlfind ocamlc (bytecode) ---"
BUILD_RC=0
BUILD_OUT=$(cd "$BUILD_DIR" && ocamlfind ocamlc \
  -package fstar.lib,str,zarith,sha,digestif.c,unix,uucp -linkpkg -w -8-14-26 \
  Parser_FastString_Spec.ml Parser_FastString_CharBoundary.ml Parser_FastString.ml \
  parser_fast_string_equivalence.ml \
  -o fast_string_equiv.byte 2>&1) || BUILD_RC=$?
echo "$BUILD_OUT" | grep -vi "^findlib: \[WARNING\]\|^ocamlfind: \[WARNING\]" || true
if [[ $BUILD_RC -ne 0 ]]; then
  echo "  BUILD FAILED (ocamlc, rc=$BUILD_RC)" >&2
  exit 1
fi

echo "--- js_of_ocaml (bytecode -> JS) ---"
# Same runtime file set + same order as build-ocaml.sh's Step 4 (minus
# the Zstd/HACL shims, which this test module never calls). No
# --enable/--disable flags: this is js_of_ocaml's DEFAULT string
# representation, which as of js_of_ocaml 6.4.1 is use-js-string=true
# (confirmed by inspecting the emitted buildInfo header on both this
# bundle and the committed production docs/fstar-extracted/factoidal.js
# — both say `use-js-string=true`). That is the actual "stated domain"
# this measurement covers, not the "bytes-as-JS-chars" classic/array
# representation the plan doc's Decisions section named — see the
# 2026-08-11 JS-parity results section of the plan doc for the
# discrepancy and why it doesn't change the pass/fail verdict here.
JSOO_RC=0
JSOO_OUT=$(cd "$BUILD_DIR" && js_of_ocaml \
  +zarith_stubs_js/biginteger.js \
  +zarith_stubs_js/runtime.js \
  fstar_int_stubs.js \
  fstar_hash_stubs.js \
  fstar_utf8_output_stubs.js \
  fast_string_equiv.byte \
  -o fast_string_equiv.js 2>&1) || JSOO_RC=$?
echo "$JSOO_OUT" | grep -v "^Warning \[deprecated\|^Warning \[free-variables\|^Warning \[overriding-primitive\|^  old:\|^  new:\|^vars:" || true
if [[ $JSOO_RC -ne 0 ]]; then
  echo "  BUILD FAILED (js_of_ocaml, rc=$JSOO_RC)" >&2
  exit 1
fi

echo "--- node fast_string_equiv.js ---"
RUN_RC=0
RUN_OUT=$(node "$BUILD_DIR/fast_string_equiv.js" 2>&1) || RUN_RC=$?
echo "$RUN_OUT"

echo "============================================================"
if [[ $RUN_RC -eq 0 ]]; then
  echo "run-jsoo-equivalence: PASS (node exit 0)"
  exit 0
else
  echo "run-jsoo-equivalence: FAIL (node exit $RUN_RC)"
  exit 1
fi
