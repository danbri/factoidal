#!/usr/bin/env bash
# ShExC three-way differential probe: our F*-extracted Parser.ShExC vs
# the vendored tree-sitter-shexc grammar (third_party/tree-sitter-shexc,
# MIT, see its PROVENANCE.md) vs the shexTest corpus's expected verdict.
#
# ADVISORY, not conformance: this is a comparison probe in the sense of
# skills/test-suites (like the Jena probes) -- it is not a dashboard row.
# The conformance number for grammar rejection is shex_runner
# --negative-syntax (Parser.ShExC itself).
#
# Requires: node + npm (node-gyp compiles the vendored src/parser.c on
# first run), and a built bin/<platform>/shex_runner.
set -euo pipefail
cd "$(dirname "$0")"
REPO_ROOT="$(cd ../.. && pwd)"

case "$(uname -s)-$(uname -m)" in
  Linux-x86_64)  PLATFORM=linux-x86_64 ;;
  Darwin-arm64)  PLATFORM=darwin-arm64 ;;
  *) echo "unsupported platform $(uname -s)-$(uname -m)" >&2; exit 2 ;;
esac
SHEX_RUNNER="$REPO_ROOT/bin/$PLATFORM/shex_runner"
if [[ ! -x "$SHEX_RUNNER" ]]; then
  echo "missing $SHEX_RUNNER -- build it first (formal/fstar/build-ocaml.sh compile)" >&2
  exit 2
fi

# 1. Node deps (tree-sitter runtime + node-gyp toolchain).
if [[ ! -d node_modules ]]; then
  npm install
fi

# 2. Compile the vendored grammar's parser.c into a Node addon. Build
#    artifacts live HERE (.build/, gitignored), never in third_party/ --
#    the vendored tree stays byte-identical to upstream.
if [[ ! -f .build/build/Release/tree_sitter_shexc_binding.node ]]; then
  rm -rf .build
  mkdir -p .build
  cp -r "$REPO_ROOT/third_party/tree-sitter-shexc/binding.gyp" \
        "$REPO_ROOT/third_party/tree-sitter-shexc/src" \
        "$REPO_ROOT/third_party/tree-sitter-shexc/bindings" \
        .build/
  ln -sfn ../node_modules .build/node_modules
  (cd .build && ../node_modules/.bin/node-gyp rebuild)
fi

# 3. Our parser's verdicts. Both runs may exit 1 (that is the runner
#    reporting FAILs/mismatches, which is exactly the data this probe
#    consumes) -- capture rc explicitly, fail only on real breakage
#    (anti-pattern #14: no `|| true`).
mkdir -p out
NEG_RC=0
timeout 600 "$SHEX_RUNNER" --negative-syntax -v > out/our-negative.txt || NEG_RC=$?
if [[ "$NEG_RC" -gt 1 ]]; then
  echo "shex_runner --negative-syntax broke (rc=$NEG_RC)" >&2
  exit "$NEG_RC"
fi
DIFF_RC=0
timeout 600 "$SHEX_RUNNER" --differential > out/our-differential.txt || DIFF_RC=$?
if [[ "$DIFF_RC" -gt 1 ]]; then
  echo "shex_runner --differential broke (rc=$DIFF_RC)" >&2
  exit "$DIFF_RC"
fi

# 4. Three-way agreement table.
node three-way.js out/our-negative.txt out/our-differential.txt
