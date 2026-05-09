#!/usr/bin/env bash
# tests/beyond-w3c/runners/run-js-node.sh
#
# Phase 2a (sub-issue #243) — run a SPARQL query through the
# js_of_ocaml bundle under Node. Same CLI shape as run-native.sh.
#
# This is a STUB until #243 lands: it prints a structured marker so
# run-parity.py can detect the runner is unimplemented and emit a grey
# cell rather than a red one. Replace the body with a real wrapper
# around `node docs/fstar-extracted/factoidal.js` once #243 starts.

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd)"
cd "$REPO_ROOT"

JS_BUNDLE="docs/fstar-extracted/factoidal.js"
[[ -f "$JS_BUNDLE" ]] || { echo "missing: $JS_BUNDLE (run ./formal/fstar/build-ocaml.sh js)" >&2; exit 2; }

# Sentinel so the orchestrator (Phase 2 #243) knows this runner is a
# stub. Real implementation: parse --query / --data the same way
# run-native.sh does, marshal them through node + factoidal.js, capture
# stdout, propagate exit code.
echo '{"_runner_status":"unimplemented","sub_issue":243}'
exit 77   # POSIX-ish "skip" sentinel
