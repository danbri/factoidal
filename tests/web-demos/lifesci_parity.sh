#!/usr/bin/env bash
# tests/web-demos/lifesci_parity.sh
#
# Run every query from the docs/fstar-extracted/demo-lifesci.html demo
# through three engines and assert parity of row counts:
#
#   1. native       : bin/darwin-arm64/factoidal  (or bin/linux-x86_64/)
#   2. js_of_ocaml  : node docs/fstar-extracted/factoidal.js
#   3. wasm_of_ocaml: node docs/fstar-extracted/factoidal.wasm.js
#
# The queries live in examples/wikidata/subsets/lifesci-kgx/queries/ and
# are referenced by tests/web-demos/lifesci_queries.json so the test
# definition travels with the repo (no parsing of the HTML required).
#
# Why: catch engine-specific regressions in the browser bundles before
# they land in the committed docs/fstar-extracted/ artefacts.
#
# Exit code: 0 iff all three engines produce the expected row count for
# every query.
#
# Usage:
#   tests/web-demos/lifesci_parity.sh          # run all
#   tests/web-demos/lifesci_parity.sh --skip-wasm   # skip wasm (faster)
#
# Requirements: node, jq.

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$REPO_ROOT"

# --- Engine selection -----------------------------------------------------
case "$(uname -s)-$(uname -m)" in
  Darwin-arm64)   NATIVE_BIN="bin/darwin-arm64/factoidal" ;;
  Linux-x86_64)   NATIVE_BIN="bin/linux-x86_64/factoidal" ;;
  *) echo "Unsupported platform: $(uname -s)-$(uname -m)" >&2; exit 2 ;;
esac

JS_BUNDLE="docs/fstar-extracted/factoidal.js"
WASM_BUNDLE="docs/fstar-extracted/factoidal.wasm.js"
SKIP_WASM=0

for arg in "$@"; do
  case "$arg" in
    --skip-wasm) SKIP_WASM=1 ;;
    *) echo "Unknown arg: $arg" >&2; exit 2 ;;
  esac
done

for f in "$NATIVE_BIN" "$JS_BUNDLE"; do
  [ -x "$f" ] || [ -f "$f" ] || { echo "Missing engine: $f" >&2; exit 2; }
done
[ $SKIP_WASM -eq 1 ] || [ -f "$WASM_BUNDLE" ] || {
  echo "Missing engine: $WASM_BUNDLE (use --skip-wasm to skip)" >&2; exit 2;
}
command -v node >/dev/null 2>&1 || { echo "Missing node" >&2; exit 2; }
command -v jq   >/dev/null 2>&1 || { echo "Missing jq"   >&2; exit 2; }

CONFIG="tests/web-demos/lifesci_queries.json"
[ -f "$CONFIG" ] || { echo "Missing $CONFIG" >&2; exit 2; }

# --- Dataset as --named args ---------------------------------------------
NAMED_ARGS=()
while IFS= read -r line; do
  NAMED_ARGS+=(--named "$line")
done < <(jq -r '.dataset[] | "\(.graph)=\(.file)"' "$CONFIG")

# --- Run one query on one engine, return row count (JSON) ----------------
run_query () {
  local engine="$1"
  local qfile="$2"
  local out
  case "$engine" in
    native) out=$("$NATIVE_BIN"         "${NAMED_ARGS[@]}" -q "$qfile" -o json 2>&1) ;;
    js)     out=$(node "$JS_BUNDLE"     "${NAMED_ARGS[@]}" -q "$qfile" -o json 2>&1) ;;
    wasm)   out=$(node "$WASM_BUNDLE"   "${NAMED_ARGS[@]}" -q "$qfile" -o json 2>&1) ;;
    *) echo "bad engine: $engine" >&2; return 2 ;;
  esac
  printf '%s' "$out" | jq '.results.bindings | length' 2>/dev/null || {
    echo "BAD_OUTPUT" >&2
    printf '%s\n' "$out" >&2
    return 1
  }
}

# --- Main loop ------------------------------------------------------------
OVERALL=0
while IFS= read -r query_json; do
  qname=$(echo   "$query_json" | jq -r '.name')
  qfile=$(echo   "$query_json" | jq -r '.file')
  qexp=$(echo    "$query_json" | jq -r '.expected_rows // empty')
  qexpmin=$(echo "$query_json" | jq -r '.expected_rows_min // empty')

  [ -f "$qfile" ] || { echo "SKIP $qname: missing $qfile"; continue; }

  echo "=== $qname ==="

  for engine in native js $( [ $SKIP_WASM -eq 1 ] || echo wasm ); do
    # Known-failure allowlist: if the config says this engine is
    # expected to fail this query, record it as KNOWN-FAIL rather
    # than letting it flip the overall exit code.
    known_fail=$(jq -r --arg e "$engine" --arg n "$qname" '.known_failures[$e][$n] // empty' "$CONFIG")

    actual=$(run_query "$engine" "$qfile" 2>/dev/null) || {
      if [ -n "$known_fail" ]; then
        echo "  $engine: query errored (KNOWN-FAIL: $known_fail)"
      else
        echo "  $engine: query errored  FAIL"
        OVERALL=1
      fi
      continue
    }

    verdict="FAIL"
    if [ -n "$qexp" ] && [ "$actual" -eq "$qexp" ]; then verdict="PASS"
    elif [ -n "$qexpmin" ] && [ "$actual" -ge "$qexpmin" ]; then verdict="PASS"
    fi

    if [ "$verdict" = "PASS" ]; then
      if [ -n "$qexp" ]; then
        echo "  $engine: $actual rows (expected $qexp)  PASS"
      else
        echo "  $engine: $actual rows (expected >= $qexpmin)  PASS"
      fi
    elif [ -n "$known_fail" ]; then
      echo "  $engine: $actual rows (KNOWN-FAIL: $known_fail)"
    else
      if [ -n "$qexp" ]; then
        echo "  $engine: $actual rows (expected $qexp)  FAIL"
      else
        echo "  $engine: $actual rows (expected >= $qexpmin)  FAIL"
      fi
      OVERALL=1
    fi
  done
done < <(jq -c '.queries[]' "$CONFIG")

echo "==="
if [ $OVERALL -eq 0 ]; then
  echo "lifesci parity: ALL PASS"
else
  echo "lifesci parity: FAILED — see above" >&2
fi
exit $OVERALL
