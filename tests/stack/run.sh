#!/usr/bin/env bash
#
# tests/stack/run.sh — the deep-input stress suite.
#
# Every case here is an ordinary document that is only LARGE in one
# dimension a caller controls: how many entity references, how long a
# literal, how many collection items, how many quads, how many UNION
# arms, how deep a group, how many manifest entries. A function that
# recurses over that dimension without a tail-call loop consumes one
# C stack frame per step and the process dies; a function that loops,
# or that carries a worklist, does not.
#
# Two routes, because they have different stacks:
#   wasm    the shipped module (docs/web/hub/assets/l4/), run in Node.
#           This is the SMALLEST stack we ship, and the one a browser
#           tab runs.  IT IS THE COMMITTED ARTIFACT: a Lean fix does
#           not reach it until the wasm module is rebuilt.
#   native  formal/lean4/.lake/build/bin/l4wasm-cli, the same dispatch
#           ABI compiled for the host, with the host's 8 MB stack.
#
# Usage:  tests/stack/run.sh [--route wasm|native|both] [--fixtures DIR]
#
# Scores are printed as "N pass, M fail (out of T)" per route.
set -uo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
LEAN_DIR="$ROOT/formal/lean4"
CLI="$LEAN_DIR/.lake/build/bin/l4wasm-cli"

ROUTE=both
FIXTURES="${STACK_FIXTURES:-${TMPDIR:-/tmp}/factoidal-stack-fixtures}"
TIMEOUT="${STACK_TIMEOUT:-120}"
while [ $# -gt 0 ]; do
  case "$1" in
    --route) ROUTE="$2"; shift 2 ;;
    --fixtures) FIXTURES="$2"; shift 2 ;;
    --timeout) TIMEOUT="$2"; shift 2 ;;
    *) echo "unknown argument: $1" >&2; exit 2 ;;
  esac
done

echo "=== generating fixtures in $FIXTURES"
python3 "$HERE/gen_cases.py" "$FIXTURES" || exit 2

# A portable timeout: macOS ships no coreutils `timeout`.
# The watchdog's own stdout MUST go to /dev/null. Command substitution
# waits for every writer to close the pipe, so a watchdog that inherits
# stdout holds `$(...)` open for the whole timeout and every case then
# "passes" after exactly the cap. That bug made the first run of this
# suite report seven passes at 30,000 ms each.
run_capped() {
  local secs="$1"; shift
  "$@" &
  local pid=$!
  ( sleep "$secs"; kill -9 "$pid" ) >/dev/null 2>&1 &
  local killer=$!
  wait "$pid"; local rc=$?
  kill -9 "$killer" >/dev/null 2>&1
  wait "$killer" 2>/dev/null
  return "$rc"
}

PASS=0; FAIL=0; TOTAL=0
declare -a RESULTS=()

record() { # record <route> <case> <ok:0|1> <detail>
  TOTAL=$((TOTAL + 1))
  if [ "$3" = 0 ]; then
    PASS=$((PASS + 1)); printf 'ok   %-8s %-22s %s\n' "$1" "$2" "$4"
  else
    FAIL=$((FAIL + 1)); printf 'FAIL %-8s %-22s %s\n' "$1" "$2" "$4"
  fi
}

# ---------------------------------------------------------------- native
native_case() { # native_case <case> <op> <argsfile>
  local name="$1" op="$2" argsfile="$3"
  local out rc t0 t1
  t0=$(python3 -c 'import time;print(int(time.time()*1000))')
  out="$(run_capped "$TIMEOUT" "$CLI" call "$op" "$FIXTURES/$argsfile" 2>&1)"; rc=$?
  t1=$(python3 -c 'import time;print(int(time.time()*1000))')
  local ms=$((t1 - t0))
  if [ "$rc" -ne 0 ]; then
    record native "$name" 1 "exit $rc after ${ms}ms: $(printf '%s' "$out" | head -c 160)"
  elif printf '%s' "$out" | grep -q '"ok":false'; then
    record native "$name" 1 "engine error after ${ms}ms: $(printf '%s' "$out" | head -c 160)"
  else
    record native "$name" 0 "${ms}ms"
  fi
}

# ------------------------------------------------------------------ wasm
wasm_case() {
  local name="$1" out rc
  out="$(run_capped "$TIMEOUT" node "$HERE/wasm_case.mjs" "$name" "$FIXTURES" 2>&1)"; rc=$?
  if [ "$rc" -ne 0 ]; then
    record wasm "$name" 1 "node exit $rc: $(printf '%s' "$out" | head -c 160)"
    return
  fi
  local line
  line="$(printf '%s' "$out" | grep '^{' | tail -1)"
  if printf '%s' "$line" | grep -q '"ok":true'; then
    record wasm "$name" 0 "$(printf '%s' "$line" | python3 -c 'import json,sys;print(str(json.load(sys.stdin).get("ms"))+"ms")' 2>/dev/null)"
  else
    record wasm "$name" 1 "$(printf '%s' "$line" | head -c 200)"
  fi
}

CASES=(
  "xml-entities        parseToDatasetJson   args-xml.json"
  "turtle-literal      parseToDatasetJson   args-turtle-literal.json"
  "turtle-collection   parseToDatasetJson   args-turtle-collection.json"
  "nquads-one-subject  parseToDatasetJson   args-nquads.json"
  "sparql-union        queryDataset         args-sparql-union.json"
  "sparql-nested       queryDataset         args-sparql-nested.json"
  "manifest            storeManifestInspect manifest-args.json"
)

if [ "$ROUTE" = native ] || [ "$ROUTE" = both ]; then
  if [ ! -x "$CLI" ]; then
    echo "=== native: building l4wasm-cli"
    ( cd "$LEAN_DIR" && lake build l4wasm-cli >/dev/null ) || { echo "lake build failed"; exit 2; }
  fi
  echo
  echo "=== native route ($CLI)"
  for row in "${CASES[@]}"; do
    # shellcheck disable=SC2086
    set -- $row
    native_case "$1" "$2" "$3"
  done
fi

if [ "$ROUTE" = wasm ] || [ "$ROUTE" = both ]; then
  echo
  echo "=== wasm route (docs/web/hub/assets/l4/l4factoidal.wasm, Node $(node --version))"
  echo "    NOTE: this is the COMMITTED module. A Lean fix reaches it only"
  echo "    after formal/lean4/Wasm/build-wasm.sh is rerun."
  for row in "${CASES[@]}"; do
    set -- $row
    wasm_case "$1"
  done
fi

# ------------------------------- surfaces the shipped ABI does not reach
echo
echo "=== not reachable from a shipped surface (reported, not scored)"
echo "    jsonld-nested   5000-deep JSON-LD: the wasm/CLI parse op answers"
echo "                    \"JSON-LD is not in the Lean engine's v1 surface\""
echo "                    (Wasm/Ops/Parse.lean). Fixture is generated at"
echo "                    \$FIXTURES/jsonld-nested.jsonld for the l4jsonld-probe."
echo "    shacl-shapes    5000-shape SHACL graph: no SHACL op on the dispatch"
echo "                    ABI. Fixture at \$FIXTURES/shacl-shapes.ttl for l4shacl."

echo
echo "stack stress: $PASS pass, $FAIL fail (out of $TOTAL)"
[ "$FAIL" -eq 0 ]
