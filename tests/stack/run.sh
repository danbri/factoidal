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
# CANARY MODE (--canary [KB], default 512) runs the native route under a
# reduced stack, so a function that consumes a frame per input element
# fails HERE, with a case name, instead of only in a browser tab.
#
# It probes the knob before it trusts it.  `turtle-collection` is a
# recursion this suite has NOT repaired (readCollectionRest needs a
# worklist, not an accumulator): under a real 512 KB stack it must die.
# If it survives, the stack limit did not reach the process, every
# other canary result is meaningless, and the mode reports UNSUPPORTED
# rather than a green score.  An audit that cannot fail is evidence
# about the audit before it is evidence about the code (anti-pattern
# #28).
#
# Measured 2026-09-07, macOS 24.6.0, arm64: NEITHER `ulimit -s 512` NOR
# `LEAN_STACK_SIZE=131072` changes the result of a 100,000-item
# collection parse -- it still returns 200,001 quads.  The knob does not
# reach a Lean-compiled binary's main thread on this platform, so the
# probe fails and the mode declines to score.  Linux honours `ulimit -s`
# for the main thread; run the canary in CI.
#
# The wasm equivalent needs a diagnostic module, not a flag at run time.
# Rebuild with
#     -sSTACK_SIZE=262144 -sSTACK_OVERFLOW_CHECK=2
# in formal/lean4/Wasm/build-wasm.sh: the small stack makes an
# input-proportional recursion fail early, and OVERFLOW_CHECK=2 writes a
# canary word past the stack end so the abort NAMES the function instead
# of reporting "Maximum call stack size exceeded" from an arbitrary
# frame. That module is a diagnostic, never the shipped one.
#
# Usage:  tests/stack/run.sh [--route wasm|native|both] [--fixtures DIR]
#                            [--canary [KB]]
#
# Scores are printed as "N pass, M fail (out of T)" per route.
set -uo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
LEAN_DIR="$ROOT/formal/lean4"
CLI="$LEAN_DIR/.lake/build/bin/l4wasm-cli"

ROUTE=both
CANARY=0
CANARY_KB=512
FIXTURES="${STACK_FIXTURES:-${TMPDIR:-/tmp}/factoidal-stack-fixtures}"
TIMEOUT="${STACK_TIMEOUT:-120}"
while [ $# -gt 0 ]; do
  case "$1" in
    --route) ROUTE="$2"; shift 2 ;;
    --fixtures) FIXTURES="$2"; shift 2 ;;
    --timeout) TIMEOUT="$2"; shift 2 ;;
    --canary)
      CANARY=1
      case "${2:-}" in ''|-*) shift 1 ;; *) CANARY_KB="$2"; shift 2 ;; esac ;;
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

# ----------------------------------------------------------- canary probe
#
# Returns 0 when a reduced stack demonstrably reaches the process.
canary_knob_works() {
  local out
  out="$( ulimit -s "$CANARY_KB" 2>/dev/null
          LEAN_STACK_SIZE=$((CANARY_KB * 1024)) \
            "$CLI" call parseToDatasetJson \
            "$FIXTURES/args-turtle-collection.json" 2>&1 | head -c 40 )"
  # The control is an UNREPAIRED per-element recursion over 100,000
  # items. Success here means the limit was not applied.
  printf '%s' "$out" | grep -q '"ok":true' && return 1
  return 0
}

canary_case() { # canary_case <case> <op> <argsfile>
  local name="$1" op="$2" argsfile="$3" out rc
  out="$( ulimit -s "$CANARY_KB" 2>/dev/null
          LEAN_STACK_SIZE=$((CANARY_KB * 1024)) \
            run_capped "$TIMEOUT" "$CLI" call "$op" "$FIXTURES/$argsfile" 2>&1 )"
  rc=$?
  if [ "$rc" -ne 0 ]; then
    record canary "$name" 1 "exit $rc under ${CANARY_KB}KB: $(printf '%s' "$out" | head -c 140)"
  elif printf '%s' "$out" | grep -q '"ok":false'; then
    record canary "$name" 1 "engine error under ${CANARY_KB}KB: $(printf '%s' "$out" | head -c 140)"
  else
    record canary "$name" 0 "ok under ${CANARY_KB}KB"
  fi
}

# ------------------------------------------------------------------ wasm
wasm_case() {
  local name="$1" out rc
  out="$(run_capped "$TIMEOUT" node "$HERE/wasm_case.mjs" "$name" "$FIXTURES" 2>&1)"; rc=$?
  # turtle-collection is a KNOWN unrepaired per-element recursion (https://github.com/danbri/factoidal/issues/678):
  # it overflows the default wasm run too. Track it as an expected failure so
  # the suite is green while it is open and turns red if it ever passes.
  if [ "$name" = turtle-collection ]; then
    if printf '%s' "$out" | grep -q '"ok":true'; then
      record wasm "$name" 1 "UNEXPECTED PASS: flip this xfail and close https://github.com/danbri/factoidal/issues/678"
    else
      record wasm "$name" 0 "xfail: still overflows, tracked (https://github.com/danbri/factoidal/issues/678)"
    fi
    return
  fi
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

if [ "$CANARY" = 1 ]; then
  echo
  echo "=== canary route (native under a ${CANARY_KB}KB stack)"
  if canary_knob_works; then
    for row in "${CASES[@]}"; do
      set -- $row
      canary_case "$1" "$2" "$3"
    done
  else
    echo "    native ulimit route UNSUPPORTED here (neither \`ulimit -s\` nor"
    echo "    LEAN_STACK_SIZE reaches a Lean binary's main thread on macOS);"
    echo "    falling back to the wasm/JS canary below, which IS portable."
  fi
  # The tab overflow is a V8 CALL-STACK overflow, and `node --stack-size` DOES
  # bound that on every platform (measured 2026-09-08: the manifest case throws
  # under a small size before the fix, and passes after). This is the honest
  # canary for a browser tab; the wasm shadow-stack flag `-sSTACK_SIZE` bounds a
  # DIFFERENT stack and is not needed here. Runs the committed module, so a Lean
  # fix reaches it only after Wasm/build-wasm.sh.
  echo
  echo "=== canary route (wasm cases in Node under --stack-size=${CANARY_KB})"
  for row in "${CASES[@]}"; do
    set -- $row
    name="$1"
    out="$(run_capped "$TIMEOUT" node --stack-size="$CANARY_KB" "$HERE/wasm_case.mjs" "$name" "$FIXTURES" 2>&1)"; rc=$?
    threw=0
    if [ "$rc" -ne 0 ] || printf '%s' "$out" | grep -qi 'call stack\|RangeError\|overflow'; then threw=1; fi
    if [ "$name" = turtle-collection ]; then
      # KNOWN unrepaired per-element recursion (https://github.com/danbri/factoidal/issues/678): expected to overflow
      # until fixed. Pass the suite while it throws; FAIL (turn red) if it ever
      # stops throwing, so the fix flips this marker and closes the issue.
      if [ "$threw" -eq 1 ]; then record canary "$name" 0 "xfail: still overflows, tracked (https://github.com/danbri/factoidal/issues/678)"
      else record canary "$name" 1 "UNEXPECTED PASS: flip this xfail and close https://github.com/danbri/factoidal/issues/678"; fi
    elif [ "$threw" -eq 1 ]; then
      record canary "$name" 1 "wasm THREW under --stack-size=${CANARY_KB}: $(printf '%s' "$out" | head -c 140)"
    else
      record canary "$name" 0 "wasm ok under --stack-size=${CANARY_KB}"
    fi
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
