#!/usr/bin/env bash
# tools/internal-tests.sh — one runner for Factoidal's PROJECT-INTERNAL
# test assets (not the W3C conformance manifests: those run through
# w3c-tests.sh / formal/fstar/generate-report.sh and their own per-suite
# dispatch, tools/dispatch_test_suites.sh, for manifests whose `spec:`
# field is a real W3C/OGC/IETF URL).
#
# This script covers what is left: Lean 4 build-time #guard checks,
# the Lean Wasm/CLI ABI smoke suites, the Lean corpus probes declared
# as lean_exe targets, the Node hub + npm test suites, the block-engine
# smoke scripts, the persisted-store census, every `.github/test-suites/
# *.yaml` manifest whose `spec:` is "internal" (the F*-side internal
# regression registry), and the tests/ scripts that are not the
# `runner:` of ANY manifest (orphaned from both registries).
#
# Suite discovery is ALWAYS derived from the repository tree and from
# tools/dispatch_test_suites.sh at run time (anti-pattern #30: a cached
# or hard-coded suite list reports the cache, not the tree). No suite
# name below is hard-coded as a list to iterate — each block below
# GLOBS or QUERIES the repository, and only the resulting names are
# iterated.
#
# Usage:
#   tools/internal-tests.sh --list     print the derived suite names, one per line, exit 0
#   tools/internal-tests.sh --quick    run only within a ~60s per-suite budget
#   tools/internal-tests.sh            run everything (larger per-suite budget)
#
# Every suite's exit code is captured explicitly (anti-pattern #14 —
# never `|| true`). A suite this script cannot run in this environment
# (missing external service, missing submodule content, wrong-platform
# binary) is reported as SKIP with a reason, not folded into pass or
# fail. Logs land under tmp/internal-tests-<timestamp>/, printed at
# the top of the run so a failure's full output is one path away.
#
# Exit code: 0 only if every suite that ran PASSED and the suite list
# was non-empty. Any FAIL, or an empty suite list, is a non-zero exit.

set -uo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$REPO_ROOT" || exit 1

QUICK=0
LIST_ONLY=0
for arg in "$@"; do
  case "$arg" in
    --quick) QUICK=1 ;;
    --list) LIST_ONLY=1 ;;
    -h|--help)
      sed -n '2,33p' "${BASH_SOURCE[0]}"
      exit 0
      ;;
    *)
      echo "internal-tests: unknown argument: $arg" >&2
      exit 2
      ;;
  esac
done

QUICK_BUDGET=60
FULL_BUDGET=300

TS="$(date -u +%Y%m%dT%H%M%SZ)"
LOG_DIR="$REPO_ROOT/tmp/internal-tests-$TS"
if [ "$LIST_ONLY" -eq 0 ]; then
  mkdir -p "$LOG_DIR" || { echo "internal-tests: cannot create $LOG_DIR" >&2; exit 1; }
  echo "internal-tests: logs under $LOG_DIR"
fi

SUITE_COUNT=0
PASS_TOTAL=0
FAIL_TOTAL=0
SKIP_TOTAL=0
FAIL_NAMES=()

# run_suite <name> <budget-secs> <cmd...>
# Captures the exit code explicitly. In --quick mode the budget is
# capped at QUICK_BUDGET; a suite that does not finish within it is
# reported SKIP (time budget), never folded into fail.
run_suite() {
  local name="$1" budget="$2"; shift 2
  SUITE_COUNT=$((SUITE_COUNT + 1))
  if [ "$LIST_ONLY" -eq 1 ]; then
    echo "$name"
    return 0
  fi
  local eff="$budget"
  if [ "$QUICK" -eq 1 ] && [ "$eff" -gt "$QUICK_BUDGET" ]; then
    eff="$QUICK_BUDGET"
  fi
  local log="$LOG_DIR/${name//\//_}.log"
  local start end rc dur
  start=$(date +%s)
  timeout "$eff" "$@" < /dev/null > "$log" 2>&1
  rc=$?
  end=$(date +%s)
  dur=$((end - start))
  if [ "$rc" -eq 124 ] || [ "$rc" -eq 137 ]; then
    if [ "$QUICK" -eq 1 ]; then
      echo "SKIP  $name  (quick mode: exceeded ${eff}s budget)  [${dur}s]  $log"
      SKIP_TOTAL=$((SKIP_TOTAL + 1))
    else
      echo "FAIL  $name  (timed out after ${eff}s)  [${dur}s]  $log"
      FAIL_TOTAL=$((FAIL_TOTAL + 1))
      FAIL_NAMES+=("$name")
    fi
  elif [ "$rc" -eq 0 ]; then
    echo "PASS  $name  [${dur}s]  $log"
    PASS_TOTAL=$((PASS_TOTAL + 1))
  else
    echo "FAIL  $name  (rc=$rc)  [${dur}s]  $log"
    FAIL_TOTAL=$((FAIL_TOTAL + 1))
    FAIL_NAMES+=("$name")
  fi
}

# skip_suite <name> <reason> — for a suite this environment cannot run
# at all (no live service, no vendored deps installed, no matching
# platform binary). Counted apart from pass/fail per the task contract.
skip_suite() {
  local name="$1" reason="$2"
  SUITE_COUNT=$((SUITE_COUNT + 1))
  if [ "$LIST_ONLY" -eq 1 ]; then
    echo "$name"
    return 0
  fi
  echo "SKIP  $name  ($reason)"
  SKIP_TOTAL=$((SKIP_TOTAL + 1))
}

# run_suite_autoprobe <name> <budget> <runner> [args...]
# For a zero-arg Lean corpus probe: some expect CWD=repo root, some
# expect CWD=formal/lean4 (both conventions exist in the committed
# probes; see docs/20260903-internal-test-inventory.md). Try repo root
# first; if the failure text names the OTHER convention's tell
# ("ensure-test-env" or "catalog not read"), retry once from
# formal/lean4. If the FIRST line of output is a usage message, this
# is a parameterised tool, not a zero-arg probe: skip it rather than
# counting a usage error as a failure.
run_probe() {
  local name="$1" budget="$2" bin="$3"
  SUITE_COUNT=$((SUITE_COUNT + 1))
  if [ "$LIST_ONLY" -eq 1 ]; then
    echo "$name"
    return 0
  fi
  local eff="$budget"
  if [ "$QUICK" -eq 1 ] && [ "$eff" -gt "$QUICK_BUDGET" ]; then
    eff="$QUICK_BUDGET"
  fi
  local log="$LOG_DIR/${name//\//_}.log"
  local start end rc dur
  start=$(date +%s)
  ( cd "$REPO_ROOT" && timeout "$eff" "$bin" < /dev/null ) > "$log" 2>&1
  rc=$?
  if grep -qE "run tools/ensure-test-env.sh|catalog not read" "$log" 2>/dev/null; then
    ( cd "$REPO_ROOT/formal/lean4" && timeout "$eff" "$bin" < /dev/null ) > "$log" 2>&1
    rc=$?
  fi
  end=$(date +%s)
  dur=$((end - start))
  if head -1 "$log" 2>/dev/null | grep -qiE "^usage:"; then
    echo "SKIP  $name  (takes required arguments, not a zero-arg probe)  [${dur}s]  $log"
    SKIP_TOTAL=$((SKIP_TOTAL + 1))
    return 0
  fi
  if [ "$rc" -eq 124 ] || [ "$rc" -eq 137 ]; then
    if [ "$QUICK" -eq 1 ]; then
      echo "SKIP  $name  (quick mode: exceeded ${eff}s budget)  [${dur}s]  $log"
      SKIP_TOTAL=$((SKIP_TOTAL + 1))
    else
      echo "FAIL  $name  (timed out after ${eff}s)  [${dur}s]  $log"
      FAIL_TOTAL=$((FAIL_TOTAL + 1)); FAIL_NAMES+=("$name")
    fi
  elif [ "$rc" -eq 0 ]; then
    echo "PASS  $name  [${dur}s]  $log"
    PASS_TOTAL=$((PASS_TOTAL + 1))
  else
    echo "FAIL  $name  (rc=$rc)  [${dur}s]  $log"
    FAIL_TOTAL=$((FAIL_TOTAL + 1)); FAIL_NAMES+=("$name")
  fi
}

echo "=== Lean 4 (formal/lean4) ==="

# --- lean-guard-build: `lake build` type-checks every #guard in the
# tree; the guard/module counts are read from the tree at run time,
# never cached.
if [ -d "$REPO_ROOT/formal/lean4" ]; then
  GUARD_COUNT=$(grep -rhoE '#guard' "$REPO_ROOT/formal/lean4" --include='*.lean' 2>/dev/null | grep -v '/\.lake/' | wc -l | tr -d ' ')
  GUARD_MODULES=$(grep -rlE '#guard' "$REPO_ROOT/formal/lean4" --include='*.lean' 2>/dev/null | grep -v '/\.lake/' | wc -l | tr -d ' ')
  if [ "$LIST_ONLY" -eq 0 ]; then
    echo "internal-tests: lean-guard-build checks ${GUARD_COUNT} #guard declaration(s) across ${GUARD_MODULES} module(s) (counted from the tree at run time)"
  fi
  run_suite "lean-guard-build" "$FULL_BUDGET" env -C "$REPO_ROOT/formal/lean4" lake build

  NATIVE_SMOKE="$REPO_ROOT/formal/lean4/Wasm/native-smoke.sh"
  [ -f "$NATIVE_SMOKE" ] && run_suite "lean-wasm-native-smoke" "$FULL_BUDGET" bash "$NATIVE_SMOKE"

  CLI_SMOKE="$REPO_ROOT/formal/lean4/Wasm/cli-smoke.sh"
  [ -f "$CLI_SMOKE" ] && run_suite "lean-wasm-cli-smoke" "$FULL_BUDGET" bash "$CLI_SMOKE"

  # lean_exe probes: every `lean_exe «name»` / `lean_exe name` target in
  # the lakefile, minus the block-storage CLI tools (exercised by the
  # blockengine-*-smoke.sh scripts below, and taking positional args,
  # not zero-arg probes) and the two ABI entry points already covered
  # by native/cli-smoke above.
  LAKEFILE="$REPO_ROOT/formal/lean4/lakefile.lean"
  if [ -f "$LAKEFILE" ]; then
    while read -r exe; do
      case "$exe" in
        l4block-*|l4wasm-cli|l4factoidal) continue ;;
      esac
      bin="$REPO_ROOT/formal/lean4/.lake/build/bin/$exe"
      if [ -x "$bin" ]; then
        run_probe "lean-probe-$exe" "$FULL_BUDGET" "$bin"
      else
        skip_suite "lean-probe-$exe" "not built (bin/$exe missing; run lake build first)"
      fi
    done < <(grep -oE 'lean_exe «[^»]+»|lean_exe [A-Za-z0-9_-]+' "$LAKEFILE" \
      | sed -E 's/lean_exe «([^»]+)»/\1/; s/lean_exe //')
  fi
fi

echo "=== Node (hub + npm) ==="
if command -v node >/dev/null 2>&1; then
  if compgen -G "$REPO_ROOT/tests/hub/*.mjs" > /dev/null; then
    run_suite "node-hub-tests" "$FULL_BUDGET" node --test "$REPO_ROOT"/tests/hub/*.mjs
  else
    skip_suite "node-hub-tests" "no tests/hub/*.mjs in this checkout"
  fi
  if compgen -G "$REPO_ROOT/npm/factoidal/test/*.test.js" > /dev/null; then
    run_suite "node-npm-tests" "$FULL_BUDGET" node --test "$REPO_ROOT"/npm/factoidal/test/*.test.js
  else
    skip_suite "node-npm-tests" "no npm/factoidal/test/*.test.js in this checkout"
  fi
else
  skip_suite "node-hub-tests" "node not on PATH"
  skip_suite "node-npm-tests" "node not on PATH"
fi

echo "=== Block engine (tools/blockengine-*-smoke.sh) ==="
PG_UP=0
if command -v psql >/dev/null 2>&1 && psql -h 127.0.0.1 -tAc 'select 1' >/dev/null 2>&1; then
  PG_UP=1
fi
if compgen -G "$REPO_ROOT/tools/blockengine-*-smoke.sh" > /dev/null; then
  for f in "$REPO_ROOT"/tools/blockengine-*-smoke.sh; do
    name="$(basename "$f" .sh)"
    if grep -q 'psql' "$f" 2>/dev/null; then
      if [ "$PG_UP" -eq 1 ]; then
        run_suite "$name" "$FULL_BUDGET" bash "$f"
      else
        skip_suite "$name" "PostgreSQL not reachable on 127.0.0.1 in this environment"
      fi
    else
      run_suite "$name" "$FULL_BUDGET" bash "$f"
    fi
  done
else
  skip_suite "blockengine-smoke" "no tools/blockengine-*-smoke.sh in this checkout"
fi

CENSUS="$REPO_ROOT/tools/w3c-persisted-census.sh"
[ -f "$CENSUS" ] && run_suite "w3c-persisted-census" "$FULL_BUDGET" bash "$CENSUS"

PODMAN_SMOKE="$REPO_ROOT/tools/podman-fly-smoke.sh"
if [ -f "$PODMAN_SMOKE" ]; then
  if command -v podman >/dev/null 2>&1 && podman info >/dev/null 2>&1; then
    run_suite "podman-fly-smoke" "$FULL_BUDGET" sh "$PODMAN_SMOKE"
  else
    skip_suite "podman-fly-smoke" "podman machine not running in this environment"
  fi
fi

echo "=== F* internal suite registry (.github/test-suites/*.yaml, spec: internal) ==="
DISPATCH="$REPO_ROOT/tools/dispatch_test_suites.sh"
ALL_YAML_RUNNERS_FILE=""
if [ -x "$DISPATCH" ]; then
  ALL_YAML_RUNNERS_FILE=$(mktemp 2>/dev/null || echo "$LOG_DIR/_all_runners.txt")
  grep -h '^runner:' "$REPO_ROOT"/.github/test-suites/*.yaml 2>/dev/null \
    | sed -E 's/^runner:[[:space:]]*"?//; s/"?[[:space:]]*$//' > "$ALL_YAML_RUNNERS_FILE"
  while read -r suite; do
    spec=$("$DISPATCH" --field "$suite" spec 2>/dev/null || echo "")
    [ "$spec" = "internal" ] || continue
    runner=$("$DISPATCH" --field "$suite" runner 2>/dev/null || echo "")
    [ -n "$runner" ] || continue
    mapfile -t rargs < <("$DISPATCH" --list-field "$suite" runner_args 2>/dev/null)
    if [ -x "$REPO_ROOT/$runner" ] || [ -f "$REPO_ROOT/$runner" ]; then
      run_suite "fstar-internal-$suite" "$FULL_BUDGET" bash "$REPO_ROOT/$runner" "${rargs[@]}"
    else
      skip_suite "fstar-internal-$suite" "registered runner $runner not found in this checkout"
    fi
  done < <("$DISPATCH" --list 2>/dev/null)
else
  skip_suite "fstar-internal-yaml-registry" "tools/dispatch_test_suites.sh missing or not executable"
fi

echo "=== Orphaned tests/*/run.sh (not the runner: of any .github/test-suites/*.yaml manifest) ==="
if [ -n "$ALL_YAML_RUNNERS_FILE" ] && compgen -G "$REPO_ROOT/tests/*/run.sh" > /dev/null; then
  for f in "$REPO_ROOT"/tests/*/run.sh; do
    rel="tests/$(basename "$(dirname "$f")")/run.sh"
    if grep -qxF "$rel" "$ALL_YAML_RUNNERS_FILE"; then
      continue  # covered by its own W3C/OGC-spec manifest already
    fi
    name="tests-$(basename "$(dirname "$f")")"
    run_suite "$name" "$FULL_BUDGET" bash "$f"
  done
fi

echo "=== Orphaned tests/local/*.sh (not the runner: of any manifest) ==="
if [ -n "$ALL_YAML_RUNNERS_FILE" ] && compgen -G "$REPO_ROOT/tests/local/*.sh" > /dev/null; then
  UNREG_COUNT=0
  for f in "$REPO_ROOT"/tests/local/*.sh; do
    rel="tests/local/$(basename "$f")"
    grep -qxF "$rel" "$ALL_YAML_RUNNERS_FILE" && continue
    UNREG_COUNT=$((UNREG_COUNT + 1))
    run_suite "tests-local-$(basename "$f" .sh)" "$FULL_BUDGET" bash "$f"
  done
fi
[ -n "$ALL_YAML_RUNNERS_FILE" ] && [ -f "$ALL_YAML_RUNNERS_FILE" ] && rm -f "$ALL_YAML_RUNNERS_FILE"

echo "=== tests/web-demos (headless-browser smokes) ==="
if [ -d "$REPO_ROOT/node_modules" ] && compgen -G "$REPO_ROOT/tests/web-demos/*.sh" > /dev/null; then
  for f in "$REPO_ROOT"/tests/web-demos/*.sh; do
    run_suite "web-demos-$(basename "$f" .sh)" "$FULL_BUDGET" bash "$f"
  done
elif compgen -G "$REPO_ROOT/tests/web-demos/*.sh" > /dev/null; then
  for f in "$REPO_ROOT"/tests/web-demos/*.sh; do
    skip_suite "web-demos-$(basename "$f" .sh)" "repo-root node_modules/ (Playwright) not installed in this environment"
  done
fi

echo "=== tests/beyond-w3c (demo-query parity across runtimes) ==="
BEYOND_PARITY="$REPO_ROOT/tests/beyond-w3c/bin/run-parity.py"
BEYOND_MANIFEST="$REPO_ROOT/tests/beyond-w3c/fixtures/index.json"
if command -v python3 >/dev/null 2>&1 && [ -f "$BEYOND_PARITY" ] && [ -f "$BEYOND_MANIFEST" ]; then
  run_suite "beyond-w3c-parity-native" "$FULL_BUDGET" python3 "$BEYOND_PARITY" \
    --manifest "$BEYOND_MANIFEST" --runners native --output "$LOG_DIR/beyond-w3c-parity-native.json"
else
  skip_suite "beyond-w3c-parity-native" "python3 or tests/beyond-w3c/bin/run-parity.py not available"
fi

if [ "$LIST_ONLY" -eq 1 ]; then
  exit 0
fi

TOTAL=$((PASS_TOTAL + FAIL_TOTAL + SKIP_TOTAL))
echo
if [ "$SUITE_COUNT" -eq 0 ] || [ "$TOTAL" -eq 0 ]; then
  echo "internal-tests: ERROR — derived suite list was empty; nothing ran" >&2
  exit 1
fi
echo "internal-tests TOTAL: ${PASS_TOTAL} pass, ${FAIL_TOTAL} fail, ${SKIP_TOTAL} skip (out of ${TOTAL})"
if [ "$FAIL_TOTAL" -gt 0 ]; then
  echo "internal-tests: failing suites: ${FAIL_NAMES[*]}"
  exit 1
fi
exit 0
