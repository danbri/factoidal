#!/bin/bash
# Run only the test suites a change actually touches (build-speed
# item 5). Wraps tools/dispatch_test_suites.sh's manifest-driven diff
# with actual local execution of each affected suite's runner, so a
# developer doesn't have to run the full ~25-minute W3C battery for
# every landing.
#
# Usage:
#   tools/affected-tests.sh                 # base=merge-base(origin/claude/main, HEAD)
#                                            # head=working tree (incl. uncommitted changes)
#   tools/affected-tests.sh <base>          # explicit base, head=working tree
#   tools/affected-tests.sh <base> <head>   # explicit base and head (committed refs only)
#   tools/affected-tests.sh --only <suite>  # bypass diff detection, force-run one
#                                            # named suite (see .github/test-suites/
#                                            # for names) — for ad-hoc single-suite runs
#
# Output: the computed plan (which paths triggered which suites), then
# per-suite pass/fail summaries, then a recap. Exits non-zero if any
# affected suite reported a failure (skips don't count as failure).
#
# This is a FAST LOCAL SIGNAL, not a substitute for the full battery.
# Nightly CI (.github/workflows/w3c-tests.yml) and any release-grade
# / multi-package landing are still gated by the full W3C run
# (./w3c-tests.sh or formal/fstar/generate-report.sh) — see the
# reminder printed at the end of every run.

set -uo pipefail  # deliberately not -e: one suite failing must not stop the rest

ROOT="$(git -C "$(dirname "${BASH_SOURCE[0]}")" rev-parse --show-toplevel 2>/dev/null || pwd)"
DISPATCH="$ROOT/tools/dispatch_test_suites.sh"
SUITES_DIR="$ROOT/.github/test-suites"
RUN_TIMEOUT=600  # anti-pattern #17: cap ad-hoc runs at 10 minutes

ONLY_SUITE=""
BASE=""
HEAD=""

if [ "${1:-}" = "--only" ]; then
  ONLY_SUITE="${2:-}"
  if [ -z "$ONLY_SUITE" ]; then
    echo "Usage: tools/affected-tests.sh --only <suite-name>" >&2
    exit 2
  fi
else
  BASE="${1:-}"
  HEAD="${2:-}"

  if [ -z "$BASE" ]; then
    BASE="$(git -C "$ROOT" merge-base origin/claude/main HEAD 2>/dev/null || true)"
    if [ -z "$BASE" ]; then
      BASE="$(git -C "$ROOT" merge-base main HEAD 2>/dev/null || true)"
    fi
    if [ -z "$BASE" ]; then
      echo "affected-tests.sh: could not compute a default base ref (no" >&2
      echo "  origin/claude/main or main reachable). Pass one explicitly:" >&2
      echo "  tools/affected-tests.sh <base-ref> [<head-ref>]" >&2
      exit 2
    fi
  fi
fi

# --- extract_counts <line> -> sets PASS_N, FAIL_N (best-effort) ------------
# Tries the unambiguous "pass=N" / "fail=N" key=value form FIRST for
# each of PASS_N/FAIL_N independently, falling back to "N pass" / "N
# fail" only when that form is absent. This order matters: on a line
# like "pass=4 fail=0", the digit immediately before the word "fail"
# is actually the PASS count ("...4 fail=0"), so trying the "N fail"
# fallback before the "fail=N" form would misattribute it.
extract_counts() {
  local line="$1"
  PASS_N="$(printf '%s' "$line" | grep -oE 'pass[:=][[:space:]]*[0-9]+' | grep -oE '[0-9]+' | head -1)"
  FAIL_N="$(printf '%s' "$line" | grep -oE 'fail[:=][[:space:]]*[0-9]+' | grep -oE '[0-9]+' | head -1)"
  [ -z "$PASS_N" ] && PASS_N="$(printf '%s' "$line" | grep -oE '[0-9]+[[:space:]]*pass' | grep -oE '[0-9]+' | head -1)"
  [ -z "$FAIL_N" ] && FAIL_N="$(printf '%s' "$line" | grep -oE '[0-9]+[[:space:]]*fail' | grep -oE '[0-9]+' | head -1)"
  PASS_N="${PASS_N:-0}"
  FAIL_N="${FAIL_N:-0}"
}

# --- summarize_output <captured-output> <exit-code> -> prints one line ----
# Tries, in order: "N pass, M fail" (W3C runners + most local scripts),
# "pass=N fail=M" (some local scripts), counting bare PASS/FAIL lines,
# then falls back to exit-code-only. Always returns a labelled line
# with numerator/denominator context (anti-pattern #25).
#
# NOTE: this is invoked via command substitution ("$(summarize_output
# ...)"), which runs in a subshell — any variables it sets do NOT
# propagate back to the caller. So it only prints; callers must run
# extract_counts on the RETURNED line (not on raw runner output) to
# get PASS_N/FAIL_N in their own shell.
summarize_output() {
  local output="$1" rc="$2" line

  line="$(printf '%s\n' "$output" | grep -E '[0-9]+[[:space:]]*pass,?[[:space:]]*[0-9]+[[:space:]]*fail' | tail -1)"
  if [ -n "$line" ]; then
    printf '%s\n' "$line" | sed 's/^[[:space:]]*//'
    return
  fi

  line="$(printf '%s\n' "$output" | grep -E 'pass=[0-9]+.*fail=[0-9]+' | tail -1)"
  if [ -n "$line" ]; then
    printf '%s\n' "$line" | sed 's/^[[:space:]]*//'
    return
  fi

  local pass_n fail_n
  pass_n="$(printf '%s\n' "$output" | grep -c '^PASS ')"
  fail_n="$(printf '%s\n' "$output" | grep -c '^FAIL ')"
  if [ "$pass_n" -gt 0 ] || [ "$fail_n" -gt 0 ]; then
    echo "${pass_n} pass, ${fail_n} fail (counted from PASS/FAIL lines; runner prints no summary line)"
    return
  fi

  if [ "$rc" -eq 0 ]; then
    echo "1 pass, 0 fail (exit 0, no per-test summary found — treating as a single pass/fail unit)"
  else
    echo "0 pass, 1 fail (exit ${rc}, no per-test summary found — treating as a single pass/fail unit)"
  fi
}

echo "== tools/affected-tests.sh =="

if [ -n "$ONLY_SUITE" ]; then
  echo "mode: forced single-suite run (--only), bypassing diff detection"
  SUITES=("$ONLY_SUITE")
else
  echo "base: ${BASE}"
  echo "head: ${HEAD:-<working tree, including uncommitted changes>}"
  echo

  DIFF_ARGS=(--diff "$BASE")
  [ -n "$HEAD" ] && DIFF_ARGS+=("$HEAD")

  echo "-- plan (why each suite fired) --"
  "$DISPATCH" "${DIFF_ARGS[@]}" --verbose 2>&1 | sed 's/^/  /'
  echo

  mapfile -t SUITES < <("$DISPATCH" "${DIFF_ARGS[@]}")

  if [ "${#SUITES[@]}" -eq 0 ]; then
    echo "No suites affected by this diff. Nothing to run."
    echo
    echo "REMINDER: the FULL W3C battery still gates release-grade landings"
    echo "(nightly CI at .github/workflows/w3c-tests.yml, plus any"
    echo "multi-package landing) — this tool is a fast local signal, not a"
    echo "substitute. Run ./w3c-tests.sh before those."
    exit 0
  fi
fi

echo "Plan: ${#SUITES[@]} suite(s) affected:"
printf '  - %s\n' "${SUITES[@]}"
echo

declare -a RECAP_LINES=()
GRAND_PASS=0
GRAND_FAIL=0
ANY_FAIL=0

for suite in "${SUITES[@]}"; do
  manifest="$SUITES_DIR/${suite}.yaml"
  if [ ! -f "$manifest" ]; then
    echo "=== ${suite} ==="
    echo "SKIP ${suite}: no manifest file found at ${manifest#"$ROOT"/}"
    echo
    RECAP_LINES+=("${suite}: SKIP (manifest missing)")
    continue
  fi

  suite_name="$("$DISPATCH" --field "$suite" name)"
  runner_rel="$("$DISPATCH" --field "$suite" runner)"
  runner_abs="${ROOT}/${runner_rel}"
  mapfile -t runner_args < <("$DISPATCH" --list-field "$suite" runner_args)

  echo "=== ${suite} (${suite_name:-$suite}) ==="

  if [ -z "$runner_rel" ] || [ ! -x "$runner_abs" ]; then
    echo "SKIP ${suite}: runner binary/script missing or not executable:"
    echo "  ${runner_rel:-<no runner field>}"
    echo "  (build it — see the build-and-test skill — or ignore if this"
    echo "   suite isn't wired up in this checkout yet)"
    echo
    RECAP_LINES+=("${suite}: SKIP (runner missing: ${runner_rel:-?})")
    continue
  fi

  RUN_RC=0
  RUN_OUT="$(cd "$ROOT" && timeout "$RUN_TIMEOUT" "$runner_abs" "${runner_args[@]}" 2>&1)" || RUN_RC=$?

  if [ "$RUN_RC" -eq 124 ]; then
    echo "FAIL ${suite}: timed out after ${RUN_TIMEOUT}s"
    echo
    RECAP_LINES+=("${suite}: TIMEOUT after ${RUN_TIMEOUT}s")
    ANY_FAIL=1
    continue
  fi

  summary="$(summarize_output "$RUN_OUT" "$RUN_RC")"
  echo "${suite}: ${summary}"
  echo

  RECAP_LINES+=("${suite}: ${summary}")
  extract_counts "$summary"
  GRAND_PASS=$((GRAND_PASS + PASS_N))
  GRAND_FAIL=$((GRAND_FAIL + FAIL_N))
  [ "$FAIL_N" -gt 0 ] && ANY_FAIL=1
done

echo "===================================================="
echo "RECAP (${#SUITES[@]} suite(s) affected)"
printf '  %s\n' "${RECAP_LINES[@]}"
echo
echo "Grand total across run suites: ${GRAND_PASS} pass, ${GRAND_FAIL} fail"
echo "(best-effort tally; see per-suite lines above for exact labels —"
echo " anti-pattern #25: never quote this total without the per-suite"
echo " breakdown alongside it)."
echo
echo "REMINDER: this ran ONLY the suites affected by the diff. The FULL"
echo "W3C battery still gates release-grade landings — nightly CI"
echo "(.github/workflows/w3c-tests.yml) and any multi-package landing"
echo "must still run the complete suite (./w3c-tests.sh) before those."

if [ "$ANY_FAIL" -eq 1 ]; then
  exit 1
fi
exit 0
