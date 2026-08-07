#!/usr/bin/env bash
# Rerunnable entry point for the RDFS / OWL-RL closure benchmark.
#
# Phase 0 of docs/designissues/2026-07-31-rdfs-performance-scalability.md:
# until 2026-07-31 this repository had no entailment or closure benchmark
# at all, which is why an O(n^3) closure was first noticed as a W3C OWL
# conformance failure rather than as a slowdown.
#
# What this wrapper does that tools/bench_closure.py does not:
#   1. Refuses to run when the committed binary is missing, with a
#      message that says which one.
#   2. Tees everything to .claude-runs/ with a UTC timestamp
#      (anti-patterns #16 no truncation, #19 logged long runs).
#
# Usage:
#   tools/bench-closure.sh                     # measure, print, write JSON
#   tools/bench-closure.sh --check             # gate against the baseline
#   tools/bench-closure.sh --update-baseline   # freeze a new baseline
#   tools/bench-closure.sh --quick             # smaller sweep, 1 run each
#   tools/bench-closure.sh --binary /path/to/factoidal    # control experiment
#
# Any extra arguments are forwarded verbatim to tools/bench_closure.py;
# run `tools/bench_closure.py --help` for the full list.
set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "${ROOT}"

case "$(uname -s)-$(uname -m)" in
  Linux-x86_64) PLATFORM="linux-x86_64" ;;
  Darwin-arm64) PLATFORM="darwin-arm64" ;;
  *)
    echo "Unsupported platform $(uname -s)-$(uname -m); this bench targets the" \
         "committed bin/linux-x86_64 (or darwin-arm64) binaries only." >&2
    exit 2
    ;;
esac

if [[ ! -x "${ROOT}/bin/${PLATFORM}/factoidal" && "$*" != *--binary* ]]; then
  echo "::error::committed binary missing or not executable:" \
       "bin/${PLATFORM}/factoidal" >&2
  echo "This bench runs against committed binaries only -- no toolchain build." >&2
  exit 2
fi

RUN_LOG_DIR="${ROOT}/.claude-runs"
mkdir -p "${RUN_LOG_DIR}"
TS="$(date -u +%Y%m%dT%H%M%SZ)"
LOG_FILE="${RUN_LOG_DIR}/bench-closure-${TS}.log"

echo "[bench-closure.sh] logging to ${LOG_FILE}"
python3 "${ROOT}/tools/bench_closure.py" "$@" 2>&1 | tee "${LOG_FILE}"
RC=${PIPESTATUS[0]}
echo "[bench-closure.sh] exit ${RC}; full log at ${LOG_FILE}"
exit "${RC}"
