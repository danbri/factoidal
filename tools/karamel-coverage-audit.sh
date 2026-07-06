#!/bin/bash
# KaRaMeL coverage audit — foreground entry point.
#
# For every formal/fstar/*.fst module, attempts F* --codegen krml then
# krml lowering to C, walking the dependency DAG bottom-up. Every module
# is tested for real; the DAG is used only to LABEL a failure as
# BLOCKED_SELF (all in-set deps lower clean) vs BLOCKED_TRANSITIVE (a
# dep in its closure is itself blocked). See the .py docstring for why
# an inferred-transitive shortcut was removed (measured false positive).
#
# Read-only w.r.t. the ocaml build: no .fst is edited, and all krml/.c
# scratch output lands under --scratch (default: mktemp -d), never in
# formal/fstar/krml-output or formal/fstar/c-output (the ocaml-build /
# karamel-c-build.sh pilot's own directories). This script DOES invoke
# fstar.exe --cache_checked_modules against the existing formal/fstar/
# *.fst.checked cache (read reuse, same as any other fstar.exe run on
# an unmodified tree; it does not force reverification or edit the
# .extract-state manifest build-ocaml.sh owns).
#
# Usage:
#   eval $(opam env --switch=fstar)   # F* on PATH (iron rule #12)
#   tools/karamel-coverage-audit.sh [--scratch DIR] [--jobs N]
#
# Output (written under --scratch unless overridden):
#   karamel-coverage.tsv   — one row per module: status, blocker
#                            category, first error, deps.
#   karamel-coverage-raw.log — full captured stdout/stderr per module,
#                            in the order modules were tested.
#
# Bounded: 120s timeout per fstar.exe --codegen krml call, 120s per
# krml lowering call (FSTAR_TIMEOUT_S / KRML_TIMEOUT_S in the .py — the
# two-stage split distinguishes an F* extraction blocker from a krml
# lowering blocker), so worst case per module is 240s. Measured full-tree
# run 2026-07-06 (warm .checked cache, 4 jobs): ~14 min.

set -euo pipefail
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
cd "$SCRIPT_DIR/../formal/fstar"

if ! command -v fstar.exe >/dev/null 2>&1; then
  echo "FATAL: fstar.exe not on PATH. Run: eval \$(opam env --switch=fstar)" >&2
  exit 127
fi
if ! command -v krml >/dev/null 2>&1; then
  echo "FATAL: krml not on PATH. See docs/designissues/2026-05-10-krml-install-notes.md" >&2
  exit 127
fi
if ! command -v python3 >/dev/null 2>&1; then
  echo "FATAL: python3 not on PATH." >&2
  exit 127
fi

SCRATCH=""
JOBS=""
while [[ $# -gt 0 ]]; do
  case "$1" in
    --scratch) SCRATCH="$2"; shift 2 ;;
    --jobs) JOBS="$2"; shift 2 ;;
    *) echo "unknown arg: $1" >&2; exit 2 ;;
  esac
done
if [[ -z "$SCRATCH" ]]; then
  SCRATCH="$(mktemp -d /tmp/karamel-coverage-audit.XXXXXX)"
fi
mkdir -p "$SCRATCH"
echo "Scratch dir: $SCRATCH" >&2

# Bounded wait on the extraction lock — never run alongside a live
# build-ocaml.sh (shared .checked cache; concurrent ad-hoc fstar.exe is
# unsafe per skills/fast-verify-extract).
for i in $(seq 1 60); do
  [[ ! -f .build-running ]] && break
  [[ "$i" == 60 ]] && { echo "FATAL: .build-running still present after 10 min." >&2; exit 75; }
  sleep 10
done

ARGS=(--fstar-dir . --scratch "$SCRATCH" \
      --out-tsv "$SCRATCH/karamel-coverage.tsv" \
      --out-log "$SCRATCH/karamel-coverage-raw.log")
[[ -n "$JOBS" ]] && ARGS+=(--jobs "$JOBS")

python3 "$SCRIPT_DIR/karamel-coverage-audit.py" "${ARGS[@]}"

echo "TSV:     $SCRATCH/karamel-coverage.tsv" >&2
echo "Raw log: $SCRATCH/karamel-coverage-raw.log" >&2
