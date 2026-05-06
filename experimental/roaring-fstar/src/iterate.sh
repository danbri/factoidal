#!/bin/bash
# Iterative verify-and-show-errors loop for the roaring-fstar Phase A sources.
# Runs fstar.exe on each module in dependency order; on first failure prints
# the error and stops. Designed to be run repeatedly during proof iteration.

set -uo pipefail

# Activate the fstar opam switch.
export OPAMROOT=$HOME/.opam
eval "$(opam env --switch=fstar --set-switch 2>/dev/null)"

if ! command -v fstar.exe >/dev/null; then
  echo "fstar.exe not on PATH after opam env activation. Aborting." >&2
  exit 1
fi

if ! z3 --version | grep -q 4.13.3; then
  echo "z3 is not 4.13.3 (currently: $(z3 --version)). Aborting." >&2
  exit 1
fi

cd "$(dirname "$0")"

MODULES=(Spec Container.Array Test)

for m in "${MODULES[@]}"; do
  echo "=========================="
  echo "Verifying: $m"
  echo "=========================="
  if ! fstar.exe "${m}.fst"; then
    echo
    echo "FAILED on $m. Stop." >&2
    exit 1
  fi
  echo "[ok] $m"
done

echo
echo "All Phase A modules verified."
