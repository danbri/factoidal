#!/bin/bash
# Regenerate the machine-derived per-module assurance inventory
# (issue #315, sub-issue of the #313 claim-discipline epic).
#
# Writes three artifacts, all generated, none hand-written:
#
#   docs/web/conformance/assurance-inventory.md    the site page, rendered
#                                                  by Eleventy next to the
#                                                  other conformance pages
#   docs/test-results/assurance-inventory.json     machine-readable, published
#                                                  alongside the dashboard
#                                                  (docs/test-results/ is
#                                                  passthrough-copied to Pages)
#   docs/test-results/assurance-inventory.html     standalone scrollable table
#
# No toolchain needed: this reads source, the committed extracted OCaml, the
# build module list, the per-suite manifests and the committed suite logs.
# It never runs F*, never runs a test suite, and never writes outside the
# three paths above.
#
# Usage:
#   tools/assurance-inventory.sh              # regenerate all three
#   tools/assurance-inventory.sh --check      # also fail if any active
#                                             # admission / lax region exists
#   tools/assurance-inventory.sh --summary    # print totals, write nothing

set -euo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(git -C "$HERE" rev-parse --show-toplevel 2>/dev/null || true)"
[ -n "$ROOT" ] || ROOT="$(dirname "$HERE")"
PY="$ROOT/tools/assurance_inventory.py"

if [ "${1:-}" = "--summary" ]; then
  exec python3 "$PY" --repo-root "$ROOT" --summary
fi

CHECK=()
if [ "${1:-}" = "--check" ]; then
  CHECK=(--check)
fi

MD="$ROOT/docs/web/conformance/assurance-inventory.md"
JSON="$ROOT/docs/test-results/assurance-inventory.json"
HTML="$ROOT/docs/test-results/assurance-inventory.html"

RC=0
python3 "$PY" \
  --repo-root "$ROOT" \
  --markdown "$MD" --eleventy \
  --json "$JSON" \
  --html "$HTML" \
  --summary "${CHECK[@]+"${CHECK[@]}"}" || RC=$?

echo
echo "wrote:"
echo "  ${MD#"$ROOT"/}"
echo "  ${JSON#"$ROOT"/}"
echo "  ${HTML#"$ROOT"/}"

exit "$RC"
