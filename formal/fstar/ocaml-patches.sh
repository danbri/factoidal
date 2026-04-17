#!/bin/bash
# Master script: applies all patches from
# minimal_regrettable_glue_code_each_with_an_open_issue/
#
# Each patch is a self-contained script named <issue>_<description>.sh
# with a corresponding open GitHub issue. See the README.md in that
# directory for the full inventory and rules.
#
# Applied automatically by build-ocaml.sh after F* extraction.
#
# This file must NEVER contain RDF/SPARQL semantic logic.
# See CLAUDE.md iron rule #10 and anti-pattern #15.

set -euo pipefail

OUTDIR="$1"

# Backward compatibility: if $1 is a .ml file, use its directory
if [[ -f "$OUTDIR" && "$OUTDIR" == *.ml ]]; then
  OUTDIR="$(dirname "$OUTDIR")"
fi

if [[ ! -d "$OUTDIR" ]]; then
  echo "Error: $OUTDIR is not a directory" >&2
  exit 1
fi

# Find the patch directory (relative to this script)
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PATCH_DIR="$SCRIPT_DIR/minimal_regrettable_glue_code_each_with_an_open_issue"
EXPERIMENTAL_DIR="$SCRIPT_DIR/experimental_ocaml_glue"

if [[ ! -d "$PATCH_DIR" ]]; then
  echo "Error: patch directory not found: $PATCH_DIR" >&2
  exit 1
fi

# Apply each patch in sorted order (by issue number)
PATCH_COUNT=0
PATCH_ERRORS=0
for patch in "$PATCH_DIR"/*.sh; do
  [[ -f "$patch" ]] || continue
  patch_name="$(basename "$patch")"
  PATCH_RC=0
  bash "$patch" "$OUTDIR" || PATCH_RC=$?
  if [[ $PATCH_RC -ne 0 ]]; then
    echo "  WARNING: $patch_name failed (exit $PATCH_RC)" >&2
    PATCH_ERRORS=$((PATCH_ERRORS + 1))
  fi
  PATCH_COUNT=$((PATCH_COUNT + 1))
done

# Apply experimental runtime glue scripts in sorted order.
if [[ -d "$EXPERIMENTAL_DIR" ]]; then
  for patch in "$EXPERIMENTAL_DIR"/*.sh; do
    [[ -f "$patch" ]] || continue
    patch_name="$(basename "$patch")"
    PATCH_RC=0
    bash "$patch" "$OUTDIR" || PATCH_RC=$?
    if [[ $PATCH_RC -ne 0 ]]; then
      echo "  WARNING: experimental $patch_name failed (exit $PATCH_RC)" >&2
      PATCH_ERRORS=$((PATCH_ERRORS + 1))
    fi
    PATCH_COUNT=$((PATCH_COUNT + 1))
  done
fi

echo "  All patches applied successfully."
if [[ $PATCH_ERRORS -gt 0 ]]; then
  echo "  WARNING: $PATCH_ERRORS of $PATCH_COUNT patches had errors" >&2
fi
