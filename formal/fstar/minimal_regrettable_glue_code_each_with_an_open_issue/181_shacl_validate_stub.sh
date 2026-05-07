#!/bin/bash
# Issue #181: realise SHACL.Validation.validate /
# parse_shape_from_graph / eval_sparql_target_select stubs.
# https://github.com/danbri/factoidal/issues/181
#
# Phase 1 SKELETON patch. SHACL.Validation.fst declares three
# `assume val` entry points whose F* extraction emits
# `failwith "Not yet implemented: ..."` bodies. This patch is a
# no-op idempotent placeholder: the SHACL skeleton is committed
# without a runtime realisation because Phase 1 is AST + types
# only — there is no consumer yet that calls `validate`. Phase 2
# will:
#   - move `parse_shape_from_graph` into pure F* (no patch needed)
#   - move `validate` into a thin orchestrator over pure F*
#     constraint evaluators (no patch needed for the orchestrator,
#     but the SPARQL-target dispatch in `eval_sparql_target_select`
#     stays here as a rule-#11(c) host call-out into the extracted
#     SPARQL evaluator).
#
# Why ship a no-op? CLAUDE.md rule #3: every `assume val` MUST have
# a corresponding patch file with an open issue. This file
# discharges that bookkeeping invariant for the Phase 1 skeleton
# and keeps the patch inventory honest. When Phase 2 lands, this
# patch shrinks to wire only `eval_sparql_target_select` and
# retires the other two entries.
#
# Recovery plan reference:
#   docs/designissues/2026-05-07-query-planning-fstar-recovery.md
#   (sister track: SHACL Core)
#
# Trust boundary: `eval_sparql_target_select` calls into the
# extracted SPARQL evaluator (rule-#11(c) host call-out). The
# pure-AST helpers in SHACL.Validation are total F* and require
# no patch.

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

FILE="$OUTDIR/SHACL_Validation.ml"
if [[ ! -f "$FILE" ]]; then
  echo "  WARN: $FILE not found; skipping 181_shacl_validate_stub patch."
  echo "         (F* extract may not have produced SHACL.Validation yet.)"
  exit 0
fi

# Idempotency: marker comment we inject below distinguishes a
# patched file from the raw extracted output.
if grep -q 'SHACL phase-1 stub acknowledgement' "$FILE"; then
  echo "  [181_shacl_validate_stub] already applied; skipping."
  exit 0
fi

echo "  Patching $FILE (Phase 1 SHACL stub acknowledgement)..."

python3 - "$FILE" <<'PYEOF'
import sys

path = sys.argv[1]
with open(path, "r") as f:
    content = f.read()

# Inject a header comment near the top of the file marking the
# phase-1 stub so future runs detect the patch via the marker
# above, and so anyone reading the extracted .ml sees the issue
# pointer without having to grep the F* source.
marker = (
    "(* SHACL phase-1 stub acknowledgement -- issue #181.\n"
    "   `validate`, `parse_shape_from_graph`, and\n"
    "   `eval_sparql_target_select` are extracted as `failwith`\n"
    "   stubs by design. Phase 2 replaces the first two with pure\n"
    "   F-star and rewires this patch to realise only the SPARQL\n"
    "   target call-out. See\n"
    "     formal/fstar/minimal_regrettable_glue_code_each_with_an_open_issue/\n"
    "     181_shacl_validate_stub.sh\n"
    "   for the migration plan. *)\n"
)

# Insert the marker right after the `open Prims` preamble so it
# appears at the head of the module without disturbing extraction
# offsets.
needle = "open Prims\n"
if needle not in content:
    sys.stderr.write(
        "  ERROR: 181_shacl_validate_stub: did not find `open Prims` in "
        + path
        + "; extraction shape changed?\n"
    )
    sys.exit(1)

content = content.replace(needle, needle + marker, 1)

with open(path, "w") as f:
    f.write(content)
PYEOF

echo "  [181_shacl_validate_stub] applied: phase-1 marker injected."
