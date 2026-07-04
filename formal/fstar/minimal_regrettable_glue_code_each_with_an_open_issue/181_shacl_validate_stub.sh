#!/bin/bash
# Issue #181: realise SHACL.Validation.eval_sparql_target_select stub.
# https://github.com/danbri/factoidal/issues/181
#
# UPDATED for Phase 2 / slice 1 (SHACL Core validator, 2026-07-04):
# `validate` and `parse_shape_from_graph` are now real F* (Tot,
# wrapped in a thin ML entry point) — see SHACL.Validation.fst
# sections 11a-11j. Their extracted OCaml is real code, not a
# `failwith` stub, so this patch no longer touches them.
#
# The ONE remaining `assume val` is `eval_sparql_target_select`
# (sh:sparql / sh:select target + constraint dispatch into the
# SPARQL evaluator — a genuine rule-#11(c) host call-out, not a
# temporary gap). Slice 1 never calls it: T_Sparql targets and
# CC_Sparql constraints both evaluate to "no result" in pure F*, so
# the extracted `failwith "Not yet implemented: ...
# eval_sparql_target_select"` body is unreachable in the current
# corpus. This patch stays a no-op marker-injection (idempotent) so
# CLAUDE.md rule #3's patch-file requirement is discharged without
# pretending there's a real realisation yet. Wiring an actual SPARQL
# dispatch is the natural Phase 3 follow-up once a SPARQL-target test
# in the vendored suite actually needs it.
#
# Recovery plan reference:
#   docs/designissues/2026-05-07-query-planning-fstar-recovery.md
#   (sister track: SHACL Core)
#
# Trust boundary: `eval_sparql_target_select` calls into the
# extracted SPARQL evaluator (rule-#11(c) host call-out). Every other
# function in SHACL.Validation is total F* and requires no patch.

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
if grep -q 'SHACL sh:sparql dispatch acknowledgement' "$FILE"; then
  echo "  [181_shacl_validate_stub] already applied; skipping."
  exit 0
fi

echo "  Patching $FILE (SHACL sh:sparql dispatch acknowledgement)..."

python3 - "$FILE" <<'PYEOF'
import sys

path = sys.argv[1]
with open(path, "r") as f:
    content = f.read()

# Inject a header comment near the top of the file marking the
# remaining stub so future runs detect the patch via the marker
# above, and so anyone reading the extracted .ml sees the issue
# pointer without having to grep the F* source.
marker = (
    "(* SHACL sh:sparql dispatch acknowledgement -- issue #181.\n"
    "   `validate` and `parse_shape_from_graph` are real F-star\n"
    "   (Phase 2 / slice 1 landed 2026-07-04) -- only\n"
    "   `eval_sparql_target_select` is still extracted as a\n"
    "   `failwith` stub, and it is unreachable this slice (T_Sparql\n"
    "   targets and CC_Sparql constraints both evaluate to \"no\n"
    "   result\" in pure F-star). See\n"
    "     formal/fstar/minimal_regrettable_glue_code_each_with_an_open_issue/\n"
    "     181_shacl_validate_stub.sh\n"
    "   for the wiring plan. *)\n"
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

echo "  [181_shacl_validate_stub] applied: sh:sparql dispatch marker injected."
