#!/bin/bash
# Issue #181: realise SHACL.Validation.eval_sparql_target_select stub.
# https://github.com/danbri/factoidal/issues/181
#
# UPDATED for Phase 3 (sh:sparql constraint dispatch, 2026-07-04):
# `validate`, `parse_shape_from_graph`, report serialization
# (`validation_report_to_graph`), AND the sh:sparql CONSTRAINT
# dispatch (CC_Sparql -> SPARQL11.Parser.parse_sparql +
# SPARQL11.Algebra.eval_select_query, both Tot) are all real F* —
# see SHACL.Validation.fst sections 11a-11k + 13. No OCaml glue
# realises any of them.
#
# The ONE remaining `assume val` is `eval_sparql_target_select`,
# which now covers ONLY the SPARQL-SELECT-based TARGET form
# (`sh:target [ a sh:SPARQLTarget ; sh:select ... ]` / T_Sparql — a
# shape's target set computed by a query, distinct from the sh:sparql
# CONSTRAINT form that Phase 3 implemented in pure F*). Nothing calls
# it: T_Sparql targets still evaluate to "no focus nodes" in
# eval_target, an honest FAIL against any test needing them. This
# patch stays a no-op marker-injection (idempotent) so CLAUDE.md rule
# #3's patch-file requirement is discharged without pretending
# there's a real realisation yet.
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
