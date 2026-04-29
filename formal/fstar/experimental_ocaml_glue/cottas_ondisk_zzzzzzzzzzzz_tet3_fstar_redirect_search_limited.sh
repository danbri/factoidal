#!/bin/bash
# Tet3 -> F* redirect, step 3: search_fast_limited's candidate gate.
# (issue #100, 2026-04-26, fstar-purity-unwind Phase 2.6).
#
# What this patch does:
#
#   Replaces the per-rg `could_p / could_s / could_o` gate inside
#   `search_fast_limited_inner` (aleph6-installed) so the presence-
#   bitmap test goes through the F*-extracted reader
#   `RDF_CottasStore_PresenceBitmap.rg_could_contain` instead of
#   Tet3's local string-keyed Hashtbls in
#   `Cottas_ondisk_lazy.{pred,subj,obj}_rg_could_contain`.
#
#   This is the third (and final) Tet3 -> F* call-site redirect.
#   The first two were `estimate_fast_inner` (commit c99dc31) and
#   `search_fast_inner` (commit ce922d7). Once this patch is in
#   place, ALL three OCaml call sites of Tet3's per-rg Hashtbls go
#   through the F* reader. Tet3's `ensure_*_loaded` Hashtbl
#   population becomes dead code and the Tet3 patch
#   (cottas_ondisk_zzzz_tet3_subj_obj_prune.sh) becomes a candidate
#   for deletion (issue #100 cleanup).
#
#   Helper module `Tet3_fstar_redirect` was installed by the FIRST
#   redirect patch (estimate). This patch only consumes that helper.
#
#   Shape (a) per fstar-purity-unwind.md: thin dispatch shim that
#   calls F*-extracted code (rule #11(c)). Identical pattern to the
#   prior two redirect patches.
#
# Sort order: cottas_ondisk_zzzzzzzzzzzz_* — twelve z's, one more
# than the search_fast_inner redirect (eleven z's). Runs strictly
# after both prior redirects.
#
# Idempotency: skip-if-marker pattern.

set -euo pipefail

OUTDIR="$1"

if [[ -f "$OUTDIR" && "$OUTDIR" == *.ml ]]; then
  OUTDIR="$(dirname "$OUTDIR")"
fi

FILE="$OUTDIR/RDF_CottasStore.ml"
if [[ ! -f "$FILE" ]]; then
  echo "  Warning: $FILE not found, skipping tet3-fstar-redirect-search-limited patch" >&2
  exit 0
fi

# Sanity: prerequisite redirects must have run.
if ! grep -q 'tet3_fstar_redirect: estimate helper installed' "$FILE"; then
  echo "  Warning: tet3-fstar-redirect-search-limited needs the estimate redirect's helper module;" >&2
  echo "  experimental_ocaml_glue/cottas_ondisk_zzzzzzzzzz_tet3_fstar_redirect_estimate.sh must run first." >&2
  exit 0
fi

if grep -q 'tet3_fstar_redirect_search_limited: search_fast_limited installed' "$FILE"; then
  echo "  Tet3 -> F* redirect (search_fast_limited) patch already present."
  exit 0
fi

python3 - "$FILE" <<'PYEOF'
import sys
from pathlib import Path

path = Path(sys.argv[1])
content = path.read_text()

# ----------------------------------------------------------------------
# Replace the candidate-gate block inside `search_fast_limited_inner`
# (aleph6-installed, with yod6 ensure_predicates_loaded prepended) so
# the per-rg presence test goes through the F* helper. The exact gate is:
#
#     while !rg < rg_count && !n_matches < limit do
#       let r = !rg in
#       let could_p = Cottas_ondisk_lazy.pred_rg_could_contain path r bound_p in
#       let could_s = Cottas_ondisk_lazy.subj_rg_could_contain path r bound_s in
#       let could_o = Cottas_ondisk_lazy.obj_rg_could_contain  path r bound_o in
#       if not (could_p && could_s && could_o) then begin
#         incr n_skipped;
#         ...
#       end else begin
#       (decode + walk row group)
#       ...
#
# We rewrite each `could_X` to: try F* first, fall back to Tet3 if F*
# returned None (companion absent). Identical semantics on corpora
# without companion files; on parliament (which has all 4 .presence
# files) the F* path is always taken and the Hashtbl path is dead.
#
# bound.cbqp_p / cbqp_s / cbqp_o (the raw nat ids) are in scope
# because `bound : Parser_BallyhooCOTTAS.cottas_bound_qp` is the
# function parameter.
# ----------------------------------------------------------------------

old_block = """    (try
      while !rg < rg_count && !n_matches < limit do
        let r = !rg in
        let could_p = Cottas_ondisk_lazy.pred_rg_could_contain path r bound_p in
        let could_s = Cottas_ondisk_lazy.subj_rg_could_contain path r bound_s in
        let could_o = Cottas_ondisk_lazy.obj_rg_could_contain  path r bound_o in
        if not (could_p && could_s && could_o) then begin
          incr n_skipped;
          if !n_skipped <= 3 || !n_skipped mod 5 = 0 then
            Printf.eprintf "[tet3-trace] search_fast_limited rg=%d skipped (could_p=%b could_s=%b could_o=%b)\\n%!"
              r could_p could_s could_o;
          incr rg
        end else begin"""

new_block = """    (* tet3_fstar_redirect_search_limited: search_fast_limited installed
       (issue #100, 2026-04-26). Per-rg gate routed through F*'s
       RDF_CottasStore_PresenceBitmap via the Tet3_fstar_redirect
       helper (installed by the estimate-redirect patch). Fall back
       to the existing Tet3 Hashtbl path only when could_via_fstar
       returns None (companion file absent). *)
    let n_via_fstar_lim = ref 0 in
    let n_via_hashtbl_lim = ref 0 in
    (try
      while !rg < rg_count && !n_matches < limit do
        let r = !rg in
        let could_via path_ col_idx bound_id bound_str fallback_get =
          match Tet3_fstar_redirect.could_via_fstar
                  path_ col_idx r bound_id with
          | FStar_Pervasives_Native.Some b ->
            incr n_via_fstar_lim; b
          | FStar_Pervasives_Native.None ->
            incr n_via_hashtbl_lim; fallback_get path_ r bound_str in
        let could_p = could_via path 1 bound.Parser_BallyhooCOTTAS.cbqp_p
          bound_p Cottas_ondisk_lazy.pred_rg_could_contain in
        let could_s = could_via path 0 bound.Parser_BallyhooCOTTAS.cbqp_s
          bound_s Cottas_ondisk_lazy.subj_rg_could_contain in
        let could_o = could_via path 2 bound.Parser_BallyhooCOTTAS.cbqp_o
          bound_o Cottas_ondisk_lazy.obj_rg_could_contain in
        if not (could_p && could_s && could_o) then begin
          incr n_skipped;
          if !n_skipped <= 3 || !n_skipped mod 5 = 0 then
            Printf.eprintf "[tet3-trace] search_fast_limited rg=%d skipped (could_p=%b could_s=%b could_o=%b)\\n%!"
              r could_p could_s could_o;
          incr rg
        end else begin"""

if old_block not in content:
    sys.stderr.write("  [tet3-fstar-redirect-search-limited] WARN: search_fast_limited gate anchor not found; aborting\n")
    sys.exit(0)

content = content.replace(old_block, new_block, 1)

# Append a trace line just before the final aleph6-trace summary so the
# via_fstar / via_hashtbl counts are visible in the smoke logs. Anchor:
# the existing `[aleph6-trace] search_fast_limited: matched ...` line.
old_summary = """    Printf.eprintf "[aleph6-trace] search_fast_limited: matched %d/%d row(s), walked %d/%d rg(s)\\n%!"
      !n_matches limit !rg rg_count;"""

new_summary = """    Printf.eprintf "[tet3-fstar-trace] search_fast_limited: rg-tests via_fstar=%d via_hashtbl=%d\\n%!"
      !n_via_fstar_lim !n_via_hashtbl_lim;
    Printf.eprintf "[aleph6-trace] search_fast_limited: matched %d/%d row(s), walked %d/%d rg(s)\\n%!"
      !n_matches limit !rg rg_count;"""

if old_summary not in content:
    sys.stderr.write("  [tet3-fstar-redirect-search-limited] WARN: aleph6-trace summary anchor not found; trace line not added (gate redirect still applied)\n")
else:
    content = content.replace(old_summary, new_summary, 1)

path.write_text(content)
sys.stderr.write("  [tet3-fstar-redirect-search-limited] applied: search_fast_limited candidate-gate routed through F* RDF_CottasStore_PresenceBitmap\n")
PYEOF

echo "  Tet3 -> F* redirect (search_fast_limited) patch applied."
