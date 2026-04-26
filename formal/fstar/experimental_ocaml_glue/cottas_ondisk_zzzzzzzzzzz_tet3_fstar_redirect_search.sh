#!/bin/bash
# Tet3 -> F* redirect, step 2: search_fast_inner candidate gate.
# (issue #100, 2026-04-26, fstar-purity-unwind Phase 2.6).
#
# What this patch does:
#
#   Replaces the per-rg `could_p / could_s / could_o` gate inside
#   `search_fast_inner` so the presence-bitmap test goes through the
#   F*-extracted reader `RDF_CottasStore_PresenceBitmap.rg_could_contain`
#   instead of Tet3's local string-keyed Hashtbls in
#   `Cottas_ondisk_lazy.{pred,subj,obj}_rg_could_contain`.
#
#   This is the second of three Tet3 -> F* redirects (the first was
#   `estimate_fast_inner`; the third will be `search_fast_limited`).
#   Each is a separate small commit.
#
#   Helper module `Tet3_fstar_redirect` was installed by the prior
#   patch (cottas_ondisk_zzzzzzzzzz_tet3_fstar_redirect_estimate.sh).
#   This patch only consumes that helper — it does NOT redefine it.
#   The helper provides `could_via_fstar : path -> col_idx -> rg ->
#   bound_id -> bool option`. `Some b` means F* answered definitively;
#   `None` means companion file absent — fall back to Tet3 Hashtbl.
#
#   Shape (a) per fstar-purity-unwind.md: thin dispatch shim that
#   calls F*-extracted code (rule #11(c)). The decision logic ("is
#   this rg a candidate?") is now in F*; this patch only switches one
#   more call site to consult it.
#
# Sort order: cottas_ondisk_zzzzzzzzzzz_* — one more `z` than the
# estimate redirect, so it runs strictly after it. The estimate
# redirect installs the `Tet3_fstar_redirect` helper module; this
# patch needs that helper to exist.
#
# Idempotency: skip-if-marker pattern.

set -euo pipefail

OUTDIR="$1"

if [[ -f "$OUTDIR" && "$OUTDIR" == *.ml ]]; then
  OUTDIR="$(dirname "$OUTDIR")"
fi

FILE="$OUTDIR/RDF_CottasStore.ml"
if [[ ! -f "$FILE" ]]; then
  echo "  Warning: $FILE not found, skipping tet3-fstar-redirect-search patch" >&2
  exit 0
fi

# Sanity: prerequisite redirects must have run.
if ! grep -q 'tet3_fstar_redirect: estimate helper installed' "$FILE"; then
  echo "  Warning: tet3-fstar-redirect-search needs the estimate redirect's helper module;" >&2
  echo "  experimental_ocaml_glue/cottas_ondisk_zzzzzzzzzz_tet3_fstar_redirect_estimate.sh must run first." >&2
  exit 0
fi

if grep -q 'tet3_fstar_redirect_search: search_fast_inner installed' "$FILE"; then
  echo "  Tet3 -> F* redirect (search_fast_inner) patch already present."
  exit 0
fi

python3 - "$FILE" <<'PYEOF'
import sys
from pathlib import Path

path = Path(sys.argv[1])
content = path.read_text()

# ----------------------------------------------------------------------
# Replace the candidate-gate block inside `search_fast_inner` so the
# per-rg presence test goes through the F* helper. The exact gate is:
#
#     for rg = 0 to rg_count - 1 do
#       let could_p = Cottas_ondisk_lazy.pred_rg_could_contain path rg bound_p in
#       let could_s = Cottas_ondisk_lazy.subj_rg_could_contain path rg bound_s in
#       let could_o = Cottas_ondisk_lazy.obj_rg_could_contain  path rg bound_o in
#       if not (could_p && could_s && could_o) then begin
#         incr n_skipped;
#         ...
#       end else begin
#         try walk_rg rg
#         ...
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

old_block = """    let n_skipped = ref 0 in
    for rg = 0 to rg_count - 1 do
      let could_p = Cottas_ondisk_lazy.pred_rg_could_contain path rg bound_p in
      let could_s = Cottas_ondisk_lazy.subj_rg_could_contain path rg bound_s in
      let could_o = Cottas_ondisk_lazy.obj_rg_could_contain  path rg bound_o in
      if not (could_p && could_s && could_o) then begin
        incr n_skipped;
        if !n_skipped <= 3 || !n_skipped mod 5 = 0 then
          Printf.eprintf "[tet3-trace] search_fast rg=%d skipped (could_p=%b could_s=%b could_o=%b)\\n%!"
            rg could_p could_s could_o
      end else begin
        try walk_rg rg
        with e ->
          let bt = Printexc.get_backtrace () in
          Printf.eprintf "[pe4-FATAL] search_fast rg=%d EXCEPTION: %s\\nbacktrace=%s\\n%!"
            rg (Printexc.to_string e) bt;
          raise e
      end
    done;"""

new_block = """    let n_skipped = ref 0 in
    (* tet3_fstar_redirect_search: search_fast_inner installed
       (issue #100, 2026-04-26). Per-rg gate routed through F*'s
       RDF_CottasStore_PresenceBitmap via the Tet3_fstar_redirect
       helper (installed by the prior estimate-redirect patch).
       Fall back to the existing Tet3 Hashtbl path only when
       could_via_fstar returns None (companion file absent). *)
    let n_via_fstar_search = ref 0 in
    let n_via_hashtbl_search = ref 0 in
    for rg = 0 to rg_count - 1 do
      let could_via path_ col_idx bound_id bound_str fallback_get =
        match Tet3_fstar_redirect.could_via_fstar
                path_ col_idx rg bound_id with
        | FStar_Pervasives_Native.Some b ->
          incr n_via_fstar_search; b
        | FStar_Pervasives_Native.None ->
          incr n_via_hashtbl_search; fallback_get path_ rg bound_str in
      let could_p = could_via path 1 bound.Parser_BallyhooCOTTAS.cbqp_p
        bound_p Cottas_ondisk_lazy.pred_rg_could_contain in
      let could_s = could_via path 0 bound.Parser_BallyhooCOTTAS.cbqp_s
        bound_s Cottas_ondisk_lazy.subj_rg_could_contain in
      let could_o = could_via path 2 bound.Parser_BallyhooCOTTAS.cbqp_o
        bound_o Cottas_ondisk_lazy.obj_rg_could_contain in
      if not (could_p && could_s && could_o) then begin
        incr n_skipped;
        if !n_skipped <= 3 || !n_skipped mod 5 = 0 then
          Printf.eprintf "[tet3-trace] search_fast rg=%d skipped (could_p=%b could_s=%b could_o=%b)\\n%!"
            rg could_p could_s could_o
      end else begin
        try walk_rg rg
        with e ->
          let bt = Printexc.get_backtrace () in
          Printf.eprintf "[pe4-FATAL] search_fast rg=%d EXCEPTION: %s\\nbacktrace=%s\\n%!"
            rg (Printexc.to_string e) bt;
          raise e
      end
    done;
    Printf.eprintf "[tet3-fstar-trace] search_fast_inner: rg-tests via_fstar=%d via_hashtbl=%d\\n%!"
      !n_via_fstar_search !n_via_hashtbl_search;"""

if old_block not in content:
    sys.stderr.write("  [tet3-fstar-redirect-search] WARN: search_fast_inner gate anchor not found; aborting\n")
    sys.exit(0)

content = content.replace(old_block, new_block, 1)

path.write_text(content)
sys.stderr.write("  [tet3-fstar-redirect-search] applied: search_fast_inner candidate-gate routed through F* RDF_CottasStore_PresenceBitmap\n")
PYEOF

echo "  Tet3 -> F* redirect (search_fast_inner) patch applied."
