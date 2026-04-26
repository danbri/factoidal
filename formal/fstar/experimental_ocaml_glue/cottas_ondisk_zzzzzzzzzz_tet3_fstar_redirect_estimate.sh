#!/bin/bash
# Tet3 -> F* redirect, step 1: estimate_fast_inner candidate counter
# (issue #100, 2026-04-26, fstar-purity-unwind Phase 2.6).
#
# What this patch does:
#
#   Replaces the per-rg `could_p / could_s / could_o` block inside
#   `estimate_fast_inner` (installed by Mem5) so that the presence-
#   bitmap test goes through the F*-extracted reader
#   `RDF_CottasStore_PresenceBitmap.rg_could_contain` instead of
#   Tet3's local `Cottas_ondisk_lazy.{pred,subj,obj}_rg_could_contain`
#   string-keyed Hashtbls.
#
#   This is one of the smallest commit-shaped steps in retiring Tet3
#   (the full Tet3 patch's 310 LoC of OCaml-side semantic logic is
#   the rule #11 violator). It is NOT a full retirement: only ONE call
#   site (estimate_fast_inner) is redirected. The other Tet3 call
#   sites (search_fast_inner gate, search_fast_limited gate) still go
#   through Tet3's Hashtbls in this patch. Subsequent commits redirect
#   each of those.
#
#   Shape (a) per fstar-purity-unwind.md: thin dispatch shim that
#   calls F*-extracted code. Per CLAUDE.md rule #11(c), trivial
#   dispatch shims that call F*-extracted code are allowed in
#   experimental_ocaml_glue/. The decision logic ("is this rg a
#   candidate?") is now in F*; the OCaml side is reduced to:
#     1. derive companion-file path (.s.presence / .p.presence /
#        .o.presence) from cottas_path
#     2. call RDF_CottasStore_PresenceBitmap.open_bitmap (cached)
#     3. call RDF_CottasStore_PresenceBitmap.rg_could_contain
#
#   The token-id namespace used by `bound.cbqp_p`/`cbqp_s`/`cbqp_o`
#   (Prims.nat option) IS the .dict-sorted-id namespace populated by
#   Vav3's `bulk_load_column_into_tables`. So the int passed to F*'s
#   `rg_could_contain` matches the bit position the Vav3 writer set
#   in the .presence bitmap. This is the same equivalence Tet3's
#   string-keyed Hashtbls rely on, just expressed via the F* API.
#
#   Soundness fallback: if `open_bitmap` returns None (companion
#   file missing or header invalid) the helper falls back to the
#   existing Tet3 Hashtbl path. So this is strictly a redirect when
#   companions are present; behaviour is identical otherwise.
#
# Sort order: cottas_ondisk_zzzzzzzzzz_* — must run AFTER Mem5
# (zzzzzzz) which installed estimate_fast_inner's body, AND after
# the q03 fix (zzzzzzzzz). Higher z-count -> later in sort order.
#
# Rule #11(c) compliance: the helper module added by this patch
# contains zero RDF/SPARQL semantic logic. It only:
#   - resolves a path-string to a column suffix
#   - caches `option bitmap_handle` per (cottas_path, col_idx)
#   - calls into RDF_CottasStore_PresenceBitmap.* (F*-extracted)
# The decision "could rg contain bound token?" lives in F*.
#
# When the next commit redirects search_fast_inner / _limited, the
# Tet3 Hashtbl population in ensure_subjects_loaded /
# ensure_objects_loaded becomes dead code; eventually the Tet3 patch
# itself (cottas_ondisk_zzzz_tet3_subj_obj_prune.sh) is deleted and
# this redirect helper becomes the only path.
#
# Idempotency: skip-if-marker pattern.

set -euo pipefail

OUTDIR="$1"

if [[ -f "$OUTDIR" && "$OUTDIR" == *.ml ]]; then
  OUTDIR="$(dirname "$OUTDIR")"
fi

FILE="$OUTDIR/RDF_CottasStore.ml"
if [[ ! -f "$FILE" ]]; then
  echo "  Warning: $FILE not found, skipping tet3-fstar-redirect patch" >&2
  exit 0
fi

# Sanity: prerequisite patches must have already run.
if ! grep -q 'mem5: estimate_fast_inner presence-bitmap fast path' "$FILE"; then
  echo "  Warning: tet3-fstar-redirect needs Mem5's estimate_fast_inner;" >&2
  echo "  experimental_ocaml_glue/cottas_ondisk_zzzzzzz_mem5_estimate_presence.sh must run first." >&2
  exit 0
fi

if grep -q 'tet3_fstar_redirect: estimate helper installed' "$FILE"; then
  echo "  Tet3 -> F* redirect patch already present."
  exit 0
fi

python3 - "$FILE" <<'PYEOF'
import sys
from pathlib import Path

path = Path(sys.argv[1])
content = path.read_text()

# ----------------------------------------------------------------------
# Step 1: Insert helper module `Tet3_fstar_redirect` after Vav3's
# Cottas_companion_writer / Cottas_companion_boot block. Anchor on the
# Tet3 patch marker comment (which sits at the end of Cottas_ondisk_lazy
# additions) — too early. Better anchor: insert just before
# `module Cottas_ondisk_runtime = struct` which is where the runtime
# functions live and where helpers should be in scope.
#
# Looking at the post-Mem5 structure: the runtime functions
# (estimate_fast_inner, search_fast_inner, etc.) are inside
# `module Cottas_ondisk_runtime = struct`. We insert the helper module
# AT TOP-LEVEL just before that module definition, so it's reachable.
#
# Anchor: the literal string `module Cottas_ondisk_runtime = struct`.
# ----------------------------------------------------------------------

helper_module = """(* tet3_fstar_redirect: estimate helper installed (issue #100, 2026-04-26).
   Bridges OCaml call sites to F*'s RDF_CottasStore_PresenceBitmap.
   Caches `option bitmap_handle` per (cottas_path, col_idx). The cache
   value is itself the `option bitmap_handle` so a "no companion"
   result is memoised too — `None` fall through is fast.

   Rule #11(c) compliant: trivial dispatch shim. The decision
   "rg could contain token" lives in F*'s rg_could_contain. *)
module Tet3_fstar_redirect = struct
  open Stdlib
  type pint = Stdlib.Int.t

  (* Companion path suffix per column (matches Vav3's writer). *)
  let presence_path (cottas_path : string) (col_idx : pint) : string =
    let suf = match col_idx with
      | 0 -> "s" | 1 -> "p" | 2 -> "o" | _ -> "g" in
    Printf.sprintf "%s.%s.presence" cottas_path suf

  (* Cache key (cottas_path, col_idx) -> option bitmap_handle. *)
  let cache : (string * pint, RDF_CottasStore_PresenceBitmap.bitmap_handle FStar_Pervasives_Native.option) Hashtbl.t
    = Hashtbl.create 17

  let bitmap_for (cottas_path : string) (col_idx : pint)
    : RDF_CottasStore_PresenceBitmap.bitmap_handle FStar_Pervasives_Native.option =
    let key = (cottas_path, col_idx) in
    match Hashtbl.find_opt cache key with
    | Some oh -> oh
    | None ->
      let ppath = presence_path cottas_path col_idx in
      let oh = RDF_CottasStore_PresenceBitmap.open_bitmap ppath in
      Hashtbl.add cache key oh;
      Printf.eprintf "[tet3-fstar-trace] bitmap_for col=%d path=%s opened=%b\\n%!"
        col_idx ppath
        (match oh with FStar_Pervasives_Native.Some _ -> true | _ -> false);
      oh

  (* could_via_fstar:
     Returns Some b iff the companion is present and the F* bitmap
     gave a definitive answer. Returns None to mean "fall back to the
     OCaml Tet3 Hashtbl path" (companion absent or header invalid).

     Token-id type bridge: the OCaml call sites have
     `bound.cbqp_X : Prims.nat option` (the dict-id namespace). We pass
     it through as-is to rg_could_contain, which expects
     `option nat`. Both forms are FStar_Pervasives_Native.option of
     Prims.nat — same OCaml representation post-extraction. *)
  let could_via_fstar
    (cottas_path : string) (col_idx : pint) (rg : pint)
    (bound_tok_id : Prims.nat FStar_Pervasives_Native.option)
    : bool FStar_Pervasives_Native.option =
    let oh = bitmap_for cottas_path col_idx in
    match oh with
    | FStar_Pervasives_Native.None ->
      (* No companion file: fall back to existing Tet3 path (returns
         None to signal "use the Hashtbl path"). *)
      FStar_Pervasives_Native.None
    | FStar_Pervasives_Native.Some _ ->
      (* Companion is present: trust F*'s answer. *)
      let b = RDF_CottasStore_PresenceBitmap.rg_could_contain
                oh (Z.of_int rg) bound_tok_id in
      FStar_Pervasives_Native.Some b
end

"""

anchor = "module Cottas_ondisk_runtime = struct"
if anchor not in content:
    sys.stderr.write("  [tet3-fstar-redirect] WARN: Cottas_ondisk_runtime anchor not found; aborting\n")
    sys.exit(0)

content = content.replace(anchor, helper_module + anchor, 1)

# ----------------------------------------------------------------------
# Step 2: Replace the candidate-counting block inside
# `estimate_fast_inner` (Mem5-installed) so the per-rg presence test
# goes through the F* helper. The exact block is:
#
#       let candidates = ref 0 in
#       for rg = 0 to rg_count - 1 do
#         let could_p = Cottas_ondisk_lazy.pred_rg_could_contain path rg bound_p in
#         let could_s = Cottas_ondisk_lazy.subj_rg_could_contain path rg bound_s in
#         let could_o = Cottas_ondisk_lazy.obj_rg_could_contain  path rg bound_o in
#         if could_p && could_s && could_o then incr candidates
#       done;
#
# We rewrite each `could_X` to: try F* first, fall back to Tet3 if F*
# returned None (companion absent). The fall-back preserves identical
# semantics on corpora without companion files; on parliament (which
# has all 4 .presence files) the F* path is always taken.
#
# We also need bound.cbqp_p / cbqp_s / cbqp_o (the raw nat ids) in
# scope. They are upstream in the same function: `bound : Parser_-
# BallyhooCOTTAS.cottas_bound_qp` is the parameter. So we use
# `bound.Parser_BallyhooCOTTAS.cbqp_p` etc.
# ----------------------------------------------------------------------

old_block = """      let candidates = ref 0 in
      for rg = 0 to rg_count - 1 do
        let could_p = Cottas_ondisk_lazy.pred_rg_could_contain path rg bound_p in
        let could_s = Cottas_ondisk_lazy.subj_rg_could_contain path rg bound_s in
        let could_o = Cottas_ondisk_lazy.obj_rg_could_contain  path rg bound_o in
        if could_p && could_s && could_o then incr candidates
      done;"""

new_block = """      let candidates = ref 0 in
      let n_via_fstar = ref 0 in
      let n_via_hashtbl = ref 0 in
      for rg = 0 to rg_count - 1 do
        (* tet3_fstar_redirect: try F* RDF_CottasStore_PresenceBitmap
           first; fall back to Tet3's OCaml Hashtbl path only when the
           companion file is absent (open_bitmap = None). On corpora
           with companion files (parliament has all 4) the F* path is
           always taken and the Hashtbl path is dead. *)
        let could_via path_ col_idx bound_id bound_str fallback_get =
          match Tet3_fstar_redirect.could_via_fstar
                  path_ col_idx rg bound_id with
          | FStar_Pervasives_Native.Some b ->
            incr n_via_fstar; b
          | FStar_Pervasives_Native.None ->
            incr n_via_hashtbl; fallback_get path_ rg bound_str in
        let could_p = could_via path 1 bound.Parser_BallyhooCOTTAS.cbqp_p
          bound_p Cottas_ondisk_lazy.pred_rg_could_contain in
        let could_s = could_via path 0 bound.Parser_BallyhooCOTTAS.cbqp_s
          bound_s Cottas_ondisk_lazy.subj_rg_could_contain in
        let could_o = could_via path 2 bound.Parser_BallyhooCOTTAS.cbqp_o
          bound_o Cottas_ondisk_lazy.obj_rg_could_contain in
        if could_p && could_s && could_o then incr candidates
      done;
      Printf.eprintf "[tet3-fstar-trace] estimate_fast_inner: rg-tests via_fstar=%d via_hashtbl=%d\\n%!"
        !n_via_fstar !n_via_hashtbl;"""

if old_block not in content:
    sys.stderr.write("  [tet3-fstar-redirect] WARN: estimate_fast_inner candidate-block anchor not found; aborting\n")
    sys.exit(0)

content = content.replace(old_block, new_block, 1)

path.write_text(content)
sys.stderr.write("  [tet3-fstar-redirect] applied: estimate_fast_inner candidate-counter routed through F* RDF_CottasStore_PresenceBitmap\n")
PYEOF

echo "  Tet3 -> F* redirect (estimate_fast_inner) patch applied."
