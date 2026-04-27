#!/bin/bash
# Compound (p, o) -> F* redirect: estimate_fast_inner candidate counter.
# Issue #104, 2026-04-26 (handle: nun4, reader half).
#
# What this patch does:
#
#   The writer patch (cottas_ondisk_zzzzzzzzzzzzz_compound_po_writer.sh)
#   builds a sibling `<cottas>.po.presence` companion file at boot:
#   per-row-group sparse-roaring sorted (p_id, o_id) pair list. This
#   patch wires the READER half: a thin OCaml dispatch shim that calls
#   the F*-extracted reader RDF_CottasStore_CompoundPresenceBitmap to
#   answer "could rg `r` contain at least one row whose predicate-token
#   is `p` AND object-token is `o`?".
#
#   The shim is then consulted from inside `estimate_fast_inner`'s
#   per-rg candidate-counting loop, AND-composed with the existing
#   per-column Tet3 redirect verdict. When both p and o are bound and
#   the compound bitmap says "no pair in this rg", the rg drops out of
#   `candidates`. For Q03 (`?o a geo:wktLiteral`) the compound says no
#   for all 26 parliament rgs -> mem5 returns est=0 -> planner short-
#   circuits BGP eval -> Q03 drops from ~3.82s to <100ms.
#
#   Shape (c) per fstar-purity-unwind.md: trivial dispatch shim that
#   calls F*-extracted code (rule #11(c)). The decision logic ("rg
#   could contain (p, o)?") lives entirely in F*'s
#   RDF_CottasStore_CompoundPresenceBitmap.rg_could_contain_pair. The
#   OCaml side only:
#     1. derives the .po.presence path from cottas_path,
#     2. caches `option compound_handle` per cottas_path,
#     3. calls into the F*-extracted reader.
#
#   Soundness fallback: if `open_compound` returns None (companion file
#   missing or header invalid) the helper returns `None` from
#   `could_contain_pair_via_fstar`, so the caller's per-column-only
#   verdict carries — strictly identical semantics to before this patch.
#   On parliament (which has the .po.presence file) the F* path is
#   always taken and adds a single extra AND-conjunct.
#
# Sort order: cottas_ondisk_zzzzzzzzzzzzzz_* (14 z's) — runs strictly
# AFTER the writer at 13 z's (alphabetical sort of the experimental_
# ocaml_glue/ directory).
#
# Rule #11(c): NO RDF/SPARQL semantic logic in this patch. The shim
# only opens / caches / dispatches. The per-rg pair-presence test is
# in F*. If you find yourself adding rule logic here, STOP — it goes
# in F*.
#
# Rule #16: no `tail -N` / `head -N` truncation. Patch logs go to
# stderr unfiltered.
# Rule #15: no semantic logic in patches.
# Rule #13: this patch is applied post-extraction; no direct edits to
# .ml files in source-controlled trees.
#
# Idempotency: skip-if-marker pattern.

set -euo pipefail

OUTDIR="$1"

if [[ -f "$OUTDIR" && "$OUTDIR" == *.ml ]]; then
  OUTDIR="$(dirname "$OUTDIR")"
fi

FILE="$OUTDIR/RDF_CottasStore.ml"
if [[ ! -f "$FILE" ]]; then
  echo "  Warning: $FILE not found, skipping compound-po-redirect patch" >&2
  exit 0
fi

# Sanity: prerequisite patches must have already run.
# Need the writer (so the file exists at boot) and the Tet3 estimate
# redirect (whose anchor we modify).
if ! grep -q 'compound-po: Cottas_compound_po_writer installed' "$FILE"; then
  echo "  Warning: compound-po-redirect needs the writer patch;" >&2
  echo "  experimental_ocaml_glue/cottas_ondisk_zzzzzzzzzzzzz_compound_po_writer.sh must run first." >&2
  exit 0
fi

if ! grep -q 'tet3_fstar_redirect: estimate helper installed' "$FILE"; then
  echo "  Warning: compound-po-redirect needs the Tet3 estimate redirect helper;" >&2
  echo "  experimental_ocaml_glue/cottas_ondisk_zzzzzzzzzz_tet3_fstar_redirect_estimate.sh must run first." >&2
  exit 0
fi

if grep -q 'compound_po_fstar_redirect: estimate helper installed' "$FILE"; then
  echo "  Compound (p, o) F* redirect (estimate) patch already present."
  exit 0
fi

python3 - "$FILE" <<'PYEOF'
import sys
from pathlib import Path

path = Path(sys.argv[1])
content = path.read_text()

# ----------------------------------------------------------------------
# Step 1: Install helper module `Compound_po_fstar_redirect` next to
# `Tet3_fstar_redirect`. Anchor: insert IMMEDIATELY AFTER Tet3's helper
# module's closing `end`, so we don't disturb any other anchors. The
# Tet3 helper module's closing tag is the unique line:
#   end
# directly following Tet3's `let could_via_fstar` definition. To make
# the anchor robust, we anchor on the closing two lines of Tet3's
# module + the blank line after, and insert our new module in between.
# ----------------------------------------------------------------------

helper_module = """(* compound_po_fstar_redirect: estimate helper installed (issue #104,
   2026-04-26). Bridges the OCaml estimate_fast_inner candidate-counting
   loop to F*'s RDF_CottasStore_CompoundPresenceBitmap. Caches
   `option compound_handle` per cottas_path. Cache value is the option
   itself, so a "no companion file" result is memoised too — `None`
   fall-through is fast.

   Rule #11(c) compliant: trivial dispatch shim. The decision
   "rg could contain (p, o) jointly" lives in F*'s
   rg_could_contain_pair. *)
module Compound_po_fstar_redirect = struct
  open Stdlib
  type pint = Stdlib.Int.t

  (* Companion path suffix: <cottas_path>.po.presence (matches the
     writer patch's `compound_path`). *)
  let compound_path (cottas_path : string) : string =
    cottas_path ^ ".po.presence"

  (* Cache key cottas_path -> option compound_handle. *)
  let cache : (string, RDF_CottasStore_CompoundPresenceBitmap.compound_handle FStar_Pervasives_Native.option) Hashtbl.t
    = Hashtbl.create 17

  let compound_for (cottas_path : string)
    : RDF_CottasStore_CompoundPresenceBitmap.compound_handle FStar_Pervasives_Native.option =
    match Hashtbl.find_opt cache cottas_path with
    | Some oh -> oh
    | None ->
      let cpath = compound_path cottas_path in
      let oh = RDF_CottasStore_CompoundPresenceBitmap.open_compound cpath in
      Hashtbl.add cache cottas_path oh;
      Printf.eprintf "[compound-po-fstar-trace] compound_for path=%s opened=%b\\n%!"
        cpath
        (match oh with FStar_Pervasives_Native.Some _ -> true | _ -> false);
      oh

  (* could_contain_pair_via_fstar:
     Returns Some b iff the compound companion is present AND both p
     and o are bound (the only case where compound says anything
     meaningful). Returns None if the companion is absent OR either
     bound is None — in either case the caller's per-column-only
     verdict carries (we have no opinion). *)
  let could_contain_pair_via_fstar
    (cottas_path : string) (rg : pint)
    (bound_p_id : Prims.nat FStar_Pervasives_Native.option)
    (bound_o_id : Prims.nat FStar_Pervasives_Native.option)
    : bool FStar_Pervasives_Native.option =
    match bound_p_id, bound_o_id with
    | FStar_Pervasives_Native.Some _, FStar_Pervasives_Native.Some _ ->
      (let oh = compound_for cottas_path in
       match oh with
       | FStar_Pervasives_Native.None ->
         FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some _ ->
         let b = RDF_CottasStore_CompoundPresenceBitmap.compound_rg_passes_pair
                   oh (Z.of_int rg) bound_p_id bound_o_id in
         FStar_Pervasives_Native.Some b)
    | _, _ ->
      (* compound has no opinion when p or o is unbound *)
      FStar_Pervasives_Native.None
end

"""

# Anchor: place the new helper module right after Tet3_fstar_redirect's
# closing `end`. The Tet3 helper module's signature ends with the unique
# line `end` followed by exactly one blank line and the
# `module Cottas_ondisk_runtime = struct` declaration (which Tet3
# inserts before). To minimise anchor fragility, we anchor on the
# Tet3 helper's `let could_via_fstar` signature's closing pattern —
# the FStar_Pervasives_Native.Some b value followed by `end`.

tet3_close_anchor = """      let b = RDF_CottasStore_PresenceBitmap.rg_could_contain
                oh (Z.of_int rg) bound_tok_id in
      FStar_Pervasives_Native.Some b
end

"""

if tet3_close_anchor not in content:
    sys.stderr.write("  [compound-po-fstar-redirect] FATAL: Tet3 helper's closing anchor not found; aborting\n")
    sys.exit(1)

content = content.replace(tet3_close_anchor,
                          tet3_close_anchor + helper_module, 1)

# ----------------------------------------------------------------------
# Step 2: Modify the candidate-counting loop in estimate_fast_inner.
# After the existing Tet3 redirect block computes `could_p && could_s
# && could_o`, AND it with the compound verdict (when decisive). The
# loop body before our patch is the multi-line block ending with:
#     if could_p && could_s && could_o then incr candidates
#
# We change that line to:
#     let compound_ok = match Compound_po_fstar_redirect... with
#       | Some b -> b | None -> true in
#     if could_p && could_s && could_o && compound_ok then incr candidates
#
# Anchor on the unique 3-line block (also includes the surrounding
# tet3_fstar_redirect comment so the anchor cannot match in
# search_fast_inner / search_fast_limited).
# ----------------------------------------------------------------------

old_block = """        let could_o = could_via path 2 bound.Parser_BallyhooCOTTAS.cbqp_o
          bound_o Cottas_ondisk_lazy.obj_rg_could_contain in
        if could_p && could_s && could_o then incr candidates
      done;
      Printf.eprintf "[tet3-fstar-trace] estimate_fast_inner: rg-tests via_fstar=%d via_hashtbl=%d\\n%!"
        !n_via_fstar !n_via_hashtbl;"""

new_block = """        let could_o = could_via path 2 bound.Parser_BallyhooCOTTAS.cbqp_o
          bound_o Cottas_ondisk_lazy.obj_rg_could_contain in
        (* compound_po_fstar_redirect: AND-compose the per-column verdict
           with the joint-(p, o) compound bitmap when both are bound and
           the .po.presence companion is present. F*'s
           rg_could_contain_pair does the actual binary-search; we just
           wire the AND. *)
        let compound_ok =
          match Compound_po_fstar_redirect.could_contain_pair_via_fstar
                  path rg bound.Parser_BallyhooCOTTAS.cbqp_p
                  bound.Parser_BallyhooCOTTAS.cbqp_o with
          | FStar_Pervasives_Native.Some b -> b
          | FStar_Pervasives_Native.None -> true in
        if could_p && could_s && could_o && compound_ok then
          incr candidates
      done;
      Printf.eprintf "[tet3-fstar-trace] estimate_fast_inner: rg-tests via_fstar=%d via_hashtbl=%d\\n%!"
        !n_via_fstar !n_via_hashtbl;"""

if old_block not in content:
    sys.stderr.write("  [compound-po-fstar-redirect] FATAL: estimate_fast_inner candidate-block anchor not found; aborting\n")
    sys.exit(1)

content = content.replace(old_block, new_block, 1)

path.write_text(content)
sys.stderr.write("  [compound-po-fstar-redirect] applied: estimate_fast_inner candidate-counter AND-composed with F* compound (p, o) bitmap\n")
PYEOF

echo "  Compound (p, o) F* redirect (estimate) patch applied."
