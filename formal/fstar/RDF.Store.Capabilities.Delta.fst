module RDF.Store.Capabilities.Delta

(* The D-overlay — docs/designissues/2026-07-06-unified-store-
   architecture.md §3.3 ("COTTAS + delta as a composition — the
   elegance") and docs/designissues/2026-07-06-durable-update-design.md
   stage 3. `overlay` is the single function that turns any base read
   seam (`RDF.Store.Capabilities.store_caps`) plus a resolved delta
   (`RDF.Store.Columnar.DeltaMerge.delta_resolved`, ONE graph's worth —
   see that module's own banner for why) into another `store_caps` of
   the SAME type — no new constructor, no optional field, exactly as
   the design doc's §3.3 states: "overlay is a function store_caps ->
   delta -> store_caps, so there is no new constructor and no optional
   field on an existing one."

   Split into its own sibling module (alongside
   RDF.Store.Capabilities.Cottas) rather than folded into
   RDF.Store.Capabilities itself, because `overlay` needs BOTH
   `store_caps` (RDF.Store.Capabilities) and `delta_resolved`
   (RDF.Store.Columnar.DeltaMerge, which itself sits below
   RDF.Store.Capabilities in the DAG per that module's own banner —
   DeltaMerge depends on SPARQL11.Algebra + RDF.Graph.Executable +
   RDF.Store.Columnar.DeltaLog only, none of which import
   RDF.Store.Capabilities). Folding `overlay` into
   RDF.Store.Capabilities.fst itself would make THAT module depend on
   DeltaMerge, which is harmless dependency-direction-wise but is
   avoided here anyway so RDF.Store.Capabilities.fst's own contract
   ("this module introduces ONLY the types + the in-memory builder")
   stays intentionally narrow, matching how RDF.Store.Capabilities.
   Cottas already carries the COTTAS-specific builder as its own
   sibling rather than growing the base module. This module is
   Unix/mmap-free (same as RDF.Store.Capabilities itself) — `overlay`
   is a pure function over already-built `store_caps`/`delta_resolved`
   values, so it is safe to include in a JS/wasm module list wherever
   RDF.Store.Capabilities itself is. *)

open RDF.Graph.Executable
open SPARQL11.Algebra
open RDF.Store.Capabilities

module DM = RDF.Store.Columnar.DeltaMerge

// `RDF.Store.Capabilities.fst`'s own local copy of `list_take_n`
// (that module's adjustment #3) — duplicated here for the same DAG
// reason (this module cannot import SPARQL11.Store, which sits ABOVE
// it and owns the canonical `list_take_n`).
let rec delta_caps_take_n (#a:Type) (n : nat) (xs : list a)
  : Tot (list a) (decreases n) =
  if n = 0 then []
  else
    match xs with
    | [] -> []
    | hd :: tl -> hd :: delta_caps_take_n (n - 1) tl

// The overlay (design doc §3.3's sketch, realised): base capability
// plus a resolved per-graph delta equals the SAME interface, so the
// evaluator never learns a delta exists. Every field degenerates to
// EXACTLY `base`'s own field when the delta is empty
// (`DM.delta_resolved_is_empty`) — the "empty delta costs nothing"
// floor (durable-update design §1 requirement 3) is this function's
// own no-op branch, not a separate optimisation layered on top.
let overlay (base : store_caps) (delta : DM.delta_resolved) : Tot store_caps =
  if DM.delta_resolved_is_empty delta then
    { base with sc_flags = { base.sc_flags with scf_supports_update = true } }
  else
    {
      sc_flags = { base.sc_flags with scf_supports_update = true };

      // Realises DM.merge_on_read on top of whatever `base.sc_solve`
      // already returns for this bound — pure composition, no change
      // to how the base itself is read.
      sc_solve = (fun b -> DM.merge_on_read (base.sc_solve b) delta b);

      // No real LIMIT pushdown once a delta is in play (the design
      // doc's own sketch accepts the same trade — §3.3's `overlay`
      // sample uses `list_take_n n (merge_on_read ...)` too): solve
      // the full merged view for this bound, then truncate.
      sc_solve_limited =
        (fun b n -> delta_caps_take_n n (DM.merge_on_read (base.sc_solve b) delta b));

      // O(delta) additive term only — never re-touches base_results.
      sc_estimate = (fun b -> base.sc_estimate b + DM.delta_matching_count delta b);

      // Recomputed via the merged view (exact, by construction of
      // `merge_on_read`) rather than base's count +/- delta arithmetic:
      // avoids a `nat` underflow proof obligation the arithmetic form
      // would carry (base.sc_count_exact b and length(base.sc_solve b)
      // are not provably equal for an arbitrary store_caps instance),
      // at the honest cost of materialising base.sc_solve b whenever
      // the delta is non-empty — the SAME cost `sc_solve` already
      // pays for this bound, not an extra materialisation.
      sc_count_exact =
        (fun b -> List.Tot.length (DM.merge_on_read (base.sc_solve b) delta b));

      // Conservative OR (never a false negative — see
      // DM.delta_added_has_predicate's own comment for the accepted
      // false-positive direction).
      sc_predicate_present =
        (fun pred -> base.sc_predicate_present pred || DM.delta_added_has_predicate delta.DM.dr_added pred);

      // The delta layer introduces no decode failures of its own.
      sc_decode_failure = base.sc_decode_failure;
    }
