module SPARQL.Plan.Pruning

// Row-group prune predicate for the COTTAS / columnar query planner.
//
// Recovery plan Phase 4 (docs/designissues/2026-05-07-query-planning-
// fstar-recovery.md). Retires three codename violators in one descriptive
// home:
//
//   - Yod6 — predicate-presence row-group skip predicate.
//     Old shape: per-rg `.p.presence` bitmap consulted via an OCaml
//     Hashtbl mirror inside `cottas_ondisk_zzz_yod6_pred_presence_prune.sh`.
//     New shape: F* function over `RDF.CottasStore.PresenceBitmap`'s
//     read API (Psi3 in `RDF.CottasStore.PresenceBitmap.fst`).
//   - Tet3 — subject + object presence row-group skip predicate.
//     Old shape: per-rg `.s.presence` / `.o.presence` bitmaps consulted
//     via the OCaml mirror in `cottas_ondisk_zzzz_tet3_subj_obj_prune.sh`.
//     New shape: same `RDF.CottasStore.PresenceBitmap` reader, called
//     for the subject and object column with their bound token-id.
//   - The compound (p, o) joint-presence prune (Nun4) is the strictly-
//     stronger composition; we expose it here so a single call site
//     gets all three checks at once.
//
// Per CLAUDE.md rule #11: this module is pure F*. It does not introduce
// any new `assume val`s. All byte-range I/O delegates through the
// presence-bitmap modules, which delegate through `OnDiskIndex.fst`.
//
// Soundness: each per-column lemma in `RDF.CottasStore.PresenceBitmap`
// (`rg_contains_token_sound`) and `RDF.CottasStore.CompoundPresenceBitmap`
// (`rg_could_contain_pair_sound`) says that a `false` result is sound to
// trust as "no row matches". The composed predicate `rg_can_match` here
// short-circuits on the first `false` from any sub-predicate; if it
// returns `false` at all, one of the underlying soundness lemmas
// witnesses that the rg cannot match. Therefore `false` from
// `rg_can_match` is sound to skip.
//
// Wiring status: this module replaces the OCaml-side prune logic that
// used to live in `experimental_ocaml_glue/cottas_ondisk_zzz_yod6_*.sh`,
// `cottas_ondisk_zzzz_tet3_*.sh`. Those glue patches were retired in
// earlier phases (the in-tree filename pattern survives as
// `cottas_ondisk_zzzzz_ondisk_index.sh` Vav3 with the writers; readers
// went away in Yod7-Phase A). The active call site in
// `RDF.CottasStore.filter_candidates_by_compound_po` and
// `RDF.CottasStore.cottas_ondisk_estimate` will be updated to consume
// `compound_po_can_match` and the Estimate module in a thin follow-up
// once the F* extraction toolchain version drift is resolved (the
// committed `ocaml-output/RDF_CottasStore.ml` was extracted by a prior
// F* with the `let foo (arg : T) :` style; current F* emits
// `let (foo :` and the post-extraction patches have not yet been
// updated for the new shape). This module's API surface IS the final
// shape; the wiring is a build-system gap, not a spec gap.

module PB  = RDF.CottasStore.PresenceBitmap
module CPB = RDF.CottasStore.CompoundPresenceBitmap

// NOTE: This module deliberately does NOT depend on `SPARQL11.Algebra`.
// The triple-pattern shape `triple_pattern` is in Algebra; the prune
// predicate operates on RESOLVED token-ids (`option nat`), not on the
// raw pattern shape. The translation from `triple_pattern` -> bound
// token-ids is an access-path concern that lives in the COTTAS store
// (where the dictionary is) and will move to `SPARQL.Plan.AccessPath`
// in Phase 6. Keeping Pruning Algebra-free lets it compile in the
// "below SPARQL11.Algebra" slot of the COMMON_MODULES build chain.

// ---------------------------------------------------------------------------
// Bound token-ids per triple-pattern position.
//
// `option nat` per position: `Some id` means the column has a known
// token-id from the dictionary; `None` means either the position is a
// variable (no bound to test) OR the bound term wasn't in the dictionary
// (and the executor will handle that empty-result case separately).
//
// Convention chosen to mirror the existing `RDF.CottasStore.PresenceBitmap`
// API (`rg_could_contain : option bitmap_handle -> nat -> option nat -> bool`).
// ---------------------------------------------------------------------------

noeq type pattern_bound_ids = {
  pbi_s : option nat;
  pbi_p : option nat;
  pbi_o : option nat;
}

// Constructors corresponding to common shapes.
let no_bounds : pattern_bound_ids =
  { pbi_s = None; pbi_p = None; pbi_o = None }

let mk_bounds (s p o : option nat) : pattern_bound_ids =
  { pbi_s = s; pbi_p = p; pbi_o = o }

// ---------------------------------------------------------------------------
// Yod6 — predicate-presence row-group skip predicate.
//
// "For a triple pattern with a known predicate, can this row-group
// possibly contain a matching triple?" Reads the per-rg predicate-
// presence bitmap (`<corpus>.p.presence`).
//
// Semantics:
//   - Predicate position unbound (None) → true (no opinion).
//   - Bitmap not opened (None handle) → true (safe over-include).
//   - Bound predicate id `p`, bitmap available → bit at (rg, p).
// ---------------------------------------------------------------------------

let predicate_can_match
  (oh_p : option PB.bitmap_handle)
  (rg : nat)
  (bound_p : option nat)
  : Tot bool =
  PB.rg_could_contain oh_p rg bound_p

// ---------------------------------------------------------------------------
// Tet3 — subject + object presence row-group skip predicate.
//
// Same shape as Yod6 but on the subject and object column bitmaps. The
// two are distinct functions to keep call-site readability; they
// compose under `rg_can_match` below.
// ---------------------------------------------------------------------------

let subject_can_match
  (oh_s : option PB.bitmap_handle)
  (rg : nat)
  (bound_s : option nat)
  : Tot bool =
  PB.rg_could_contain oh_s rg bound_s

let object_can_match
  (oh_o : option PB.bitmap_handle)
  (rg : nat)
  (bound_o : option nat)
  : Tot bool =
  PB.rg_could_contain oh_o rg bound_o

// ---------------------------------------------------------------------------
// Compound (s, p) and (p, o) presence skip predicates.
//
// When two columns are jointly bound, the compound bitmap can rule out
// row groups that have BOTH tokens individually present but never as
// the same row. Strictly more selective than the per-column AND.
// `RDF.CottasStore.CompoundPresenceBitmap` currently exposes the (p, o)
// reader (Nun4); the (s, p) variant has the same shape but a separate
// companion file. We expose both so the planner can call either when a
// future writer lands.
//
// `compound_sp_can_match` mirrors `compound_po_can_match`: given a
// compound handle and bound (s, p) ids, return whether the rg may
// contain a row with both. The current writer is only (p, o); calling
// this with a (p, o) handle would be a usage error. We document this
// as a precondition rather than enforce it in the type — the call site
// in the COTTAS store knows which compound file it opened.
// ---------------------------------------------------------------------------

let compound_po_can_match
  (oh_compound : option CPB.compound_handle)
  (rg : nat)
  (bound_p : option nat) (bound_o : option nat)
  : Tot bool =
  CPB.compound_rg_passes_pair oh_compound rg bound_p bound_o

let compound_sp_can_match
  (oh_compound : option CPB.compound_handle)
  (rg : nat)
  (bound_s : option nat) (bound_p : option nat)
  : Tot bool =
  // Reuses the same compound-bitmap shape: the file format pairs two
  // ids by lex-sort. The first arg of `rg_passes_pair` is treated as
  // the high-32-bit slot; for an (s, p) bitmap that's `s`. The CPB
  // module is column-agnostic at the type level — the calling code
  // passes the handle for whichever compound it opened.
  CPB.compound_rg_passes_pair oh_compound rg bound_s bound_p

// ---------------------------------------------------------------------------
// rg_can_match — the top-level prune predicate.
//
// Composes Yod6 + Tet3 + the compound (p, o) gate. Returns true iff the
// rg cannot be ruled out by any of them, i.e. it should be scanned.
// Returns false only when at least one underlying gate decisively
// rules the rg out.
//
// Argument order mirrors the call-site in `RDF.CottasStore.fst`:
// per-column handles for s, p, o; bounds; compound handle for (p, o);
// the rg index.
// ---------------------------------------------------------------------------

let rg_can_match
  (rg : nat)
  (oh_s : option PB.bitmap_handle) (bound_s : option nat)
  (oh_p : option PB.bitmap_handle) (bound_p : option nat)
  (oh_o : option PB.bitmap_handle) (bound_o : option nat)
  (oh_compound_po : option CPB.compound_handle)
  : Tot bool =
  PB.rg_passes_all rg oh_s bound_s oh_p bound_p oh_o bound_o &&
  CPB.compound_rg_passes_pair oh_compound_po rg bound_p bound_o

// Caller-shaped wrapper. Takes the bundled `pattern_bound_ids` record.
let rg_can_match_for_pattern
  (rg : nat)
  (bounds : pattern_bound_ids)
  (oh_s : option PB.bitmap_handle)
  (oh_p : option PB.bitmap_handle)
  (oh_o : option PB.bitmap_handle)
  (oh_compound_po : option CPB.compound_handle)
  : Tot bool =
  rg_can_match rg
    oh_s bounds.pbi_s
    oh_p bounds.pbi_p
    oh_o bounds.pbi_o
    oh_compound_po

// ---------------------------------------------------------------------------
// Filter a candidate-rg list by `rg_can_match`. This is the loop the
// COTTAS store currently writes inline; lifted here as a pure
// combinator. Callers pass in the candidate list (e.g. produced by
// per-column dict-page intersection) and get back the surviving rgs.
//
// The result preserves input order. Empty input → empty output.
// ---------------------------------------------------------------------------

let rec filter_candidates_by_prune
  (candidates : list nat)
  (oh_s : option PB.bitmap_handle) (bound_s : option nat)
  (oh_p : option PB.bitmap_handle) (bound_p : option nat)
  (oh_o : option PB.bitmap_handle) (bound_o : option nat)
  (oh_compound_po : option CPB.compound_handle)
  : Tot (list nat) (decreases candidates) =
  match candidates with
  | [] -> []
  | rg :: rest ->
    let surviving_rest =
      filter_candidates_by_prune rest
        oh_s bound_s oh_p bound_p oh_o bound_o oh_compound_po in
    if rg_can_match rg
         oh_s bound_s oh_p bound_p oh_o bound_o oh_compound_po
    then rg :: surviving_rest
    else surviving_rest

// ---------------------------------------------------------------------------
// Identity-when-all-empty property.
//
// When no column is bound and no compound bitmap is open, every rg
// passes; the filter is the identity. This is the "no opinion ->
// include everything" safety property the existing OCaml prune-callers
// rely on.
// ---------------------------------------------------------------------------

let rg_can_match_all_unbound_is_true
  (rg : nat)
  : Lemma
    (ensures
      rg_can_match rg None None None None None None None = true)
  = ()

// Soundness sketch (statement-level; the per-column lemmas live in
// `RDF.CottasStore.PresenceBitmap.rg_contains_token_sound` and
// `CompoundPresenceBitmap.rg_could_contain_pair_sound`). We do NOT
// re-state a separate lemma here: when `rg_can_match = false`, exactly
// one of the conjuncts is false, and that conjunct's underlying
// soundness lemma (already proven in PB / CPB) says the rg has no
// matching row. The composition is a boolean AND; soundness composes.
