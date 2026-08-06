module SPARQL11.Algebra.BGPRefinement

// ===================================================================
// LAYER 2 of the G3/M3 query-rung reduction
// (docs/designissues/2026-08-06-query-rung-design.md):
//
//   "simple matching of a BGP over a FIXED graph is already the
//    verified evaluator's core ...; the statement is that the
//    evaluator's solution set over `rdfs_closure g` equals
//    { mu | mu(BGP) subset-of rdfs_closure g, mu minimal-scoped }"
//
// This module proves BOTH HALVES of that set equality against the
// SHIPPING evaluator -- `SPARQL11.Algebra.eval_bgp`, the function the
// engine actually calls -- for an ARBITRARY fixed graph, and (finding
// RT-2's generalisation) at an ARBITRARY store carrying the relevant
// probe property, which is what reaches the selective-index store the
// shipping ASK path builds. Parts 1-6 and 8 are SOUNDNESS; Parts 2c
// and 9-12 are COMPLETENESS (2026-08-06), which discharges finding
// BR-4 below. Read BR-4 and BR-5 before the completeness theorems:
// BR-5 in particular corrects the SHAPE of the completeness
// statement, and that correction is a statement fix, not a
// proof-engineering compromise. Nothing
// here mentions entailment: per SPARQL 1.1 Entailment Regimes section
// 2, a regime redefines BGP matching only, so layer 2 is
// entailment-agnostic and layer 3 instantiates it at the closure
// graph. That is also why the module is named
// `SPARQL11.Algebra.BGPRefinement` and not `SPARQL.Entailment.*`:
// it sits in the `SPARQL11.Algebra.Spec` / `SPARQL11.Algebra.
// Refinement` family, refines a named shipping function of
// `SPARQL11.Algebra`, and mentions no entailment relation.
//
// It continues SPARQL11.Algebra.Refinement.fst, whose Part 14 stops
// at ONE triple pattern (`theorem_tp_match_instantiates`). Everything
// between one pattern and `eval_bgp` -- the cost-based pattern
// reordering, the index probe, the fuel-bounded fan-out -- is new
// here.
//
// -------------------------------------------------------------------
// FINDINGS -- READ BEFORE READING THE THEOREMS
// -------------------------------------------------------------------
//
// BR-1. THE FULLTEXT TRIPLE PATTERN IS NOT SUBSET-MATCHING AT ALL.
//   `eval_single_tp_store` (SPARQL11.Algebra.fst:2789) dispatches to
//   `eval_fulltext_tp_store` whenever the pattern predicate is the
//   IRI `SPARQL.FullText.fulltext_query_pred` and the object is a
//   decodable arguments literal. That path binds the SUBJECT ONLY
//   (`try_bind_subject tp.tp_s t.s mu`) and never binds or checks the
//   pattern's predicate or object against the matched triple. So for
//   such a pattern the result mapping mu does NOT satisfy
//   `instantiate_tp tp mu == Some t` for any t of the graph -- the
//   engine is deliberately computing a search, not a match. It also
//   applies `ftq_limit`, which TRUNCATES the solution set.
//   Consequence for this module: the subset-matching characterisation
//   is FALSE without excluding that predicate, so `tp_not_fulltext`
//   is an explicit hypothesis (`tp_frag`) rather than a silent
//   assumption. This is not a corner case of the proof -- it is a
//   documented extension whose semantics is outside SPARQL 1.1
//   section 18.3.1.
//
// BR-2. QUERY BLANK NODES ARE CONSTANTS, NOT NON-DISTINGUISHED
//   VARIABLES. SPARQL 1.1 section 18.3.1 defines BGP matching with a
//   blank-node renaming: mu is a solution when there EXISTS sigma
//   from the BGP's blank nodes to RDF terms with
//   mu(sigma(BGP)) a subgraph of G. The shipping `try_bind_subject`
//   (SPARQL11.Algebra.fst:2684) matches `PS_BNode b` only against a
//   data blank node with the SAME LABEL b, and `try_bind_term`
//   (:2708) does the same for `PT_BNode`. So the engine implements
//   sigma = identity. Every theorem below is therefore stated with
//   the identity renaming built in (`instantiate_tp p mu == Some t`,
//   no sigma), which is exactly what the engine computes and is
//   SOUND for a BGP containing no blank nodes -- the case the
//   entailment-regime suite exercises. The general statement needs
//   the existential sigma and is not proved here.
//
// BR-3. THE SUBSET-MATCH CHARACTERISATION IS A SET STATEMENT, NOT A
//   MULTISET ONE. `eval_bgp` returns a `solution_sequence` (a list).
//   The engine's own `store_search` may return the same triple twice
//   if the underlying `rdf_graph` list carries a duplicate, and the
//   fan-out then carries the duplicate into the result. Section
//   18.3.1's Card[mu] = 1 clause therefore needs a no-duplicates
//   hypothesis on the graph, which is NOT assumed below: the theorems
//   are membership statements (`memP mu (eval_bgp b g) ==> ...`),
//   which is the direction layer 3 consumes and which is unaffected.
//
// BR-4. COMPLETENESS WAS BLOCKED ON INDEX COMPLETENESS.
//   DISCHARGED 2026-08-06 (Parts 2c, 9, 10, 11, 12 below). The
//   original text, kept because both of its claims turned out to be
//   right and both shaped the fix:
//
//     "The converse ('every subset-matching mu is in `eval_bgp b g`')
//      needs: every graph triple satisfying the probe's bound
//      positions is returned by `ig_search`. `ig_search`
//      (SPARQL11.Algebra.fst:236) narrows to ONE bucket chosen by
//      `pick_smaller_bucket` over six candidates. Completeness is
//      proved today for the PREDICATE bucket only
//      (RDF.Indexed.Completeness.lemma_build_indexed_complete_pred,
//      2026-08-05); there is no analogue for ig_subj / ig_obj / ig_sp
//      / ig_po / ig_so. Worse for the object-keyed buckets: the probe
//      accepts a candidate on `rdf_term_eq` (coarse -- see finding
//      SR-2 of SPARQL11.Algebra.Refinement) while the bucket keys on
//      `term_to_key_opt` (byte-exact), so "x"@en and "x"@EN are
//      probe-equal and land in different buckets. Completeness of
//      `ig_search` in the object-bound case is thus not merely
//      unproved, it is expected to be FALSE outside the `term_exact`
//      fragment."
//
//   HOW EACH WAS CLOSED.
//   (a) The five missing bucket lemmas are one line each at
//       `RDF.Indexed.Completeness.lemma_build_bucket_complete`, which
//       was already GENERIC over `key_of`; see that module's stage 6.
//       The three option-keyed buckets (obj / po / so) get a
//       conditional statement -- "for triples whose key exists" --
//       because `build_bucket` genuinely files a literal-object
//       triple in no binding at all.
//   (b) The falsity claim is correct and is handled by the FRAGMENT,
//       not by weakening: `R.term_exact o` says `rdf_term_eq` is
//       identity AT `o`, so inside it probe-match implies key-match
//       and the "x"@en / "x"@EN split cannot happen. It appears as
//       the explicit precondition `bound_obj_exact` on
//       `lemma_ig_search_complete`, and it is the same `term_exact`
//       layer 2 already carries in `bgp_frag` / `graph_frag` -- not a
//       new hypothesis class.
//
//   Part 2c proves completeness at `build_indexed_selective` for an
//   ARBITRARY `needs`, exactly as Part 2b does for soundness, and for
//   the same reason: `ig_search` reads every bucket behind its own
//   `ig_built.bn_*` gate, so an OMITTED bucket is never offered as a
//   candidate and `bucket_cand_complete t None` is vacuously true.
//   Finding RT-2's "nothing about the selective store makes
//   completeness easier" is right -- and nothing makes it harder
//   either.
//
//   Soundness -- Parts 1-6 and 8 -- still needs none of it, because
//   `triple_matches_bound` re-checks every candidate against the
//   ACTUAL bound before returning it.
//
// BR-5. THE COMPLETE STATEMENT IS AN ANSWER EQUALITY, NOT A LIST
//   MEMBERSHIP. `memP muf (eval_bgp b g)` for a CALLER-SUPPLIED `muf`
//   is false, and no index lemma can rescue it: `solution_mapping` is
//   an association LIST and `sm_bind` conses
//   (SPARQL11.Algebra.fst:103), so the evaluator emits exactly one
//   permutation of the bindings -- the one `choose_best_tp`'s cost
//   ordering over the actual data dictates. Two patterns and two
//   variables suffice to exhibit a `muf` with the same bindings in the
//   other order. What IS proved is `theorem_eval_bgp_store_complete`
//   (the engine returns a `muo` that `muf` extends) and
//   `theorem_eval_bgp_store_complete_answer` (that `muo` instantiates
//   the BGP to the SAME triples). Everything downstream --
//   SPARQL11.EntailmentRegime.RDFS in full -- speaks
//   `instantiate_bgp q mu`, so this is the form the composition
//   needs. The residual is the DOMAIN clause `dom(mu) = var(BGP)`
//   that Part 6 already names as a separate commit.
//
// No admit, no --lax, no --admit_smt_queries, no assume. z3 4.13.3.
// Zero change to any shipping module: this file only reads them.
// ===================================================================

open FStar.List.Tot
open RDF.Graph.Executable
open SPARQL11.Algebra

module S  = SPARQL11.Algebra.Spec
module R  = SPARQL11.Algebra.Refinement
module Ml = OWL.Semantics.MemLemmas
module IC = RDF.Indexed.Completeness
module Lh = RDF.List.Helpers
module T  = FStar.Tactics

#push-options "--z3rlimit 120 --fuel 2 --ifuel 2"

(** ====================================================================== **)
(** Part 1: the fragment hypotheses                                        **)
(** ====================================================================== **)

/// Finding BR-1: the fulltext predicate is not doing BGP matching.
/// Excluded by name, decidably, rather than assumed away.
let tp_not_fulltext (tp : triple_pattern) : bool =
  match tp.tp_p with
  | PT_IRI p -> not (p = SPARQL.FullText.fulltext_query_pred)
  | _ -> true

/// A triple pattern inside the fragment: RDF 1.2 triple terms
/// quarantined (as in SPARQL11.Algebra.Refinement Part 14), literal
/// constants exact (finding SR-1's `rdf_term_eq` coarseness), and not
/// the fulltext escape hatch.
let tp_frag (tp : triple_pattern) : prop =
  R.psub_tt_free tp.tp_s /\
  R.ptrm_tt_free tp.tp_p /\ R.ptrm_exact tp.tp_p /\
  R.ptrm_tt_free tp.tp_o /\ R.ptrm_exact tp.tp_o /\
  tp_not_fulltext tp == true

let bgp_frag (b : bgp) : prop =
  forall (p : triple_pattern). List.Tot.memP p b ==> tp_frag p

/// The graph-side half of the same fragment: every object term is
/// exact and triple-term free. Subjects and predicates need no
/// condition (`subject_eq` and IRI equality are already identity).
let graph_frag (g : rdf_graph) : prop =
  forall (t : triple). List.Tot.memP t g ==>
    (R.term_exact t.o /\ R.term_tt_free t.o)

/// "mu(BGP) is a subgraph of G": the FIRST conjunct of
/// `SPARQL11.Algebra.Spec.bgp_sol_spec`, transcribed verbatim with
/// `inst` instantiated at the shipping `instantiate_tp` and `tp`
/// at the shipping `triple_pattern`. Kept as its own name so the
/// theorems below read as the spec clause they discharge.
let bgp_subgraph_clause (b : bgp) (g : rdf_graph) (mu : solution_mapping) : prop =
  forall (p : triple_pattern). List.Tot.memP p b ==>
    (exists (t : triple). instantiate_tp p mu == Some t /\ List.Tot.memP t g)

(** ====================================================================== **)
(** Part 2: the index probe returns graph triples                          **)
(** ====================================================================== **)

/// The `so` bucket's weak well-formedness. OWL.Semantics.MemLemmas
/// proves this for pred / subj / obj / sp / po; `so` was never needed
/// there. Same three-line shape.
let lemma_build_indexed_wf_so_weak (g : rdf_graph)
  : Lemma
    (ensures (let ig = build_indexed g in
              forall (k : string) (t : triple).
                List.Tot.memP t (bucket_lookup ig.ig_so k) ==>
                List.Tot.memP t ig.ig_triples)) =
  let ig = build_indexed g in
  Ml.lemma_build_bucket_ok bucket_key_so g;
  assert (ig.ig_so == build_bucket bucket_key_so g);
  introduce forall (k : string) (t : triple).
      List.Tot.memP t (bucket_lookup ig.ig_so k) ==> List.Tot.memP t ig.ig_triples
  with introduce List.Tot.memP t (bucket_lookup ig.ig_so k) ==>
                 List.Tot.memP t ig.ig_triples
  with _ . Ml.lemma_tree_ok_lookup bucket_key_so g ig.ig_so k t

/// `triple_matches_bound` only ever returns elements of its input.
/// (RDF.Store.Columnar.DeltaMerge proves the `mem_triple` analogue
/// for the DECIDABLE membership; this is the propositional `memP`
/// form the refinement layer speaks, and does not depend on
/// `triple_eq`.)
let rec lemma_memP_tmb_acc (b : triple_pattern_bound) (ts acc : list triple) (t : triple)
  : Lemma (requires List.Tot.memP t (triple_matches_bound_acc b ts acc))
          (ensures  List.Tot.memP t ts \/ List.Tot.memP t acc)
          (decreases ts) =
  match ts with
  | [] -> ()
  | x :: rest ->
    let subj_ok = match b.bs with | None -> true | Some s -> subject_eq s x.s in
    let pred_ok = match b.bp with | None -> true | Some p -> p = x.p in
    let obj_ok  = match b.bo with | None -> true | Some o -> rdf_term_eq o x.o in
    if subj_ok && pred_ok && obj_ok
    then lemma_memP_tmb_acc b rest (x :: acc) t
    else lemma_memP_tmb_acc b rest acc t

let lemma_memP_triple_matches_bound (b : triple_pattern_bound) (ts : list triple) (t : triple)
  : Lemma (requires List.Tot.memP t (triple_matches_bound b ts))
          (ensures  List.Tot.memP t ts) =
  FStar.List.Tot.Properties.rev_memP (triple_matches_bound_acc b ts []) t;
  lemma_memP_tmb_acc b ts [] t

/// A narrowing candidate is SOUND when everything it offers is a
/// graph triple. `ig_search` picks among six of these plus the
/// always-present full list.
let bucket_cand_sound (ig : indexed_graph) (o : option (list triple)) : prop =
  forall (t : triple). Some? o /\ List.Tot.memP t (Some?.v o) ==>
                       List.Tot.memP t ig.ig_triples

let lemma_pick_smaller_bucket_sound (ig : indexed_graph) (a b : option (list triple))
  : Lemma (requires bucket_cand_sound ig a /\ bucket_cand_sound ig b)
          (ensures  bucket_cand_sound ig (pick_smaller_bucket a b)) = ()

/// THE INDEX PROBE IS SOUND: every triple `ig_search` serves for a
/// bound is a member of the graph the index was built from. This is
/// the lemma SPARQL11.Algebra.Refinement's banner records as missing
/// ("bucket_lookup's result is a sublist of the indexed sequence, a
/// lemma about RDF.Indexed's balanced-tree index that does not exist
/// yet") -- for the BGP probe, which is where it is load-bearing.
#push-options "--z3rlimit 400 --fuel 2 --ifuel 4"
let lemma_ig_search_sound (g : rdf_graph) (b : triple_pattern_bound) (t : triple)
  : Lemma (requires List.Tot.memP t (ig_search (build_indexed g) b))
          (ensures  List.Tot.memP t g) =
  let ig = build_indexed g in
  Ml.lemma_build_indexed_wf_pred g;
  Ml.lemma_build_indexed_wf_subj_weak g;
  Ml.lemma_build_indexed_wf_obj_weak g;
  Ml.lemma_build_indexed_wf_sp_weak g;
  Ml.lemma_build_indexed_wf_po_weak g;
  lemma_build_indexed_wf_so_weak g;
  // Replicated exactly from `ig_search` so the names line up and the
  // definition delta-reduces onto them.
  let pred_b = match b.bp with
    | Some p -> if ig.ig_built.bn_pred then Some (bucket_lookup ig.ig_pred p) else None
    | None -> None in
  let subj_b = match b.bs with
    | Some s -> if ig.ig_built.bn_subj then Some (bucket_lookup ig.ig_subj (subject_to_key s)) else None
    | None -> None in
  let obj_b = match b.bo with
    | Some o ->
      if ig.ig_built.bn_obj then
        (match term_to_key_opt o with
         | Some k -> Some (bucket_lookup ig.ig_obj k)
         | None -> None)
      else None
    | None -> None in
  let sp_b = match b.bs, b.bp with
    | Some s, Some p -> if ig.ig_built.bn_sp then Some (bucket_lookup ig.ig_sp (sp_key s p)) else None
    | _ -> None in
  let po_b = match b.bp, b.bo with
    | Some p, Some o ->
      if ig.ig_built.bn_po then
        (match po_key_opt p o with
         | Some k -> Some (bucket_lookup ig.ig_po k)
         | None -> None)
      else None
    | _ -> None in
  let so_b = match b.bs, b.bo with
    | Some s, Some o ->
      if ig.ig_built.bn_so then
        (match so_key_opt s o with
         | Some k -> Some (bucket_lookup ig.ig_so k)
         | None -> None)
      else None
    | _ -> None in
  assert (bucket_cand_sound ig pred_b);
  assert (bucket_cand_sound ig subj_b);
  assert (bucket_cand_sound ig obj_b);
  assert (bucket_cand_sound ig sp_b);
  assert (bucket_cand_sound ig po_b);
  assert (bucket_cand_sound ig so_b);
  lemma_pick_smaller_bucket_sound ig sp_b po_b;
  lemma_pick_smaller_bucket_sound ig (pick_smaller_bucket sp_b po_b) so_b;
  lemma_pick_smaller_bucket_sound ig pred_b subj_b;
  lemma_pick_smaller_bucket_sound ig (pick_smaller_bucket pred_b subj_b) obj_b;
  let compound = pick_smaller_bucket (pick_smaller_bucket sp_b po_b) so_b in
  let single   = pick_smaller_bucket (pick_smaller_bucket pred_b subj_b) obj_b in
  lemma_pick_smaller_bucket_sound ig compound single;
  let candidate = pick_smaller_bucket compound single in
  let pool = match candidate with
    | Some bucket -> bucket
    | None -> ig.ig_triples in
  assert (forall (x : triple). List.Tot.memP x pool ==> List.Tot.memP x ig.ig_triples);
  assert (ig_search ig b == triple_matches_bound b pool);
  lemma_memP_triple_matches_bound b pool t;
  assert (ig.ig_triples == g)
#pop-options

let lemma_store_search_sound (g : rdf_graph) (b : triple_pattern_bound) (t : triple)
  : Lemma (requires List.Tot.memP t (store_search (graph_to_store g) b))
          (ensures  List.Tot.memP t g) =
  lemma_ig_search_sound g b t

(** ====================================================================== **)
(** Part 2b: THE SELECTIVE-INDEX PROBE IS SOUND (closes finding RT-2)      **)
(**                                                                        **)
(** `build_indexed_selective needs g` (RDF.Indexed.fsti:651-661) is what   **)
(** `graph_to_store_for` actually builds (SPARQL11.Algebra.fst:3588-3589) **)
(** -- the store `eval_pattern`/`eval_ask_query` run on, NOT the           **)
(** `build_indexed g` (== `build_indexed_selective all_bucket_needs g`)    **)
(** `lemma_ig_search_sound` above is proved for. The two constructors      **)
(** share ONE field unconditionally -- `ig_triples = g` -- and differ     **)
(** only in which of the six buckets get `build_bucket key_of g` versus   **)
(** `BLeaf` (the RDF.Indexed.fsti record literal). `ig_search` already     **)
(** reads every bucket behind its own `ig.ig_built.bn_*` gate (part 2     **)
(** above, replicated again below), so an OMITTED bucket is never looked  **)
(** up: its candidate is `None`, not an empty-but-consulted                **)
(** `bucket_lookup` result -- `bucket_cand_sound ig None` is vacuously     **)
(** true by definition. The six weak well-formedness lemmas below         **)
(** therefore hold for EVERY `needs`, not just `all_bucket_needs`, by      **)
(** splitting on the one flag each guards: the TRUE branch is the         **)
(** identical `build_bucket`/`tree_ok` argument `Ml.lemma_build_indexed_   **)
(** wf_*` already makes (`Ml.lemma_build_bucket_ok` / `Ml.lemma_tree_ok_   **)
(** lookup` are both generic in `key_of` and the source list -- neither   **)
(** mentions `build_indexed`); the FALSE branch reduces the bucket to     **)
(** `BLeaf`, whose `bucket_lookup` is `[]` by `RDF.Indexed.fsti`'s own     **)
(** definition (`bucket_lookup BLeaf k = []`), so the implication is      **)
(** vacuous. This is exactly the "an omitted bucket serves nothing"       **)
(** case; there is no "falls back to the full list" case to prove HERE    **)
(** (that fallback is `ig_search`'s `pool` computation, unchanged, and is **)
(** re-verified below in `lemma_ig_search_sound_selective`'s own body).   **)
(** ====================================================================== **)

let lemma_build_indexed_selective_wf_pred (needs : bucket_needs) (g : rdf_graph)
  : Lemma
    (ensures (let ig = build_indexed_selective needs g in
              forall (k : string) (t : triple).
                List.Tot.memP t (bucket_lookup ig.ig_pred k) ==>
                List.Tot.memP t ig.ig_triples)) =
  let ig = build_indexed_selective needs g in
  if needs.bn_pred then begin
    Ml.lemma_build_bucket_ok bucket_key_pred g;
    assert (ig.ig_pred == build_bucket bucket_key_pred g);
    introduce forall (k : string) (t : triple).
        List.Tot.memP t (bucket_lookup ig.ig_pred k) ==> List.Tot.memP t ig.ig_triples
    with introduce List.Tot.memP t (bucket_lookup ig.ig_pred k) ==> List.Tot.memP t ig.ig_triples
    with _ . Ml.lemma_tree_ok_lookup bucket_key_pred g ig.ig_pred k t
  end else
    assert (ig.ig_pred == BLeaf)

let lemma_build_indexed_selective_wf_subj_weak (needs : bucket_needs) (g : rdf_graph)
  : Lemma
    (ensures (let ig = build_indexed_selective needs g in
              forall (k : string) (t : triple).
                List.Tot.memP t (bucket_lookup ig.ig_subj k) ==>
                List.Tot.memP t ig.ig_triples)) =
  let ig = build_indexed_selective needs g in
  if needs.bn_subj then begin
    Ml.lemma_build_bucket_ok bucket_key_subj g;
    assert (ig.ig_subj == build_bucket bucket_key_subj g);
    introduce forall (k : string) (t : triple).
        List.Tot.memP t (bucket_lookup ig.ig_subj k) ==> List.Tot.memP t ig.ig_triples
    with introduce List.Tot.memP t (bucket_lookup ig.ig_subj k) ==> List.Tot.memP t ig.ig_triples
    with _ . Ml.lemma_tree_ok_lookup bucket_key_subj g ig.ig_subj k t
  end else
    assert (ig.ig_subj == BLeaf)

let lemma_build_indexed_selective_wf_obj_weak (needs : bucket_needs) (g : rdf_graph)
  : Lemma
    (ensures (let ig = build_indexed_selective needs g in
              forall (k : string) (t : triple).
                List.Tot.memP t (bucket_lookup ig.ig_obj k) ==>
                List.Tot.memP t ig.ig_triples)) =
  let ig = build_indexed_selective needs g in
  if needs.bn_obj then begin
    Ml.lemma_build_bucket_ok bucket_key_obj g;
    assert (ig.ig_obj == build_bucket bucket_key_obj g);
    introduce forall (k : string) (t : triple).
        List.Tot.memP t (bucket_lookup ig.ig_obj k) ==> List.Tot.memP t ig.ig_triples
    with introduce List.Tot.memP t (bucket_lookup ig.ig_obj k) ==> List.Tot.memP t ig.ig_triples
    with _ . Ml.lemma_tree_ok_lookup bucket_key_obj g ig.ig_obj k t
  end else
    assert (ig.ig_obj == BLeaf)

let lemma_build_indexed_selective_wf_sp_weak (needs : bucket_needs) (g : rdf_graph)
  : Lemma
    (ensures (let ig = build_indexed_selective needs g in
              forall (k : string) (t : triple).
                List.Tot.memP t (bucket_lookup ig.ig_sp k) ==>
                List.Tot.memP t ig.ig_triples)) =
  let ig = build_indexed_selective needs g in
  if needs.bn_sp then begin
    Ml.lemma_build_bucket_ok bucket_key_sp g;
    assert (ig.ig_sp == build_bucket bucket_key_sp g);
    introduce forall (k : string) (t : triple).
        List.Tot.memP t (bucket_lookup ig.ig_sp k) ==> List.Tot.memP t ig.ig_triples
    with introduce List.Tot.memP t (bucket_lookup ig.ig_sp k) ==> List.Tot.memP t ig.ig_triples
    with _ . Ml.lemma_tree_ok_lookup bucket_key_sp g ig.ig_sp k t
  end else
    assert (ig.ig_sp == BLeaf)

let lemma_build_indexed_selective_wf_po_weak (needs : bucket_needs) (g : rdf_graph)
  : Lemma
    (ensures (let ig = build_indexed_selective needs g in
              forall (k : string) (t : triple).
                List.Tot.memP t (bucket_lookup ig.ig_po k) ==>
                List.Tot.memP t ig.ig_triples)) =
  let ig = build_indexed_selective needs g in
  if needs.bn_po then begin
    Ml.lemma_build_bucket_ok bucket_key_po g;
    assert (ig.ig_po == build_bucket bucket_key_po g);
    introduce forall (k : string) (t : triple).
        List.Tot.memP t (bucket_lookup ig.ig_po k) ==> List.Tot.memP t ig.ig_triples
    with introduce List.Tot.memP t (bucket_lookup ig.ig_po k) ==> List.Tot.memP t ig.ig_triples
    with _ . Ml.lemma_tree_ok_lookup bucket_key_po g ig.ig_po k t
  end else
    assert (ig.ig_po == BLeaf)

let lemma_build_indexed_selective_wf_so_weak (needs : bucket_needs) (g : rdf_graph)
  : Lemma
    (ensures (let ig = build_indexed_selective needs g in
              forall (k : string) (t : triple).
                List.Tot.memP t (bucket_lookup ig.ig_so k) ==>
                List.Tot.memP t ig.ig_triples)) =
  let ig = build_indexed_selective needs g in
  if needs.bn_so then begin
    Ml.lemma_build_bucket_ok bucket_key_so g;
    assert (ig.ig_so == build_bucket bucket_key_so g);
    introduce forall (k : string) (t : triple).
        List.Tot.memP t (bucket_lookup ig.ig_so k) ==> List.Tot.memP t ig.ig_triples
    with introduce List.Tot.memP t (bucket_lookup ig.ig_so k) ==> List.Tot.memP t ig.ig_triples
    with _ . Ml.lemma_tree_ok_lookup bucket_key_so g ig.ig_so k t
  end else
    assert (ig.ig_so == BLeaf)

/// THE SELECTIVE-INDEX PROBE IS SOUND: the exact analogue of
/// `lemma_ig_search_sound` above, for `build_indexed_selective needs g`
/// at an ARBITRARY `needs`. Body is `lemma_ig_search_sound`'s body
/// verbatim (same replication of `ig_search`'s own case split, so the
/// names line up and the definition delta-reduces onto them) with the
/// six `Ml.lemma_build_indexed_wf_*` calls replaced by the six
/// `_selective` lemmas just above.
#push-options "--z3rlimit 400 --fuel 2 --ifuel 4"
let lemma_ig_search_sound_selective
      (needs : bucket_needs) (g : rdf_graph) (b : triple_pattern_bound) (t : triple)
  : Lemma (requires List.Tot.memP t (ig_search (build_indexed_selective needs g) b))
          (ensures  List.Tot.memP t g) =
  let ig = build_indexed_selective needs g in
  lemma_build_indexed_selective_wf_pred needs g;
  lemma_build_indexed_selective_wf_subj_weak needs g;
  lemma_build_indexed_selective_wf_obj_weak needs g;
  lemma_build_indexed_selective_wf_sp_weak needs g;
  lemma_build_indexed_selective_wf_po_weak needs g;
  lemma_build_indexed_selective_wf_so_weak needs g;
  let pred_b = match b.bp with
    | Some p -> if ig.ig_built.bn_pred then Some (bucket_lookup ig.ig_pred p) else None
    | None -> None in
  let subj_b = match b.bs with
    | Some s -> if ig.ig_built.bn_subj then Some (bucket_lookup ig.ig_subj (subject_to_key s)) else None
    | None -> None in
  let obj_b = match b.bo with
    | Some o ->
      if ig.ig_built.bn_obj then
        (match term_to_key_opt o with
         | Some k -> Some (bucket_lookup ig.ig_obj k)
         | None -> None)
      else None
    | None -> None in
  let sp_b = match b.bs, b.bp with
    | Some s, Some p -> if ig.ig_built.bn_sp then Some (bucket_lookup ig.ig_sp (sp_key s p)) else None
    | _ -> None in
  let po_b = match b.bp, b.bo with
    | Some p, Some o ->
      if ig.ig_built.bn_po then
        (match po_key_opt p o with
         | Some k -> Some (bucket_lookup ig.ig_po k)
         | None -> None)
      else None
    | _ -> None in
  let so_b = match b.bs, b.bo with
    | Some s, Some o ->
      if ig.ig_built.bn_so then
        (match so_key_opt s o with
         | Some k -> Some (bucket_lookup ig.ig_so k)
         | None -> None)
      else None
    | _ -> None in
  assert (bucket_cand_sound ig pred_b);
  assert (bucket_cand_sound ig subj_b);
  assert (bucket_cand_sound ig obj_b);
  assert (bucket_cand_sound ig sp_b);
  assert (bucket_cand_sound ig po_b);
  assert (bucket_cand_sound ig so_b);
  lemma_pick_smaller_bucket_sound ig sp_b po_b;
  lemma_pick_smaller_bucket_sound ig (pick_smaller_bucket sp_b po_b) so_b;
  lemma_pick_smaller_bucket_sound ig pred_b subj_b;
  lemma_pick_smaller_bucket_sound ig (pick_smaller_bucket pred_b subj_b) obj_b;
  let compound = pick_smaller_bucket (pick_smaller_bucket sp_b po_b) so_b in
  let single   = pick_smaller_bucket (pick_smaller_bucket pred_b subj_b) obj_b in
  lemma_pick_smaller_bucket_sound ig compound single;
  let candidate = pick_smaller_bucket compound single in
  let pool = match candidate with
    | Some bucket -> bucket
    | None -> ig.ig_triples in
  assert (forall (x : triple). List.Tot.memP x pool ==> List.Tot.memP x ig.ig_triples);
  assert (ig_search ig b == triple_matches_bound b pool);
  lemma_memP_triple_matches_bound b pool t;
  assert (ig.ig_triples == g)
#pop-options

/// The store-level form, at the ARBITRARY-`p` selective store: the
/// exact analogue of `lemma_store_search_sound`, one call deeper
/// (`bucket_needs_of_pattern p` instead of `all_bucket_needs`).
let lemma_store_search_sound_for (p : group_graph_pattern) (g : rdf_graph) (b : triple_pattern_bound) (t : triple)
  : Lemma (requires List.Tot.memP t (store_search (graph_to_store_for p g) b))
          (ensures  List.Tot.memP t g) =
  lemma_ig_search_sound_selective (bucket_needs_of_pattern p) g b t

(** ====================================================================== **)
(** Part 2c: THE INDEX PROBE IS COMPLETE (closes finding BR-4)             **)
(**                                                                        **)
(** The mirror of parts 2 and 2b: every graph triple that SATISFIES the    **)
(** bound is served by `ig_search`, at `build_indexed_selective needs g`   **)
(** for an ARBITRARY `needs` (hence at both `graph_to_store` and the       **)
(** shipping `graph_to_store_for`). Two things make it go through, and     **)
(** both are recorded as findings rather than assumed:                     **)
(**                                                                        **)
(**  (a) The five missing bucket-completeness lemmas are instantiations    **)
(**      of `RDF.Indexed.Completeness.lemma_build_bucket_complete`, which  **)
(**      is generic in `key_of`. Each is gated on its own `needs.bn_*`     **)
(**      flag, because a bucket that was never built is `BLeaf` and        **)
(**      serves nothing -- but `ig_search` never offers it either, so      **)
(**      `bucket_cand_complete t None` (vacuously true) covers exactly     **)
(**      that case. This is part 2b's argument with the polarity flipped.  **)
(**                                                                        **)
(**  (b) The probe accepts an object candidate on `rdf_term_eq` while the  **)
(**      bucket keys on `term_to_key_opt`, so completeness IS false in     **)
(**      general -- BR-4 predicted this correctly. `bound_obj_exact`       **)
(**      names the fragment where `rdf_term_eq` collapses to identity at   **)
(**      the bound object, and there probe-match implies key-match. It is  **)
(**      the same `R.term_exact` the module already carries in `bgp_frag`  **)
(**      and `graph_frag`, not a new hypothesis class.                     **)
(** ====================================================================== **)

/// `triple_matches_bound`'s acceptance test, transcribed from
/// SPARQL11.Algebra.fst:194-206's inline conjunction (the same
/// transcription discipline `lemma_ig_search_sound` uses for
/// `ig_search`'s six candidates).
let bound_holds (b : triple_pattern_bound) (t : triple) : bool =
  (match b.bs with | None -> true | Some s -> subject_eq s t.s) &&
  (match b.bp with | None -> true | Some p -> p = t.p) &&
  (match b.bo with | None -> true | Some o -> rdf_term_eq o t.o)

/// `subject_eq` IS subject identity -- no fragment condition needed
/// (both constructors carry a plain `string`, an `eqtype`). Proved
/// locally rather than imported from
/// RDF.Entailment.Simple.Refinement so this module keeps its
/// dependency set to the algebra side.
let lemma_subject_eq_ident (s1 s2 : subject)
  : Lemma (requires subject_eq s1 s2 == true) (ensures s1 == s2) =
  match s1, s2 with
  | S_IRI _, S_IRI _ -> ()
  | S_BNode _, S_BNode _ -> ()
  | _, _ -> ()

/// The filter keeps every input element that passes the bound.
let rec lemma_tmb_acc_complete (b : triple_pattern_bound) (ts acc : list triple) (t : triple)
  : Lemma (requires (List.Tot.memP t ts /\ bound_holds b t == true) \/ List.Tot.memP t acc)
          (ensures  List.Tot.memP t (triple_matches_bound_acc b ts acc))
          (decreases ts) =
  match ts with
  | [] -> ()
  | x :: rest ->
    let subj_ok = match b.bs with | None -> true | Some s -> subject_eq s x.s in
    let pred_ok = match b.bp with | None -> true | Some p -> p = x.p in
    let obj_ok  = match b.bo with | None -> true | Some o -> rdf_term_eq o x.o in
    if subj_ok && pred_ok && obj_ok
    then lemma_tmb_acc_complete b rest (x :: acc) t
    else lemma_tmb_acc_complete b rest acc t

let lemma_triple_matches_bound_complete (b : triple_pattern_bound) (ts : list triple) (t : triple)
  : Lemma (requires List.Tot.memP t ts /\ bound_holds b t == true)
          (ensures  List.Tot.memP t (triple_matches_bound b ts)) =
  lemma_tmb_acc_complete b ts [] t;
  FStar.List.Tot.Properties.rev_memP (triple_matches_bound_acc b ts []) t

/// A narrowing candidate is COMPLETE FOR `t` when, if it is offered at
/// all, it contains `t`. The mirror of `bucket_cand_sound`; a `None`
/// candidate is vacuously complete, which is exactly right -- an
/// unoffered bucket cannot lose a triple, and `ig_search` falls back
/// to the full list when every candidate is `None`.
let bucket_cand_complete (t : triple) (o : option (list triple)) : prop =
  Some? o ==> List.Tot.memP t (Some?.v o)

let lemma_pick_smaller_bucket_complete (t : triple) (a b : option (list triple))
  : Lemma (requires bucket_cand_complete t a /\ bucket_cand_complete t b)
          (ensures  bucket_cand_complete t (pick_smaller_bucket a b)) = ()

/// The fragment condition on the PROBE side: a bound object term whose
/// `rdf_term_eq` class is a singleton. See the Part 2c banner, (b).
let bound_obj_exact (b : triple_pattern_bound) : prop =
  forall (o : rdf_term). b.bo == Some o ==> R.term_exact o

/// The six per-bucket completeness facts at the SELECTIVE constructor,
/// each gated on its own flag (banner (a)). Bodies are one call to the
/// generic `IC.lemma_build_bucket_complete` per graph triple.
let lemma_build_indexed_selective_complete_pred (needs : bucket_needs) (g : rdf_graph)
  : Lemma
    (ensures (let ig = build_indexed_selective needs g in
              needs.bn_pred ==>
              (forall (t : triple).
                 List.Tot.memP t g ==>
                 List.Tot.memP t (bucket_lookup ig.ig_pred t.p)))) =
  let ig = build_indexed_selective needs g in
  if needs.bn_pred then begin
    assert (ig.ig_pred == build_bucket bucket_key_pred g);
    let aux (t : triple) : Lemma
      (requires List.Tot.memP t g)
      (ensures List.Tot.memP t (bucket_lookup ig.ig_pred t.p)) =
      IC.lemma_build_bucket_complete bucket_key_pred g t.p t
    in FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
  end else ()

let lemma_build_indexed_selective_complete_subj (needs : bucket_needs) (g : rdf_graph)
  : Lemma
    (ensures (let ig = build_indexed_selective needs g in
              needs.bn_subj ==>
              (forall (t : triple).
                 List.Tot.memP t g ==>
                 List.Tot.memP t (bucket_lookup ig.ig_subj (subject_to_key t.s))))) =
  let ig = build_indexed_selective needs g in
  if needs.bn_subj then begin
    assert (ig.ig_subj == build_bucket bucket_key_subj g);
    let aux (t : triple) : Lemma
      (requires List.Tot.memP t g)
      (ensures List.Tot.memP t (bucket_lookup ig.ig_subj (subject_to_key t.s))) =
      IC.lemma_build_bucket_complete bucket_key_subj g (subject_to_key t.s) t
    in FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
  end else ()

let lemma_build_indexed_selective_complete_sp (needs : bucket_needs) (g : rdf_graph)
  : Lemma
    (ensures (let ig = build_indexed_selective needs g in
              needs.bn_sp ==>
              (forall (t : triple).
                 List.Tot.memP t g ==>
                 List.Tot.memP t (bucket_lookup ig.ig_sp (sp_key t.s t.p))))) =
  let ig = build_indexed_selective needs g in
  if needs.bn_sp then begin
    assert (ig.ig_sp == build_bucket bucket_key_sp g);
    let aux (t : triple) : Lemma
      (requires List.Tot.memP t g)
      (ensures List.Tot.memP t (bucket_lookup ig.ig_sp (sp_key t.s t.p))) =
      IC.lemma_build_bucket_complete bucket_key_sp g (sp_key t.s t.p) t
    in FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
  end else ()

let lemma_build_indexed_selective_complete_obj (needs : bucket_needs) (g : rdf_graph)
  : Lemma
    (ensures (let ig = build_indexed_selective needs g in
              needs.bn_obj ==>
              (forall (t : triple) (k : string).
                 List.Tot.memP t g /\ term_to_key_opt t.o == Some k ==>
                 List.Tot.memP t (bucket_lookup ig.ig_obj k)))) =
  let ig = build_indexed_selective needs g in
  if needs.bn_obj then begin
    assert (ig.ig_obj == build_bucket bucket_key_obj g);
    let aux (t : triple) (k : string) : Lemma
      (requires List.Tot.memP t g /\ term_to_key_opt t.o == Some k)
      (ensures List.Tot.memP t (bucket_lookup ig.ig_obj k)) =
      IC.lemma_build_bucket_complete bucket_key_obj g k t
    in FStar.Classical.forall_intro_2 (fun t -> FStar.Classical.move_requires (aux t))
  end else ()

let lemma_build_indexed_selective_complete_po (needs : bucket_needs) (g : rdf_graph)
  : Lemma
    (ensures (let ig = build_indexed_selective needs g in
              needs.bn_po ==>
              (forall (t : triple) (k : string).
                 List.Tot.memP t g /\ po_key_opt t.p t.o == Some k ==>
                 List.Tot.memP t (bucket_lookup ig.ig_po k)))) =
  let ig = build_indexed_selective needs g in
  if needs.bn_po then begin
    assert (ig.ig_po == build_bucket bucket_key_po g);
    let aux (t : triple) (k : string) : Lemma
      (requires List.Tot.memP t g /\ po_key_opt t.p t.o == Some k)
      (ensures List.Tot.memP t (bucket_lookup ig.ig_po k)) =
      IC.lemma_build_bucket_complete bucket_key_po g k t
    in FStar.Classical.forall_intro_2 (fun t -> FStar.Classical.move_requires (aux t))
  end else ()

let lemma_build_indexed_selective_complete_so (needs : bucket_needs) (g : rdf_graph)
  : Lemma
    (ensures (let ig = build_indexed_selective needs g in
              needs.bn_so ==>
              (forall (t : triple) (k : string).
                 List.Tot.memP t g /\ so_key_opt t.s t.o == Some k ==>
                 List.Tot.memP t (bucket_lookup ig.ig_so k)))) =
  let ig = build_indexed_selective needs g in
  if needs.bn_so then begin
    assert (ig.ig_so == build_bucket bucket_key_so g);
    let aux (t : triple) (k : string) : Lemma
      (requires List.Tot.memP t g /\ so_key_opt t.s t.o == Some k)
      (ensures List.Tot.memP t (bucket_lookup ig.ig_so k)) =
      IC.lemma_build_bucket_complete bucket_key_so g k t
    in FStar.Classical.forall_intro_2 (fun t -> FStar.Classical.move_requires (aux t))
  end else ()

#push-options "--z3rlimit 600 --fuel 2 --ifuel 4"
/// THE INDEX PROBE IS COMPLETE, at an ARBITRARY `needs`. Structure
/// mirrors `lemma_ig_search_sound_selective` branch for branch, with
/// `bucket_cand_sound` replaced by `bucket_cand_complete` throughout.
let lemma_ig_search_complete_selective
      (needs : bucket_needs) (g : rdf_graph) (b : triple_pattern_bound) (t : triple)
  : Lemma (requires List.Tot.memP t g /\ bound_holds b t == true /\ bound_obj_exact b)
          (ensures  List.Tot.memP t (ig_search (build_indexed_selective needs g) b)) =
  let ig = build_indexed_selective needs g in
  lemma_build_indexed_selective_complete_pred needs g;
  lemma_build_indexed_selective_complete_subj needs g;
  lemma_build_indexed_selective_complete_obj  needs g;
  lemma_build_indexed_selective_complete_sp   needs g;
  lemma_build_indexed_selective_complete_po   needs g;
  lemma_build_indexed_selective_complete_so   needs g;
  // Probe-match implies key-match, one position at a time. The subject
  // and predicate positions are identity already; the object position
  // is where `bound_obj_exact` earns its place.
  (match b.bs with
   | Some s -> lemma_subject_eq_ident s t.s
   | None -> ());
  assert (match b.bs with | Some s -> s == t.s | None -> True);
  assert (match b.bp with | Some p -> p == t.p | None -> True);
  assert (match b.bo with | Some o -> o == t.o | None -> True);
  // Replicated exactly from `ig_search`, as in the soundness proofs.
  let pred_b = match b.bp with
    | Some p -> if ig.ig_built.bn_pred then Some (bucket_lookup ig.ig_pred p) else None
    | None -> None in
  let subj_b = match b.bs with
    | Some s -> if ig.ig_built.bn_subj then Some (bucket_lookup ig.ig_subj (subject_to_key s)) else None
    | None -> None in
  let obj_b = match b.bo with
    | Some o ->
      if ig.ig_built.bn_obj then
        (match term_to_key_opt o with
         | Some k -> Some (bucket_lookup ig.ig_obj k)
         | None -> None)
      else None
    | None -> None in
  let sp_b = match b.bs, b.bp with
    | Some s, Some p -> if ig.ig_built.bn_sp then Some (bucket_lookup ig.ig_sp (sp_key s p)) else None
    | _ -> None in
  let po_b = match b.bp, b.bo with
    | Some p, Some o ->
      if ig.ig_built.bn_po then
        (match po_key_opt p o with
         | Some k -> Some (bucket_lookup ig.ig_po k)
         | None -> None)
      else None
    | _ -> None in
  let so_b = match b.bs, b.bo with
    | Some s, Some o ->
      if ig.ig_built.bn_so then
        (match so_key_opt s o with
         | Some k -> Some (bucket_lookup ig.ig_so k)
         | None -> None)
      else None
    | _ -> None in
  assert (ig.ig_built == needs);
  assert (bucket_cand_complete t pred_b);
  assert (bucket_cand_complete t subj_b);
  assert (bucket_cand_complete t obj_b);
  assert (bucket_cand_complete t sp_b);
  assert (bucket_cand_complete t po_b);
  assert (bucket_cand_complete t so_b);
  lemma_pick_smaller_bucket_complete t sp_b po_b;
  lemma_pick_smaller_bucket_complete t (pick_smaller_bucket sp_b po_b) so_b;
  lemma_pick_smaller_bucket_complete t pred_b subj_b;
  lemma_pick_smaller_bucket_complete t (pick_smaller_bucket pred_b subj_b) obj_b;
  let compound = pick_smaller_bucket (pick_smaller_bucket sp_b po_b) so_b in
  let single   = pick_smaller_bucket (pick_smaller_bucket pred_b subj_b) obj_b in
  lemma_pick_smaller_bucket_complete t compound single;
  let candidate = pick_smaller_bucket compound single in
  let pool = match candidate with
    | Some bucket -> bucket
    | None -> ig.ig_triples in
  assert (ig.ig_triples == g);
  assert (List.Tot.memP t pool);
  assert (ig_search ig b == triple_matches_bound b pool);
  lemma_triple_matches_bound_complete b pool t
#pop-options

/// The full-index specialisation (`build_indexed` IS
/// `build_indexed_selective all_bucket_needs`, RDF.Indexed.fsti).
let lemma_ig_search_complete (g : rdf_graph) (b : triple_pattern_bound) (t : triple)
  : Lemma (requires List.Tot.memP t g /\ bound_holds b t == true /\ bound_obj_exact b)
          (ensures  List.Tot.memP t (ig_search (build_indexed g) b)) =
  lemma_ig_search_complete_selective all_bucket_needs g b t

let lemma_store_search_complete (g : rdf_graph) (b : triple_pattern_bound) (t : triple)
  : Lemma (requires List.Tot.memP t g /\ bound_holds b t == true /\ bound_obj_exact b)
          (ensures  List.Tot.memP t (store_search (graph_to_store g) b)) =
  lemma_ig_search_complete g b t

/// The SHIPPING-store form: the selective store `graph_to_store_for`
/// builds serves every matching triple too.
let lemma_store_search_complete_for
      (p : group_graph_pattern) (g : rdf_graph) (b : triple_pattern_bound) (t : triple)
  : Lemma (requires List.Tot.memP t g /\ bound_holds b t == true /\ bound_obj_exact b)
          (ensures  List.Tot.memP t (store_search (graph_to_store_for p g) b)) =
  lemma_ig_search_complete_selective (bucket_needs_of_pattern p) g b t

(** ====================================================================== **)
(** Part 3: one triple pattern, closed under later extensions              **)
(** ====================================================================== **)

/// `bound_predicate_of_pattern` agrees with `bound_object_of_pattern`
/// wherever the latter yields an IRI. Needed because `tp_match`
/// binds the predicate position through `try_bind_term` (whose
/// refinement lemma speaks `bound_object_of_pattern`) while
/// `instantiate_tp` reads it back through
/// `bound_predicate_of_pattern`.
let lemma_bound_pred_from_obj (pt : pattern_term) (mu : solution_mapping) (p : wf_iri)
  : Lemma (requires bound_object_of_pattern pt mu == Some (T_IRI p))
          (ensures  bound_predicate_of_pattern pt mu == Some p) =
  match pt with
  | PT_Var v -> ()
  | _ -> ()

/// `SPARQL11.Algebra.Refinement.theorem_tp_match_instantiates`, with
/// the conclusion CLOSED UNDER LATER EXTENSIONS. This is the shape
/// section 7.3 of the simple-entailment design doc identifies as the
/// only usable one for a search-with-accumulator induction: the
/// mapping that finally explains this pattern is the FINAL binding of
/// the whole BGP fan-out, built long after this step. The existing
/// theorem states the instantiation at the step's own output mu'
/// only, which the BGP induction cannot use.
let theorem_tp_match_instantiates_ext
      (tp : triple_pattern) (t : triple) (mu mu' : solution_mapping)
  : Lemma (requires tp_match tp t mu == Some mu' /\ R.smap_exact mu /\
                    R.psub_tt_free tp.tp_s /\
                    R.ptrm_tt_free tp.tp_p /\ R.ptrm_exact tp.tp_p /\
                    R.ptrm_tt_free tp.tp_o /\ R.ptrm_exact tp.tp_o /\
                    R.term_exact t.o /\ R.term_tt_free t.o)
          (ensures  R.binding_extends mu' mu /\ R.smap_exact mu' /\
                    (forall (mu2 : solution_mapping).
                       R.binding_extends mu2 mu' ==>
                       instantiate_tp tp mu2 == Some t)) =
  let mu1 = Some?.v (try_bind_subject tp.tp_s t.s mu) in
  R.lemma_try_bind_subject_instantiates tp.tp_s t.s mu mu1;
  let mu2 = Some?.v (try_bind_term tp.tp_p (T_IRI t.p) mu1) in
  R.lemma_try_bind_term_instantiates tp.tp_p (T_IRI t.p) mu1 mu2;
  R.lemma_try_bind_term_instantiates tp.tp_o t.o mu2 mu';
  R.lemma_binding_extends_trans mu' mu2 mu1;
  R.lemma_binding_extends_trans mu' mu1 mu;
  let aux (mu3 : solution_mapping)
    : Lemma (requires R.binding_extends mu3 mu')
            (ensures  instantiate_tp tp mu3 == Some t) =
    R.lemma_binding_extends_trans mu3 mu' mu2;
    R.lemma_binding_extends_trans mu3 mu' mu1;
    assert (bound_subject_of_pattern tp.tp_s mu3 == Some t.s);
    assert (bound_object_of_pattern tp.tp_p mu3 == Some (T_IRI t.p));
    lemma_bound_pred_from_obj tp.tp_p mu3 t.p;
    assert (bound_object_of_pattern tp.tp_o mu3 == Some t.o)
  in
  FStar.Classical.forall_intro (fun mu3 -> FStar.Classical.move_requires aux mu3)

(** ====================================================================== **)
(** Part 4: one triple pattern against the store                           **)
(** ====================================================================== **)

/// Outside the fulltext escape hatch (finding BR-1), the dispatcher
/// IS the default path. Decidable hypothesis, no assumption.
let lemma_eval_single_tp_store_default_eq
      (tp : triple_pattern) (gs : graph_store) (mu : solution_mapping)
  : Lemma (requires tp_not_fulltext tp == true)
          (ensures  eval_single_tp_store tp gs mu ==
                    eval_single_tp_store_default tp gs mu) = ()

/// Every mapping the store-backed single-pattern step produces comes
/// from `tp_match` against an actual triple of the graph.
let lemma_eval_single_tp_sound
      (tp : triple_pattern) (g : rdf_graph) (mu mu' : solution_mapping)
  : Lemma (requires List.Tot.memP mu' (eval_single_tp_store_default tp (graph_to_store g) mu))
          (ensures  (exists (t : triple).
                       List.Tot.memP t g /\ tp_match tp t mu == Some mu')) =
  let gs = graph_to_store g in
  let bound = {
    bs = bound_subject_of_pattern tp.tp_s mu;
    bp = bound_predicate_of_pattern tp.tp_p mu;
    bo = bound_object_of_pattern tp.tp_o mu;
  } in
  let candidates = store_search gs bound in
  R.lemma_memP_filter_map (fun (t : triple) -> tp_match tp t mu) candidates mu';
  introduce forall (t : triple). List.Tot.memP t candidates ==> List.Tot.memP t g
  with introduce List.Tot.memP t candidates ==> List.Tot.memP t g
  with _ . lemma_store_search_sound g bound t

(** ====================================================================== **)
(** Part 5: the cost-based pattern chooser covers the BGP                   **)
(** ====================================================================== **)

/// `choose_best_tp` REORDERS the BGP by index-cardinality estimate
/// (SPARQL11.Algebra.fst:2810). For the refinement statement all that
/// matters is that the reordering is a permutation step: it removes
/// exactly one pattern, that pattern plus the remainder covers the
/// input, and the remainder introduces nothing new. Estimates are
/// irrelevant to the conclusion -- which is the precise sense in
/// which the query planner cannot change the answer set.
let rec lemma_choose_best_tp_cover (patterns : bgp) (gs : graph_store) (mu : solution_mapping)
  : Lemma (ensures (match choose_best_tp patterns gs mu with
                    | None -> patterns == []
                    | Some (tp, rest) ->
                      Cons? patterns /\
                      List.Tot.length rest = List.Tot.length patterns - 1 /\
                      List.Tot.memP tp patterns /\
                      (forall (p : triple_pattern). List.Tot.memP p rest ==>
                          List.Tot.memP p patterns) /\
                      (forall (p : triple_pattern). List.Tot.memP p patterns ==>
                          (p == tp \/ List.Tot.memP p rest))))
          (decreases patterns) =
  match patterns with
  | [] -> ()
  | tp :: rest ->
    lemma_choose_best_tp_cover rest gs mu;
    (match choose_best_tp rest gs mu with
     | None -> ()
     | Some (best, remaining) -> ())

(** ====================================================================== **)
(** Part 6: the BGP fan-out                                                 **)
(** ====================================================================== **)

/// The tail-recursive `concatMap_tr` the fan-out uses (issue #94's
/// stack-overflow fix) has the same membership semantics as
/// `List.Tot.concatMap`: `RDF.List.Helpers.lemma_concatMap_tr_eq`
/// says so, and `SPARQL11.Algebra.Refinement.lemma_memP_concatMap`
/// gives the membership characterisation of the latter.
let lemma_memP_concatMap_tr (#a #b : Type) (f : a -> list b) (xs : list a) (y : b)
  : Lemma (requires List.Tot.memP y (Lh.concatMap_tr f xs))
          (ensures  (exists (x : a). List.Tot.memP x xs /\ List.Tot.memP y (f x))) =
  Lh.lemma_concatMap_tr_eq f xs;
  R.lemma_memP_concatMap f xs y

/// The fan-out's continuation, given a NAME. Naming it is what makes
/// the equation below usable: a bare lambda is encoded to SMT as an
/// opaque symbol with no congruence to any other lambda, even a
/// syntactically identical one, so an equation whose right-hand side
/// is a lambda cannot be applied to a goal mentioning "the same"
/// lambda. A partial application of a named function has the ordinary
/// application encoding and composes.
let bgp_fanout_cont (rest : bgp) (gs : graph_store) (n : nat) (mu' : solution_mapping)
  : solution_sequence =
  eval_bgp_store_from_mu_fuel rest gs mu' n

/// The fan-out's defining equation, TRANSCRIBED (not derived): the
/// right-hand side repeats SPARQL11.Algebra.fst:2826-2845 verbatim,
/// including the `choose_best_tp` match, and the proof is the
/// normalizer plus reflexivity.
///
/// It must be stated this way, and closed by a tactic rather than by
/// SMT, for a mechanical reason worth recording: the body contains a
/// LAMBDA, and F*'s SMT encoding gives a lambda written in
/// SPARQL11.Algebra a different opaque symbol from a syntactically
/// identical lambda written here. SMT has no congruence relating the
/// two, so `= ()` cannot close the goal no matter the rlimit -- the
/// three failed attempts before this one all died on exactly that.
/// Under the normalizer both sides delta-reduce to the same term and
/// `trefl` closes it without ever encoding a lambda.
///
/// The recursive call's fuel is spelled `n + 1 - 1`, not `n`: the
/// normalizer leaves symbolic integer arithmetic alone, so writing
/// `n` here makes `trefl` fail on that one subterm. SMT closes the
/// arithmetic gap at the use site, where no lambda is involved.
let lemma_eval_bgp_store_unfold
      (hd : triple_pattern) (tl : bgp) (gs : graph_store) (mu : solution_mapping) (n : nat)
  : Lemma (ensures eval_bgp_store_from_mu_fuel (hd :: tl) gs mu (n + 1) ==
                   (if n + 1 = 0 then [mu]
                    else match choose_best_tp (hd :: tl) gs mu with
                    | None -> [mu]
                    | Some (tp, rest) ->
                      Lh.concatMap_tr
                        (bgp_fanout_cont rest gs (n + 1 - 1))
                        (eval_single_tp_store tp gs mu))) =
  assert (eval_bgp_store_from_mu_fuel (hd :: tl) gs mu (n + 1) ==
          (if n + 1 = 0 then [mu]
           else match choose_best_tp (hd :: tl) gs mu with
           | None -> [mu]
           | Some (tp, rest) ->
             Lh.concatMap_tr
               (bgp_fanout_cont rest gs (n + 1 - 1))
               (eval_single_tp_store tp gs mu)))
    by (T.norm [delta_only [`%eval_bgp_store_from_mu_fuel; `%bgp_fanout_cont];
                zeta; iota; primops; unascribe; unmeta];
        T.trefl ())

/// One step of the fan-out, in membership form. The lambda occurs
/// only inside THIS module, so `lemma_memP_concatMap_tr` applies.
let lemma_eval_bgp_store_step
      (hd : triple_pattern) (tl : bgp) (gs : graph_store) (mu muf : solution_mapping) (n : nat)
      (tp : triple_pattern) (rest : bgp)
  : Lemma (requires choose_best_tp (hd :: tl) gs mu == Some (tp, rest) /\
                    List.Tot.memP muf (eval_bgp_store_from_mu_fuel (hd :: tl) gs mu (n + 1)))
          (ensures  (exists (mu' : solution_mapping).
                       List.Tot.memP mu' (eval_single_tp_store tp gs mu) /\
                       List.Tot.memP muf (eval_bgp_store_from_mu_fuel rest gs mu' n))) =
  lemma_eval_bgp_store_unfold hd tl gs mu n;
  lemma_memP_concatMap_tr
    (bgp_fanout_cont rest gs (n + 1 - 1))
    (eval_single_tp_store tp gs mu) muf

/// THE LAYER-2 SOUNDNESS THEOREM, in the induction-carrying form.
///
/// Reading: whatever mapping `muf` the fuel-bounded BGP fan-out
/// produces from a starting mapping `mu`, (a) it extends `mu`, (b) it
/// stays inside the exact fragment, and (c) it instantiates EVERY
/// pattern of the BGP to a triple that is actually in `g` -- which is
/// "mu(BGP) is a subgraph of G", section 18.3.1's subgraph clause and
/// the first conjunct of `SPARQL11.Algebra.Spec.bgp_sol_spec`.
///
/// `fuel >= length patterns` is not slack: at fuel 0 the evaluator
/// RETURNS `[mu]` with patterns still unconsumed (SPARQL11.Algebra.
/// fst:2833), so the conclusion is false without it. The shipping
/// entry point supplies `length patterns + 1`, so the hypothesis is
/// discharged, not inherited -- see `theorem_eval_bgp_subgraph`.
let rec theorem_eval_bgp_sound_fuel
      (patterns : bgp) (g : rdf_graph) (mu muf : solution_mapping) (fuel : nat)
  : Lemma (requires List.Tot.memP muf
                      (eval_bgp_store_from_mu_fuel patterns (graph_to_store g) mu fuel) /\
                    fuel >= List.Tot.length patterns /\
                    R.smap_exact mu /\ bgp_frag patterns /\ graph_frag g)
          (ensures  R.binding_extends muf mu /\ R.smap_exact muf /\
                    bgp_subgraph_clause patterns g muf)
          (decreases fuel) =
  let gs = graph_to_store g in
  if fuel = 0 then ()
  else
    match patterns with
    | [] -> ()
    | hd :: tl ->
      lemma_choose_best_tp_cover patterns gs mu;
      (match choose_best_tp patterns gs mu with
       | None -> ()
       | Some (tp, rest) ->
         assert (tp_frag tp);
         lemma_eval_single_tp_store_default_eq tp gs mu;
         assert (choose_best_tp patterns gs mu == Some (tp, rest));
         lemma_eval_bgp_store_step hd tl gs mu muf (fuel - 1) tp rest;
         assert (exists (mu' : solution_mapping).
                   List.Tot.memP mu' (eval_single_tp_store tp gs mu) /\
                   List.Tot.memP muf (eval_bgp_store_from_mu_fuel rest gs mu' (fuel - 1)));
         let step (mu' : solution_mapping)
           : Lemma (requires List.Tot.memP mu' (eval_single_tp_store tp gs mu) /\
                             List.Tot.memP muf
                               (eval_bgp_store_from_mu_fuel rest gs mu' (fuel - 1)))
                   (ensures  R.binding_extends muf mu /\ R.smap_exact muf /\
                             bgp_subgraph_clause patterns g muf) =
           lemma_eval_single_tp_sound tp g mu mu';
           let inner (t : triple)
             : Lemma (requires List.Tot.memP t g /\ tp_match tp t mu == Some mu')
                     (ensures  R.binding_extends muf mu /\ R.smap_exact muf /\
                               bgp_subgraph_clause patterns g muf) =
             theorem_tp_match_instantiates_ext tp t mu mu';
             theorem_eval_bgp_sound_fuel rest g mu' muf (fuel - 1);
             R.lemma_binding_extends_trans muf mu' mu;
             assert (instantiate_tp tp muf == Some t);
             assert (bgp_subgraph_clause rest g muf);
             introduce forall (p : triple_pattern). List.Tot.memP p patterns ==>
                 (exists (t2 : triple).
                    instantiate_tp p muf == Some t2 /\ List.Tot.memP t2 g)
             with introduce List.Tot.memP p patterns ==>
                    (exists (t2 : triple).
                       instantiate_tp p muf == Some t2 /\ List.Tot.memP t2 g)
             with _ .
               eliminate (p == tp) \/ List.Tot.memP p rest
               returns (exists (t2 : triple).
                          instantiate_tp p muf == Some t2 /\ List.Tot.memP t2 g)
               with _ .
                 introduce exists (t2 : triple).
                     instantiate_tp p muf == Some t2 /\ List.Tot.memP t2 g
                 with t and ()
               and _ . ()
           in
           FStar.Classical.forall_intro (FStar.Classical.move_requires inner)
         in
         FStar.Classical.forall_intro (FStar.Classical.move_requires step))

/// THE SHIPPING STATEMENT. `eval_bgp` is what the evaluator calls for
/// every basic graph pattern (SPARQL11.Algebra.fst:2846). Every
/// solution it returns subset-matches the graph.
let theorem_eval_bgp_subgraph (b : bgp) (g : rdf_graph) (mu : solution_mapping)
  : Lemma (requires List.Tot.memP mu (eval_bgp b g) /\ bgp_frag b /\ graph_frag g)
          (ensures  bgp_subgraph_clause b g mu) =
  theorem_eval_bgp_sound_fuel b g sm_empty mu (List.Tot.length b + 1)

/// The same conclusion in the form layer 3 consumes: the INSTANTIATED
/// BGP, as a concrete triple list, is a subset of the graph. This is
/// literally the `mu(BGP) subset-of rdfs_closure g` side of the
/// design doc's layer-1 equivalence, once `g` is instantiated at the
/// closure.
let rec lemma_instantiate_bgp_subset (b : bgp) (g : rdf_graph) (mu : solution_mapping)
  : Lemma (requires bgp_subgraph_clause b g mu)
          (ensures  (forall (t : triple).
                       List.Tot.memP t (instantiate_bgp b mu) ==> List.Tot.memP t g))
          (decreases b) =
  match b with
  | [] -> ()
  | p :: rest ->
    lemma_instantiate_bgp_subset rest g mu;
    (match instantiate_tp p mu with
     | None -> ()
     | Some t -> ())

/// The tie-back to the INDEPENDENT specification module. Nothing
/// above mentions `SPARQL11.Algebra.Spec`; this lemma checks, by
/// machine rather than by comment, that `bgp_subgraph_clause` is
/// literally the first conjunct of `S.bgp_sol_spec` at the shipping
/// instantiation (`inst := instantiate_tp` with its two arguments
/// swapped -- the spec writes `inst mu p`, the engine
/// `instantiate_tp p mu` -- `tp := triple_pattern`,
/// `gtriple := RDF.Triple.triple`), and names the exact residual
/// obligation for a full section-18.3.1 solution: the DOMAIN clause
/// `dom(mu) = var(BGP)`. That clause is about `sm_bind` bookkeeping,
/// not about the graph, and is a separate commit.
let lemma_bgp_sol_spec_from_subgraph_clause
      (b : bgp) (g : rdf_graph) (mu : solution_mapping)
      (patvars : triple_pattern -> list S.var_name)
  : Lemma (requires bgp_subgraph_clause b g mu /\
                    (forall (v : S.var_name).
                       Some? (S.sval v mu) <==>
                       (exists (p : triple_pattern).
                          List.Tot.memP p b /\ List.Tot.memP v (patvars p))))
          (ensures  S.bgp_sol_spec
                      (fun (m : S.smap) (p : triple_pattern) -> instantiate_tp p m)
                      patvars b g mu) = ()

let theorem_eval_bgp_instantiates_into_graph (b : bgp) (g : rdf_graph) (mu : solution_mapping)
  : Lemma (requires List.Tot.memP mu (eval_bgp b g) /\ bgp_frag b /\ graph_frag g)
          (ensures  (forall (t : triple).
                       List.Tot.memP t (instantiate_bgp b mu) ==> List.Tot.memP t g)) =
  theorem_eval_bgp_subgraph b g mu;
  lemma_instantiate_bgp_subset b g mu

(** ====================================================================== **)
(** Part 8: THE BGP FAN-OUT AT ANY SOUND STORE (closes finding RT-2)       **)
(**                                                                        **)
(** Part 6 is stated at `graph_to_store g` specifically because its one    **)
(** index-soundness step calls `lemma_store_search_sound`, which is        **)
(** proved only for that constructor. Generalising the SAME induction      **)
(** over an ARBITRARY `gs : graph_store` carrying probe-soundness as an    **)
(** explicit hypothesis (`store_search_sound gs`) costs nothing new        **)
(** mathematically -- every step below is Part 6's proof with `g` read     **)
(** as `gs.gs_graph`, `graph_to_store g` read as `gs`, and the one call to **)
(** `lemma_store_search_sound` replaced by consuming the hypothesis --     **)
(** and it is what makes the selective store's probe soundness (part 2b)   **)
(** reach `eval_bgp_store` rather than stopping at `ig_search`. The        **)
(** specialisation at the end (`theorem_eval_bgp_store_for_instantiates_   **)
(** into_graph`) is layer 2's closing statement for finding RT-2: the      **)
(** shipping `graph_to_store_for` store carries the SAME soundness         **)
(** theorem `theorem_eval_bgp_instantiates_into_graph` proves for          **)
(** `graph_to_store`.                                                      **)
(** ====================================================================== **)

/// Probe soundness, as a property of a STORE rather than of a
/// construction function -- what Part 6's induction actually needs at
/// each step, independent of how the store was built.
let store_search_sound (gs : graph_store) : prop =
  forall (b : triple_pattern_bound) (t : triple).
    List.Tot.memP t (store_search gs b) ==> List.Tot.memP t gs.gs_graph

/// `graph_to_store` satisfies the property (tie-back to Part 2's
/// original lemma, so a caller with a plain `rdf_graph` need not know
/// this section exists).
let lemma_graph_to_store_sound (g : rdf_graph)
  : Lemma (store_search_sound (graph_to_store g)) =
  introduce forall (b : triple_pattern_bound) (t : triple).
      List.Tot.memP t (store_search (graph_to_store g) b) ==> List.Tot.memP t g
  with introduce List.Tot.memP t (store_search (graph_to_store g) b) ==> List.Tot.memP t g
  with _ . lemma_store_search_sound g b t

/// `graph_to_store_for` satisfies the property (part 2b's closing
/// tie-back): THIS is the fact that lets the induction below run at
/// the SELECTIVE store.
let lemma_graph_to_store_for_sound (p : group_graph_pattern) (g : rdf_graph)
  : Lemma (store_search_sound (graph_to_store_for p g)) =
  introduce forall (b : triple_pattern_bound) (t : triple).
      List.Tot.memP t (store_search (graph_to_store_for p g) b) ==> List.Tot.memP t g
  with introduce List.Tot.memP t (store_search (graph_to_store_for p g) b) ==> List.Tot.memP t g
  with _ . lemma_store_search_sound_for p g b t

/// Part 4's single-pattern soundness lemma, generalised from `graph_to_
/// store g` to an arbitrary sound `gs`. Body identical to
/// `lemma_eval_single_tp_sound` except the final connective step reads
/// the `store_search_sound gs` hypothesis instead of calling
/// `lemma_store_search_sound` on a graph literal.
let lemma_eval_single_tp_sound_at
      (tp : triple_pattern) (gs : graph_store) (mu mu' : solution_mapping)
  : Lemma (requires List.Tot.memP mu' (eval_single_tp_store_default tp gs mu) /\
                    store_search_sound gs)
          (ensures  (exists (t : triple).
                       List.Tot.memP t gs.gs_graph /\ tp_match tp t mu == Some mu')) =
  let bound = {
    bs = bound_subject_of_pattern tp.tp_s mu;
    bp = bound_predicate_of_pattern tp.tp_p mu;
    bo = bound_object_of_pattern tp.tp_o mu;
  } in
  let candidates = store_search gs bound in
  R.lemma_memP_filter_map (fun (t : triple) -> tp_match tp t mu) candidates mu';
  introduce forall (t : triple). List.Tot.memP t candidates ==> List.Tot.memP t gs.gs_graph
  with introduce List.Tot.memP t candidates ==> List.Tot.memP t gs.gs_graph
  with _ . ()

/// Part 6's induction, generalised. Same recursion, same case split,
/// same helper lemmas (`lemma_choose_best_tp_cover`,
/// `lemma_eval_bgp_store_step`, `theorem_tp_match_instantiates_ext`)
/// -- none of which reference `graph_to_store` -- with only the one
/// soundness step re-pointed at `lemma_eval_single_tp_sound_at` and
/// `store_search_sound gs` threaded as a hypothesis (constant across
/// the recursion: `gs` never changes, so it is available unchanged at
/// every recursive call).
let rec theorem_eval_bgp_store_sound_fuel
      (patterns : bgp) (gs : graph_store) (mu muf : solution_mapping) (fuel : nat)
  : Lemma (requires List.Tot.memP muf
                      (eval_bgp_store_from_mu_fuel patterns gs mu fuel) /\
                    fuel >= List.Tot.length patterns /\
                    R.smap_exact mu /\ bgp_frag patterns /\ graph_frag gs.gs_graph /\
                    store_search_sound gs)
          (ensures  R.binding_extends muf mu /\ R.smap_exact muf /\
                    bgp_subgraph_clause patterns gs.gs_graph muf)
          (decreases fuel) =
  if fuel = 0 then ()
  else
    match patterns with
    | [] -> ()
    | hd :: tl ->
      lemma_choose_best_tp_cover patterns gs mu;
      (match choose_best_tp patterns gs mu with
       | None -> ()
       | Some (tp, rest) ->
         assert (tp_frag tp);
         lemma_eval_single_tp_store_default_eq tp gs mu;
         assert (choose_best_tp patterns gs mu == Some (tp, rest));
         lemma_eval_bgp_store_step hd tl gs mu muf (fuel - 1) tp rest;
         assert (exists (mu' : solution_mapping).
                   List.Tot.memP mu' (eval_single_tp_store tp gs mu) /\
                   List.Tot.memP muf (eval_bgp_store_from_mu_fuel rest gs mu' (fuel - 1)));
         let step (mu' : solution_mapping)
           : Lemma (requires List.Tot.memP mu' (eval_single_tp_store tp gs mu) /\
                             List.Tot.memP muf
                               (eval_bgp_store_from_mu_fuel rest gs mu' (fuel - 1)))
                   (ensures  R.binding_extends muf mu /\ R.smap_exact muf /\
                             bgp_subgraph_clause patterns gs.gs_graph muf) =
           lemma_eval_single_tp_sound_at tp gs mu mu';
           let inner (t : triple)
             : Lemma (requires List.Tot.memP t gs.gs_graph /\ tp_match tp t mu == Some mu')
                     (ensures  R.binding_extends muf mu /\ R.smap_exact muf /\
                               bgp_subgraph_clause patterns gs.gs_graph muf) =
             theorem_tp_match_instantiates_ext tp t mu mu';
             theorem_eval_bgp_store_sound_fuel rest gs mu' muf (fuel - 1);
             R.lemma_binding_extends_trans muf mu' mu;
             assert (instantiate_tp tp muf == Some t);
             assert (bgp_subgraph_clause rest gs.gs_graph muf);
             introduce forall (p : triple_pattern). List.Tot.memP p patterns ==>
                 (exists (t2 : triple).
                    instantiate_tp p muf == Some t2 /\ List.Tot.memP t2 gs.gs_graph)
             with introduce List.Tot.memP p patterns ==>
                    (exists (t2 : triple).
                       instantiate_tp p muf == Some t2 /\ List.Tot.memP t2 gs.gs_graph)
             with _ .
               eliminate (p == tp) \/ List.Tot.memP p rest
               returns (exists (t2 : triple).
                          instantiate_tp p muf == Some t2 /\ List.Tot.memP t2 gs.gs_graph)
               with _ .
                 introduce exists (t2 : triple).
                     instantiate_tp p muf == Some t2 /\ List.Tot.memP t2 gs.gs_graph
                 with t and ()
               and _ . ()
           in
           FStar.Classical.forall_intro (FStar.Classical.move_requires inner)
         in
         FStar.Classical.forall_intro (FStar.Classical.move_requires step))

/// THE STORE-GENERIC SHIPPING STATEMENT: every solution `eval_bgp_store`
/// returns over ANY sound store instantiates into that store's graph.
let theorem_eval_bgp_store_subgraph (b : bgp) (gs : graph_store) (mu : solution_mapping)
  : Lemma (requires List.Tot.memP mu (eval_bgp_store b gs) /\ bgp_frag b /\
                    graph_frag gs.gs_graph /\ store_search_sound gs)
          (ensures  bgp_subgraph_clause b gs.gs_graph mu) =
  theorem_eval_bgp_store_sound_fuel b gs sm_empty mu (List.Tot.length b + 1)

let theorem_eval_bgp_store_instantiates_into_graph (b : bgp) (gs : graph_store) (mu : solution_mapping)
  : Lemma (requires List.Tot.memP mu (eval_bgp_store b gs) /\ bgp_frag b /\
                    graph_frag gs.gs_graph /\ store_search_sound gs)
          (ensures  (forall (t : triple).
                       List.Tot.memP t (instantiate_bgp b mu) ==> List.Tot.memP t gs.gs_graph)) =
  theorem_eval_bgp_store_subgraph b gs mu;
  lemma_instantiate_bgp_subset b gs.gs_graph mu

/// THE SELECTIVE-STORE SHIPPING STATEMENT (finding RT-2, RESOLVED).
/// `graph_to_store_for` is what `eval_pattern`/`eval_ask_query`
/// actually build (SPARQL11.Algebra.fst:3588-3589), not `graph_to_
/// store`. Every solution `eval_bgp_store` returns over THAT store
/// instantiates into the graph -- the exact analogue of
/// `theorem_eval_bgp_instantiates_into_graph` (Part 6's closing
/// theorem, for the full-index store), now for the store the shipping
/// evaluator actually runs on.
let theorem_eval_bgp_store_for_instantiates_into_graph
      (p : group_graph_pattern) (b : bgp) (g : rdf_graph) (mu : solution_mapping)
  : Lemma (requires List.Tot.memP mu (eval_bgp_store b (graph_to_store_for p g)) /\
                    bgp_frag b /\ graph_frag g)
          (ensures  (forall (t : triple).
                       List.Tot.memP t (instantiate_bgp b mu) ==> List.Tot.memP t g)) =
  lemma_graph_to_store_for_sound p g;
  theorem_eval_bgp_store_instantiates_into_graph b (graph_to_store_for p g) mu

(** ====================================================================== **)
(** Part 9: the CONVERSE of Part 3 -- an instantiation IS a match          **)
(**                                                                        **)
(** Part 3 goes match-to-instantiation; completeness needs the other       **)
(** direction, and it is not a mirror image: there the mapping already     **)
(** exists and the pattern is read off it, here the mapping has to be      **)
(** BUILT and each `try_bind_*` has to be shown to SUCCEED.                **)
(** ====================================================================== **)

/// `subject_to_term` lands on the two constructors where `rdf_term_eq`
/// is already identity (both carry a plain `string`, an `eqtype`), so
/// every subject term is `term_exact`. Handed to SMT as an instantiated
/// `forall` because `R.term_exact` is a quantified proposition, not a
/// pattern match.
let lemma_term_exact_subject (sj : subject) : Lemma (R.term_exact (subject_to_term sj)) =
  let aux (t' : rdf_term)
    : Lemma (requires rdf_term_eq (subject_to_term sj) t' == true)
            (ensures  subject_to_term sj == t') =
    match sj, t' with
    | S_IRI _, T_IRI _ -> ()
    | S_BNode _, T_BNode _ -> ()
    | _, _ -> ()
  in FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

let lemma_term_exact_iri (i : wf_iri) : Lemma (R.term_exact (T_IRI i)) =
  lemma_term_exact_subject (S_IRI i)

let lemma_term_exact_bnode (b : bnode_id) : Lemma (R.term_exact (T_BNode b)) =
  lemma_term_exact_subject (S_BNode b)

/// MONOTONICITY of the three `bound_*_of_pattern` readers under
/// `binding_extends`. A position that is already determined by the
/// partial mapping keeps the same value in every later extension --
/// which is what makes the index probe computed at step k still
/// correct about the mapping finished at step n.
#push-options "--z3rlimit 300 --fuel 2 --ifuel 4"
let lemma_bound_subject_mono
      (ps : pattern_subject) (mu muf : solution_mapping) (sj : subject)
  : Lemma (requires R.binding_extends muf mu /\ bound_subject_of_pattern ps mu == Some sj)
          (ensures  bound_subject_of_pattern ps muf == Some sj) =
  match ps with
  | PS_Var v ->
    Lh.lemma_assoc_tr_eq v mu;
    Lh.lemma_assoc_tr_eq v muf;
    // Spelled out because the reader REBUILDS the subject
    // (`Some (T_IRI i)` becomes `Some (S_IRI i)`) rather than passing
    // the looked-up value through, so SMT needs the two lookups
    // identified before it can identify the two rebuilds.
    (match sm_lookup v mu with
     | Some x ->
       assert (S.sval v mu == Some x);
       assert (S.sval v muf == Some x);
       assert (sm_lookup v muf == Some x)
     | None -> ())
  | _ -> ()

let lemma_bound_predicate_mono
      (pt : pattern_term) (mu muf : solution_mapping) (p : wf_iri)
  : Lemma (requires R.binding_extends muf mu /\ bound_predicate_of_pattern pt mu == Some p)
          (ensures  bound_predicate_of_pattern pt muf == Some p) =
  match pt with
  | PT_Var v ->
    Lh.lemma_assoc_tr_eq v mu;
    Lh.lemma_assoc_tr_eq v muf;
    (match sm_lookup v mu with
     | Some x ->
       assert (S.sval v mu == Some x);
       assert (S.sval v muf == Some x);
       assert (sm_lookup v muf == Some x)
     | None -> ())
  | _ -> ()

let lemma_bound_object_mono
      (pt : pattern_term) (mu muf : solution_mapping) (o : rdf_term)
  : Lemma (requires R.binding_extends muf mu /\ bound_object_of_pattern pt mu == Some o /\
                    R.ptrm_tt_free pt)
          (ensures  bound_object_of_pattern pt muf == Some o) =
  match pt with
  | PT_Var v ->
    Lh.lemma_assoc_tr_eq v mu;
    Lh.lemma_assoc_tr_eq v muf;
    (match sm_lookup v mu with
     | Some x ->
       assert (S.sval v mu == Some x);
       assert (S.sval v muf == Some x);
       assert (sm_lookup v muf == Some x)
     | None -> ())
  | _ -> ()
#pop-options

/// The converse of `lemma_bound_pred_from_obj` (Part 3): a determined
/// predicate position is also determined as an OBJECT term, which is
/// the form `try_bind_term` speaks.
let lemma_bound_obj_from_pred (pt : pattern_term) (mu : solution_mapping) (p : wf_iri)
  : Lemma (requires bound_predicate_of_pattern pt mu == Some p)
          (ensures  bound_object_of_pattern pt mu == Some (T_IRI p)) =
  match pt with
  | PT_Var v -> ()
  | _ -> ()

/// A determined object position inside the fragment is `term_exact`:
/// constants by their constructor, literals by `R.ptrm_exact`, and
/// variables by the mapping's own exactness.
let lemma_bound_object_exact (pt : pattern_term) (mu : solution_mapping) (o : rdf_term)
  : Lemma (requires bound_object_of_pattern pt mu == Some o /\ R.smap_exact mu /\
                    R.ptrm_exact pt /\ R.ptrm_tt_free pt)
          (ensures  R.term_exact o) =
  match pt with
  | PT_IRI i -> lemma_term_exact_iri i
  | PT_BNode b -> lemma_term_exact_bnode b
  | PT_Literal l -> ()
  | PT_Var v -> Lh.lemma_assoc_tr_eq v mu; R.lemma_smap_exact_sval mu v o
  | PT_TripleTerm _ _ _ -> ()

#push-options "--z3rlimit 300 --fuel 2 --ifuel 4"
/// `sm_bind` is a cons, so its `sval` is the one-key update. Stated
/// once here rather than re-derived at each of the four sites that
/// need it (two `try_bind_*` completeness lemmas, two branches each).
let lemma_sm_bind_sval (v w : string) (t : rdf_term) (mu : solution_mapping)
  : Lemma (ensures S.sval w (sm_bind v t mu) ==
                   (if w = v then Some t else S.sval w mu)) = ()

let lemma_sm_bind_extends (v : string) (t : rdf_term) (mu : solution_mapping)
  : Lemma (requires S.sval v mu == None)
          (ensures  R.binding_extends (sm_bind v t mu) mu) =
  FStar.Classical.forall_intro (fun (w : string) -> lemma_sm_bind_sval v w t mu)

let lemma_sm_bind_under (v : string) (t : rdf_term) (mu muf : solution_mapping)
  : Lemma (requires R.binding_extends muf mu /\ S.sval v muf == Some t)
          (ensures  R.binding_extends muf (sm_bind v t mu)) =
  FStar.Classical.forall_intro (fun (w : string) -> lemma_sm_bind_sval v w t mu)

/// `try_bind_subject` SUCCEEDS whenever the final mapping already
/// determines the position, and its output sits between `mu` and
/// `muf`. The `Some existing` branch closes by reflexivity of
/// `rdf_term_eq` (the existing binding IS the incoming term, since
/// `muf` extends `mu` and both determine the same position); the
/// `None` branch by the two `sm_bind` facts above.
let lemma_try_bind_subject_complete
      (ps : pattern_subject) (sj : subject) (mu muf : solution_mapping)
  : Lemma (requires R.binding_extends muf mu /\
                    bound_subject_of_pattern ps muf == Some sj /\ R.smap_exact mu)
          (ensures  Some? (try_bind_subject ps sj mu) /\
                    (let mu' = Some?.v (try_bind_subject ps sj mu) in
                     R.binding_extends muf mu' /\ R.binding_extends mu' mu /\
                     R.smap_exact mu')) =
  match ps with
  | PS_Var v ->
    Lh.lemma_assoc_tr_eq v mu;
    Lh.lemma_assoc_tr_eq v muf;
    lemma_term_exact_subject sj;
    let tm = subject_to_term sj in
    lemma_rdf_term_eq_refl tm;
    // Force the split that identifies `muf`'s binding with the
    // subject's TERM form -- the reader rebuilds a subject from it.
    (match sm_lookup v muf with
     | Some (T_IRI _) -> ()
     | Some (T_BNode _) -> ()
     | _ -> ());
    assert (S.sval v muf == Some tm);
    (match sm_lookup v mu with
     | Some existing ->
       assert (S.sval v mu == Some existing);
       assert (existing == tm);
       R.lemma_binding_extends_refl mu
     | None ->
       lemma_sm_bind_extends v tm mu;
       lemma_sm_bind_under v tm mu muf)
  | _ -> R.lemma_binding_extends_refl mu

let lemma_try_bind_term_complete
      (pt : pattern_term) (tm : rdf_term) (mu muf : solution_mapping)
  : Lemma (requires R.binding_extends muf mu /\
                    bound_object_of_pattern pt muf == Some tm /\
                    R.smap_exact mu /\ R.ptrm_tt_free pt /\ R.term_exact tm)
          (ensures  Some? (try_bind_term pt tm mu) /\
                    (let mu' = Some?.v (try_bind_term pt tm mu) in
                     R.binding_extends muf mu' /\ R.binding_extends mu' mu /\
                     R.smap_exact mu')) =
  match pt with
  | PT_Var v ->
    Lh.lemma_assoc_tr_eq v mu;
    Lh.lemma_assoc_tr_eq v muf;
    lemma_rdf_term_eq_refl tm;
    assert (S.sval v muf == Some tm);
    (match sm_lookup v mu with
     | Some existing ->
       assert (S.sval v mu == Some existing);
       assert (existing == tm);
       R.lemma_binding_extends_refl mu
     | None ->
       lemma_sm_bind_extends v tm mu;
       lemma_sm_bind_under v tm mu muf)
  | PT_Literal l -> lemma_literal_eq_refl l; R.lemma_binding_extends_refl mu
  | _ -> R.lemma_binding_extends_refl mu

/// ONE PATTERN, converse form: if the final mapping instantiates `tp`
/// to a triple `t`, then `tp_match` accepts `t` against the partial
/// mapping, and the accepted result still sits under `muf`.
let lemma_tp_match_complete
      (tp : triple_pattern) (t : triple) (mu muf : solution_mapping)
  : Lemma (requires R.binding_extends muf mu /\ instantiate_tp tp muf == Some t /\
                    R.smap_exact mu /\
                    R.ptrm_tt_free tp.tp_p /\ R.ptrm_tt_free tp.tp_o /\
                    R.term_exact t.o)
          (ensures  Some? (tp_match tp t mu) /\
                    (let mu' = Some?.v (tp_match tp t mu) in
                     R.binding_extends muf mu' /\ R.binding_extends mu' mu /\
                     R.smap_exact mu')) =
  assert (bound_subject_of_pattern tp.tp_s muf == Some t.s);
  assert (bound_predicate_of_pattern tp.tp_p muf == Some t.p);
  assert (bound_object_of_pattern tp.tp_o muf == Some t.o);
  lemma_try_bind_subject_complete tp.tp_s t.s mu muf;
  let mu1 = Some?.v (try_bind_subject tp.tp_s t.s mu) in
  lemma_bound_obj_from_pred tp.tp_p muf t.p;
  lemma_term_exact_iri t.p;
  lemma_try_bind_term_complete tp.tp_p (T_IRI t.p) mu1 muf;
  let mu2 = Some?.v (try_bind_term tp.tp_p (T_IRI t.p) mu1) in
  lemma_try_bind_term_complete tp.tp_o t.o mu2 muf;
  let mu3 = Some?.v (try_bind_term tp.tp_o t.o mu2) in
  R.lemma_binding_extends_trans mu3 mu2 mu1;
  R.lemma_binding_extends_trans mu3 mu1 mu
#pop-options

(** ====================================================================== **)
(** Part 10: the index probe, driven from the pattern                      **)
(** ====================================================================== **)

/// The bound `eval_single_tp_store_default` computes, given a NAME
/// (SPARQL11.Algebra.fst:2762-2766 spells it as an inline record).
let tp_bound (tp : triple_pattern) (mu : solution_mapping) : triple_pattern_bound =
  { bs = bound_subject_of_pattern tp.tp_s mu;
    bp = bound_predicate_of_pattern tp.tp_p mu;
    bo = bound_object_of_pattern tp.tp_o mu }

/// The probe computed at the PARTIAL mapping accepts the triple the
/// FINAL mapping picks out. Each position is either unbound (accepted
/// unconditionally) or bound, and then monotonicity forces it equal to
/// the triple's own component, so the acceptance test is a reflexivity.
let lemma_bound_holds_of_instantiate
      (tp : triple_pattern) (t : triple) (mu muf : solution_mapping)
  : Lemma (requires R.binding_extends muf mu /\ instantiate_tp tp muf == Some t /\
                    R.ptrm_tt_free tp.tp_o)
          (ensures  bound_holds (tp_bound tp mu) t == true) =
  (match bound_subject_of_pattern tp.tp_s mu with
   | Some s -> lemma_bound_subject_mono tp.tp_s mu muf s; lemma_subject_eq_refl s
   | None -> ());
  (match bound_predicate_of_pattern tp.tp_p mu with
   | Some p -> lemma_bound_predicate_mono tp.tp_p mu muf p
   | None -> ());
  (match bound_object_of_pattern tp.tp_o mu with
   | Some o -> lemma_bound_object_mono tp.tp_o mu muf o; lemma_rdf_term_eq_refl o
   | None -> ())

let lemma_tp_bound_obj_exact (tp : triple_pattern) (mu : solution_mapping)
  : Lemma (requires R.smap_exact mu /\ R.ptrm_exact tp.tp_o /\ R.ptrm_tt_free tp.tp_o)
          (ensures  bound_obj_exact (tp_bound tp mu)) =
  match bound_object_of_pattern tp.tp_o mu with
  | Some o -> lemma_bound_object_exact tp.tp_o mu o
  | None -> ()

/// Probe COMPLETENESS as a property of a STORE, the mirror of Part 8's
/// `store_search_sound` and for the same reason: it is what the
/// induction needs at each step, independent of how the store was
/// built, which is what lets one induction serve both
/// `graph_to_store` and the shipping `graph_to_store_for`.
let store_search_complete (gs : graph_store) : prop =
  forall (b : triple_pattern_bound) (t : triple).
    List.Tot.memP t gs.gs_graph /\ bound_holds b t == true /\ bound_obj_exact b ==>
    List.Tot.memP t (store_search gs b)

let lemma_graph_to_store_complete (g : rdf_graph)
  : Lemma (store_search_complete (graph_to_store g)) =
  introduce forall (b : triple_pattern_bound) (t : triple).
      List.Tot.memP t g /\ bound_holds b t == true /\ bound_obj_exact b ==>
      List.Tot.memP t (store_search (graph_to_store g) b)
  with introduce List.Tot.memP t g /\ bound_holds b t == true /\ bound_obj_exact b ==>
                 List.Tot.memP t (store_search (graph_to_store g) b)
  with _ . lemma_store_search_complete g b t

let lemma_graph_to_store_for_complete (p : group_graph_pattern) (g : rdf_graph)
  : Lemma (store_search_complete (graph_to_store_for p g)) =
  introduce forall (b : triple_pattern_bound) (t : triple).
      List.Tot.memP t g /\ bound_holds b t == true /\ bound_obj_exact b ==>
      List.Tot.memP t (store_search (graph_to_store_for p g) b)
  with introduce List.Tot.memP t g /\ bound_holds b t == true /\ bound_obj_exact b ==>
                 List.Tot.memP t (store_search (graph_to_store_for p g) b)
  with _ . lemma_store_search_complete_for p g b t

/// The completeness goal for one pattern, named so the `move_requires`
/// idiom below can carry it through an existential elimination.
let single_tp_goal (tp : triple_pattern) (gs : graph_store) (mu muf : solution_mapping) : prop =
  exists (mu' : solution_mapping).
    List.Tot.memP mu' (eval_single_tp_store tp gs mu) /\
    R.binding_extends muf mu' /\ R.binding_extends mu' mu /\ R.smap_exact mu'

#push-options "--z3rlimit 400 --fuel 2 --ifuel 3"
/// ONE PATTERN AGAINST THE STORE, completeness. This is where Part 2c
/// (the probe serves the triple) and Part 9 (the match accepts it)
/// meet: the index cannot hide the triple, and the filter cannot
/// reject it.
let lemma_eval_single_tp_complete_at
      (tp : triple_pattern) (gs : graph_store) (mu muf : solution_mapping) (t : triple)
  : Lemma (requires tp_frag tp /\ graph_frag gs.gs_graph /\ R.smap_exact mu /\
                    store_search_complete gs /\
                    R.binding_extends muf mu /\
                    instantiate_tp tp muf == Some t /\ List.Tot.memP t gs.gs_graph)
          (ensures  single_tp_goal tp gs mu muf) =
  let bound = tp_bound tp mu in
  lemma_eval_single_tp_store_default_eq tp gs mu;
  lemma_bound_holds_of_instantiate tp t mu muf;
  lemma_tp_bound_obj_exact tp mu;
  assert (List.Tot.memP t (store_search gs bound));
  lemma_tp_match_complete tp t mu muf;
  let mu' = Some?.v (tp_match tp t mu) in
  R.lemma_memP_filter_map (fun (x : triple) -> tp_match tp x mu) (store_search gs bound) mu';
  introduce exists (mu2 : solution_mapping).
      List.Tot.memP mu2 (eval_single_tp_store tp gs mu) /\
      R.binding_extends muf mu2 /\ R.binding_extends mu2 mu /\ R.smap_exact mu2
  with mu' and ()
#pop-options

(** ====================================================================== **)
(** Part 11: the fan-out, completeness, at any complete store              **)
(** ====================================================================== **)

let lemma_memP_concatMap_tr_intro (#a #b : Type) (f : a -> list b) (xs : list a) (x : a) (y : b)
  : Lemma (requires List.Tot.memP x xs /\ List.Tot.memP y (f x))
          (ensures  List.Tot.memP y (Lh.concatMap_tr f xs)) =
  Lh.lemma_concatMap_tr_eq f xs;
  R.lemma_memP_concatMap f xs y

/// The mirror of `lemma_eval_bgp_store_step` (Part 6), built on the
/// SAME transcribed unfolding equation, so the named continuation
/// `bgp_fanout_cont` does the lambda-avoidance work once for both
/// directions.
let lemma_eval_bgp_store_step_intro
      (hd : triple_pattern) (tl : bgp) (gs : graph_store)
      (mu mu' muf : solution_mapping) (n : nat)
      (tp : triple_pattern) (rest : bgp)
  : Lemma (requires choose_best_tp (hd :: tl) gs mu == Some (tp, rest) /\
                    List.Tot.memP mu' (eval_single_tp_store tp gs mu) /\
                    List.Tot.memP muf (eval_bgp_store_from_mu_fuel rest gs mu' n))
          (ensures  List.Tot.memP muf
                      (eval_bgp_store_from_mu_fuel (hd :: tl) gs mu (n + 1))) =
  lemma_eval_bgp_store_unfold hd tl gs mu n;
  lemma_memP_concatMap_tr_intro
    (bgp_fanout_cont rest gs (n + 1 - 1))
    (eval_single_tp_store tp gs mu) mu' muf

let bgp_complete_goal
      (patterns : bgp) (gs : graph_store) (mu muf : solution_mapping) (fuel : nat) : prop =
  exists (muo : solution_mapping).
    List.Tot.memP muo (eval_bgp_store_from_mu_fuel patterns gs mu fuel) /\
    R.binding_extends muf muo /\ R.binding_extends muo mu /\ R.smap_exact muo

#push-options "--z3rlimit 600 --fuel 2 --ifuel 2"
/// THE LAYER-2 COMPLETENESS THEOREM, in the induction-carrying form --
/// the exact counterpart of `theorem_eval_bgp_store_sound_fuel`, over
/// the same fold, with the same fuel side condition, at any store
/// carrying `store_search_complete`.
///
/// Reading: if SOME mapping `muf` explains every pattern of the BGP by
/// a triple of the store's graph, then the fan-out DOES produce a
/// solution `muo` that `muf` extends. `muo` is not claimed to be `muf`
/// itself, and it cannot be: `sm_bind` conses
/// (SPARQL11.Algebra.fst:103), so the engine's output is a LIST whose
/// order is fixed by `choose_best_tp`'s cost ordering, while `muf` is
/// an arbitrary list with the same lookup behaviour (finding BR-5).
/// `binding_extends muf muo` is the strongest statement that survives
/// that representation gap, and Part 12 shows it is enough: `muo` and
/// `muf` instantiate the BGP to the SAME triples.
let rec theorem_eval_bgp_store_complete_fuel
      (patterns : bgp) (gs : graph_store) (mu muf : solution_mapping) (fuel : nat)
  : Lemma (requires fuel >= List.Tot.length patterns /\
                    R.smap_exact mu /\ bgp_frag patterns /\ graph_frag gs.gs_graph /\
                    store_search_complete gs /\
                    R.binding_extends muf mu /\
                    bgp_subgraph_clause patterns gs.gs_graph muf)
          (ensures  bgp_complete_goal patterns gs mu muf fuel)
          (decreases fuel) =
  if fuel = 0 then
    (R.lemma_binding_extends_refl mu;
     introduce exists (muo : solution_mapping).
         List.Tot.memP muo (eval_bgp_store_from_mu_fuel patterns gs mu fuel) /\
         R.binding_extends muf muo /\ R.binding_extends muo mu /\ R.smap_exact muo
     with mu and ())
  else
    match patterns with
    | [] ->
      (R.lemma_binding_extends_refl mu;
       introduce exists (muo : solution_mapping).
           List.Tot.memP muo (eval_bgp_store_from_mu_fuel patterns gs mu fuel) /\
           R.binding_extends muf muo /\ R.binding_extends muo mu /\ R.smap_exact muo
       with mu and ())
    | hd :: tl ->
      lemma_choose_best_tp_cover patterns gs mu;
      (match choose_best_tp patterns gs mu with
       | None -> ()
       | Some (tp, rest) ->
         assert (tp_frag tp);
         assert (choose_best_tp patterns gs mu == Some (tp, rest));
         let finish (mu' : solution_mapping)
           : Lemma (requires List.Tot.memP mu' (eval_single_tp_store tp gs mu) /\
                             R.binding_extends muf mu' /\ R.binding_extends mu' mu /\
                             R.smap_exact mu')
                   (ensures  bgp_complete_goal patterns gs mu muf fuel) =
           theorem_eval_bgp_store_complete_fuel rest gs mu' muf (fuel - 1);
           let land (muo : solution_mapping)
             : Lemma (requires List.Tot.memP muo
                                 (eval_bgp_store_from_mu_fuel rest gs mu' (fuel - 1)) /\
                               R.binding_extends muf muo /\ R.binding_extends muo mu' /\
                               R.smap_exact muo)
                     (ensures  bgp_complete_goal patterns gs mu muf fuel) =
             lemma_eval_bgp_store_step_intro hd tl gs mu mu' muo (fuel - 1) tp rest;
             R.lemma_binding_extends_trans muo mu' mu;
             introduce exists (muo2 : solution_mapping).
                 List.Tot.memP muo2 (eval_bgp_store_from_mu_fuel patterns gs mu fuel) /\
                 R.binding_extends muf muo2 /\ R.binding_extends muo2 mu /\
                 R.smap_exact muo2
             with muo and ()
           in
           FStar.Classical.forall_intro (FStar.Classical.move_requires land)
         in
         let step (t : triple)
           : Lemma (requires instantiate_tp tp muf == Some t /\ List.Tot.memP t gs.gs_graph)
                   (ensures  bgp_complete_goal patterns gs mu muf fuel) =
           lemma_eval_single_tp_complete_at tp gs mu muf t;
           FStar.Classical.forall_intro (FStar.Classical.move_requires finish)
         in
         FStar.Classical.forall_intro (FStar.Classical.move_requires step))
#pop-options

/// THE STORE-GENERIC SHIPPING STATEMENT, completeness half.
/// `List.Tot.length b + 1` is the fuel `eval_bgp_store` supplies, so
/// the fuel side condition is discharged here exactly as it is for
/// soundness.
let theorem_eval_bgp_store_complete (b : bgp) (gs : graph_store) (muf : solution_mapping)
  : Lemma (requires bgp_frag b /\ graph_frag gs.gs_graph /\ store_search_complete gs /\
                    bgp_subgraph_clause b gs.gs_graph muf)
          (ensures  (exists (muo : solution_mapping).
                       List.Tot.memP muo (eval_bgp_store b gs) /\
                       R.binding_extends muf muo /\ R.smap_exact muo)) =
  theorem_eval_bgp_store_complete_fuel b gs sm_empty muf (List.Tot.length b + 1)

let theorem_eval_bgp_complete (b : bgp) (g : rdf_graph) (muf : solution_mapping)
  : Lemma (requires bgp_frag b /\ graph_frag g /\ bgp_subgraph_clause b g muf)
          (ensures  (exists (muo : solution_mapping).
                       List.Tot.memP muo (eval_bgp b g) /\
                       R.binding_extends muf muo /\ R.smap_exact muo)) =
  lemma_graph_to_store_complete g;
  theorem_eval_bgp_store_complete b (graph_to_store g) muf

(** ====================================================================== **)
(** Part 12: from `binding_extends` to the SAME ANSWER                     **)
(**                                                                        **)
(** Finding BR-5 in force: `memP muf (eval_bgp b g)` is NOT provable and   **)
(** not because of a missing lemma -- `solution_mapping` is an             **)
(** association LIST and `sm_bind` conses, so the engine emits one         **)
(** specific permutation, fixed by `choose_best_tp`'s cost ordering over   **)
(** the actual data. The statement that IS true, and that every            **)
(** downstream consumer actually uses, is at the ANSWER level: the engine  **)
(** returns a solution that instantiates the BGP to exactly the same       **)
(** triples. Everything in SPARQL11.EntailmentRegime.RDFS speaks           **)
(** `instantiate_bgp q mu` and nothing there inspects the list, so this    **)
(** loses nothing there. The residual -- upgrading to `S.smap_eq muo muf`  **)
(** -- is the DOMAIN clause `dom(mu) = var(BGP)` that Part 6's             **)
(** `lemma_bgp_sol_spec_from_subgraph_clause` already names as a separate  **)
(** commit; it is `sm_bind` bookkeeping, not graph mathematics.            **)
(** ====================================================================== **)

let lemma_instantiate_tp_mono
      (tp : triple_pattern) (mu muf : solution_mapping) (t : triple)
  : Lemma (requires R.binding_extends muf mu /\ instantiate_tp tp mu == Some t /\
                    R.ptrm_tt_free tp.tp_o)
          (ensures  instantiate_tp tp muf == Some t) =
  lemma_bound_subject_mono tp.tp_s mu muf t.s;
  lemma_bound_predicate_mono tp.tp_p mu muf t.p;
  lemma_bound_object_mono tp.tp_o mu muf t.o

let rec lemma_instantiate_bgp_agree (b : bgp) (mu muf : solution_mapping)
  : Lemma (requires R.binding_extends muf mu /\
                    (forall (p : triple_pattern). List.Tot.memP p b ==>
                       (R.ptrm_tt_free p.tp_o /\ Some? (instantiate_tp p mu))))
          (ensures  instantiate_bgp b muf == instantiate_bgp b mu)
          (decreases b) =
  match b with
  | [] -> ()
  | p :: rest ->
    lemma_instantiate_bgp_agree rest mu muf;
    (match instantiate_tp p mu with
     | Some t -> lemma_instantiate_tp_mono p mu muf t
     | None -> ())

/// The `bgp_subgraph_clause` form recovered from the two facts a
/// caller actually has: the instantiated BGP is inside the graph, and
/// every pattern instantiates. The second is not implied by the first
/// -- `instantiate_bgp` SILENTLY DROPS a pattern it cannot instantiate
/// (SPARQL11.Algebra.fst:7557-7564) -- so it is a hypothesis.
let rec lemma_subgraph_clause_of_instantiated (b : bgp) (g : rdf_graph) (mu : solution_mapping)
  : Lemma (requires (forall (t : triple).
                       List.Tot.memP t (instantiate_bgp b mu) ==> List.Tot.memP t g) /\
                    (forall (p : triple_pattern). List.Tot.memP p b ==>
                       Some? (instantiate_tp p mu)))
          (ensures  bgp_subgraph_clause b g mu)
          (decreases b) =
  match b with
  | [] -> ()
  | p :: rest ->
    lemma_subgraph_clause_of_instantiated rest g mu;
    (match instantiate_tp p mu with
     | Some t -> ()
     | None -> ())

#push-options "--z3rlimit 400 --fuel 2 --ifuel 2"
/// THE ANSWER-LEVEL COMPLETENESS THEOREM -- finding BR-4 discharged in
/// the form layer 3 consumes, at any store that is BOTH sound and
/// complete. If any mapping explains the BGP inside the store's graph,
/// `eval_bgp_store` returns a solution with the SAME instantiated BGP.
///
/// The proof composes both halves of layer 2: completeness produces a
/// `muo` under `muf`, and then SOUNDNESS applied to that very `muo`
/// supplies the missing "every pattern instantiates under `muo`" fact
/// which turns `binding_extends` into answer equality.
let theorem_eval_bgp_store_complete_answer
      (b : bgp) (gs : graph_store) (muf : solution_mapping)
  : Lemma (requires bgp_frag b /\ graph_frag gs.gs_graph /\
                    store_search_sound gs /\ store_search_complete gs /\
                    bgp_subgraph_clause b gs.gs_graph muf)
          (ensures  (exists (muo : solution_mapping).
                       List.Tot.memP muo (eval_bgp_store b gs) /\
                       instantiate_bgp b muo == instantiate_bgp b muf)) =
  theorem_eval_bgp_store_complete b gs muf;
  let aux (muo : solution_mapping)
    : Lemma (requires List.Tot.memP muo (eval_bgp_store b gs) /\ R.binding_extends muf muo)
            (ensures  (exists (mu2 : solution_mapping).
                         List.Tot.memP mu2 (eval_bgp_store b gs) /\
                         instantiate_bgp b mu2 == instantiate_bgp b muf)) =
    theorem_eval_bgp_store_subgraph b gs muo;
    lemma_instantiate_bgp_agree b muo muf;
    introduce exists (mu2 : solution_mapping).
        List.Tot.memP mu2 (eval_bgp_store b gs) /\
        instantiate_bgp b mu2 == instantiate_bgp b muf
    with muo and ()
  in FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

/// The same theorem from the hypotheses layer 3 actually has: the
/// instantiated BGP is a subset of the graph, and every pattern
/// instantiates (the second is finding RT-6 of layer 3).
let theorem_eval_bgp_store_complete_from_subset
      (b : bgp) (gs : graph_store) (muf : solution_mapping)
  : Lemma (requires bgp_frag b /\ graph_frag gs.gs_graph /\
                    store_search_sound gs /\ store_search_complete gs /\
                    (forall (t : triple).
                       List.Tot.memP t (instantiate_bgp b muf) ==>
                       List.Tot.memP t gs.gs_graph) /\
                    (forall (p : triple_pattern). List.Tot.memP p b ==>
                       Some? (instantiate_tp p muf)))
          (ensures  (exists (muo : solution_mapping).
                       List.Tot.memP muo (eval_bgp_store b gs) /\
                       instantiate_bgp b muo == instantiate_bgp b muf)) =
  lemma_subgraph_clause_of_instantiated b gs.gs_graph muf;
  theorem_eval_bgp_store_complete_answer b gs muf

/// THE FULL-INDEX SPECIALISATION -- the `eval_bgp` form.
let theorem_eval_bgp_complete_from_subset (b : bgp) (g : rdf_graph) (muf : solution_mapping)
  : Lemma (requires bgp_frag b /\ graph_frag g /\
                    (forall (t : triple).
                       List.Tot.memP t (instantiate_bgp b muf) ==> List.Tot.memP t g) /\
                    (forall (p : triple_pattern). List.Tot.memP p b ==>
                       Some? (instantiate_tp p muf)))
          (ensures  (exists (muo : solution_mapping).
                       List.Tot.memP muo (eval_bgp b g) /\
                       instantiate_bgp b muo == instantiate_bgp b muf)) =
  lemma_graph_to_store_sound g;
  lemma_graph_to_store_complete g;
  theorem_eval_bgp_store_complete_from_subset b (graph_to_store g) muf

/// THE SELECTIVE-STORE SPECIALISATION (finding RT-2's store, finding
/// BR-4's direction). `graph_to_store_for` is what
/// `eval_pattern`/`eval_ask_query` actually build, so this is the
/// completeness counterpart of
/// `theorem_eval_bgp_store_for_instantiates_into_graph`.
let theorem_eval_bgp_store_for_complete_from_subset
      (p : group_graph_pattern) (b : bgp) (g : rdf_graph) (muf : solution_mapping)
  : Lemma (requires bgp_frag b /\ graph_frag g /\
                    (forall (t : triple).
                       List.Tot.memP t (instantiate_bgp b muf) ==> List.Tot.memP t g) /\
                    (forall (q : triple_pattern). List.Tot.memP q b ==>
                       Some? (instantiate_tp q muf)))
          (ensures  (exists (muo : solution_mapping).
                       List.Tot.memP muo (eval_bgp_store b (graph_to_store_for p g)) /\
                       instantiate_bgp b muo == instantiate_bgp b muf)) =
  lemma_graph_to_store_for_sound p g;
  lemma_graph_to_store_for_complete p g;
  theorem_eval_bgp_store_complete_from_subset b (graph_to_store_for p g) muf
#pop-options

(** ====================================================================== **)
(** Part 13: THE DOMAIN CLAUSE -- dom(mu) = var(BGP)                       **)
(**                                                                        **)
(** The residual finding BR-5 and Part 6's `lemma_bgp_sol_spec_from_       **)
(** subgraph_clause` both named as a separate commit: `S.bgp_sol_spec`'s   **)
(** SECOND conjunct,                                                       **)
(**                                                                        **)
(**   forall v. Some? (sval v mu) <==>                                    **)
(**     (exists p. memP p b /\ memP v (patvars p))                        **)
(**                                                                        **)
(** is about `sm_bind` bookkeeping, not graph content -- so the proof       **)
(** below never reads a store, a probe, or a graph triple. It is the      **)
(** SAME induction shape as Part 6/8's subgraph clause (an accumulator     **)
(** search over `eval_bgp_store_from_mu_fuel`, threading `choose_best_tp`'s **)
(** cover fact through `lemma_eval_bgp_store_step`), generalised over an   **)
(** ARBITRARY starting mapping `mu` so the recursion composes: the         **)
(** induction hypothesis needs "dom(muf) = dom(mu') UNION var(rest)" at    **)
(** the recursive call, not "dom(muf) = var(rest)" alone, because the      **)
(** search carries the ACCUMULATED mapping forward, not a fresh one, at    **)
(** each step (mirrors `R.binding_extends` in Part 6/8). Specialising at   **)
(** `mu := sm_empty` (whose domain is empty) turns the growth statement    **)
(** into the exact residual clause.                                       **)
(**                                                                        **)
(** Two things the induction must get right, both flagged in the task     **)
(** brief:                                                                 **)
(**  - A bnode/constant pattern position (`PS_IRI`/`PS_BNode`/`PT_IRI`/    **)
(**    `PT_BNode`/`PT_Literal`) binds NOTHING: `try_bind_subject` /        **)
(**    `try_bind_term` return the mapping UNCHANGED on that branch, and    **)
(**    `pattern_subject_var` / `pattern_term_var` return `[]` for it, so   **)
(**    the growth equation holds with an empty contributed set -- not a    **)
(**    special case, the same formula degenerates correctly.               **)
(**  - Finding RT-5 (binding ORDER is evaluator-chosen, via `choose_best_  **)
(**    tp`'s cost estimates, and NOT reproducible by a caller) is a        **)
(**    statement about the association LIST's structure. The domain        **)
(**    clause is a SET-level statement (`Some? (sval v mu)`, an existence   **)
(**    check, never a position or an order), so RT-5 does not touch it:    **)
(**    `lemma_bgp_vars_cover` below combines `choose_best_tp`'s cover fact  **)
(**    (patterns = {tp} UNION rest, as sets, via `lemma_choose_best_tp_    **)
(**    cover`) with no reference to list order at all.                    **)
(** ====================================================================== **)

#push-options "--z3rlimit 200 --fuel 2 --ifuel 2"

/// A pattern position that binds nothing contributes no variable and no
/// domain growth: `try_bind_subject` on a constant subject returns the
/// mapping UNCHANGED (never `sm_bind`s), and `pattern_subject_var` of a
/// constant is `[]`. `PS_TripleTerm` is excluded by `psub_tt_free` (as
/// throughout this module); it always returns `None`, so the `Some mu'`
/// hypothesis makes that branch vacuous.
let lemma_try_bind_subject_domain
      (ps : pattern_subject) (sj : subject) (mu mu' : solution_mapping)
  : Lemma (requires try_bind_subject ps sj mu == Some mu' /\ R.psub_tt_free ps)
          (ensures  forall (v : S.var_name).
                       Some? (S.sval v mu') <==>
                       (Some? (S.sval v mu) \/ List.Tot.memP v (pattern_subject_var ps))) =
  match ps with
  | PS_Var v0 ->
    Lh.lemma_assoc_tr_eq v0 mu;
    (match sm_lookup v0 mu with
     | Some existing ->
       assert (mu' == mu);
       let aux (w : S.var_name)
         : Lemma (Some? (S.sval w mu') <==>
                    (Some? (S.sval w mu) \/ List.Tot.memP w (pattern_subject_var ps))) = ()
       in FStar.Classical.forall_intro aux
     | None ->
       let aux (w : S.var_name)
         : Lemma (Some? (S.sval w mu') <==>
                    (Some? (S.sval w mu) \/ List.Tot.memP w (pattern_subject_var ps))) =
         lemma_sm_bind_sval v0 w (subject_to_term sj) mu
       in FStar.Classical.forall_intro aux)
  | _ -> ()

/// Same statement for `try_bind_term` / `pattern_term_var`. RDF 1.2
/// triple-term patterns are excluded by `ptrm_tt_free`, as everywhere
/// else in this module -- the recursive case is not needed on the
/// fragment this module proves.
let lemma_try_bind_term_domain
      (pt : pattern_term) (t : rdf_term) (mu mu' : solution_mapping)
  : Lemma (requires try_bind_term pt t mu == Some mu' /\ R.ptrm_tt_free pt)
          (ensures  forall (v : S.var_name).
                       Some? (S.sval v mu') <==>
                       (Some? (S.sval v mu) \/ List.Tot.memP v (pattern_term_var pt))) =
  match pt with
  | PT_Var v0 ->
    Lh.lemma_assoc_tr_eq v0 mu;
    (match sm_lookup v0 mu with
     | Some existing ->
       assert (mu' == mu);
       let aux (w : S.var_name)
         : Lemma (Some? (S.sval w mu') <==>
                    (Some? (S.sval w mu) \/ List.Tot.memP w (pattern_term_var pt))) = ()
       in FStar.Classical.forall_intro aux
     | None ->
       let aux (w : S.var_name)
         : Lemma (Some? (S.sval w mu') <==>
                    (Some? (S.sval w mu) \/ List.Tot.memP w (pattern_term_var pt))) =
         lemma_sm_bind_sval v0 w t mu
       in FStar.Classical.forall_intro aux)
  | _ -> ()

/// One triple pattern: `tp_match` threads subject -> predicate ->
/// object, so its domain growth is the UNION of the three positions'
/// contributed variables, which is exactly `tp_vars`.
let lemma_tp_match_domain
      (tp : triple_pattern) (t : triple) (mu mu' : solution_mapping)
  : Lemma (requires tp_match tp t mu == Some mu' /\
                    R.psub_tt_free tp.tp_s /\
                    R.ptrm_tt_free tp.tp_p /\ R.ptrm_tt_free tp.tp_o)
          (ensures  forall (v : S.var_name).
                       Some? (S.sval v mu') <==>
                       (Some? (S.sval v mu) \/ List.Tot.memP v (tp_vars tp))) =
  let mu1 = Some?.v (try_bind_subject tp.tp_s t.s mu) in
  lemma_try_bind_subject_domain tp.tp_s t.s mu mu1;
  let mu2 = Some?.v (try_bind_term tp.tp_p (T_IRI t.p) mu1) in
  lemma_try_bind_term_domain tp.tp_p (T_IRI t.p) mu1 mu2;
  lemma_try_bind_term_domain tp.tp_o t.o mu2 mu';
  let aux (v : S.var_name)
    : Lemma (Some? (S.sval v mu') <==>
               (Some? (S.sval v mu) \/ List.Tot.memP v (tp_vars tp))) =
    List.Tot.append_memP (pattern_term_var tp.tp_p) (pattern_term_var tp.tp_o) v;
    List.Tot.append_memP (pattern_subject_var tp.tp_s)
      (List.Tot.append (pattern_term_var tp.tp_p) (pattern_term_var tp.tp_o)) v
  in FStar.Classical.forall_intro aux

/// One fan-out step at the store: whatever `mu'` the single-pattern
/// evaluator returns, its domain is `dom(mu) UNION tp_vars tp`. Routed
/// through the same `list_filter_map` membership lemma Part 4 uses for
/// soundness, and through the same fulltext-dispatch equality Part 6
/// establishes for `choose_best_tp`'s chosen pattern (finding BR-1: the
/// fragment's `tp_not_fulltext` makes the dispatcher the default path).
let lemma_eval_single_tp_store_domain
      (tp : triple_pattern) (gs : graph_store) (mu mu' : solution_mapping)
  : Lemma (requires List.Tot.memP mu' (eval_single_tp_store tp gs mu) /\
                    tp_frag tp)
          (ensures  forall (v : S.var_name).
                       Some? (S.sval v mu') <==>
                       (Some? (S.sval v mu) \/ List.Tot.memP v (tp_vars tp))) =
  lemma_eval_single_tp_store_default_eq tp gs mu;
  let bound = {
    bs = bound_subject_of_pattern tp.tp_s mu;
    bp = bound_predicate_of_pattern tp.tp_p mu;
    bo = bound_object_of_pattern tp.tp_o mu;
  } in
  let candidates = store_search gs bound in
  R.lemma_memP_filter_map (fun (t : triple) -> tp_match tp t mu) candidates mu';
  eliminate exists (t : triple).
      List.Tot.memP t candidates /\ tp_match tp t mu == Some mu'
  returns (forall (v : S.var_name).
             Some? (S.sval v mu') <==>
             (Some? (S.sval v mu) \/ List.Tot.memP v (tp_vars tp)))
  with _ . lemma_tp_match_domain tp t mu mu'

/// `choose_best_tp`'s cover fact (Part 5), read at the level of
/// VARIABLE SETS rather than pattern lists: the variables reachable
/// from the whole BGP are exactly the chosen pattern's variables union
/// the remainder's -- independent of `rest`'s ORDER (finding RT-5 does
/// not reach this statement; it is about the returned MAPPING's list
/// structure, not about which patterns cover the BGP).
let lemma_bgp_vars_cover
      (patterns : bgp) (tp : triple_pattern) (rest : bgp)
  : Lemma (requires Cons? patterns /\ List.Tot.memP tp patterns /\
                    (forall (p : triple_pattern). List.Tot.memP p rest ==>
                        List.Tot.memP p patterns) /\
                    (forall (p : triple_pattern). List.Tot.memP p patterns ==>
                        (p == tp \/ List.Tot.memP p rest)))
          (ensures  forall (v : S.var_name).
                       (exists (p : triple_pattern).
                          List.Tot.memP p patterns /\ List.Tot.memP v (tp_vars p)) <==>
                       (List.Tot.memP v (tp_vars tp) \/
                        (exists (p : triple_pattern).
                           List.Tot.memP p rest /\ List.Tot.memP v (tp_vars p)))) =
  let aux (v : S.var_name)
    : Lemma ((exists (p : triple_pattern).
                 List.Tot.memP p patterns /\ List.Tot.memP v (tp_vars p)) <==>
             (List.Tot.memP v (tp_vars tp) \/
              (exists (p : triple_pattern).
                 List.Tot.memP p rest /\ List.Tot.memP v (tp_vars p)))) = ()
  in FStar.Classical.forall_intro aux

/// THE DOMAIN-GROWTH CLAUSE, in the form the induction carries: `muf`'s
/// domain is `mu`'s domain UNION the BGP's variables. Composes with
/// `R.binding_extends` (Part 6/8's carried invariant) the same way:
/// both are properties of the ACCUMULATED mapping at the end of the
/// fuel-bounded search, not of any one step in isolation.
let bgp_dom_grow_clause (patterns : bgp) (mu muf : solution_mapping) : prop =
  forall (v : S.var_name).
    Some? (S.sval v muf) <==>
    (Some? (S.sval v mu) \/
     (exists (p : triple_pattern). List.Tot.memP p patterns /\ List.Tot.memP v (tp_vars p)))

/// THE INDUCTION. Same recursion, same case split, same two helper
/// facts (`lemma_choose_best_tp_cover`, `lemma_eval_bgp_store_step`) as
/// `theorem_eval_bgp_store_sound_fuel` (Part 8) -- this is that proof's
/// SKELETON with the conclusion swapped from `bgp_subgraph_clause` (a
/// graph-content fact) to `bgp_dom_grow_clause` (an `sm_bind`-bookkeeping
/// fact), and correspondingly the one per-step lemma swapped from
/// `lemma_eval_single_tp_sound_at` to `lemma_eval_single_tp_store_domain`.
/// Store-generic exactly as Part 8 is, and for the same reason: nothing
/// about which variables get bound depends on how the store was built.
let rec theorem_eval_bgp_store_domain_fuel
      (patterns : bgp) (gs : graph_store) (mu muf : solution_mapping) (fuel : nat)
  : Lemma (requires List.Tot.memP muf
                      (eval_bgp_store_from_mu_fuel patterns gs mu fuel) /\
                    fuel >= List.Tot.length patterns /\ bgp_frag patterns)
          (ensures  bgp_dom_grow_clause patterns mu muf)
          (decreases fuel) =
  if fuel = 0 then ()
  else
    match patterns with
    | [] -> ()
    | hd :: tl ->
      lemma_choose_best_tp_cover patterns gs mu;
      (match choose_best_tp patterns gs mu with
       | None -> ()
       | Some (tp, rest) ->
         assert (tp_frag tp);
         lemma_eval_single_tp_store_default_eq tp gs mu;
         assert (choose_best_tp patterns gs mu == Some (tp, rest));
         lemma_eval_bgp_store_step hd tl gs mu muf (fuel - 1) tp rest;
         let step (mu' : solution_mapping)
           : Lemma (requires List.Tot.memP mu' (eval_single_tp_store tp gs mu) /\
                             List.Tot.memP muf
                               (eval_bgp_store_from_mu_fuel rest gs mu' (fuel - 1)))
                   (ensures  bgp_dom_grow_clause patterns mu muf) =
           lemma_eval_single_tp_store_domain tp gs mu mu';
           theorem_eval_bgp_store_domain_fuel rest gs mu' muf (fuel - 1);
           lemma_bgp_vars_cover patterns tp rest;
           let aux (v : S.var_name)
             : Lemma (Some? (S.sval v muf) <==>
                        (Some? (S.sval v mu) \/
                         (exists (p : triple_pattern).
                            List.Tot.memP p patterns /\ List.Tot.memP v (tp_vars p)))) = ()
           in FStar.Classical.forall_intro aux
         in
         FStar.Classical.forall_intro (FStar.Classical.move_requires step))

/// The `eval_bgp` specialisation, starting mapping `sm_empty`.
let theorem_eval_bgp_domain (b : bgp) (g : rdf_graph) (mu : solution_mapping)
  : Lemma (requires List.Tot.memP mu (eval_bgp b g) /\ bgp_frag b)
          (ensures  bgp_dom_grow_clause b sm_empty mu) =
  theorem_eval_bgp_store_domain_fuel b (graph_to_store g) sm_empty mu (List.Tot.length b + 1)

/// THE RESIDUAL CLAUSE ITSELF -- `S.bgp_sol_spec`'s second conjunct,
/// transcribed at `patvars := tp_vars`: `dom(mu) = var(BGP)`.
/// `bgp_dom_grow_clause b sm_empty mu` degenerates to exactly this once
/// `sm_empty`'s domain is recognised as empty (`sval` of `[]` is always
/// `None`).
let bgp_dom_clause (b : bgp) (mu : solution_mapping) : prop =
  forall (v : S.var_name).
    Some? (S.sval v mu) <==>
    (exists (p : triple_pattern). List.Tot.memP p b /\ List.Tot.memP v (tp_vars p))

let theorem_eval_bgp_dom_clause (b : bgp) (g : rdf_graph) (mu : solution_mapping)
  : Lemma (requires List.Tot.memP mu (eval_bgp b g) /\ bgp_frag b)
          (ensures  bgp_dom_clause b mu) =
  theorem_eval_bgp_domain b g mu

/// THE CAPSTONE -- BOTH CONJUNCTS OF `S.bgp_sol_spec`, at the shipping
/// evaluator, closing the loop between `eval_bgp` and the declarative
/// section-18.3.1 spec: every mapping `eval_bgp` returns is a solution
/// of the BGP in the FULL sense the spec module states, `patvars :=
/// tp_vars`. Composes `theorem_eval_bgp_subgraph` (conjunct 1, Part 6),
/// `theorem_eval_bgp_dom_clause` (conjunct 2, above), and
/// `lemma_bgp_sol_spec_from_subgraph_clause` (Part 6's machine-checked
/// tie-back that the two conjuncts together ARE `S.bgp_sol_spec`).
let theorem_eval_bgp_full_spec (b : bgp) (g : rdf_graph) (mu : solution_mapping)
  : Lemma (requires List.Tot.memP mu (eval_bgp b g) /\ bgp_frag b /\ graph_frag g)
          (ensures  S.bgp_sol_spec
                      (fun (m : S.smap) (p : triple_pattern) -> instantiate_tp p m)
                      tp_vars b g mu) =
  theorem_eval_bgp_subgraph b g mu;
  theorem_eval_bgp_dom_clause b g mu;
  lemma_bgp_sol_spec_from_subgraph_clause b g mu tp_vars

#pop-options

#pop-options
