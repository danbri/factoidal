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
// This module proves the SOUNDNESS half of that set equality against
// the SHIPPING evaluator -- `SPARQL11.Algebra.eval_bgp`, the function
// the engine actually calls -- for an ARBITRARY fixed graph. Nothing
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
// BR-4. COMPLETENESS IS BLOCKED ON INDEX COMPLETENESS, AND THE BLOCK
//   IS NARROW AND NAMED. The converse ("every subset-matching mu is
//   in `eval_bgp b g`") needs: every graph triple satisfying the
//   probe's bound positions is returned by `ig_search`. `ig_search`
//   (SPARQL11.Algebra.fst:236) narrows to ONE bucket chosen by
//   `pick_smaller_bucket` over six candidates. Completeness is proved
//   today for the PREDICATE bucket only
//   (RDF.Indexed.Completeness.lemma_build_indexed_complete_pred,
//   2026-08-05); there is no analogue for ig_subj / ig_obj / ig_sp /
//   ig_po / ig_so. Worse for the object-keyed buckets: the probe
//   accepts a candidate on `rdf_term_eq` (coarse -- see finding SR-2
//   of SPARQL11.Algebra.Refinement) while the bucket keys on
//   `term_to_key_opt` (byte-exact), so `"x"@en` and `"x"@EN` are
//   probe-equal and land in different buckets. Completeness of
//   `ig_search` in the object-bound case is thus not merely unproved,
//   it is expected to be FALSE outside the `term_exact` fragment.
//   Stated, not attempted. Soundness -- this module -- needs none of
//   that, because `triple_matches_bound` re-checks every candidate
//   against the ACTUAL bound before returning it.
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

#pop-options
