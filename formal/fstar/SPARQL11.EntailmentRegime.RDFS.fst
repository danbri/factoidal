module SPARQL11.EntailmentRegime.RDFS

// ===================================================================
// LAYER 3 of the G3/M3 query-rung reduction -- THE COMPOSED REGIME
// THEOREM (docs/designissues/2026-08-06-query-rung-design.md).
//
// The design doc factors "SPARQL under the RDFS entailment regime
// returns the regime-defined answers on the rho-df fragment" into
// three layers. Layer 1 is `RDF.Entailment.RDFS.RhoDFClosure.
// rho_df_closure_decides` (landed 8aaa655, strengthened 4fff958).
// Layer 2 is `SPARQL11.Algebra.BGPRefinement.theorem_eval_bgp_
// instantiates_into_graph` (landed 30beac8). This module is layer 3:
// it JOINS them, at the graph `rho_df_closure g fuel`, and states the
// ASK corollary.
//
// -------------------------------------------------------------------
// NAMING
// -------------------------------------------------------------------
// `SPARQL11.Algebra.BGPRefinement`'s own banner sets the family rule:
// a module goes in the `SPARQL11.Algebra.*` family when it refines a
// named shipping function of `SPARQL11.Algebra` and MENTIONS NO
// ENTAILMENT RELATION. This module mentions two (`rho_df_entails`
// and `simple_entailment_spec`) and refines nothing new, so it does
// not belong there. It is named after the W3C document whose
// statement it discharges -- SPARQL 1.1 Entailment Regimes (W3C
// Recommendation 21 March 2013), section 2 (the regime redefines BGP
// matching only) and section 6 (the RDFS regime) -- with the regime
// name as the last component, so a future D-entailment or OWL-RL
// regime theorem gets a sibling rather than a rename.
//
// -------------------------------------------------------------------
// WHAT IS PROVED, AND WHAT IS NOT
// -------------------------------------------------------------------
// PROVED (unconditional, modulo the enumerated hypotheses):
//   SOUNDNESS -- every solution the shipping `eval_bgp` returns over
//   the rho-df closure is a solution the RDFS regime licenses:
//     memP mu (eval_bgp q c)  ==>  g rho-df-entails mu(q)
//   (`theorem_rdfs_regime_bgp_sound`). This is the direction an
//   engine's answers have to satisfy for its output to be correct.
//
// NOT PROVED, and named rather than assumed:
//   COMPLETENESS -- the converse. It composes `rho_df_closure_
//   decides` LEFT-to-right with layer 2's completeness, and layer 2's
//   completeness is BLOCKED (finding BR-4 of SPARQL11.Algebra.
//   BGPRefinement: `ig_search` narrows to one of six index buckets and
//   only the PREDICATE bucket has a completeness lemma; for the
//   object-keyed buckets completeness is expected to be FALSE outside
//   the `term_exact` fragment, because the probe accepts on
//   `rdf_term_eq` while the bucket keys on `term_to_key_opt`).
//   So the converse is stated CONDITIONALLY, on an explicitly named
//   `eval_bgp_complete_at` hypothesis (part 6) that says exactly what
//   is missing and nothing more. `theorem_rdfs_regime_bgp_exact` is
//   the iff under that hypothesis; it is the shape M3 wants, with its
//   one open obligation carried in plain sight rather than folded in.
//
// -------------------------------------------------------------------
// FINDINGS
// -------------------------------------------------------------------
// RT-1. THE GROUND COLLAPSE HOLDS ONE WAY UNCONDITIONALLY AND THE
//   OTHER WAY ONLY FOR GROUND `e`. `rho_df_closure_decides` speaks
//   `simple_entailment_spec c e`, layer 2 delivers `e subset-of c`.
//   Part 3 below proves both halves separately, and the asymmetry is
//   what makes the soundness theorem need NO groundness hypothesis at
//   all: `is_subgraph e c ==> simple_entailment_spec c e` holds for
//   EVERY `e`, via the identity substitution (`lemma_subgraph_
//   implies_spec`, proved for arbitrary `e` including RDF 1.2 triple
//   terms). Only the completeness direction needs `graph_ground e`,
//   and it is required only there. An earlier reading of the brief
//   would have put `graph_ground` on the soundness statement too;
//   that would have been a silent strengthening of a theorem that
//   does not need it.
//
// RT-2. THE SHIPPING ASK ENTRY POINT DOES NOT GO THROUGH `eval_bgp` --
//   RESOLVED, part 8. `SPARQL11.Algebra.eval_ask_query` calls
//   `eval_pattern`, which builds its store with `graph_to_store_for`
//   (SPARQL11.Algebra.fst:3588) -- `build_indexed_selective
//   (bucket_needs_of_pattern p) g`, NOT the `build_indexed g` that
//   `eval_bgp` uses via `graph_to_store`. Layer 2's index-probe
//   soundness lemma (`BR.lemma_ig_search_sound`) was proved for
//   `build_indexed` only, so the ASK corollary was originally stated
//   at `eval_bgp`, with the gap recorded by a machine-checked equation
//   (`lemma_eval_pattern_bgp_is_selective_store`, part 7) rather than
//   by comment.
//   RESOLUTION (SPARQL11.Algebra.BGPRefinement.fst parts 2b/8):
//   `lemma_ig_search_sound_selective` proves the selective-index probe
//   sound for EVERY `bucket_needs`, not just the all-true one
//   `build_indexed` passes -- an omitted bucket's candidate is `None`
//   (gated by `ig_built`), never a consulted `BLeaf`, so it is
//   vacuously sound rather than needing a "falls back to the full
//   list" case of its own. `theorem_eval_bgp_store_for_instantiates_
//   into_graph` lifts that through the whole BGP fan-out induction
//   (generalised from `graph_to_store` to any store carrying the
//   probe-soundness property) to the store `graph_to_store_for`
//   actually builds. Part 8 of THIS module composes that with the
//   unchanged entailment bridge (parts 3-5) to restate soundness
//   (`theorem_rdfs_regime_bgp_sound_selective`,
//   `theorem_rdfs_regime_ask_pattern_sound`) and, finally, the
//   completeness-conditional mirror, at the literal shipping entry
//   point `eval_ask_query` itself
//   (`theorem_rdfs_regime_ask_query_sound`,
//   `theorem_rdfs_regime_ask_query_complete_conditional`), for the
//   bare-BGP/no-FROM/no-post-VALUES ASK shape. No entailment content
//   changed -- RT-2 was a store-selection finding, not a mathematical
//   one, exactly as originally recorded.
//
// RT-3. `graph_ground` SUBSUMES `graph_tt_free`. `rho_df_closure_
//   decides` carries `graph_tt_free e`. Rather than take it twice,
//   part 2 proves `graph_ground e ==> graph_tt_free e`
//   (`lemma_ground_implies_tt_free`) and part 4 derives the same
//   conclusion for the soundness route from `BR.graph_frag c` plus
//   the layer-2 subset -- so `graph_tt_free` never appears as a
//   hypothesis of a theorem in this module. Hypotheses that can be
//   discharged are discharged; the ones that cannot are enumerated.
//
// RT-4. "NO QUERY BLANK NODE" IS NOT SUFFICIENT FOR A GROUND ANSWER.
//   The decidable discharge route of part 2 first read
//   `psub_bnode_free` / `ptrm_bnode_free` -- exclude `PS_BNode` and
//   `PT_BNode`, nothing else. F* rejected `lemma_bound_object_ground`
//   against it, and the counterexample is the RDF 1.2 triple-term
//   pattern: `bound_object_of_pattern` on `PT_TripleTerm ps pp po`
//   returns `Some (T_TripleTerm ...)` (SPARQL11.Algebra.fst:397-409)
//   from ordinary IRI/literal sub-positions and no blank node
//   anywhere, and part 1 classifies a triple term as NOT ground on
//   purpose. The corrected predicates (`psub_ground_positions` /
//   `ptrm_ground_positions`) exclude both constructors. Caught by the
//   proof, not by review -- and it is a STATEMENT bug, not proof
//   engineering: the wrong version would have let a caller discharge
//   `graph_ground` for an answer that is not ground.
//
// No admit, no --lax, no --admit_smt_queries, no assume. z3 4.13.3.
// Zero change to any shipping module: this file only reads them.
// ===================================================================

open FStar.List.Tot
open RDF.Graph.Executable
open SPARQL11.Algebra

module Tm = RDF.Term
module G  = RDF.Graph
module BR = SPARQL11.Algebra.BGPRefinement
module R  = SPARQL11.Algebra.Refinement
module SS = RDF.Entailment.Simple.Spec
module RC = RDF.Entailment.RDFS.RhoDFClosure
module CP = RDF.Entailment.RDFS.Completeness
module FP = RDF.Entailment.RDFS.FixedPoint
module OS = OWL.Semantics
module IX = RDF.Indexed

#push-options "--z3rlimit 120 --fuel 2 --ifuel 3"

(** ====================================================================== **)
(** Part 1: GROUNDNESS                                                     **)
(**                                                                        **)
(** The scoping decision the brief asks to be stated explicitly.           **)
(**                                                                        **)
(** DECISION. Restrict the COMPLETENESS direction to solutions whose       **)
(** instantiated BGP is GROUND -- no blank node in any position -- and     **)
(** leave the SOUNDNESS direction unrestricted.                            **)
(**                                                                        **)
(** RATIONALE.                                                             **)
(**  (a) It is what the mathematics needs and no more (finding RT-1):      **)
(**      the collapse of `simple_entailment_spec c e` to `e subset-of c`   **)
(**      is an equivalence only when `e` is ground, because a non-ground   **)
(**      `e` may be entailed by an INSTANCE of itself sitting in `c`       **)
(**      without `e` itself being in `c`. Soundness uses only the          **)
(**      direction that holds for every `e`.                               **)
(**  (b) It matches the design doc's own C1 answer-restriction reading     **)
(**      ("terms of mu come from the graph's vocabulary union the query's  **)
(**      vocabulary"): a decidable sufficient condition for groundness     **)
(**      is `bgp_ground_positions q /\ smap_ground mu` (part 2), both checkable  **)
(**      per query and per solution.                                       **)
(**  (c) The alternative -- carrying non-ground answers through the        **)
(**      model-theoretic bnode-restriction lemma (`RDF.Entailment.Simple.  **)
(**      ModelTheory.graph_bnodes_complete`) -- would move the statement   **)
(**      from the syntactic interpolation form the whole vertical is       **)
(**      built on onto the satisfaction form, for a case the entailment-   **)
(**      regime suite does not exercise (finding BR-2: the shipping        **)
(**      matcher implements sigma = identity, so a query blank node is a   **)
(**      constant and a solution binding a variable to a data blank node   **)
(**      is exactly the case the completeness direction is blocked on for  **)
(**      an unrelated reason anyway).                                      **)
(**                                                                        **)
(** RDF 1.2 triple terms are NOT ground here. They have no denotation in   **)
(** either RDF-Semantics baseline (`SS.term_tt_free`'s quarantine), and    **)
(** treating them as ground would let a `graph_ground` hypothesis silently **)
(** discharge a `graph_tt_free` one that means something different. So the **)
(** clause is `False`, and finding RT-3's subsumption is real rather than  **)
(** definitional sleight of hand.                                          **)
(** ====================================================================== **)

let term_ground (t : rdf_term) : prop =
  match t with
  | T_IRI _            -> True
  | T_Literal _        -> True
  | T_BNode _          -> False
  | T_TripleTerm _ _ _ -> False

let subject_ground (s : subject) : prop =
  match s with
  | S_IRI _   -> True
  | S_BNode _ -> False

let triple_ground (t : triple) : prop = subject_ground t.s /\ term_ground t.o

let graph_ground (h : list triple) : prop =
  forall (t : triple). memP t h ==> triple_ground t

/// Finding RT-3: groundness is strictly stronger than the RDF 1.2
/// quarantine `rho_df_closure_decides` asks for.
let lemma_ground_implies_tt_free (h : list triple)
  : Lemma (requires graph_ground h) (ensures SS.graph_tt_free h) = ()

(** ====================================================================== **)
(** Part 2: a DECIDABLE sufficient condition for groundness                **)
(**                                                                        **)
(** Not needed by any theorem below -- it is the discharge route a caller  **)
(** uses to satisfy the completeness direction's `graph_ground` hypothesis **)
(** without inspecting the instantiated graph. Both conjuncts are          **)
(** syntactic checks on the query and on the candidate solution.           **)
(** ====================================================================== **)

/// FINDING RT-4 (caught by the proof, first verification run). The
/// obvious spelling of this predicate -- "no query blank node" --
/// is NOT sufficient for a ground answer, and F* refused
/// `lemma_bound_object_ground` until it was corrected. The RDF 1.2
/// case is the reason: `bound_object_of_pattern` on a
/// `PT_TripleTerm` returns `Some (T_TripleTerm ...)`
/// (SPARQL11.Algebra.fst:397-409), and part 1 classifies a triple
/// term as NOT ground, deliberately (a triple term has no denotation
/// in either RDF-Semantics baseline). So the position predicate has
/// to exclude BOTH the blank-node constant and the triple-term
/// constructor.
///
/// A caller already carrying `BR.bgp_frag q` gets the triple-term
/// half for free (`R.psub_tt_free` / `R.ptrm_tt_free` say the same
/// thing); the clause is repeated here so part 2 stands on its own
/// and does not silently inherit a layer-2 hypothesis.
let psub_ground_positions (ps : pattern_subject) : bool =
  match ps with
  | PS_BNode _            -> false
  | PS_TripleTerm _ _ _   -> false
  | _                     -> true

let ptrm_ground_positions (pt : pattern_term) : bool =
  match pt with
  | PT_BNode _            -> false
  | PT_TripleTerm _ _ _   -> false
  | _                     -> true

let tp_ground_positions (tp : triple_pattern) : prop =
  psub_ground_positions tp.tp_s == true /\ ptrm_ground_positions tp.tp_o == true

let bgp_ground_positions (b : bgp) : prop =
  forall (p : triple_pattern). memP p b ==> tp_ground_positions p

/// Every term a solution binds is ground. Stated over the LIST, in
/// the same shape as `R.smap_exact`, because `sm_lookup` walks it.
let rec smap_ground (mu : solution_mapping) : Tot prop (decreases mu) =
  match mu with
  | []            -> True
  | (_, t) :: rest -> term_ground t /\ smap_ground rest

let rec lemma_smap_ground_lookup (mu : solution_mapping) (v : string) (x : rdf_term)
  : Lemma (requires smap_ground mu /\ sm_lookup v mu == Some x)
          (ensures  term_ground x)
          (decreases mu) =
  match mu with
  | []             -> ()
  | (w, _) :: rest -> if w = v then () else lemma_smap_ground_lookup rest v x

let lemma_bound_subject_ground (ps : pattern_subject) (mu : solution_mapping) (s : subject)
  : Lemma (requires psub_ground_positions ps == true /\ smap_ground mu /\
                    bound_subject_of_pattern ps mu == Some s)
          (ensures  subject_ground s) =
  match ps with
  | PS_Var v ->
    (match sm_lookup v mu with
     | Some x -> lemma_smap_ground_lookup mu v x
     | None   -> ())
  | _ -> ()

let lemma_bound_object_ground (pt : pattern_term) (mu : solution_mapping) (o : rdf_term)
  : Lemma (requires ptrm_ground_positions pt == true /\ smap_ground mu /\
                    bound_object_of_pattern pt mu == Some o)
          (ensures  term_ground o) =
  match pt with
  | PT_Var v ->
    (match sm_lookup v mu with
     | Some x -> lemma_smap_ground_lookup mu v x
     | None   -> ())
  | _ -> ()

/// The three positions are matched in `instantiate_tp`'s OWN order and
/// spelling, so the definition delta-reduces onto the names the two
/// position lemmas are instantiated at; the record equation is then
/// asserted explicitly rather than left for SMT to reconstruct through
/// `Some?.v`.
let lemma_instantiate_tp_ground (tp : triple_pattern) (mu : solution_mapping) (t : triple)
  : Lemma (requires tp_ground_positions tp /\ smap_ground mu /\ instantiate_tp tp mu == Some t)
          (ensures  triple_ground t) =
  match bound_subject_of_pattern tp.tp_s mu with
  | None -> ()
  | Some s ->
    match bound_predicate_of_pattern tp.tp_p mu with
    | None -> ()
    | Some p ->
      match bound_object_of_pattern tp.tp_o mu with
      | None -> ()
      | Some o ->
        lemma_bound_subject_ground tp.tp_s mu s;
        lemma_bound_object_ground tp.tp_o mu o;
        assert (t == ({ s = s; p = p; o = o } <: triple));
        assert (t.s == s);
        assert (t.o == o);
        assert (subject_ground t.s);
        assert (term_ground t.o)

let rec lemma_instantiate_bgp_ground (b : bgp) (mu : solution_mapping)
  : Lemma (requires bgp_ground_positions b /\ smap_ground mu)
          (ensures  graph_ground (instantiate_bgp b mu))
          (decreases b) =
  match b with
  | []          -> ()
  | tp :: rest ->
    lemma_instantiate_bgp_ground rest mu;
    (match instantiate_tp tp mu with
     | None   -> ()
     | Some t -> lemma_instantiate_tp_ground tp mu t)

(** ====================================================================== **)
(** Part 3: THE GROUND-COLLAPSE BRIDGE LEMMA                               **)
(**                                                                        **)
(** `rho_df_closure_decides` decides `simple_entailment_spec c e`. Layer 2 **)
(** delivers `e subset-of c`. These are the two sides of the bridge, and   **)
(** the RDF 1.1 Semantics interpolation lemma is what makes them meet:     **)
(** "G simply entails E iff a subgraph of G is an instance of E". When E   **)
(** is ground its only instance is itself, so "a subgraph of G is an       **)
(** instance of E" degenerates to "E is a subgraph of G".                  **)
(** ====================================================================== **)

/// The identity substitution, as a NAMED function rather than a
/// lambda. `SS.bnode_subst = bnode_id -> rdf_term`, and a top-level
/// lambda bound to a name gets an opaque SMT symbol with no
/// congruence to anything (the closure-identity law); a named
/// function has the ordinary application encoding and beta-reduces
/// where the proof needs it.
let id_subst (l : Tm.bnode_id) : rdf_term = T_BNode l

let lemma_subj_inst_id (s : subject) : Lemma (SS.subj_inst id_subst s s) = ()

let rec lemma_term_inst_id (t : rdf_term)
  : Lemma (ensures SS.term_inst id_subst t t) (decreases t) =
  match t with
  | T_TripleTerm ps pp po ->
    lemma_subj_inst_id ps;
    lemma_term_inst_id po;
    introduce exists (gs : subject) (go : rdf_term).
        t == T_TripleTerm gs pp go /\
        SS.subj_inst id_subst ps gs /\ SS.term_inst id_subst po go
    with ps po and ()
  | _ -> ()

let lemma_triple_inst_id (t : triple) : Lemma (SS.triple_inst id_subst t t) =
  lemma_subj_inst_id t.s;
  lemma_term_inst_id t.o

/// HALF ONE -- unconditional. `e subset-of c ==> c simply entails e`,
/// for EVERY `e`, ground or not, triple terms included. This is the
/// half the soundness theorem consumes (finding RT-1).
let lemma_subgraph_implies_spec (c e : list triple)
  : Lemma (requires SS.is_subgraph e c)
          (ensures  SS.simple_entailment_spec c e) =
  introduce forall (tb : triple). memP tb e ==>
      (exists (ta : triple). memP ta c /\ SS.triple_inst id_subst tb ta)
  with introduce memP tb e ==>
         (exists (ta : triple). memP ta c /\ SS.triple_inst id_subst tb ta)
  with _ . begin
    lemma_triple_inst_id tb;
    introduce exists (ta : triple). memP ta c /\ SS.triple_inst id_subst tb ta
    with tb and ()
  end;
  introduce exists (m : SS.bnode_subst).
      forall (tb : triple). memP tb e ==>
        (exists (ta : triple). memP ta c /\ SS.triple_inst m tb ta)
  with id_subst and ()

/// A ground triple has exactly one instance: itself. (RDF 1.1
/// Semantics section 4: an instance replaces BLANK NODES; a triple
/// with no blank node in any position is fixed by every substitution.)
let lemma_triple_inst_ground (m : SS.bnode_subst) (tb ta : triple)
  : Lemma (requires triple_ground tb /\ SS.triple_inst m tb ta)
          (ensures  ta == tb) =
  assert (tb.p == ta.p);
  assert (SS.subj_inst m tb.s ta.s);
  assert (S_IRI? tb.s);
  assert (ta.s == tb.s);
  assert (T_IRI? tb.o \/ T_Literal? tb.o);
  assert (ta.o == tb.o)

/// HALF TWO -- ground only. `c simply entails e ==> e subset-of c`.
let lemma_spec_ground_implies_subgraph (c e : list triple)
  : Lemma (requires graph_ground e /\ SS.simple_entailment_spec c e)
          (ensures  SS.is_subgraph e c) =
  eliminate exists (m : SS.bnode_subst).
      forall (tb : triple). memP tb e ==>
        (exists (ta : triple). memP ta c /\ SS.triple_inst m tb ta)
  returns SS.is_subgraph e c
  with _ .
    introduce forall (t : triple). memP t e ==> memP t c
    with introduce memP t e ==> memP t c
    with _ .
      eliminate exists (ta : triple). memP ta c /\ SS.triple_inst m t ta
      returns memP t c
      with _ . lemma_triple_inst_ground m t ta

/// THE BRIDGE, as an iff at ground `e`.
let lemma_ground_entailment_collapse (c e : list triple)
  : Lemma (requires graph_ground e)
          (ensures  (SS.simple_entailment_spec c e <==> SS.is_subgraph e c)) =
  FStar.Classical.move_requires (lemma_spec_ground_implies_subgraph c) e;
  FStar.Classical.move_requires (lemma_subgraph_implies_spec c) e

(** ====================================================================== **)
(** Part 4: the RDF 1.2 quarantine, carried across the layer-2 subset      **)
(**                                                                        **)
(** `rho_df_closure_decides` takes `graph_tt_free e`. On the soundness     **)
(** route `e` is `instantiate_bgp q mu`, whose triples are all triples of  **)
(** `c` (layer 2), and `BR.graph_frag c` already says every object of `c`  **)
(** is triple-term free. So the hypothesis is DISCHARGED, not carried      **)
(** (finding RT-3).                                                        **)
(** ====================================================================== **)

let lemma_term_tt_free_bridge (t : rdf_term)
  : Lemma (requires R.term_tt_free t == true) (ensures SS.term_tt_free t) = ()

let lemma_graph_frag_tt_free (h : rdf_graph)
  : Lemma (requires BR.graph_frag h) (ensures SS.graph_tt_free h) =
  introduce forall (t : triple). memP t h ==> SS.term_tt_free t.o
  with introduce memP t h ==> SS.term_tt_free t.o
  with _ . lemma_term_tt_free_bridge t.o

let lemma_tt_free_subset (e h : list triple)
  : Lemma (requires SS.graph_tt_free h /\ SS.is_subgraph e h)
          (ensures  SS.graph_tt_free e) = ()

(** ====================================================================== **)
(** Part 5: THE HYPOTHESIS BUNDLE OF `rho_df_closure_decides`              **)
(**                                                                        **)
(** Transcribed VERBATIM from RDF.Entailment.RDFS.RhoDFClosure.fst:1701-   **)
(** 1710, minus the one clause that depends on the entailed graph `e`      **)
(** (`graph_tt_free e`, discharged separately -- part 4 and finding RT-3). **)
(** Not weakened and not strengthened: `lemma_decides_hyps_suffices` below **)
(** MACHINE-CHECKS that this bundle plus `graph_tt_free e` is enough to    **)
(** call the theorem, which catches any weakening; the verbatim            **)
(** transcription is what a reader checks against for strengthening.       **)
(** ====================================================================== **)

let rho_df_decides_hyps (g : rdf_graph) (fuel : nat) : prop =
  let c = RC.rho_df_closure g fuel in
  // --- chain conditions on the STARTING graph (M2's carried pair) ---
  RC.rho_df_chain_canonical g /\
  RC.rho_df_chain_wf g /\
  // --- fragment + index well-formedness at the CLOSURE ---
  //     (`rho_df_frag_graph c` is NOT derivable from `rho_df_frag_graph
  //      g`: finding F-1 of RhoDFClosure has a two-triple witness.)
  CP.rho_df_frag_graph c /\
  OS.ig_wf_sp (IX.build_indexed c) /\
  // --- finding F-2: row 9 (rdfs9/subClassOf) needs IRI subjects ---
  RC.rho_df_subclass_subjects_iri c /\
  // --- the two explicit dedup/length hypotheses FixedPoint takes ---
  FP.no_dup_keys (RC.rho_df_closure_step_pre_dedup c) /\
  no_repeats_p c /\
  no_repeats_p (RC.rho_df_closure_step c) /\
  // --- the fuel witness: the length test has actually saturated ---
  G.graph_len (RC.rho_df_closure_step c) = G.graph_len c

/// The machine check that the bundle is SUFFICIENT (no weakening).
let lemma_decides_hyps_suffices (g e : rdf_graph) (fuel : nat)
  : Lemma (requires rho_df_decides_hyps g fuel /\ SS.graph_tt_free e)
          (ensures  (let c = RC.rho_df_closure g fuel in
                     CP.rho_df_entails g e <==> SS.simple_entailment_spec c e)) =
  RC.rho_df_closure_decides g e fuel

(** ====================================================================== **)
(** Part 6: THE COMPOSED REGIME THEOREM                                    **)
(** ====================================================================== **)

/// THE SOUNDNESS HALF. Every hypothesis, with provenance:
///
///   memP mu (eval_bgp q c)   -- the fact being interpreted; this is
///                               the shipping evaluator's own output
///                               at the closure graph.
///   BR.bgp_frag q            -- LAYER 2. Fragment-scoped BGP:
///                               triple-term-free positions, exact
///                               literal constants, and NOT the
///                               fulltext escape hatch (finding BR-1,
///                               which is not BGP matching at all).
///   BR.graph_frag c          -- LAYER 2. Every object term of the
///                               CLOSURE is exact and triple-term
///                               free. Stated at `c`, not at `g`,
///                               because that is the graph the
///                               evaluator runs on.
///   rho_df_decides_hyps      -- DECIDES. The nine clauses of part 5,
///                               verbatim from `rho_df_closure_
///                               decides`, no silent strengthening.
///
/// NOT required, deliberately (finding RT-1): no groundness condition
/// on `mu`, on `q`, or on `instantiate_bgp q mu`. The soundness route
/// uses only the unconditional half of the ground collapse.
val theorem_rdfs_regime_bgp_sound
      (g : rdf_graph) (q : bgp) (mu : solution_mapping) (fuel : nat)
  : Lemma
    (requires (let c = RC.rho_df_closure g fuel in
               memP mu (eval_bgp q c) /\
               BR.bgp_frag q /\ BR.graph_frag c /\
               rho_df_decides_hyps g fuel))
    (ensures  CP.rho_df_entails g (instantiate_bgp q mu))

let theorem_rdfs_regime_bgp_sound g q mu fuel =
  let c = RC.rho_df_closure g fuel in
  let e = instantiate_bgp q mu in
  // LAYER 2: mu(q) is a subgraph of the closure.
  BR.theorem_eval_bgp_instantiates_into_graph q c mu;
  assert (SS.is_subgraph e c);
  // RDF 1.2 quarantine, discharged rather than carried (part 4).
  lemma_graph_frag_tt_free c;
  lemma_tt_free_subset e c;
  // GROUND COLLAPSE, unconditional half (part 3).
  lemma_subgraph_implies_spec c e;
  // DECIDES, right-to-left.
  lemma_decides_hyps_suffices g e fuel

/// The named gap. Finding BR-4 of SPARQL11.Algebra.BGPRefinement:
/// `ig_search` narrows to ONE of six index buckets and completeness is
/// proved for the predicate bucket only. This predicate says exactly
/// what layer 2 would have to deliver, at the one graph layer 3 needs
/// it at, and nothing more. It is a HYPOTHESIS, never an `assume`.
let eval_bgp_complete_at (q : bgp) (h : rdf_graph) (mu : solution_mapping) : prop =
  SS.is_subgraph (instantiate_bgp q mu) h ==> memP mu (eval_bgp q h)

/// THE COMPLETENESS HALF, conditional. Hypotheses and provenance:
///
///   CP.rho_df_entails g (instantiate_bgp q mu)
///                            -- the regime-side fact.
///   graph_ground (instantiate_bgp q mu)
///                            -- NEW (this module, part 1). The
///                               scoping decision; discharge it with
///                               `lemma_instantiate_bgp_ground` from
///                               the decidable `bgp_ground_positions q /\
///                               smap_ground mu`.
///   rho_df_decides_hyps g fuel
///                            -- DECIDES, part 5.
///   eval_bgp_complete_at q c mu
///                            -- THE NAMED GAP (finding BR-4). Not
///                               proved anywhere in the tree today.
///
/// `graph_tt_free` is NOT a hypothesis: groundness subsumes it
/// (finding RT-3, `lemma_ground_implies_tt_free`).
val theorem_rdfs_regime_bgp_complete_conditional
      (g : rdf_graph) (q : bgp) (mu : solution_mapping) (fuel : nat)
  : Lemma
    (requires (let c = RC.rho_df_closure g fuel in
               CP.rho_df_entails g (instantiate_bgp q mu) /\
               graph_ground (instantiate_bgp q mu) /\
               rho_df_decides_hyps g fuel /\
               eval_bgp_complete_at q c mu))
    (ensures  memP mu (eval_bgp q (RC.rho_df_closure g fuel)))

let theorem_rdfs_regime_bgp_complete_conditional g q mu fuel =
  let c = RC.rho_df_closure g fuel in
  let e = instantiate_bgp q mu in
  lemma_ground_implies_tt_free e;
  // DECIDES, left-to-right.
  lemma_decides_hyps_suffices g e fuel;
  assert (SS.simple_entailment_spec c e);
  // GROUND COLLAPSE, the half that needs groundness (part 3).
  lemma_spec_ground_implies_subgraph c e

/// THE IFF, under the named gap. This is M3's target shape: the
/// evaluator's solution set over the rho-df closure IS the RDFS
/// regime's answer set, on the fragment, for ground answers.
val theorem_rdfs_regime_bgp_exact
      (g : rdf_graph) (q : bgp) (mu : solution_mapping) (fuel : nat)
  : Lemma
    (requires (let c = RC.rho_df_closure g fuel in
               BR.bgp_frag q /\ BR.graph_frag c /\
               graph_ground (instantiate_bgp q mu) /\
               rho_df_decides_hyps g fuel /\
               eval_bgp_complete_at q c mu))
    (ensures  (let c = RC.rho_df_closure g fuel in
               memP mu (eval_bgp q c) <==>
               CP.rho_df_entails g (instantiate_bgp q mu)))

let theorem_rdfs_regime_bgp_exact g q mu fuel =
  FStar.Classical.move_requires
    (theorem_rdfs_regime_bgp_sound g q mu) fuel;
  FStar.Classical.move_requires
    (theorem_rdfs_regime_bgp_complete_conditional g q mu) fuel

(** ====================================================================== **)
(** Part 7: THE ASK COROLLARY                                              **)
(**                                                                        **)
(** SPARQL 1.1 Entailment Regimes section 2: "an entailment regime         **)
(** specifies ... how a basic graph pattern BGP is matched", and nothing   **)
(** above BGP matching changes. So ASK over a fragment BGP is the          **)
(** non-emptiness of the very solution sequence part 6 characterises --    **)
(** no new entailment content, and the existing algebra refinement is      **)
(** INHERITED rather than reproved, which is what the design doc's layer   **)
(** 3 asks for.                                                            **)
(** ====================================================================== **)

/// ASK at the BGP level. Finding RT-2 records why this is not spelled
/// `eval_ask_query`: that entry point builds a SELECTIVE index, which
/// layer 2's probe-soundness lemma does not cover.
let ask_bgp (q : bgp) (h : rdf_graph) : bool = Cons? (eval_bgp q h)

/// The machine-checked record of finding RT-2: the shipping pattern
/// evaluator on a bare BGP is `eval_bgp_store` at the SELECTIVE store,
/// not `eval_bgp` (which is `eval_bgp_store` at `graph_to_store`).
/// Comparing the two is a separate index lemma, not layer-3 content.
let lemma_eval_pattern_bgp_is_selective_store
      (base : option wf_iri) (q : bgp) (h : rdf_graph) (ds : rdf_dataset)
  : Lemma (eval_pattern base (GP_BGP q) h ds ==
           eval_bgp_store q (graph_to_store_for (GP_BGP q) h)) = ()

let lemma_ask_bgp_gives_solution (q : bgp) (h : rdf_graph)
  : Lemma (requires ask_bgp q h == true)
          (ensures  (exists (mu : solution_mapping). memP mu (eval_bgp q h))) =
  match eval_bgp q h with
  | hd :: _ ->
    introduce exists (mu : solution_mapping). memP mu (eval_bgp q h)
    with hd and ()

/// ASK SOUNDNESS under the RDFS regime: if the engine answers `true`
/// on the closure, the regime licenses that answer -- there really is
/// a solution mapping whose instantiated BGP the original graph
/// rho-df-entails.
val theorem_rdfs_regime_ask_sound (g : rdf_graph) (q : bgp) (fuel : nat)
  : Lemma
    (requires (let c = RC.rho_df_closure g fuel in
               ask_bgp q c == true /\
               BR.bgp_frag q /\ BR.graph_frag c /\
               rho_df_decides_hyps g fuel))
    (ensures  (exists (mu : solution_mapping).
                 CP.rho_df_entails g (instantiate_bgp q mu)))

let theorem_rdfs_regime_ask_sound g q fuel =
  let c = RC.rho_df_closure g fuel in
  lemma_ask_bgp_gives_solution q c;
  eliminate exists (mu : solution_mapping). memP mu (eval_bgp q c)
  returns (exists (mu2 : solution_mapping). CP.rho_df_entails g (instantiate_bgp q mu2))
  with _ . begin
    theorem_rdfs_regime_bgp_sound g q mu fuel;
    introduce exists (mu2 : solution_mapping). CP.rho_df_entails g (instantiate_bgp q mu2)
    with mu and ()
  end

/// ASK COMPLETENESS, conditional -- the mirror image, carrying the
/// same named gap and the same scoping decision as part 6.
val theorem_rdfs_regime_ask_complete_conditional
      (g : rdf_graph) (q : bgp) (mu : solution_mapping) (fuel : nat)
  : Lemma
    (requires (let c = RC.rho_df_closure g fuel in
               CP.rho_df_entails g (instantiate_bgp q mu) /\
               graph_ground (instantiate_bgp q mu) /\
               rho_df_decides_hyps g fuel /\
               eval_bgp_complete_at q c mu))
    (ensures  ask_bgp q (RC.rho_df_closure g fuel) == true)

let theorem_rdfs_regime_ask_complete_conditional g q mu fuel =
  let c = RC.rho_df_closure g fuel in
  theorem_rdfs_regime_bgp_complete_conditional g q mu fuel;
  assert (memP mu (eval_bgp q c));
  match eval_bgp q c with
  | _ :: _ -> ()

(** ====================================================================== **)
(** Part 8: THE SHIPPING ASK ENTRY POINT (finding RT-2, RESOLVED)          **)
(**                                                                        **)
(** Part 7 states ASK soundness at `ask_bgp`, which computes over          **)
(** `eval_bgp` -- the FULL-index store (`graph_to_store`). Finding RT-2    **)
(** is that `eval_ask_query` does not go through `eval_bgp`: it calls      **)
(** `eval_pattern`, which builds its store with `graph_to_store_for` --    **)
(** `build_indexed_selective`, a store some of whose six buckets are left  **)
(** unbuilt. `SPARQL11.Algebra.BGPRefinement.fst` parts 2b/8 now prove the **)
(** selective-index probe sound and generalise the whole BGP fan-out       **)
(** induction to any store carrying that soundness property                **)
(** (`BR.theorem_eval_bgp_store_for_instantiates_into_graph`). This part   **)
(** composes that with layer 3's own bridge (parts 3-5, UNCHANGED) to      **)
(** restate every theorem of part 7 at the SHIPPING entry points --        **)
(** `eval_pattern` first (`ask_pattern`), then `eval_ask_query` itself --  **)
(** under the syntactic shape the shipping ASK path for a bare BGP has     **)
(** (no FROM/FROM NAMED, no post-query VALUES: `apply_query_dataset` and   **)
(** the VALUES join are dataset-selection and join bookkeeping, not BGP    **)
(** matching, and are out of scope for both this part and part 7's         **)
(** `ask_bgp` proxy). RT-2's finding is a store-selection gap, not an      **)
(** entailment one, so nothing in parts 3-5 changes.                      **)
(** ====================================================================== **)

/// The `eval_pattern`-level ASK predicate: non-emptiness of the SAME
/// function `eval_ask_query` calls, at the SELECTIVE store finding RT-2
/// names (via `lemma_eval_pattern_bgp_is_selective_store` above).
let ask_pattern (base : option wf_iri) (q : bgp) (h : rdf_graph) (ds : rdf_dataset) : bool =
  Cons? (eval_pattern base (GP_BGP q) h ds)

let lemma_ask_pattern_gives_solution
      (base : option wf_iri) (q : bgp) (h : rdf_graph) (ds : rdf_dataset)
  : Lemma (requires ask_pattern base q h ds == true)
          (ensures  (exists (mu : solution_mapping).
                       memP mu (eval_bgp_store q (graph_to_store_for (GP_BGP q) h)))) =
  lemma_eval_pattern_bgp_is_selective_store base q h ds;
  match eval_pattern base (GP_BGP q) h ds with
  | hd :: _ ->
    introduce exists (mu : solution_mapping).
        memP mu (eval_bgp_store q (graph_to_store_for (GP_BGP q) h))
    with hd and ()

/// THE SOUNDNESS HALF, at the SELECTIVE store -- the exact analogue of
/// `theorem_rdfs_regime_bgp_sound` (part 6), with `BR.theorem_eval_bgp_
/// instantiates_into_graph` replaced by `BR.theorem_eval_bgp_store_for_
/// instantiates_into_graph`. Nothing else in the bridge (parts 3-5)
/// changes: RT-2 is a store-selection finding, not an entailment one.
val theorem_rdfs_regime_bgp_sound_selective
      (g : rdf_graph) (q : bgp) (mu : solution_mapping) (fuel : nat)
  : Lemma
    (requires (let c = RC.rho_df_closure g fuel in
               memP mu (eval_bgp_store q (graph_to_store_for (GP_BGP q) c)) /\
               BR.bgp_frag q /\ BR.graph_frag c /\
               rho_df_decides_hyps g fuel))
    (ensures  CP.rho_df_entails g (instantiate_bgp q mu))

let theorem_rdfs_regime_bgp_sound_selective g q mu fuel =
  let c = RC.rho_df_closure g fuel in
  let e = instantiate_bgp q mu in
  BR.theorem_eval_bgp_store_for_instantiates_into_graph (GP_BGP q) q c mu;
  assert (SS.is_subgraph e c);
  lemma_graph_frag_tt_free c;
  lemma_tt_free_subset e c;
  lemma_subgraph_implies_spec c e;
  lemma_decides_hyps_suffices g e fuel

/// ASK SOUNDNESS at `eval_pattern` -- the shipping store, one layer
/// below `eval_ask_query`.
val theorem_rdfs_regime_ask_pattern_sound
      (g : rdf_graph) (base : option wf_iri) (q : bgp) (ds : rdf_dataset) (fuel : nat)
  : Lemma
    (requires (let c = RC.rho_df_closure g fuel in
               ask_pattern base q c ds == true /\
               BR.bgp_frag q /\ BR.graph_frag c /\
               rho_df_decides_hyps g fuel))
    (ensures  (exists (mu : solution_mapping).
                 CP.rho_df_entails g (instantiate_bgp q mu)))

let theorem_rdfs_regime_ask_pattern_sound g base q ds fuel =
  let c = RC.rho_df_closure g fuel in
  lemma_ask_pattern_gives_solution base q c ds;
  eliminate exists (mu : solution_mapping).
      memP mu (eval_bgp_store q (graph_to_store_for (GP_BGP q) c))
  returns (exists (mu2 : solution_mapping). CP.rho_df_entails g (instantiate_bgp q mu2))
  with _ . begin
    theorem_rdfs_regime_bgp_sound_selective g q mu fuel;
    introduce exists (mu2 : solution_mapping). CP.rho_df_entails g (instantiate_bgp q mu2)
    with mu and ()
  end

/// The syntactic bridge from `eval_ask_query` (the record-shaped
/// SHIPPING query evaluator) down to `ask_pattern`: for the bare-BGP,
/// no-dataset-clause, no-post-VALUES ASK shape, `eval_ask_query`
/// literally computes `ask_pattern`. `apply_query_dataset [] h ds`
/// is `(h, ds)` by its own first match arm; `q.q_values == None`
/// takes `eval_ask_query`'s inner match to its `None` arm; and the
/// final `[] -> false | _ -> true` match is definitionally `Cons?`.
let lemma_eval_ask_query_bgp_shape
      (q : query) (bgp_q : bgp) (h : rdf_graph) (ds : rdf_dataset)
  : Lemma (requires q.q_form == QF_Ask /\ q.q_pattern == GP_BGP bgp_q /\
                    q.q_dataset == [] /\ q.q_values == None)
          (ensures  eval_ask_query q h ds == ask_pattern q.q_base bgp_q h ds) =
  assert (apply_query_dataset q.q_dataset h ds == (h, ds))

/// THE SHIPPING-PATH THEOREM. `eval_ask_query` is the function
/// `SPARQL11.Algebra`'s ASK query form actually calls
/// (SPARQL11.Algebra.fst:6158-6169). Finding RT-2 is closed: this
/// carries the SAME soundness statement `theorem_rdfs_regime_ask_
/// sound` (part 7) proves for the `ask_bgp` proxy, now at the literal
/// shipping entry point, for the syntactic shape a bare-BGP ASK query
/// has (no FROM/FROM NAMED, no post-query VALUES -- both are
/// dataset/join bookkeeping the algebra layer above BGP matching
/// owns, out of scope for both this theorem and part 7's `ask_bgp`
/// proxy).
val theorem_rdfs_regime_ask_query_sound
      (g : rdf_graph) (q : query) (bgp_q : bgp) (ds : rdf_dataset) (fuel : nat)
  : Lemma
    (requires (let c = RC.rho_df_closure g fuel in
               q.q_form == QF_Ask /\ q.q_pattern == GP_BGP bgp_q /\
               q.q_dataset == [] /\ q.q_values == None /\
               eval_ask_query q c ds == true /\
               BR.bgp_frag bgp_q /\ BR.graph_frag c /\
               rho_df_decides_hyps g fuel))
    (ensures  (exists (mu : solution_mapping).
                 CP.rho_df_entails g (instantiate_bgp bgp_q mu)))

let theorem_rdfs_regime_ask_query_sound g q bgp_q ds fuel =
  let c = RC.rho_df_closure g fuel in
  lemma_eval_ask_query_bgp_shape q bgp_q c ds;
  theorem_rdfs_regime_ask_pattern_sound g q.q_base bgp_q ds fuel

/// The named gap for the SELECTIVE store -- the shipping ASK entry
/// point's analogue of `eval_bgp_complete_at` (finding BR-4), at the
/// store `graph_to_store_for` actually builds. NOT proved: index
/// completeness for a store some of whose buckets were never built
/// carries at least the same open status as the full-index version
/// (BR-4 is about `ig_search`'s bucket CHOICE, which is identical at
/// both stores -- a bucket the selective store never built is simply
/// never offered as a candidate, BGPRefinement part 2b -- so nothing
/// about the selective store makes completeness EASIER; closing it is
/// not this module's job, and RT-2 itself is a soundness finding, not
/// a completeness one).
let eval_bgp_store_complete_at (q : bgp) (h : rdf_graph) (mu : solution_mapping) : prop =
  SS.is_subgraph (instantiate_bgp q mu) h ==>
  memP mu (eval_bgp_store q (graph_to_store_for (GP_BGP q) h))

/// THE COMPLETENESS HALF, conditional, at the selective store -- the
/// exact analogue of `theorem_rdfs_regime_bgp_complete_conditional`
/// (part 6), swapping `eval_bgp_complete_at` for `eval_bgp_store_
/// complete_at`. Proof body is UNCHANGED from the full-store version:
/// the ground-collapse argument never mentions which store `eval_bgp`
/// used, only that `instantiate_bgp q mu` is a subgraph of `c` -- the
/// named-gap hypothesis supplies the final membership fact by plain
/// modus ponens, as in the original.
val theorem_rdfs_regime_bgp_complete_conditional_selective
      (g : rdf_graph) (q : bgp) (mu : solution_mapping) (fuel : nat)
  : Lemma
    (requires (let c = RC.rho_df_closure g fuel in
               CP.rho_df_entails g (instantiate_bgp q mu) /\
               graph_ground (instantiate_bgp q mu) /\
               rho_df_decides_hyps g fuel /\
               eval_bgp_store_complete_at q c mu))
    (ensures  memP mu (eval_bgp_store q (graph_to_store_for (GP_BGP q) (RC.rho_df_closure g fuel))))

let theorem_rdfs_regime_bgp_complete_conditional_selective g q mu fuel =
  let c = RC.rho_df_closure g fuel in
  let e = instantiate_bgp q mu in
  lemma_ground_implies_tt_free e;
  lemma_decides_hyps_suffices g e fuel;
  assert (SS.simple_entailment_spec c e);
  lemma_spec_ground_implies_subgraph c e

/// ASK COMPLETENESS, conditional, at the literal shipping entry point.
val theorem_rdfs_regime_ask_query_complete_conditional
      (g : rdf_graph) (q : query) (bgp_q : bgp) (mu : solution_mapping) (ds : rdf_dataset) (fuel : nat)
  : Lemma
    (requires (let c = RC.rho_df_closure g fuel in
               q.q_form == QF_Ask /\ q.q_pattern == GP_BGP bgp_q /\
               q.q_dataset == [] /\ q.q_values == None /\
               CP.rho_df_entails g (instantiate_bgp bgp_q mu) /\
               graph_ground (instantiate_bgp bgp_q mu) /\
               rho_df_decides_hyps g fuel /\
               eval_bgp_store_complete_at bgp_q c mu))
    (ensures  eval_ask_query q (RC.rho_df_closure g fuel) ds == true)

let theorem_rdfs_regime_ask_query_complete_conditional g q bgp_q mu ds fuel =
  let c = RC.rho_df_closure g fuel in
  theorem_rdfs_regime_bgp_complete_conditional_selective g bgp_q mu fuel;
  assert (memP mu (eval_bgp_store bgp_q (graph_to_store_for (GP_BGP bgp_q) c)));
  lemma_eval_pattern_bgp_is_selective_store q.q_base bgp_q c ds;
  assert (Cons? (eval_pattern q.q_base (GP_BGP bgp_q) c ds));
  lemma_eval_ask_query_bgp_shape q bgp_q c ds

#pop-options
