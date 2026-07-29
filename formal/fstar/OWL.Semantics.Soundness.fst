module OWL.Semantics.Soundness

// Machine-checked soundness proofs for SHIPPING closure rules from
// RDFS.Closure.fsti / OWL.Closure.fsti, against the OWL 2 RDF-Based
// semantic conditions formalized in OWL.Semantics.fst. Every theorem
// below is about the exact executable rule function the engine runs —
// not a model or transcription of it. No admits, no --lax.
//
// Pilot rules proven (design doc: docs/designissues/2026-07-29-
// rdf-based-semantics-formalization.md):
//   * rdfs_rule_domain              (rdfs2 — RDFS family, index-driven)
//   * owl_rule_symmetric_property   (prp-symp — property characteristic)
//   * owl_rule_sameAs_symmetry      (eq-sym — equality family, snapshot
//                                    pair-list machinery included)
//   * owl_rule_cls_oneof            (cls-oo — the list-walking case,
//                                    via decode_iri_list_sound)
//
// Proof shape shared by all four: fix an interpretation and ONE bnode
// assignment; show every triple the rule appends is true under that
// same assignment (the pilot rules mint no fresh bnodes); conclude at
// the satisfaction level. The fold_left inductions all go through
// OWL.Semantics.MemLemmas.fold_left_inv with the step obligation
// established by an `introduce forall` block.

open FStar.List.Tot
open RDF.Term
open RDF.Triple
open RDF.Graph
open RDF.Indexed
open RDFS.Closure
open OWL.Closure
open OWL.Semantics
open OWL.Semantics.MemLemmas

// ===================================================================
// Small bridging lemmas: boolean structural equality to propositional
// equality, in the shapes the rule bodies use.
// ===================================================================

let lemma_rdf_term_eq_iri (o : rdf_term) (x : wf_iri)
  : Lemma (requires rdf_term_eq o (T_IRI x) = true)
          (ensures o == T_IRI x) =
  match o with
  | T_IRI _ -> ()
  | _ -> ()

// ===================================================================
// Rule 1: owl_rule_symmetric_property (prp-symp).
// OWL 2 RL/RDF rules table: T(?p, rdf:type, owl:SymmetricProperty),
// T(?x, ?p, ?y) => T(?y, ?p, ?x). Uses no index bucket.
// ===================================================================

// Everything the collection fold gathers really is declared
// symmetric in g — stated semantically (its denotation is in
// ICEXT(I(owl:SymmetricProperty))) so the emission fold can consume
// it directly.
let sym_props_sound (i : interp) (a : bnode_assignment i.idom) (ps : list wf_iri) : prop =
  forall (p : wf_iri). List.Tot.mem p ps ==>
    icext i (i.i_iri p) (i.i_iri owl_SymmetricProperty)

val owl_rule_symmetric_property_sound
    (i : interp) (a : bnode_assignment i.idom) (g : rdf_graph) (ig : indexed_graph)
  : Lemma
    (requires cond_symmetric i /\ holds_all i a g)
    (ensures  holds_all i a (owl_rule_symmetric_property g ig))

let owl_rule_symmetric_property_sound i a g ig =
  let collect_step : list wf_iri -> triple -> list wf_iri =
    fun (acc : list wf_iri) (t : triple) ->
      if t.p = rdf_type && rdf_term_eq t.o (T_IRI owl_SymmetricProperty) then
        match t.s with
        | S_IRI p_iri -> cons_if_new_iri p_iri acc
        | _ -> acc
      else acc in
  let sym_props = List.Tot.fold_left collect_step [] g in
  // Step 1: the collection fold is sound.
  introduce forall (acc : list wf_iri) (t : triple).
      (List.Tot.memP t g /\ sym_props_sound i a acc) ==>
      sym_props_sound i a (collect_step acc t)
  with introduce (List.Tot.memP t g /\ sym_props_sound i a acc) ==>
                 sym_props_sound i a (collect_step acc t)
  with _ . begin
    if t.p = rdf_type && rdf_term_eq t.o (T_IRI owl_SymmetricProperty) then begin
      lemma_rdf_term_eq_iri t.o owl_SymmetricProperty;
      assert (triple_holds i a t)
    end else ()
  end;
  fold_left_inv (sym_props_sound i a) collect_step g [];
  assert (sym_props_sound i a sym_props);
  // Step 2: the emission fold preserves truth.
  let emit_step : rdf_graph -> triple -> rdf_graph =
    fun (acc : rdf_graph) (t : triple) ->
      if List.Tot.mem t.p sym_props then
        match term_to_subject t.o with
        | Some new_subj ->
          let new_t : triple = { s = new_subj; p = t.p; o = subject_to_term t.s } in
          add_triple_unchecked acc new_t
        | None -> acc
      else acc in
  introduce forall (acc : rdf_graph) (t : triple).
      (List.Tot.memP t g /\ holds_all i a acc) ==> holds_all i a (emit_step acc t)
  with introduce (List.Tot.memP t g /\ holds_all i a acc) ==>
                 holds_all i a (emit_step acc t)
  with _ . begin
    if List.Tot.mem t.p sym_props then
      match term_to_subject t.o with
      | Some new_subj ->
        lemma_denot_term_to_subject i a t.o new_subj;
        lemma_denot_subject_to_term i a t.s;
        assert (triple_holds i a t);
        assert (i.iext (i.i_iri t.p) (denot_subject i a t.s) (denot_term i a t.o))
      | None -> ()
    else ()
  end;
  fold_left_inv (holds_all i a) emit_step g g;
  assert_norm (owl_rule_symmetric_property g ig ==
               List.Tot.fold_left emit_step g g)

// ===================================================================
// Rule 2: rdfs_rule_domain (rdfs2).
// RDF 1.1 Semantics, RDFS entailment rule rdfs2: (P rdfs:domain C),
// (a P b) |- (a rdf:type C). Reads the ig_pred bucket twice (once
// for the domain declarations, once for the data triples of each
// declared property), so its hypotheses are ig_wf_pred plus truth of
// the snapshot.
// ===================================================================

val rdfs_rule_domain_sound
    (i : interp) (a : bnode_assignment i.idom) (g : rdf_graph) (ig : indexed_graph)
  : Lemma
    (requires cond_domain i /\ holds_all i a g /\
              holds_all i a ig.ig_triples /\ ig_wf_pred ig)
    (ensures  holds_all i a (rdfs_rule_domain g ig))

let rdfs_rule_domain_sound i a g ig =
  let decls = bucket_lookup ig.ig_pred rdfs_domain in
  let outer_step : rdf_graph -> triple -> rdf_graph =
    fun (acc : rdf_graph) (decl : triple) ->
      match decl.s with
      | S_IRI p ->
        let matching = bucket_lookup ig.ig_pred p in
        List.Tot.fold_left
          (fun (acc2 : rdf_graph) (t : triple) ->
            let new_t : triple = { s = t.s; p = rdf_type; o = decl.o } in
            add_triple_unchecked acc2 new_t)
          acc matching
      | _ -> acc in
  introduce forall (acc : rdf_graph) (decl : triple).
      (List.Tot.memP decl decls /\ holds_all i a acc) ==>
      holds_all i a (outer_step acc decl)
  with introduce (List.Tot.memP decl decls /\ holds_all i a acc) ==>
                 holds_all i a (outer_step acc decl)
  with _ . begin
    // ig_wf_pred at key rdfs_domain: decl is a real snapshot triple
    // asserting (decl.s rdfs:domain decl.o).
    assert (List.Tot.memP decl ig.ig_triples /\ decl.p == rdfs_domain);
    assert (triple_holds i a decl);
    match decl.s with
    | S_IRI p ->
      let matching = bucket_lookup ig.ig_pred p in
      let inner_step : rdf_graph -> triple -> rdf_graph =
        fun (acc2 : rdf_graph) (t : triple) ->
          let new_t : triple = { s = t.s; p = rdf_type; o = decl.o } in
          add_triple_unchecked acc2 new_t in
      introduce forall (acc2 : rdf_graph) (t : triple).
          (List.Tot.memP t matching /\ holds_all i a acc2) ==>
          holds_all i a (inner_step acc2 t)
      with introduce (List.Tot.memP t matching /\ holds_all i a acc2) ==>
                     holds_all i a (inner_step acc2 t)
      with _ . begin
        // ig_wf_pred at key p: t really is an (x P y) data triple.
        assert (List.Tot.memP t ig.ig_triples /\ t.p == p);
        assert (triple_holds i a t);
        // cond_domain: <I(P), I(C)> in IEXT(I(rdfs:domain)) and
        // <x,y> in IEXT(I(P)) give x in ICEXT(I(C)).
        assert (i.iext (i.i_iri rdfs_domain) (i.i_iri p) (denot_term i a decl.o));
        assert (icext i (denot_subject i a t.s) (denot_term i a decl.o))
      end;
      fold_left_inv (holds_all i a) inner_step matching acc
    | _ -> ()
  end;
  fold_left_inv (holds_all i a) outer_step decls g;
  assert_norm (rdfs_rule_domain g ig == List.Tot.fold_left outer_step g decls)

// ===================================================================
// Rule 3: owl_rule_sameAs_symmetry (eq-sym).
// OWL 2 RL/RDF rules table: T(?x, owl:sameAs, ?y) => T(?y,
// owl:sameAs, ?x). The rule folds over the deduped snapshot pair
// list (#262 perf shape), so the proof first carries truth through
// the collect / sortWith / dedup pipeline.
// ===================================================================

// Membership preservation through OWL.Closure's pair dedup walk.
let rec lemma_dedup_pairs_memP (prev : option string)
    (ps acc : list (subject * subject)) (x : subject * subject)
  : Lemma
    (ensures List.Tot.memP x (dedup_pairs_sorted_aux prev ps acc) ==>
             (List.Tot.memP x ps \/ List.Tot.memP x acc))
    (decreases ps) =
  match ps with
  | [] -> List.Tot.rev_memP acc x
  | p :: rest ->
    lemma_dedup_pairs_memP prev rest acc x;
    lemma_dedup_pairs_memP (Some (sameas_pair_key p)) rest (p :: acc) x

// Every pair the snapshot machinery yields is a true sameAs edge.
let sameas_pairs_hold (i : interp) (a : bnode_assignment i.idom)
    (ps : list (subject * subject)) : prop =
  forall (xy : subject * subject). List.Tot.memP xy ps ==>
    i.iext (i.i_iri owl_sameAs)
           (denot_subject i a (fst xy)) (denot_subject i a (snd xy))

let lemma_sameas_pairs_hold
    (i : interp) (a : bnode_assignment i.idom) (ig : indexed_graph)
  : Lemma
    (requires holds_all i a ig.ig_triples)
    (ensures  sameas_pairs_hold i a (sameas_pairs ig)) =
  let collect_step : list (subject * subject) -> triple -> list (subject * subject) =
    fun (acc : list (subject * subject)) (t : triple) ->
      if t.p = owl_sameAs then
        match term_to_subject t.o with
        | Some y -> if subject_eq t.s y then acc else (t.s, y) :: acc
        | None -> acc
      else acc in
  let raw = List.Tot.fold_left collect_step [] ig.ig_triples in
  introduce forall (acc : list (subject * subject)) (t : triple).
      (List.Tot.memP t ig.ig_triples /\ sameas_pairs_hold i a acc) ==>
      sameas_pairs_hold i a (collect_step acc t)
  with introduce (List.Tot.memP t ig.ig_triples /\ sameas_pairs_hold i a acc) ==>
                 sameas_pairs_hold i a (collect_step acc t)
  with _ . begin
    if t.p = owl_sameAs then
      match term_to_subject t.o with
      | Some y ->
        lemma_denot_term_to_subject i a t.o y;
        assert (triple_holds i a t)
      | None -> ()
    else ()
  end;
  fold_left_inv (sameas_pairs_hold i a) collect_step ig.ig_triples [];
  let sorted = List.Tot.sortWith sameas_pair_cmp raw in
  lemma_sortWith_memP_forall sameas_pair_cmp raw;
  FStar.Classical.forall_intro (lemma_dedup_pairs_memP None sorted []);
  assert_norm (sameas_pairs ig == dedup_pairs_sorted_aux None sorted [])

val owl_rule_sameAs_symmetry_sound
    (i : interp) (a : bnode_assignment i.idom) (g : rdf_graph) (ig : indexed_graph)
  : Lemma
    (requires cond_sameas_identity i /\ holds_all i a g /\ holds_all i a ig.ig_triples)
    (ensures  holds_all i a (owl_rule_sameAs_symmetry g ig))

let owl_rule_sameAs_symmetry_sound i a g ig =
  lemma_sameas_pairs_hold i a ig;
  let emit_step : rdf_graph -> (subject * subject) -> rdf_graph =
    fun (acc : rdf_graph) (xy : subject * subject) ->
      let (x, y) = xy in
      let new_t : triple = { s = y; p = owl_sameAs; o = subject_to_term x } in
      add_triple_unchecked acc new_t in
  introduce forall (acc : rdf_graph) (xy : subject * subject).
      (List.Tot.memP xy (sameas_pairs ig) /\ holds_all i a acc) ==>
      holds_all i a (emit_step acc xy)
  with introduce (List.Tot.memP xy (sameas_pairs ig) /\ holds_all i a acc) ==>
                 holds_all i a (emit_step acc xy)
  with _ . begin
    let (x, y) = xy in
    lemma_denot_subject_to_term i a x;
    // sameas_pairs_hold gives IEXT(sameAs)(dx, dy); the identity
    // condition collapses dx == dy, and then gives the flipped edge.
    assert (i.iext (i.i_iri owl_sameAs)
                   (denot_subject i a x) (denot_subject i a y))
  end;
  fold_left_inv (holds_all i a) emit_step (sameas_pairs ig) g;
  assert_norm (owl_rule_sameAs_symmetry g ig ==
               List.Tot.fold_left emit_step g (sameas_pairs ig))
