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
