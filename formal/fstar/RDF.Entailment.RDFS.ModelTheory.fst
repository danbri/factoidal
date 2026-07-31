module RDF.Entailment.RDFS.ModelTheory

// ===================================================================
// THE MODEL THEORY of the RDF and RDFS rungs, and the soundness of
// the shipping closure against it.
//
// RDF.Entailment.RDFS.Spec.fst transcribes the W3C RULE TABLES;
// RDF.Entailment.RDFS.Refinement.fst proves the shipping rules emit
// only triples those tables license. Neither says why the tables are
// correct. This module supplies that half:
//
//   1. the RDF and RDFS INTERPRETATION CONDITIONS (RDF 1.1 Semantics
//      sections 8 and 9), one `cond_*` per table row, each the weakest
//      reading the row implies -- the method the OWL 2 RDF-Based pilot
//      established (docs/designissues/2026-07-29-rdf-based-semantics-
//      formalization.md, "Choosing the condition strength");
//   2. `rdf_entails` / `rdfs_entails`, instances of
//      `OWL.Semantics.entails_under`;
//   3. SOUNDNESS OF EVERY RULE ROW: `rdfs_licensed_true` -- if a
//      triple is licensed by the rule tables from a true graph, it is
//      true. Nothing about the engine appears in that theorem;
//   4. composed with the Refinement module: soundness of the SHIPPING
//      `rdfs_closure_step` and `rdfs_closure`, i.e.
//      `rdfs_entails g (rdfs_closure g fuel)`.
//
// -------------------------------------------------------------------
// REUSE, not re-derivation
// -------------------------------------------------------------------
// `interp` / `denot_*` / `holds_all` / `satisfies` / `entails_under` /
// `icext` / `cond_domain` / `cond_range` are `OWL.Semantics`', from
// the 2026-07-29 pilot. `cond_domain` and `cond_range` were already
// there and already carried a W3C-refinement theorem for rdfs2
// (`OWL.Semantics.Soundness.rdfs_rule_domain_sound`); this module adds
// the rest of the RDFS condition table around them rather than
// starting a second one. Same superset-of-the-genuine-class caveat as
// the pilot: dropping conditions and totalizing partial maps ENLARGES
// the interpretation class, which strengthens every soundness result
// here and weakens any completeness result -- see "What is not
// proved" at the bottom.
//
// -------------------------------------------------------------------
// RDF 1.2 QUARANTINE
// -------------------------------------------------------------------
// As at the simple rung: `T_TripleTerm` has no denotation in either
// baseline, `OWL.Semantics.interp` gives it an uninterpreted
// compositional constructor, and the soundness results below hold for
// ALL graphs because they only ever need `i_tt` to be a function of
// the component denotations. The `graph_tt_free` hypothesis of
// RDF.Entailment.Simple.Spec is needed only where a countermodel has
// to be CONSTRUCTED, i.e. in the completeness direction.
// ===================================================================

open FStar.List.Tot
open RDF.Term
open RDF.Triple
open RDF.Graph
open RDF.Indexed
open RDFS.Closure
open OWL.Semantics
open OWL.Semantics.MemLemmas
open RDF.Vocabulary.Axioms
open RDF.Entailment.Simple.Spec
open RDF.Entailment.RDF.Spec
open RDF.Entailment.RDFS.Spec
open RDF.Entailment.RDFS.Refinement

// ===================================================================
// 0. Plumbing.
// ===================================================================

// `subj_term` (Spec) and `subject_to_term` (RDF.Graph, which
// OWL.Semantics' denotation lemmas are stated over) are the same
// function. Same nine-line bridge the simple-entailment vertical
// needed; kept local rather than shared, so neither Spec module has to
// open RDF.Graph.
let lemma_subj_term_denot (i : interp) (a : bnode_assignment i.idom) (s : subject)
  : Lemma (denot_term i a (subj_term s) == denot_subject i a s) =
  match s with
  | S_IRI _ -> ()
  | S_BNode _ -> ()

// ===================================================================
// 1. RDF INTERPRETATION CONDITIONS.
// RDF 1.1 Semantics section 8 ("RDF Interpretations"), semantic
// conditions table.
// ===================================================================

// "x is in IP if and only if <x, I(rdf:Property)> is in
//  IEXT(I(rdf:type))."
//
// `OWL.Semantics.interp` has no IP field -- IEXT is totalized over the
// domain (the pilot's enlarging simplification). The reading that
// survives that totalization, and the one rdfD2 needs, is the ONLY-IF
// half read through "IP is the set of things IEXT is defined on":
// anything that relates a pair is a property.
let cond_rdf_property (i : interp) : prop =
  forall (p x y : i.idom). i.iext p x y ==> icext i p (i.i_iri rdf_Property)

// "... and the RDF axiomatic triples must be satisfied."
// Every axiomatic triple is ground, so it holds under every
// assignment; the quantifier over assignments costs nothing and makes
// the condition directly usable at any point of a proof.
let cond_rdf_axioms (i : interp) : prop =
  forall (a : bnode_assignment i.idom) (t : triple).
    rdf_axiomatic t ==> triple_holds i a t

let rdf_conditions (i : interp) : prop = cond_rdf_property i /\ cond_rdf_axioms i

// RDF entailment: RDF 1.1 Semantics section 8. "S RDF entails E when
// every RDF interpretation satisfying S also satisfies E."
let rdf_entails (g1 g2 : rdf_graph) : prop = entails_under rdf_conditions g1 g2

// ===================================================================
// 2. RDFS INTERPRETATION CONDITIONS.
// RDF 1.1 Semantics section 9 ("RDFS Interpretations"), semantic
// conditions table. One condition per row, in the row's own order,
// each quoted at its definition.
// ===================================================================

// "If aaa is in D then I(aaa) is in ICEXT(I(rdfs:Datatype))."
// (The condition rdfs1 rests on.)
let cond_datatypes (dd : datatype_set) (i : interp) : prop =
  forall (a : wf_iri). dd a ==> icext i (i.i_iri a) (i.i_iri rdfs_Datatype)

// "ICEXT(I(rdfs:Resource)) = IR."  (rdfs4a / rdfs4b.)
let cond_resource (i : interp) : prop =
  forall (x : i.idom). icext i x (i.i_iri rdfs_Resource)

// "If <x,y> is in IEXT(I(rdfs:subPropertyOf)) then x and y are in IP
//  and IEXT(x) is a subset of IEXT(y)."  (rdfs7; the IP conjunct is
//  dropped, per the enlarging convention.)
let cond_subPropertyOf (i : interp) : prop =
  forall (x y u v : i.idom).
    i.iext (i.i_iri rdfs_subPropertyOf) x y ==> i.iext x u v ==> i.iext y u v

// "IEXT(I(rdfs:subPropertyOf)) is transitive and reflexive on IP."
// Split into its two halves, because rdfs5 needs only transitivity and
// rdfs6 needs only reflexivity, and the reflexive half is stated with
// ICEXT(I(rdf:Property)) in place of IP -- which is exactly what the
// RDF-rung condition `cond_rdf_property` identifies IP with.
let cond_subPropertyOf_trans (i : interp) : prop =
  forall (x y z : i.idom).
    i.iext (i.i_iri rdfs_subPropertyOf) x y ==>
    i.iext (i.i_iri rdfs_subPropertyOf) y z ==>
    i.iext (i.i_iri rdfs_subPropertyOf) x z

let cond_subPropertyOf_refl (i : interp) : prop =
  forall (x : i.idom).
    icext i x (i.i_iri rdf_Property) ==> i.iext (i.i_iri rdfs_subPropertyOf) x x

// "If <x,y> is in IEXT(I(rdfs:subClassOf)) then x and y are in IC and
//  ICEXT(x) is a subset of ICEXT(y)."  (rdfs9.)
let cond_subClassOf (i : interp) : prop =
  forall (x y u : i.idom).
    i.iext (i.i_iri rdfs_subClassOf) x y ==> icext i u x ==> icext i u y

// "IEXT(I(rdfs:subClassOf)) is transitive and reflexive on IC."
// (rdfs11 / rdfs10; IC = ICEXT(I(rdfs:Class)) by the section's own
// definition, which is how the reflexive half is spelled.)
let cond_subClassOf_trans (i : interp) : prop =
  forall (x y z : i.idom).
    i.iext (i.i_iri rdfs_subClassOf) x y ==>
    i.iext (i.i_iri rdfs_subClassOf) y z ==>
    i.iext (i.i_iri rdfs_subClassOf) x z

let cond_subClassOf_refl (i : interp) : prop =
  forall (x : i.idom).
    icext i x (i.i_iri rdfs_Class) ==> i.iext (i.i_iri rdfs_subClassOf) x x

// "If x is in IC then <x, I(rdfs:Resource)> is in
//  IEXT(I(rdfs:subClassOf))."  (rdfs8.)
let cond_class_subclass_resource (i : interp) : prop =
  forall (x : i.idom).
    icext i x (i.i_iri rdfs_Class) ==>
    i.iext (i.i_iri rdfs_subClassOf) x (i.i_iri rdfs_Resource)

// "If x is in ICEXT(I(rdfs:Datatype)) then <x, I(rdfs:Literal)> is in
//  IEXT(I(rdfs:subClassOf))."  (rdfs13.)
let cond_datatype_subclass_literal (i : interp) : prop =
  forall (x : i.idom).
    icext i x (i.i_iri rdfs_Datatype) ==>
    i.iext (i.i_iri rdfs_subClassOf) x (i.i_iri rdfs_Literal)

// "If x is in ICEXT(I(rdfs:ContainerMembershipProperty)) then
//  <x, I(rdfs:member)> is in IEXT(I(rdfs:subPropertyOf))."  (rdfs12.)
let cond_cmp_member (i : interp) : prop =
  forall (x : i.idom).
    icext i x (i.i_iri rdfs_ContainerMembershipProperty) ==>
    i.iext (i.i_iri rdfs_subPropertyOf) x (i.i_iri rdfs_member)

// "If <x,y> is in IEXT(I(rdfs:subClassOf)) then x and y are in IC and
//  ICEXT(x) is a subset of ICEXT(y)."  -- the IC HALF, which
// `cond_subClassOf` above drops per the enlarging convention. It is
// restored here (as its own condition, so `cond_subClassOf` keeps the
// exact strength rdfs9 needs) because the shipping
// `rdfs_reflexivity_axioms` harvest reads subClassOf ENDPOINTS, and the
// IC half plus reflexivity on IC is what licenses that. IC is
// ICEXT(I(rdfs:Class)) by section 9's own definition.
//
// Adding a condition SHRINKS the interpretation class, so every
// soundness theorem below stays true; the class is still a superset of
// the genuine RDFS interpretations, which satisfy this condition by
// definition.
let cond_subClassOf_ic (i : interp) : prop =
  forall (x y : i.idom).
    i.iext (i.i_iri rdfs_subClassOf) x y ==>
    icext i x (i.i_iri rdfs_Class) /\ icext i y (i.i_iri rdfs_Class)

// "If <x,y> is in IEXT(I(rdfs:subPropertyOf)) then x and y are in IP
//  and IEXT(x) is a subset of IEXT(y)."  -- the IP half, dual to the
// above. IP is identified with ICEXT(I(rdf:Property)) exactly as
// `cond_rdf_property` / `cond_subPropertyOf_refl` already do.
let cond_subPropertyOf_ip (i : interp) : prop =
  forall (x y : i.idom).
    i.iext (i.i_iri rdfs_subPropertyOf) x y ==>
    icext i x (i.i_iri rdf_Property) /\ icext i y (i.i_iri rdf_Property)

// RDF 1.1 Semantics section 8: "RDF interpretations ... recognize the
// datatype IRIs rdf:langString and xsd:string", i.e. `d_minimal` is a
// subset of EVERY recognized-datatype set D. Stated as its own
// condition so that a theorem parameterised by an arbitrary D still has
// the two guaranteed datatypes available -- which is what the shipping
// rdfs1 rule emits.
let cond_datatypes_minimal (i : interp) : prop = cond_datatypes d_minimal i

// "... and the RDFS axiomatic triples must be satisfied."
let cond_rdfs_axioms (i : interp) : prop =
  forall (a : bnode_assignment i.idom) (t : triple).
    rdfs_axiomatic t ==> triple_holds i a t

// The RDFS condition bundle, parameterised by the recognized-datatype
// set D exactly as the W3C text is ("RDFS entailment recognizing D").
let rdfs_conditions (dd : datatype_set) (i : interp) : prop =
  rdf_conditions i /\
  cond_domain i /\ cond_range i /\
  cond_datatypes dd i /\ cond_datatypes_minimal i /\ cond_resource i /\
  cond_subPropertyOf i /\ cond_subPropertyOf_trans i /\ cond_subPropertyOf_refl i /\
  cond_subPropertyOf_ip i /\
  cond_subClassOf i /\ cond_subClassOf_trans i /\ cond_subClassOf_refl i /\
  cond_subClassOf_ic i /\
  cond_class_subclass_resource i /\ cond_datatype_subclass_literal i /\
  cond_cmp_member i /\ cond_rdfs_axioms i

// RDFS entailment: RDF 1.1 Semantics section 9.
let rdfs_entails (dd : datatype_set) (g1 g2 : rdf_graph) : prop =
  entails_under (rdfs_conditions dd) g1 g2

// ===================================================================
// 3. SOUNDNESS OF THE RULE TABLE.
//
// One lemma per row of RDF.Entailment.RDFS.Spec's transcription. Each
// is the row's semantic justification and mentions no engine function.
// ===================================================================

let rdfD2_true (i : interp) (a : bnode_assignment i.idom) (g : rdf_graph) (t : triple)
  : Lemma (requires cond_rdf_property i /\ holds_all i a g /\ rdfD2_derives g t)
          (ensures triple_holds i a t) =
  lemma_vocab_agree ();
  eliminate exists (u : triple). memP u g /\ t == rdfD2_conclusion u
  returns triple_holds i a t
  with _ . assert (triple_holds i a u)

let rdfs1_true (dd : datatype_set) (i : interp) (a : bnode_assignment i.idom) (t : triple)
  : Lemma (requires cond_datatypes dd i /\ rdfs1_derives dd t)
          (ensures triple_holds i a t) = lemma_vocab_agree ()

let rdfs2_true (i : interp) (a : bnode_assignment i.idom) (g : rdf_graph) (t : triple)
  : Lemma (requires cond_domain i /\ holds_all i a g /\ rdfs2_derives g t)
          (ensures triple_holds i a t) =
  lemma_vocab_agree ();
  eliminate exists (decl u : triple) (aa : wf_iri).
      memP decl g /\ decl.p == i_rdfs_domain /\ decl.s == S_IRI aa /\
      memP u g /\ u.p == aa /\
      t == ({ s = u.s; p = i_rdf_type; o = decl.o } <: triple)
  returns triple_holds i a t
  with _ . begin
    assert (triple_holds i a decl);
    assert (triple_holds i a u);
    assert (i.iext (i.i_iri rdfs_domain) (i.i_iri aa) (denot_term i a decl.o));
    assert (i.iext (i.i_iri aa) (denot_subject i a u.s) (denot_term i a u.o));
    assert (icext i (denot_subject i a u.s) (denot_term i a decl.o))
  end

let rdfs3_true (i : interp) (a : bnode_assignment i.idom) (g : rdf_graph) (t : triple)
  : Lemma (requires cond_range i /\ holds_all i a g /\ rdfs3_derives g t)
          (ensures triple_holds i a t) =
  lemma_vocab_agree ();
  eliminate exists (decl u : triple) (aa : wf_iri) (zs : subject).
      memP decl g /\ decl.p == i_rdfs_range /\ decl.s == S_IRI aa /\
      memP u g /\ u.p == aa /\ subj_term zs == u.o /\
      t == ({ s = zs; p = i_rdf_type; o = decl.o } <: triple)
  returns triple_holds i a t
  with _ . begin
    assert (triple_holds i a decl);
    assert (triple_holds i a u);
    lemma_subj_term_denot i a zs;
    assert (i.iext (i.i_iri rdfs_range) (i.i_iri aa) (denot_term i a decl.o));
    assert (i.iext (i.i_iri aa) (denot_subject i a u.s) (denot_term i a u.o));
    assert (icext i (denot_term i a u.o) (denot_term i a decl.o))
  end

let rdfs4a_true (i : interp) (a : bnode_assignment i.idom) (g : rdf_graph) (t : triple)
  : Lemma (requires cond_resource i /\ rdfs4a_derives g t)
          (ensures triple_holds i a t) = lemma_vocab_agree ()

let rdfs4b_true (i : interp) (a : bnode_assignment i.idom) (g : rdf_graph) (t : triple)
  : Lemma (requires cond_resource i /\ rdfs4b_derives g t)
          (ensures triple_holds i a t) = lemma_vocab_agree ()

let rdfs5_true (i : interp) (a : bnode_assignment i.idom) (gd gs : rdf_graph) (t : triple)
  : Lemma (requires cond_subPropertyOf_trans i /\ holds_all i a gd /\ holds_all i a gs /\
                    rdfs5_derives2 gd gs t)
          (ensures triple_holds i a t) =
  lemma_vocab_agree ();
  eliminate exists (t1 t2 : triple) (ys : subject).
      memP t1 gd /\ t1.p == i_rdfs_subPropertyOf /\
      memP t2 gs /\ t2.p == i_rdfs_subPropertyOf /\
      subj_term ys == t1.o /\ t2.s == ys /\
      t == ({ s = t1.s; p = i_rdfs_subPropertyOf; o = t2.o } <: triple)
  returns triple_holds i a t
  with _ . begin
    assert (triple_holds i a t1);
    assert (triple_holds i a t2);
    lemma_subj_term_denot i a ys
  end

let rdfs6_true (i : interp) (a : bnode_assignment i.idom) (g : rdf_graph) (t : triple)
  : Lemma (requires cond_subPropertyOf_refl i /\ holds_all i a g /\ rdfs6_derives g t)
          (ensures triple_holds i a t) =
  lemma_vocab_agree ();
  eliminate exists (u : triple).
      memP u g /\ u.p == i_rdf_type /\ u.o == T_IRI i_rdf_Property /\
      t == ({ s = u.s; p = i_rdfs_subPropertyOf; o = subj_term u.s } <: triple)
  returns triple_holds i a t
  with _ . begin
    assert (triple_holds i a u);
    lemma_subj_term_denot i a u.s
  end

let rdfs7_true (i : interp) (a : bnode_assignment i.idom) (g : rdf_graph) (t : triple)
  : Lemma (requires cond_subPropertyOf i /\ holds_all i a g /\ rdfs7_derives g t)
          (ensures triple_holds i a t) =
  lemma_vocab_agree ();
  eliminate exists (decl u : triple) (aa b : wf_iri).
      memP decl g /\ decl.p == i_rdfs_subPropertyOf /\
      decl.s == S_IRI aa /\ decl.o == T_IRI b /\
      memP u g /\ u.p == aa /\
      t == ({ s = u.s; p = b; o = u.o } <: triple)
  returns triple_holds i a t
  with _ . begin
    assert (triple_holds i a decl);
    assert (triple_holds i a u)
  end

let rdfs8_true (i : interp) (a : bnode_assignment i.idom) (g : rdf_graph) (t : triple)
  : Lemma (requires cond_class_subclass_resource i /\ holds_all i a g /\ rdfs8_derives g t)
          (ensures triple_holds i a t) =
  lemma_vocab_agree ();
  eliminate exists (u : triple).
      memP u g /\ u.p == i_rdf_type /\ u.o == T_IRI i_rdfs_Class /\
      t == ({ s = u.s; p = i_rdfs_subClassOf; o = T_IRI i_rdfs_Resource } <: triple)
  returns triple_holds i a t
  with _ . assert (triple_holds i a u)

let rdfs9_true (i : interp) (a : bnode_assignment i.idom) (gd gs : rdf_graph) (t : triple)
  : Lemma (requires cond_subClassOf i /\ holds_all i a gd /\ holds_all i a gs /\
                    rdfs9_derives2 gd gs t)
          (ensures triple_holds i a t) =
  lemma_vocab_agree ();
  eliminate exists (sub typ : triple) (xs : subject).
      memP sub gs /\ sub.p == i_rdfs_subClassOf /\ sub.s == xs /\
      memP typ gd /\ typ.p == i_rdf_type /\ typ.o == subj_term xs /\
      t == ({ s = typ.s; p = i_rdf_type; o = sub.o } <: triple)
  returns triple_holds i a t
  with _ . begin
    assert (triple_holds i a sub);
    assert (triple_holds i a typ);
    lemma_subj_term_denot i a xs;
    assert (icext i (denot_subject i a typ.s) (denot_subject i a xs));
    assert (i.iext (i.i_iri rdfs_subClassOf) (denot_subject i a xs)
                   (denot_term i a sub.o));
    assert (icext i (denot_subject i a typ.s) (denot_term i a sub.o))
  end

let rdfs10_true (i : interp) (a : bnode_assignment i.idom) (g : rdf_graph) (t : triple)
  : Lemma (requires cond_subClassOf_refl i /\ holds_all i a g /\ rdfs10_derives g t)
          (ensures triple_holds i a t) =
  lemma_vocab_agree ();
  eliminate exists (u : triple).
      memP u g /\ u.p == i_rdf_type /\ u.o == T_IRI i_rdfs_Class /\
      t == ({ s = u.s; p = i_rdfs_subClassOf; o = subj_term u.s } <: triple)
  returns triple_holds i a t
  with _ . begin
    assert (triple_holds i a u);
    lemma_subj_term_denot i a u.s
  end

let rdfs11_true (i : interp) (a : bnode_assignment i.idom) (gd gs : rdf_graph) (t : triple)
  : Lemma (requires cond_subClassOf_trans i /\ holds_all i a gd /\ holds_all i a gs /\
                    rdfs11_derives2 gd gs t)
          (ensures triple_holds i a t) =
  lemma_vocab_agree ();
  eliminate exists (t1 t2 : triple) (ys : subject).
      memP t1 gd /\ t1.p == i_rdfs_subClassOf /\
      memP t2 gs /\ t2.p == i_rdfs_subClassOf /\
      subj_term ys == t1.o /\ t2.s == ys /\
      t == ({ s = t1.s; p = i_rdfs_subClassOf; o = t2.o } <: triple)
  returns triple_holds i a t
  with _ . begin
    assert (triple_holds i a t1);
    assert (triple_holds i a t2);
    lemma_subj_term_denot i a ys
  end

let rdfs12_true (i : interp) (a : bnode_assignment i.idom) (g : rdf_graph) (t : triple)
  : Lemma (requires cond_cmp_member i /\ holds_all i a g /\ rdfs12_derives g t)
          (ensures triple_holds i a t) =
  lemma_vocab_agree ();
  eliminate exists (u : triple).
      memP u g /\ u.p == i_rdf_type /\
      u.o == T_IRI i_rdfs_ContainerMembershipProperty /\
      t == ({ s = u.s; p = i_rdfs_subPropertyOf; o = T_IRI i_rdfs_member } <: triple)
  returns triple_holds i a t
  with _ . assert (triple_holds i a u)

let rdfs13_true (i : interp) (a : bnode_assignment i.idom) (g : rdf_graph) (t : triple)
  : Lemma (requires cond_datatype_subclass_literal i /\ holds_all i a g /\
                    rdfs13_derives g t)
          (ensures triple_holds i a t) =
  lemma_vocab_agree ();
  eliminate exists (u : triple).
      memP u g /\ u.p == i_rdf_type /\ u.o == T_IRI i_rdfs_Datatype /\
      t == ({ s = u.s; p = i_rdfs_subClassOf; o = T_IRI i_rdfs_Literal } <: triple)
  returns triple_holds i a t
  with _ . assert (triple_holds i a u)

// `rdf:_n rdfs:subPropertyOf rdfs:member` -- rdfs12 applied to the
// axiomatic `rdf:_n rdf:type rdfs:ContainerMembershipProperty` row.
// True in every RDFS interpretation, with no premise from the data.
let rdfs_member_subproperty_true (i : interp) (a : bnode_assignment i.idom) (t : triple)
  : Lemma (requires cond_cmp_member i /\ cond_rdfs_axioms i /\ rdfs_member_subproperty t)
          (ensures triple_holds i a t) =
  lemma_vocab_agree ();
  eliminate exists (n : wf_iri). is_rdf_member_iri n /\
      t == ({ s = S_IRI n; p = i_rdfs_subPropertyOf; o = T_IRI i_rdfs_member } <: triple)
  returns triple_holds i a t
  with _ . begin
    let ax : triple = { s = S_IRI n; p = i_rdf_type;
                        o = T_IRI i_rdfs_ContainerMembershipProperty } in
    assert (rdfs_axiomatic ax);
    assert (triple_holds i a ax);
    assert (icext i (i.i_iri n) (i.i_iri rdfs_ContainerMembershipProperty))
  end

// The two CONDITION-LEVEL consequences the Spec module names alongside
// `rdfs_member_subproperty`: an endpoint of an `rdfs:subClassOf` triple
// is in IC, and IEXT(I(rdfs:subClassOf)) is reflexive on IC, so the
// self-loop holds. Dual for subPropertyOf on IP. These are what license
// the shipping `rdfs_reflexivity_axioms` harvest (finding RS-1's fix).
let rdfs_subClassOf_endpoint_refl_true (i : interp) (a : bnode_assignment i.idom)
                                       (g : rdf_graph) (t : triple)
  : Lemma (requires cond_subClassOf_ic i /\ cond_subClassOf_refl i /\
                    holds_all i a g /\ rdfs_subClassOf_endpoint_refl g t)
          (ensures triple_holds i a t) =
  lemma_vocab_agree ();
  eliminate exists (u : triple) (xs : subject).
      memP u g /\ u.p == i_rdfs_subClassOf /\
      (u.s == xs \/ u.o == subj_term xs) /\
      t == ({ s = xs; p = i_rdfs_subClassOf; o = subj_term xs } <: triple)
  returns triple_holds i a t
  with _ . begin
    assert (triple_holds i a u);
    lemma_subj_term_denot i a xs;
    lemma_subj_term_denot i a u.s;
    assert (i.iext (i.i_iri rdfs_subClassOf)
                   (denot_subject i a u.s) (denot_term i a u.o));
    assert (icext i (denot_subject i a xs) (i.i_iri rdfs_Class))
  end

let rdfs_subPropertyOf_endpoint_refl_true (i : interp) (a : bnode_assignment i.idom)
                                          (g : rdf_graph) (t : triple)
  : Lemma (requires cond_subPropertyOf_ip i /\ cond_subPropertyOf_refl i /\
                    holds_all i a g /\ rdfs_subPropertyOf_endpoint_refl g t)
          (ensures triple_holds i a t) =
  lemma_vocab_agree ();
  eliminate exists (u : triple) (xs : subject).
      memP u g /\ u.p == i_rdfs_subPropertyOf /\
      (u.s == xs \/ u.o == subj_term xs) /\
      t == ({ s = xs; p = i_rdfs_subPropertyOf; o = subj_term xs } <: triple)
  returns triple_holds i a t
  with _ . begin
    assert (triple_holds i a u);
    lemma_subj_term_denot i a xs;
    lemma_subj_term_denot i a u.s;
    assert (i.iext (i.i_iri rdfs_subPropertyOf)
                   (denot_subject i a u.s) (denot_term i a u.o));
    assert (icext i (denot_subject i a xs) (i.i_iri rdf_Property))
  end

// -------------------------------------------------------------------
// THEOREM. The RDF/RDFS rule tables are SOUND: anything they license
// from a true graph is true. No engine function appears.
// -------------------------------------------------------------------
#push-options "--z3rlimit 60"
val rdfs_licensed_true (dd : datatype_set) (i : interp) (a : bnode_assignment i.idom)
                       (g : rdf_graph) (t : triple)
  : Lemma (requires rdfs_conditions dd i /\ holds_all i a g /\ rdfs_licensed dd g t)
          (ensures  triple_holds i a t)

let rdfs_licensed_true dd i a g t =
  begin
    FStar.Classical.move_requires (rdfD2_true i a g) t;
    FStar.Classical.move_requires (rdfs1_true dd i a) t;
    FStar.Classical.move_requires (rdfs2_true i a g) t;
    FStar.Classical.move_requires (rdfs3_true i a g) t;
    FStar.Classical.move_requires (rdfs4a_true i a g) t;
    FStar.Classical.move_requires (rdfs4b_true i a g) t;
    FStar.Classical.move_requires (rdfs5_true i a g g) t;
    FStar.Classical.move_requires (rdfs6_true i a g) t;
    FStar.Classical.move_requires (rdfs7_true i a g) t;
    FStar.Classical.move_requires (rdfs8_true i a g) t;
    FStar.Classical.move_requires (rdfs9_true i a g g) t;
    FStar.Classical.move_requires (rdfs10_true i a g) t;
    FStar.Classical.move_requires (rdfs11_true i a g g) t;
    FStar.Classical.move_requires (rdfs12_true i a g) t;
    FStar.Classical.move_requires (rdfs13_true i a g) t;
    FStar.Classical.move_requires (rdfs_member_subproperty_true i a) t;
    FStar.Classical.move_requires (rdfs_subClassOf_endpoint_refl_true i a g) t;
    FStar.Classical.move_requires (rdfs_subPropertyOf_endpoint_refl_true i a g) t
  end
#pop-options

// ===================================================================
// 4. SOUNDNESS OF THE SHIPPING CLOSURE.
//
// Composition of section 3 with RDF.Entailment.RDFS.Refinement's
// per-rule licence theorems. The `licensed_by2` shape (source graph
// decoupled from seed graph) is what makes the seven-rule chain inside
// `rdfs_closure_step` go through: the index snapshot is built once,
// from the step's INPUT, while the accumulator grows across the chain.
// ===================================================================

let bridge (i : interp) (a : bnode_assignment i.idom)
           (r : list triple -> triple -> prop) (src seed out : list triple)
  : Lemma (requires holds_all i a seed /\
                    licensed_by2 r src seed out /\
                    (forall (t : triple). r src t ==> triple_holds i a t))
          (ensures  holds_all i a out) = ()

// The per-rule truth-preservation corollaries, in the two-graph shape.
#push-options "--z3rlimit 60"
let rdfs_rule_subPropertyOf_preserves (i : interp) (a : bnode_assignment i.idom)
                                      (g : rdf_graph) (ig : indexed_graph)
  : Lemma (requires cond_subPropertyOf i /\ ig_wf_pred ig /\
                    holds_all i a g /\ holds_all i a ig.ig_triples)
          (ensures  holds_all i a (rdfs_rule_subPropertyOf g ig)) =
  rdfs_rule_subPropertyOf_licensed g ig;
  FStar.Classical.forall_intro
    (FStar.Classical.move_requires (rdfs7_true i a ig.ig_triples));
  bridge i a rdfs7_derives ig.ig_triples g (rdfs_rule_subPropertyOf g ig)

let rdfs_rule_domain_preserves (i : interp) (a : bnode_assignment i.idom)
                               (g : rdf_graph) (ig : indexed_graph)
  : Lemma (requires cond_domain i /\ ig_wf_pred ig /\
                    holds_all i a g /\ holds_all i a ig.ig_triples)
          (ensures  holds_all i a (rdfs_rule_domain g ig)) =
  rdfs_rule_domain_licensed g ig;
  FStar.Classical.forall_intro
    (FStar.Classical.move_requires (rdfs2_true i a ig.ig_triples));
  bridge i a rdfs2_derives ig.ig_triples g (rdfs_rule_domain g ig)

let rdfs_rule_range_preserves (i : interp) (a : bnode_assignment i.idom)
                              (g : rdf_graph) (ig : indexed_graph)
  : Lemma (requires cond_range i /\ ig_wf_pred ig /\
                    holds_all i a g /\ holds_all i a ig.ig_triples)
          (ensures  holds_all i a (rdfs_rule_range g ig)) =
  rdfs_rule_range_licensed g ig;
  FStar.Classical.forall_intro
    (FStar.Classical.move_requires (rdfs3_true i a ig.ig_triples));
  bridge i a rdfs3_derives ig.ig_triples g (rdfs_rule_range g ig)

let rdfs_rule_subClassOf_preserves (i : interp) (a : bnode_assignment i.idom)
                                   (g : rdf_graph) (ig : indexed_graph)
  : Lemma (requires cond_subClassOf i /\ ig_wf_sp ig /\
                    holds_all i a g /\ holds_all i a ig.ig_triples)
          (ensures  holds_all i a (rdfs_rule_subClassOf g ig)) =
  rdfs_rule_subClassOf_licensed g ig;
  FStar.Classical.forall_intro
    (FStar.Classical.move_requires (rdfs9_true i a g ig.ig_triples));
  bridge i a (rdfs9_derives2 g) ig.ig_triples g (rdfs_rule_subClassOf g ig)

let rdfs_rule_subClassOf_trans_preserves (i : interp) (a : bnode_assignment i.idom)
                                         (g : rdf_graph) (ig : indexed_graph)
  : Lemma (requires cond_subClassOf_trans i /\ ig_wf_sp ig /\
                    holds_all i a g /\ holds_all i a ig.ig_triples)
          (ensures  holds_all i a (rdfs_rule_subClassOf_trans g ig)) =
  rdfs_rule_subClassOf_trans_licensed g ig;
  FStar.Classical.forall_intro
    (FStar.Classical.move_requires (rdfs11_true i a g ig.ig_triples));
  bridge i a (rdfs11_derives2 g) ig.ig_triples g (rdfs_rule_subClassOf_trans g ig)

let rdfs_rule_subPropertyOf_trans_preserves (i : interp) (a : bnode_assignment i.idom)
                                            (g : rdf_graph) (ig : indexed_graph)
  : Lemma (requires cond_subPropertyOf_trans i /\ ig_wf_sp ig /\
                    holds_all i a g /\ holds_all i a ig.ig_triples)
          (ensures  holds_all i a (rdfs_rule_subPropertyOf_trans g ig)) =
  rdfs_rule_subPropertyOf_trans_licensed g ig;
  FStar.Classical.forall_intro
    (FStar.Classical.move_requires (rdfs5_true i a g ig.ig_triples));
  bridge i a (rdfs5_derives2 g) ig.ig_triples g (rdfs_rule_subPropertyOf_trans g ig)

let rdfs_rule_container_membership_preserves (i : interp) (a : bnode_assignment i.idom)
                                             (g : rdf_graph) (ig : indexed_graph)
  : Lemma (requires cond_cmp_member i /\ cond_rdfs_axioms i /\ holds_all i a g)
          (ensures  holds_all i a (rdfs_rule_container_membership g ig)) =
  rdfs_rule_container_membership_licensed g ig;
  FStar.Classical.forall_intro
    (FStar.Classical.move_requires (rdfs_member_subproperty_true i a))

// The rows added 2026-07-31 (RS-2). Each reads its premises from the
// graph it folds over, so the source and seed graphs coincide and the
// bridge is applied at the diagonal.
let rdfs_rule_recognized_datatypes_preserves (i : interp) (a : bnode_assignment i.idom)
                                             (g : rdf_graph) (ig : indexed_graph)
  : Lemma (requires cond_datatypes_minimal i /\ holds_all i a g)
          (ensures  holds_all i a (rdfs_rule_recognized_datatypes g ig)) =
  rdfs_rule_recognized_datatypes_licensed g ig;
  FStar.Classical.forall_intro
    (FStar.Classical.move_requires (rdfs1_true d_minimal i a))

let rdfs_rule_resource_subject_preserves (i : interp) (a : bnode_assignment i.idom)
                                         (g : rdf_graph) (ig : indexed_graph)
  : Lemma (requires cond_resource i /\ holds_all i a g)
          (ensures  holds_all i a (rdfs_rule_resource_subject g ig)) =
  rdfs_rule_resource_subject_licensed g ig;
  FStar.Classical.forall_intro
    (FStar.Classical.move_requires (rdfs4a_true i a g));
  bridge i a rdfs4a_derives g g (rdfs_rule_resource_subject g ig)

let rdfs_rule_resource_object_preserves (i : interp) (a : bnode_assignment i.idom)
                                        (g : rdf_graph) (ig : indexed_graph)
  : Lemma (requires cond_resource i /\ holds_all i a g)
          (ensures  holds_all i a (rdfs_rule_resource_object g ig)) =
  rdfs_rule_resource_object_licensed g ig;
  FStar.Classical.forall_intro
    (FStar.Classical.move_requires (rdfs4b_true i a g));
  bridge i a rdfs4b_derives g g (rdfs_rule_resource_object g ig)

let rdfs_rule_class_subclass_resource_preserves (i : interp) (a : bnode_assignment i.idom)
                                                (g : rdf_graph) (ig : indexed_graph)
  : Lemma (requires cond_class_subclass_resource i /\ holds_all i a g)
          (ensures  holds_all i a (rdfs_rule_class_subclass_resource g ig)) =
  rdfs_rule_class_subclass_resource_licensed g ig;
  FStar.Classical.forall_intro
    (FStar.Classical.move_requires (rdfs8_true i a g));
  bridge i a rdfs8_derives g g (rdfs_rule_class_subclass_resource g ig)

let rdfs_rule_datatype_subclass_literal_preserves (i : interp) (a : bnode_assignment i.idom)
                                                  (g : rdf_graph) (ig : indexed_graph)
  : Lemma (requires cond_datatype_subclass_literal i /\ holds_all i a g)
          (ensures  holds_all i a (rdfs_rule_datatype_subclass_literal g ig)) =
  rdfs_rule_datatype_subclass_literal_licensed g ig;
  FStar.Classical.forall_intro
    (FStar.Classical.move_requires (rdfs13_true i a g));
  bridge i a rdfs13_derives g g (rdfs_rule_datatype_subclass_literal g ig)
#pop-options

// -------------------------------------------------------------------
// THEOREM. One RDFS closure step preserves truth.
//
// `ig_wf_sp (build_indexed g)` is an explicit hypothesis, not an
// oversight: recovering a triple's subject and predicate from the
// composite key `sp_key s p` needs sp_key injectivity, which needs
// "U+001F never occurs in a blank-node label". That is the OWL pilot's
// finding F1, unchanged, and this vertical inherits it because rdfs9 /
// rdfs11 / rdfs5 are the index-driven rules.
// -------------------------------------------------------------------
#push-options "--z3rlimit 120"
val rdfs_closure_step_sound (dd : datatype_set) (i : interp)
                            (a : bnode_assignment i.idom) (g : rdf_graph)
  : Lemma (requires rdfs_conditions dd i /\ holds_all i a g /\
                    ig_wf_sp (build_indexed g))
          (ensures  holds_all i a (rdfs_closure_step g))

let rdfs_closure_step_sound dd i a g =
  let ig = build_indexed g in
  lemma_build_indexed_wf_pred g;
  assert (ig.ig_triples == g);
  assert (ig_wf_pred ig);
  let g1 = rdfs_rule_subPropertyOf g ig in
  rdfs_rule_subPropertyOf_preserves i a g ig;
  let g2 = rdfs_rule_domain g1 ig in
  rdfs_rule_domain_preserves i a g1 ig;
  let g3 = rdfs_rule_range g2 ig in
  rdfs_rule_range_preserves i a g2 ig;
  let g4 = rdfs_rule_subClassOf g3 ig in
  rdfs_rule_subClassOf_preserves i a g3 ig;
  let g5 = rdfs_rule_container_membership g4 ig in
  rdfs_rule_container_membership_preserves i a g4 ig;
  let g6 = rdfs_rule_subClassOf_trans g5 ig in
  rdfs_rule_subClassOf_trans_preserves i a g5 ig;
  let g7 = rdfs_rule_subPropertyOf_trans g6 ig in
  rdfs_rule_subPropertyOf_trans_preserves i a g6 ig;
  // The rows added 2026-07-31 (RS-2), in pipeline order.
  let g8 = rdfs_rule_recognized_datatypes g7 ig in      // rdfs1
  rdfs_rule_recognized_datatypes_preserves i a g7 ig;
  let g9 = rdfs_rule_class_subclass_resource g8 ig in   // rdfs8
  rdfs_rule_class_subclass_resource_preserves i a g8 ig;
  let g10 = rdfs_rule_datatype_subclass_literal g9 ig in // rdfs13
  rdfs_rule_datatype_subclass_literal_preserves i a g9 ig;
  let g11 = rdfs_rule_resource_subject g10 ig in        // rdfs4a
  rdfs_rule_resource_subject_preserves i a g10 ig;
  let g12 = rdfs_rule_resource_object g11 ig in         // rdfs4b
  rdfs_rule_resource_object_preserves i a g11 ig;
  FStar.Classical.forall_intro (lemma_graph_dedup_sort_memP g12);
  assert (rdfs_closure_step g == graph_dedup_sort g12)
#pop-options

// -------------------------------------------------------------------
// The index hypothesis, stated so that it is SATISFIABLE.
//
// `ig_wf_sp (build_indexed h)` is not provable for an arbitrary h (the
// pilot's finding F1: sp_key injectivity needs "U+001F never occurs in
// a blank-node label", which nothing in the tree enforces), so the
// driver's soundness has to assume it. Assuming it for EVERY graph
// would make the theorem vacuous, because a blank-node label
// containing U+001F does make it false. The hypothesis is therefore
// scoped to the graphs the driver actually indexes: the chain
// g, step g, step (step g), ... Closure rules never mint blank-node
// labels, so a graph with clean labels has a clean chain, and the
// hypothesis is satisfied by every such graph.
// -------------------------------------------------------------------
let rec closure_iter (g : rdf_graph) (n : nat) : Tot rdf_graph (decreases n) =
  if n = 0 then g else closure_iter (rdfs_closure_step g) (n - 1)

let closure_chain_wf (g : rdf_graph) : prop =
  forall (n : nat). ig_wf_sp (build_indexed (closure_iter g n))

let lemma_closure_iter_shift (g : rdf_graph) (n : nat)
  : Lemma (closure_iter (rdfs_closure_step g) n == closure_iter g (n + 1)) = ()

let lemma_chain_shift (g : rdf_graph)
  : Lemma (requires closure_chain_wf g)
          (ensures  closure_chain_wf (rdfs_closure_step g)) =
  FStar.Classical.forall_intro (lemma_closure_iter_shift g)

// -------------------------------------------------------------------
// THEOREM. The whole fixed-point driver preserves truth, at any fuel.
// -------------------------------------------------------------------
// --z3rlimit 240 + the explicit `fuel > 0` (2026-07-31): the RS-2 rows
// enlarged the encoding of `rdfs_closure_step` enough that z3 stopped
// discharging the recursive call's `fuel - 1 : nat` subtyping and its
// `<<` decreases obligation on its own. A budget bump plus one hint;
// no --lax, no --admit_smt_queries.
#push-options "--z3rlimit 240"
let rec rdfs_closure_sound (dd : datatype_set) (i : interp)
                           (a : bnode_assignment i.idom) (g : rdf_graph) (fuel : nat)
  : Lemma (requires rdfs_conditions dd i /\ holds_all i a g /\ closure_chain_wf g)
          (ensures  holds_all i a (rdfs_closure g fuel))
          (decreases fuel) =
  if fuel = 0 then ()
  else begin
    assert (fuel > 0);
    let g' = rdfs_closure_step g in
    assert (closure_iter g 0 == g);
    rdfs_closure_step_sound dd i a g;
    lemma_chain_shift g;
    if graph_len g' = graph_len g then ()
    else rdfs_closure_sound dd i a g' (fuel - 1)
  end
#pop-options

// -------------------------------------------------------------------
// COROLLARY (the headline). The shipping RDFS closure is RDFS-SOUND:
// the closed graph is RDFS-entailed by the input.
// -------------------------------------------------------------------
val rdfs_closure_entails (dd : datatype_set) (g : rdf_graph) (fuel : nat)
  : Lemma (requires closure_chain_wf g)
          (ensures  rdfs_entails dd g (rdfs_closure g fuel))

let rdfs_closure_entails dd g fuel =
  introduce forall (i : interp).
      rdfs_conditions dd i ==> satisfies i g ==> satisfies i (rdfs_closure g fuel)
  with introduce rdfs_conditions dd i ==>
                 (satisfies i g ==> satisfies i (rdfs_closure g fuel))
  with _ . introduce satisfies i g ==> satisfies i (rdfs_closure g fuel)
  with _ . begin
    eliminate exists (a : bnode_assignment i.idom). holds_all i a g
    returns satisfies i (rdfs_closure g fuel)
    with _ . rdfs_closure_sound dd i a g fuel
  end

// -------------------------------------------------------------------
// COROLLARY. The pure-RDF regime function is RDF-SOUND.
// -------------------------------------------------------------------
val rdf_property_axiom_closure_entails (g : rdf_graph)
  : Lemma (rdf_entails g (rdf_property_axiom_closure g))

let rdf_property_axiom_closure_entails g =
  introduce forall (i : interp).
      rdf_conditions i ==> satisfies i g ==> satisfies i (rdf_property_axiom_closure g)
  with introduce rdf_conditions i ==>
                 (satisfies i g ==> satisfies i (rdf_property_axiom_closure g))
  with _ . introduce satisfies i g ==> satisfies i (rdf_property_axiom_closure g)
  with _ . begin
    eliminate exists (a : bnode_assignment i.idom). holds_all i a g
    returns satisfies i (rdf_property_axiom_closure g)
    with _ . begin
      rdf_property_axiom_closure_licensed g;
      FStar.Classical.forall_intro (FStar.Classical.move_requires (rdfD2_true i a g));
      assert (holds_all i a (rdf_property_axiom_closure g))
    end
  end

// ===================================================================
// 4c. `rdfs_closure_with_reflexivity` IS SOUND (2026-07-31).
//
// Before the RS-1 regime split this theorem was DELIBERATELY ABSENT:
// the function harvested classes and properties through the OWL typing
// IRIs, which no RDFS condition licenses, so the only way to prove it
// sound would have been to weaken the specification -- exactly what
// this pattern exists to prevent. The split fixed the function, and
// `RDF.Entailment.RDFS.Refinement.rdfs_reflexivity_axioms_licensed`
// proves the narrow harvest emits only `rdfs_licensed` triples, so the
// proof now closes against the specification as written.
//
// Stated at `d_minimal`: the licence theorem is at `d_minimal`, and the
// harvest emits no datatype triple, so no wider D is needed.
//
// The hypothesis names the index chain of BOTH closure passes, for the
// reason section 3 of the design note records: a `forall`-over-all-graphs
// index hypothesis is false and would make the theorem vacuous.
// ===================================================================

let rdfs_reflexivity_axioms_preserves (i : interp) (a : bnode_assignment i.idom)
                                      (g : rdf_graph)
  : Lemma (requires rdfs_conditions d_minimal i /\ holds_all i a g)
          (ensures  holds_all i a (rdfs_reflexivity_axioms g)) =
  rdfs_reflexivity_axioms_licensed g;
  FStar.Classical.forall_intro
    (FStar.Classical.move_requires (rdfs_licensed_true d_minimal i a g))

let lemma_add_triples_if_new_holds (i : interp) (a : bnode_assignment i.idom)
                                   (g ts : rdf_graph)
  : Lemma (requires holds_all i a g /\ holds_all i a ts)
          (ensures  holds_all i a (add_triples_if_new g ts)) =
  FStar.Classical.forall_intro (lemma_add_triples_if_new_memP g ts)

// The second pass's input, named so the hypothesis can mention it.
let reflexivity_seeded (g : rdf_graph) (fuel : nat) : rdf_graph =
  let closed = rdfs_closure g fuel in
  add_triples_if_new closed (rdfs_reflexivity_axioms closed)

#push-options "--z3rlimit 120"
val rdfs_closure_with_reflexivity_sound (i : interp) (a : bnode_assignment i.idom)
                                        (g : rdf_graph) (fuel : nat)
  : Lemma (requires rdfs_conditions d_minimal i /\ holds_all i a g /\
                    closure_chain_wf g /\
                    closure_chain_wf (reflexivity_seeded g fuel))
          (ensures  holds_all i a (rdfs_closure_with_reflexivity g fuel))

let rdfs_closure_with_reflexivity_sound i a g fuel =
  let closed = rdfs_closure g fuel in
  rdfs_closure_sound d_minimal i a g fuel;
  rdfs_reflexivity_axioms_preserves i a closed;
  lemma_add_triples_if_new_holds i a closed (rdfs_reflexivity_axioms closed);
  assert (reflexivity_seeded g fuel ==
          add_triples_if_new closed (rdfs_reflexivity_axioms closed));
  rdfs_closure_sound d_minimal i a (reflexivity_seeded g fuel) fuel
#pop-options

// COROLLARY. The RDFS regime's entry point is RDFS-SOUND.
val rdfs_closure_with_reflexivity_entails (g : rdf_graph) (fuel : nat)
  : Lemma (requires closure_chain_wf g /\ closure_chain_wf (reflexivity_seeded g fuel))
          (ensures  rdfs_entails d_minimal g (rdfs_closure_with_reflexivity g fuel))

let rdfs_closure_with_reflexivity_entails g fuel =
  introduce forall (i : interp).
      rdfs_conditions d_minimal i ==>
      satisfies i g ==> satisfies i (rdfs_closure_with_reflexivity g fuel)
  with introduce rdfs_conditions d_minimal i ==>
                 (satisfies i g ==> satisfies i (rdfs_closure_with_reflexivity g fuel))
  with _ . introduce satisfies i g ==> satisfies i (rdfs_closure_with_reflexivity g fuel)
  with _ . begin
    eliminate exists (a : bnode_assignment i.idom). holds_all i a g
    returns satisfies i (rdfs_closure_with_reflexivity g fuel)
    with _ . rdfs_closure_with_reflexivity_sound i a g fuel
  end


// ===================================================================
// 4b. FINDING RS-1, the model-theoretic half.
//
// RDF.Entailment.RDFS.Refinement.reflexivity_axioms_not_rdfs_sound is
// the syntactic witness: `rdfs_reflexivity_axioms` emits
// `c rdfs:subClassOf c` from `c rdf:type owl:Class`, and no row of
// either rule table licenses it. The semantic side of the same
// statement is the contrapositive of `cond_subClassOf_refl`: the ONLY
// premise-free route the RDFS conditions offer to a subClassOf
// self-loop is membership in IC = ICEXT(I(rdfs:Class)). An RDFS
// interpretation is free to read `owl:Class` as an arbitrary IRI, so
// `c rdf:type owl:Class` supplies no such membership.
//
// (Under the OWL 2 RDF-Based Semantics, Table 5.3 DOES identify
// ICEXT(I(owl:Class)) with IC, which is why the same shipping code is
// sound in the OWL-RL regime and unsound in the RDFS regime. That
// contrast is the RDFS-rung analogue of the simple rung's finding
// SE-1, where `literal_eq`'s XMLLiteral canonicalisation is unlicensed
// at the simple rung and licensed at this one.)
// ===================================================================

let reflexivity_needs_rdfs_Class (i : interp) (x : i.idom)
  : Lemma (requires cond_subClassOf_refl i /\
                    ~(i.iext (i.i_iri rdfs_subClassOf) x x))
          (ensures  ~(icext i x (i.i_iri rdfs_Class))) = ()

// ===================================================================
// 5. WHAT IS NOT PROVED HERE
//
// Stated plainly so no later document has to reconstruct it.
//
// * COMPLETENESS. See RDF.Entailment.RDFS.Refinement's finding RS-2:
//   rdfs1, rdfs4a, rdfs4b, rdfs8, rdfs13 and rdfD1 have no
//   implementation, and the axiomatic triples are not seeded (the
//   attempt was made and reverted -- RDFS.Closure.fsti's
//   `rdfs_closure_with_reflexivity` banner records the measured OWL-RL
//   regression). So the shipping closure is NOT the RDFS closure and
//   no unrestricted completeness theorem can be true of it. What IS in
//   reach is the rho-df result of Munoz/Perez/Gutierrez, whose six
//   rules are exactly the shipping six; the fragment predicate
//   `rho_df_graph` is defined in the Spec module for that purpose and
//   the theorem is the next commit's target. The blocking analysis is
//   in the design note.
// * `rdfs_closure_with_reflexivity`. NO LONGER ABSENT as of 2026-07-31
//   -- see section 4c. It used to be deliberately unproven because it
//   called a harvest that read the OWL typing IRIs, which no RDFS
//   condition licenses (finding RS-1). The regime split fixed the
//   function rather than weakening the specification, and the theorem
//   then closed on the specification as written. The OWL-regime
//   variant, `owl_rdfs_closure_with_reflexivity`, is still NOT proven
//   RDFS-sound and must not be -- `owl_reflexivity_axioms_not_rdfs_sound`
//   in the Refinement module is the witness that it cannot be.
// * The GENUINE RDFS-interpretation class. `interp` is the OWL pilot's
//   superset. For soundness the inclusion runs the right way and every
//   theorem above is thereby STRONGER. For completeness it runs the
//   wrong way. Same phase-2 embedding obligation the simple rung
//   recorded, now with a third customer.
// * `ig_wf_sp (build_indexed h)`. Assumed as an explicit hypothesis
//   wherever the index-driven rules are involved; it is the pilot's
//   finding F1 (sp_key injectivity) and is not this vertical's to
//   discharge.
// ===================================================================
