module RDF.Entailment.RDF.Spec

// ===================================================================
// A DECLARATIVE specification of RDF ENTAILMENT — rung two of Hayes'
// entailment ladder, above simple entailment
// (RDF.Entailment.Simple.Spec.fst) and below RDFS entailment
// (RDF.Entailment.RDFS.Spec.fst).
//
// This module deliberately computes nothing about the engine. It does
// NOT open RDFS.Closure, OWL.Closure, RDF.Graph.Executable or
// RDF.Entailment.Regime — a reader can diff it against the W3C text
// alone. The shipping functions are proven against it in
// RDF.Entailment.RDFS.Refinement.fst; the model theory that justifies
// each rule is in RDF.Entailment.RDFS.ModelTheory.fst.
//
// -------------------------------------------------------------------
// BASELINE PINNING (the pilot's phase-2 obligation, restated)
// -------------------------------------------------------------------
// Primary baseline: RDF 1.1 Semantics, W3C Recommendation
// 25 February 2014 (https://www.w3.org/TR/rdf11-mt/).
//   section 8, "RDF Interpretations" — the semantic conditions, the
//   RDF axiomatic triples, and the RDF entailment rule table
//   (rows rdfD1 and rdfD2).
//
// Cross-checked against Hayes, RDF Semantics, W3C Recommendation
// 10 February 2004 (REC-rdf-mt-20040210) section 3 ("Interpreting the
// RDF vocabulary"), the baseline the normative OWL 2 (2012)
// specifications build on.
//
// The RDF-rung DELTA between the two baselines — the table this
// vertical owes, per the mission brief:
//
//   D1. LITERAL STRUCTURE. RDF 2004 has plain literals (with an
//       optional language tag) and typed literals as two different
//       abstract-syntax shapes; RDF 1.1 has exactly one shape, and
//       every literal carries a datatype IRI (Concepts section 3.3),
//       with rdf:langString for language-tagged strings. `RDF.Term`'s
//       `literal` record is the RDF 1.1 shape, so this module is
//       written against RDF 1.1 and the 2004 reading is recovered by
//       reading a plain literal as xsd:string / rdf:langString.
//   D2. rdf:XMLLiteral. 2004 makes XMLLiteral a REQUIRED recognized
//       datatype of every rdf-interpretation (section 3.1: "I(rdf:
//       XMLLiteral) ... the value space ... well-typed XML literals"),
//       so 2004-RDF entailment DOES identify two XMLLiteral literals
//       whose lexical forms are exclusive-canonical-XML-equal. RDF 1.1
//       demotes rdf:XMLLiteral to a NON-NORMATIVE datatype (Concepts
//       section 5.3) and makes recognizing it optional. See the
//       finding on `literal_eq` in the design note: XMLLiteral
//       canonicalisation is LICENSED at this rung under the 2004
//       baseline (and under RDF 1.1 for an interpretation recognizing
//       rdf:XMLLiteral), which is the exact contrast with the simple
//       rung, where it is licensed under neither.
//   D3. LANGUAGE TAG CASE. 2004 Concepts section 6.5 normalizes the
//       abstract-syntax language identifier to lower case, so `@EN`
//       does not occur; RDF 1.1 Concepts section 3.3 keeps the tag
//       verbatim in the term but puts the VALUE of a language-tagged
//       string at (lexical form, lowercased tag) — RDF 1.1 Semantics
//       section 8's condition on IL for rdf:langString. So under RDF
//       1.1, case-insensitive language-tag matching is a D-entailment
//       (hence RDF-entailment) behaviour, NOT a simple-entailment one.
//       Same contrast as D2.
//   D4. IRIs vs URI references. 2004 says "URI reference" throughout;
//       1.1 says "IRI". No semantic content; `RDF.Term.wf_iri` covers
//       both.
//   D5. GENERALIZED RDF. RDF 1.1 Semantics states the entailment rules
//       over GENERALIZED RDF triples (literals and blank nodes allowed
//       in any position) and then observes that the closure of an
//       ordinary graph may leave the ordinary syntax. `RDF.Term`'s
//       `subject` type is IRI-or-bnode only, so this tree cannot
//       express a literal-subject triple. Every rule below whose
//       conclusion would need one is therefore stated with an explicit
//       subject-recovery premise, and the resulting INCOMPLETENESS is
//       named rather than hidden (see `rdfs3_derives` in the RDFS
//       module).
//   D6. RDF 1.2 TRIPLE TERMS. Absent from both baselines. Handled
//       syntactically (the engine runs on graphs that may contain
//       them) and QUARANTINED from the model theory with the
//       `graph_tt_free` hypothesis the simple-entailment vertical
//       introduced (RDF.Entailment.Simple.Spec.graph_tt_free), reused
//       verbatim.
// ===================================================================

open FStar.List.Tot
open RDF.Term
open RDF.Triple
open RDF.Vocabulary.Axioms

// -------------------------------------------------------------------
// The recognized datatype set D.
//
// RDF 1.1 Semantics section 8 defines RDF entailment "recognizing D"
// for a set D of datatype IRIs, with rdf:langString and xsd:string
// always in D. Keeping D a parameter is what lets the rdfD1 rule and
// the XMLLiteral question (delta D2) be stated without prejudging
// which datatypes an implementation recognizes.
// -------------------------------------------------------------------
let datatype_set = wf_iri -> prop

// The minimum D of RDF 1.1 Semantics section 8: "RDF interpretations
// ... recognize the datatype IRIs rdf:langString and xsd:string".
let d_minimal : datatype_set =
  fun (d : wf_iri) -> d == rdf_lang_string \/ d == xsd_string

// -------------------------------------------------------------------
// RULE rdfD2, RDF 1.1 Semantics section 8, RDF entailment rule table,
// quoted verbatim:
//
//   "rdfD2 | xxx aaa yyy . | aaa rdf:type rdf:Property ."
//
// (2004 numbers the same rule `rdf1`; the content is identical.)
//
// `aaa` is a predicate, hence an IRI, hence legal as the subject of
// the conclusion — this rule needs no generalized-RDF escape.
// -------------------------------------------------------------------
let rdfD2_conclusion (u : triple) : triple =
  { s = S_IRI u.p; p = i_rdf_type; o = T_IRI i_rdf_Property }

let rdfD2_derives (g : list triple) (t : triple) : prop =
  exists (u : triple). memP u g /\ t == rdfD2_conclusion u

// -------------------------------------------------------------------
// RULE rdfD1, RDF 1.1 Semantics section 8, quoted verbatim:
//
//   "rdfD1 | xxx aaa "sss"^^ddd . (for ddd in D) |
//            xxx aaa _:nnn . _:nnn rdf:type ddd ."
//
// The conclusion mints a FRESH blank node, so the relation is stated
// with the label as an explicit parameter plus the freshness side
// condition, rather than existentially — a rule that may invent a name
// is not a function of the premise alone.
//
// NOTE (deliberate): the shipping tree implements NO rdfD1. It is
// specified here so that the RDF rung's rule table is complete in the
// document and the gap is visible, and so that the RDFS module's
// completeness statement can name the fragment where rdfD1 cannot
// fire. See the design note.
// -------------------------------------------------------------------
// Freshness, stated at the top level of a triple. (An RDF 1.2 triple
// term could bury the same label deeper; rdfD1 is not implemented in
// this tree, so nothing depends on that case, and delta D6 quarantines
// triple terms from the model theory anyway.)
let bnode_fresh_for (b : bnode_id) (g : list triple) : prop =
  forall (t : triple). memP t g ==>
    t.s =!= S_BNode b /\ t.o =!= T_BNode b

let rdfD1_derives (dd : datatype_set) (g : list triple)
                  (b : bnode_id) (t1 t2 : triple) : prop =
  bnode_fresh_for b g /\
  (exists (u : triple) (l : wf_literal).
     memP u g /\ u.o == T_Literal l /\ dd l.datatype /\
     t1 == ({ s = u.s; p = u.p; o = T_BNode b } <: triple) /\
     t2 == ({ s = S_BNode b; p = i_rdf_type; o = T_IRI l.datatype } <: triple))

// -------------------------------------------------------------------
// The RDF axiomatic triples.
//
// RDF 1.1 Semantics section 8 lists them; the finite rows are already
// transcribed, one `let` per row with its spec citation, in
// RDF.Vocabulary.Axioms (`rdf_axiomatic_triples`, 8 rows). This module
// reuses that table rather than making a second copy — the whole point
// of the "no cobbling" rule.
//
// The INFINITE family `rdf:_1 rdf:type rdf:Property .`, `rdf:_2 ...`
// is not tabulable; it is captured by the schema `rdf_container_axiom`
// below, which is the declarative form of what the shipping
// `rdfs_rule_container_membership` approximates on a finite slice.
// -------------------------------------------------------------------
// `rdf:_n` for some positive n. Stated as membership in the syntactic
// family rather than by arithmetic on the IRI string: what matters
// downstream is only that the shipping engine's finite slice
// (`rdf:_1` .. `rdf:_5`) is CONTAINED in it.
let rdf_member_iri_str (n : string) : string =
  FStar.String.concat "" ["http://www.w3.org/1999/02/22-rdf-syntax-ns#_"; n]

let is_rdf_member_iri (i : wf_iri) : prop =
  exists (n : string). (i <: string) == rdf_member_iri_str n

let rdf_axiomatic (t : triple) : prop =
  memP t rdf_axiomatic_triples \/
  (exists (i : wf_iri).
     is_rdf_member_iri i /\
     t == ({ s = S_IRI i; p = i_rdf_type; o = T_IRI i_rdf_Property } <: triple))

// -------------------------------------------------------------------
// THE SPECIFICATION, syntactic side: what it means for a graph to be
// RDF-CLOSED (recognizing D).
//
// RDF 1.1 Semantics section 8's completeness statement is about
// closures: "If S is RDF consistent, then S RDF entails E just when
// the generalized RDF closure of S towards E simply entails E." A
// graph is a closure when it contains the axiomatic triples and is
// shut under the rule table.
//
// rdfD1 is excluded from `rdf_closed` on purpose: it mints fresh blank
// nodes, so a graph closed under it is not finite. The spec text
// handles this the same way, by taking the closure "towards E".
// -------------------------------------------------------------------
let rdf_closed (g : list triple) : prop =
  (forall (t : triple). rdf_axiomatic t ==> memP t g) /\
  (forall (t : triple). rdfD2_derives g t ==> memP t g)

// The weaker, monotone notion the shipping engine actually targets:
// every triple the engine adds is licensed by the rule table applied
// to the ORIGINAL graph. This is the property a soundness proof about
// a one-pass rule function establishes, and it composes: see
// `rdf_step_licensed` used in the Refinement module.
let rdf_step_licensed (g out : list triple) : prop =
  forall (t : triple). memP t out ==>
    (memP t g \/ rdf_axiomatic t \/ rdfD2_derives g t)

// -------------------------------------------------------------------
// finite_rdf_axioms_sound (adoption item A5, docs/designissues/2026-08-
// 05-semantics-proposal-adoption.md): the bridge from the transcribed
// finite table (`RDF.Vocabulary.Axioms.rdf_axiomatic_triples`, 8 rows)
// to the semantic-side recognizer `rdf_axiomatic` above, made an
// explicit checked lemma rather than left implicit.
//
// Today that bridge is IMPLICIT: it is exactly the left disjunct of
// `rdf_axiomatic`'s own definition (line ~178), so any proof that
// needs it re-derives the fact by unfolding the disjunction on the
// spot (see e.g. `RDF.Semantics.HypothesisWitness.lemma_sep_rdf_axioms`,
// which does this inline via `eliminate`). Naming it here means a
// reader — or a future proof — can cite `finite_rdf_axioms_sound`
// instead of re-noticing the disjunct.
//
// No existing predicate in this module (or elsewhere in the tree) is
// separate from `rdf_axiomatic` and narrower than it; `rdf_axiomatic`
// itself is the semantic-side predicate the adoption item means (it is
// exactly "finite table OR rdf:_n family", the split the proposal's
// question 7 asked for and the tree already answered). So this lemma
// is stated against `rdf_axiomatic`, in this module, rather than
// introducing a second predicate that would just restate it.
//
// SOUNDNESS DIRECTION ONLY, per the proposal's own rule: this does NOT
// claim the finite table is a COMPLETE listing of every RDF axiomatic
// triple (the `rdf:_n` family is infinite and handled by
// `is_rdf_member_iri` above, not by enumeration) — see the module
// banner ("no cobbling") and RDF.Vocabulary.Axioms's own banner.
//
// Proved by list enumeration over the finite table (8 rows): `memP t
// rdf_axiomatic_triples` unfolds to the same disjunction of equalities
// `rdf_axiomatic` itself checks in its left disjunct, so every one of
// the 8 named triples (`rdf_axiom_type_type_property`, ...,
// `rdf_axiom_nil_type_list`) discharges by \/-introduction alone; no
// row needs a separate case split on its shape.
// -------------------------------------------------------------------
let finite_rdf_axioms_sound (t : triple)
  : Lemma (requires memP t rdf_axiomatic_triples)
          (ensures  rdf_axiomatic t) = ()
