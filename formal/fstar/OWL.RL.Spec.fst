module OWL.RL.Spec

// ===================================================================
// A DECLARATIVE specification of the OWL 2 RL/RDF entailment rules.
//
// Like RDF.Entailment.RDFS.Spec (whose idiom this module clones), it
// computes nothing and mentions no function of the engine: it does NOT
// open OWL.Closure, RDFS.Closure, RDF.Graph.Executable or
// RDF.Entailment.Regime. A reviewer can diff it against the W3C rule
// table alone. Even the OWL vocabulary IRIs are spelled LOCALLY,
// verbatim from the namespace document, rather than imported from
// OWL.Closure — so an engine-side spelling mistake cannot silently
// become "the spec" here; it becomes a refinement-proof failure.
//
// -------------------------------------------------------------------
// BASELINE PINNING
// -------------------------------------------------------------------
// Primary baseline: OWL 2 Web Ontology Language Profiles (Second
// Edition), W3C Recommendation 11 December 2012
// (https://www.w3.org/TR/owl2-profiles/), section 4.3 "OWL 2 RL",
// rule tables 4-9 ("The Semantics of Equality", "... of Axioms about
// Properties", "... of Classes", "... of Class Axioms", "... of
// Datatypes", "... of Schema Vocabulary"). Rules are quoted row by
// row in the table's own T(...) notation.
//
// THIS FILE IS LANDING 1 OF A FAMILY-BY-FAMILY PROGRAM (approved
// 2026-08-04): Table 4's two families — equality (eq-*) and property
// axioms (prp-*) — complete, including the clash rows. Tables 5-9 and
// the engine's own sound extensions follow in later landings; the
// checklist at the bottom of this banner is the ledger.
//
// -------------------------------------------------------------------
// HOW THE T(...) NOTATION IS TRANSCRIBED
// -------------------------------------------------------------------
// * A premise "T(?x, ?p, ?y)" becomes an `exists`-bound triple that is
//   `memP` in the graph, with each table variable one bound variable.
// * A conclusion row becomes an equation fixing the derived triple's
//   record. Rules with several conclusion triples (eq-ref) become a
//   DISJUNCTION over the conclusion shapes: `r_derives g t` reads
//   "t is one of the triples this row derives from g".
// * A "false" conclusion (the clash rows: eq-diff1, prp-irp, prp-asyp,
//   prp-pdw, prp-npa1, prp-npa2, prp-adp) becomes a `*_clash : graph
//   -> prop` — the row derives no triple; it convicts the graph.
// * LIST[...] premises (prp-spo2, prp-key, prp-adp) use
//   `owl_list_denotes` below: the rdf:first/rdf:rest chain from a head
//   node to rdf:nil, transcribed structurally.
//
// -------------------------------------------------------------------
// GENERALIZED-RDF DELTAS (same family as RDFS Spec deltas D5-D9)
// -------------------------------------------------------------------
// The tables are stated over generalized RDF; this tree's
// `RDF.Term.subject` is IRI-or-bnode only. Wherever a table variable
// moves from object position (any term) to SUBJECT position in a
// conclusion or later premise, the row carries an explicit
// subject-eligibility premise (`subj_term s == ...` for a bound subject s),
// exactly as RDFS.Spec's rdfs3 does. Each such premise restricts the
// row to the triples this tree's term algebra admits — the shipping
// engine's own restriction, stated rather than hidden. Affected rows
// are marked "delta GR" at the rule.
//
// Predicate positions narrow further: `triple.p : wf_iri`, so a table
// variable used AS a predicate ranges over IRIs only ("delta GP").
//
// -------------------------------------------------------------------
// LEDGER (families -> landing status)
// -------------------------------------------------------------------
//   Table 4  eq-*    THIS FILE (eq-ref eq-sym eq-trans eq-rep-s
//                    eq-rep-p eq-rep-o eq-diff1; eq-diff2/eq-diff3
//                    [AllDifferent] deferred with the list machinery
//                    they share with prp-adp)
//   Table 4  prp-*   THIS FILE (prp-dom prp-rng prp-fp prp-ifp
//                    prp-irp prp-symp prp-asyp prp-trp prp-spo1
//                    prp-spo2 prp-eqp1 prp-eqp2 prp-pdw prp-inv1
//                    prp-inv2 prp-key prp-npa1 prp-npa2; prp-adp
//                    deferred alongside eq-diff2/3; prp-ap is an
//                    axiomatic-triple table, not a rule)
//   Table 5  cls-*   next landing
//   Table 6  cax-*   next landing
//   Table 7  dt-*    later landing
//   Table 8  scm-*   later landing
//   engine extensions (comp-* witnesses, dt-rng-intersect,
//                    chain<->transitive bridges, ...): final landing,
//                    each stated WITH its sound-extension obligation
// ===================================================================

open FStar.List.Tot
open RDF.Term
open RDF.Triple
open RDF.Entailment.Simple.Spec

// -------------------------------------------------------------------
// Vocabulary, spelled locally (see banner). One constant per IRI this
// file's rules mention; nothing imported from engine modules.
// -------------------------------------------------------------------

let o_rdf_type : wf_iri =
  assert_norm (is_iri "http://www.w3.org/1999/02/22-rdf-syntax-ns#type");
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#type"
let o_rdf_first : wf_iri =
  assert_norm (is_iri "http://www.w3.org/1999/02/22-rdf-syntax-ns#first");
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#first"
let o_rdf_rest : wf_iri =
  assert_norm (is_iri "http://www.w3.org/1999/02/22-rdf-syntax-ns#rest");
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#rest"
let o_rdf_nil : wf_iri =
  assert_norm (is_iri "http://www.w3.org/1999/02/22-rdf-syntax-ns#nil");
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#nil"
let o_rdfs_domain : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2000/01/rdf-schema#domain");
  "http://www.w3.org/2000/01/rdf-schema#domain"
let o_rdfs_range : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2000/01/rdf-schema#range");
  "http://www.w3.org/2000/01/rdf-schema#range"
let o_rdfs_subPropertyOf : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2000/01/rdf-schema#subPropertyOf");
  "http://www.w3.org/2000/01/rdf-schema#subPropertyOf"
let o_owl_sameAs : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#sameAs");
  "http://www.w3.org/2002/07/owl#sameAs"
let o_owl_differentFrom : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#differentFrom");
  "http://www.w3.org/2002/07/owl#differentFrom"
let o_owl_FunctionalProperty : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#FunctionalProperty");
  "http://www.w3.org/2002/07/owl#FunctionalProperty"
let o_owl_InverseFunctionalProperty : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#InverseFunctionalProperty");
  "http://www.w3.org/2002/07/owl#InverseFunctionalProperty"
let o_owl_IrreflexiveProperty : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#IrreflexiveProperty");
  "http://www.w3.org/2002/07/owl#IrreflexiveProperty"
let o_owl_SymmetricProperty : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#SymmetricProperty");
  "http://www.w3.org/2002/07/owl#SymmetricProperty"
let o_owl_AsymmetricProperty : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#AsymmetricProperty");
  "http://www.w3.org/2002/07/owl#AsymmetricProperty"
let o_owl_TransitiveProperty : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#TransitiveProperty");
  "http://www.w3.org/2002/07/owl#TransitiveProperty"
let o_owl_propertyChainAxiom : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#propertyChainAxiom");
  "http://www.w3.org/2002/07/owl#propertyChainAxiom"
let o_owl_equivalentProperty : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#equivalentProperty");
  "http://www.w3.org/2002/07/owl#equivalentProperty"
let o_owl_propertyDisjointWith : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#propertyDisjointWith");
  "http://www.w3.org/2002/07/owl#propertyDisjointWith"
let o_owl_inverseOf : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#inverseOf");
  "http://www.w3.org/2002/07/owl#inverseOf"
let o_owl_hasKey : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#hasKey");
  "http://www.w3.org/2002/07/owl#hasKey"
let o_owl_sourceIndividual : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#sourceIndividual");
  "http://www.w3.org/2002/07/owl#sourceIndividual"
let o_owl_assertionProperty : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#assertionProperty");
  "http://www.w3.org/2002/07/owl#assertionProperty"
let o_owl_targetIndividual : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#targetIndividual");
  "http://www.w3.org/2002/07/owl#targetIndividual"
let o_owl_targetValue : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#targetValue");
  "http://www.w3.org/2002/07/owl#targetValue"
let o_owl_NegativePropertyAssertion : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#NegativePropertyAssertion");
  "http://www.w3.org/2002/07/owl#NegativePropertyAssertion"

// -------------------------------------------------------------------
// LIST[...] premises. `owl_list_denotes g head elems` transcribes the
// table's "T(?x, rdf:first, ?e1) T(?x, rdf:rest, ?z1) ..." chain: the
// head term denotes exactly the sequence `elems` through
// rdf:first/rdf:rest links ending at rdf:nil. Structural recursion on
// `elems`; a cyclic or rdf:nil-less chain denotes nothing.
// -------------------------------------------------------------------
let rec owl_list_denotes (g : list triple) (head : rdf_term)
                         (elems : list rdf_term)
  : Tot prop (decreases elems) =
  match elems with
  | [] -> head == T_IRI o_rdf_nil
  | e :: rest ->
    exists (node : subject) (tail : rdf_term).
      subj_term node == head /\
      memP ({ s = node; p = o_rdf_first; o = e } <: triple) g /\
      memP ({ s = node; p = o_rdf_rest; o = tail } <: triple) g /\
      owl_list_denotes g tail rest

(** ================================================================= **)
(** Table 4, family 1: The Semantics of Equality                      **)
(** ================================================================= **)

// -------------------------------------------------------------------
// eq-ref, Table 4, verbatim:
//   "eq-ref | T(?s, ?p, ?o) |
//      T(?s, owl:sameAs, ?s)  T(?p, owl:sameAs, ?p)
//      T(?o, owl:sameAs, ?o)"
// Three conclusion triples; `t` is any one of them (see banner).
// Delta GR: ?o as a conclusion SUBJECT needs subject-eligibility;
// delta GP: ?p is an IRI by this tree's triple type.
// -------------------------------------------------------------------
let eq_ref_derives (g : list triple) (t : triple) : prop =
  exists (u : triple).
    memP u g /\
    (t == ({ s = u.s; p = o_owl_sameAs; o = subj_term u.s } <: triple) \/
     t == ({ s = S_IRI u.p; p = o_owl_sameAs; o = T_IRI u.p } <: triple) \/
     (exists (os : subject).
        subj_term os == u.o /\
        t == ({ s = os; p = o_owl_sameAs; o = u.o } <: triple)))

// -------------------------------------------------------------------
// eq-sym, Table 4, verbatim:
//   "eq-sym | T(?x, owl:sameAs, ?y) | T(?y, owl:sameAs, ?x)"
// Delta GR on ?y (object -> subject).
// -------------------------------------------------------------------
let eq_sym_derives (g : list triple) (t : triple) : prop =
  exists (u : triple) (ys : subject).
    memP u g /\ u.p == o_owl_sameAs /\
    subj_term ys == u.o /\
    t == ({ s = ys; p = o_owl_sameAs; o = subj_term u.s } <: triple)

// -------------------------------------------------------------------
// eq-trans, Table 4, verbatim:
//   "eq-trans | T(?x, owl:sameAs, ?y)  T(?y, owl:sameAs, ?z) |
//               T(?x, owl:sameAs, ?z)"
// The shared ?y appears as u1's object and u2's subject; the join is
// `subj_term u2.s == u1.o`.
// -------------------------------------------------------------------
let eq_trans_derives (g : list triple) (t : triple) : prop =
  exists (u1 u2 : triple).
    memP u1 g /\ u1.p == o_owl_sameAs /\
    memP u2 g /\ u2.p == o_owl_sameAs /\
    subj_term u2.s == u1.o /\
    t == ({ s = u1.s; p = o_owl_sameAs; o = u2.o } <: triple)

// -------------------------------------------------------------------
// eq-rep-s, Table 4, verbatim:
//   "eq-rep-s | T(?s, owl:sameAs, ?s')  T(?s, ?p, ?o) |
//               T(?s', ?p, ?o)"
// Delta GR on ?s' (object of the sameAs premise -> subject).
// -------------------------------------------------------------------
let eq_rep_s_derives (g : list triple) (t : triple) : prop =
  exists (eq u : triple) (s' : subject).
    memP eq g /\ eq.p == o_owl_sameAs /\
    memP u g /\ u.s == eq.s /\
    subj_term s' == eq.o /\
    t == ({ s = s'; p = u.p; o = u.o } <: triple)

// -------------------------------------------------------------------
// eq-rep-p, Table 4, verbatim:
//   "eq-rep-p | T(?p, owl:sameAs, ?p')  T(?s, ?p, ?o) |
//               T(?s, ?p', ?o)"
// Delta GP twice over: both ?p and ?p' occupy predicate position, so
// both are IRIs here; the sameAs premise's subject is S_IRI ?p and its
// object T_IRI ?p'.
// -------------------------------------------------------------------
let eq_rep_p_derives (g : list triple) (t : triple) : prop =
  exists (eq u : triple) (p' : wf_iri).
    memP eq g /\ eq.p == o_owl_sameAs /\
    eq.s == S_IRI u.p /\ eq.o == T_IRI p' /\
    memP u g /\
    t == ({ s = u.s; p = p'; o = u.o } <: triple)

// -------------------------------------------------------------------
// eq-rep-o, Table 4, verbatim:
//   "eq-rep-o | T(?o, owl:sameAs, ?o')  T(?s, ?p, ?o) |
//               T(?s, ?p, ?o')"
// The sameAs premise's SUBJECT is the data triple's OBJECT (join via
// subj_term); no new subject position opens, so no GR delta.
// -------------------------------------------------------------------
let eq_rep_o_derives (g : list triple) (t : triple) : prop =
  exists (eq u : triple).
    memP eq g /\ eq.p == o_owl_sameAs /\
    memP u g /\ subj_term eq.s == u.o /\
    t == ({ s = u.s; p = u.p; o = eq.o } <: triple)

// -------------------------------------------------------------------
// eq-diff1, Table 4, verbatim (a CLASH row):
//   "eq-diff1 | T(?x, owl:sameAs, ?y)  T(?x, owl:differentFrom, ?y) |
//               false"
// -------------------------------------------------------------------
let eq_diff1_clash (g : list triple) : prop =
  exists (u1 u2 : triple).
    memP u1 g /\ u1.p == o_owl_sameAs /\
    memP u2 g /\ u2.p == o_owl_differentFrom /\
    u1.s == u2.s /\ u1.o == u2.o

// eq-diff2 / eq-diff3 (owl:AllDifferent over LIST[...]): deferred to
// the AllDifferent landing, together with prp-adp — see the ledger.

(** ================================================================= **)
(** Table 4, family 2: The Semantics of Axioms about Properties       **)
(** ================================================================= **)

// -------------------------------------------------------------------
// prp-dom, Table 4, verbatim:
//   "prp-dom | T(?p, rdfs:domain, ?c)  T(?x, ?p, ?y) |
//              T(?x, rdf:type, ?c)"
// Identical content to RDFS Spec's rdfs2_derives — restated in this
// table's own row name so the OWL-RL ledger is complete in one place;
// the refinement layer may connect the two rather than prove twice.
// -------------------------------------------------------------------
let prp_dom_derives (g : list triple) (t : triple) : prop =
  exists (decl u : triple) (p : wf_iri).
    memP decl g /\ decl.p == o_rdfs_domain /\ decl.s == S_IRI p /\
    memP u g /\ u.p == p /\
    t == ({ s = u.s; p = o_rdf_type; o = decl.o } <: triple)

// -------------------------------------------------------------------
// prp-rng, Table 4, verbatim:
//   "prp-rng | T(?p, rdfs:range, ?c)  T(?x, ?p, ?y) |
//              T(?y, rdf:type, ?c)"
// Delta GR on ?y. The conclusion types the premise's OBJECT — the row
// at the centre of issue #345, where the accusation was that the
// engine types the subject. rdfs_rule_range_sound
// (OWL.Semantics.Soundness) is the truth-preservation half; this row
// is the syntax the refinement layer licenses emissions against.
// -------------------------------------------------------------------
let prp_rng_derives (g : list triple) (t : triple) : prop =
  exists (decl u : triple) (p : wf_iri) (ys : subject).
    memP decl g /\ decl.p == o_rdfs_range /\ decl.s == S_IRI p /\
    memP u g /\ u.p == p /\
    subj_term ys == u.o /\
    t == ({ s = ys; p = o_rdf_type; o = decl.o } <: triple)

// -------------------------------------------------------------------
// prp-fp, Table 4, verbatim:
//   "prp-fp | T(?p, rdf:type, owl:FunctionalProperty)
//             T(?x, ?p, ?y1)  T(?x, ?p, ?y2) |
//             T(?y1, owl:sameAs, ?y2)"
// Delta GR on ?y1 (object -> conclusion subject).
// -------------------------------------------------------------------
let prp_fp_derives (g : list triple) (t : triple) : prop =
  exists (decl u1 u2 : triple) (p : wf_iri) (y1s : subject).
    memP decl g /\ decl.p == o_rdf_type /\
    decl.s == S_IRI p /\ decl.o == T_IRI o_owl_FunctionalProperty /\
    memP u1 g /\ u1.p == p /\
    memP u2 g /\ u2.p == p /\ u2.s == u1.s /\
    subj_term y1s == u1.o /\
    t == ({ s = y1s; p = o_owl_sameAs; o = u2.o } <: triple)

// -------------------------------------------------------------------
// prp-ifp, Table 4, verbatim:
//   "prp-ifp | T(?p, rdf:type, owl:InverseFunctionalProperty)
//              T(?x1, ?p, ?y)  T(?x2, ?p, ?y) |
//              T(?x1, owl:sameAs, ?x2)"
// -------------------------------------------------------------------
let prp_ifp_derives (g : list triple) (t : triple) : prop =
  exists (decl u1 u2 : triple) (p : wf_iri).
    memP decl g /\ decl.p == o_rdf_type /\
    decl.s == S_IRI p /\ decl.o == T_IRI o_owl_InverseFunctionalProperty /\
    memP u1 g /\ u1.p == p /\
    memP u2 g /\ u2.p == p /\ u2.o == u1.o /\
    t == ({ s = u1.s; p = o_owl_sameAs; o = subj_term u2.s } <: triple)

// -------------------------------------------------------------------
// prp-irp, Table 4, verbatim (a CLASH row):
//   "prp-irp | T(?p, rdf:type, owl:IrreflexiveProperty)
//              T(?x, ?p, ?x) | false"
// "T(?x, ?p, ?x)" — the subject and object are the SAME node; stated
// via subj_term.
// -------------------------------------------------------------------
let prp_irp_clash (g : list triple) : prop =
  exists (decl u : triple) (p : wf_iri).
    memP decl g /\ decl.p == o_rdf_type /\
    decl.s == S_IRI p /\ decl.o == T_IRI o_owl_IrreflexiveProperty /\
    memP u g /\ u.p == p /\ u.o == subj_term u.s

// -------------------------------------------------------------------
// prp-symp, Table 4, verbatim:
//   "prp-symp | T(?p, rdf:type, owl:SymmetricProperty)
//               T(?x, ?p, ?y) | T(?y, ?p, ?x)"
// Delta GR on ?y.
// -------------------------------------------------------------------
let prp_symp_derives (g : list triple) (t : triple) : prop =
  exists (decl u : triple) (p : wf_iri) (ys : subject).
    memP decl g /\ decl.p == o_rdf_type /\
    decl.s == S_IRI p /\ decl.o == T_IRI o_owl_SymmetricProperty /\
    memP u g /\ u.p == p /\
    subj_term ys == u.o /\
    t == ({ s = ys; p = p; o = subj_term u.s } <: triple)

// -------------------------------------------------------------------
// prp-asyp, Table 4, verbatim (a CLASH row):
//   "prp-asyp | T(?p, rdf:type, owl:AsymmetricProperty)
//               T(?x, ?p, ?y)  T(?y, ?p, ?x) | false"
// -------------------------------------------------------------------
let prp_asyp_clash (g : list triple) : prop =
  exists (decl u1 u2 : triple) (p : wf_iri).
    memP decl g /\ decl.p == o_rdf_type /\
    decl.s == S_IRI p /\ decl.o == T_IRI o_owl_AsymmetricProperty /\
    memP u1 g /\ u1.p == p /\
    memP u2 g /\ u2.p == p /\
    subj_term u2.s == u1.o /\ u2.o == subj_term u1.s

// -------------------------------------------------------------------
// prp-trp, Table 4, verbatim:
//   "prp-trp | T(?p, rdf:type, owl:TransitiveProperty)
//              T(?x, ?p, ?y)  T(?y, ?p, ?z) | T(?x, ?p, ?z)"
// -------------------------------------------------------------------
let prp_trp_derives (g : list triple) (t : triple) : prop =
  exists (decl u1 u2 : triple) (p : wf_iri).
    memP decl g /\ decl.p == o_rdf_type /\
    decl.s == S_IRI p /\ decl.o == T_IRI o_owl_TransitiveProperty /\
    memP u1 g /\ u1.p == p /\
    memP u2 g /\ u2.p == p /\ subj_term u2.s == u1.o /\
    t == ({ s = u1.s; p = p; o = u2.o } <: triple)

// -------------------------------------------------------------------
// prp-spo1, Table 4, verbatim:
//   "prp-spo1 | T(?p1, rdfs:subPropertyOf, ?p2)  T(?x, ?p1, ?y) |
//               T(?x, ?p2, ?y)"
// Delta GP on ?p2 (used as the conclusion's predicate).
// -------------------------------------------------------------------
let prp_spo1_derives (g : list triple) (t : triple) : prop =
  exists (decl u : triple) (p1 p2 : wf_iri).
    memP decl g /\ decl.p == o_rdfs_subPropertyOf /\
    decl.s == S_IRI p1 /\ decl.o == T_IRI p2 /\
    memP u g /\ u.p == p1 /\
    t == ({ s = u.s; p = p2; o = u.o } <: triple)

// -------------------------------------------------------------------
// prp-spo2, Table 4, verbatim:
//   "prp-spo2 | T(?p, owl:propertyChainAxiom, ?x)
//               LIST[?x, ?p1, ..., ?pn]
//               T(?u1, ?p1, ?u2)  T(?u2, ?p2, ?u3) ...
//               T(?un, ?pn, ?un+1) |
//               T(?u1, ?p, ?un+1)"
// The chain of data triples is `chain_holds` below: consecutive links
// share their meeting node (object of one = subject of the next, via
// subj_term), predicates drawn in order from the LIST[...] sequence.
// Delta GP: every chain element occupies predicate position.
// -------------------------------------------------------------------
let rec chain_holds (g : list triple) (start : subject)
                    (preds : list wf_iri) (finish : rdf_term)
  : Tot prop (decreases preds) =
  match preds with
  | [] -> subj_term start == finish
  | p :: rest ->
    exists (u : triple).
      memP u g /\ u.s == start /\ u.p == p /\
      (match rest with
       | [] -> u.o == finish
       | _ ->
         exists (mid : subject).
           subj_term mid == u.o /\
           chain_holds g mid rest finish)

let prp_spo2_derives (g : list triple) (t : triple) : prop =
  exists (decl : triple) (p : wf_iri)
         (pred_terms : list rdf_term) (preds : list wf_iri)
         (x1 : subject) (xn : rdf_term).
    memP decl g /\ decl.p == o_owl_propertyChainAxiom /\
    decl.s == S_IRI p /\
    owl_list_denotes g decl.o pred_terms /\
    Cons? preds /\
    pred_terms == List.Tot.map (fun (q : wf_iri) -> T_IRI q) preds /\
    chain_holds g x1 preds xn /\
    t == ({ s = x1; p = p; o = xn } <: triple)

// -------------------------------------------------------------------
// prp-eqp1 / prp-eqp2, Table 4, verbatim:
//   "prp-eqp1 | T(?p1, owl:equivalentProperty, ?p2)  T(?x, ?p1, ?y) |
//               T(?x, ?p2, ?y)"
//   "prp-eqp2 | T(?p1, owl:equivalentProperty, ?p2)  T(?x, ?p2, ?y) |
//               T(?x, ?p1, ?y)"
// -------------------------------------------------------------------
let prp_eqp1_derives (g : list triple) (t : triple) : prop =
  exists (decl u : triple) (p1 p2 : wf_iri).
    memP decl g /\ decl.p == o_owl_equivalentProperty /\
    decl.s == S_IRI p1 /\ decl.o == T_IRI p2 /\
    memP u g /\ u.p == p1 /\
    t == ({ s = u.s; p = p2; o = u.o } <: triple)

let prp_eqp2_derives (g : list triple) (t : triple) : prop =
  exists (decl u : triple) (p1 p2 : wf_iri).
    memP decl g /\ decl.p == o_owl_equivalentProperty /\
    decl.s == S_IRI p1 /\ decl.o == T_IRI p2 /\
    memP u g /\ u.p == p2 /\
    t == ({ s = u.s; p = p1; o = u.o } <: triple)

// -------------------------------------------------------------------
// prp-pdw, Table 4, verbatim (a CLASH row):
//   "prp-pdw | T(?p1, owl:propertyDisjointWith, ?p2)
//              T(?x, ?p1, ?y)  T(?x, ?p2, ?y) | false"
// -------------------------------------------------------------------
let prp_pdw_clash (g : list triple) : prop =
  exists (decl u1 u2 : triple) (p1 p2 : wf_iri).
    memP decl g /\ decl.p == o_owl_propertyDisjointWith /\
    decl.s == S_IRI p1 /\ decl.o == T_IRI p2 /\
    memP u1 g /\ u1.p == p1 /\
    memP u2 g /\ u2.p == p2 /\
    u2.s == u1.s /\ u2.o == u1.o

// -------------------------------------------------------------------
// prp-inv1 / prp-inv2, Table 4, verbatim:
//   "prp-inv1 | T(?p1, owl:inverseOf, ?p2)  T(?x, ?p1, ?y) |
//               T(?y, ?p2, ?x)"
//   "prp-inv2 | T(?p1, owl:inverseOf, ?p2)  T(?x, ?p2, ?y) |
//               T(?y, ?p1, ?x)"
// Delta GR on ?y in both.
// -------------------------------------------------------------------
let prp_inv1_derives (g : list triple) (t : triple) : prop =
  exists (decl u : triple) (p1 p2 : wf_iri) (ys : subject).
    memP decl g /\ decl.p == o_owl_inverseOf /\
    decl.s == S_IRI p1 /\ decl.o == T_IRI p2 /\
    memP u g /\ u.p == p1 /\
    subj_term ys == u.o /\
    t == ({ s = ys; p = p2; o = subj_term u.s } <: triple)

let prp_inv2_derives (g : list triple) (t : triple) : prop =
  exists (decl u : triple) (p1 p2 : wf_iri) (ys : subject).
    memP decl g /\ decl.p == o_owl_inverseOf /\
    decl.s == S_IRI p1 /\ decl.o == T_IRI p2 /\
    memP u g /\ u.p == p2 /\
    subj_term ys == u.o /\
    t == ({ s = ys; p = p1; o = subj_term u.s } <: triple)

// -------------------------------------------------------------------
// prp-key, Table 4, verbatim:
//   "prp-key | T(?c, owl:hasKey, ?u)  LIST[?u, ?p1, ..., ?pn]
//              T(?x, rdf:type, ?c)  T(?x, ?p1, ?z1) ... T(?x, ?pn, ?zn)
//              T(?y, rdf:type, ?c)  T(?y, ?p1, ?z1) ... T(?y, ?pn, ?zn) |
//              T(?x, owl:sameAs, ?y)"
// `shares_key_values` states the paired premises: for each key
// property in order, the two individuals carry SOME shared value.
// -------------------------------------------------------------------
let rec shares_key_values (g : list triple) (x y : subject)
                          (preds : list wf_iri)
  : Tot prop (decreases preds) =
  match preds with
  | [] -> True
  | p :: rest ->
    (exists (ux uy : triple).
       memP ux g /\ ux.s == x /\ ux.p == p /\
       memP uy g /\ uy.s == y /\ uy.p == p /\
       ux.o == uy.o) /\
    shares_key_values g x y rest

let prp_key_derives (g : list triple) (t : triple) : prop =
  exists (decl tx ty : triple)
         (pred_terms : list rdf_term) (preds : list wf_iri).
    memP decl g /\ decl.p == o_owl_hasKey /\
    owl_list_denotes g decl.o pred_terms /\
    Cons? preds /\
    pred_terms == List.Tot.map (fun (q : wf_iri) -> T_IRI q) preds /\
    memP tx g /\ tx.p == o_rdf_type /\ tx.o == subj_term decl.s /\
    memP ty g /\ ty.p == o_rdf_type /\ ty.o == subj_term decl.s /\
    shares_key_values g tx.s ty.s preds /\
    t == ({ s = tx.s; p = o_owl_sameAs; o = subj_term ty.s } <: triple)

// -------------------------------------------------------------------
// prp-npa1 / prp-npa2, Table 4, verbatim (CLASH rows):
//   "prp-npa1 | T(?i, owl:sourceIndividual, ?x)
//               T(?i, owl:assertionProperty, ?p)
//               T(?i, owl:targetIndividual, ?y)
//               T(?x, ?p, ?y) | false"
//   "prp-npa2 | T(?i, owl:sourceIndividual, ?x)
//               T(?i, owl:assertionProperty, ?p)
//               T(?i, owl:targetValue, ?lt)
//               T(?x, ?p, ?lt) | false"
// -------------------------------------------------------------------
let prp_npa1_clash (g : list triple) : prop =
  exists (src ap ti u : triple) (p : wf_iri) (xs : subject).
    memP src g /\ src.p == o_owl_sourceIndividual /\
    memP ap  g /\ ap.p  == o_owl_assertionProperty /\ ap.s == src.s /\
    ap.o == T_IRI p /\
    memP ti  g /\ ti.p  == o_owl_targetIndividual /\ ti.s == src.s /\
    memP u g /\ u.p == p /\
    subj_term xs == src.o /\ u.s == xs /\
    u.o == ti.o

let prp_npa2_clash (g : list triple) : prop =
  exists (src ap tv u : triple) (p : wf_iri) (xs : subject).
    memP src g /\ src.p == o_owl_sourceIndividual /\
    memP ap  g /\ ap.p  == o_owl_assertionProperty /\ ap.s == src.s /\
    ap.o == T_IRI p /\
    memP tv  g /\ tv.p  == o_owl_targetValue /\ tv.s == src.s /\
    memP u g /\ u.p == p /\
    subj_term xs == src.o /\ u.s == xs /\
    u.o == tv.o

// -------------------------------------------------------------------
// Table 4, whole-family derivability: `t` is derivable from `g` by
// SOME row of the two families above. The refinement layer's target:
// every triple the corresponding engine rules emit is licensed here.
// -------------------------------------------------------------------
let table4_derives (g : list triple) (t : triple) : prop =
  eq_ref_derives g t \/ eq_sym_derives g t \/ eq_trans_derives g t \/
  eq_rep_s_derives g t \/ eq_rep_p_derives g t \/ eq_rep_o_derives g t \/
  prp_dom_derives g t \/ prp_rng_derives g t \/
  prp_fp_derives g t \/ prp_ifp_derives g t \/
  prp_symp_derives g t \/ prp_trp_derives g t \/
  prp_spo1_derives g t \/ prp_spo2_derives g t \/
  prp_eqp1_derives g t \/ prp_eqp2_derives g t \/
  prp_inv1_derives g t \/ prp_inv2_derives g t \/
  prp_key_derives g t

let table4_clashes (g : list triple) : prop =
  eq_diff1_clash g \/ prp_irp_clash g \/ prp_asyp_clash g \/
  prp_pdw_clash g \/ prp_npa1_clash g \/ prp_npa2_clash g
