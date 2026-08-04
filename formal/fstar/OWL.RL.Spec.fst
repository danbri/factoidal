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
//   Table 5  cls-*   THIS FILE, landing 2 (cls-thing cls-nothing1
//                    cls-nothing2 cls-int1 cls-int2 cls-uni cls-com
//                    cls-svf1 cls-svf2 cls-avf cls-hv1 cls-hv2
//                    cls-maxc1 cls-maxc2 cls-maxqc1 cls-maxqc2
//                    cls-maxqc3 cls-maxqc4 cls-oo)
//   Table 6  cax-*   THIS FILE, landing 2 (cax-sco cax-eqc1 cax-eqc2
//                    cax-dw cax-adc)
//   Table 7  dt-*    THIS FILE, landing 3 (dt-type1 dt-type2 dt-eq;
//                    CLASH rows dt-diff dt-not-type; all PARAMETRIC
//                    over the datatype map -- see Table 7's banner)
//   Table 8  scm-*   THIS FILE, landing 3 (scm-cls scm-sco scm-eqc1
//                    scm-eqc2 scm-op scm-dp scm-spo scm-eqp1 scm-eqp2
//                    scm-dom1 scm-dom2 scm-rng1 scm-rng2 scm-hv
//                    scm-svf1 scm-svf2 scm-avf1 scm-avf2 scm-int
//                    scm-uni)
//   deferred rows    landed in landing 3: eq-diff2 eq-diff3 prp-adp
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


(** ================================================================= **)
(** Landing 2 vocabulary                                              **)
(** ================================================================= **)

let o_owl_Class : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#Class");
  "http://www.w3.org/2002/07/owl#Class"
let o_owl_Thing : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#Thing");
  "http://www.w3.org/2002/07/owl#Thing"
let o_owl_Nothing : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#Nothing");
  "http://www.w3.org/2002/07/owl#Nothing"
let o_owl_intersectionOf : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#intersectionOf");
  "http://www.w3.org/2002/07/owl#intersectionOf"
let o_owl_unionOf : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#unionOf");
  "http://www.w3.org/2002/07/owl#unionOf"
let o_owl_complementOf : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#complementOf");
  "http://www.w3.org/2002/07/owl#complementOf"
let o_owl_someValuesFrom : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#someValuesFrom");
  "http://www.w3.org/2002/07/owl#someValuesFrom"
let o_owl_allValuesFrom : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#allValuesFrom");
  "http://www.w3.org/2002/07/owl#allValuesFrom"
let o_owl_onProperty : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#onProperty");
  "http://www.w3.org/2002/07/owl#onProperty"
let o_owl_hasValue : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#hasValue");
  "http://www.w3.org/2002/07/owl#hasValue"
let o_owl_maxCardinality : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#maxCardinality");
  "http://www.w3.org/2002/07/owl#maxCardinality"
let o_owl_maxQualifiedCardinality : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#maxQualifiedCardinality");
  "http://www.w3.org/2002/07/owl#maxQualifiedCardinality"
let o_owl_onClass : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#onClass");
  "http://www.w3.org/2002/07/owl#onClass"
let o_owl_oneOf : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#oneOf");
  "http://www.w3.org/2002/07/owl#oneOf"
let o_rdfs_subClassOf : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2000/01/rdf-schema#subClassOf");
  "http://www.w3.org/2000/01/rdf-schema#subClassOf"
let o_owl_equivalentClass : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#equivalentClass");
  "http://www.w3.org/2002/07/owl#equivalentClass"
let o_owl_disjointWith : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#disjointWith");
  "http://www.w3.org/2002/07/owl#disjointWith"
let o_owl_AllDisjointClasses : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#AllDisjointClasses");
  "http://www.w3.org/2002/07/owl#AllDisjointClasses"
let o_owl_members : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#members");
  "http://www.w3.org/2002/07/owl#members"
let o_xsd_nonNegativeInteger : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2001/XMLSchema#nonNegativeInteger");
  "http://www.w3.org/2001/XMLSchema#nonNegativeInteger"

// The literals the cardinality rows quote. The table writes
// "0"^^xsd:nonNegativeInteger / "1"^^xsd:nonNegativeInteger literally;
// this transcription matches the LEXICAL FORM the table shows.
// ⚠ Delta LIT: a graph writing the same value as "00" or "+1" is not
// matched by these rows as transcribed — the Recommendation's own
// notation is lexical here, and the engine-side question of numeric
// value-space matching belongs to the refinement layer, not the spec.
let lit_nni_0 : literal =
  { lexical_form = "0"; datatype = o_xsd_nonNegativeInteger;
    lang_tag = None; direction = None }
let lit_nni_1 : literal =
  { lexical_form = "1"; datatype = o_xsd_nonNegativeInteger;
    lang_tag = None; direction = None }

// `types_all g y cs`: T(?y, rdf:type, ci) for every ci in cs
// (cls-int1's batched premise).
let rec types_all (g : list triple) (y : subject) (cs : list rdf_term)
  : Tot prop (decreases cs) =
  match cs with
  | [] -> True
  | c :: rest ->
    (exists (u : triple).
       memP u g /\ u == ({ s = y; p = o_rdf_type; o = c } <: triple)) /\
    types_all g y rest

// Two DISTINCT positions of a list (cax-adc / cls-int2's "some member"
// pairs): ci and cj occur at different indices, in either order.
let two_distinct_members (elems : list rdf_term) (ci cj : rdf_term) : prop =
  exists (l1 l2 l3 : list rdf_term).
    elems == l1 @ (ci :: (l2 @ (cj :: l3))) \/
    elems == l1 @ (cj :: (l2 @ (ci :: l3)))

(** ================================================================= **)
(** Table 5: The Semantics of Classes                                 **)
(** ================================================================= **)

// -------------------------------------------------------------------
// cls-thing / cls-nothing1, Table 5, verbatim (premise-free rows):
//   "cls-thing    |  | T(owl:Thing, rdf:type, owl:Class)"
//   "cls-nothing1 |  | T(owl:Nothing, rdf:type, owl:Class)"
// -------------------------------------------------------------------
let cls_thing_derives (g : list triple) (t : triple) : prop =
  t == ({ s = S_IRI o_owl_Thing; p = o_rdf_type; o = T_IRI o_owl_Class } <: triple)

let cls_nothing1_derives (g : list triple) (t : triple) : prop =
  t == ({ s = S_IRI o_owl_Nothing; p = o_rdf_type; o = T_IRI o_owl_Class } <: triple)

// -------------------------------------------------------------------
// cls-nothing2, Table 5, verbatim (a CLASH row):
//   "cls-nothing2 | T(?x, rdf:type, owl:Nothing) | false"
// -------------------------------------------------------------------
let cls_nothing2_clash (g : list triple) : prop =
  exists (u : triple).
    memP u g /\ u.p == o_rdf_type /\ u.o == T_IRI o_owl_Nothing

// -------------------------------------------------------------------
// cls-int1, Table 5, verbatim:
//   "cls-int1 | T(?c, owl:intersectionOf, ?x)  LIST[?x, ?c1, ..., ?cn]
//               T(?y, rdf:type, ?c1) ... T(?y, rdf:type, ?cn) |
//               T(?y, rdf:type, ?c)"
// -------------------------------------------------------------------
let cls_int1_derives (g : list triple) (t : triple) : prop =
  exists (decl : triple) (cs : list rdf_term) (y : subject).
    memP decl g /\ decl.p == o_owl_intersectionOf /\
    owl_list_denotes g decl.o cs /\ Cons? cs /\
    types_all g y cs /\
    t == ({ s = y; p = o_rdf_type; o = subj_term decl.s } <: triple)

// -------------------------------------------------------------------
// cls-int2, Table 5, verbatim:
//   "cls-int2 | T(?c, owl:intersectionOf, ?x)  LIST[?x, ?c1, ..., ?cn]
//               T(?y, rdf:type, ?c) |
//               T(?y, rdf:type, ?c1) ... T(?y, rdf:type, ?cn)"
// `t` is any one of the n conclusions: its class is SOME member.
// -------------------------------------------------------------------
let cls_int2_derives (g : list triple) (t : triple) : prop =
  exists (decl u : triple) (cs : list rdf_term) (ci : rdf_term).
    memP decl g /\ decl.p == o_owl_intersectionOf /\
    owl_list_denotes g decl.o cs /\
    memP u g /\ u.p == o_rdf_type /\ u.o == subj_term decl.s /\
    memP ci cs /\
    t == ({ s = u.s; p = o_rdf_type; o = ci } <: triple)

// -------------------------------------------------------------------
// cls-uni, Table 5, verbatim:
//   "cls-uni | T(?c, owl:unionOf, ?x)  LIST[?x, ?c1, ..., ?cn]
//              T(?y, rdf:type, ?ci)   (for any 1 <= i <= n) |
//              T(?y, rdf:type, ?c)"
// -------------------------------------------------------------------
let cls_uni_derives (g : list triple) (t : triple) : prop =
  exists (decl u : triple) (cs : list rdf_term) (ci : rdf_term).
    memP decl g /\ decl.p == o_owl_unionOf /\
    owl_list_denotes g decl.o cs /\
    memP ci cs /\
    memP u g /\ u.p == o_rdf_type /\ u.o == ci /\
    t == ({ s = u.s; p = o_rdf_type; o = subj_term decl.s } <: triple)

// -------------------------------------------------------------------
// cls-com, Table 5, verbatim (a CLASH row):
//   "cls-com | T(?c1, owl:complementOf, ?c2)
//              T(?x, rdf:type, ?c1)  T(?x, rdf:type, ?c2) | false"
// -------------------------------------------------------------------
let cls_com_clash (g : list triple) : prop =
  exists (decl u1 u2 : triple).
    memP decl g /\ decl.p == o_owl_complementOf /\
    memP u1 g /\ u1.p == o_rdf_type /\ u1.o == subj_term decl.s /\
    memP u2 g /\ u2.p == o_rdf_type /\ u2.o == decl.o /\
    u2.s == u1.s

// -------------------------------------------------------------------
// cls-svf1, Table 5, verbatim:
//   "cls-svf1 | T(?x, owl:someValuesFrom, ?y)  T(?x, owl:onProperty, ?p)
//               T(?u, ?p, ?v)  T(?v, rdf:type, ?y) |
//               T(?u, rdf:type, ?x)"
// The join between the data edge's object ?v and the typing premise's
// subject goes through subj_term, as everywhere.
// -------------------------------------------------------------------
let cls_svf1_derives (g : list triple) (t : triple) : prop =
  exists (svf onp u tv : triple) (p : wf_iri).
    memP svf g /\ svf.p == o_owl_someValuesFrom /\
    memP onp g /\ onp.p == o_owl_onProperty /\ onp.s == svf.s /\
    onp.o == T_IRI p /\
    memP u g /\ u.p == p /\
    memP tv g /\ tv.p == o_rdf_type /\ subj_term tv.s == u.o /\
    tv.o == svf.o /\
    t == ({ s = u.s; p = o_rdf_type; o = subj_term svf.s } <: triple)

// -------------------------------------------------------------------
// cls-svf2, Table 5, verbatim:
//   "cls-svf2 | T(?x, owl:someValuesFrom, owl:Thing)
//               T(?x, owl:onProperty, ?p)  T(?u, ?p, ?v) |
//               T(?u, rdf:type, ?x)"
// -------------------------------------------------------------------
let cls_svf2_derives (g : list triple) (t : triple) : prop =
  exists (svf onp u : triple) (p : wf_iri).
    memP svf g /\ svf.p == o_owl_someValuesFrom /\
    svf.o == T_IRI o_owl_Thing /\
    memP onp g /\ onp.p == o_owl_onProperty /\ onp.s == svf.s /\
    onp.o == T_IRI p /\
    memP u g /\ u.p == p /\
    t == ({ s = u.s; p = o_rdf_type; o = subj_term svf.s } <: triple)

// -------------------------------------------------------------------
// cls-avf, Table 5, verbatim:
//   "cls-avf | T(?x, owl:allValuesFrom, ?y)  T(?x, owl:onProperty, ?p)
//              T(?u, rdf:type, ?x)  T(?u, ?p, ?v) |
//              T(?v, rdf:type, ?y)"
// Delta GR on ?v.
// -------------------------------------------------------------------
let cls_avf_derives (g : list triple) (t : triple) : prop =
  exists (avf onp tu u : triple) (p : wf_iri) (vs : subject).
    memP avf g /\ avf.p == o_owl_allValuesFrom /\
    memP onp g /\ onp.p == o_owl_onProperty /\ onp.s == avf.s /\
    onp.o == T_IRI p /\
    memP tu g /\ tu.p == o_rdf_type /\ tu.o == subj_term avf.s /\
    memP u g /\ u.p == p /\ u.s == tu.s /\
    subj_term vs == u.o /\
    t == ({ s = vs; p = o_rdf_type; o = avf.o } <: triple)

// -------------------------------------------------------------------
// cls-hv1 / cls-hv2, Table 5, verbatim:
//   "cls-hv1 | T(?x, owl:hasValue, ?y)  T(?x, owl:onProperty, ?p)
//              T(?u, rdf:type, ?x) | T(?u, ?p, ?y)"
//   "cls-hv2 | T(?x, owl:hasValue, ?y)  T(?x, owl:onProperty, ?p)
//              T(?u, ?p, ?y) | T(?u, rdf:type, ?x)"
// -------------------------------------------------------------------
let cls_hv1_derives (g : list triple) (t : triple) : prop =
  exists (hv onp tu : triple) (p : wf_iri).
    memP hv g /\ hv.p == o_owl_hasValue /\
    memP onp g /\ onp.p == o_owl_onProperty /\ onp.s == hv.s /\
    onp.o == T_IRI p /\
    memP tu g /\ tu.p == o_rdf_type /\ tu.o == subj_term hv.s /\
    t == ({ s = tu.s; p = p; o = hv.o } <: triple)

let cls_hv2_derives (g : list triple) (t : triple) : prop =
  exists (hv onp u : triple) (p : wf_iri).
    memP hv g /\ hv.p == o_owl_hasValue /\
    memP onp g /\ onp.p == o_owl_onProperty /\ onp.s == hv.s /\
    onp.o == T_IRI p /\
    memP u g /\ u.p == p /\ u.o == hv.o /\
    t == ({ s = u.s; p = o_rdf_type; o = subj_term hv.s } <: triple)

// -------------------------------------------------------------------
// cls-maxc1, Table 5, verbatim (a CLASH row):
//   "cls-maxc1 | T(?x, owl:maxCardinality, "0"^^xsd:nonNegativeInteger)
//                T(?x, owl:onProperty, ?p)
//                T(?u, rdf:type, ?x)  T(?u, ?p, ?y) | false"
// ⚠ Delta LIT applies (see lit_nni_0's banner).
// -------------------------------------------------------------------
let cls_maxc1_clash (g : list triple) : prop =
  exists (mc onp tu u : triple) (p : wf_iri).
    memP mc g /\ mc.p == o_owl_maxCardinality /\
    mc.o == T_Literal lit_nni_0 /\
    memP onp g /\ onp.p == o_owl_onProperty /\ onp.s == mc.s /\
    onp.o == T_IRI p /\
    memP tu g /\ tu.p == o_rdf_type /\ tu.o == subj_term mc.s /\
    memP u g /\ u.p == p /\ u.s == tu.s

// -------------------------------------------------------------------
// cls-maxc2, Table 5, verbatim:
//   "cls-maxc2 | T(?x, owl:maxCardinality, "1"^^xsd:nonNegativeInteger)
//                T(?x, owl:onProperty, ?p)  T(?u, rdf:type, ?x)
//                T(?u, ?p, ?y1)  T(?u, ?p, ?y2) |
//                T(?y1, owl:sameAs, ?y2)"
// Delta GR on ?y1; ⚠ Delta LIT.
// -------------------------------------------------------------------
let cls_maxc2_derives (g : list triple) (t : triple) : prop =
  exists (mc onp tu u1 u2 : triple) (p : wf_iri) (y1s : subject).
    memP mc g /\ mc.p == o_owl_maxCardinality /\
    mc.o == T_Literal lit_nni_1 /\
    memP onp g /\ onp.p == o_owl_onProperty /\ onp.s == mc.s /\
    onp.o == T_IRI p /\
    memP tu g /\ tu.p == o_rdf_type /\ tu.o == subj_term mc.s /\
    memP u1 g /\ u1.p == p /\ u1.s == tu.s /\
    memP u2 g /\ u2.p == p /\ u2.s == tu.s /\
    subj_term y1s == u1.o /\
    t == ({ s = y1s; p = o_owl_sameAs; o = u2.o } <: triple)

// -------------------------------------------------------------------
// cls-maxqc1 / cls-maxqc2, Table 5, verbatim (CLASH rows):
//   "cls-maxqc1 | T(?x, owl:maxQualifiedCardinality,
//                    "0"^^xsd:nonNegativeInteger)
//                 T(?x, owl:onProperty, ?p)  T(?x, owl:onClass, ?c)
//                 T(?u, rdf:type, ?x)  T(?u, ?p, ?y)
//                 T(?y, rdf:type, ?c) | false"
//   "cls-maxqc2 | ... T(?x, owl:onClass, owl:Thing)
//                 T(?u, rdf:type, ?x)  T(?u, ?p, ?y) | false"
// -------------------------------------------------------------------
let cls_maxqc1_clash (g : list triple) : prop =
  exists (mqc onp onc tu u ty : triple) (p : wf_iri).
    memP mqc g /\ mqc.p == o_owl_maxQualifiedCardinality /\
    mqc.o == T_Literal lit_nni_0 /\
    memP onp g /\ onp.p == o_owl_onProperty /\ onp.s == mqc.s /\
    onp.o == T_IRI p /\
    memP onc g /\ onc.p == o_owl_onClass /\ onc.s == mqc.s /\
    memP tu g /\ tu.p == o_rdf_type /\ tu.o == subj_term mqc.s /\
    memP u g /\ u.p == p /\ u.s == tu.s /\
    memP ty g /\ ty.p == o_rdf_type /\ subj_term ty.s == u.o /\
    ty.o == onc.o

let cls_maxqc2_clash (g : list triple) : prop =
  exists (mqc onp onc tu u : triple) (p : wf_iri).
    memP mqc g /\ mqc.p == o_owl_maxQualifiedCardinality /\
    mqc.o == T_Literal lit_nni_0 /\
    memP onp g /\ onp.p == o_owl_onProperty /\ onp.s == mqc.s /\
    onp.o == T_IRI p /\
    memP onc g /\ onc.p == o_owl_onClass /\ onc.s == mqc.s /\
    onc.o == T_IRI o_owl_Thing /\
    memP tu g /\ tu.p == o_rdf_type /\ tu.o == subj_term mqc.s /\
    memP u g /\ u.p == p /\ u.s == tu.s

// -------------------------------------------------------------------
// cls-maxqc3 / cls-maxqc4, Table 5, verbatim:
//   "cls-maxqc3 | T(?x, owl:maxQualifiedCardinality,
//                    "1"^^xsd:nonNegativeInteger)
//                 T(?x, owl:onProperty, ?p)  T(?x, owl:onClass, ?c)
//                 T(?u, rdf:type, ?x)
//                 T(?u, ?p, ?y1)  T(?y1, rdf:type, ?c)
//                 T(?u, ?p, ?y2)  T(?y2, rdf:type, ?c) |
//                 T(?y1, owl:sameAs, ?y2)"
//   "cls-maxqc4 | ... T(?x, owl:onClass, owl:Thing)
//                 T(?u, ?p, ?y1)  T(?u, ?p, ?y2) |
//                 T(?y1, owl:sameAs, ?y2)"
// Delta GR on ?y1 in both.
// -------------------------------------------------------------------
let cls_maxqc3_derives (g : list triple) (t : triple) : prop =
  exists (mqc onp onc tu u1 ty1 u2 ty2 : triple) (p : wf_iri) (y1s : subject).
    memP mqc g /\ mqc.p == o_owl_maxQualifiedCardinality /\
    mqc.o == T_Literal lit_nni_1 /\
    memP onp g /\ onp.p == o_owl_onProperty /\ onp.s == mqc.s /\
    onp.o == T_IRI p /\
    memP onc g /\ onc.p == o_owl_onClass /\ onc.s == mqc.s /\
    memP tu g /\ tu.p == o_rdf_type /\ tu.o == subj_term mqc.s /\
    memP u1 g /\ u1.p == p /\ u1.s == tu.s /\
    memP ty1 g /\ ty1.p == o_rdf_type /\ subj_term ty1.s == u1.o /\
    ty1.o == onc.o /\
    memP u2 g /\ u2.p == p /\ u2.s == tu.s /\
    memP ty2 g /\ ty2.p == o_rdf_type /\ subj_term ty2.s == u2.o /\
    ty2.o == onc.o /\
    subj_term y1s == u1.o /\
    t == ({ s = y1s; p = o_owl_sameAs; o = u2.o } <: triple)

let cls_maxqc4_derives (g : list triple) (t : triple) : prop =
  exists (mqc onp onc tu u1 u2 : triple) (p : wf_iri) (y1s : subject).
    memP mqc g /\ mqc.p == o_owl_maxQualifiedCardinality /\
    mqc.o == T_Literal lit_nni_1 /\
    memP onp g /\ onp.p == o_owl_onProperty /\ onp.s == mqc.s /\
    onp.o == T_IRI p /\
    memP onc g /\ onc.p == o_owl_onClass /\ onc.s == mqc.s /\
    onc.o == T_IRI o_owl_Thing /\
    memP tu g /\ tu.p == o_rdf_type /\ tu.o == subj_term mqc.s /\
    memP u1 g /\ u1.p == p /\ u1.s == tu.s /\
    memP u2 g /\ u2.p == p /\ u2.s == tu.s /\
    subj_term y1s == u1.o /\
    t == ({ s = y1s; p = o_owl_sameAs; o = u2.o } <: triple)

// -------------------------------------------------------------------
// cls-oo, Table 5, verbatim:
//   "cls-oo | T(?c, owl:oneOf, ?x)  LIST[?x, ?y1, ..., ?yn] |
//             T(?y1, rdf:type, ?c) ... T(?yn, rdf:type, ?c)"
// `t` is any one of the n conclusions; delta GR on the member.
// -------------------------------------------------------------------
let cls_oo_derives (g : list triple) (t : triple) : prop =
  exists (decl : triple) (ys : list rdf_term) (yi : rdf_term) (yis : subject).
    memP decl g /\ decl.p == o_owl_oneOf /\
    owl_list_denotes g decl.o ys /\
    memP yi ys /\ subj_term yis == yi /\
    t == ({ s = yis; p = o_rdf_type; o = subj_term decl.s } <: triple)

(** ================================================================= **)
(** Table 6: The Semantics of Class Axioms                            **)
(** ================================================================= **)

// -------------------------------------------------------------------
// cax-sco, Table 6, verbatim:
//   "cax-sco | T(?c1, rdfs:subClassOf, ?c2)  T(?x, rdf:type, ?c1) |
//              T(?x, rdf:type, ?c2)"
// -------------------------------------------------------------------
let cax_sco_derives (g : list triple) (t : triple) : prop =
  exists (decl u : triple).
    memP decl g /\ decl.p == o_rdfs_subClassOf /\
    memP u g /\ u.p == o_rdf_type /\ u.o == subj_term decl.s /\
    t == ({ s = u.s; p = o_rdf_type; o = decl.o } <: triple)

// -------------------------------------------------------------------
// cax-eqc1 / cax-eqc2, Table 6, verbatim:
//   "cax-eqc1 | T(?c1, owl:equivalentClass, ?c2)  T(?x, rdf:type, ?c1) |
//               T(?x, rdf:type, ?c2)"
//   "cax-eqc2 | T(?c1, owl:equivalentClass, ?c2)  T(?x, rdf:type, ?c2) |
//               T(?x, rdf:type, ?c1)"
// -------------------------------------------------------------------
let cax_eqc1_derives (g : list triple) (t : triple) : prop =
  exists (decl u : triple).
    memP decl g /\ decl.p == o_owl_equivalentClass /\
    memP u g /\ u.p == o_rdf_type /\ u.o == subj_term decl.s /\
    t == ({ s = u.s; p = o_rdf_type; o = decl.o } <: triple)

let cax_eqc2_derives (g : list triple) (t : triple) : prop =
  exists (decl u : triple).
    memP decl g /\ decl.p == o_owl_equivalentClass /\
    memP u g /\ u.p == o_rdf_type /\ u.o == decl.o /\
    t == ({ s = u.s; p = o_rdf_type; o = subj_term decl.s } <: triple)

// -------------------------------------------------------------------
// cax-dw, Table 6, verbatim (a CLASH row):
//   "cax-dw | T(?c1, owl:disjointWith, ?c2)
//             T(?x, rdf:type, ?c1)  T(?x, rdf:type, ?c2) | false"
// -------------------------------------------------------------------
let cax_dw_clash (g : list triple) : prop =
  exists (decl u1 u2 : triple).
    memP decl g /\ decl.p == o_owl_disjointWith /\
    memP u1 g /\ u1.p == o_rdf_type /\ u1.o == subj_term decl.s /\
    memP u2 g /\ u2.p == o_rdf_type /\ u2.o == decl.o /\
    u2.s == u1.s

// -------------------------------------------------------------------
// cax-adc, Table 6, verbatim (a CLASH row):
//   "cax-adc | T(?y, rdf:type, owl:AllDisjointClasses)
//              T(?y, owl:members, ?x)  LIST[?x, ?c1, ..., ?cn]
//              T(?z, rdf:type, ?ci)  T(?z, rdf:type, ?cj)
//              (for any i != j) | false"
// -------------------------------------------------------------------
let cax_adc_clash (g : list triple) : prop =
  exists (ty mem u1 u2 : triple) (cs : list rdf_term) (ci cj : rdf_term).
    memP ty g /\ ty.p == o_rdf_type /\ ty.o == T_IRI o_owl_AllDisjointClasses /\
    memP mem g /\ mem.p == o_owl_members /\ mem.s == ty.s /\
    owl_list_denotes g mem.o cs /\
    two_distinct_members cs ci cj /\
    memP u1 g /\ u1.p == o_rdf_type /\ u1.o == ci /\
    memP u2 g /\ u2.p == o_rdf_type /\ u2.o == cj /\
    u2.s == u1.s

// -------------------------------------------------------------------
// Whole-family rollups, landing 2.
// -------------------------------------------------------------------
let table5_derives (g : list triple) (t : triple) : prop =
  cls_thing_derives g t \/ cls_nothing1_derives g t \/
  cls_int1_derives g t \/ cls_int2_derives g t \/ cls_uni_derives g t \/
  cls_svf1_derives g t \/ cls_svf2_derives g t \/ cls_avf_derives g t \/
  cls_hv1_derives g t \/ cls_hv2_derives g t \/
  cls_maxc2_derives g t \/ cls_maxqc3_derives g t \/
  cls_maxqc4_derives g t \/ cls_oo_derives g t

let table5_clashes (g : list triple) : prop =
  cls_nothing2_clash g \/ cls_com_clash g \/ cls_maxc1_clash g \/
  cls_maxqc1_clash g \/ cls_maxqc2_clash g

let table6_derives (g : list triple) (t : triple) : prop =
  cax_sco_derives g t \/ cax_eqc1_derives g t \/ cax_eqc2_derives g t

let table6_clashes (g : list triple) : prop =
  cax_dw_clash g \/ cax_adc_clash g


(** ================================================================= **)
(** Landing 3 vocabulary                                              **)
(** ================================================================= **)

let o_owl_AllDifferent : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#AllDifferent");
  "http://www.w3.org/2002/07/owl#AllDifferent"
let o_owl_AllDisjointProperties : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#AllDisjointProperties");
  "http://www.w3.org/2002/07/owl#AllDisjointProperties"
let o_owl_distinctMembers : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#distinctMembers");
  "http://www.w3.org/2002/07/owl#distinctMembers"
let o_owl_ObjectProperty : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#ObjectProperty");
  "http://www.w3.org/2002/07/owl#ObjectProperty"
let o_owl_DatatypeProperty : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#DatatypeProperty");
  "http://www.w3.org/2002/07/owl#DatatypeProperty"
let o_rdfs_Datatype : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2000/01/rdf-schema#Datatype");
  "http://www.w3.org/2000/01/rdf-schema#Datatype"

(** ================================================================= **)
(** Landing 3a: the deferred AllDifferent / AllDisjointProperties     **)
(** rows of Table 4 (see the ledger)                                  **)
(** ================================================================= **)

// -------------------------------------------------------------------
// eq-diff2 / eq-diff3, Table 4, verbatim (CLASH rows):
//   "eq-diff2 | T(?x, rdf:type, owl:AllDifferent)
//               T(?x, owl:members, ?y)  LIST[?y, ?z1, ..., ?zn]
//               T(?zi, owl:sameAs, ?zj)  (for any i != j) | false"
//   "eq-diff3 | T(?x, rdf:type, owl:AllDifferent)
//               T(?x, owl:distinctMembers, ?y)  LIST[?y, ?z1, ..., ?zn]
//               T(?zi, owl:sameAs, ?zj)  (for any i != j) | false"
// The two rows differ only in the membership predicate.
// -------------------------------------------------------------------
let eq_diff23_clash_via (members_pred : wf_iri) (g : list triple) : prop =
  exists (ty mem sa : triple) (zs : list rdf_term)
         (zi zj : rdf_term) (zis : subject).
    memP ty g /\ ty.p == o_rdf_type /\ ty.o == T_IRI o_owl_AllDifferent /\
    memP mem g /\ mem.p == members_pred /\ mem.s == ty.s /\
    owl_list_denotes g mem.o zs /\
    two_distinct_members zs zi zj /\
    memP sa g /\ sa.p == o_owl_sameAs /\
    subj_term zis == zi /\ sa.s == zis /\ sa.o == zj

let eq_diff2_clash (g : list triple) : prop =
  eq_diff23_clash_via o_owl_members g

let eq_diff3_clash (g : list triple) : prop =
  eq_diff23_clash_via o_owl_distinctMembers g

// -------------------------------------------------------------------
// prp-adp, Table 4, verbatim (a CLASH row):
//   "prp-adp | T(?x, rdf:type, owl:AllDisjointProperties)
//              T(?x, owl:members, ?y)  LIST[?y, ?p1, ..., ?pn]
//              T(?u, ?pi, ?v)  T(?u, ?pj, ?v)  (for any i != j) |
//              false"
// Delta GP: the members occupy predicate position in the data
// premises, so the two distinct list members must be IRIs.
// -------------------------------------------------------------------
let prp_adp_clash (g : list triple) : prop =
  exists (ty mem u1 u2 : triple) (ps : list rdf_term) (pi pj : wf_iri).
    memP ty g /\ ty.p == o_rdf_type /\
    ty.o == T_IRI o_owl_AllDisjointProperties /\
    memP mem g /\ mem.p == o_owl_members /\ mem.s == ty.s /\
    owl_list_denotes g mem.o ps /\
    two_distinct_members ps (T_IRI pi) (T_IRI pj) /\
    memP u1 g /\ u1.p == pi /\
    memP u2 g /\ u2.p == pj /\
    u2.s == u1.s /\ u2.o == u1.o

(** ================================================================= **)
(** Table 7: The Semantics of Datatypes                               **)
(**                                                                   **)
(** The dt-* rows quantify over DATA VALUES: "for each literal lt1    **)
(** and lt2 with the same data value" (dt-eq), "... with different    **)
(** data values" (dt-diff), "for each literal lt in the value space   **)
(** of datatype dt" (dt-type2). A value space is a property of the    **)
(** DATATYPE MAP, not of the graph, so these rows are stated          **)
(** PARAMETRICALLY: each takes the value-level relation it quantifies **)
(** over as an argument. The module fixes no datatype map — that is   **)
(** the refinement layer's obligation to discharge with the engine's  **)
(** concrete one, and the parameter makes the dependency explicit     **)
(** instead of baking one interpretation in as "the spec".            **)
(** ================================================================= **)

// -------------------------------------------------------------------
// dt-type1, Table 7, verbatim:
//   "dt-type1 |  | T(?dt, rdf:type, rdfs:Datatype)
//    (for each datatype ?dt supported in the datatype map)"
// Parameter: the supported-datatype set.
// -------------------------------------------------------------------
let dt_type1_derives (supported : wf_iri -> prop)
                     (g : list triple) (t : triple) : prop =
  exists (dt : wf_iri).
    supported dt /\
    t == ({ s = S_IRI dt; p = o_rdf_type; o = T_IRI o_rdfs_Datatype } <: triple)

// -------------------------------------------------------------------
// dt-type2, Table 7, verbatim:
//   "dt-type2 |  | T(?lt, rdf:type, ?dt)
//    (for each literal ?lt and each datatype ?dt supported in the
//     datatype map such that the data value of ?lt is contained in
//     the value space of ?dt)"
// Delta GR: a literal cannot occupy subject position in this tree's
// term algebra, so the row as transcribed can never fire — recorded
// as a row with an explicit FALSE eligibility premise rather than
// silently dropped. (Generalized-RDF engines materialise it; ours
// cannot express its conclusion.)
// -------------------------------------------------------------------
let dt_type2_derives (in_value_space : wf_literal -> wf_iri -> prop)
                     (g : list triple) (t : triple) : prop =
  exists (lt : wf_literal) (dt : wf_iri) (ls : subject).
    in_value_space lt dt /\
    subj_term ls == T_Literal lt /\   // unsatisfiable here: delta GR
    t == ({ s = ls; p = o_rdf_type; o = T_IRI dt } <: triple)

// -------------------------------------------------------------------
// dt-eq, Table 7, verbatim:
//   "dt-eq | T(?s, ?p, ?lt1)  T(?s2, ?p2, ?lt2) |
//            T(?lt1, owl:sameAs, ?lt2)
//    (for all ?lt1 and ?lt2 with the same data value)"
// Same delta GR as dt-type2 on the conclusion subject.
// -------------------------------------------------------------------
let dt_eq_derives (same_value : wf_literal -> wf_literal -> prop)
                  (g : list triple) (t : triple) : prop =
  exists (u1 u2 : triple) (l1 l2 : wf_literal) (ls : subject).
    memP u1 g /\ u1.o == T_Literal l1 /\
    memP u2 g /\ u2.o == T_Literal l2 /\
    same_value l1 l2 /\
    subj_term ls == T_Literal l1 /\   // unsatisfiable here: delta GR
    t == ({ s = ls; p = o_owl_sameAs; o = T_Literal l2 } <: triple)

// -------------------------------------------------------------------
// dt-diff, Table 7, verbatim (a CLASH row):
//   "dt-diff | T(?lt1, owl:sameAs, ?lt2) | false
//    (for all ?lt1 and ?lt2 with different data values)"
// A sameAs whose OBJECT is a literal is expressible; one whose subject
// is a literal is not (delta GR). The expressible half is transcribed:
// any sameAs edge REACHING a literal from a term whose own literal
// reading differs. The refinement layer decides how much of this row
// the engine can check.
// -------------------------------------------------------------------
let dt_diff_clash (different_value : wf_literal -> wf_literal -> prop)
                  (g : list triple) : prop =
  exists (sa : triple) (l1 l2 : wf_literal) (ls : subject).
    memP sa g /\ sa.p == o_owl_sameAs /\
    subj_term ls == T_Literal l1 /\   // unsatisfiable here: delta GR
    sa.s == ls /\ sa.o == T_Literal l2 /\
    different_value l1 l2

// -------------------------------------------------------------------
// dt-not-type, Table 7, verbatim (a CLASH row):
//   "dt-not-type | T(?lt, rdf:type, ?dt) | false
//    (for each literal ?lt and each datatype ?dt supported in the
//     datatype map such that the data value of ?lt is not contained
//     in the value space of ?dt)"
// Same delta GR (literal subject).
// -------------------------------------------------------------------
let dt_not_type_clash (not_in_value_space : wf_literal -> wf_iri -> prop)
                      (g : list triple) : prop =
  exists (u : triple) (lt : wf_literal) (dt : wf_iri) (ls : subject).
    memP u g /\ u.p == o_rdf_type /\ u.o == T_IRI dt /\
    subj_term ls == T_Literal lt /\   // unsatisfiable here: delta GR
    u.s == ls /\
    not_in_value_space lt dt

(** ================================================================= **)
(** Table 8: The Semantics of Schema Vocabulary                       **)
(** ================================================================= **)

// -------------------------------------------------------------------
// scm-cls, Table 8, verbatim:
//   "scm-cls | T(?c, rdf:type, owl:Class) |
//              T(?c, rdfs:subClassOf, ?c)
//              T(?c, owl:equivalentClass, ?c)
//              T(?c, rdfs:subClassOf, owl:Thing)
//              T(owl:Nothing, rdfs:subClassOf, ?c)"
// Four conclusion triples; `t` is any one (disjunction, as eq-ref).
// -------------------------------------------------------------------
let scm_cls_derives (g : list triple) (t : triple) : prop =
  exists (u : triple).
    memP u g /\ u.p == o_rdf_type /\ u.o == T_IRI o_owl_Class /\
    (t == ({ s = u.s; p = o_rdfs_subClassOf; o = subj_term u.s } <: triple) \/
     t == ({ s = u.s; p = o_owl_equivalentClass; o = subj_term u.s } <: triple) \/
     t == ({ s = u.s; p = o_rdfs_subClassOf; o = T_IRI o_owl_Thing } <: triple) \/
     t == ({ s = S_IRI o_owl_Nothing; p = o_rdfs_subClassOf; o = subj_term u.s } <: triple))

// -------------------------------------------------------------------
// scm-sco, Table 8, verbatim:
//   "scm-sco | T(?c1, rdfs:subClassOf, ?c2)
//              T(?c2, rdfs:subClassOf, ?c3) |
//              T(?c1, rdfs:subClassOf, ?c3)"
// -------------------------------------------------------------------
let scm_sco_derives (g : list triple) (t : triple) : prop =
  exists (u1 u2 : triple).
    memP u1 g /\ u1.p == o_rdfs_subClassOf /\
    memP u2 g /\ u2.p == o_rdfs_subClassOf /\
    subj_term u2.s == u1.o /\
    t == ({ s = u1.s; p = o_rdfs_subClassOf; o = u2.o } <: triple)

// -------------------------------------------------------------------
// scm-eqc1 / scm-eqc2, Table 8, verbatim:
//   "scm-eqc1 | T(?c1, owl:equivalentClass, ?c2) |
//               T(?c1, rdfs:subClassOf, ?c2)
//               T(?c2, rdfs:subClassOf, ?c1)"
//   "scm-eqc2 | T(?c1, rdfs:subClassOf, ?c2)
//               T(?c2, rdfs:subClassOf, ?c1) |
//               T(?c1, owl:equivalentClass, ?c2)"
// -------------------------------------------------------------------
let scm_eqc1_derives (g : list triple) (t : triple) : prop =
  exists (u : triple) (c2s : subject).
    memP u g /\ u.p == o_owl_equivalentClass /\
    (t == ({ s = u.s; p = o_rdfs_subClassOf; o = u.o } <: triple) \/
     (subj_term c2s == u.o /\
      t == ({ s = c2s; p = o_rdfs_subClassOf; o = subj_term u.s } <: triple)))

let scm_eqc2_derives (g : list triple) (t : triple) : prop =
  exists (u1 u2 : triple).
    memP u1 g /\ u1.p == o_rdfs_subClassOf /\
    memP u2 g /\ u2.p == o_rdfs_subClassOf /\
    subj_term u2.s == u1.o /\ u2.o == subj_term u1.s /\
    t == ({ s = u1.s; p = o_owl_equivalentClass; o = u1.o } <: triple)

// -------------------------------------------------------------------
// scm-op / scm-dp, Table 8, verbatim:
//   "scm-op | T(?p, rdf:type, owl:ObjectProperty) |
//             T(?p, rdfs:subPropertyOf, ?p)
//             T(?p, owl:equivalentProperty, ?p)"
//   "scm-dp | T(?p, rdf:type, owl:DatatypeProperty) | (same two)"
// -------------------------------------------------------------------
let scm_op_dp_derives_via (prop_class : wf_iri)
                          (g : list triple) (t : triple) : prop =
  exists (u : triple).
    memP u g /\ u.p == o_rdf_type /\ u.o == T_IRI prop_class /\
    (t == ({ s = u.s; p = o_rdfs_subPropertyOf; o = subj_term u.s } <: triple) \/
     t == ({ s = u.s; p = o_owl_equivalentProperty; o = subj_term u.s } <: triple))

let scm_op_derives (g : list triple) (t : triple) : prop =
  scm_op_dp_derives_via o_owl_ObjectProperty g t

let scm_dp_derives (g : list triple) (t : triple) : prop =
  scm_op_dp_derives_via o_owl_DatatypeProperty g t

// -------------------------------------------------------------------
// scm-spo, Table 8, verbatim:
//   "scm-spo | T(?p1, rdfs:subPropertyOf, ?p2)
//              T(?p2, rdfs:subPropertyOf, ?p3) |
//              T(?p1, rdfs:subPropertyOf, ?p3)"
// -------------------------------------------------------------------
let scm_spo_derives (g : list triple) (t : triple) : prop =
  exists (u1 u2 : triple).
    memP u1 g /\ u1.p == o_rdfs_subPropertyOf /\
    memP u2 g /\ u2.p == o_rdfs_subPropertyOf /\
    subj_term u2.s == u1.o /\
    t == ({ s = u1.s; p = o_rdfs_subPropertyOf; o = u2.o } <: triple)

// -------------------------------------------------------------------
// scm-eqp1 / scm-eqp2, Table 8, verbatim (property mirror of eqc1/2):
//   "scm-eqp1 | T(?p1, owl:equivalentProperty, ?p2) |
//               T(?p1, rdfs:subPropertyOf, ?p2)
//               T(?p2, rdfs:subPropertyOf, ?p1)"
//   "scm-eqp2 | T(?p1, rdfs:subPropertyOf, ?p2)
//               T(?p2, rdfs:subPropertyOf, ?p1) |
//               T(?p1, owl:equivalentProperty, ?p2)"
// -------------------------------------------------------------------
let scm_eqp1_derives (g : list triple) (t : triple) : prop =
  exists (u : triple) (p2s : subject).
    memP u g /\ u.p == o_owl_equivalentProperty /\
    (t == ({ s = u.s; p = o_rdfs_subPropertyOf; o = u.o } <: triple) \/
     (subj_term p2s == u.o /\
      t == ({ s = p2s; p = o_rdfs_subPropertyOf; o = subj_term u.s } <: triple)))

let scm_eqp2_derives (g : list triple) (t : triple) : prop =
  exists (u1 u2 : triple).
    memP u1 g /\ u1.p == o_rdfs_subPropertyOf /\
    memP u2 g /\ u2.p == o_rdfs_subPropertyOf /\
    subj_term u2.s == u1.o /\ u2.o == subj_term u1.s /\
    t == ({ s = u1.s; p = o_owl_equivalentProperty; o = u1.o } <: triple)

// -------------------------------------------------------------------
// scm-dom1 / scm-dom2, Table 8, verbatim:
//   "scm-dom1 | T(?p, rdfs:domain, ?c1)  T(?c1, rdfs:subClassOf, ?c2) |
//               T(?p, rdfs:domain, ?c2)"
//   "scm-dom2 | T(?p2, rdfs:domain, ?c)
//               T(?p1, rdfs:subPropertyOf, ?p2) |
//               T(?p1, rdfs:domain, ?c)"
// -------------------------------------------------------------------
let scm_dom1_derives (g : list triple) (t : triple) : prop =
  exists (dom sub : triple).
    memP dom g /\ dom.p == o_rdfs_domain /\
    memP sub g /\ sub.p == o_rdfs_subClassOf /\
    subj_term sub.s == dom.o /\
    t == ({ s = dom.s; p = o_rdfs_domain; o = sub.o } <: triple)

let scm_dom2_derives (g : list triple) (t : triple) : prop =
  exists (dom sub : triple).
    memP dom g /\ dom.p == o_rdfs_domain /\
    memP sub g /\ sub.p == o_rdfs_subPropertyOf /\
    sub.o == subj_term dom.s /\
    t == ({ s = sub.s; p = o_rdfs_domain; o = dom.o } <: triple)

// -------------------------------------------------------------------
// scm-rng1 / scm-rng2, Table 8, verbatim (range mirrors):
//   "scm-rng1 | T(?p, rdfs:range, ?c1)  T(?c1, rdfs:subClassOf, ?c2) |
//               T(?p, rdfs:range, ?c2)"
//   "scm-rng2 | T(?p2, rdfs:range, ?c)
//               T(?p1, rdfs:subPropertyOf, ?p2) |
//               T(?p1, rdfs:range, ?c)"
// -------------------------------------------------------------------
let scm_rng1_derives (g : list triple) (t : triple) : prop =
  exists (rng sub : triple).
    memP rng g /\ rng.p == o_rdfs_range /\
    memP sub g /\ sub.p == o_rdfs_subClassOf /\
    subj_term sub.s == rng.o /\
    t == ({ s = rng.s; p = o_rdfs_range; o = sub.o } <: triple)

let scm_rng2_derives (g : list triple) (t : triple) : prop =
  exists (rng sub : triple).
    memP rng g /\ rng.p == o_rdfs_range /\
    memP sub g /\ sub.p == o_rdfs_subPropertyOf /\
    sub.o == subj_term rng.s /\
    t == ({ s = sub.s; p = o_rdfs_range; o = rng.o } <: triple)

// -------------------------------------------------------------------
// scm-hv, Table 8, verbatim:
//   "scm-hv | T(?c1, owl:hasValue, ?i)  T(?c1, owl:onProperty, ?p1)
//             T(?c2, owl:hasValue, ?i)  T(?c2, owl:onProperty, ?p2)
//             T(?p1, rdfs:subPropertyOf, ?p2) |
//             T(?c1, rdfs:subClassOf, ?c2)"
// -------------------------------------------------------------------
let scm_hv_derives (g : list triple) (t : triple) : prop =
  exists (hv1 onp1 hv2 onp2 sub : triple) (p1 p2 : wf_iri).
    memP hv1 g /\ hv1.p == o_owl_hasValue /\
    memP onp1 g /\ onp1.p == o_owl_onProperty /\ onp1.s == hv1.s /\
    onp1.o == T_IRI p1 /\
    memP hv2 g /\ hv2.p == o_owl_hasValue /\ hv2.o == hv1.o /\
    memP onp2 g /\ onp2.p == o_owl_onProperty /\ onp2.s == hv2.s /\
    onp2.o == T_IRI p2 /\
    memP sub g /\ sub.p == o_rdfs_subPropertyOf /\
    sub.s == S_IRI p1 /\ sub.o == T_IRI p2 /\
    t == ({ s = hv1.s; p = o_rdfs_subClassOf; o = subj_term hv2.s } <: triple)

// -------------------------------------------------------------------
// scm-svf1 / scm-svf2, Table 8, verbatim:
//   "scm-svf1 | T(?c1, owl:someValuesFrom, ?y1)
//               T(?c1, owl:onProperty, ?p)
//               T(?c2, owl:someValuesFrom, ?y2)
//               T(?c2, owl:onProperty, ?p)
//               T(?y1, rdfs:subClassOf, ?y2) |
//               T(?c1, rdfs:subClassOf, ?c2)"
//   "scm-svf2 | T(?c1, owl:someValuesFrom, ?y)
//               T(?c1, owl:onProperty, ?p1)
//               T(?c2, owl:someValuesFrom, ?y)
//               T(?c2, owl:onProperty, ?p2)
//               T(?p1, rdfs:subPropertyOf, ?p2) |
//               T(?c1, rdfs:subClassOf, ?c2)"
// -------------------------------------------------------------------
let scm_svf1_derives (g : list triple) (t : triple) : prop =
  exists (svf1 onp1 svf2 onp2 sub : triple) (p : wf_iri).
    memP svf1 g /\ svf1.p == o_owl_someValuesFrom /\
    memP onp1 g /\ onp1.p == o_owl_onProperty /\ onp1.s == svf1.s /\
    onp1.o == T_IRI p /\
    memP svf2 g /\ svf2.p == o_owl_someValuesFrom /\
    memP onp2 g /\ onp2.p == o_owl_onProperty /\ onp2.s == svf2.s /\
    onp2.o == T_IRI p /\
    memP sub g /\ sub.p == o_rdfs_subClassOf /\
    subj_term sub.s == svf1.o /\ sub.o == svf2.o /\
    t == ({ s = svf1.s; p = o_rdfs_subClassOf; o = subj_term svf2.s } <: triple)

let scm_svf2_derives (g : list triple) (t : triple) : prop =
  exists (svf1 onp1 svf2 onp2 sub : triple) (p1 p2 : wf_iri).
    memP svf1 g /\ svf1.p == o_owl_someValuesFrom /\
    memP onp1 g /\ onp1.p == o_owl_onProperty /\ onp1.s == svf1.s /\
    onp1.o == T_IRI p1 /\
    memP svf2 g /\ svf2.p == o_owl_someValuesFrom /\ svf2.o == svf1.o /\
    memP onp2 g /\ onp2.p == o_owl_onProperty /\ onp2.s == svf2.s /\
    onp2.o == T_IRI p2 /\
    memP sub g /\ sub.p == o_rdfs_subPropertyOf /\
    sub.s == S_IRI p1 /\ sub.o == T_IRI p2 /\
    t == ({ s = svf1.s; p = o_rdfs_subClassOf; o = subj_term svf2.s } <: triple)

// -------------------------------------------------------------------
// scm-avf1 / scm-avf2, Table 8, verbatim:
//   "scm-avf1 | T(?c1, owl:allValuesFrom, ?y1)
//               T(?c1, owl:onProperty, ?p)
//               T(?c2, owl:allValuesFrom, ?y2)
//               T(?c2, owl:onProperty, ?p)
//               T(?y1, rdfs:subClassOf, ?y2) |
//               T(?c1, rdfs:subClassOf, ?c2)"
//   "scm-avf2 | T(?c1, owl:allValuesFrom, ?y)
//               T(?c1, owl:onProperty, ?p1)
//               T(?c2, owl:allValuesFrom, ?y)
//               T(?c2, owl:onProperty, ?p2)
//               T(?p1, rdfs:subPropertyOf, ?p2) |
//               T(?c2, rdfs:subClassOf, ?c1)"
// NOTE the direction flip in scm-avf2's conclusion (c2 below c1):
// widening the property NARROWS the universal restriction. The flip is
// the Recommendation's own text, transcribed as printed.
// -------------------------------------------------------------------
let scm_avf1_derives (g : list triple) (t : triple) : prop =
  exists (avf1 onp1 avf2 onp2 sub : triple) (p : wf_iri).
    memP avf1 g /\ avf1.p == o_owl_allValuesFrom /\
    memP onp1 g /\ onp1.p == o_owl_onProperty /\ onp1.s == avf1.s /\
    onp1.o == T_IRI p /\
    memP avf2 g /\ avf2.p == o_owl_allValuesFrom /\
    memP onp2 g /\ onp2.p == o_owl_onProperty /\ onp2.s == avf2.s /\
    onp2.o == T_IRI p /\
    memP sub g /\ sub.p == o_rdfs_subClassOf /\
    subj_term sub.s == avf1.o /\ sub.o == avf2.o /\
    t == ({ s = avf1.s; p = o_rdfs_subClassOf; o = subj_term avf2.s } <: triple)

let scm_avf2_derives (g : list triple) (t : triple) : prop =
  exists (avf1 onp1 avf2 onp2 sub : triple) (p1 p2 : wf_iri).
    memP avf1 g /\ avf1.p == o_owl_allValuesFrom /\
    memP onp1 g /\ onp1.p == o_owl_onProperty /\ onp1.s == avf1.s /\
    onp1.o == T_IRI p1 /\
    memP avf2 g /\ avf2.p == o_owl_allValuesFrom /\ avf2.o == avf1.o /\
    memP onp2 g /\ onp2.p == o_owl_onProperty /\ onp2.s == avf2.s /\
    onp2.o == T_IRI p2 /\
    memP sub g /\ sub.p == o_rdfs_subPropertyOf /\
    sub.s == S_IRI p1 /\ sub.o == T_IRI p2 /\
    t == ({ s = avf2.s; p = o_rdfs_subClassOf; o = subj_term avf1.s } <: triple)

// -------------------------------------------------------------------
// scm-int, Table 8, verbatim:
//   "scm-int | T(?c, owl:intersectionOf, ?x)  LIST[?x, ?c1, ..., ?cn] |
//              T(?c, rdfs:subClassOf, ?c1) ...
//              T(?c, rdfs:subClassOf, ?cn)"
// scm-uni, Table 8, verbatim:
//   "scm-uni | T(?c, owl:unionOf, ?x)  LIST[?x, ?c1, ..., ?cn] |
//              T(?c1, rdfs:subClassOf, ?c) ...
//              T(?cn, rdfs:subClassOf, ?c)"
// -------------------------------------------------------------------
let scm_int_derives (g : list triple) (t : triple) : prop =
  exists (decl : triple) (cs : list rdf_term) (ci : rdf_term).
    memP decl g /\ decl.p == o_owl_intersectionOf /\
    owl_list_denotes g decl.o cs /\ memP ci cs /\
    t == ({ s = decl.s; p = o_rdfs_subClassOf; o = ci } <: triple)

let scm_uni_derives (g : list triple) (t : triple) : prop =
  exists (decl : triple) (cs : list rdf_term) (ci : rdf_term) (cis : subject).
    memP decl g /\ decl.p == o_owl_unionOf /\
    owl_list_denotes g decl.o cs /\ memP ci cs /\
    subj_term cis == ci /\
    t == ({ s = cis; p = o_rdfs_subClassOf; o = subj_term decl.s } <: triple)

// -------------------------------------------------------------------
// Whole-family rollups, landing 3. The dt-* rollups carry the same
// parameters their rows do.
// -------------------------------------------------------------------
let table7_derives (supported : wf_iri -> prop)
                   (in_value_space : wf_literal -> wf_iri -> prop)
                   (same_value : wf_literal -> wf_literal -> prop)
                   (g : list triple) (t : triple) : prop =
  dt_type1_derives supported g t \/
  dt_type2_derives in_value_space g t \/
  dt_eq_derives same_value g t

let table7_clashes (different_value : wf_literal -> wf_literal -> prop)
                   (not_in_value_space : wf_literal -> wf_iri -> prop)
                   (g : list triple) : prop =
  dt_diff_clash different_value g \/
  dt_not_type_clash not_in_value_space g

let table8_derives (g : list triple) (t : triple) : prop =
  scm_cls_derives g t \/ scm_sco_derives g t \/
  scm_eqc1_derives g t \/ scm_eqc2_derives g t \/
  scm_op_derives g t \/ scm_dp_derives g t \/
  scm_spo_derives g t \/ scm_eqp1_derives g t \/ scm_eqp2_derives g t \/
  scm_dom1_derives g t \/ scm_dom2_derives g t \/
  scm_rng1_derives g t \/ scm_rng2_derives g t \/
  scm_hv_derives g t \/ scm_svf1_derives g t \/ scm_svf2_derives g t \/
  scm_avf1_derives g t \/ scm_avf2_derives g t \/
  scm_int_derives g t \/ scm_uni_derives g t

let table4_clashes_complete (g : list triple) : prop =
  table4_clashes g \/ eq_diff2_clash g \/ eq_diff3_clash g \/
  prp_adp_clash g
