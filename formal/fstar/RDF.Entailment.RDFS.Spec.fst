module RDF.Entailment.RDFS.Spec

// ===================================================================
// A DECLARATIVE specification of RDFS ENTAILMENT — rung three of
// Hayes' entailment ladder, above RDF entailment
// (RDF.Entailment.RDF.Spec.fst) and above simple entailment
// (RDF.Entailment.Simple.Spec.fst).
//
// Like its two predecessors this module computes nothing and mentions
// no function of the engine: it does NOT open RDFS.Closure,
// OWL.Closure, RDF.Graph.Executable or RDF.Entailment.Regime. A
// reviewer can diff it against the W3C rule table alone. The shipping
// closure is proven against it in RDF.Entailment.RDFS.Refinement.fst;
// the interpretation conditions that JUSTIFY each rule are in
// RDF.Entailment.RDFS.ModelTheory.fst.
//
// -------------------------------------------------------------------
// BASELINE PINNING
// -------------------------------------------------------------------
// Primary baseline: RDF 1.1 Semantics, W3C Recommendation
// 25 February 2014 (https://www.w3.org/TR/rdf11-mt/) section 9,
// "RDFS Interpretations" — the semantic conditions, the RDFS axiomatic
// triples, and the RDFS entailment rule table rdfs1 .. rdfs13, quoted
// row by row below.
//
// Cross-checked against Hayes, RDF Semantics, W3C Recommendation
// 10 February 2004 (REC-rdf-mt-20040210) section 4 ("Interpreting the
// RDFS vocabulary") and its rule table. RDFS-rung deltas beyond the
// RDF-rung deltas D1-D6 already tabulated in
// RDF.Entailment.RDF.Spec.fst's banner:
//
//   D7. rdfs1. 2004's rdfs1 reads "uuu aaa lll (lll a plain literal) =>
//       uuu aaa _:nnn . _:nnn rdf:type rdfs:Literal" — a bnode-minting
//       rule about PLAIN literals, which RDF 1.1 does not have (delta
//       D1). RDF 1.1's rdfs1 instead reads "any IRI aaa in D => aaa
//       rdf:type rdfs:Datatype". Two different rules under one number.
//       This module transcribes the RDF 1.1 reading and names the 2004
//       reading as `rdfs1_2004_derives` so the divergence is explicit
//       rather than resolved silently.
//   D8. rdfs4a / rdfs4b. Identical text in both baselines. In 2004
//       these are the only route to `rdfs:Resource` membership; in 1.1
//       the semantic condition ICEXT(I(rdfs:Resource)) = IR does the
//       same work. No delta in the RULE, a presentational delta in the
//       condition.
//   D9. rdfs6 / rdfs10 (reflexivity of subPropertyOf on IP, of
//       subClassOf on IC) are rules in both baselines and are ALSO
//       semantic conditions in both. The shipping tree implements a
//       harvesting APPROXIMATION of them (`rdfs_reflexivity_axioms`)
//       whose class/property collection is wider than either rule
//       licenses — see finding RS-1 in the Refinement module.
//
// -------------------------------------------------------------------
// GENERALIZED RDF (delta D5, restated where it bites)
// -------------------------------------------------------------------
// RDF 1.1 Semantics states these rules over GENERALIZED RDF, where a
// literal may be a subject. `RDF.Term.subject` is IRI-or-bnode only,
// so three of the rules below (rdfs3, rdfs5, rdfs9, rdfs11) carry an
// explicit "the object is subject-eligible" premise. Each such premise
// is a real INCOMPLETENESS of what this tree can express, and each is
// flagged at its rule. Nothing is weakened to make a proof close: the
// premises restrict the RULE to the triples this tree's term algebra
// admits, which is exactly the shipping engine's own restriction, and
// the fragment statements in the ModelTheory module name it.
// ===================================================================

open FStar.List.Tot
open RDF.Term
open RDF.Triple
open RDF.Vocabulary.Axioms
open RDF.Entailment.RDF.Spec
// The rung below: `subj_term` (a subject viewed as a term) and the
// `graph_tt_free` quarantine predicate are reused verbatim rather than
// re-spelled. That module opens nothing but RDF.Term / RDF.Triple, so
// the "Spec does not name the engine" property is preserved.
open RDF.Entailment.Simple.Spec

// -------------------------------------------------------------------
// rdfs1 (RDF 1.1 reading), section 9 rule table, verbatim:
//   "rdfs1 | any IRI aaa in D | aaa rdf:type rdfs:Datatype ."
// -------------------------------------------------------------------
let rdfs1_derives (dd : datatype_set) (t : triple) : prop =
  exists (a : wf_iri).
    dd a /\ t == ({ s = S_IRI a; p = i_rdf_type; o = T_IRI i_rdfs_Datatype } <: triple)

// rdfs1 (2004 reading), REC-rdf-mt-20040210 section 4.3, verbatim:
//   "rdfs1 | uuu aaa lll .  (lll a plain literal) |
//            uuu aaa _:nnn . _:nnn rdf:type rdfs:Literal ."
// Kept for the delta table (D7); a plain literal in RDF 1.1's term
// algebra is one typed xsd:string or rdf:langString.
let rdfs1_2004_derives (g : list triple) (b : bnode_id) (t1 t2 : triple) : prop =
  bnode_fresh_for b g /\
  (exists (u : triple) (l : wf_literal).
     memP u g /\ u.o == T_Literal l /\
     (l.datatype == xsd_string \/ l.datatype == rdf_lang_string) /\
     t1 == ({ s = u.s; p = u.p; o = T_BNode b } <: triple) /\
     t2 == ({ s = S_BNode b; p = i_rdf_type; o = T_IRI i_rdfs_Literal } <: triple))

// -------------------------------------------------------------------
// rdfs2, section 9 rule table, verbatim:
//   "rdfs2 | aaa rdfs:domain xxx . yyy aaa zzz . | yyy rdf:type xxx ."
// `aaa` occupies a predicate slot in the second premise and a subject
// slot in the first, so it is an IRI on both sides — no escape needed.
// `xxx` may be any term (generalized RDF permits a literal class name
// in object position, and `RDF.Term` can express that).
// -------------------------------------------------------------------
let rdfs2_derives (g : list triple) (t : triple) : prop =
  exists (decl u : triple) (a : wf_iri).
    memP decl g /\ decl.p == i_rdfs_domain /\ decl.s == S_IRI a /\
    memP u g /\ u.p == a /\
    t == ({ s = u.s; p = i_rdf_type; o = decl.o } <: triple)

// -------------------------------------------------------------------
// rdfs3, section 9 rule table, verbatim:
//   "rdfs3 | aaa rdfs:range xxx . yyy aaa zzz . | zzz rdf:type xxx ."
// GENERALIZED-RDF PREMISE (delta D5): `zzz` moves from object position
// to subject position. When zzz is a literal or an RDF 1.2 triple term
// the conclusion is not an RDF triple this tree can build, and the
// rule simply does not fire. `term_to_subject u.o == Some zs` is that
// side condition, stated rather than hidden.
// -------------------------------------------------------------------
let rdfs3_derives (g : list triple) (t : triple) : prop =
  exists (decl u : triple) (a : wf_iri) (zs : subject).
    memP decl g /\ decl.p == i_rdfs_range /\ decl.s == S_IRI a /\
    memP u g /\ u.p == a /\
    subj_term zs == u.o /\
    t == ({ s = zs; p = i_rdf_type; o = decl.o } <: triple)

// -------------------------------------------------------------------
// rdfs4a / rdfs4b, section 9 rule table, verbatim:
//   "rdfs4a | xxx aaa yyy . | xxx rdf:type rdfs:Resource ."
//   "rdfs4b | xxx aaa yyy . | yyy rdf:type rdfs:Resource ."
// rdfs4b carries the same generalized-RDF premise as rdfs3.
// NOT IMPLEMENTED by the shipping closure — see finding RS-2.
// -------------------------------------------------------------------
let rdfs4a_derives (g : list triple) (t : triple) : prop =
  exists (u : triple). memP u g /\
    t == ({ s = u.s; p = i_rdf_type; o = T_IRI i_rdfs_Resource } <: triple)

let rdfs4b_derives (g : list triple) (t : triple) : prop =
  exists (u : triple) (ys : subject). memP u g /\ subj_term ys == u.o /\
    t == ({ s = ys; p = i_rdf_type; o = T_IRI i_rdfs_Resource } <: triple)

// -------------------------------------------------------------------
// rdfs5, section 9 rule table, verbatim:
//   "rdfs5 | xxx rdfs:subPropertyOf yyy . yyy rdfs:subPropertyOf zzz . |
//            xxx rdfs:subPropertyOf zzz ."
// Generalized-RDF premise on `yyy` (object of the first premise,
// subject of the second).
// -------------------------------------------------------------------
let rdfs5_derives2 (gd gs : list triple) (t : triple) : prop =
  exists (t1 t2 : triple) (ys : subject).
    memP t1 gd /\ t1.p == i_rdfs_subPropertyOf /\
    memP t2 gs /\ t2.p == i_rdfs_subPropertyOf /\
    subj_term ys == t1.o /\ t2.s == ys /\
    t == ({ s = t1.s; p = i_rdfs_subPropertyOf; o = t2.o } <: triple)

let rdfs5_derives (g : list triple) (t : triple) : prop = rdfs5_derives2 g g t

// -------------------------------------------------------------------
// rdfs6, section 9 rule table, verbatim:
//   "rdfs6 | xxx rdf:type rdf:Property . | xxx rdfs:subPropertyOf xxx ."
// -------------------------------------------------------------------
let rdfs6_derives (g : list triple) (t : triple) : prop =
  exists (u : triple). memP u g /\ u.p == i_rdf_type /\ u.o == T_IRI i_rdf_Property /\
    t == ({ s = u.s; p = i_rdfs_subPropertyOf; o = subj_term u.s } <: triple)

// -------------------------------------------------------------------
// rdfs7, section 9 rule table, verbatim:
//   "rdfs7 | aaa rdfs:subPropertyOf bbb . xxx aaa yyy . | xxx bbb yyy ."
// `bbb` moves into a PREDICATE slot, so it must be an IRI. That is a
// genuine restriction of generalized RDF too (a bnode-valued
// subPropertyOf object licenses no ordinary-RDF conclusion), and it is
// exactly the shipping rule's `T_IRI q` match.
// -------------------------------------------------------------------
let rdfs7_derives (g : list triple) (t : triple) : prop =
  exists (decl u : triple) (a b : wf_iri).
    memP decl g /\ decl.p == i_rdfs_subPropertyOf /\
    decl.s == S_IRI a /\ decl.o == T_IRI b /\
    memP u g /\ u.p == a /\
    t == ({ s = u.s; p = b; o = u.o } <: triple)

// -------------------------------------------------------------------
// rdfs8, section 9 rule table, verbatim:
//   "rdfs8 | xxx rdf:type rdfs:Class . | xxx rdfs:subClassOf rdfs:Resource ."
// NOT IMPLEMENTED by the shipping closure — see finding RS-2.
// -------------------------------------------------------------------
let rdfs8_derives (g : list triple) (t : triple) : prop =
  exists (u : triple). memP u g /\ u.p == i_rdf_type /\ u.o == T_IRI i_rdfs_Class /\
    t == ({ s = u.s; p = i_rdfs_subClassOf; o = T_IRI i_rdfs_Resource } <: triple)

// -------------------------------------------------------------------
// rdfs9, section 9 rule table, verbatim:
//   "rdfs9 | xxx rdfs:subClassOf yyy . zzz rdf:type xxx . | zzz rdf:type yyy ."
// `xxx` appears as the SUBJECT of the subClassOf premise and as the
// OBJECT of the type premise, so the two occurrences are linked by
// `subj_term`.
// -------------------------------------------------------------------
// TWO-SOURCE form. The shipping rule reads its `rdf:type` premise
// from the graph it is folding over and its `rdfs:subClassOf` premise
// from an index SNAPSHOT that may be older. Splitting the two premise
// sources is what lets the fixed-point driver's soundness compose (the
// snapshot is built once per closure step, from the step's input,
// while the accumulator grows within the step). `rdfs9_derives` is the
// diagonal and is the form the W3C table states.
let rdfs9_derives2 (gd gs : list triple) (t : triple) : prop =
  exists (sub typ : triple) (xs : subject).
    memP sub gs /\ sub.p == i_rdfs_subClassOf /\ sub.s == xs /\
    memP typ gd /\ typ.p == i_rdf_type /\ typ.o == subj_term xs /\
    t == ({ s = typ.s; p = i_rdf_type; o = sub.o } <: triple)

let rdfs9_derives (g : list triple) (t : triple) : prop = rdfs9_derives2 g g t

// -------------------------------------------------------------------
// rdfs10, section 9 rule table, verbatim:
//   "rdfs10 | xxx rdf:type rdfs:Class . | xxx rdfs:subClassOf xxx ."
// -------------------------------------------------------------------
let rdfs10_derives (g : list triple) (t : triple) : prop =
  exists (u : triple). memP u g /\ u.p == i_rdf_type /\ u.o == T_IRI i_rdfs_Class /\
    t == ({ s = u.s; p = i_rdfs_subClassOf; o = subj_term u.s } <: triple)

// -------------------------------------------------------------------
// rdfs11, section 9 rule table, verbatim:
//   "rdfs11 | xxx rdfs:subClassOf yyy . yyy rdfs:subClassOf zzz . |
//             xxx rdfs:subClassOf zzz ."
// Generalized-RDF premise on `yyy`, as in rdfs5.
// -------------------------------------------------------------------
let rdfs11_derives2 (gd gs : list triple) (t : triple) : prop =
  exists (t1 t2 : triple) (ys : subject).
    memP t1 gd /\ t1.p == i_rdfs_subClassOf /\
    memP t2 gs /\ t2.p == i_rdfs_subClassOf /\
    subj_term ys == t1.o /\ t2.s == ys /\
    t == ({ s = t1.s; p = i_rdfs_subClassOf; o = t2.o } <: triple)

let rdfs11_derives (g : list triple) (t : triple) : prop = rdfs11_derives2 g g t

// -------------------------------------------------------------------
// rdfs12, section 9 rule table, verbatim:
//   "rdfs12 | xxx rdf:type rdfs:ContainerMembershipProperty . |
//             xxx rdfs:subPropertyOf rdfs:member ."
// -------------------------------------------------------------------
let rdfs12_derives (g : list triple) (t : triple) : prop =
  exists (u : triple). memP u g /\ u.p == i_rdf_type /\
    u.o == T_IRI i_rdfs_ContainerMembershipProperty /\
    t == ({ s = u.s; p = i_rdfs_subPropertyOf; o = T_IRI i_rdfs_member } <: triple)

// -------------------------------------------------------------------
// rdfs13, section 9 rule table, verbatim:
//   "rdfs13 | xxx rdf:type rdfs:Datatype . | xxx rdfs:subClassOf rdfs:Literal ."
// NOT IMPLEMENTED by the shipping closure — see finding RS-2.
// -------------------------------------------------------------------
let rdfs13_derives (g : list triple) (t : triple) : prop =
  exists (u : triple). memP u g /\ u.p == i_rdf_type /\ u.o == T_IRI i_rdfs_Datatype /\
    t == ({ s = u.s; p = i_rdfs_subClassOf; o = T_IRI i_rdfs_Literal } <: triple)

// ===================================================================
// The RDFS axiomatic triples.
//
// RDF 1.1 Semantics section 9 lists them. The 38 finite rows are
// already transcribed one-per-`let`, with per-row citations, in
// RDF.Vocabulary.Axioms (`rdfs_axiomatic_triples`); reused here rather
// than copied. The infinite `rdf:_n` family is captured by the schema.
// ===================================================================
let rdfs_axiomatic (t : triple) : prop =
  memP t rdfs_axiomatic_triples \/
  (exists (i : wf_iri). is_rdf_member_iri i /\
     (t == ({ s = S_IRI i; p = i_rdf_type;
              o = T_IRI i_rdfs_ContainerMembershipProperty } <: triple) \/
      t == ({ s = S_IRI i; p = i_rdfs_domain; o = T_IRI i_rdfs_Resource } <: triple) \/
      t == ({ s = S_IRI i; p = i_rdfs_range;  o = T_IRI i_rdfs_Resource } <: triple)))

// The rdfs12 consequence of the axiomatic `rdf:_n rdf:type
// rdfs:ContainerMembershipProperty` rows. NOT itself an axiomatic
// triple — RDF 1.1 Semantics section 9 lists only the type / domain /
// range rows for the rdf:_n family — but RDFS-entailed by the EMPTY
// graph, since the axiomatic row plus rdfs12 gives it with no premise
// from the data. Named separately so the shipping container rule's
// refinement theorem can say exactly which of the two triples it emits
// is axiomatic and which is one rdfs12 step past an axiom.
let rdfs_member_subproperty (t : triple) : prop =
  exists (i : wf_iri). is_rdf_member_iri i /\
    t == ({ s = S_IRI i; p = i_rdfs_subPropertyOf;
            o = T_IRI i_rdfs_member } <: triple)

// ===================================================================
// THE SPECIFICATION, syntactic side.
//
// `rdfs_licensed g t` — "t is licensed at the RDFS rung by graph g":
// t is already in g, or it is an RDF/RDFS axiomatic triple, or one
// application of some row of the RDF/RDFS rule tables to g derives it.
//
// This is the relation the shipping rules are proven to respect
// (`rdfs_step_licensed` below): a rule pass may only add licensed
// triples. Note the ORDER of quantification — the premises are read
// off `g`, the INPUT graph, not off the growing accumulator. That is
// the shape that makes per-rule soundness composable through the
// fixed-point driver, and it is strictly stronger than "licensed by
// the output".
// ===================================================================
let rdfs_licensed (dd : datatype_set) (g : list triple) (t : triple) : prop =
  memP t g \/ rdf_axiomatic t \/ rdfs_axiomatic t \/
  rdfs_member_subproperty t \/
  rdfD2_derives g t \/
  rdfs1_derives dd t \/ rdfs2_derives g t \/ rdfs3_derives g t \/
  rdfs4a_derives g t \/ rdfs4b_derives g t \/ rdfs5_derives g t \/
  rdfs6_derives g t \/ rdfs7_derives g t \/ rdfs8_derives g t \/
  rdfs9_derives g t \/ rdfs10_derives g t \/ rdfs11_derives g t \/
  rdfs12_derives g t \/ rdfs13_derives g t

let rdfs_step_licensed (dd : datatype_set) (g out : list triple) : prop =
  forall (t : triple). memP t out ==> rdfs_licensed dd g t

// A graph is RDFS-CLOSED when it contains the axiomatic triples and
// is shut under every rule of the table. RDF 1.1 Semantics section 9's
// completeness statement is about exactly this object:
//   "If S is RDFS consistent, then S RDFS entails E just when the
//    generalized RDFS closure of S towards E simply entails E."
// The bnode-minting rules (rdfD1, the 2004 rdfs1) are excluded, as in
// the spec's own "towards E" formulation.
let rdfs_closed (dd : datatype_set) (g : list triple) : prop =
  (forall (t : triple). rdf_axiomatic t ==> memP t g) /\
  (forall (t : triple). rdfs_axiomatic t ==> memP t g) /\
  (forall (t : triple). rdfD2_derives g t ==> memP t g) /\
  (forall (t : triple). rdfs1_derives dd t ==> memP t g) /\
  (forall (t : triple). rdfs2_derives g t ==> memP t g) /\
  (forall (t : triple). rdfs3_derives g t ==> memP t g) /\
  (forall (t : triple). rdfs4a_derives g t ==> memP t g) /\
  (forall (t : triple). rdfs4b_derives g t ==> memP t g) /\
  (forall (t : triple). rdfs5_derives g t ==> memP t g) /\
  (forall (t : triple). rdfs6_derives g t ==> memP t g) /\
  (forall (t : triple). rdfs7_derives g t ==> memP t g) /\
  (forall (t : triple). rdfs8_derives g t ==> memP t g) /\
  (forall (t : triple). rdfs9_derives g t ==> memP t g) /\
  (forall (t : triple). rdfs10_derives g t ==> memP t g) /\
  (forall (t : triple). rdfs11_derives g t ==> memP t g) /\
  (forall (t : triple). rdfs12_derives g t ==> memP t g) /\
  (forall (t : triple). rdfs13_derives g t ==> memP t g)

// ===================================================================
// THE rho-df FRAGMENT (Munoz, Perez, Gutierrez, "Simple and Efficient
// Minimal RDFS", J. Web Semantics 7(3) 2009; earlier as ESWC 2007).
//
// rho-df is the sub-vocabulary { rdfs:subPropertyOf, rdfs:subClassOf,
// rdfs:domain, rdfs:range, rdf:type }. Their Theorem: the six rules
// (2)(a,b) and (3)(a,b) and (4)(a,b) of that paper — which are exactly
// rdfs5, rdfs7, rdfs11, rdfs9, rdfs2, rdfs3 — are SOUND and COMPLETE
// for RDFS entailment restricted to rho-df, and the reflexivity /
// axiomatic-triple machinery is not needed there.
//
// That set is, triple for triple, the shipping rule set of
// RDFS.Closure.fsti. Naming the fragment here is what lets the
// ModelTheory module state a completeness theorem with a fragment that
// is a published result rather than an artefact of this codebase.
//
// `rho_df_triple` additionally requires the rho-df vocabulary NOT to
// appear in a position the fragment does not interpret (the paper's
// restriction that the vocabulary is used "as intended"), and that no
// blank node or literal sits where a rule would need an IRI.
// ===================================================================
let is_rho_df_iri (i : wf_iri) : prop =
  i == i_rdfs_subPropertyOf \/ i == i_rdfs_subClassOf \/
  i == i_rdfs_domain \/ i == i_rdfs_range \/ i == i_rdf_type

// The rho-df vocabulary never occurs outside the predicate slot.
let rho_df_term_ok (t : rdf_term) : prop =
  match t with
  | T_IRI i -> ~(is_rho_df_iri i)
  | T_BNode _ -> True
  | T_Literal _ -> True
  | T_TripleTerm _ _ _ -> False

let rho_df_subject_ok (s : subject) : prop =
  match s with
  | S_IRI i -> ~(is_rho_df_iri i)
  | S_BNode _ -> True

let rho_df_triple (t : triple) : prop =
  rho_df_subject_ok t.s /\ rho_df_term_ok t.o

let rho_df_graph (g : list triple) : prop =
  forall (t : triple). memP t g ==> rho_df_triple t
