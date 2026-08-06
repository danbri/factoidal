module OWL.Semantics

// Model-theoretic semantics for RDF graphs, targeting the OWL 2
// RDF-Based Semantics (W3C Rec 2012-12-11) restricted to the semantic
// conditions the shipping OWL 2 RL closure rules (OWL.Closure.fsti /
// RDFS.Closure.fsti) need for their soundness proofs. This module is a
// PROOF-LAYER module: it defines interpretations, denotation,
// satisfaction, entailment, and the pilot slice of semantic
// conditions. It computes nothing at runtime; the soundness theorems
// live in OWL.Semantics.Soundness.fst.
//
// Design doc: docs/designissues/2026-07-29-rdf-based-semantics-
// formalization.md. Read that first — it records the formalization
// SHAPE decisions (why IEXT is a ternary prop over an arbitrary
// domain type, why bnode satisfaction is an existential over total
// assignments, why every semantic condition below is stated in the
// weakest form the W3C tables imply) and the citations into Hayes'
// RDF Semantics and the OWL 2 RDF-Based Semantics tables.
//
// The simplifications relative to the full W3C interpretation
// structure are all in the SOUND direction: this module's class of
// interpretations is a SUPERSET of the OWL 2 RDF-Based
// interpretations (we drop conditions — e.g. IP membership guards,
// datatype map conformance, the only-if halves of iff conditions —
// and we totalize partial maps). A rule proven sound against every
// interpretation here is therefore sound against every genuine OWL 2
// RDF-Based interpretation. The converse (completeness) is out of
// scope and would need the missing conditions.

open FStar.List.Tot
open RDF.Term
open RDF.Triple
open RDF.Graph
open RDF.Indexed
open RDFS.Closure
open OWL.Closure

// ===================================================================
// Interpretations — Hayes, RDF 1.1 Semantics section 5 ("simple
// interpretations"), merged with the OWL 2 RDF-Based Semantics
// interpretation structure (section 4: IR, IP, IEXT, ICEXT).
// ===================================================================

// A simple interpretation over a vocabulary, folded into one record:
//
//   idom      the domain of discourse IR (a nonempty set of
//             "resources"). Represented as an arbitrary F* type
//             carrying at least one inhabitant (idom_wit). Infinite
//             domains — and datatype value spaces embedded in IR —
//             enter for free: any F* type may serve, and nothing
//             below ever needs to decide or enumerate membership.
//   i_iri     IS: IRI -> IR. Total, as in Hayes section 5.
//   i_lit     IL: literal -> IR. Total over well-formed literals.
//             The W3C structure sends ill-typed literals to
//             arbitrary resources anyway (RDF 1.1 Semantics section
//             7), so totalizing loses no generality for soundness.
//   i_tt      denotation constructor for RDF 1.2 triple terms, taking
//             the denotations of the three components. The pilot
//             rules never inspect triple terms; making their
//             denotation an uninterpreted function of the component
//             denotations keeps denot_term total and compositional.
//   iext      IEXT as a curried ternary relation:
//             iext p x y  means  <x,y> `elem` IEXT(p).
//             The W3C structure types IEXT : IP -> P(IR x IR); we
//             totalize it over all of IR (equivalently: we drop the
//             "p `elem` IP" side conditions). Dropping a condition
//             ENLARGES the interpretation class, which only
//             strengthens soundness results (see module banner).
//
// prop (not bool) throughout: satisfaction over an infinite domain is
// definable but not decidable, and never needs to be decided — the
// theorems quantify over it.
noeq type interp = {
  idom     : Type0;
  idom_wit : idom;
  i_iri    : wf_iri -> idom;
  i_lit    : wf_literal -> idom;
  i_tt     : idom -> idom -> idom -> idom;
  iext     : idom -> idom -> idom -> prop;
}

// A blank-node assignment ("mapping A" in Hayes section 5.2): a total
// function from bnode labels to domain elements. Totality is another
// enlarging simplification — every partial assignment extends to a
// total one using idom_wit, so the existential below is unchanged.
let bnode_assignment (d : Type0) = bnode_id -> d

// ===================================================================
// Denotation — [I+A] in Hayes section 5.2.
// ===================================================================

let denot_subject (i : interp) (a : bnode_assignment i.idom) (s : subject) : i.idom =
  match s with
  | S_IRI x   -> i.i_iri x
  | S_BNode b -> a b

let rec denot_term (i : interp) (a : bnode_assignment i.idom) (t : rdf_term)
  : Tot i.idom (decreases t) =
  match t with
  | T_IRI x            -> i.i_iri x
  | T_BNode b          -> a b
  | T_Literal l        -> i.i_lit l
  | T_TripleTerm s p o -> i.i_tt (denot_subject i a s) (i.i_iri p) (denot_term i a o)

// A subject seen through term_to_subject / subject_to_term denotes
// the same resource in both roles. (Mechanical; used constantly by
// the soundness proofs because the closure rules round-trip objects
// into subjects via term_to_subject.)
let lemma_denot_subject_to_term (i : interp) (a : bnode_assignment i.idom) (s : subject)
  : Lemma (denot_term i a (subject_to_term s) == denot_subject i a s) = ()

let lemma_denot_term_to_subject (i : interp) (a : bnode_assignment i.idom)
    (t : rdf_term) (s : subject)
  : Lemma (requires term_to_subject t == Some s)
          (ensures  denot_subject i a s == denot_term i a t) = ()

// ===================================================================
// Satisfaction and entailment — Hayes section 5.2 (truth of triples
// and graphs), with the existential bnode semantics on both sides.
// ===================================================================

// Truth of one triple under a fixed assignment: the pair of the
// subject's and object's denotations is in IEXT of the predicate's
// denotation.
let triple_holds (i : interp) (a : bnode_assignment i.idom) (t : triple) : prop =
  i.iext (i.i_iri t.p) (denot_subject i a t.s) (denot_term i a t.o)

// Truth of a whole graph under a FIXED assignment. The soundness
// proofs work at this level: the closure rules never mint fresh
// blank nodes (in the pilot slice), so one assignment serves the
// input and the output graph alike.
let holds_all (i : interp) (a : bnode_assignment i.idom) (g : rdf_graph) : prop =
  forall (t : triple). List.Tot.memP t g ==> triple_holds i a t

// Graph satisfaction: some assignment of the blank nodes makes every
// triple true (Hayes section 5.2: "I(G) = true if [I+A](G) = true for
// some mapping A").
let satisfies (i : interp) (g : rdf_graph) : prop =
  exists (a : bnode_assignment i.idom). holds_all i a g

// Entailment relative to a class of interpretations (a set of
// semantic conditions): every interpretation in the class satisfying
// g1 satisfies g2. Instantiated below with the pilot condition
// bundle; the framework deliberately keeps the class a parameter so
// later waves can grow the bundle without restating theorems.
let entails_under (conds : interp -> prop) (g1 g2 : rdf_graph) : prop =
  forall (i : interp). conds i ==> satisfies i g1 ==> satisfies i g2

// ===================================================================
// Class extension — ICEXT, OWL 2 RDF-Based Semantics section 4.2:
// ICEXT(c) = { x | <x,c> `elem` IEXT(I(rdf:type)) }.
// ===================================================================

let icext (i : interp) (x c : i.idom) : prop =
  i.iext (i.i_iri rdf_type) x c

// ===================================================================
// Semantic sequences — the denotation-level image of rdf:List
// structure. OWL 2 RDF-Based Semantics section 3 defines "s is a
// sequence of a1 ... an over IR" as: there are l1 ... ln in IR with
// l1 = s, <lk, ak> in IEXT(I(rdf:first)), <lk, l(k+1)> in
// IEXT(I(rdf:rest)), and l(n+1) = I(rdf:nil). seq_is transcribes
// that definition with the element list as the induction handle.
// ===================================================================

let rec seq_is (i : interp) (l : i.idom) (elems : list i.idom)
  : Tot prop (decreases elems) =
  match elems with
  | [] -> l == i.i_iri rdf_nil_iri
  | x :: rest ->
    exists (l' : i.idom).
      i.iext (i.i_iri rdf_first) l x /\
      i.iext (i.i_iri rdf_rest) l l' /\
      seq_is i l' rest

// ===================================================================
// The pilot semantic conditions. Each is the weakest reading the
// cited W3C table row implies (only-if halves and IP/IC membership
// side conditions dropped; see the design doc section "Choosing the
// condition strength"). Only conditions the four pilot rules need
// are present; the full-program plan adds one small prop per rule
// family.
// ===================================================================

// rdfs:domain — RDF 1.1 Semantics section 9 (RDFS interpretations),
// condition on IEXT(I(rdfs:domain)); identically present in OWL 2
// RDF-Based Semantics Table 5.8. If <p,c> in IEXT(I(rdfs:domain))
// and <x,y> in IEXT(p) then x in ICEXT(c).
let cond_domain (i : interp) : prop =
  forall (p c x y : i.idom).
    i.iext (i.i_iri rdfs_domain) p c ==> i.iext p x y ==> icext i x c

// rdfs:range — dual of cond_domain (same table rows): the OBJECT
// falls in the class.
let cond_range (i : interp) : prop =
  forall (p c x y : i.idom).
    i.iext (i.i_iri rdfs_range) p c ==> i.iext p x y ==> icext i y c

// owl:SymmetricProperty — OWL 2 RDF-Based Semantics Table 5.14
// (property characteristics), if-direction: membership in
// ICEXT(I(owl:SymmetricProperty)) makes the extension symmetric.
let cond_symmetric (i : interp) : prop =
  forall (p x y : i.idom).
    icext i p (i.i_iri owl_SymmetricProperty) ==> i.iext p x y ==> i.iext p y x

// owl:sameAs — OWL 2 RDF-Based Semantics Table 5.2 (equality):
// IEXT(I(owl:sameAs)) = { <x,y> | x = y }. Stated as the full iff:
// both directions are exactly what the table asserts, and the
// congruence rules (eq-rep-*) need the forward direction while
// eq-ref needs the backward one.
let cond_sameas_identity (i : interp) : prop =
  forall (x y : i.idom).
    i.iext (i.i_iri owl_sameAs) x y <==> x == y

// owl:oneOf — OWL 2 RDF-Based Semantics Table 5.9 (enumerations):
// if <c,l> in IEXT(I(owl:oneOf)) and l is a sequence of a1 ... an
// over IR, then ICEXT(c) = { a1, ..., an }. The pilot needs only the
// superset half (every listed element is a member); the hypothesis
// keeps the table's shape — the sequence reading is a PREMISE, so
// the condition constrains every sequence reading the interpretation
// gives l, which is what makes the syntactic-list argument in the
// soundness proof go through (see the design doc, "The oneOf
// condition and sequence readings").
let cond_oneof (i : interp) : prop =
  forall (c l : i.idom) (elems : list i.idom).
    i.iext (i.i_iri owl_oneOf_iri) c l ==> seq_is i l elems ==>
    (forall (x : i.idom). List.Tot.memP x elems ==> icext i x c)

// owl:equivalentClass — OWL 2 RDF-Based Semantics Table 5.8
// (equivalentClass condition): IEXT(I(owl:equivalentClass)) =
// { <x,y> | ICEXT(x) = ICEXT(y) }. The pilot needs only the
// implication the closure rule relies on — extension equality
// implies both rdfs:subClassOf directions — so this condition is
// stated as that implication rather than the full class-extension
// equality (the weakest reading the table row implies; see the
// module banner and cond_oneof's comment for the same pattern).
// NOT added to owl_rl_pilot_conditions: see the design note on
// owl_rule_equivalent_class_sound in OWL.Semantics.Soundness.fst —
// growing that bundle perturbs the SMT context for its existing
// consumers, so this rule's lemma takes the condition explicitly.
let cond_equivalent_class (i : interp) : prop =
  forall (c d : i.idom).
    i.iext (i.i_iri owl_equivalentClass) c d ==>
    (i.iext (i.i_iri rdfs_subClassOf) c d /\
     i.iext (i.i_iri rdfs_subClassOf) d c)

// owl:equivalentProperty -- OWL 2 RDF-Based Semantics Table 5.9
// (equivalentProperty condition): IEXT(I(owl:equivalentProperty)) =
// { <p,q> | IEXT(p) = IEXT(q) }. As with cond_equivalent_class, the
// pilot needs only the implication the closure rule relies on --
// extension equality implies both rdfs:subPropertyOf directions --
// so this condition is stated as that implication rather than the
// full extension equality (the weakest reading the table row
// implies; see cond_equivalent_class's comment for the same
// pattern). NOT added to owl_rl_pilot_conditions: same reasoning as
// cond_equivalent_class -- growing that bundle perturbs the SMT
// context for its existing consumers, so this rule's lemma takes
// the condition explicitly.
let cond_equivalent_property (i : interp) : prop =
  forall (p q : i.idom).
    i.iext (i.i_iri owl_equivalentProperty) p q ==>
    (i.iext (i.i_iri rdfs_subPropertyOf) p q /\
     i.iext (i.i_iri rdfs_subPropertyOf) q p)

// owl:sameAs, reflexive half -- OWL 2 RDF-Based Semantics Table 5.11:
// IEXT(I(owl:sameAs)) is the identity relation on IR, which contains
// every reflexive pair <x,x>. cond_sameas_identity above states the
// COLLAPSE direction (x = y follows from sameAs x y, needed by the
// eq-rep-* congruence rules); this condition is the other half the
// identity relation gives for free -- every element is sameAs itself
// -- which cond_sameas_identity's iff does not by itself hand the
// eq-ref soundness proof without redoing the identity-relation
// argument, so it is stated directly.
let cond_sameas_reflexive (i : interp) : prop =
  forall (x : i.idom). i.iext (i.i_iri owl_sameAs) x x

// owl:differentFrom, symmetry -- OWL 2 RDF-Based Semantics Table 5.13
// (differentFrom condition): <x,y> in IEXT(I(owl:differentFrom)) iff x
// and y are distinct. Distinctness is symmetric in x and y, so the
// relation the table defines is symmetric; this condition states just
// that symmetry, the half owl_rule_differentFrom_symmetry needs. This
// is the pilot's first [ext] condition: the OWL.RL.Spec.fst engine
// ledger lists differentFrom_symmetry [ext] "Table 5.13's differentFrom
// condition is symmetric in its arguments" -- the rule implements no
// W3C RL table row, and this condition together with the lemma in
// OWL.Semantics.Soundness.fst is that justification made
// machine-checked. NOT added to owl_rl_pilot_conditions: same
// reasoning as cond_equivalent_class / cond_equivalent_property --
// growing that bundle perturbs the SMT context for its existing
// consumers, so this rule's lemma takes the condition explicitly.
let cond_differentfrom_symmetric (i : interp) : prop =
  forall (x y : i.idom).
    i.iext (i.i_iri owl_differentFrom) x y ==>
    i.iext (i.i_iri owl_differentFrom) y x

// owl:disjointWith, symmetry -- OWL 2 RDF-Based Semantics Table 5.14
// (disjointWith condition): <x,y> in IEXT(I(owl:disjointWith)) iff
// CEXT(x) and CEXT(y) are disjoint (have empty intersection). Set
// disjointness is symmetric in its arguments, so the relation the
// table defines is symmetric; this condition states just that
// symmetry, the half owl_rule_disjoint_with_propagation's first
// branch needs. This is the pilot's second [ext] condition: the
// OWL.RL.Spec.fst engine ledger justifies the rule by "disjointness
// symmetry plus complementOf-implies-disjointness" -- this condition
// together with cond_complementof_disjoint and the lemma in
// OWL.Semantics.Soundness.fst is that justification made
// machine-checked. NOT added to owl_rl_pilot_conditions: same
// reasoning as cond_equivalent_class / cond_differentfrom_symmetric --
// growing that bundle perturbs the SMT context for its existing
// consumers, so this rule's lemma takes the condition explicitly.
let cond_disjointwith_symmetric (i : interp) : prop =
  forall (x y : i.idom).
    i.iext (i.i_iri owl_disjointWith_iri) x y ==>
    i.iext (i.i_iri owl_disjointWith_iri) y x

// owl:complementOf implies disjointWith, both directions -- OWL 2
// RDF-Based Semantics Table 5.15 (complementOf condition): <x,y> in
// IEXT(I(owl:complementOf)) iff CEXT(x) is the complement of CEXT(y)
// (relative to the domain of discourse). A class and its complement
// have empty intersection by definition, so they are disjoint, and
// disjointness does not care which side is named "the complement" --
// hence both disjointWith directions. This is the weakest implication
// owl_rule_disjoint_with_propagation's second branch uses (it does not
// need the converse: disjointness does not imply complementation,
// since that also requires the union to exhaust owl:Thing -- see the
// engine rule's comment on why the reverse direction is deliberately
// not emitted).
let cond_complementof_disjoint (i : interp) : prop =
  forall (x y : i.idom).
    i.iext (i.i_iri owl_complementOf_iri) x y ==>
    (i.iext (i.i_iri owl_disjointWith_iri) x y /\
     i.iext (i.i_iri owl_disjointWith_iri) y x)

// owl:complementOf, symmetry -- OWL 2 RDF-Based Semantics Table 5.15
// (complementOf condition): <x,y> in IEXT(I(owl:complementOf)) iff
// CEXT(x) = IOT \ CEXT(y) (both class extensions are subsets of IOT,
// the domain of interpretation for classes). Relative complement
// within IOT is an involution, so CEXT(x) = IOT \ CEXT(y) iff
// CEXT(y) = IOT \ CEXT(x) -- the condition is symmetric in its two
// arguments (WebOnt-complementOf-001 states exactly this:
// "complementOf is a SymmetricProperty"). Distinct from
// cond_complementof_disjoint above, which derives the WEAKER
// owl:disjointWith consequence owl_rule_disjoint_with_propagation
// needs; this condition states the direct predicate-level flip
// owl_rule_symmetric_metapredicates needs -- one of the six [ext]
// conditions the THIRD [ext] ledger entry (Group E(a), OWL.Closure.fsti
// ~line 3684 "A binary OWL vocabulary predicate is SYMMETRIC exactly
// when the semantic condition ... is invariant under swapping its two
// arguments") needs machine-checked. NOT added to owl_rl_pilot_conditions:
// same reasoning as the other [ext] conditions above -- growing that
// bundle perturbs the SMT context for its existing consumers, so this
// rule's lemma takes the condition explicitly.
let cond_complementof_symmetric (i : interp) : prop =
  forall (x y : i.idom).
    i.iext (i.i_iri owl_complementOf_iri) x y ==>
    i.iext (i.i_iri owl_complementOf_iri) y x

// owl:propertyDisjointWith, symmetry -- OWL 2 RDF-Based Semantics,
// the property-level counterpart of Table 5.14's disjointWith
// condition: <x,y> in IEXT(I(owl:propertyDisjointWith)) iff EXT(x)
// and EXT(y) are disjoint (empty intersection). Set intersection
// commutes, so the condition is symmetric in its arguments -- same
// argument as cond_disjointwith_symmetric above, one level down
// (property extensions rather than class extensions). One of the six
// [ext] conditions Group E(a) needs; see cond_complementof_symmetric's
// comment for the shared ledger context. NOT added to
// owl_rl_pilot_conditions: same reasoning as the other [ext]
// conditions above.
let cond_propertydisjointwith_symmetric (i : interp) : prop =
  forall (x y : i.idom).
    i.iext (i.i_iri owl_propertyDisjointWith) x y ==>
    i.iext (i.i_iri owl_propertyDisjointWith) y x

// owl:inverseOf, symmetry -- OWL 2 RDF-Based Semantics condition for
// owl:inverseOf: <p,q> in IEXT(I(owl:inverseOf)) iff EXT(p) = converse
// of EXT(q). Converse is an involution (the converse of the converse
// of a relation R is R itself), so EXT(p) = converse EXT(q) iff
// EXT(q) = converse EXT(p) -- the condition is symmetric in its two
// arguments. One of the six [ext] conditions Group E(a) needs; see
// cond_complementof_symmetric's comment for the shared ledger context.
// NOT added to owl_rl_pilot_conditions: same reasoning as the other
// [ext] conditions above.
let cond_inverseof_symmetric (i : interp) : prop =
  forall (p q : i.idom).
    i.iext (i.i_iri owl_inverseOf) p q ==>
    i.iext (i.i_iri owl_inverseOf) q p

// owl:equivalentClass, symmetry -- OWL 2 RDF-Based Semantics Table 5.8
// (equivalentClass condition): IEXT(I(owl:equivalentClass)) =
// { <x,y> | CEXT(x) = CEXT(y) }; equality of class extensions is
// symmetric, so the relation the table defines is symmetric. Distinct
// from cond_equivalent_class above, which states the WEAKER
// rdfs:subClassOf-both-directions consequence cls-eqc1/2 needs; this
// condition states the direct predicate-level flip
// owl_rule_symmetric_metapredicates needs. One of the six [ext]
// conditions Group E(a) needs; see cond_complementof_symmetric's
// comment for the shared ledger context. NOT added to
// owl_rl_pilot_conditions: same reasoning as the other [ext]
// conditions above.
let cond_equivalentclass_symmetric (i : interp) : prop =
  forall (x y : i.idom).
    i.iext (i.i_iri owl_equivalentClass) x y ==>
    i.iext (i.i_iri owl_equivalentClass) y x

// owl:equivalentProperty, symmetry -- OWL 2 RDF-Based Semantics
// Table 5.9 (equivalentProperty condition): IEXT(I(owl:equivalentProperty))
// = { <p,q> | EXT(p) = EXT(q) }; equality of extensions is symmetric.
// Distinct from cond_equivalent_property above, which states the
// WEAKER rdfs:subPropertyOf-both-directions consequence prp-eqp1/2
// needs; this condition states the direct predicate-level flip. One
// of the six [ext] conditions Group E(a) needs; see
// cond_complementof_symmetric's comment for the shared ledger
// context. NOT added to owl_rl_pilot_conditions: same reasoning as
// the other [ext] conditions above.
let cond_equivalentproperty_symmetric (i : interp) : prop =
  forall (p q : i.idom).
    i.iext (i.i_iri owl_equivalentProperty) p q ==>
    i.iext (i.i_iri owl_equivalentProperty) q p

// owl:propertyChainAxiom composed with itself implies owl:TransitiveProperty
// -- OWL.Closure.fsti's owl_rule_chain_to_transitive banner names this
// scm-trans-from-chain: "sound but not in OWL 2 RL/RDF Table 9: if (P
// owl:propertyChainAxiom (P P)) ... then P is transitive." Two real table
// rows combine to license it: (1) OWL 2 RDF-Based Semantics Table 5
// (Additional Semantic Conditions for the Axiom Mapping), the
// SubObjectPropertyOf(ObjectPropertyChain(P1..Pn), Q) row, specialized to
// n=2, Q=P1=P2=P (self-composition) -- a propertyChainAxiom edge from P to
// a sequence reading [P;P] forces IEXT(P) to be closed under
// self-composition, i.e. IEXT(P) transitive; (2) Table 5.14's
// owl:TransitiveProperty condition, the CONVERSE half of the direction
// cond_symmetric above uses for owl:SymmetricProperty (that condition
// reads "membership implies the extension is symmetric"; this one reads
// the other way, "the extension being transitive implies membership" --
// the full table row is the iff both directions come from). Stated as one
// direct implication (premise -> conclusion, the weakest reading the rule
// needs) rather than exposing the general n-ary chain-composition
// condition or the TransitiveProperty iff's other half separately, same
// pattern as cond_domain / cond_complementof_disjoint above. NOT added to
// owl_rl_pilot_conditions: same reasoning as the other [ext] conditions
// above -- growing that bundle perturbs the SMT context for its existing
// consumers, so this rule's lemma takes the condition explicitly.
let cond_chain2_transitive (i : interp) : prop =
  forall (p l : i.idom).
    i.iext (i.i_iri owl_propertyChainAxiom) p l ==>
    seq_is i l [p; p] ==>
    icext i p (i.i_iri owl_TransitiveProperty)

// owl:Restriction is a subclass of owl:Class -- OWL 2 RL/RDF "Table 5:
// Axiomatic Triples" (the same table already cited by
// OWL.Closure.fsti's Group E owl:Thing/owl:Nothing axioms, ~line 5534)
// lists `owl:Restriction rdfs:subClassOf owl:Class` as an axiomatic
// triple, true unconditionally in every OWL 2 RL/RDF interpretation.
// Reading that fixed subClassOf fact through the RDFS class-extension
// semantic condition (RDF 1.1 Semantics section 9: CEXT(c) is a subset
// of CEXT(d) whenever c rdfs:subClassOf d holds) gives: every element
// of ICEXT(owl:Restriction) is also in ICEXT(owl:Class). This is the
// weakest reading OWL.Closure.fsti's owl_rule_scm_cls_restriction needs
// -- its own banner already states the target directly ("scm-cls
// [OWL 2 RL/RDF, partial]: every owl:Restriction is also an
// owl:Class"); the general class-subsumption transfer for arbitrary
// c/d is not needed, only this one fixed instance. This is the
// OWL.RL.Spec.fst ledger's [ext] entry "scm-cls extended to
// restriction nodes". NOT added to owl_rl_pilot_conditions: same
// reasoning as the other [ext] conditions above -- growing that bundle
// perturbs the SMT context for its existing consumers, so this rule's
// lemma takes the condition explicitly.
let cond_restriction_subclass_of_class (i : interp) : prop =
  forall (x : i.idom).
    icext i x (i.i_iri owl_Restriction_iri) ==> icext i x (i.i_iri owl_Class)

// Mutual rdfs:subClassOf implies owl:equivalentClass -- OWL 2
// RDF-Based Semantics Table 5.8 (equivalentClass condition):
// IEXT(I(owl:equivalentClass)) = { <x,y> | CEXT(x) = CEXT(y) }; two
// classes with CEXT(c) = CEXT(d) satisfy rdfs:subClassOf in BOTH
// directions (Table 5.8's subClassOf condition, CEXT(c) subset-of
// CEXT(d)) and conversely rdfs:subClassOf both ways forces CEXT(c) =
// CEXT(d) by antisymmetry of subset. This is the OTHER direction of
// the same table row cond_equivalent_class above reads forward
// (equivalentClass ==> both subClassOf directions); OWL.Closure.fsti's
// owl_rule_scm_eqc2 banner names it directly: "scm-eqc2: if (C
// rdfs:subClassOf D) and (D rdfs:subClassOf C) then (C
// owl:equivalentClass D) -- Reverse of cls-eqc1/cls-eqc2." Stated as
// one direct implication (both subClassOf directions -> the
// equivalentClass conclusion, the weakest reading the rule needs)
// rather than exposing the full CEXT-equality biconditional, same
// pattern as cond_equivalent_class / cond_chain2_transitive above.
// NOT added to owl_rl_pilot_conditions: same reasoning as the other
// [ext]/table-row conditions above -- growing that bundle perturbs
// the SMT context for its existing consumers, so this rule's lemma
// takes the condition explicitly.
let cond_mutual_subclass_equivalent (i : interp) : prop =
  forall (c d : i.idom).
    i.iext (i.i_iri rdfs_subClassOf) c d ==>
    i.iext (i.i_iri rdfs_subClassOf) d c ==>
    i.iext (i.i_iri owl_equivalentClass) c d

// Mutual rdfs:subPropertyOf implies owl:equivalentProperty -- OWL 2
// RDF-Based Semantics Table 5.9 (equivalentProperty condition):
// IEXT(I(owl:equivalentProperty)) = { <p,q> | EXT(p) = EXT(q) }; two
// properties with EXT(p) = EXT(q) satisfy rdfs:subPropertyOf in BOTH
// directions (Table 5.9's subPropertyOf condition, EXT(p) subset-of
// EXT(q)) and conversely rdfs:subPropertyOf both ways forces EXT(p) =
// EXT(q) by antisymmetry of subset. Exact mirror of
// cond_mutual_subclass_equivalent above, one level down (properties
// rather than classes); OWL.Closure.fsti's owl_rule_scm_eqp2 banner
// names it directly: "scm-eqp2: if (P rdfs:subPropertyOf Q) and (Q
// rdfs:subPropertyOf P) then (P owl:equivalentProperty Q) -- Reverse
// of prp-eqp1/prp-eqp2." Stated as one direct implication (both
// subPropertyOf directions -> the equivalentProperty conclusion, the
// weakest reading the rule needs), same pattern as
// cond_mutual_subclass_equivalent. NOT added to
// owl_rl_pilot_conditions: same reasoning as the other [ext]/table-row
// conditions above -- growing that bundle perturbs the SMT context for
// its existing consumers, so this rule's lemma takes the condition
// explicitly.
let cond_mutual_subproperty_equivalent (i : interp) : prop =
  forall (p q : i.idom).
    i.iext (i.i_iri rdfs_subPropertyOf) p q ==>
    i.iext (i.i_iri rdfs_subPropertyOf) q p ==>
    i.iext (i.i_iri owl_equivalentProperty) p q

// owl:TransitiveProperty -- OWL 2 RDF-Based Semantics Table 5.14
// (property characteristics), if-direction: membership in
// ICEXT(I(owl:TransitiveProperty)) makes the extension transitive.
// Converse half of the direction cond_symmetric above uses for
// owl:SymmetricProperty (same table row, "membership implies a
// closure property of the extension" pattern); the rule this backs,
// owl_rule_transitive_property (prp-trp), is the instance-level sibling
// of owl_rule_chain_to_transitive's cond_chain2_transitive (the same
// table condition read through a propertyChainAxiom witness instead of
// a direct rdf:type owl:TransitiveProperty declaration).
let cond_transitive (i : interp) : prop =
  forall (p x y z : i.idom).
    icext i p (i.i_iri owl_TransitiveProperty) ==>
    i.iext p x y ==> i.iext p y z ==> i.iext p x z

// owl:FunctionalProperty -- OWL 2 RDF-Based Semantics Table 5.14
// (property characteristics), if-direction: membership in
// ICEXT(I(owl:FunctionalProperty)) makes the extension a partial
// function -- two objects related to the same subject under a
// functional property are the SAME domain element (not merely
// owl:sameAs-related; owl_rule_functional's emission is the sameAs
// TRIPLE, but the semantic content Table 5.14 asserts is the stronger
// domain-element identity, which cond_sameas_identity's backward
// direction then turns into the emitted sameAs fact -- see
// owl_rule_functional_sound in OWL.Semantics.Soundness.fst for that
// composition). Mirrors cond_symmetric/cond_transitive's "membership
// implies a closure property of the extension" pattern.
let cond_functional (i : interp) : prop =
  forall (p x y z : i.idom).
    icext i p (i.i_iri owl_FunctionalProperty) ==>
    i.iext p x y ==> i.iext p x z ==> y == z

// owl:inverseOf -- OWL 2 RDF-Based Semantics Table 5.5 (property
// mapping): <p,q> in IEXT(I(owl:inverseOf)) iff EXT(q) is the converse
// of EXT(p): forall x y. iext p x y <==> iext q y x. prp-inv1/prp-inv2
// (OWL 2 RL/RDF Table 4) are the two Horn-clause halves of this iff
// read forward from one owl:inverseOf declaration; stated directly as
// the iff here (the weakest reading that licenses BOTH directions
// owl_rule_inverse_of emits from the single declaration inv_t, since
// the rule's inner fold tests t.p against BOTH p1_iri and p2_iri in
// one pass -- see owl_rule_inverse_of_sound).
let cond_inverse_of (i : interp) : prop =
  forall (p q x y : i.idom).
    i.iext (i.i_iri owl_inverseOf) p q ==>
    (i.iext p x y <==> i.iext q y x)

// Literal RDF-term equality respects the interpretation -- RDF 1.1
// Concepts SS3.3 / RDF 1.1 Semantics SS3.1 (Literals): two literals
// whose lexical form, datatype IRI, and language tag agree UP TO CASE
// (RDF.Term.fsti's rdf_term_eq / lang_tag_eq; same treatment for
// rdf:XMLLiteral lexical forms via xml_canon_eq) are not merely
// co-denoting distinct literals under RDF's abstract syntax -- they
// ARE the same literal TERM (RDF 1.1 Concepts explicitly normalizes
// language-tag case for term identity), so any genuine interpretation
// (a function of RDF TERMS) denotes them identically. This is a
// well-formedness fact about what counts as an interpretation AT ALL
// -- the same status this file's i_iri/i_lit already carry by being
// well-defined FUNCTIONS of their string argument -- not an extra OWL
// semantic condition narrowing genuine models: every OWL 2 RDF-Based
// interpretation satisfies it, because this record's i_lit : wf_literal
// -> idom is typed over the RAW STRING encoding (case-sensitive
// lang_tag field) rather than RDF's term-equality quotient, a gap this
// file's own simplifications (module banner: "totalizing partial maps
// ... all in the SOUND direction") introduce and this condition closes
// back up. #337's value-equality semantics is the engine-side mirror
// of the same fact (RDF.Term.fsti, join_canon_term). Needed by
// owl_rule_prp_key_sound: agree_on_property's rdf_term_eq witness pairs
// must denote identically for the hasKey semantic condition to fire.
let cond_literal_term_eq_respecting (i : interp) : prop =
  forall (l1 l2 : wf_literal). rdf_term_eq (T_Literal l1) (T_Literal l2) == true ==>
    i.i_lit l1 == i.i_lit l2

// Bridging lemma for prp-key's truth proof (and any future rule
// reading agree_on_property / rdf_term_eq-matching object pairs):
// rdf_term_eq-equal RDF terms denote the SAME domain element under any
// interpretation satisfying cond_literal_term_eq_respecting. Recursion
// mirrors rdf_term_eq's own structural recursion (RDF.Term.fsti):
// T_IRI/T_BNode cases close via F*'s decidable string equality (i1 = i2
// as booleans gives i1 == i2 as values for the eqtype `string`, hence
// constructor congruence gives T_IRI i1 == T_IRI i2 -- no condition
// needed, these are never literals); T_Literal needs
// cond_literal_term_eq_respecting directly; T_TripleTerm recurses into
// the object sub-term and reuses i_tt's plain-function structure
// (equal component denotations give an equal i_tt result for free,
// since i_tt is just an uninterpreted function of its three
// arguments). Mismatched-constructor cases are unreachable under the
// rdf_term_eq == true hypothesis (rdf_term_eq's own definition returns
// false there) and close vacuously.
// owl:hasKey -- OWL 2 RDF-Based Semantics Table 5 (HasKey mapping):
// if <c,l> in IEXT(I(owl:hasKey)), l is a sequence of p1 ... pn over
// IP, x and y are both in ICEXT(c), and for every pi there is a value
// v with <x,v> and <y,v> both in IEXT(pi), then x = y. Same seq_is
// premise shape as cond_oneof above (the key-property list is itself
// an rdf:List, read the same way); the pilot's prp-key rule
// (owl_rule_prp_key) needs exactly this forward implication -- the
// weakest reading the table row implies -- to license its owl:sameAs
// emission. NOT added to owl_rl_pilot_conditions: same reasoning as
// the other explicitly-threaded conditions above.
let cond_haskey (i : interp) : prop =
  forall (c l x y : i.idom) (pterms : list i.idom).
    i.iext (i.i_iri owl_hasKey) c l ==>
    seq_is i l pterms ==>
    icext i x c ==> icext i y c ==>
    (forall (p : i.idom). List.Tot.memP p pterms ==>
       (exists (v : i.idom). i.iext p x v /\ i.iext p y v)) ==>
    x == y

let rec lemma_rdf_term_eq_denot
    (i : interp) (a : bnode_assignment i.idom) (t1 t2 : rdf_term)
  : Lemma
    (requires cond_literal_term_eq_respecting i /\ rdf_term_eq t1 t2 == true)
    (ensures  denot_term i a t1 == denot_term i a t2)
    (decreases t1) =
  match t1, t2 with
  | T_IRI _, T_IRI _ -> ()
  | T_BNode _, T_BNode _ -> ()
  | T_Literal l1, T_Literal l2 -> assert (i.i_lit l1 == i.i_lit l2)
  | T_TripleTerm _ _ o1, T_TripleTerm _ _ o2 -> lemma_rdf_term_eq_denot i a o1 o2
  | _, _ -> ()

// The pilot bundle. Every OWL 2 RDF-Based interpretation (in the
// W3C sense, with any datatype map) satisfies all five conditions,
// so entails_under owl_rl_pilot_conditions is implied by (is weaker
// than) RDF-Based entailment — the safe direction for soundness.
let owl_rl_pilot_conditions (i : interp) : prop =
  cond_domain i /\ cond_range i /\ cond_symmetric i /\
  cond_sameas_identity i /\ cond_oneof i

let pilot_entails (g1 g2 : rdf_graph) : prop =
  entails_under owl_rl_pilot_conditions g1 g2

// ===================================================================
// Index well-formedness — the hypotheses the soundness proofs need
// about the indexed_graph snapshot the rules consult. Split per
// bucket because different rules touch different buckets, and
// because the two clauses have different discharge status against
// build_indexed (see OWL.Semantics.Soundness.fst: the ig_pred clause
// is proven outright; the ig_sp clause's key-decomposition half
// depends on sp_key injectivity — a FINDING, see the design doc).
// ===================================================================

// Every triple the predicate bucket serves up under key k is a real
// triple of the snapshot and really has predicate k.
let ig_wf_pred (ig : indexed_graph) : prop =
  forall (k : string) (t : triple).
    List.Tot.memP t (bucket_lookup ig.ig_pred k) ==>
    List.Tot.memP t ig.ig_triples /\ t.p == k

// Every triple the subject-predicate bucket serves up under the
// composite key sp_key s p is a real triple of the snapshot with
// exactly that subject and predicate.
let ig_wf_sp (ig : indexed_graph) : prop =
  forall (s : subject) (p : wf_iri) (t : triple).
    List.Tot.memP t (bucket_lookup ig.ig_sp (sp_key s p)) ==>
    List.Tot.memP t ig.ig_triples /\ t.s == s /\ t.p == p

// Every triple the subject bucket serves up under subject_to_key s
// is a real triple of the snapshot with exactly that subject.
// Unlike ig_wf_sp there is NO separator side condition to carry:
// subject_to_key is injective outright (its two-char tag separates
// the constructors and the label is carried whole --
// RDF.Indexed.KeyInjectivity.lemma_subject_to_key_injective), so
// build_indexed discharges this for EVERY graph
// (lemma_build_indexed_wf_subj in the same module).
let ig_wf_subj (ig : indexed_graph) : prop =
  forall (s : subject) (t : triple).
    List.Tot.memP t (bucket_lookup ig.ig_subj (subject_to_key s)) ==>
    List.Tot.memP t ig.ig_triples /\ t.s == s

// Every triple the object bucket serves up under the subject-shaped
// key `subject_to_key s` is a real triple of the snapshot whose
// object is exactly the term `s` denotes. ig_obj is keyed by
// term_to_key_opt (RDF.Indexed.fsti), which shares the I_/B_ key
// space with subject_to_key and omits only literals/triple-terms; the
// eq-rep-o rule only ever queries ig_obj via `subject_to_key` of a
// sameAs partner (never a literal), so this subject-shaped form is
// exactly what that rule's licensing proof needs -- no separator side
// condition either, mirroring ig_wf_subj. Strong discharge:
// RDF.Indexed.KeyInjectivity.lemma_build_indexed_wf_obj.
let ig_wf_obj (ig : indexed_graph) : prop =
  forall (s : subject) (t : triple).
    List.Tot.memP t (bucket_lookup ig.ig_obj (subject_to_key s)) ==>
    List.Tot.memP t ig.ig_triples /\ t.o == subject_to_term s

// Every triple the predicate-object bucket serves up under the
// composite key `po_key p s` (RDF.Indexed.fsti's total companion to
// `po_key_opt`) is a real triple of the snapshot with exactly that
// predicate, and whose object is exactly the term `s` denotes.
// Subject-shaped for the same reason `ig_wf_obj` is: po_key_opt is
// only ever `Some` on a non-literal object, and prp-ifp's
// `find_subjects_indexed` (RDF.Indexed.fsti) only reaches ig_po in
// that case; the literal-object fallback reads ig_pred instead. Unlike
// ig_wf_subj/ig_wf_obj, po_key is a COMPOSITE key (predicate ^
// separator ^ object-key, mirroring sp_key's own subject-key ^
// separator ^ predicate shape), so it needs a separator-freeness side
// condition to discharge for a concrete `build_indexed` snapshot --
// RDF.Indexed.KeyInjectivity.lemma_build_indexed_wf_po. This is the
// discharge OWL.RL.Refinement's owl_rule_inverse_functional_licensed
// consumes.
let ig_wf_po (ig : indexed_graph) : prop =
  forall (p : wf_iri) (s : subject) (t : triple).
    List.Tot.memP t (bucket_lookup ig.ig_po (po_key p s)) ==>
    List.Tot.memP t ig.ig_triples /\ t.p == p /\ t.o == subject_to_term s
