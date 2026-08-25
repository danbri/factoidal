/-
L4Factoidal.OWL.NegationGoals — entailment by refutation: negate a
PositiveEntailment conclusion graph into clash-seeking refutation
goals.

Port of `formal/fstar/Tableau.Refute.fst` §11a/11b (`negation_goals`
and its builders), step 2 of
https://github.com/danbri/factoidal/issues/586 .

## The soundness contract

For a premise `P` and a conclusion graph `C`, under OWL 2 Direct
Semantics:

    P ⊨ C   ⟺   P ∪ ¬C is UNSATISFIABLE.

A conclusion graph is the conjunction of its content assertions
`A₁ ⊓ … ⊓ Aₙ`, and `P ⊨ (A₁ ⊓ … ⊓ Aₙ)` iff `P ⊨ Aₖ` for every `k`.
So each conjunct is refuted SEPARATELY: goal `k` augments `P` with
`¬Aₖ` alone — never with the other conjuncts, because assuming an
unproven `Aⱼ` while proving `Aₖ` is the unsound direction. An
equivalence conclusion `C ≡ D` expands to the two subsumption goals
`C ⊑ D` and `D ⊑ C`, both required; likewise `P ≡ Q` for properties.
One unsupported conjunct collapses the whole conclusion to `none`
(conservative — the caller keeps its closure verdict).

`negationGoals` returns the CONJUNCTION of goals: the caller proves
the entailment iff `tableauConsistent (closure ++ goal) fuel` answers
`some false` for EVERY goal; a `some true` on any goal is a
countermodel (not entailed); otherwise the answer is indeterminate.

## The ¬p(x,y) encoding

The sound negation of a property assertion `s p o` (and the witness
half of a property subsumption `P ⊑ Q`) needs "x has no p-successor
equal to y" as a clash target the tableau can consume. It is encoded
as

    x rdf:type ObjectMaxCardinality(0, p, ObjectOneOf(y))

i.e. `x : ≤0 p.{y}`. In every model `{y}` denotes `{den(y)}`, so
`≤0 p.{y}` denotes exactly the individuals with no p-successor equal
to `y` — precisely `¬(⟨x,y⟩ ∈ EXT(p))`, nothing stronger (a bare
`≤0 p` would forbid ALL p-successors, which is unsound). The
tautology `y ∈ {y}` is asserted alongside so the filler filter
recognises `y`. A literal object is out of this encoding
(`owl:oneOf` of a literal is a data range) — such a conclusion falls
to `none`.

## Structural vs content triples

Class-expression scaffolding (restriction/list/declaration triples)
constrains nothing on its own; it is kept verbatim in EVERY goal so a
goal refuting a subsumption still has the defining structure of both
classes available. A named-subject `owl:complementOf` / `owl:unionOf`
/ `owl:intersectionOf` marker is an ASSERTED CLASS AXIOM, not
scaffolding (F* 2026-07-28 note: `WebOnt-I5.2-004`'s conclusion is
exactly `notA owl:complementOf A`); a bnode-subject marker builds an
anonymous expression and stays structural. Any predicate NOT
classified structural is treated as content — the safe
over-approximation, since a misclassification toward content can only
push the conclusion to `none`, never hide an assertion.
-/
import L4Factoidal.OWL.Refute

namespace L4Factoidal.OWL.Refute

open L4Factoidal.RDF
open L4Factoidal.OWL
open L4Factoidal.OWL.RL

/-! ## Vocabulary this module needs and `OWL/Vocabulary.lean` /
`OWL/Refute.lean` do not carry -/

def owlDatatypeProperty : WfIri :=
  ⟨"http://www.w3.org/2002/07/owl#DatatypeProperty", rfl⟩
def owlAnnotationProperty : WfIri :=
  ⟨"http://www.w3.org/2002/07/owl#AnnotationProperty", rfl⟩
def owlNamedIndividual : WfIri :=
  ⟨"http://www.w3.org/2002/07/owl#NamedIndividual", rfl⟩
def owlOntology : WfIri :=
  ⟨"http://www.w3.org/2002/07/owl#Ontology", rfl⟩
def owlDataRange : WfIri :=
  ⟨"http://www.w3.org/2002/07/owl#DataRange", rfl⟩
def rdfsClass : WfIri :=
  ⟨"http://www.w3.org/2000/01/rdf-schema#Class", rfl⟩
def rdfProperty : WfIri :=
  ⟨"http://www.w3.org/1999/02/22-rdf-syntax-ns#Property", rfl⟩
def owlDatatypeComplementOf : WfIri :=
  ⟨"http://www.w3.org/2002/07/owl#datatypeComplementOf", rfl⟩
def owlWithRestrictions : WfIri :=
  ⟨"http://www.w3.org/2002/07/owl#withRestrictions", rfl⟩
def owlOnProperties : WfIri :=
  ⟨"http://www.w3.org/2002/07/owl#onProperties", rfl⟩
def owlOnDataRange : WfIri :=
  ⟨"http://www.w3.org/2002/07/owl#onDataRange", rfl⟩

/-! ## Structural / content classification -/

/-- `rdf:type` objects that DECLARE rather than assert: membership in
    one of these is never the fact a PositiveEntailment conclusion is
    testing. `owl:Nothing` is deliberately absent — an
    `i rdf:type owl:Nothing` conclusion is a real, if degenerate,
    claim. Port of `is_meta_type_iri`. -/
def isMetaTypeIri (i : WfIri) : Bool :=
  i == owlClass || i == owlObjectProperty || i == owlDatatypeProperty
  || i == owlAnnotationProperty || i == owlNamedIndividual
  || i == owlRestriction || i == rdfsClass || i == rdfProperty
  || i == rdfsDatatype || i == owlDataRange || i == owlThing
  || i == owlOntology
  || i == owlFunctionalProperty || i == owlInverseFunctionalProperty
  || i == owlTransitiveProperty || i == owlSymmetricProperty
  || i == owlAsymmetricProperty || i == owlIrreflexiveProperty
  || i == owlReflexiveProperty

/-- A predicate that BUILDS a class expression / list / restriction,
    or wires a declaration — never itself the asserted fact of a PE
    conclusion. Port of `is_structural_predicate`. -/
def isStructuralPredicate (p : WfIri) : Bool :=
  p == owlOnProperty || p == owlSomeValuesFrom || p == owlAllValuesFrom
  || p == owlHasValue || p == owlOnClass || p == owlOnDataRange
  || p == owlCardinality || p == owlMinCardinality || p == owlMaxCardinality
  || p == owlQualifiedCardinality || p == owlMinQualifiedCardinality
  || p == owlMaxQualifiedCardinality || p == owlIntersectionOf
  || p == owlUnionOf || p == owlComplementOf || p == owlDatatypeComplementOf
  || p == owlOneOf || p == owlHasSelf || p == owlInverseOf
  || p == owlDistinctMembers || p == owlMembers
  || p == owlWithRestrictions || p == owlOnProperties
  || p == rdfFirst || p == rdfRest

/-- Port of `is_structural_triple`, including the named-subject
    boolean-marker exception (module header). -/
def isStructuralTriple (t : Triple) : Bool :=
  (t.p == rdfType &&
    (match t.o with
     | .iri c => isMetaTypeIri c
     | _      => false))
  || (if t.p == owlComplementOf || t.p == owlUnionOf || t.p == owlIntersectionOf
      then (match t.s with | .bnode _ => true | .iri _ => false)
      else isStructuralPredicate t.p)

/-- The content assertions of a conclusion graph. -/
def contentTriples (g : Graph) : List Triple :=
  g.filter (fun t => !isStructuralTriple t)

/-- The scaffolding — kept verbatim in every refutation goal. -/
def structuralTriples (g : Graph) : List Triple :=
  g.filter isStructuralTriple

/-- A single class-membership assertion of a NAMED individual in a
    non-meta class (IRI or anonymous class-expression bnode). -/
def isClassMembership (t : Triple) : Bool :=
  t.p == rdfType
  && (match t.s with | .iri _ => true | .bnode _ => false)
  && (match t.o with
      | .iri c   => !isMetaTypeIri c
      | .bnode _ => true
      | _        => false)

/-- OWL/RDFS axiom and equality/nominal vocabulary — never a plain
    object-property assertion whose ¬p(s,o) encoding would be
    meaningful. Port of `is_axiom_or_special_predicate`. -/
def isAxiomOrSpecialPredicate (p : WfIri) : Bool :=
  p == rdfType || p == rdfsSubClassOf || p == rdfsSubPropertyOf
  || p == owlEquivalentClass || p == owlEquivalentProperty
  || p == owlDisjointWith || p == owlSameAs || p == owlDifferentFrom
  || p == owlPropertyDisjointWith || p == rdfsDomain || p == rdfsRange

/-- A plain object-property assertion `s p o` (s an IRI, o a
    resource, p not axiom/nominal vocabulary): its sound negation is
    ¬p(s,o). -/
def isNegatablePropertyAssertion (t : Triple) : Bool :=
  (match t.s with | .iri _ => true | .bnode _ => false)
  && (match t.o with | .iri _ => true | .bnode _ => true | _ => false)
  && !isAxiomOrSpecialPredicate t.p

/-! ## Fresh bnode ids

The `__factoidal_` prefix is illegal in W3C fixtures / parser output,
so these never collide with premise or closure bnodes. Each
refutation goal is a SEPARATE graph handed to the refuter on its own,
so reusing one fixed id set across goals is safe. -/

def peNegClassBNode  : BNodeId := "__factoidal_pe_neg_class"
def peSubFreshBNode  : BNodeId := "__factoidal_pe_sub_witness"
def pePropABNode     : BNodeId := "__factoidal_pe_prop_a"
def pePropBBNode     : BNodeId := "__factoidal_pe_prop_b"
def pePropRestrBNode : BNodeId := "__factoidal_pe_prop_restr"
def pePropOneofBNode : BNodeId := "__factoidal_pe_prop_oneof"
def pePropListBNode  : BNodeId := "__factoidal_pe_prop_list"
def peNegClassBNodeB : BNodeId := "__factoidal_pe_neg_class_b"
def peBoolCeBNode    : BNodeId := "__factoidal_pe_bool_ce"

/-! ## Goal builders -/

/-- The triples encoding `sub rdf:type ObjectMaxCardinality(0, p,
    ObjectOneOf(m))` plus the tautology `m ∈ {m}`. Together they
    assert exactly ¬p(sub, m) — see the module header. `none` when
    `m` is a literal or triple term. The `"0"` bound is
    `Vocabulary.litNni0` (`"0"^^xsd:nonNegativeInteger`), the same
    literal the F* builder uses. -/
def negPairTriples (sub : Subject) (p : WfIri) (m : Term)
    : Option (List Triple) :=
  match termAsSubject m with
  | none => none
  | some mSubj =>
    let restr : Subject := .bnode pePropRestrBNode
    let oneof : Subject := .bnode pePropOneofBNode
    let lcell : Subject := .bnode pePropListBNode
    some [
      ⟨sub,   rdfType,                    .bnode pePropRestrBNode⟩,
      ⟨restr, rdfType,                    .iri owlRestriction⟩,
      ⟨restr, owlOnProperty,              .iri p⟩,
      ⟨restr, owlMaxQualifiedCardinality, .literal litNni0⟩,
      ⟨restr, owlOnClass,                 .bnode pePropOneofBNode⟩,
      ⟨oneof, rdfType,                    .iri owlClass⟩,
      ⟨oneof, owlOneOf,                   .bnode pePropListBNode⟩,
      ⟨lcell, rdfFirst,                   m⟩,
      ⟨lcell, rdfRest,                    .iri rdfNil⟩,
      ⟨mSubj, rdfType,                    .bnode pePropOneofBNode⟩ ]

/-- Refutation goal for a property SUBSUMPTION `P ⊑ Q`: a fresh pair
    ⟨a,b⟩ with `P(a,b)` and `a : ≤0 Q.{b}` (= ¬Q(a,b)). `b` is a
    bnode, so `negPairTriples` is always `some` here (the `none` arm
    is unreachable and degrades to the bare edge). -/
def propInclusionGoal (base : Graph) (p q : WfIri) : Graph :=
  let a : Subject := .bnode pePropABNode
  let b : Term := .bnode pePropBBNode
  let edge : Triple := ⟨a, p, b⟩
  match negPairTriples a q b with
  | some ts => (edge :: ts) ++ base
  | none    => edge :: base

/-- One content assertion → the refutation goals it expands to (a
    conjunction — every goal required). `none` = unsupported shape.
    Port of `negate_content_triple`; each arm's Direct Semantics
    soundness argument is in the F* original and summarised here. -/
def negateContentTriple (base : Graph) (t : Triple)
    : Option (List Graph) :=
  if isClassMembership t then
    -- (a) `i rdf:type C` → `i rdf:type ¬C`.
    let comp : Triple := ⟨.bnode peNegClassBNode, owlComplementOf, t.o⟩
    let member : Triple := ⟨t.s, rdfType, .bnode peNegClassBNode⟩
    some [comp :: member :: base]
  else if t.p == rdfsSubClassOf then
    -- (b) `C rdfs:subClassOf D` → fresh _:x with x ∈ C ⊓ ¬D.
    match termAsSubject t.o with
    | none   => none
    | some _ =>
      let x : Subject := .bnode peSubFreshBNode
      let inC : Triple := ⟨x, rdfType, t.s.toTerm⟩
      let comp : Triple := ⟨.bnode peNegClassBNode, owlComplementOf, t.o⟩
      let inNegD : Triple := ⟨x, rdfType, .bnode peNegClassBNode⟩
      some [inC :: comp :: inNegD :: base]
  else if t.p == owlEquivalentClass then
    -- `C ≡ D` → refute C ⊑ D and D ⊑ C, both required.
    match termAsSubject t.o with
    | none   => none
    | some _ =>
      let x : Subject := .bnode peSubFreshBNode
      let compD : Triple := ⟨.bnode peNegClassBNode, owlComplementOf, t.o⟩
      let g1 : Graph :=
        [ ⟨x, rdfType, t.s.toTerm⟩, compD,
          ⟨x, rdfType, .bnode peNegClassBNode⟩ ] ++ base
      let compC : Triple := ⟨.bnode peNegClassBNode, owlComplementOf, t.s.toTerm⟩
      let g2 : Graph :=
        [ ⟨x, rdfType, t.o⟩, compC,
          ⟨x, rdfType, .bnode peNegClassBNode⟩ ] ++ base
      some [g1, g2]
  else if t.p == rdfsSubPropertyOf then
    -- `P ⊑ Q` → one property-subsumption refutation goal.
    match t.s, t.o with
    | .iri p, .iri q => some [propInclusionGoal base p q]
    | _, _           => none
  else if t.p == owlEquivalentProperty then
    -- `P ≡ Q` → refute P ⊑ Q and Q ⊑ P.
    match t.s, t.o with
    | .iri p, .iri q =>
        some [propInclusionGoal base p q, propInclusionGoal base q p]
    | _, _           => none
  else if t.p == owlComplementOf then
    -- Named-subject `X owl:complementOf Y`: CEXT(X) = Δ \ CEXT(Y) —
    -- disjointness AND coverage. Negation is the disjunction
    -- ∃x.(x ∈ X ⊓ Y) ∨ ∃x.(x ∈ ¬X ⊓ ¬Y), and P ∪ (A ∨ B) is
    -- unsatisfiable iff P ∪ A and P ∪ B each are — two goals, both
    -- required, each asserting exactly its disjunct on a fresh
    -- individual.
    match termAsSubject t.o with
    | none   => none
    | some _ =>
      let x : Subject := .bnode peSubFreshBNode
      let g1 : Graph :=
        [ ⟨x, rdfType, t.s.toTerm⟩, ⟨x, rdfType, t.o⟩ ] ++ base
      let compS : Triple := ⟨.bnode peNegClassBNode, owlComplementOf, t.s.toTerm⟩
      let compO : Triple := ⟨.bnode peNegClassBNodeB, owlComplementOf, t.o⟩
      let g2 : Graph :=
        [ compS, ⟨x, rdfType, .bnode peNegClassBNode⟩,
          compO, ⟨x, rdfType, .bnode peNegClassBNodeB⟩ ] ++ base
      some [g1, g2]
  else if t.p == owlUnionOf || t.p == owlIntersectionOf then
    -- Named-subject boolean marker: the OWL 2 RDF mapping reads
    -- `S owl:unionOf (L)` as the class EQUALITY S ≡ CE(L) — refute
    -- S ⊑ CE(L) and CE(L) ⊑ S. A fresh bnode carrying the SAME
    -- marker over the SAME list stands for CE(L); the list cells are
    -- structural and already kept in `base`.
    match t.s with
    | .bnode _ => none  -- unreachable given the structural split
    | .iri _ =>
      let x : Subject := .bnode peSubFreshBNode
      let ce : Triple := ⟨.bnode peBoolCeBNode, t.p, t.o⟩
      let compCe : Triple :=
        ⟨.bnode peNegClassBNode, owlComplementOf, .bnode peBoolCeBNode⟩
      let g1 : Graph :=
        [ ce, ⟨x, rdfType, t.s.toTerm⟩,
          compCe, ⟨x, rdfType, .bnode peNegClassBNode⟩ ] ++ base
      let compS : Triple :=
        ⟨.bnode peNegClassBNodeB, owlComplementOf, t.s.toTerm⟩
      let g2 : Graph :=
        [ ce, ⟨x, rdfType, .bnode peBoolCeBNode⟩,
          compS, ⟨x, rdfType, .bnode peNegClassBNodeB⟩ ] ++ base
      some [g1, g2]
  else if isNegatablePropertyAssertion t then
    -- `s p o` → ¬p(s,o) on the existing named terms.
    match negPairTriples t.s t.p t.o with
    | none    => none
    | some ts => some [ts ++ base]
  else none

def negateContentList (base : Graph) : List Triple → Option (List Graph)
  | []      => some []
  | t :: tl =>
    match negateContentTriple base t with
    | none    => none
    | some gs =>
      match negateContentList base tl with
      | none      => none
      | some rest => some (gs ++ rest)

/-- The conjunction of refutation goals for a conclusion graph, or
    `none` when any content assertion is an unsupported shape
    (conservative: the caller keeps its closure verdict). The caller
    ANDs the refuter over the returned list — the entailment is
    proven iff EVERY goal refutes. Port of `negation_goals`. -/
def negationGoals (gC : Graph) : Option (List Graph) :=
  match contentTriples gC with
  | []  => none
  | cs  =>
    match negateContentList (structuralTriples gC) cs with
    | none          => none
    | some []       => none
    | some (g :: t) => some (g :: t)

end L4Factoidal.OWL.Refute
