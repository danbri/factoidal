/-
L4Factoidal.OWL.ClassExpr — OWL 2 class expressions, read out of an
RDF graph.

Port of the class-expression AST and parser of
`formal/fstar/Tableau.fst` (§§2–4). Spec: OWL 2 Mapping to RDF Graphs
(https://www.w3.org/TR/owl2-mapping-to-rdf/), which says which
triples on a blank node denote which class expression.

This is the shared front end of the DL reasoner: both the positive
materialisation and the refutation calculus read the same AST, so a
disagreement between them about what a restriction MEANS is
impossible by construction.

## An unreadable expression is `unknown`, never a guess

`ClassExpr.unknown` is what the parser emits when it does not
recognise the shape, when the fuel runs out, or when a cardinality
lexeme is not a run of digits. Every consumer answers `none` —
"I do not know" — for it, and `none` is always sound under the open
world assumption. A parser that guessed would make the reasoner
answer a question it had not read.
-/
import L4Factoidal.OWL.RLClosureIndexed

namespace L4Factoidal.OWL

open L4Factoidal.RDF
open L4Factoidal.OWL.RL

/-! ## Vocabulary this module needs beyond `Vocabulary.lean`

The datatype-restriction markers. They are file-local for the same
reason the F* module keeps them local: `Vocabulary.lean` is shared by
many consumers and these three have exactly one. -/

def owlOnDatatype : WfIri := ⟨"http://www.w3.org/2002/07/owl#onDatatype", rfl⟩
def owlWithRestrictions : WfIri :=
  ⟨"http://www.w3.org/2002/07/owl#withRestrictions", rfl⟩
def owlDatatypeComplementOf : WfIri :=
  ⟨"http://www.w3.org/2002/07/owl#datatypeComplementOf", rfl⟩
def owlMinQualifiedCardinality : WfIri :=
  ⟨"http://www.w3.org/2002/07/owl#minQualifiedCardinality", rfl⟩
def owlQualifiedCardinality : WfIri :=
  ⟨"http://www.w3.org/2002/07/owl#qualifiedCardinality", rfl⟩
def owlCardinality : WfIri := ⟨"http://www.w3.org/2002/07/owl#cardinality", rfl⟩

/-- The four ordering facets. `pattern` and the length facets are out
    of scope here and are simply absent from a parse, never guessed
    at. -/
def facetMinInclusive : WfIri :=
  ⟨"http://www.w3.org/2001/XMLSchema#minInclusive", rfl⟩
def facetMaxInclusive : WfIri :=
  ⟨"http://www.w3.org/2001/XMLSchema#maxInclusive", rfl⟩
def facetMinExclusive : WfIri :=
  ⟨"http://www.w3.org/2001/XMLSchema#minExclusive", rfl⟩
def facetMaxExclusive : WfIri :=
  ⟨"http://www.w3.org/2001/XMLSchema#maxExclusive", rfl⟩

def orderingFacets : List WfIri :=
  [facetMinInclusive, facetMaxInclusive, facetMinExclusive, facetMaxExclusive]

/-! ## The AST -/

/-- An OWL 2 class expression, in the fragment the reasoner reads. -/
inductive ClassExpr where
  | named        (c : WfIri)
  /-- `∃ P. C` — `owl:someValuesFrom`. -/
  | someOf       (p : WfIri) (c : ClassExpr)
  /-- `∀ P. C` — `owl:allValuesFrom`. -/
  | allOf        (p : WfIri) (c : ClassExpr)
  /-- `∃ P. {v}` — `owl:hasValue`. -/
  | hasValue     (p : WfIri) (v : Term)
  /-- `C1 ⊓ C2 ⊓ …`. An empty list is `owl:Thing`. -/
  | intersection (cs : List ClassExpr)
  /-- `C1 ⊔ C2 ⊔ …`. -/
  | union        (cs : List ClassExpr)
  /-- `¬ C`, from `owl:complementOf` or `owl:datatypeComplementOf` —
      the two produce the same shape and nothing downstream needs to
      know which predicate it came from. -/
  | complement   (c : ClassExpr)
  | minCard      (n : Nat) (p : WfIri)
  | maxCard      (n : Nat) (p : WfIri)
  | exactCard    (n : Nat) (p : WfIri)
  | minQualCard  (n : Nat) (p : WfIri) (c : ClassExpr)
  | maxQualCard  (n : Nat) (p : WfIri) (c : ClassExpr)
  | exactQualCard (n : Nat) (p : WfIri) (c : ClassExpr)
  /-- `owl:oneOf {a1, …, am}`. The members are INDIVIDUALS, not
      nested class expressions, so the parser does not recurse into
      them — the same choice `hasValue` makes. -/
  | oneOf        (vs : List Term)
  /-- `DatatypeRestriction(DT F1 v1 …)`: the base datatype and the
      raw (facet IRI, value) pairs the graph carries. -/
  | dataRestriction (dt : WfIri) (facets : List (WfIri × Term))
  /-- The parser did not recognise the shape. Every consumer answers
      "I do not know" for this. -/
  | unknown
deriving Repr, Inhabited

/-! ## Structural comparison

`ClassExpr` is a NESTED inductive (`List ClassExpr` in
`intersection`/`union`), so no `DecidableEq` deriving handler applies.
Rather than hand-write one, this is a named Boolean comparison used
EXPLICITLY at the two places that need it — the complement clash and
the witness-reuse check. Nothing gets an anonymous `==` on a class
expression, which is what keeps a structural comparison from being
mistaken for a semantic one: two different expressions can denote the
same class, and `beq` says nothing about that. -/

mutual

def ClassExpr.beq : ClassExpr → ClassExpr → Bool
  | .named a,          .named b          => a == b
  | .unknown,          .unknown          => true
  | .hasValue p v,     .hasValue q w     => p == q && v == w
  | .oneOf a,          .oneOf b          => a == b
  | .dataRestriction d f, .dataRestriction e h => d == e && f == h
  | .minCard n p,      .minCard m q      => n == m && p == q
  | .maxCard n p,      .maxCard m q      => n == m && p == q
  | .exactCard n p,    .exactCard m q    => n == m && p == q
  | .complement a,     .complement b     => ClassExpr.beq a b
  | .someOf p a,       .someOf q b       => p == q && ClassExpr.beq a b
  | .allOf p a,        .allOf q b        => p == q && ClassExpr.beq a b
  | .minQualCard n p a, .minQualCard m q b => n == m && p == q && ClassExpr.beq a b
  | .maxQualCard n p a, .maxQualCard m q b => n == m && p == q && ClassExpr.beq a b
  | .exactQualCard n p a, .exactQualCard m q b => n == m && p == q && ClassExpr.beq a b
  | .intersection a,   .intersection b   => ClassExpr.beqList a b
  | .union a,          .union b          => ClassExpr.beqList a b
  | _,                 _                 => false

def ClassExpr.beqList : List ClassExpr → List ClassExpr → Bool
  | [],      []      => true
  | x :: xs, y :: ys => ClassExpr.beq x y && ClassExpr.beqList xs ys
  | _,       _       => false

end
/-! ## Reading a class expression out of a graph -/

/-- The first object of `(s, p, ·)`, or `none`. -/
def firstObject (st : Store) (s : Subject) (p : WfIri) : Option Term :=
  (st.withSubjPred s p).head?.map (·.o)

def termAsSubject : Term → Option Subject
  | .iri i   => some (.iri i)
  | .bnode b => some (.bnode b)
  | _        => none

/-- Walk an RDF collection, returning its elements in order. Fuel
    bounds the walk; a cell that reuses a node cannot outrun the
    graph's own length. -/
def walkRdfList (st : Store) : Term → Nat → List Term
  | _,    0     => []
  | head, n + 1 =>
      match head with
      | .iri _ => []
      | _ =>
        match termAsSubject head with
        | none => []
        | some s =>
            match firstObject st s rdfFirst, firstObject st s rdfRest with
            | some h, some t => h :: walkRdfList st t n
            | _, _           => []

/-- A cardinality lexeme is a run of ASCII digits. Anything else is
    `none`, which makes the parse `unknown` — sound under the open
    world, where a restriction nobody could read constrains nothing. -/
def cardinalityOfLexeme (s : String) : Option Nat :=
  let cs := s.toList
  if cs.isEmpty then none
  else cs.foldl (fun acc c =>
    acc.bind (fun n =>
      if '0' ≤ c && c ≤ '9' then some (n * 10 + (c.toNat - '0'.toNat)) else none))
    (some 0)

def cardinalityValue (st : Store) (s : Subject) (p : WfIri) : Option Nat :=
  match firstObject st s p with
  | some (.literal l) => cardinalityOfLexeme l.val.lexicalForm
  | _                 => none

/-- One `owl:withRestrictions` element is a blank node carrying
    exactly one `<facetIRI> <value>` triple. The four ordering facets
    are probed by name — four lookups, and an unrecognised facet is
    simply absent from the result rather than guessed at. -/
def facetPairsOf (st : Store) (heads : List Term) : List (WfIri × Term) :=
  heads.flatMap (fun h =>
    match termAsSubject h with
    | none   => []
    | some s => orderingFacets.filterMap (fun f =>
        (firstObject st s f).map (fun v => (f, v))))

mutual

/-- Read the class expression a term denotes.

    The dispatch ORDER is the F* module's, and it matters:
    `owl:intersectionOf`, then `owl:unionOf`, then `owl:oneOf`, then
    the datatype markers, then `owl:complementOf`, and only then the
    `owl:onProperty` restriction shapes. A blank node carrying both a
    Boolean marker and a restriction marker is malformed; reading the
    Boolean one first is what the mapping specification's own
    ordering says. -/
def parseClassExpr (st : Store) (t : Term) (fuel : Nat) : ClassExpr :=
  match fuel with
  | 0 => .unknown
  | n + 1 =>
    match t with
    | .iri i => .named i
    | .bnode _ =>
      (match termAsSubject t with
       | none => .unknown
       | some s => parseCeMarkers st s n)
    | _ => .unknown
termination_by 3 * fuel

/-- The class expression a SUBJECT's OWN markers denote, with `n` the
    already-decremented fuel.

    Split out of `parseClassExpr` because a NAMED class expression
    exists: OWL 2 RDF-Based semantics lets an IRI subject carry
    `owl:onProperty` / `owl:unionOf` / `owl:intersectionOf` and denote
    exactly that class. `parseClassExpr` maps every IRI straight to
    `named` — correct where an IRI appears as a FILLER, since the
    filler's own definition is the closure's business — so it can
    never see those markers. Reading them needs this entry. -/
def parseCeMarkers (st : Store) (s : Subject) (n : Nat) : ClassExpr :=
         match firstObject st s owlIntersectionOf with
         | some head => .intersection (parseClassExprList st (walkRdfList st head (n + 1)) n)
         | none =>
         match firstObject st s owlUnionOf with
         | some head => .union (parseClassExprList st (walkRdfList st head (n + 1)) n)
         | none =>
         match firstObject st s owlOneOf with
         | some head => .oneOf (walkRdfList st head (n + 1))
         | none =>
         match firstObject st s owlOnDatatype with
         | some (.iri baseDt) =>
             (match firstObject st s owlWithRestrictions with
              | some head =>
                  .dataRestriction baseDt (facetPairsOf st (walkRdfList st head (n + 1)))
              | none => .dataRestriction baseDt [])
         | _ =>
         match firstObject st s owlComplementOf with
         | some c => .complement (parseClassExpr st c n)
         | none =>
         match firstObject st s owlDatatypeComplementOf with
         | some c => .complement (parseClassExpr st c n)
         | none =>
         match firstObject st s owlOnProperty with
         | some (.iri p) =>
             (match firstObject st s owlSomeValuesFrom with
              | some c => .someOf p (parseClassExpr st c n)
              | none =>
              match firstObject st s owlAllValuesFrom with
              | some c => .allOf p (parseClassExpr st c n)
              | none =>
              match firstObject st s owlHasValue with
              | some v => .hasValue p v
              | none =>
              match cardinalityValue st s owlMinQualifiedCardinality with
              | some k =>
                  (match firstObject st s owlOnClass with
                   | some c => .minQualCard k p (parseClassExpr st c n)
                   | none   => .minCard k p)
              | none =>
              match cardinalityValue st s owlMaxQualifiedCardinality with
              | some k =>
                  (match firstObject st s owlOnClass with
                   | some c => .maxQualCard k p (parseClassExpr st c n)
                   | none   => .maxCard k p)
              | none =>
              match cardinalityValue st s owlQualifiedCardinality with
              | some k =>
                  (match firstObject st s owlOnClass with
                   | some c => .exactQualCard k p (parseClassExpr st c n)
                   | none   => .exactCard k p)
              | none =>
              match cardinalityValue st s owlMinCardinality with
              | some k => .minCard k p
              | none =>
              match cardinalityValue st s owlMaxCardinality with
              | some k => .maxCard k p
              | none =>
              match cardinalityValue st s owlCardinality with
              | some k => .exactCard k p
              | none   => .unknown)
         | _ => .unknown
termination_by 3 * n + 2

def parseClassExprList (st : Store) (ts : List Term) (fuel : Nat)
    : List ClassExpr :=
  ts.map (fun t => parseClassExpr st t fuel)
termination_by 3 * fuel + 1

end

/-- The class expression a SUBJECT denotes, read from its OWN
    markers.

    This is NOT `parseClassExpr` applied to the subject as a term. For
    an IRI subject that function answers `named` without looking at
    anything, so a NAMED restriction — `z owl:onProperty p ;
    owl:someValuesFrom C`, which OWL 2 RDF-Based semantics says
    denotes exactly `∃ p. C` — came back as the opaque class `z` and
    every membership it entails went unwritten. A subject with no
    markers at all still falls back to `named` for an IRI, which is
    what it denotes, and to `unknown` for a blank node, which denotes
    nothing this reader can name. -/
def parseCeOfSubject (st : Store) (s : Subject) : ClassExpr :=
  match parseCeMarkers st s (st.graph.length + 8) with
  | .unknown => (match s with
                 | .iri i   => .named i
                 | .bnode _ => .unknown)
  | ce       => ce

end L4Factoidal.OWL
