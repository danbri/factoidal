/-
L4Factoidal.OWL.QueryMaterialise — query-time materialisation for the
maximum-qualified-cardinality-one class expression.

## The defect this repairs

`SELECT * WHERE { ?parent a [ a owl:Restriction ; owl:onProperty
:hasChild ; owl:maxQualifiedCardinality "1"^^xsd:nonNegativeInteger ;
owl:onClass :Female ] }` (the W3C entailment-regime test `parent7`)
returned 0 rows through `evalSelectOwl`; the correct answer is one row.

The rewrite (`QueryRewriteExpand`, the `cardN == 1` qualified branch)
turns that pattern into a search for a node in the DATA carrying the
restriction's four shape triples, plus a membership triple and the
anchor. The F\* engine satisfies that search because its closure
materialises a canonical restriction node and types individuals into it
— over-broadly, which is what the anchor then filters
(<https://github.com/danbri/factoidal/issues/236>). The Lean closure
materialises no such node, so the rewritten query matched nothing.

## The repair, and why it is sound

Before evaluation, for each maximum-qualified-cardinality-one shape in
the QUERY's basic graph patterns, add to the default graph one fresh
canonical node carrying the four shape triples, and one membership
triple per individual whose membership `Mat.isMember` PROVES — the
filler-bound rule from `Materialise.lean`: an individual inside
`∀ p. {a₁ … a_m}` with `m ≤ 1` has at most one distinct `p`-filler in
any model. Every added membership is entailed, so adding it cannot
create a row a model could refuse; individuals whose membership is
unprovable are not added, so no spurious rows appear — the two wrongs
of the F\* route (over-typing, then anchor-filtering) are replaced by
one sound step.

ⓘ Scope: basic graph patterns reachable without entering a sub-SELECT.
A counting class expression inside a sub-SELECT keeps the old
behaviour (no canonical node, no rows) rather than a wrong one.

No `sorry`, no user `axiom`, no `native_decide`.
-/
import L4Factoidal.OWL.QueryRewriteNested
import L4Factoidal.OWL.Materialise

namespace L4Factoidal.OWL.QueryMaterialise

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.OWL
open L4Factoidal.OWL.RL
open L4Factoidal.OWL.QueryRewriteCore

/-- Every basic graph pattern reachable without entering a
sub-SELECT. -/
def bgpsOf : QueryPattern → List Bgp
  | .bgp b => [b]
  | .join l r => bgpsOf l ++ bgpsOf r
  | .union l r => bgpsOf l ++ bgpsOf r
  | .minus l r => bgpsOf l ++ bgpsOf r
  | .lateral l r => bgpsOf l ++ bgpsOf r
  | .leftJoin l r _ => bgpsOf l ++ bgpsOf r
  | .filter _ p => bgpsOf p
  | .graph _ p => bgpsOf p
  | .bind _ _ p => bgpsOf p
  | .service _ _ p => bgpsOf p
  | .serviceVar _ _ p => bgpsOf p
  | _ => []

/-- The maximum-qualified-cardinality-one shapes of one basic graph
pattern: marker label, property, filler class. The conditions mirror
the rewrite's own branch — cardinality exactly one, property an IRI,
`owl:onClass` an IRI — so augmentation fires exactly where the
rewrite's shape search will look. -/
def maxQc1Shapes (b : Bgp) : List (String × WfIri × WfIri) :=
  (b.filterMap (fun tp =>
    match tp.s, tp.p with
    | .bnode k, .iri p =>
        if p == owlOnProperty then some k else none
    | _, _ => none)).eraseDups.filterMap (fun k =>
      match (bgpFindFirstObj b k owlOnProperty).bind patternIri,
            cardValue b k owlMaxCardinality owlMaxQualifiedCardinality,
            (bgpFindFirstObj b k owlOnClass).bind patternIri with
      | some p, some 1, some c => some (k, p, c)
      | _, _, _ => none)

def canonLabel (k : String) : BNodeId := "_mxqc1canon_" ++ k

/-- The candidate individuals: every subject of the graph, once. -/
def subjectsOf (g : Graph) : List Subject :=
  (g.map (·.s)).eraseDups

/-- The canonical node for one shape, with its proved members. -/
def canonTriples (g : Graph) (k : String) (p c : WfIri) : List Triple :=
  let canon : Subject := .bnode (canonLabel k)
  let st := RL.Store.ofGraph g
  let ce : ClassExpr := .maxQualCard 1 p (.named c)
  let shape : List Triple :=
    [ ⟨canon, rdfType, .iri owlRestriction⟩,
      ⟨canon, owlOnProperty, .iri p⟩,
      ⟨canon, owlMaxQualifiedCardinality, .literal oneNonNegIntegerLiteral⟩,
      ⟨canon, owlOnClass, .iri c⟩ ]
  let members : List Triple :=
    (subjectsOf g).filterMap (fun i =>
      if Mat.isMember st i ce (g.length + 64) == some true
      then some ⟨i, rdfType, Term.bnode (canonLabel k)⟩ else none)
  shape ++ members

/-- Augment the dataset's default graph for every
maximum-qualified-cardinality-one shape in the query. A query with no
such shape leaves the dataset unchanged. -/
def augmentForQuery (ds : Dataset) (q : Query) : Dataset :=
  let shapes := ((bgpsOf q.pattern).flatMap maxQc1Shapes).eraseDups
  match shapes with
  | [] => ds
  | _ =>
      { ds with default :=
          ds.default ++ shapes.flatMap (fun (k, p, c) =>
            canonTriples ds.default k p c) }

/-! ## Build-time checks -/

/-! A query pattern with no restriction shape changes nothing. -/
#guard
  ((augmentForQuery { Dataset.empty with default := [] }
      (mkQuery (.select .all) (.bgp []))).default.length == 0)

end L4Factoidal.OWL.QueryMaterialise
