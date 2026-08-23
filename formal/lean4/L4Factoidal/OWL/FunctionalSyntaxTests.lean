/-
L4Factoidal.OWL.FunctionalSyntaxTests — build-time checks for the
functional-syntax subset parser.

Each check shows one axiom form and the triples the OWL 2 Mapping to
RDF Graphs tables turn it into.
-/
import L4Factoidal.OWL.FunctionalSyntax

namespace L4Factoidal.OWL.FS

open L4Factoidal.RDF
open L4Factoidal.OWL.RL

private def countOf (doc : String) : Nat :=
  match parseFunctionalSyntax doc with
  | some ts => ts.length
  | none    => 0

private def hasT (doc : String) (t : Triple) : Bool :=
  match parseFunctionalSyntax doc with
  | some ts => ts.any (fun u => u == t)
  | none    => false

private def readable (doc : String) : Bool := (parseFunctionalSyntax doc).isSome

private def exA : WfIri := ⟨"http://e/a", rfl⟩
private def exC : WfIri := ⟨"http://e/C", rfl⟩
private def exP : WfIri := ⟨"http://e/p", rfl⟩

/-! ## Declarations and prefixes

An abbreviated name resolves through the `Prefix(` declarations,
including the EMPTY prefix. -/

private def docDecl : String :=
  "Prefix( : = <http://e/> )\nOntology( Declaration(Class(:C)) )"

#guard hasT docDecl ⟨.iri exC, rdfType, .iri owlClass⟩
#guard countOf docDecl == 1

private def docFull : String :=
  "Ontology( Declaration(NamedIndividual(<http://e/a>)) )"

#guard hasT docFull ⟨.iri exA, rdfType, .iri owlNamedIndividualIri⟩

/-! ## `ClassAssertion(DataHasValue(p "v"^^xsd:string) a)`

The restriction gets its own blank node carrying the three triples
the mapping table names, and the individual is typed with it. -/

private def docHasValue : String :=
  "Prefix( : = <http://e/> )\nPrefix( xsd: = <http://www.w3.org/2001/XMLSchema#> )\n" ++
  "Ontology( ClassAssertion(DataHasValue(:p \"v\"^^xsd:string) :a) )"

#guard countOf docHasValue == 4
#guard hasT docHasValue ⟨bnRestriction 0, rdfType, .iri owlRestriction⟩
#guard hasT docHasValue ⟨bnRestriction 0, owlOnProperty, .iri exP⟩
#guard hasT docHasValue ⟨.iri exA, rdfType, .bnode "owlfs_restr0"⟩

/-! ## `TransitiveObjectProperty` and `DataPropertyRange` -/

private def docTrans : String :=
  "Prefix( : = <http://e/> )\nOntology( TransitiveObjectProperty(:p) )"

#guard hasT docTrans ⟨.iri exP, rdfType, .iri owlTransitiveProperty⟩

private def docRange : String :=
  "Prefix( : = <http://e/> )\nPrefix( xsd: = <http://www.w3.org/2001/XMLSchema#> )\n" ++
  "Ontology( DataPropertyRange(:p xsd:integer) )"

#guard readable docRange
#guard countOf docRange == 1

/-! ## `SubObjectPropertyOf(ObjectPropertyChain(p q) r)`

The chain becomes an `rdf:first`/`rdf:rest` list bound to the
super-property. Five triples: two cells, two `rdf:rest`, one
`owl:propertyChainAxiom`. -/

private def docChain : String :=
  "Prefix( : = <http://e/> )\n" ++
  "Ontology( SubObjectPropertyOf(ObjectPropertyChain(:p :q) :r) )"

#guard countOf docChain == 5
#guard hasT docChain ⟨bnChain 0, rdfFirst, .iri exP⟩

/-! ## `DatatypeRestriction` — each facet pair is its OWN blank node

The mapping specification says a facet-restriction node carries
exactly one triple, so a two-facet restriction needs two facet nodes
and two list cells, not one node with two facets on it. -/

private def docFacet : String :=
  "Prefix( : = <http://e/> )\nPrefix( xsd: = <http://www.w3.org/2001/XMLSchema#> )\n" ++
  "Ontology( DataPropertyRange(:p " ++
  "DatatypeRestriction(xsd:integer xsd:minInclusive \"1\"^^xsd:integer)) )"

-- `DataPropertyRange` takes two IRIs, so a DatatypeRestriction in
-- that position is OUTSIDE this subset and is declined, not guessed.
#guard !(readable docFacet)

private def docFacetSome : String :=
  "Prefix( : = <http://e/> )\nPrefix( xsd: = <http://www.w3.org/2001/XMLSchema#> )\n" ++
  "Ontology( ClassAssertion(DataSomeValuesFrom(:p " ++
  "DatatypeRestriction(xsd:integer xsd:minInclusive \"1\"^^xsd:integer)) :a) )"

#guard readable docFacetSome
-- 1 facet triple + 2 list-cell triples + 3 datatype triples
-- + 3 restriction triples + 1 class assertion.
#guard countOf docFacetSome == 10

/-! ## What the parser declines

A construct outside the subset is a CLEAN failure, never a graph with
the axiom silently missing — a missing axiom makes an inconsistent
ontology look consistent. -/

#guard !(readable "Ontology( ObjectPropertyDomain(<http://e/p> <http://e/C>) )")
#guard !(readable "Prefix( : = <http://e/> )\nOntology( Declaration(Class(:C))")
#guard !(readable "Declaration(Class(<http://e/C>))")

/-! A literal with no datatype is outside the subset, and is declined
    rather than given a guessed `xsd:string`. -/
#guard !(readable "Prefix( : = <http://e/> )\nOntology( DataPropertyAssertion(:p :a \"v\") )")

end L4Factoidal.OWL.FS
