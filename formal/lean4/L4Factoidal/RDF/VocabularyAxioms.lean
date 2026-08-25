/-
L4Factoidal.RDF.VocabularyAxioms — the W3C axiomatic triple tables.

Port of `formal/fstar/RDF.Vocabulary.Axioms.fst` (258 lines).

RDF 1.1 Semantics publishes finite tables of axiomatic triples
(<https://www.w3.org/TR/rdf11-mt/>, §"RDF axiomatic triples" and
§"RDFS axiomatic triples"). Before the F\* module they had no
declarative representation anywhere in the tree: their consequences were
hard-coded as closure rules and reflexivity axioms were harvested
programmatically. This is the tables as literal triple lists, auditable
line by line against the specification text without executing anything.

## What is deliberately NOT here

The genuinely INFINITE families, per the specification's own note on
infinitude:

- RDF: `rdf:_1 rdf:type rdf:Property`, `rdf:_2 …`, for all n;
- RDFS: `rdf:_1 rdf:type rdfs:ContainerMembershipProperty`,
  `rdf:_1 rdfs:domain rdfs:Resource`, `rdf:_1 rdfs:range rdfs:Resource`,
  and so on for all n.

Both stay rule-generated. The container-membership rule already emits
what it needs for whatever finite set of `rdf:_n` IRIs appears in a
given graph, and rule generation is CORRECT for an infinite family. Only
the finite tables belong here.

## ⚠️ The seed-graph gate: this table is NOT wired into any closure

Wiring `finiteAxiomaticTriples` into the RDFS closure as a seed graph
was attempted in the F\* tree and DISABLED after measurement. Every
suite stayed byte-exact except OWL 2 profile-RL ConsistencyTests, which
went from 76 pass, 0 fail to 75 pass, 1 fail:
`New-Feature-ObjectQCR-002` became an unexpected inconsistency.

The seeded schema axioms inflate the closure's `rdf:type` set through
rdfs2 and rdfs3 far enough to trip the sound-but-narrow N=1
qualified-cardinality complementOf scaffolding (issue #236) into a
spurious cls-com clash. That is an UNSOUNDNESS, not an improvement, so
the seed is off.

If re-attempting: the RDF-versus-RDFS regime split still applies. The
bare RDFS closure under the "RDF" regime must NOT receive the RDFS rows
of this table (`rdfs:domain rdfs:domain rdf:Property`, for instance),
because RDF Semantics scopes the two axiomatic sets to different
entailment regimes.

## How this file was produced

The two tables were extracted from the F\* source mechanically — the
`{ s = S_IRI …; p = …; o = T_IRI … }` rows parsed and re-emitted — not
retyped. A table whose whole purpose is line-by-line auditability
against a specification is the worst possible place for a transcription
slip, and 46 rows by hand is where one happens.
-/
import L4Factoidal.RDFS.Vocabulary

namespace L4Factoidal.RDF

open L4Factoidal.RDFS

/-! ## RDF axiomatic triples

<https://www.w3.org/TR/rdf11-mt/>, §"RDF axiomatic triples". Finite rows
only — the `rdf:_n` family is excluded, see the module header. -/

def rdfAxiomaticTriples : List Triple := [
  ⟨.iri rdfType, rdfType, .iri rdfProperty⟩,
  ⟨.iri rdfSubject, rdfType, .iri rdfProperty⟩,
  ⟨.iri rdfPredicate, rdfType, .iri rdfProperty⟩,
  ⟨.iri rdfObject, rdfType, .iri rdfProperty⟩,
  ⟨.iri rdfFirst, rdfType, .iri rdfProperty⟩,
  ⟨.iri rdfRest, rdfType, .iri rdfProperty⟩,
  ⟨.iri rdfValue, rdfType, .iri rdfProperty⟩,
  ⟨.iri rdfNil, rdfType, .iri rdfList⟩
]

/-! ## RDFS axiomatic triples

<https://www.w3.org/TR/rdf11-mt/>, §"RDFS axiomatic triples". Same
exclusion, same reason. -/

def rdfsAxiomaticTriples : List Triple := [
  ⟨.iri rdfType, rdfsDomain, .iri rdfsResource⟩,
  ⟨.iri rdfsDomain, rdfsDomain, .iri rdfProperty⟩,
  ⟨.iri rdfsRange, rdfsDomain, .iri rdfProperty⟩,
  ⟨.iri rdfsSubPropertyOf, rdfsDomain, .iri rdfProperty⟩,
  ⟨.iri rdfsSubClassOf, rdfsDomain, .iri rdfsClass⟩,
  ⟨.iri rdfSubject, rdfsDomain, .iri rdfStatement⟩,
  ⟨.iri rdfPredicate, rdfsDomain, .iri rdfStatement⟩,
  ⟨.iri rdfObject, rdfsDomain, .iri rdfStatement⟩,
  ⟨.iri rdfsMember, rdfsDomain, .iri rdfsResource⟩,
  ⟨.iri rdfFirst, rdfsDomain, .iri rdfList⟩,
  ⟨.iri rdfRest, rdfsDomain, .iri rdfList⟩,
  ⟨.iri rdfsSeeAlso, rdfsDomain, .iri rdfsResource⟩,
  ⟨.iri rdfsIsDefinedBy, rdfsDomain, .iri rdfsResource⟩,
  ⟨.iri rdfsComment, rdfsDomain, .iri rdfsResource⟩,
  ⟨.iri rdfsLabel, rdfsDomain, .iri rdfsResource⟩,
  ⟨.iri rdfValue, rdfsDomain, .iri rdfsResource⟩,
  ⟨.iri rdfType, rdfsRange, .iri rdfsClass⟩,
  ⟨.iri rdfsDomain, rdfsRange, .iri rdfsClass⟩,
  ⟨.iri rdfsRange, rdfsRange, .iri rdfsClass⟩,
  ⟨.iri rdfsSubPropertyOf, rdfsRange, .iri rdfProperty⟩,
  ⟨.iri rdfsSubClassOf, rdfsRange, .iri rdfsClass⟩,
  ⟨.iri rdfSubject, rdfsRange, .iri rdfsResource⟩,
  ⟨.iri rdfPredicate, rdfsRange, .iri rdfsResource⟩,
  ⟨.iri rdfObject, rdfsRange, .iri rdfsResource⟩,
  ⟨.iri rdfsMember, rdfsRange, .iri rdfsResource⟩,
  ⟨.iri rdfFirst, rdfsRange, .iri rdfsResource⟩,
  ⟨.iri rdfRest, rdfsRange, .iri rdfList⟩,
  ⟨.iri rdfsSeeAlso, rdfsRange, .iri rdfsResource⟩,
  ⟨.iri rdfsIsDefinedBy, rdfsRange, .iri rdfsResource⟩,
  ⟨.iri rdfsComment, rdfsRange, .iri rdfsLiteral⟩,
  ⟨.iri rdfsLabel, rdfsRange, .iri rdfsLiteral⟩,
  ⟨.iri rdfValue, rdfsRange, .iri rdfsResource⟩,
  ⟨.iri rdfAlt, rdfsSubClassOf, .iri rdfsContainer⟩,
  ⟨.iri rdfBag, rdfsSubClassOf, .iri rdfsContainer⟩,
  ⟨.iri rdfSeq, rdfsSubClassOf, .iri rdfsContainer⟩,
  ⟨.iri rdfsContainerMembershipProperty, rdfsSubClassOf, .iri rdfProperty⟩,
  ⟨.iri rdfsIsDefinedBy, rdfsSubPropertyOf, .iri rdfsSeeAlso⟩,
  ⟨.iri rdfsDatatype, rdfsSubClassOf, .iri rdfsClass⟩
]

/-! ## The combined finite seed graph

8 RDF rows plus 38 RDFS rows. Not consumed anywhere —
see the seed-graph gate in the module header. -/

def finiteAxiomaticTriples : List Triple :=
  rdfAxiomaticTriples ++ rdfsAxiomaticTriples

/-! ## Build-time checks

### The row counts are pinned

The F\* module's own comment says "46 triples: 8 RDF + 38 RDFS". A
dropped row is the failure mode a table like this has, and nothing else
would notice one. -/

#guard rdfAxiomaticTriples.length == 8
#guard rdfsAxiomaticTriples.length == 38
#guard finiteAxiomaticTriples.length == 46

/-! ### No duplicates

A copy-paste that repeated a row would keep the count right only if it
also dropped one, but a duplicate on its own inflates the count AND is
worth catching directly. -/

#guard (finiteAxiomaticTriples.map (fun t => toString (repr t))).eraseDups.length
        == finiteAxiomaticTriples.length

/-! ### Spot checks against the specification text

Four rows read straight off the W3C tables. They are not a substitute
for reading the list, which is the point of the module; they catch a
systematic error such as subject and object being swapped. -/

#guard finiteAxiomaticTriples.any (fun t =>
  t.s == Subject.iri rdfType && t.p == rdfType && t.o == Term.iri rdfProperty)
#guard finiteAxiomaticTriples.any (fun t =>
  t.s == Subject.iri rdfNil && t.p == rdfType && t.o == Term.iri rdfList)
#guard finiteAxiomaticTriples.any (fun t =>
  t.s == Subject.iri rdfsIsDefinedBy && t.p == rdfsSubPropertyOf
  && t.o == Term.iri rdfsSeeAlso)
#guard finiteAxiomaticTriples.any (fun t =>
  t.s == Subject.iri rdfsDatatype && t.p == rdfsSubClassOf
  && t.o == Term.iri rdfsClass)

/-! ### The infinite families are ABSENT

`rdf:_1` must not appear. If it did, the table would be claiming to
enumerate an infinite set, and the container-membership rule would then
be duplicating it. -/

#guard !finiteAxiomaticTriples.any (fun t =>
  ((toString (repr t)).splitOn "22-rdf-syntax-ns#_1").length > 1)

end L4Factoidal.RDF
