/-
L4Factoidal.OWL.ClassExprTests — build-time checks for the
class-expression reader.

Each check states one rule of the OWL 2 Mapping to RDF Graphs and
shows the triples that carry it.
-/
import L4Factoidal.OWL.ClassExpr

namespace L4Factoidal.OWL

open L4Factoidal.RDF
open L4Factoidal.OWL.RL

private def exC : WfIri := ⟨"http://e/C", rfl⟩
private def exD : WfIri := ⟨"http://e/D", rfl⟩
private def exP : WfIri := ⟨"http://e/P", rfl⟩

private def bn (b : String) : Subject := .bnode b
private def bnT (b : String) : Term := .bnode b

private def nni : WfIri := ⟨"http://www.w3.org/2001/XMLSchema#nonNegativeInteger", rfl⟩

private def lit (s : String) : Term :=
  .literal ⟨{ lexicalForm := s, datatype := nni, langTag := none, direction := none },
            by simp [literalWf, nni, rdfLangString, rdfDirLangString, Subtype.ext_iff]⟩

private def storeOf (g : Graph) : Store := Store.ofGraph g

/-! ## `owl:someValuesFrom` -/

private def gSome : Graph :=
  [ ⟨bn "r", owlOnProperty, .iri exP⟩,
    ⟨bn "r", owlSomeValuesFrom, .iri exC⟩ ]

#guard ClassExpr.beq (parseCeOfSubject (storeOf gSome) (bn "r"))
                     (.someOf exP (.named exC))

/-! ## `owl:allValuesFrom` -/

private def gAll : Graph :=
  [ ⟨bn "r", owlOnProperty, .iri exP⟩,
    ⟨bn "r", owlAllValuesFrom, .iri exC⟩ ]

#guard ClassExpr.beq (parseCeOfSubject (storeOf gAll) (bn "r"))
                     (.allOf exP (.named exC))

/-! ## `owl:intersectionOf` — read through an RDF collection -/

private def gInter : Graph :=
  [ ⟨bn "i", owlIntersectionOf, bnT "l1"⟩,
    ⟨bn "l1", rdfFirst, .iri exC⟩,
    ⟨bn "l1", rdfRest, bnT "l2"⟩,
    ⟨bn "l2", rdfFirst, .iri exD⟩,
    ⟨bn "l2", rdfRest, .iri rdfNil⟩ ]

#guard ClassExpr.beq (parseCeOfSubject (storeOf gInter) (bn "i"))
                     (.intersection [.named exC, .named exD])

/-! ## `owl:oneOf` members are INDIVIDUALS, not class expressions

The parser does not recurse into them — the same choice `hasValue`
makes. Recursing would read an individual as a named class. -/

private def gOne : Graph :=
  [ ⟨bn "o", owlOneOf, bnT "m1"⟩,
    ⟨bn "m1", rdfFirst, .iri exC⟩,
    ⟨bn "m1", rdfRest, .iri rdfNil⟩ ]

#guard ClassExpr.beq (parseCeOfSubject (storeOf gOne) (bn "o"))
                     (.oneOf [.iri exC])

/-! ## Cardinality

A qualified cardinality WITHOUT an `owl:onClass` degrades to the
unqualified form, which is what the F* module does and what the
mapping specification's own reading gives. -/

private def gMinQ : Graph :=
  [ ⟨bn "c", owlOnProperty, .iri exP⟩,
    ⟨bn "c", owlMinQualifiedCardinality, lit "2"⟩,
    ⟨bn "c", owlOnClass, .iri exC⟩ ]

#guard ClassExpr.beq (parseCeOfSubject (storeOf gMinQ) (bn "c"))
                     (.minQualCard 2 exP (.named exC))

private def gMinQNoClass : Graph :=
  [ ⟨bn "c", owlOnProperty, .iri exP⟩,
    ⟨bn "c", owlMinQualifiedCardinality, lit "2"⟩ ]

#guard ClassExpr.beq (parseCeOfSubject (storeOf gMinQNoClass) (bn "c"))
                     (.minCard 2 exP)

/-! A cardinality lexeme is a run of digits. MULTI-DIGIT matters: the
    value-space clashes in the WebOnt corpus use 129 and 257. -/
#guard cardinalityOfLexeme "257" == some 257
#guard cardinalityOfLexeme "" == none
#guard cardinalityOfLexeme "1x" == none
#guard cardinalityOfLexeme "-1" == none

/-! ## What the parser will not guess

A restriction blank node with an `owl:onProperty` and no recognised
restriction marker is `unknown`, and every consumer answers "I do not
know" for it. Under the open world that is always sound; a guess
would make the reasoner answer a question it had not read. -/

private def gBare : Graph := [ ⟨bn "r", owlOnProperty, .iri exP⟩ ]

#guard ClassExpr.beq (parseCeOfSubject (storeOf gBare) (bn "r")) .unknown

/-! A named class is just its IRI. -/
#guard ClassExpr.beq (parseCeOfSubject (storeOf []) (.iri exC)) (.named exC)

end L4Factoidal.OWL
