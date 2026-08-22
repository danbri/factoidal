/-
L4Factoidal.RDF.EntailmentTests — build-time guards for the entailment
regimes and the full RDF/RDFS closure, on the SHAPES of the W3C rdf-mt
fixtures (`third_party/testing/w3c/rdf/rdf11/rdf-mt/`), rebuilt inline
so the guards run without file I/O. The conformance score itself comes
from `lake exe l4w3c …/rdf-mt/manifest.ttl`, which reads the real files;
these guards are the regression pins.

Every `#guard` is evaluated during `lake build` (pitfall 10: concrete
results are guards, never `decide`).
-/
import L4Factoidal.RDF.Entailment
import L4Factoidal.RDF.EntailmentTheorems
import L4Factoidal.RDFS.FullClosureTheorems

namespace L4Factoidal.RDF.EntailmentTests

open L4Factoidal.RDF L4Factoidal.RDFS

def iri! (s : String) (h : isIri s := by rfl) : WfIri := ⟨s, h⟩

def exFoo : WfIri := iri! "http://example.org/foo"
def exBar : WfIri := iri! "http://example.org/bar"
def exA   : WfIri := iri! "http://example.org/a"
def exB   : WfIri := iri! "http://example.org/b"
def exC   : WfIri := iri! "http://example.org/c"
def exD   : WfIri := iri! "http://example.org/d"
def exX   : WfIri := iri! "http://example.org/x"
def exY   : WfIri := iri! "http://example.org/y"
def exP   : WfIri := iri! "http://example.org/p"
def exQ   : WfIri := iri! "http://example.org/q"

/-- A typed literal term; the well-formedness gate is decided at run
time (every datatype used below passes it — a failure would surface as
an IRI object and a wrong guard). -/
def typed (lex : String) (dt : WfIri) : Term :=
  let l : Literal := { lexicalForm := lex, datatype := dt, langTag := none, direction := none }
  if h : literalWf l = true then .literal ⟨l, h⟩ else .iri dt

def D0 : List WfIri := withMinimalD []

/-! ## Numeric lexical forms and values -/

#guard parseIntegerLexical "010" == some 10
#guard parseIntegerLexical "-7" == some (-7)
#guard parseIntegerLexical "+3" == some 3
#guard parseIntegerLexical " 3 " == none
#guard parseIntegerLexical "flargh" == none
#guard parseIntegerLexical "" == none
#guard parseDecimalLexical "10.0" == some ⟨10, 0⟩
#guard parseDecimalLexical "10.50" == some ⟨105, 1⟩
#guard parseDecimalLexical ".5" == some ⟨5, 1⟩
#guard parseDecimalLexical "5." == some ⟨5, 0⟩
#guard parseDecimalLexical "." == none
#guard parseDecimalLexical "1e3" == none
#guard intInRange 2147483647 == true
#guard intInRange 2147483648 == false

/-! ## Well-formedness under D (rdf-mt `datatypes-non-well-formed-literal-*`,
`xmlsch-02-whitespace-facet-*`, `rdfs-entailment-test001`) -/

def flargh : Literal := { lexicalForm := "flargh", datatype := xsdInteger, langTag := none, direction := none }
def spaced3 : Literal := { lexicalForm := " 3 ", datatype := xsdInt, langTag := none, direction := none }
def lt : Literal := { lexicalForm := "<", datatype := rdfXMLLiteral, langTag := none, direction := none }
def okXml : Literal := { lexicalForm := "a<b>c</b>", datatype := rdfXMLLiteral, langTag := none, direction := none }

-- recognised → ill-formed detected; unrecognised → never checked
#guard literalIllFormed [xsdInteger] flargh == true
#guard literalIllFormed [] flargh == false
#guard literalIllFormed [xsdInt] spaced3 == true
#guard literalIllFormed [rdfXMLLiteral] lt == true
#guard literalIllFormed [rdfXMLLiteral] okXml == false
#guard xmlLiteralWellFormed "" == true

/-! ## Value equality (`datatypes-semantic-equivalence-*`, `tex-01`) -/

def i010 : Literal := { lexicalForm := "010", datatype := xsdInteger, langTag := none, direction := none }
def i10  : Literal := { lexicalForm := "10", datatype := xsdInteger, langTag := none, direction := none }
def d100 : Literal := { lexicalForm := "10.0", datatype := xsdDecimal, langTag := none, direction := none }
def s10  : Literal := { lexicalForm := "10", datatype := xsdString, langTag := none, direction := none }
def aEnUs : Literal := { lexicalForm := "a", datatype := rdfLangString, langTag := some "en-us", direction := none }
def aEnUS : Literal := { lexicalForm := "a", datatype := rdfLangString, langTag := some "en-US", direction := none }

#guard literalValueEq [xsdInteger] i010 i10 == true
#guard literalValueEq [] i010 i10 == false              -- integer not recognised
#guard literalValueEq [xsdInteger, xsdDecimal] i10 d100 == true
#guard literalValueEq [xsdInteger] i10 d100 == false    -- decimal not recognised
#guard literalValueEq D0 s10 i10 == false               -- string vs integer
#guard literalValueEq D0 aEnUs aEnUS == true            -- tag case
#guard literalStrictEq aEnUs aEnUS == false

/-! ## Simple entailment (`datatypes-test008` / `-test009`,
`rdfms-xmllang-test007*`) -/

def gTest008a : Graph :=
  [ ⟨.iri exA, exB, typed "10" xsdString⟩, ⟨.iri exC, exD, typed "10" xsdString⟩ ]
def gTest008b : Graph :=
  [ ⟨.iri exA, exB, .bnode "x"⟩, ⟨.iri exC, exD, .bnode "x"⟩ ]
def gTest009a : Graph :=
  [ ⟨.iri exA, exB, typed "10" xsdString⟩, ⟨.iri exC, exD, typed "10" xsdInteger⟩ ]

-- a blank node may map to a literal …
#guard simpleEntails gTest008a gTest008b == true
-- … but consistently: "10" and "10"^^xsd:integer are different terms
#guard simpleEntails gTest009a gTest008b == false
#guard regimeEntails .rdf D0 gTest009a gTest008b == false
-- language tags distinguish plain literals
#guard simpleEntails [⟨.iri exA, exB, .literal (Literal.langString "chat" "fr")⟩]
                     [⟨.iri exA, exB, .literal (Literal.langString "chat" "en")⟩] == false
#guard simpleEntails [⟨.iri exA, exB, .literal (Literal.langString "chat" "fr")⟩]
                     [⟨.iri exA, exB, typed "chat" xsdString⟩] == false
-- every graph entails itself and its subgraphs; a blank-node cycle needs a cycle
#guard simpleEntails gTest008a gTest008a == true
#guard simpleEntails gTest008a [] == true
#guard simpleEntails [] gTest008a == false
#guard simpleEntails [⟨.iri exA, exP, .iri exB⟩, ⟨.iri exB, exP, .iri exA⟩]
                     [⟨.bnode "u", exP, .bnode "v"⟩, ⟨.bnode "v", exP, .bnode "u"⟩] == true
#guard simpleEntails [⟨.iri exA, exP, .iri exB⟩, ⟨.iri exB, exP, .iri exC⟩]
                     [⟨.bnode "u", exP, .bnode "v"⟩, ⟨.bnode "v", exP, .bnode "u"⟩] == false

/-! ## D-value entailment (`datatypes-semantic-equivalence-*`) -/

#guard regimeEntails .rdf [xsdInteger] [⟨.iri exFoo, exBar, typed "010" xsdInteger⟩]
                                       [⟨.iri exFoo, exBar, typed "10" xsdInteger⟩] == true
#guard regimeEntails .rdf (withMinimalD [xsdInteger, xsdDecimal])
         [⟨.iri exFoo, exBar, typed "10" xsdInteger⟩]
         [⟨.iri exFoo, exBar, typed "10.0" xsdDecimal⟩] == true
#guard regimeEntails .simple [] [⟨.iri exFoo, exBar, typed "010" xsdInteger⟩]
                                [⟨.iri exFoo, exBar, typed "10" xsdInteger⟩] == false

/-! ## Inconsistency (`datatypes-range-clash`, `datatypes-test010`,
`rdfs-entailment-test002`, `datatypes-intensional-*`) -/

def gRangeClash : Graph :=
  [ ⟨.iri exFoo, exBar, typed "25" xsdInteger⟩,
    ⟨.iri exBar, rdfsRange, .iri xsdString⟩ ]
#guard regimeInconsistent .rdfs (withMinimalD [xsdInteger, xsdString]) gRangeClash == true
-- the range target must be recognised for the clash to be asserted
#guard regimeInconsistent .rdfs [xsdInteger] gRangeClash == false
-- a matching range is no clash
#guard regimeInconsistent .rdfs (withMinimalD [xsdInteger])
         [ ⟨.iri exFoo, exBar, typed "25" xsdInteger⟩,
           ⟨.iri exBar, rdfsRange, .iri xsdInteger⟩ ] == false
-- integer value in a decimal range: in the value space, no clash
#guard regimeInconsistent .rdfs (withMinimalD [xsdInteger, xsdDecimal])
         [ ⟨.iri exFoo, exBar, typed "25" xsdInteger⟩,
           ⟨.iri exBar, rdfsRange, .iri xsdDecimal⟩ ] == false
-- plain literal (xsd:string) under an integer range — datatypes-test010
#guard regimeInconsistent .rdfs (withMinimalD [xsdInteger])
         [ ⟨.iri exFoo, exBar, typed "25" xsdString⟩,
           ⟨.iri exBar, rdfsRange, .iri xsdInteger⟩ ] == true
-- xsd:string under an rdf:langString range — rdfs-entailment-test002
#guard regimeInconsistent .rdfs D0
         [ ⟨.iri exFoo, exBar, typed "flargh" xsdString⟩,
           ⟨.iri exBar, rdfsRange, .iri rdfLangString⟩ ] == true
-- a range reached through subClassOf
#guard regimeInconsistent .rdfs (withMinimalD [xsdInteger])
         [ ⟨.iri exFoo, exBar, typed "25" xsdString⟩,
           ⟨.iri exBar, rdfsRange, .iri exC⟩,
           ⟨.iri exC, rdfsSubClassOf, .iri xsdInteger⟩ ] == true
-- ill-formed literal: recognised → inconsistent; unrecognised → not
#guard regimeInconsistent .rdfs (withMinimalD [xsdInteger])
         [⟨.iri exFoo, exBar, typed "flargh" xsdInteger⟩] == true
#guard regimeInconsistent .rdfs D0 [⟨.iri exFoo, exBar, typed "flargh" xsdInteger⟩] == false
-- an inconsistent graph entails anything
#guard regimeEntails .rdfs (withMinimalD [xsdInteger])
         [⟨.iri exFoo, exBar, typed "flargh" xsdInteger⟩]
         [⟨.iri exX, exY, .iri exC⟩] == true
-- xsd:integer subClassOf xsd:decimal is consistent (intensional datatypes)
#guard regimeInconsistent .rdfs (withMinimalD [xsdInteger, xsdDecimal])
         [⟨.iri xsdInteger, rdfsSubClassOf, .iri xsdDecimal⟩] == false
-- XMLLiteral "<" under recognised rdf:XMLLiteral — rdfs-entailment-test001
#guard regimeInconsistent .rdfs (withMinimalD [rdfXMLLiteral])
         [ ⟨.iri exP, rdfsRange, .iri rdfXMLLiteral⟩,
           ⟨.iri exFoo, exP, typed "<" rdfXMLLiteral⟩ ] == true

/-! ## The RDFS rule set (`rdfms-seq-representation-*`,
`rdfs-container-membership-superProperty`, `horst-01`,
`rdfs-subPropertyOf-semantics`, `rdfs-domain-and-range`) -/

def rdf1t : WfIri := iri! "http://www.w3.org/1999/02/22-rdf-syntax-ns#_1"
def rdf7t : WfIri := iri! "http://www.w3.org/1999/02/22-rdf-syntax-ns#_7"

#guard isContainerMembershipIri rdf7t.val == true
#guard isContainerMembershipIri "http://www.w3.org/1999/02/22-rdf-syntax-ns#_" == false
#guard isContainerMembershipIri "http://www.w3.org/1999/02/22-rdf-syntax-ns#_x" == false
#guard containerMembershipIn [⟨.iri exFoo, rdf7t, .iri exBar⟩] == [rdf7t]

-- rdfms-seq-representation-test002: rdf:_1 is a ContainerMembershipProperty (axiom)
#guard regimeEntails .rdfs D0 [⟨.iri exFoo, rdf1t, .iri exBar⟩]
         [⟨.iri rdf1t, rdfType, .iri rdfsContainerMembershipProperty⟩] == true
-- test004: rdf:_1 subPropertyOf rdfs:member (rdfs12)
#guard regimeEntails .rdfs D0 [⟨.iri exFoo, rdf1t, .iri exBar⟩]
         [⟨.iri rdf1t, rdfsSubPropertyOf, .iri rdfsMember⟩] == true
-- test003: a rdf:_1 b ⊢ a rdfs:member b (rdfs12 + rdfs7)
#guard regimeEntails .rdfs D0 [⟨.iri exA, rdf1t, .iri exB⟩]
         [⟨.iri exA, rdfsMember, .iri exB⟩] == true
-- an rdf:_n only the conclusion mentions still gets its axioms
#guard regimeEntails .rdfs D0 [] [⟨.iri rdf7t, rdfType, .iri rdfProperty⟩] == true
-- the container-membership negative: member does not entail rdf:_1
#guard regimeEntails .rdfs D0 [⟨.iri exA, rdfsMember, .iri exB⟩]
         [⟨.iri exA, rdf1t, .iri exB⟩] == false
-- horst-01: rdfs:subClassOf is intensional
#guard regimeEntails .rdfs D0
         [ ⟨.iri exX, rdfType, .iri rdfsClass⟩, ⟨.iri rdfType, rdfsDomain, .iri exY⟩ ]
         [ ⟨.iri exX, rdfsSubClassOf, .iri exY⟩ ] == false
-- … but the same premise does entail x rdf:type y (rdfs2)
#guard regimeEntails .rdfs D0
         [ ⟨.iri exX, rdfType, .iri rdfsClass⟩, ⟨.iri rdfType, rdfsDomain, .iri exY⟩ ]
         [ ⟨.iri exX, rdfType, .iri exY⟩ ] == true
-- rdfs-domain-and-range intensionality: no new range triple
#guard regimeEntails .rdfs D0
         [ ⟨.iri exA, rdfsSubClassOf, .iri exB⟩, ⟨.iri exP, rdfsRange, .iri exA⟩ ]
         [ ⟨.iri exP, rdfsRange, .iri exB⟩ ] == false
-- subproperties inherit domain and range conjunctively (rdfs7, rdfs2, rdfs3)
#guard regimeEntails .rdfs D0
         [ ⟨.iri exQ, rdfsSubPropertyOf, .iri exP⟩,
           ⟨.iri exP, rdfsDomain, .iri exC⟩, ⟨.iri exQ, rdfsDomain, .iri exD⟩,
           ⟨.iri exA, exQ, .iri exB⟩ ]
         [ ⟨.iri exA, rdfType, .iri exC⟩, ⟨.iri exA, rdfType, .iri exD⟩ ] == true
-- reflexivity reached through the axioms: A subClassOf B ⊢ B subClassOf B
--   (rdfs:subClassOf rdfs:range rdfs:Class + rdfs3 + rdfs10)
#guard regimeEntails .rdfs D0 [⟨.iri exA, rdfsSubClassOf, .iri exB⟩]
         [⟨.iri exB, rdfsSubClassOf, .iri exB⟩] == true
-- rdfD2 is an RDF-regime rule …
#guard regimeEntails .rdf D0 [⟨.iri exA, exP, .iri exB⟩]
         [⟨.iri exP, rdfType, .iri rdfProperty⟩] == true
-- … and not a simple-entailment one
#guard regimeEntails .simple [] [⟨.iri exA, exP, .iri exB⟩]
         [⟨.iri exP, rdfType, .iri rdfProperty⟩] == false
-- rdfs4a/4b
#guard regimeEntails .rdfs D0 [⟨.iri exA, exP, .iri exB⟩]
         [⟨.iri exA, rdfType, .iri rdfsResource⟩, ⟨.iri exB, rdfType, .iri rdfsResource⟩] == true
-- statement-entailment: reification is not entailed
#guard regimeEntails .rdfs D0 [⟨.iri exA, exP, .iri exB⟩]
         [ ⟨.bnode "r", rdfType, .iri rdfStatement⟩, ⟨.bnode "r", rdfSubject, .iri exA⟩,
           ⟨.bnode "r", rdfPredicate, .iri exP⟩, ⟨.bnode "r", rdfObject, .iri exB⟩ ] == false

/-! ## Closure size sanity: the RDFS closure is finite and saturates -/

#guard (fullClosure D0 [rdf1] [⟨.iri exA, exP, .iri exB⟩]).length > 60
#guard (let c := fullClosure D0 [rdf1] [⟨.iri exA, exP, .iri exB⟩]
        (fullStep c).length == c.length)

/-! ## Axiom audit -/

#print axioms L4Factoidal.RDF.simpleEntails_sound
#print axioms L4Factoidal.RDFS.fullClosure_sound
#print axioms L4Factoidal.RDFS.rdfClosure_sound
#print axioms L4Factoidal.RDFS.Derives.toFull
#print axioms L4Factoidal.RDFS.fullClosure_extensive

end L4Factoidal.RDF.EntailmentTests
