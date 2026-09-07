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
import L4Factoidal.RDF.EntailmentRdfsDatatypeClash
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
-- rdfs9 (no rdf-mt entry exercises it — see the sabotage record in
-- PORT_NOTES.md; the sparql11 entailment entries rdfs04/05/09 do)
#guard regimeEntails .rdfs D0
         [ ⟨.iri exA, rdfType, .iri exC⟩, ⟨.iri exC, rdfsSubClassOf, .iri exD⟩ ]
         [ ⟨.iri exA, rdfType, .iri exD⟩ ] == true
#guard regimeEntails .simple []
         [ ⟨.iri exA, rdfType, .iri exC⟩, ⟨.iri exC, rdfsSubClassOf, .iri exD⟩ ]
         [ ⟨.iri exA, rdfType, .iri exD⟩ ] == false
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

/-! ## Quote-polarity pins (issue 602, W3C rdf12 rdf-semantics)

One shared witness — an ill-typed recognised literal INSIDE a used
triple term — and one `#guard` per semantics-relevant fold, each named
with the W3C fixture that anchors its polarity. A future change of any
fold's interior treatment fails the build with the decision in view
(https://github.com/danbri/factoidal/issues/602, proposed guard 2). -/

def qpBadLit : WfLiteral :=
  ⟨{ lexicalForm := "bad", datatype := xsdInteger,
     langTag := none, direction := none }, by decide⟩

def qpTt : Term := .tripleTerm (.iri exA) exP (.literal qpBadLit)

def qpTtGraph : Graph := [⟨.iri exA, exFoo, qpTt⟩]

-- `malformed-literal`: the interior ill-typed literal IS mentioned,
-- and makes the graph D-inconsistent (WD §5 + §7.1).
#guard termIllTypedMention [xsdInteger] qpTt
#guard hasIllFormedLiteral [xsdInteger] qpTtGraph
#guard regimeInconsistent .rdf [xsdInteger] qpTtGraph
-- WD §7.1 last sentence: unrecognised type IRI — no inconsistency.
#guard !(termIllTypedMention [] qpTt)
#guard !(regimeInconsistent .rdf [] qpTtGraph)
-- `rdfs:range` constrains ASSERTED triples only: no range clash from a
-- triple-term interior, even with the range declaration present.
#guard !(hasRangeClash [xsdInteger]
  (⟨.iri exFoo, rdfsRange, .iri xsdInteger⟩ :: qpTtGraph))
-- `malformed-literal-bnode-neg`: a blank node cannot be bound TO an
-- ill-typed recognised literal, but a triple term is bindable at its
-- own level (its interior defect already fired the inconsistency arm).
#guard !(Regime.bindable .d [xsdInteger] (.literal qpBadLit))
#guard Regime.bindable .d [xsdInteger] qpTt
-- The two detectors in this tree agree on the quote polarity
-- (`hasIllFormedRecognizedLiteral` answered the OPPOSITE until
-- 2026-08-25 — issue 602's silent double standard).
#guard hasIllFormedRecognizedLiteral qpTtGraph [xsdInteger]

/-! ## RDF 1.2 rdf-semantics pins (`lake exe l4rdf-semantics`)

One `#guard` per fixture this landing's engine change is meant to
move, using the fixture's OWN lexical values
(`third_party/testing/w3c/rdf/rdf12/rdf-semantics/`) so a regression
here is the same regression the manifest walk would report. -/

def exClark    : WfIri := iri! "http://example.com/ns#clark"
def exSuperman : WfIri := iri! "http://example.com/ns#superman"
def exReports  : WfIri := iri! "http://example.com/ns#reports"
def exCanFly   : WfIri := iri! "http://example.com/ns#can"

/-- An untagged, undirectioned literal of a given datatype — `dtValueLeq`
takes plain `Literal`s, not `WfLiteral`s, so no well-formedness proof
is needed here. -/
def plainLit (lex : String) (dt : WfIri) : Literal :=
  { lexicalForm := lex, datatype := dt, langTag := none, direction := none }

-- `RDFS-Plus` is a recognised regime name (`opaque-iri`, `opaque-iri-control`).
#guard Regime.ofName? "RDFS-Plus" == some .rdfsPlus

-- `reifies-range`: `:a rdf:reifies :b` |- `:b rdf:type rdfs:Proposition`.
#guard reifiesPropOf ⟨.iri exA, rdfReifiesIri, .iri exB⟩ ==
  [⟨.iri exB, rdfType, .iri rdfsPropositionIri⟩]
-- Under `.rdfsPlus`, not `.rdfs`: the RDF 1.2 reifies-range step is a
-- WIDENING of the RDFS closure, and `.rdfs` must stay `fullClosure`,
-- which `Unified/SparqlAdequacy.regime_sound_rdfs` is stated about.
#guard regimeEntails .rdfsPlus D0 [⟨.iri exA, rdfReifiesIri, .iri exB⟩]
  [⟨.iri exB, rdfType, .iri rdfsPropositionIri⟩] == true

-- and NOT under `.rdfs`, which is the plain RDFS closure.
#guard regimeEntails .rdfs D0 [⟨.iri exA, rdfReifiesIri, .iri exB⟩]
  [⟨.iri exB, rdfType, .iri rdfsPropositionIri⟩] == false

-- `opaque-iri`: `owl:sameAs` substitutes even inside a triple term's
-- interior. `:clark :reports <<( :superman :can :fly )>>` +
-- `:clark owl:sameAs :superman` entails
-- `:clark :reports <<( :clark :can :fly )>>`.
def opaqueIriAction : Graph :=
  [ ⟨.iri exClark, exReports, .tripleTerm (.iri exSuperman) exCanFly (.iri exY)⟩,
    ⟨.iri exClark, owlSameAsIri, .iri exSuperman⟩ ]
def opaqueIriResult : Graph :=
  [ ⟨.iri exClark, exReports, .tripleTerm (.iri exClark) exCanFly (.iri exY)⟩ ]
#guard regimeEntails .rdfsPlus D0 opaqueIriAction opaqueIriResult == true

-- `float-zero` / `double-zero`: `dtValueLeq` distinguishes ±0 (no
-- fallback to structural equality masks this — both lexicals ARE
-- structurally different strings too, so this pin is about VALUE
-- equality reaching the right answer, not accidentally matching it).
#guard dtValueLeq D0 (plainLit "0" xsdFloat) (plainLit "-0" xsdFloat) == false
#guard dtValueLeq D0 (plainLit "0" xsdDouble) (plainLit "-0" xsdDouble) == false
-- `float-round-same` / `float-round-different`: double-rounding
-- through binary64 then binary32 (`XSD.IEEE754`'s documented choice).
#guard dtValueLeq D0 (plainLit "16777206.5" xsdFloat) (plainLit "16777205.5" xsdFloat) == true
#guard dtValueLeq D0 (plainLit "16777206.5" xsdFloat) (plainLit "16777207.5" xsdFloat) == false
-- `double-round-same` / `double-round-different`.
#guard dtValueLeq D0 (plainLit "9007199254740992.5" xsdDouble)
                     (plainLit "9007199254740991.5" xsdDouble) == true
#guard dtValueLeq D0 (plainLit "9007199254740990.5" xsdDouble)
                     (plainLit "9007199254740991.5" xsdDouble) == false
-- `float-infinity` / `double-infinity`: overflow rounds to the same
-- signed infinity regardless of exact magnitude beyond the format's range.
#guard dtValueLeq D0 (plainLit "1E400" xsdFloat) (plainLit "1E401" xsdFloat) == true
#guard dtValueLeq D0 (plainLit "1E400" xsdDouble) (plainLit "1E401" xsdDouble) == true

-- ## The triple-term interior: `opaque-language-string` vs
-- `opaque-dir-language-string`
--
-- Both fixtures are `mf:entailmentRegime "simple"` with
-- `mf:recognizedDatatypes ()`, identical in shape, and OPPOSITE in
-- polarity — they differ only by the `--ltr` base direction. The pair
-- is the tight test case of
-- `docs/designissues/2026-09-07-rdf12-sparql12-semantics.md` § 3, and
-- both readings are pinned here so neither can be flipped unseen.
--
-- Reading 1 (implemented, and what the suite requires): inside a
-- triple term a directional language tag compares case-SENSITIVELY.
-- Reading 2 (RDF 1.2 Concepts §3.3 as written): the language-tag
-- component of BOTH `rdf:langString` and `rdf:dirLangString` compares
-- without regard to ASCII case, in every position.

def dirLangLit (lex tag : String) (d : TextDirection) : Literal :=
  (Literal.dirLangString lex tag d).val
def langLit (lex tag : String) : Literal :=
  (Literal.langString lex tag).val

-- `opaque-language-string-control` / `opaque-dir-language-string-control`:
-- OUTSIDE a triple term, tag case does not matter for either datatype.
-- These are the two fixtures that force `.simple` off `literalStrictEq`.
#guard Regime.literalEq .simple D0 (langLit "hello" "en-us")
                                   (langLit "hello" "en-US") == true
#guard Regime.literalEq .simple D0 (dirLangLit "hello" "en-us" .ltr)
                                   (dirLangLit "hello" "en-US" .ltr) == true

-- `opaque-language-string` (POSITIVE): a plain language-tagged string
-- inside a triple term still matches across tag case.
#guard regimeEntails .simple D0
  [⟨.iri exA, exB, .tripleTerm (.iri exA) exB (.literal (Literal.langString "hello" "en-us"))⟩]
  [⟨.iri exA, exB, .tripleTerm (.iri exA) exB (.literal (Literal.langString "hello" "en-US"))⟩]
  == true

-- `opaque-dir-language-string` (NEGATIVE): the same pair with a base
-- direction must NOT entail. This is Reading 1. Under Reading 2 this
-- `#guard` would read `== true` and the W3C fixture would fail.
#guard regimeEntails .simple D0
  [⟨.iri exA, exB, .tripleTerm (.iri exA) exB
      (.literal (Literal.dirLangString "hello" "en-us" .ltr))⟩]
  [⟨.iri exA, exB, .tripleTerm (.iri exA) exB
      (.literal (Literal.dirLangString "hello" "en-US" .ltr))⟩]
  == false

-- The tightening is confined to the triple-term interior and to
-- `rdf:dirLangString`: it must not leak to a plain language string
-- inside a triple term (the guard two above), nor to a directional one
-- outside (the guard four above).
#guard stricterInTripleTerm (literalValueEq D0)
  (dirLangLit "hello" "en-us" .ltr) (dirLangLit "hello" "en-US" .ltr) == false
#guard stricterInTripleTerm (literalValueEq D0)
  (langLit "hello" "en-us") (langLit "hello" "en-US") == true
#guard stricterInTripleTerm (literalValueEq D0)
  (dirLangLit "hello" "en-US" .ltr) (dirLangLit "hello" "en-US" .ltr) == true

-- `opaque-literal` (POSITIVE, regime "simple",
-- `mf:recognizedDatatypes (xsd:integer)`): a non-empty D makes the
-- simple regime's comparator recognise the datatype, so "042" and "42"
-- are the same value inside a triple term.
#guard Regime.literalEq .simple (withMinimalD [xsdInteger])
  (plainLit "042" xsdInteger) (plainLit "42" xsdInteger) == true
-- and with the EMPTY D it does not — the fixture's own control on
-- whether the recognized-datatype list is being read at all.
#guard Regime.literalEq .simple D0
  (plainLit "042" xsdInteger) (plainLit "42" xsdInteger) == false

-- `json-object-unordered` / `json-array-unordered` (arrays stay
-- ORDERED — the second pair is a NEGATIVE fixture).
#guard rdfJsonValueEq "{ \"a\":0, \"b\":1 }" "{ \"b\":1, \"a\":0 }" == true
#guard rdfJsonValueEq "[ -0, 0 ]" "[ 0, -0 ]" == false
-- `json-zero`: ±0 distinct in `rdf:JSON` numbers too.
#guard rdfJsonValueEq "0" "-0" == false
-- `json-round-same` / `json-round-different`, same values as the
-- `xsd:double` pins above (the manifest uses the identical lexicals).
#guard rdfJsonValueEq "9007199254740992.5" "9007199254740991.5" == true
#guard rdfJsonValueEq "9007199254740990.5" "9007199254740991.5" == false

/-! ## Axiom audit -/

#print axioms L4Factoidal.RDF.simpleEntails_sound
#print axioms L4Factoidal.RDFS.fullClosure_sound
#print axioms L4Factoidal.RDFS.rdfClosure_sound
#print axioms L4Factoidal.RDFS.Derives.toFull
#print axioms L4Factoidal.RDFS.fullClosure_extensive

end L4Factoidal.RDF.EntailmentTests
