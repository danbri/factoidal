/-
L4Factoidal.SHACL.ShaclTests — build-time `#guard`s for the SHACL Core
validator on small shapes + data graphs written in Turtle and parsed
by the Lean Turtle parser at elaboration time.

Each guard names the Recommendation clause it pins. The real W3C
suite is run by `Harness/ShaclProbe.lean` (`lake exe l4shacl`); these
are the unit-level checks that fail the BUILD when a clause regresses
(the sabotage discipline of `skills/factoidal-lean-basics`).
-/
import L4Factoidal.SHACL.Report
import L4Factoidal.Syntax.Turtle
import L4Factoidal.RDF.Isomorphism

namespace L4Factoidal.SHACL.Tests

open L4Factoidal.RDF L4Factoidal.SHACL L4Factoidal.Syntax

def prefixes : String :=
  "@prefix ex: <http://example.org/> . @prefix sh: <http://www.w3.org/ns/shacl#> . " ++
  "@prefix xsd: <http://www.w3.org/2001/XMLSchema#> . " ++
  "@prefix rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#> . " ++
  "@prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> . "

/-- Parse a Turtle body (prefixes prepended); an unparsable fixture is
the empty graph, which the guards below cannot mistake for a pass
because each one asserts a specific result count. -/
def ttl (body : String) : Graph :=
  match parseTurtle (prefixes ++ body) (some "http://example.org/doc") with
  | .ok g => g
  | .error _ => []

/-- Validate a document against itself (data graph = shapes graph). -/
def run (body : String) : ValidationReport :=
  let g := ttl body
  validate g (decodeShapesGraph g)

def components (r : ValidationReport) : List WfIri :=
  r.results.map fun v => constraintComponentIri v.constraint

def exIri (local_ : String) : WfIri := ⟨"http://example.org/" ++ local_, by simp [isIri]⟩

/-! ### §4.2.2 sh:maxCount — one result per focus node, no sh:value -/

def maxCountDoc : String :=
  "ex:S a sh:NodeShape ; sh:targetClass ex:Person ; sh:property [ sh:path ex:name ; sh:maxCount 1 ] . " ++
  "ex:bob a ex:Person ; ex:name \"A\", \"B\" . ex:ann a ex:Person ; ex:name \"C\" ."

#guard (run maxCountDoc).conforms == false
#guard components (run maxCountDoc) == [shMaxCountCC]
#guard (run maxCountDoc).results.map (·.focus) == [.iri (exIri "bob")]
#guard (run maxCountDoc).results.map (·.value) == [none]

/-! ### §4.2.1 sh:minCount 0 never produces a result -/

def minCountZeroDoc : String :=
  "ex:S a sh:NodeShape ; sh:targetClass ex:Person ; sh:property [ sh:path ex:name ; sh:minCount 0 ] . " ++
  "ex:bob a ex:Person ."

#guard (run minCountZeroDoc).conforms == true
#guard (run minCountZeroDoc).results.length == 0

/-! ### §4.6.1 sh:not flips conformance -/

def notDoc : String :=
  "ex:S a sh:NodeShape ; sh:targetNode ex:n, ex:m ; sh:not [ sh:class ex:C ] . ex:n a ex:C . ex:m a ex:D ."

#guard components (run notDoc) == [shNotCC]
#guard (run notDoc).results.map (·.focus) == [.iri (exIri "n")]

/-! ### §4.1.2 sh:datatype — ill-formed literals do not match -/

def datatypeDoc : String :=
  "ex:S a sh:NodeShape ; sh:targetNode \"aldi\"^^xsd:integer, \"12\"^^xsd:integer, \"300\"^^xsd:byte, \"3\"^^xsd:byte ; " ++
  "sh:datatype xsd:integer ."

#guard (run datatypeDoc).results.length == 3   -- "aldi" and both xsd:byte values

def byteDoc : String :=
  "ex:S a sh:NodeShape ; sh:targetNode \"300\"^^xsd:byte, \"c\"^^xsd:byte, \"3\"^^xsd:byte ; sh:datatype xsd:byte ."

#guard (run byteDoc).results.length == 2

/-! ### §1.4 / §4.1.1 sh:class — SHACL instance through rdfs:subClassOf* -/

def classDoc : String :=
  "ex:Sub rdfs:subClassOf ex:Mid . ex:Mid rdfs:subClassOf ex:Super . ex:x a ex:Sub . ex:y a ex:Other . " ++
  "ex:S a sh:NodeShape ; sh:targetNode ex:x, ex:y ; sh:class ex:Super ."

#guard (run classDoc).results.map (·.focus) == [.iri (exIri "y")]
#guard isShaclInstance (ttl classDoc) (.iri (exIri "x")) (exIri "Super") == true
#guard isShaclInstance (ttl classDoc) (.iri (exIri "x")) (exIri "Sub") == true
#guard isShaclInstance (ttl classDoc) (.iri (exIri "y")) (exIri "Super") == false

/-! ### §2.1.3.1 implicit class target -/

def implicitDoc : String :=
  "ex:C a rdfs:Class, sh:NodeShape ; sh:nodeKind sh:BlankNode . ex:i a ex:C ."

#guard components (run implicitDoc) == [shNodeKindCC]

/-! ### §4.4.3 sh:pattern with sh:flags -/

def patternDoc : String :=
  "ex:S a sh:NodeShape ; sh:targetNode \"John\", \"Mark\" ; sh:pattern \"^joh\" ; sh:flags \"i\" ."

#guard (run patternDoc).results.map (·.value) == [some (.literal (Literal.string "Mark"))]

/-! ### §2.3.1 paths: sequence, inverse, zero-or-more, alternative -/

def seqDoc : String :=
  "ex:a ex:p ex:b . ex:b ex:q ex:c . ex:c a ex:C . ex:a2 ex:p ex:b2 . ex:b2 ex:q ex:c2 . " ++
  "ex:S a sh:PropertyShape ; sh:targetNode ex:a, ex:a2 ; sh:path ( ex:p ex:q ) ; sh:class ex:C ."

#guard (run seqDoc).results.map (·.value) == [some (.iri (exIri "c2"))]

def invDoc : String :=
  "ex:child ex:parent ex:dad . ex:S a sh:PropertyShape ; sh:targetNode ex:dad ; " ++
  "sh:path [ sh:inversePath ex:parent ] ; sh:minCount 2 ."

#guard components (run invDoc) == [shMinCountCC]
#guard evalPath (ttl invDoc) (.iri (exIri "dad")) (.inverse (.pred (exIri "parent"))) == [.iri (exIri "child")]

def starDoc : String :=
  "ex:a ex:next ex:b . ex:b ex:next ex:c . ex:c ex:next ex:a ."

#guard (evalPath (ttl starDoc) (.iri (exIri "a")) (.zeroOrMore (.pred (exIri "next")))).length == 3
#guard (evalPath (ttl starDoc) (.iri (exIri "a")) (.oneOrMore (.pred (exIri "next")))).length == 3
#guard (evalPath (ttl starDoc) (.iri (exIri "a")) (.zeroOrOne (.pred (exIri "next")))).length == 2
#guard (evalPath (ttl starDoc) (.iri (exIri "a"))
  (.alt [.pred (exIri "next"), .inverse (.pred (exIri "next"))])).length == 2

/-- Path → RDF → Path round trip (`Report.pathToRdf` is the inverse of `decodePath`). -/
def roundTrip (p : Path) : Bool :=
  let (t, ts, _) := pathToRdf p 0
  decodePath ts t (ts.length + 1) == p

#guard roundTrip (.seq [.pred (exIri "p"), .inverse (.pred (exIri "q"))])
#guard roundTrip (.alt [.pred (exIri "p"), .zeroOrMore (.pred (exIri "q"))])
#guard roundTrip (.oneOrMore (.seq [.pred (exIri "p"), .pred (exIri "q")]))
#guard roundTrip (.zeroOrOne (.pred (exIri "p")))

/-! ### §4.8.1 sh:closed — one result per offending triple -/

def closedDoc : String :=
  "ex:S a sh:NodeShape ; sh:targetNode ex:n ; sh:closed true ; sh:ignoredProperties ( rdf:type ) ; " ++
  "sh:property [ sh:path ex:ok ] . ex:n a ex:C ; ex:ok 1 ; ex:bad 2 ; ex:bad 3 ."

#guard (run closedDoc).results.length == 2
#guard (run closedDoc).results.all fun v => v.path == some (.pred (exIri "bad"))

/-! ### §4.4.5 sh:uniqueLang — lexical "true" only -/

def uniqueLangDoc : String :=
  "ex:S a sh:NodeShape ; sh:targetNode ex:n ; sh:property [ sh:path ex:label ; sh:uniqueLang true ] . " ++
  "ex:n ex:label \"a\"@en, \"b\"@EN, \"c\"@de ."

#guard components (run uniqueLangDoc) == [shUniqueLangCC]

def uniqueLangOneDoc : String :=
  "ex:S a sh:NodeShape ; sh:targetNode ex:n ; sh:property [ sh:path ex:label ; sh:uniqueLang \"1\"^^xsd:boolean ] . " ++
  "ex:n ex:label \"a\"@en, \"b\"@en ."

#guard (run uniqueLangOneDoc).conforms == true

/-! ### §4.5.3 sh:lessThan — one result per incomparable pair -/

def lessThanDoc : String :=
  "ex:S a sh:NodeShape ; sh:targetNode ex:n ; sh:property [ sh:path ex:first ; sh:lessThan ex:second ] . " ++
  "ex:n ex:first 1, 2 ; ex:second \"a\", \"b\" ."

#guard (run lessThanDoc).results.length == 4

def lessThanOkDoc : String :=
  "ex:S a sh:NodeShape ; sh:targetNode ex:n ; sh:property [ sh:path ex:first ; sh:lessThan ex:second ] . " ++
  "ex:n ex:first 1, 2 ; ex:second 3, 4.5 ."

#guard (run lessThanOkDoc).conforms == true

/-! ### §4.3 value range on xsd:dateTime (timezone comparability) -/

#guard numericCmpLe (Literal.string "2002-10-10T12:00:00") (Literal.string "x") == none
#guard dtCmp "2002-10-10T12:00:00-05:00" "2002-10-10T12:00:01-05:00" == some (-1)
#guard dtCmp "2002-10-10T12:00:00-05:00" "2002-10-10T17:00:00Z" == some 0
#guard dtCmp "2002-10-10T12:00:00-05:00" "2002-10-10T12:00:00" == none

def dateTimeDoc : String :=
  "ex:S a sh:NodeShape ; sh:minInclusive \"2002-10-10T12:00:00-05:00\"^^xsd:dateTime ; " ++
  "sh:targetNode \"2002-10-10T12:00:00-05:00\"^^xsd:dateTime, \"2002-10-09T12:00:00-05:00\"^^xsd:dateTime, " ++
  "\"2002-10-10T12:00:00\"^^xsd:dateTime ."

#guard (run dateTimeDoc).results.length == 2   -- the earlier value and the naive one

/-! ### §4.7.2 sh:qualifiedValueShape with sh:qualifiedValueShapesDisjoint -/

def qualifiedDoc : String :=
  "ex:Hand a sh:NodeShape ; sh:targetNode ex:h ; sh:property ex:d1, ex:d4 . " ++
  "ex:d1 sh:path ex:digit ; sh:qualifiedMinCount 1 ; sh:qualifiedValueShape [ sh:class ex:Thumb ] ; sh:qualifiedValueShapesDisjoint true . " ++
  "ex:d4 sh:path ex:digit ; sh:qualifiedMinCount 4 ; sh:qualifiedValueShape [ sh:class ex:Finger ] ; sh:qualifiedValueShapesDisjoint true . " ++
  "ex:h ex:digit ex:f1, ex:f2, ex:f3, ex:ft . ex:f1 a ex:Finger . ex:f2 a ex:Finger . ex:f3 a ex:Finger . ex:ft a ex:Finger, ex:Thumb ."

#guard components (run qualifiedDoc) == [shQualifiedMinCountCC, shQualifiedMinCountCC]

/-! ### §4.6.4 sh:xone, §4.8.2 sh:hasValue, §4.8.3 sh:in, §4.4.4 sh:languageIn -/

def xoneDoc : String :=
  "ex:S a sh:NodeShape ; sh:targetNode ex:a, ex:b, ex:c ; sh:xone ( [ sh:class ex:C ] [ sh:class ex:D ] ) . " ++
  "ex:a a ex:C . ex:b a ex:C, ex:D . ex:c a ex:E ."

#guard (run xoneDoc).results.map (·.focus) == [.iri (exIri "b"), .iri (exIri "c")]

def hasValueInDoc : String :=
  "ex:S a sh:NodeShape ; sh:targetNode ex:n ; sh:property [ sh:path ex:p ; sh:hasValue ex:v ; sh:in ( ex:v ex:w ) ] . " ++
  "ex:n ex:p ex:w ."

#guard components (run hasValueInDoc) == [shHasValueCC]

def languageInDoc : String :=
  "ex:S a sh:NodeShape ; sh:targetNode \"Hill\"@en-NZ, \"Berg\"@de, \"Hill\" ; sh:languageIn ( \"en\" \"mi\" ) ."

#guard (run languageInDoc).results.length == 2

/-! ### §2.1.2 / §2.1.4 targetSubjectsOf, targetObjectsOf; §3.6.1.3 custom severity -/

def subjObjDoc : String :=
  "ex:S1 a sh:NodeShape ; sh:targetSubjectsOf ex:p ; sh:nodeKind sh:BlankNode . " ++
  "ex:S2 a sh:NodeShape ; sh:targetObjectsOf ex:p ; sh:nodeKind sh:Literal ; sh:severity ex:Mine . " ++
  "ex:a ex:p ex:b ."

#guard (run subjObjDoc).results.length == 2
#guard (run subjObjDoc).results.map (·.severity) == [.violation, .custom (exIri "Mine")]

/-! ### §3.6.1 sh:deactivated -/

def deactivatedDoc : String :=
  "ex:S a sh:NodeShape ; sh:targetNode ex:n ; sh:deactivated true ; sh:nodeKind sh:Literal ."

#guard (run deactivatedDoc).conforms == true

/-! ### §3.6 the report graph -/

def reportG : Graph := reportToGraph (run maxCountDoc)

#guard reportG.any fun t => t.p == shConforms && t.o == .literal (boolLiteral false)
#guard (reportG.filter fun t => t.p == shResult).length == 1
#guard (reportG.filter fun t => t.p == shSourceConstraintComponent && t.o == .iri shMaxCountCC).length == 1
#guard (reportG.filter fun t => t.p == shResultPath && t.o == .iri (exIri "name")).length == 1
-- Every minted blank node is distinct (the suite's "not shared" precondition).
#guard (dedupLabels (reportG.bnodes)).length == reportG.bnodes.length
-- A conforming report is two triples.
#guard (reportToGraph (run minCountZeroDoc)).length == 2

/-! ### SHACL-SPARQL is named, not silently skipped -/

def sparqlDoc : String :=
  "ex:S a sh:NodeShape ; sh:targetNode ex:n ; sh:sparql [ sh:select \"SELECT $this WHERE { }\" ] ."

#guard (decodeShapesGraph (ttl sparqlDoc)).unsupported == ["sh:sparql", "sh:select"]

end L4Factoidal.SHACL.Tests
