/-
L4Factoidal.SHACL.Vocabulary — the IRIs of the SHACL Core vocabulary
(W3C SHACL Recommendation, 20 July 2017, https://www.w3.org/TR/shacl/),
plus the few RDF / RDFS / OWL / XSD IRIs the shapes decoder and the
validator need.

Port of `formal/fstar/SHACL.Validation.fst` sections 1 and 11b (the
`assert_norm (is_iri …)` constants). In Lean the well-formedness
witness is `rfl` — kernel evaluation of `isIri` — so every constant is
a `WfIri` with no runtime check.

Scope: SHACL Core (§2 shapes and targets, §2.3.1 property paths, §3
validation, §4 the Core constraint components). The SHACL-SPARQL
vocabulary (sh:sparql, sh:select, sh:ask, sh:validator, sh:parameter)
appears ONLY in `sparqlFeaturePredicates` — the predicates whose
presence in a shapes graph the harness reports as `unsupported`, never
silently skipped. SHACL 1.2 additions (sh:singleLine, sh:memberShape,
sh:reifierShape, …) are not ported: the vendored suite
(`third_party/testing/shacl/data-shapes-test-suite`) is the 1.1 suite.
-/
import L4Factoidal.RDF.Core
import L4Factoidal.RDFS.Vocabulary

namespace L4Factoidal.SHACL

open L4Factoidal.RDF

/-- The SHACL namespace, `http://www.w3.org/ns/shacl#`. -/
def shNs : String := "http://www.w3.org/ns/shacl#"

/-! ## Shape classes (§2) -/

def shNodeShape     : WfIri := ⟨"http://www.w3.org/ns/shacl#NodeShape", rfl⟩
def shPropertyShape : WfIri := ⟨"http://www.w3.org/ns/shacl#PropertyShape", rfl⟩

/-! ## Targets (§2.1) -/

def shTargetClass      : WfIri := ⟨"http://www.w3.org/ns/shacl#targetClass", rfl⟩
def shTargetNode       : WfIri := ⟨"http://www.w3.org/ns/shacl#targetNode", rfl⟩
def shTargetSubjectsOf : WfIri := ⟨"http://www.w3.org/ns/shacl#targetSubjectsOf", rfl⟩
def shTargetObjectsOf  : WfIri := ⟨"http://www.w3.org/ns/shacl#targetObjectsOf", rfl⟩

/-! ## Shape-level properties (§2.2, §2.3) -/

def shPath        : WfIri := ⟨"http://www.w3.org/ns/shacl#path", rfl⟩
def shProperty    : WfIri := ⟨"http://www.w3.org/ns/shacl#property", rfl⟩
def shSeverity    : WfIri := ⟨"http://www.w3.org/ns/shacl#severity", rfl⟩
def shMessage     : WfIri := ⟨"http://www.w3.org/ns/shacl#message", rfl⟩
def shDeactivated : WfIri := ⟨"http://www.w3.org/ns/shacl#deactivated", rfl⟩

/-! ## Property paths (§2.3.1) -/

def shInversePath     : WfIri := ⟨"http://www.w3.org/ns/shacl#inversePath", rfl⟩
def shAlternativePath : WfIri := ⟨"http://www.w3.org/ns/shacl#alternativePath", rfl⟩
def shZeroOrMorePath  : WfIri := ⟨"http://www.w3.org/ns/shacl#zeroOrMorePath", rfl⟩
def shOneOrMorePath   : WfIri := ⟨"http://www.w3.org/ns/shacl#oneOrMorePath", rfl⟩
def shZeroOrOnePath   : WfIri := ⟨"http://www.w3.org/ns/shacl#zeroOrOnePath", rfl⟩

/-! ## Constraint parameters (§4) -/

def shClass        : WfIri := ⟨"http://www.w3.org/ns/shacl#class", rfl⟩
def shDatatype     : WfIri := ⟨"http://www.w3.org/ns/shacl#datatype", rfl⟩
def shNodeKind     : WfIri := ⟨"http://www.w3.org/ns/shacl#nodeKind", rfl⟩
def shMinCount     : WfIri := ⟨"http://www.w3.org/ns/shacl#minCount", rfl⟩
def shMaxCount     : WfIri := ⟨"http://www.w3.org/ns/shacl#maxCount", rfl⟩
def shMinExclusive : WfIri := ⟨"http://www.w3.org/ns/shacl#minExclusive", rfl⟩
def shMinInclusive : WfIri := ⟨"http://www.w3.org/ns/shacl#minInclusive", rfl⟩
def shMaxExclusive : WfIri := ⟨"http://www.w3.org/ns/shacl#maxExclusive", rfl⟩
def shMaxInclusive : WfIri := ⟨"http://www.w3.org/ns/shacl#maxInclusive", rfl⟩
def shMinLength    : WfIri := ⟨"http://www.w3.org/ns/shacl#minLength", rfl⟩
def shMaxLength    : WfIri := ⟨"http://www.w3.org/ns/shacl#maxLength", rfl⟩
def shPattern      : WfIri := ⟨"http://www.w3.org/ns/shacl#pattern", rfl⟩
def shFlags        : WfIri := ⟨"http://www.w3.org/ns/shacl#flags", rfl⟩
def shLanguageIn   : WfIri := ⟨"http://www.w3.org/ns/shacl#languageIn", rfl⟩
def shUniqueLang   : WfIri := ⟨"http://www.w3.org/ns/shacl#uniqueLang", rfl⟩
def shEquals       : WfIri := ⟨"http://www.w3.org/ns/shacl#equals", rfl⟩
def shDisjoint     : WfIri := ⟨"http://www.w3.org/ns/shacl#disjoint", rfl⟩
def shLessThan     : WfIri := ⟨"http://www.w3.org/ns/shacl#lessThan", rfl⟩
def shLessThanOrEquals : WfIri := ⟨"http://www.w3.org/ns/shacl#lessThanOrEquals", rfl⟩
def shNot          : WfIri := ⟨"http://www.w3.org/ns/shacl#not", rfl⟩
def shAnd          : WfIri := ⟨"http://www.w3.org/ns/shacl#and", rfl⟩
def shOr           : WfIri := ⟨"http://www.w3.org/ns/shacl#or", rfl⟩
def shXone         : WfIri := ⟨"http://www.w3.org/ns/shacl#xone", rfl⟩
def shNode         : WfIri := ⟨"http://www.w3.org/ns/shacl#node", rfl⟩
def shQualifiedValueShape : WfIri := ⟨"http://www.w3.org/ns/shacl#qualifiedValueShape", rfl⟩
def shQualifiedMinCount   : WfIri := ⟨"http://www.w3.org/ns/shacl#qualifiedMinCount", rfl⟩
def shQualifiedMaxCount   : WfIri := ⟨"http://www.w3.org/ns/shacl#qualifiedMaxCount", rfl⟩
def shQualifiedValueShapesDisjoint : WfIri :=
  ⟨"http://www.w3.org/ns/shacl#qualifiedValueShapesDisjoint", rfl⟩
def shClosed            : WfIri := ⟨"http://www.w3.org/ns/shacl#closed", rfl⟩
def shIgnoredProperties : WfIri := ⟨"http://www.w3.org/ns/shacl#ignoredProperties", rfl⟩
def shHasValue          : WfIri := ⟨"http://www.w3.org/ns/shacl#hasValue", rfl⟩
def shIn                : WfIri := ⟨"http://www.w3.org/ns/shacl#in", rfl⟩

/-! ## Node kinds (§4.1.3) -/

def shNkBlankNode          : WfIri := ⟨"http://www.w3.org/ns/shacl#BlankNode", rfl⟩
def shNkIRI                : WfIri := ⟨"http://www.w3.org/ns/shacl#IRI", rfl⟩
def shNkLiteral            : WfIri := ⟨"http://www.w3.org/ns/shacl#Literal", rfl⟩
def shNkBlankNodeOrIRI     : WfIri := ⟨"http://www.w3.org/ns/shacl#BlankNodeOrIRI", rfl⟩
def shNkBlankNodeOrLiteral : WfIri := ⟨"http://www.w3.org/ns/shacl#BlankNodeOrLiteral", rfl⟩
def shNkIRIOrLiteral       : WfIri := ⟨"http://www.w3.org/ns/shacl#IRIOrLiteral", rfl⟩

/-! ## Severities (§3.6.1.3) -/

def shInfo      : WfIri := ⟨"http://www.w3.org/ns/shacl#Info", rfl⟩
def shWarning   : WfIri := ⟨"http://www.w3.org/ns/shacl#Warning", rfl⟩
def shViolation : WfIri := ⟨"http://www.w3.org/ns/shacl#Violation", rfl⟩

/-! ## Validation report vocabulary (§3.6) -/

def shValidationReport : WfIri := ⟨"http://www.w3.org/ns/shacl#ValidationReport", rfl⟩
def shValidationResult : WfIri := ⟨"http://www.w3.org/ns/shacl#ValidationResult", rfl⟩
def shConforms         : WfIri := ⟨"http://www.w3.org/ns/shacl#conforms", rfl⟩
def shResult           : WfIri := ⟨"http://www.w3.org/ns/shacl#result", rfl⟩
def shFocusNode        : WfIri := ⟨"http://www.w3.org/ns/shacl#focusNode", rfl⟩
def shResultPath       : WfIri := ⟨"http://www.w3.org/ns/shacl#resultPath", rfl⟩
def shValue            : WfIri := ⟨"http://www.w3.org/ns/shacl#value", rfl⟩
def shSourceShape      : WfIri := ⟨"http://www.w3.org/ns/shacl#sourceShape", rfl⟩
def shSourceConstraintComponent : WfIri :=
  ⟨"http://www.w3.org/ns/shacl#sourceConstraintComponent", rfl⟩
def shSourceConstraint : WfIri := ⟨"http://www.w3.org/ns/shacl#sourceConstraint", rfl⟩
def shResultSeverity   : WfIri := ⟨"http://www.w3.org/ns/shacl#resultSeverity", rfl⟩
def shResultMessage    : WfIri := ⟨"http://www.w3.org/ns/shacl#resultMessage", rfl⟩
def shDetail           : WfIri := ⟨"http://www.w3.org/ns/shacl#detail", rfl⟩

/-! ## Constraint component IRIs (§4, one per Core component) -/

def shClassCC        : WfIri := ⟨"http://www.w3.org/ns/shacl#ClassConstraintComponent", rfl⟩
def shDatatypeCC     : WfIri := ⟨"http://www.w3.org/ns/shacl#DatatypeConstraintComponent", rfl⟩
def shNodeKindCC     : WfIri := ⟨"http://www.w3.org/ns/shacl#NodeKindConstraintComponent", rfl⟩
def shMinCountCC     : WfIri := ⟨"http://www.w3.org/ns/shacl#MinCountConstraintComponent", rfl⟩
def shMaxCountCC     : WfIri := ⟨"http://www.w3.org/ns/shacl#MaxCountConstraintComponent", rfl⟩
def shMinExclusiveCC : WfIri := ⟨"http://www.w3.org/ns/shacl#MinExclusiveConstraintComponent", rfl⟩
def shMinInclusiveCC : WfIri := ⟨"http://www.w3.org/ns/shacl#MinInclusiveConstraintComponent", rfl⟩
def shMaxExclusiveCC : WfIri := ⟨"http://www.w3.org/ns/shacl#MaxExclusiveConstraintComponent", rfl⟩
def shMaxInclusiveCC : WfIri := ⟨"http://www.w3.org/ns/shacl#MaxInclusiveConstraintComponent", rfl⟩
def shMinLengthCC    : WfIri := ⟨"http://www.w3.org/ns/shacl#MinLengthConstraintComponent", rfl⟩
def shMaxLengthCC    : WfIri := ⟨"http://www.w3.org/ns/shacl#MaxLengthConstraintComponent", rfl⟩
def shPatternCC      : WfIri := ⟨"http://www.w3.org/ns/shacl#PatternConstraintComponent", rfl⟩
def shLanguageInCC   : WfIri := ⟨"http://www.w3.org/ns/shacl#LanguageInConstraintComponent", rfl⟩
def shUniqueLangCC   : WfIri := ⟨"http://www.w3.org/ns/shacl#UniqueLangConstraintComponent", rfl⟩
def shEqualsCC       : WfIri := ⟨"http://www.w3.org/ns/shacl#EqualsConstraintComponent", rfl⟩
def shDisjointCC     : WfIri := ⟨"http://www.w3.org/ns/shacl#DisjointConstraintComponent", rfl⟩
def shLessThanCC     : WfIri := ⟨"http://www.w3.org/ns/shacl#LessThanConstraintComponent", rfl⟩
def shLessThanOrEqualsCC : WfIri :=
  ⟨"http://www.w3.org/ns/shacl#LessThanOrEqualsConstraintComponent", rfl⟩
def shNotCC          : WfIri := ⟨"http://www.w3.org/ns/shacl#NotConstraintComponent", rfl⟩
def shAndCC          : WfIri := ⟨"http://www.w3.org/ns/shacl#AndConstraintComponent", rfl⟩
def shOrCC           : WfIri := ⟨"http://www.w3.org/ns/shacl#OrConstraintComponent", rfl⟩
def shXoneCC         : WfIri := ⟨"http://www.w3.org/ns/shacl#XoneConstraintComponent", rfl⟩
def shNodeCC         : WfIri := ⟨"http://www.w3.org/ns/shacl#NodeConstraintComponent", rfl⟩
def shQualifiedMinCountCC : WfIri :=
  ⟨"http://www.w3.org/ns/shacl#QualifiedMinCountConstraintComponent", rfl⟩
def shQualifiedMaxCountCC : WfIri :=
  ⟨"http://www.w3.org/ns/shacl#QualifiedMaxCountConstraintComponent", rfl⟩
def shClosedCC       : WfIri := ⟨"http://www.w3.org/ns/shacl#ClosedConstraintComponent", rfl⟩
def shHasValueCC     : WfIri := ⟨"http://www.w3.org/ns/shacl#HasValueConstraintComponent", rfl⟩
def shInCC           : WfIri := ⟨"http://www.w3.org/ns/shacl#InConstraintComponent", rfl⟩

/-! ## SHACL-SPARQL predicates — recognised only to be reported

Part 2 of the Recommendation (SPARQL-based constraints, §5–§6) is out of
this port's scope. A shapes graph using any of these predicates is
reported as `unsupported` by the harness (counted in the denominator,
named), per the project's score-reporting rule. -/

def shSparql            : WfIri := ⟨"http://www.w3.org/ns/shacl#sparql", rfl⟩
def shSelect            : WfIri := ⟨"http://www.w3.org/ns/shacl#select", rfl⟩
def shAsk               : WfIri := ⟨"http://www.w3.org/ns/shacl#ask", rfl⟩
def shTarget            : WfIri := ⟨"http://www.w3.org/ns/shacl#target", rfl⟩
def shValidator         : WfIri := ⟨"http://www.w3.org/ns/shacl#validator", rfl⟩
def shNodeValidator     : WfIri := ⟨"http://www.w3.org/ns/shacl#nodeValidator", rfl⟩
def shPropertyValidator : WfIri := ⟨"http://www.w3.org/ns/shacl#propertyValidator", rfl⟩
def shParameter         : WfIri := ⟨"http://www.w3.org/ns/shacl#parameter", rfl⟩

/-- The predicates whose presence marks a SHACL-SPARQL shapes graph. -/
def sparqlFeaturePredicates : List (WfIri × String) :=
  [(shSparql, "sh:sparql"), (shSelect, "sh:select"), (shAsk, "sh:ask"),
   (shTarget, "sh:target"), (shValidator, "sh:validator"),
   (shNodeValidator, "sh:nodeValidator"), (shPropertyValidator, "sh:propertyValidator"),
   (shParameter, "sh:parameter")]

/-! ## RDF / RDFS / OWL IRIs used by the decoder -/

def rdfType        : WfIri := RDFS.rdfType
def rdfFirst       : WfIri := RDFS.rdfFirst
def rdfRest        : WfIri := RDFS.rdfRest
def rdfNil         : WfIri := RDFS.rdfNil
def rdfsClass      : WfIri := RDFS.rdfsClass
def rdfsSubClassOf : WfIri := RDFS.rdfsSubClassOf
def owlClass       : WfIri := ⟨"http://www.w3.org/2002/07/owl#Class", rfl⟩

/-! ## XSD datatypes the ill-formed-literal check knows (§4.1.2)

`xsd:string`, `xsd:integer`, `xsd:decimal`, `xsd:double`, `xsd:boolean`
are in `RDF.Core`; the rest of the family is here. -/

def xsdFloat              : WfIri := ⟨"http://www.w3.org/2001/XMLSchema#float", rfl⟩
def xsdDateTime           : WfIri := ⟨"http://www.w3.org/2001/XMLSchema#dateTime", rfl⟩
def xsdLong               : WfIri := ⟨"http://www.w3.org/2001/XMLSchema#long", rfl⟩
def xsdInt                : WfIri := ⟨"http://www.w3.org/2001/XMLSchema#int", rfl⟩
def xsdShort              : WfIri := ⟨"http://www.w3.org/2001/XMLSchema#short", rfl⟩
def xsdByte               : WfIri := ⟨"http://www.w3.org/2001/XMLSchema#byte", rfl⟩
def xsdUnsignedLong       : WfIri := ⟨"http://www.w3.org/2001/XMLSchema#unsignedLong", rfl⟩
def xsdUnsignedInt        : WfIri := ⟨"http://www.w3.org/2001/XMLSchema#unsignedInt", rfl⟩
def xsdUnsignedShort      : WfIri := ⟨"http://www.w3.org/2001/XMLSchema#unsignedShort", rfl⟩
def xsdUnsignedByte       : WfIri := ⟨"http://www.w3.org/2001/XMLSchema#unsignedByte", rfl⟩
def xsdNonNegativeInteger : WfIri := ⟨"http://www.w3.org/2001/XMLSchema#nonNegativeInteger", rfl⟩
def xsdPositiveInteger    : WfIri := ⟨"http://www.w3.org/2001/XMLSchema#positiveInteger", rfl⟩
def xsdNonPositiveInteger : WfIri := ⟨"http://www.w3.org/2001/XMLSchema#nonPositiveInteger", rfl⟩
def xsdNegativeInteger    : WfIri := ⟨"http://www.w3.org/2001/XMLSchema#negativeInteger", rfl⟩

end L4Factoidal.SHACL
