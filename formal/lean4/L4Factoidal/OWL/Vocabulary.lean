/-
L4Factoidal.OWL.Vocabulary — every IRI the ported OWL 2 RL/RDF rule
rows mention.

Port of the vocabulary blocks of `formal/fstar/OWL.RL.Spec.fst`
(lines 109-182, 623-681, 1082-1097) and `formal/fstar/OWL.Closure.fsti`
(the `owl_*` / `o_owl_*` constants interleaved with the rule bodies —
the F* module's own banner records that this interleaving is why they
never moved to `RDF.Vocabulary`).

Only the terms the ported rows name are here. The rows are those of
the OWL 2 RL/RDF rule tables,
https://www.w3.org/TR/owl2-profiles/#Reasoning_in_OWL_2_RL_and_RDF_Graphs_using_Rules
— see `RLRules.lean` for which rows are ported and which are not.

Every constant is a `WfIri` whose well-formedness witness is `rfl`:
the kernel evaluates `isIri` on the literal string at elaboration
time, so a mistyped IRI is a build error rather than a runtime
surprise. That is the Lean counterpart of the F* tree's
`assert_norm (is_iri "...")` witnesses.

The five RDF/RDFS terms the OWL rows share with the rdfs-core fragment
are re-exported from `L4Factoidal.RDFS.Vocabulary` rather than
redefined, so the two closures agree on them by construction and not
by inspection.
-/
import L4Factoidal.RDF.Core
import L4Factoidal.RDFS.Vocabulary

namespace L4Factoidal.OWL.RL

open L4Factoidal.RDF

/-! ## Re-exports from the rdfs-core vocabulary

`rdf:type`, `rdfs:subClassOf`, `rdfs:subPropertyOf`, `rdfs:domain`,
`rdfs:range` — named by Table 4's prp-dom/prp-rng/prp-spo1, Table 6's
cax-sco and most of Table 8. `abbrev` (not `def`) so the kernel still
unfolds them inside the `decide`/`rfl` reductions the `#guard` tests
run. -/

abbrev rdfType : WfIri := L4Factoidal.RDFS.rdfType
abbrev rdfsSubClassOf : WfIri := L4Factoidal.RDFS.rdfsSubClassOf
abbrev rdfsSubPropertyOf : WfIri := L4Factoidal.RDFS.rdfsSubPropertyOf
abbrev rdfsDomain : WfIri := L4Factoidal.RDFS.rdfsDomain
abbrev rdfsRange : WfIri := L4Factoidal.RDFS.rdfsRange
/-- `rdfs:Datatype` — the class of datatypes (RDF 1.1 Schema §3.5).
Named by Table 7's dt-type1 and by the XSD axiom table of the
`[ext]` section in `RLRules.lean`. -/
abbrev rdfsDatatype : WfIri := L4Factoidal.RDFS.rdfsDatatype

/-! ## RDF collection vocabulary — RDF 1.1 Schema §5.1

The `LIST[?x, ?e1, ..., ?en]` premise the table writes for cls-int1,
cls-int2, cls-uni, cls-oo, prp-spo2, prp-key, scm-int and scm-uni is
an rdf:first/rdf:rest chain terminated by rdf:nil. `RLRules.lean`
turns that notation into the two inductive relations `ListMember` and
`ListDenotes`. -/

def rdfFirst : WfIri :=
  ⟨"http://www.w3.org/1999/02/22-rdf-syntax-ns#first", rfl⟩

def rdfRest : WfIri :=
  ⟨"http://www.w3.org/1999/02/22-rdf-syntax-ns#rest", rfl⟩

def rdfNil : WfIri :=
  ⟨"http://www.w3.org/1999/02/22-rdf-syntax-ns#nil", rfl⟩

/-! ## Table 4 — equality and property axioms -/

/-- `owl:sameAs` — the conclusion predicate of eq-sym, eq-trans,
eq-ref, prp-fp, prp-ifp, prp-key, cls-maxc2. -/
def owlSameAs : WfIri :=
  ⟨"http://www.w3.org/2002/07/owl#sameAs", rfl⟩

/-- `owl:differentFrom` — the second premise of the eq-diff1 clash. -/
def owlDifferentFrom : WfIri :=
  ⟨"http://www.w3.org/2002/07/owl#differentFrom", rfl⟩

def owlFunctionalProperty : WfIri :=
  ⟨"http://www.w3.org/2002/07/owl#FunctionalProperty", rfl⟩

def owlInverseFunctionalProperty : WfIri :=
  ⟨"http://www.w3.org/2002/07/owl#InverseFunctionalProperty", rfl⟩

def owlIrreflexiveProperty : WfIri :=
  ⟨"http://www.w3.org/2002/07/owl#IrreflexiveProperty", rfl⟩

def owlSymmetricProperty : WfIri :=
  ⟨"http://www.w3.org/2002/07/owl#SymmetricProperty", rfl⟩

def owlAsymmetricProperty : WfIri :=
  ⟨"http://www.w3.org/2002/07/owl#AsymmetricProperty", rfl⟩

def owlTransitiveProperty : WfIri :=
  ⟨"http://www.w3.org/2002/07/owl#TransitiveProperty", rfl⟩

def owlPropertyChainAxiom : WfIri :=
  ⟨"http://www.w3.org/2002/07/owl#propertyChainAxiom", rfl⟩

def owlEquivalentProperty : WfIri :=
  ⟨"http://www.w3.org/2002/07/owl#equivalentProperty", rfl⟩

def owlPropertyDisjointWith : WfIri :=
  ⟨"http://www.w3.org/2002/07/owl#propertyDisjointWith", rfl⟩

def owlInverseOf : WfIri :=
  ⟨"http://www.w3.org/2002/07/owl#inverseOf", rfl⟩

def owlHasKey : WfIri :=
  ⟨"http://www.w3.org/2002/07/owl#hasKey", rfl⟩

/-! ### owl:NegativePropertyAssertion reification — prp-npa1 / prp-npa2 -/

def owlSourceIndividual : WfIri :=
  ⟨"http://www.w3.org/2002/07/owl#sourceIndividual", rfl⟩

def owlAssertionProperty : WfIri :=
  ⟨"http://www.w3.org/2002/07/owl#assertionProperty", rfl⟩

def owlTargetIndividual : WfIri :=
  ⟨"http://www.w3.org/2002/07/owl#targetIndividual", rfl⟩

def owlTargetValue : WfIri :=
  ⟨"http://www.w3.org/2002/07/owl#targetValue", rfl⟩

/-! ## Table 5 / Table 6 — classes and class axioms -/

def owlClass : WfIri :=
  ⟨"http://www.w3.org/2002/07/owl#Class", rfl⟩

def owlThing : WfIri :=
  ⟨"http://www.w3.org/2002/07/owl#Thing", rfl⟩

def owlNothing : WfIri :=
  ⟨"http://www.w3.org/2002/07/owl#Nothing", rfl⟩

def owlIntersectionOf : WfIri :=
  ⟨"http://www.w3.org/2002/07/owl#intersectionOf", rfl⟩

def owlUnionOf : WfIri :=
  ⟨"http://www.w3.org/2002/07/owl#unionOf", rfl⟩

def owlComplementOf : WfIri :=
  ⟨"http://www.w3.org/2002/07/owl#complementOf", rfl⟩

def owlSomeValuesFrom : WfIri :=
  ⟨"http://www.w3.org/2002/07/owl#someValuesFrom", rfl⟩

def owlAllValuesFrom : WfIri :=
  ⟨"http://www.w3.org/2002/07/owl#allValuesFrom", rfl⟩

def owlOnProperty : WfIri :=
  ⟨"http://www.w3.org/2002/07/owl#onProperty", rfl⟩

def owlHasValue : WfIri :=
  ⟨"http://www.w3.org/2002/07/owl#hasValue", rfl⟩

def owlHasSelf : WfIri :=
  ⟨"http://www.w3.org/2002/07/owl#hasSelf", rfl⟩

def owlMaxCardinality : WfIri :=
  ⟨"http://www.w3.org/2002/07/owl#maxCardinality", rfl⟩

def owlMaxQualifiedCardinality : WfIri :=
  ⟨"http://www.w3.org/2002/07/owl#maxQualifiedCardinality", rfl⟩

def owlOnClass : WfIri :=
  ⟨"http://www.w3.org/2002/07/owl#onClass", rfl⟩

def owlOneOf : WfIri :=
  ⟨"http://www.w3.org/2002/07/owl#oneOf", rfl⟩

def owlEquivalentClass : WfIri :=
  ⟨"http://www.w3.org/2002/07/owl#equivalentClass", rfl⟩

def owlDisjointWith : WfIri :=
  ⟨"http://www.w3.org/2002/07/owl#disjointWith", rfl⟩

def owlAllDisjointClasses : WfIri :=
  ⟨"http://www.w3.org/2002/07/owl#AllDisjointClasses", rfl⟩

def owlMembers : WfIri :=
  ⟨"http://www.w3.org/2002/07/owl#members", rfl⟩

/-! ## Cardinality literals

Table 5's cls-maxc1/cls-maxc2/cls-maxqc1..4 rows quote
`"0"^^xsd:nonNegativeInteger` and `"1"^^xsd:nonNegativeInteger`
LITERALLY. The transcription matches the lexical form the
Recommendation prints, so a graph writing the same value as `"00"` or
`"+1"` is not matched — the same delta the F* `lit_nni_0` banner
records. Numeric value-space matching is an engine question, not a
rule-table one. -/

def xsdNonNegativeInteger : WfIri :=
  ⟨"http://www.w3.org/2001/XMLSchema#nonNegativeInteger", rfl⟩

/-- `"0"^^xsd:nonNegativeInteger`. -/
def litNni0 : WfLiteral :=
  ⟨{ lexicalForm := "0", datatype := xsdNonNegativeInteger,
     langTag := none, direction := none }, rfl⟩

/-- `"1"^^xsd:nonNegativeInteger`. -/
def litNni1 : WfLiteral :=
  ⟨{ lexicalForm := "1", datatype := xsdNonNegativeInteger,
     langTag := none, direction := none }, rfl⟩

/-! ## The self-restriction literal

Table 6's cls-hs1 and cls-hs2 rows quote `"true"^^xsd:boolean`
LITERALLY, the same way the cardinality rows quote their
`xsd:nonNegativeInteger` values. The transcription matches the lexical
form the Recommendation prints, so a graph writing the same value as
`"1"^^xsd:boolean` is not matched: the lexical mapping of
`xsd:boolean` is not injective. Value-space matching is an engine
question, not a rule-table one. -/

/-- `"true"^^xsd:boolean` — the object of the `owl:hasSelf` premise of
cls-hs1 and cls-hs2. -/
def litTrueBoolean : WfLiteral :=
  ⟨{ lexicalForm := "true", datatype := xsdBoolean,
     langTag := none, direction := none }, rfl⟩

/-! ## Vocabulary the `[ext]` rows name

Nothing below is named by a W3C table row. Each constant is used by
exactly one `[ext]` row of `RLRules.lean`, whose doc comment carries
the OWL 2 RDF-Based Semantics condition it relies on. -/

/-- `owl:ReflexiveProperty` — the driving premise of prp-rfl. -/
def owlReflexiveProperty : WfIri :=
  ⟨"http://www.w3.org/2002/07/owl#ReflexiveProperty", rfl⟩

/-- `owl:ObjectProperty` — the driving premise of the min-cardinality
comprehension row. -/
def owlObjectProperty : WfIri :=
  ⟨"http://www.w3.org/2002/07/owl#ObjectProperty", rfl⟩

/-- `owl:Restriction` — the class of restriction class expressions. -/
def owlRestriction : WfIri :=
  ⟨"http://www.w3.org/2002/07/owl#Restriction", rfl⟩

/-- `owl:minCardinality`. -/
def owlMinCardinality : WfIri :=
  ⟨"http://www.w3.org/2002/07/owl#minCardinality", rfl⟩

/-- The remaining three members of the OWL 2 cardinality family. The
unqualified `owl:cardinality` and the two qualified forms complete the
set the query rewriter classifies on (`OWL/QueryRewriteRestriction.lean`);
`owl:maxCardinality`, `owl:maxQualifiedCardinality` and
`owl:minCardinality` were already here. -/
def owlCardinality : WfIri :=
  ⟨"http://www.w3.org/2002/07/owl#cardinality", rfl⟩

def owlMinQualifiedCardinality : WfIri :=
  ⟨"http://www.w3.org/2002/07/owl#minQualifiedCardinality", rfl⟩

def owlQualifiedCardinality : WfIri :=
  ⟨"http://www.w3.org/2002/07/owl#qualifiedCardinality", rfl⟩

/-- `"1"^^xsd:int` — the OWL 1 RDF mapping's spelling of the
cardinality value 1, which the WebOnt-era conclusion documents use.
`litNni1` is the OWL 2 spelling of the same VALUE; the comprehension
row emits both, see its doc comment. -/
def litInt1 : WfLiteral :=
  ⟨{ lexicalForm := "1",
     datatype := ⟨"http://www.w3.org/2001/XMLSchema#int", rfl⟩,
     langTag := none, direction := none }, rfl⟩

/-! ### The XSD numeric tower

The XSD IRIs the `xsdAxioms` row asserts a subtype tower over. `xsd:string`,
`xsd:integer`, `xsd:decimal`, `xsd:double` and `xsd:boolean` come from
`RDF/Core.lean`; the derived numeric types below have no other use in
this tree. -/

def xsdLong : WfIri := ⟨"http://www.w3.org/2001/XMLSchema#long", rfl⟩
def xsdIntIri : WfIri := ⟨"http://www.w3.org/2001/XMLSchema#int", rfl⟩
def xsdShort : WfIri := ⟨"http://www.w3.org/2001/XMLSchema#short", rfl⟩
def xsdByte : WfIri := ⟨"http://www.w3.org/2001/XMLSchema#byte", rfl⟩
def xsdPositiveInteger : WfIri :=
  ⟨"http://www.w3.org/2001/XMLSchema#positiveInteger", rfl⟩
def xsdUnsignedLong : WfIri :=
  ⟨"http://www.w3.org/2001/XMLSchema#unsignedLong", rfl⟩
def xsdUnsignedInt : WfIri :=
  ⟨"http://www.w3.org/2001/XMLSchema#unsignedInt", rfl⟩
def xsdUnsignedShort : WfIri :=
  ⟨"http://www.w3.org/2001/XMLSchema#unsignedShort", rfl⟩
def xsdUnsignedByte : WfIri :=
  ⟨"http://www.w3.org/2001/XMLSchema#unsignedByte", rfl⟩
def xsdNonPositiveInteger : WfIri :=
  ⟨"http://www.w3.org/2001/XMLSchema#nonPositiveInteger", rfl⟩
def xsdNegativeInteger : WfIri :=
  ⟨"http://www.w3.org/2001/XMLSchema#negativeInteger", rfl⟩

/-- The XSD namespace, as the `xsdMentions` guard tests it. -/
def xsdNamespace : String := "http://www.w3.org/2001/XMLSchema#"

/-- Is this IRI in the XSD namespace? -/
def iriInXsdNs (i : WfIri) : Bool := i.val.startsWith xsdNamespace

end L4Factoidal.OWL.RL
