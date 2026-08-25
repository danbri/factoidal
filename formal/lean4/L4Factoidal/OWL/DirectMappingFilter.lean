/-
L4Factoidal.OWL.DirectMappingFilter — annotation-triple exclusion.

Port of `formal/fstar/OWL.DirectMapping.Filter.fst` (71 lines).

The OWL 2 RDF-compatible mapping to the Direct Semantics
(<https://www.w3.org/TR/owl2-mapping-to-rdf/>) treats a predicate
declared `rdf:type owl:AnnotationProperty` — and the legacy OWL 1 DL
`rdf:type owl:OntologyProperty`, used by ontology-level metadata
properties such as `owl:imports` and `owl:priorVersion` — as
annotation, not part of the graph Direct Semantics reasons over.
Triples using such a predicate must be excluded before the graph feeds
an OWL-Direct closure or the rules layered on it.

The RIF Core corpus states the same purpose for its
Non-Annotation_Entailment test: "annotation properties must be
discarded, and do not affect the rules or the conclusions that may be
drawn from the ruleset."

Which triples are IN the graph is a semantics decision, so it lives
here per iron rule #1, not in runner plumbing.

## Scope, stated rather than quietly widened

This handles the "declared as an annotation or ontology property in the
same graph being filtered" case — what the vendored RIF Core corpus
exercises. It does NOT special-case the built-in OWL 2 annotation
properties that need no declaration (`rdfs:label`, `rdfs:comment`,
`owl:versionInfo`), nor the
`owl:annotatedSource`/`owl:annotatedProperty`/`owl:annotatedTarget`
reification triples. No corpus test exercises those, and adding them
speculatively is anti-pattern #4.
-/
import L4Factoidal.RDF.Graph
import L4Factoidal.RDFS.Vocabulary

namespace L4Factoidal.OWL

open L4Factoidal.RDF L4Factoidal.RDFS

def owlAnnotationProperty : WfIri :=
  ⟨"http://www.w3.org/2002/07/owl#AnnotationProperty", rfl⟩

def owlOntologyProperty : WfIri :=
  ⟨"http://www.w3.org/2002/07/owl#OntologyProperty", rfl⟩

/-- Does `g` declare `p` as an annotation-only predicate, anywhere? -/
def isDeclaredAnnotationPredicate (g : L4Factoidal.RDF.Graph) (p : WfIri) : Bool :=
  g.any (fun t =>
    t.s == Subject.iri p && t.p == rdfType &&
    (t.o == Term.iri owlAnnotationProperty || t.o == Term.iri owlOntologyProperty))

/-- Drop every triple whose predicate is so declared.

    The declaration triples themselves use `rdf:type` as their
    predicate, and `rdf:type` is never itself declared an annotation
    property, so they SURVIVE — matching the mapping specification,
    which excludes annotation ASSERTIONS, not the declarations that
    identify them. -/
def excludeAnnotationTriples (g : L4Factoidal.RDF.Graph) : L4Factoidal.RDF.Graph :=
  g.filter (fun t => !(isDeclaredAnnotationPredicate g t.p))

/-! ## Build-time checks -/

private theorem exIri (s : String) : isIri ("http://e/" ++ s) = true := by
  simp [isIri, String.isEmpty]

private def oi (s : String) : WfIri := ⟨"http://e/" ++ s, exIri s⟩

private def decl : Triple :=
  ⟨.iri (oi "title"), rdfType, .iri owlAnnotationProperty⟩
private def onto : Triple :=
  ⟨.iri (oi "imports"), rdfType, .iri owlOntologyProperty⟩
private def ann : Triple :=
  ⟨.iri (oi "doc"), oi "title", .iri (oi "SomeTitle")⟩
private def annO : Triple :=
  ⟨.iri (oi "doc"), oi "imports", .iri (oi "Other")⟩
private def regular : Triple :=
  ⟨.iri (oi "a"), oi "p", .iri (oi "b")⟩

private def g0 : L4Factoidal.RDF.Graph := [decl, onto, ann, annO, regular]

#guard isDeclaredAnnotationPredicate g0 (oi "title")
#guard isDeclaredAnnotationPredicate g0 (oi "imports")
#guard !isDeclaredAnnotationPredicate g0 (oi "p")
#guard !isDeclaredAnnotationPredicate g0 rdfType

/-! The annotation ASSERTIONS go; the regular triple stays. -/

#guard !(excludeAnnotationTriples g0).contains ann
#guard !(excludeAnnotationTriples g0).contains annO
#guard (excludeAnnotationTriples g0).contains regular

/-! The DECLARATIONS survive, because their predicate is `rdf:type` and
    `rdf:type` is never itself declared an annotation property. This is
    the case a filter written as "drop every triple mentioning an
    annotation property" would get wrong. -/

#guard (excludeAnnotationTriples g0).contains decl
#guard (excludeAnnotationTriples g0).contains onto
#guard (excludeAnnotationTriples g0).length == 3

/-! With no declaration in the graph, nothing is dropped — the filter is
    driven by what the graph says, not by a built-in list. -/

#guard (excludeAnnotationTriples [ann, regular]).length == 2

/-! Both vocabularies are needed: the legacy `owl:OntologyProperty` is
    not a synonym anyone can drop. -/

#guard (excludeAnnotationTriples [onto, annO]).length == 1
#guard (excludeAnnotationTriples [decl, ann]).length == 1

end L4Factoidal.OWL
