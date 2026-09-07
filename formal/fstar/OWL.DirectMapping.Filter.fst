module OWL.DirectMapping.Filter

(* OWL 2 Direct Semantics — ontology-annotation triple exclusion.
 *
 * Diagnosed in bin/rif-runner/README.md ("Non-Annotation_Entailment"):
 * the OWL 2 RDF-Compatible mapping to the Direct Semantics
 * (https://www.w3.org/TR/owl2-mapping-to-rdf/) treats a predicate
 * declared `rdf:type owl:AnnotationProperty` — and the legacy OWL 1
 * DL vocabulary `rdf:type owl:OntologyProperty` used by ontology-level
 * metadata properties (owl:imports, owl:priorVersion,
 * owl:backwardCompatibleWith, and this test's `dc:title`) — as
 * annotation/ontology-metadata, not part of the "regular" OWL graph
 * that Direct-Semantics entailment reasons over. Triples using such a
 * predicate must be excluded from a graph before it feeds an
 * OWL-Direct closure or the rules layered on top of it (the RIF
 * "OWL-Direct" combination profile), matching the RIF Core corpus's
 * own purpose statement for this test: "annotation properties must be
 * discarded, and do not affect the rules or the conclusions that may
 * be drawn from the ruleset."
 *
 * This is a semantics decision (which triples are "in" the graph
 * Direct Semantics reasons over), so per CLAUDE.md iron rule #1 it
 * lives in F*, not in runner/plumbing code. Deliberately a standalone
 * module rather than an edit to RDF.Graph.Executable.fst — that file
 * is owned by another concurrent work item this wave (OWL closure
 * rules); this filter only needs the `triple`/`rdf_graph`/`wf_iri`
 * types it already exports, no new dependency on its internals.
 *
 * 2026-09-07: EXTENDED to the built-in annotation properties. OWL 2
 * Structural Specification section 5.5 fixes nine IRIs as annotation
 * properties without any declaration triple: rdfs:label, rdfs:comment,
 * rdfs:seeAlso, rdfs:isDefinedBy, owl:deprecated, owl:versionInfo,
 * owl:backwardCompatibleWith, owl:incompatibleWith, owl:priorVersion.
 * A conclusion graph using one of them therefore carries an annotation
 * assertion even though the graph declares nothing, and under the
 * Direct Semantics an AnnotationAssertion contributes no condition to
 * the interpretation, so such a triple must be excluded here on the
 * same ground as a declared one. The list is
 * `OWL.Closure.owl_builtin_annotation_properties`, reused rather than
 * restated so the two places cannot drift.
 *
 * The driving test is `WebOnt-I4.6-005-Direct` (profile-RL/EL/QL), whose
 * conclusion is `C2 rdfs:comment "An example class."`. Its own
 * test:description says "Under the direct semantics, test
 * WebOnt-I4.6-005 must be treated as a positive entailment"; the
 * conclusion ontology holds exactly one annotation axiom, which has no
 * Direct-Semantics content, so the entailment is vacuous. Before this
 * change the F* engine passed it through a DIFFERENT route: the
 * (unsound, now deleted) `owl_rule_named_equivClass_to_sameAs` rule
 * fabricated `C1 owl:sameAs C2` and eq-rep-s copied the comment across.
 * See docs/designissues/2026-09-07-fstar-owl-soundness-audit.md.
 *
 * Still NOT special-cased: `owl:annotatedSource` /
 * `owl:annotatedProperty` / `owl:annotatedTarget` reification triples —
 * no corpus test here exercises those.
 *)

open FStar.List.Tot
open RDF.Graph.Executable

let owl_AnnotationProperty : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#AnnotationProperty");
  "http://www.w3.org/2002/07/owl#AnnotationProperty"

let owl_OntologyProperty : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#OntologyProperty");
  "http://www.w3.org/2002/07/owl#OntologyProperty"

// Is `p` one of the nine built-in annotation properties that OWL 2
// Structural Specification section 5.5 fixes as annotation properties
// with no declaration triple required?
let is_builtin_annotation_predicate (p : wf_iri) : bool =
  mem p owl_builtin_annotation_properties

// Is `p` declared (anywhere in `g`) as an annotation-only predicate,
// i.e. does `g` contain `p rdf:type owl:AnnotationProperty` or the
// legacy `p rdf:type owl:OntologyProperty`?
let is_declared_annotation_predicate (g : rdf_graph) (p : wf_iri) : bool =
  existsb
    (fun (t : triple) ->
       subject_eq t.s (S_IRI p) && t.p = rdf_type &&
       (rdf_term_eq t.o (T_IRI owl_AnnotationProperty) ||
        rdf_term_eq t.o (T_IRI owl_OntologyProperty)))
    g

// An annotation predicate is one the graph declares, or one of the
// built-in nine.
let is_annotation_predicate (g : rdf_graph) (p : wf_iri) : bool =
  is_builtin_annotation_predicate p || is_declared_annotation_predicate g p

// Drop every triple whose predicate is declared annotation/ontology-
// only per `is_declared_annotation_predicate g`. The declaration
// triples (`p rdf:type owl:AnnotationProperty`) themselves use
// `rdf:type` as predicate, which is never itself so declared, so
// they survive this filter — matching the mapping spec, which
// excludes annotation *assertions*, not the annotation-property
// *declarations* that identify them.
let exclude_annotation_triples (g : rdf_graph) : rdf_graph =
  filter (fun (t : triple) -> not (is_annotation_predicate g t.p)) g
