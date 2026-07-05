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
 * Scope note: this is the "declared as an annotation/ontology
 * property in the same graph being filtered" case, i.e. what the
 * vendored RIF Core corpus exercises. It does not (yet) special-case
 * the built-in OWL 2 annotation properties that need no explicit
 * declaration (rdfs:label, rdfs:comment, owl:versionInfo, ...) nor
 * `owl:annotatedSource`/`owl:annotatedProperty`/`owl:annotatedTarget`
 * reification triples — no corpus test here exercises those, and
 * adding them speculatively without a driving test would be exactly
 * the "figure it out" over-reach the project's anti-patterns warn
 * against (docs/claude-rules/anti-patterns.md #4).
 *)

open FStar.List.Tot
open RDF.Graph.Executable

let owl_AnnotationProperty : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#AnnotationProperty");
  "http://www.w3.org/2002/07/owl#AnnotationProperty"

let owl_OntologyProperty : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#OntologyProperty");
  "http://www.w3.org/2002/07/owl#OntologyProperty"

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

// Drop every triple whose predicate is declared annotation/ontology-
// only per `is_declared_annotation_predicate g`. The declaration
// triples (`p rdf:type owl:AnnotationProperty`) themselves use
// `rdf:type` as predicate, which is never itself so declared, so
// they survive this filter — matching the mapping spec, which
// excludes annotation *assertions*, not the annotation-property
// *declarations* that identify them.
let exclude_annotation_triples (g : rdf_graph) : rdf_graph =
  filter (fun (t : triple) -> not (is_declared_annotation_predicate g t.p)) g
