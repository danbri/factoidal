module OWL.Vocabulary

(* Shared OWL + RDF vocabulary IRI constants.
 *
 * Per #209 (Tableau audit): for a long time the same OWL IRI strings
 * were defined in two places — Tableau.fst (no suffix) and
 * OWL.QueryRewrite.fst (`_iri` suffix) — with a comment in
 * OWL.QueryRewrite.fst:76-80 noting the deliberate duplication. This
 * module is the single source of truth.
 *
 * Convention: NO `_iri` suffix. The wf_iri type already says "this is
 * an IRI"; the suffix was redundant. OWL.QueryRewrite.fst will
 * migrate at its own pace; for now it can keep its `owl_X_iri`
 * aliases as forwarders to these.
 *
 * Coverage:
 *   - Class-expression bookkeeping (intersectionOf, unionOf, ...)
 *   - Restrictions (Restriction class + onProperty, someValuesFrom,
 *     allValuesFrom, hasValue, cardinality family, onClass)
 *   - rdf:first / rdf:rest / rdf:nil for collection chains
 *   - Top-level OWL classes (Class, Thing, Nothing, NamedIndividual)
 *   - Object/data property markers (FunctionalProperty,
 *     InverseFunctionalProperty, TransitiveProperty,
 *     SymmetricProperty, ObjectProperty, DatatypeProperty)
 *   - Equality + inequality (sameAs, differentFrom, equivalentClass,
 *     equivalentProperty, inverseOf, propertyDisjointWith)
 *   - rdf:type, rdfs:subClassOf, rdfs:subPropertyOf, rdfs:domain,
 *     rdfs:range, rdfs:Class, rdfs:Resource, rdfs:Datatype,
 *     rdfs:Literal — convenience for the broader OWL/RDF family
 *
 * Each constant is a `wf_iri` with `assert_norm (is_iri "...")` so
 * the type-system witness lands at module load.
 *)

open RDF.Graph.Executable

(* ----- Class-expression bookkeeping ----------------------------------- *)

let owl_intersectionOf : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#intersectionOf");
  "http://www.w3.org/2002/07/owl#intersectionOf"

let owl_unionOf : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#unionOf");
  "http://www.w3.org/2002/07/owl#unionOf"

let owl_complementOf : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#complementOf");
  "http://www.w3.org/2002/07/owl#complementOf"

let owl_disjointWith : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#disjointWith");
  "http://www.w3.org/2002/07/owl#disjointWith"

(* ----- Restrictions --------------------------------------------------- *)

let owl_Restriction : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#Restriction");
  "http://www.w3.org/2002/07/owl#Restriction"

let owl_onProperty : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#onProperty");
  "http://www.w3.org/2002/07/owl#onProperty"

let owl_someValuesFrom : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#someValuesFrom");
  "http://www.w3.org/2002/07/owl#someValuesFrom"

let owl_allValuesFrom : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#allValuesFrom");
  "http://www.w3.org/2002/07/owl#allValuesFrom"

let owl_hasValue : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#hasValue");
  "http://www.w3.org/2002/07/owl#hasValue"

(* ----- Cardinality family --------------------------------------------- *)

let owl_cardinality : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#cardinality");
  "http://www.w3.org/2002/07/owl#cardinality"

let owl_minCardinality : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#minCardinality");
  "http://www.w3.org/2002/07/owl#minCardinality"

let owl_maxCardinality : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#maxCardinality");
  "http://www.w3.org/2002/07/owl#maxCardinality"

let owl_qualifiedCardinality : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#qualifiedCardinality");
  "http://www.w3.org/2002/07/owl#qualifiedCardinality"

let owl_minQualifiedCardinality : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#minQualifiedCardinality");
  "http://www.w3.org/2002/07/owl#minQualifiedCardinality"

let owl_maxQualifiedCardinality : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#maxQualifiedCardinality");
  "http://www.w3.org/2002/07/owl#maxQualifiedCardinality"

let owl_onClass : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#onClass");
  "http://www.w3.org/2002/07/owl#onClass"

(* ----- RDF list-chain markers (used by OWL collections) --------------- *)

let rdf_first : wf_iri =
  assert_norm (is_iri "http://www.w3.org/1999/02/22-rdf-syntax-ns#first");
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#first"

let rdf_rest : wf_iri =
  assert_norm (is_iri "http://www.w3.org/1999/02/22-rdf-syntax-ns#rest");
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#rest"

let rdf_nil : wf_iri =
  assert_norm (is_iri "http://www.w3.org/1999/02/22-rdf-syntax-ns#nil");
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#nil"
