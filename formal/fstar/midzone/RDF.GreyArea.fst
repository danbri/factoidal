module RDF.GreyArea

// Bucket: GREY AREA.
//
// This module is for choices that are defensible but not simply "the RDF
// Concepts definition copied into F*". They should be small, explicit, and
// easy for W3C/RDF readers to debate.

open RDF.CoreSpec

// The RDF Concepts document gives a syntactic notion of datasets and dataset
// comparison. A full meaning for datasets is not settled in the same way RDF
// graph semantics is. Keep policy choices here until they are justified.
type dataset_semantics_policy =
  | DatasetSyntaxOnly
  | DatasetDefaultGraphMeaning
  | DatasetNamedGraphAssertion

// IRI validation is another boundary: the core model can treat IRIs as atomic,
// while parsers and deployments may choose strict RFC3987/RFC3986 validation,
// lenient acceptance, or vocabulary-specific constraints.
type iri_validation_policy =
  | AtomicIRI
  | RequireAbsoluteIRI
  | ParserValidatedIRI

// Datatype value equality depends on selected datatype maps and lexical-to-
// value functions. RDF Semantics has the framework; implementation coverage
// for xsd datatypes is a project choice.
type datatype_policy =
  | LexicalOnly
  | RDFRecognizedDatatypeMap
  | ProjectDatatypeSubset

// JSON-LD-specific context policy has its own module: JSONLD.Policy.
