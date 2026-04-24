module JSONLD.Policy

open RDF.CoreSpec

// JSON-LD processing policy.
//
// Bucket: MIDZONE.
//
// JSON-LD is a W3C syntax, but remote contexts make graph/dataset denotation
// depend on a processing environment. Keep those assumptions explicit here.

type context_iri = iri
type context_document = data_item

type jsonld_context_policy =
  | NoRemoteContexts
  | FixedContextMap
  | NetworkContextLoading

noeq type jsonld_processing_environment = {
  context_policy : jsonld_context_policy;
  base_iri       : option iri;
  fixed_context  : context_iri -> option context_document;
}

let jsonld_dataset_denotation
  (_:jsonld_processing_environment)
  (_:dataset_syntax)
  (_:dataset)
  : proposition = True
