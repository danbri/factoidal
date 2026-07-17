open Prims
let resolve_iri (base : RDF_Term.wf_iri) (relative : Prims.string) :
  RDF_Term.wf_iri= RDF_IRI.resolve_iri base relative
let resolve_query_iri (base : RDF_Term.wf_iri FStar_Pervasives_Native.option)
  (rel : Prims.string) : RDF_Term.wf_iri FStar_Pervasives_Native.option=
  RDF_IRI.resolve_query_iri base rel
