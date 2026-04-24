module RDF.Vocabulary

open RDF.CoreSpec

// RDF namespace vocabulary from the RDF/RDFS specifications.
//
// Bucket: CORE SPEC.

let rdf_ns : string = "http://www.w3.org/1999/02/22-rdf-syntax-ns#"

let rdf_type : iri = "http://www.w3.org/1999/02/22-rdf-syntax-ns#type"
let rdf_Property : iri = "http://www.w3.org/1999/02/22-rdf-syntax-ns#Property"
let rdf_langString : iri = "http://www.w3.org/1999/02/22-rdf-syntax-ns#langString"

let rdf_1 : iri = "http://www.w3.org/1999/02/22-rdf-syntax-ns#_1"
let rdf_2 : iri = "http://www.w3.org/1999/02/22-rdf-syntax-ns#_2"
let rdf_3 : iri = "http://www.w3.org/1999/02/22-rdf-syntax-ns#_3"
let rdf_4 : iri = "http://www.w3.org/1999/02/22-rdf-syntax-ns#_4"
let rdf_5 : iri = "http://www.w3.org/1999/02/22-rdf-syntax-ns#_5"

let container_membership_properties : list iri =
  [rdf_1; rdf_2; rdf_3; rdf_4; rdf_5]
