module RDFS.Vocabulary

open RDF.CoreSpec

// RDFS namespace vocabulary from RDF Schema.
//
// Bucket: CORE SPEC.

let rdfs_ns : string = "http://www.w3.org/2000/01/rdf-schema#"

let rdfs_subClassOf : iri = "http://www.w3.org/2000/01/rdf-schema#subClassOf"
let rdfs_subPropertyOf : iri = "http://www.w3.org/2000/01/rdf-schema#subPropertyOf"
let rdfs_domain : iri = "http://www.w3.org/2000/01/rdf-schema#domain"
let rdfs_range : iri = "http://www.w3.org/2000/01/rdf-schema#range"
let rdfs_Class : iri = "http://www.w3.org/2000/01/rdf-schema#Class"
let rdfs_Resource : iri = "http://www.w3.org/2000/01/rdf-schema#Resource"
let rdfs_Literal : iri = "http://www.w3.org/2000/01/rdf-schema#Literal"
let rdfs_ContainerMembershipProperty : iri =
  "http://www.w3.org/2000/01/rdf-schema#ContainerMembershipProperty"
let rdfs_member : iri = "http://www.w3.org/2000/01/rdf-schema#member"
let rdfs_Datatype : iri = "http://www.w3.org/2000/01/rdf-schema#Datatype"
