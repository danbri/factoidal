module OWL.Vocabulary

open RDF.CoreSpec

// OWL namespace vocabulary used by OWL profile specifications.
//
// Bucket: CORE SPEC.

let owl_ns : string = "http://www.w3.org/2002/07/owl#"

let owl_Class : iri = "http://www.w3.org/2002/07/owl#Class"
let owl_ObjectProperty : iri = "http://www.w3.org/2002/07/owl#ObjectProperty"
let owl_DatatypeProperty : iri = "http://www.w3.org/2002/07/owl#DatatypeProperty"
let owl_Thing : iri = "http://www.w3.org/2002/07/owl#Thing"
let owl_Nothing : iri = "http://www.w3.org/2002/07/owl#Nothing"
let owl_NamedIndividual : iri = "http://www.w3.org/2002/07/owl#NamedIndividual"
let owl_sameAs : iri = "http://www.w3.org/2002/07/owl#sameAs"
let owl_SymmetricProperty : iri = "http://www.w3.org/2002/07/owl#SymmetricProperty"
let owl_TransitiveProperty : iri = "http://www.w3.org/2002/07/owl#TransitiveProperty"
let owl_InverseFunctionalProperty : iri =
  "http://www.w3.org/2002/07/owl#InverseFunctionalProperty"
let owl_inverseOf : iri = "http://www.w3.org/2002/07/owl#inverseOf"
let owl_equivalentClass : iri = "http://www.w3.org/2002/07/owl#equivalentClass"
let owl_equivalentProperty : iri =
  "http://www.w3.org/2002/07/owl#equivalentProperty"
