module RDF.Vocabulary

// This is the tree's FIRST .fsti (docs/designissues/2026-07-05-
// foundational-core-refactor.md §2.6/§2.9). Every value below is a
// *transparent* `let` (not an abstract `val`): this module's whole job
// is to be the single, grep-verifiable source of RDF/RDFS/OWL
// vocabulary IRI strings — transparency is the point, not a
// compromise. No concept/mechanism split needed: every entry has the
// same shape (`let name : string = "..."`), so the whole file reads
// as one flat, skimmable table. Full exclusion-list history in
// RDF.Vocabulary.fst's banner.

(** ------------------------------------------------------------------ *)
(** RDF core (RDF 1.1 Concepts §3 / RDF 1.1 namespace document)        *)
(** ------------------------------------------------------------------ *)

/// rdf:type — the type-membership predicate.
let rdf_type : string = "http://www.w3.org/1999/02/22-rdf-syntax-ns#type"

/// rdf:Property — the class of RDF properties.
let rdf_Property : string = "http://www.w3.org/1999/02/22-rdf-syntax-ns#Property"

/// rdf:List — the class of RDF collections (linked lists).
let rdf_List : string = "http://www.w3.org/1999/02/22-rdf-syntax-ns#List"

/// rdf:Statement — the class of reified triples.
let rdf_Statement : string = "http://www.w3.org/1999/02/22-rdf-syntax-ns#Statement"

/// rdf:first — head of an rdf:List cons cell.
let rdf_first : string = "http://www.w3.org/1999/02/22-rdf-syntax-ns#first"

/// rdf:rest — tail of an rdf:List cons cell.
let rdf_rest : string = "http://www.w3.org/1999/02/22-rdf-syntax-ns#rest"

/// rdf:nil — the empty rdf:List.
let rdf_nil : string = "http://www.w3.org/1999/02/22-rdf-syntax-ns#nil"

/// rdf:subject — reification: the subject of the reified statement.
let rdf_subject : string = "http://www.w3.org/1999/02/22-rdf-syntax-ns#subject"

/// rdf:predicate — reification: the predicate of the reified statement.
let rdf_predicate : string = "http://www.w3.org/1999/02/22-rdf-syntax-ns#predicate"

/// rdf:object — reification: the object of the reified statement.
let rdf_object : string = "http://www.w3.org/1999/02/22-rdf-syntax-ns#object"

/// rdf:value — the generic "has value" auxiliary property.
let rdf_value : string = "http://www.w3.org/1999/02/22-rdf-syntax-ns#value"

/// rdf:Alt — the class of "alternative" containers.
let rdf_Alt : string = "http://www.w3.org/1999/02/22-rdf-syntax-ns#Alt"

/// rdf:Bag — the class of unordered containers.
let rdf_Bag : string = "http://www.w3.org/1999/02/22-rdf-syntax-ns#Bag"

/// rdf:Seq — the class of ordered containers.
let rdf_Seq : string = "http://www.w3.org/1999/02/22-rdf-syntax-ns#Seq"

/// rdf:_1 .. rdf:_5 — the first five container-membership properties.
/// The full family rdf:_n is infinite (RDF Semantics' own note on
/// infinitude); only these five are pre-declared here for the closure
/// rules' `container_membership_properties` seed list (RDF.Graph.
/// Executable.fst's shim reconstructs the wf_iri-typed list locally).
let rdf_1 : string = "http://www.w3.org/1999/02/22-rdf-syntax-ns#_1"
let rdf_2 : string = "http://www.w3.org/1999/02/22-rdf-syntax-ns#_2"
let rdf_3 : string = "http://www.w3.org/1999/02/22-rdf-syntax-ns#_3"
let rdf_4 : string = "http://www.w3.org/1999/02/22-rdf-syntax-ns#_4"
let rdf_5 : string = "http://www.w3.org/1999/02/22-rdf-syntax-ns#_5"

(** ------------------------------------------------------------------ *)
(** RDFS (RDF Schema 1.1 namespace document / RDF Semantics §9 tables) *)
(** ------------------------------------------------------------------ *)

/// rdfs:subClassOf.
let rdfs_subClassOf : string = "http://www.w3.org/2000/01/rdf-schema#subClassOf"

/// rdfs:subPropertyOf.
let rdfs_subPropertyOf : string = "http://www.w3.org/2000/01/rdf-schema#subPropertyOf"

/// rdfs:domain.
let rdfs_domain : string = "http://www.w3.org/2000/01/rdf-schema#domain"

/// rdfs:range.
let rdfs_range : string = "http://www.w3.org/2000/01/rdf-schema#range"

/// rdfs:Class — the class of classes.
let rdfs_Class : string = "http://www.w3.org/2000/01/rdf-schema#Class"

/// rdfs:Resource — the class of everything.
let rdfs_Resource : string = "http://www.w3.org/2000/01/rdf-schema#Resource"

/// rdfs:Literal — the class of literal values.
let rdfs_Literal : string = "http://www.w3.org/2000/01/rdf-schema#Literal"

/// rdfs:Datatype — the class of datatypes.
let rdfs_Datatype : string = "http://www.w3.org/2000/01/rdf-schema#Datatype"

/// rdfs:ContainerMembershipProperty — the class of rdf:_n properties.
let rdfs_ContainerMembershipProperty : string =
  "http://www.w3.org/2000/01/rdf-schema#ContainerMembershipProperty"

/// rdfs:member — the super-property of every rdf:_n.
let rdfs_member : string = "http://www.w3.org/2000/01/rdf-schema#member"

/// rdfs:Container — the class of RDF containers (super-class of
/// rdf:Alt/rdf:Bag/rdf:Seq).
let rdfs_Container : string = "http://www.w3.org/2000/01/rdf-schema#Container"

/// rdfs:seeAlso.
let rdfs_seeAlso : string = "http://www.w3.org/2000/01/rdf-schema#seeAlso"

/// rdfs:isDefinedBy.
let rdfs_isDefinedBy : string = "http://www.w3.org/2000/01/rdf-schema#isDefinedBy"

/// rdfs:comment.
let rdfs_comment : string = "http://www.w3.org/2000/01/rdf-schema#comment"

/// rdfs:label.
let rdfs_label : string = "http://www.w3.org/2000/01/rdf-schema#label"

(** ------------------------------------------------------------------ *)
(** OWL 2 (OWL 2 Web Ontology Language / RDF-Based Semantics)          *)
(** ------------------------------------------------------------------ *)

/// owl:intersectionOf — class-expression conjunction.
let owl_intersectionOf : string = "http://www.w3.org/2002/07/owl#intersectionOf"

/// owl:unionOf — class-expression disjunction.
let owl_unionOf : string = "http://www.w3.org/2002/07/owl#unionOf"

/// owl:complementOf — class-expression negation.
let owl_complementOf : string = "http://www.w3.org/2002/07/owl#complementOf"

/// owl:disjointWith.
let owl_disjointWith : string = "http://www.w3.org/2002/07/owl#disjointWith"

/// owl:Restriction — the class of property restrictions.
let owl_Restriction : string = "http://www.w3.org/2002/07/owl#Restriction"

/// owl:onProperty — the restricted property of an owl:Restriction.
let owl_onProperty : string = "http://www.w3.org/2002/07/owl#onProperty"

/// owl:someValuesFrom.
let owl_someValuesFrom : string = "http://www.w3.org/2002/07/owl#someValuesFrom"

/// owl:allValuesFrom.
let owl_allValuesFrom : string = "http://www.w3.org/2002/07/owl#allValuesFrom"

/// owl:hasValue.
let owl_hasValue : string = "http://www.w3.org/2002/07/owl#hasValue"

/// owl:cardinality.
let owl_cardinality : string = "http://www.w3.org/2002/07/owl#cardinality"

/// owl:minCardinality.
let owl_minCardinality : string = "http://www.w3.org/2002/07/owl#minCardinality"

/// owl:maxCardinality.
let owl_maxCardinality : string = "http://www.w3.org/2002/07/owl#maxCardinality"

/// owl:qualifiedCardinality.
let owl_qualifiedCardinality : string = "http://www.w3.org/2002/07/owl#qualifiedCardinality"

/// owl:minQualifiedCardinality.
let owl_minQualifiedCardinality : string =
  "http://www.w3.org/2002/07/owl#minQualifiedCardinality"

/// owl:maxQualifiedCardinality.
let owl_maxQualifiedCardinality : string =
  "http://www.w3.org/2002/07/owl#maxQualifiedCardinality"

/// owl:onClass — the qualifying class of a qualified cardinality
/// restriction.
let owl_onClass : string = "http://www.w3.org/2002/07/owl#onClass"
