module RDF.Vocabulary

// This is the tree's FIRST .fsti (see docs/designissues/2026-07-05-
// foundational-core-refactor.md §2.6/§2.9 and the build-pipeline note
// in the same doc's step table). Every value below is a *transparent*
// `let` (not an abstract `val`) on purpose: this module's whole job is
// to be the single, grep-verifiable source of RDF/RDFS/OWL vocabulary
// IRI strings, and downstream consumers (RDF.Graph.Executable.fst's
// re-export shim, OWL.Vocabulary.fst's re-export shim,
// RDF.Vocabulary.Axioms.fst) need `assert_norm` to unfold the literal
// string to re-derive a `wf_iri`-refined copy locally — an opaque
// `val name : string` would make that unfoldable. Transparency here is
// the point, not a compromise: this module IS the specification data.
//
// Deliberately excluded from this module (still assigned to other
// designs' modules, so a reader doesn't wonder where they went):
//   - `xsd:string`/`xsd:integer`/`xsd:decimal`/`xsd:double`/`xsd:boolean`
//     — these are part of the term algebra (`literal`/`wf_literal`
//     construction), not "vocabulary" in the RDFS/OWL sense; they now
//     live in `RDF.Term.fsti` (design doc §2.1, step 5, landed
//     2026-07-05 — previously inline in RDF.Graph.Executable.fst
//     lines 36-50, then a "future module" note here before step 5
//     shipped), not here.
//   - The XSD datatype-hierarchy constants (`xsd_long`,
//     `xsd_nonNegativeInteger`, `xsd_hierarchy_edges`, RDF.Graph.
//     Executable.fst lines ~4007-4098) and the `_iri`-suffixed OWL
//     restriction-vocabulary duplicate block (lines 2216-2283) — both
//     are interleaved with OWL-RL closure code that hasn't moved out
//     of RDF.Graph.Executable.fst yet (design doc step 6). Moving
//     their vocabulary constants here now would require either
//     duplicating the closure code's own copies or creating a
//     dependency cycle (RDF.Vocabulary would need `wf_iri`/`is_iri`
//     from RDF.Graph.Executable, whose closure code would then need to
//     `open RDF.Vocabulary` back). Deferred to when step 6 relocates
//     the closure code that consumes them.
//   - `rdf:first`/`rdf:rest`/`rdf:nil_iri` as separately named at
//     RDF.Graph.Executable.fst lines 3340-3350 (property-chain/list
//     decoding inside the OWL-RL closure section) — same reason.
//   - OWL.QueryRewrite.fst's own `_iri`-suffixed forwarders — out of
//     this slice's territory (a different agent's migration step).
//
// What DID move here (slice 1 of the RDF.Vocabulary consolidation):
//   - RDF.Graph.Executable.fst's section 16 "RDF/RDFS Vocabulary
//     Constants" block (lines 806-876).
//   - OWL.Vocabulary.fst's entire content (class-expression/
//     restriction/cardinality constants + its own rdf:first/rdf:rest/
//     rdf:nil copy).
//   - New: the additional RDF/RDFS terms needed by the
//     `RDF.Vocabulary.Axioms` companion (rdf:subject/predicate/object/
//     value/Statement/Alt/Bag/Seq/List, rdfs:seeAlso/isDefinedBy/
//     comment/label/Container) that previously had no named constant
//     anywhere in the tree (only inline string literals, e.g.
//     RDF.Graph.Executable.fst lines 2708-2710).

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
