open Prims
let owl_AnnotationProperty : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#AnnotationProperty"
let owl_OntologyProperty : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#OntologyProperty"
let is_declared_annotation_predicate (g : RDF_Graph.rdf_graph)
  (p : RDF_Term.wf_iri) : Prims.bool=
  FStar_List_Tot_Base.existsb
    (fun t ->
       ((RDF_Term.subject_eq t.RDF_Triple.s (RDF_Term.S_IRI p)) &&
          (t.RDF_Triple.p = RDFS_Closure.rdf_type))
         &&
         ((RDF_Term.rdf_term_eq t.RDF_Triple.o
             (RDF_Term.T_IRI owl_AnnotationProperty))
            ||
            (RDF_Term.rdf_term_eq t.RDF_Triple.o
               (RDF_Term.T_IRI owl_OntologyProperty)))) g
let exclude_annotation_triples (g : RDF_Graph.rdf_graph) :
  RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.filter
    (fun t ->
       Prims.op_Negation (is_declared_annotation_predicate g t.RDF_Triple.p))
    g
