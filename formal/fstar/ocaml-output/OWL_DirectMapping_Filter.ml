open Prims
let owl_AnnotationProperty : RDF_Graph_Executable.wf_iri=
  "http://www.w3.org/2002/07/owl#AnnotationProperty"
let owl_OntologyProperty : RDF_Graph_Executable.wf_iri=
  "http://www.w3.org/2002/07/owl#OntologyProperty"
let is_declared_annotation_predicate (g : RDF_Graph_Executable.rdf_graph)
  (p : RDF_Graph_Executable.wf_iri) : Prims.bool=
  FStar_List_Tot_Base.existsb
    (fun t ->
       ((RDF_Graph_Executable.subject_eq t.RDF_Graph_Executable.s
           (RDF_Graph_Executable.S_IRI p))
          && (t.RDF_Graph_Executable.p = RDF_Graph_Executable.rdf_type))
         &&
         ((RDF_Graph_Executable.rdf_term_eq t.RDF_Graph_Executable.o
             (RDF_Graph_Executable.T_IRI owl_AnnotationProperty))
            ||
            (RDF_Graph_Executable.rdf_term_eq t.RDF_Graph_Executable.o
               (RDF_Graph_Executable.T_IRI owl_OntologyProperty)))) g
let exclude_annotation_triples (g : RDF_Graph_Executable.rdf_graph) :
  RDF_Graph_Executable.rdf_graph=
  FStar_List_Tot_Base.filter
    (fun t ->
       Prims.op_Negation
         (is_declared_annotation_predicate g t.RDF_Graph_Executable.p)) g
