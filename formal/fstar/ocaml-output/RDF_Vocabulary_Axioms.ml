open Prims
let i_rdf_type : RDF_Graph_Executable.wf_iri= RDF_Vocabulary.rdf_type
let i_rdf_Property : RDF_Graph_Executable.wf_iri= RDF_Vocabulary.rdf_Property
let i_rdf_List : RDF_Graph_Executable.wf_iri= RDF_Vocabulary.rdf_List
let i_rdf_Statement : RDF_Graph_Executable.wf_iri=
  RDF_Vocabulary.rdf_Statement
let i_rdf_first : RDF_Graph_Executable.wf_iri= RDF_Vocabulary.rdf_first
let i_rdf_rest : RDF_Graph_Executable.wf_iri= RDF_Vocabulary.rdf_rest
let i_rdf_nil : RDF_Graph_Executable.wf_iri= RDF_Vocabulary.rdf_nil
let i_rdf_subject : RDF_Graph_Executable.wf_iri= RDF_Vocabulary.rdf_subject
let i_rdf_predicate : RDF_Graph_Executable.wf_iri=
  RDF_Vocabulary.rdf_predicate
let i_rdf_object : RDF_Graph_Executable.wf_iri= RDF_Vocabulary.rdf_object
let i_rdf_value : RDF_Graph_Executable.wf_iri= RDF_Vocabulary.rdf_value
let i_rdf_Alt : RDF_Graph_Executable.wf_iri= RDF_Vocabulary.rdf_Alt
let i_rdf_Bag : RDF_Graph_Executable.wf_iri= RDF_Vocabulary.rdf_Bag
let i_rdf_Seq : RDF_Graph_Executable.wf_iri= RDF_Vocabulary.rdf_Seq
let i_rdfs_subClassOf : RDF_Graph_Executable.wf_iri=
  RDF_Vocabulary.rdfs_subClassOf
let i_rdfs_subPropertyOf : RDF_Graph_Executable.wf_iri=
  RDF_Vocabulary.rdfs_subPropertyOf
let i_rdfs_domain : RDF_Graph_Executable.wf_iri= RDF_Vocabulary.rdfs_domain
let i_rdfs_range : RDF_Graph_Executable.wf_iri= RDF_Vocabulary.rdfs_range
let i_rdfs_Class : RDF_Graph_Executable.wf_iri= RDF_Vocabulary.rdfs_Class
let i_rdfs_Resource : RDF_Graph_Executable.wf_iri=
  RDF_Vocabulary.rdfs_Resource
let i_rdfs_Literal : RDF_Graph_Executable.wf_iri= RDF_Vocabulary.rdfs_Literal
let i_rdfs_Datatype : RDF_Graph_Executable.wf_iri=
  RDF_Vocabulary.rdfs_Datatype
let i_rdfs_ContainerMembershipProperty : RDF_Graph_Executable.wf_iri=
  RDF_Vocabulary.rdfs_ContainerMembershipProperty
let i_rdfs_member : RDF_Graph_Executable.wf_iri= RDF_Vocabulary.rdfs_member
let i_rdfs_Container : RDF_Graph_Executable.wf_iri=
  RDF_Vocabulary.rdfs_Container
let i_rdfs_seeAlso : RDF_Graph_Executable.wf_iri= RDF_Vocabulary.rdfs_seeAlso
let i_rdfs_isDefinedBy : RDF_Graph_Executable.wf_iri=
  RDF_Vocabulary.rdfs_isDefinedBy
let i_rdfs_comment : RDF_Graph_Executable.wf_iri= RDF_Vocabulary.rdfs_comment
let i_rdfs_label : RDF_Graph_Executable.wf_iri= RDF_Vocabulary.rdfs_label
let rdf_axiom_type_type_property : RDF_Graph_Executable.triple=
  {
    RDF_Graph_Executable.s = (RDF_Graph_Executable.S_IRI i_rdf_type);
    RDF_Graph_Executable.p = i_rdf_type;
    RDF_Graph_Executable.o = (RDF_Graph_Executable.T_IRI i_rdf_Property)
  }
let rdf_axiom_subject_type_property : RDF_Graph_Executable.triple=
  {
    RDF_Graph_Executable.s = (RDF_Graph_Executable.S_IRI i_rdf_subject);
    RDF_Graph_Executable.p = i_rdf_type;
    RDF_Graph_Executable.o = (RDF_Graph_Executable.T_IRI i_rdf_Property)
  }
let rdf_axiom_predicate_type_property : RDF_Graph_Executable.triple=
  {
    RDF_Graph_Executable.s = (RDF_Graph_Executable.S_IRI i_rdf_predicate);
    RDF_Graph_Executable.p = i_rdf_type;
    RDF_Graph_Executable.o = (RDF_Graph_Executable.T_IRI i_rdf_Property)
  }
let rdf_axiom_object_type_property : RDF_Graph_Executable.triple=
  {
    RDF_Graph_Executable.s = (RDF_Graph_Executable.S_IRI i_rdf_object);
    RDF_Graph_Executable.p = i_rdf_type;
    RDF_Graph_Executable.o = (RDF_Graph_Executable.T_IRI i_rdf_Property)
  }
let rdf_axiom_first_type_property : RDF_Graph_Executable.triple=
  {
    RDF_Graph_Executable.s = (RDF_Graph_Executable.S_IRI i_rdf_first);
    RDF_Graph_Executable.p = i_rdf_type;
    RDF_Graph_Executable.o = (RDF_Graph_Executable.T_IRI i_rdf_Property)
  }
let rdf_axiom_rest_type_property : RDF_Graph_Executable.triple=
  {
    RDF_Graph_Executable.s = (RDF_Graph_Executable.S_IRI i_rdf_rest);
    RDF_Graph_Executable.p = i_rdf_type;
    RDF_Graph_Executable.o = (RDF_Graph_Executable.T_IRI i_rdf_Property)
  }
let rdf_axiom_value_type_property : RDF_Graph_Executable.triple=
  {
    RDF_Graph_Executable.s = (RDF_Graph_Executable.S_IRI i_rdf_value);
    RDF_Graph_Executable.p = i_rdf_type;
    RDF_Graph_Executable.o = (RDF_Graph_Executable.T_IRI i_rdf_Property)
  }
let rdf_axiom_nil_type_list : RDF_Graph_Executable.triple=
  {
    RDF_Graph_Executable.s = (RDF_Graph_Executable.S_IRI i_rdf_nil);
    RDF_Graph_Executable.p = i_rdf_type;
    RDF_Graph_Executable.o = (RDF_Graph_Executable.T_IRI i_rdf_List)
  }
let rdf_axiomatic_triples : RDF_Graph_Executable.triple Prims.list=
  [rdf_axiom_type_type_property;
  rdf_axiom_subject_type_property;
  rdf_axiom_predicate_type_property;
  rdf_axiom_object_type_property;
  rdf_axiom_first_type_property;
  rdf_axiom_rest_type_property;
  rdf_axiom_value_type_property;
  rdf_axiom_nil_type_list]
let rdfs_axiom_dom_type : RDF_Graph_Executable.triple=
  {
    RDF_Graph_Executable.s = (RDF_Graph_Executable.S_IRI i_rdf_type);
    RDF_Graph_Executable.p = i_rdfs_domain;
    RDF_Graph_Executable.o = (RDF_Graph_Executable.T_IRI i_rdfs_Resource)
  }
let rdfs_axiom_dom_domain : RDF_Graph_Executable.triple=
  {
    RDF_Graph_Executable.s = (RDF_Graph_Executable.S_IRI i_rdfs_domain);
    RDF_Graph_Executable.p = i_rdfs_domain;
    RDF_Graph_Executable.o = (RDF_Graph_Executable.T_IRI i_rdf_Property)
  }
let rdfs_axiom_dom_range : RDF_Graph_Executable.triple=
  {
    RDF_Graph_Executable.s = (RDF_Graph_Executable.S_IRI i_rdfs_range);
    RDF_Graph_Executable.p = i_rdfs_domain;
    RDF_Graph_Executable.o = (RDF_Graph_Executable.T_IRI i_rdf_Property)
  }
let rdfs_axiom_dom_subPropertyOf : RDF_Graph_Executable.triple=
  {
    RDF_Graph_Executable.s =
      (RDF_Graph_Executable.S_IRI i_rdfs_subPropertyOf);
    RDF_Graph_Executable.p = i_rdfs_domain;
    RDF_Graph_Executable.o = (RDF_Graph_Executable.T_IRI i_rdf_Property)
  }
let rdfs_axiom_dom_subClassOf : RDF_Graph_Executable.triple=
  {
    RDF_Graph_Executable.s = (RDF_Graph_Executable.S_IRI i_rdfs_subClassOf);
    RDF_Graph_Executable.p = i_rdfs_domain;
    RDF_Graph_Executable.o = (RDF_Graph_Executable.T_IRI i_rdfs_Class)
  }
let rdfs_axiom_dom_subject : RDF_Graph_Executable.triple=
  {
    RDF_Graph_Executable.s = (RDF_Graph_Executable.S_IRI i_rdf_subject);
    RDF_Graph_Executable.p = i_rdfs_domain;
    RDF_Graph_Executable.o = (RDF_Graph_Executable.T_IRI i_rdf_Statement)
  }
let rdfs_axiom_dom_predicate : RDF_Graph_Executable.triple=
  {
    RDF_Graph_Executable.s = (RDF_Graph_Executable.S_IRI i_rdf_predicate);
    RDF_Graph_Executable.p = i_rdfs_domain;
    RDF_Graph_Executable.o = (RDF_Graph_Executable.T_IRI i_rdf_Statement)
  }
let rdfs_axiom_dom_object : RDF_Graph_Executable.triple=
  {
    RDF_Graph_Executable.s = (RDF_Graph_Executable.S_IRI i_rdf_object);
    RDF_Graph_Executable.p = i_rdfs_domain;
    RDF_Graph_Executable.o = (RDF_Graph_Executable.T_IRI i_rdf_Statement)
  }
let rdfs_axiom_dom_member : RDF_Graph_Executable.triple=
  {
    RDF_Graph_Executable.s = (RDF_Graph_Executable.S_IRI i_rdfs_member);
    RDF_Graph_Executable.p = i_rdfs_domain;
    RDF_Graph_Executable.o = (RDF_Graph_Executable.T_IRI i_rdfs_Resource)
  }
let rdfs_axiom_dom_first : RDF_Graph_Executable.triple=
  {
    RDF_Graph_Executable.s = (RDF_Graph_Executable.S_IRI i_rdf_first);
    RDF_Graph_Executable.p = i_rdfs_domain;
    RDF_Graph_Executable.o = (RDF_Graph_Executable.T_IRI i_rdf_List)
  }
let rdfs_axiom_dom_rest : RDF_Graph_Executable.triple=
  {
    RDF_Graph_Executable.s = (RDF_Graph_Executable.S_IRI i_rdf_rest);
    RDF_Graph_Executable.p = i_rdfs_domain;
    RDF_Graph_Executable.o = (RDF_Graph_Executable.T_IRI i_rdf_List)
  }
let rdfs_axiom_dom_seeAlso : RDF_Graph_Executable.triple=
  {
    RDF_Graph_Executable.s = (RDF_Graph_Executable.S_IRI i_rdfs_seeAlso);
    RDF_Graph_Executable.p = i_rdfs_domain;
    RDF_Graph_Executable.o = (RDF_Graph_Executable.T_IRI i_rdfs_Resource)
  }
let rdfs_axiom_dom_isDefinedBy : RDF_Graph_Executable.triple=
  {
    RDF_Graph_Executable.s = (RDF_Graph_Executable.S_IRI i_rdfs_isDefinedBy);
    RDF_Graph_Executable.p = i_rdfs_domain;
    RDF_Graph_Executable.o = (RDF_Graph_Executable.T_IRI i_rdfs_Resource)
  }
let rdfs_axiom_dom_comment : RDF_Graph_Executable.triple=
  {
    RDF_Graph_Executable.s = (RDF_Graph_Executable.S_IRI i_rdfs_comment);
    RDF_Graph_Executable.p = i_rdfs_domain;
    RDF_Graph_Executable.o = (RDF_Graph_Executable.T_IRI i_rdfs_Resource)
  }
let rdfs_axiom_dom_label : RDF_Graph_Executable.triple=
  {
    RDF_Graph_Executable.s = (RDF_Graph_Executable.S_IRI i_rdfs_label);
    RDF_Graph_Executable.p = i_rdfs_domain;
    RDF_Graph_Executable.o = (RDF_Graph_Executable.T_IRI i_rdfs_Resource)
  }
let rdfs_axiom_dom_value : RDF_Graph_Executable.triple=
  {
    RDF_Graph_Executable.s = (RDF_Graph_Executable.S_IRI i_rdf_value);
    RDF_Graph_Executable.p = i_rdfs_domain;
    RDF_Graph_Executable.o = (RDF_Graph_Executable.T_IRI i_rdfs_Resource)
  }
let rdfs_axiom_rng_type : RDF_Graph_Executable.triple=
  {
    RDF_Graph_Executable.s = (RDF_Graph_Executable.S_IRI i_rdf_type);
    RDF_Graph_Executable.p = i_rdfs_range;
    RDF_Graph_Executable.o = (RDF_Graph_Executable.T_IRI i_rdfs_Class)
  }
let rdfs_axiom_rng_domain : RDF_Graph_Executable.triple=
  {
    RDF_Graph_Executable.s = (RDF_Graph_Executable.S_IRI i_rdfs_domain);
    RDF_Graph_Executable.p = i_rdfs_range;
    RDF_Graph_Executable.o = (RDF_Graph_Executable.T_IRI i_rdfs_Class)
  }
let rdfs_axiom_rng_range : RDF_Graph_Executable.triple=
  {
    RDF_Graph_Executable.s = (RDF_Graph_Executable.S_IRI i_rdfs_range);
    RDF_Graph_Executable.p = i_rdfs_range;
    RDF_Graph_Executable.o = (RDF_Graph_Executable.T_IRI i_rdfs_Class)
  }
let rdfs_axiom_rng_subPropertyOf : RDF_Graph_Executable.triple=
  {
    RDF_Graph_Executable.s =
      (RDF_Graph_Executable.S_IRI i_rdfs_subPropertyOf);
    RDF_Graph_Executable.p = i_rdfs_range;
    RDF_Graph_Executable.o = (RDF_Graph_Executable.T_IRI i_rdf_Property)
  }
let rdfs_axiom_rng_subClassOf : RDF_Graph_Executable.triple=
  {
    RDF_Graph_Executable.s = (RDF_Graph_Executable.S_IRI i_rdfs_subClassOf);
    RDF_Graph_Executable.p = i_rdfs_range;
    RDF_Graph_Executable.o = (RDF_Graph_Executable.T_IRI i_rdfs_Class)
  }
let rdfs_axiom_rng_subject : RDF_Graph_Executable.triple=
  {
    RDF_Graph_Executable.s = (RDF_Graph_Executable.S_IRI i_rdf_subject);
    RDF_Graph_Executable.p = i_rdfs_range;
    RDF_Graph_Executable.o = (RDF_Graph_Executable.T_IRI i_rdfs_Resource)
  }
let rdfs_axiom_rng_predicate : RDF_Graph_Executable.triple=
  {
    RDF_Graph_Executable.s = (RDF_Graph_Executable.S_IRI i_rdf_predicate);
    RDF_Graph_Executable.p = i_rdfs_range;
    RDF_Graph_Executable.o = (RDF_Graph_Executable.T_IRI i_rdfs_Resource)
  }
let rdfs_axiom_rng_object : RDF_Graph_Executable.triple=
  {
    RDF_Graph_Executable.s = (RDF_Graph_Executable.S_IRI i_rdf_object);
    RDF_Graph_Executable.p = i_rdfs_range;
    RDF_Graph_Executable.o = (RDF_Graph_Executable.T_IRI i_rdfs_Resource)
  }
let rdfs_axiom_rng_member : RDF_Graph_Executable.triple=
  {
    RDF_Graph_Executable.s = (RDF_Graph_Executable.S_IRI i_rdfs_member);
    RDF_Graph_Executable.p = i_rdfs_range;
    RDF_Graph_Executable.o = (RDF_Graph_Executable.T_IRI i_rdfs_Resource)
  }
let rdfs_axiom_rng_first : RDF_Graph_Executable.triple=
  {
    RDF_Graph_Executable.s = (RDF_Graph_Executable.S_IRI i_rdf_first);
    RDF_Graph_Executable.p = i_rdfs_range;
    RDF_Graph_Executable.o = (RDF_Graph_Executable.T_IRI i_rdfs_Resource)
  }
let rdfs_axiom_rng_rest : RDF_Graph_Executable.triple=
  {
    RDF_Graph_Executable.s = (RDF_Graph_Executable.S_IRI i_rdf_rest);
    RDF_Graph_Executable.p = i_rdfs_range;
    RDF_Graph_Executable.o = (RDF_Graph_Executable.T_IRI i_rdf_List)
  }
let rdfs_axiom_rng_seeAlso : RDF_Graph_Executable.triple=
  {
    RDF_Graph_Executable.s = (RDF_Graph_Executable.S_IRI i_rdfs_seeAlso);
    RDF_Graph_Executable.p = i_rdfs_range;
    RDF_Graph_Executable.o = (RDF_Graph_Executable.T_IRI i_rdfs_Resource)
  }
let rdfs_axiom_rng_isDefinedBy : RDF_Graph_Executable.triple=
  {
    RDF_Graph_Executable.s = (RDF_Graph_Executable.S_IRI i_rdfs_isDefinedBy);
    RDF_Graph_Executable.p = i_rdfs_range;
    RDF_Graph_Executable.o = (RDF_Graph_Executable.T_IRI i_rdfs_Resource)
  }
let rdfs_axiom_rng_comment : RDF_Graph_Executable.triple=
  {
    RDF_Graph_Executable.s = (RDF_Graph_Executable.S_IRI i_rdfs_comment);
    RDF_Graph_Executable.p = i_rdfs_range;
    RDF_Graph_Executable.o = (RDF_Graph_Executable.T_IRI i_rdfs_Literal)
  }
let rdfs_axiom_rng_label : RDF_Graph_Executable.triple=
  {
    RDF_Graph_Executable.s = (RDF_Graph_Executable.S_IRI i_rdfs_label);
    RDF_Graph_Executable.p = i_rdfs_range;
    RDF_Graph_Executable.o = (RDF_Graph_Executable.T_IRI i_rdfs_Literal)
  }
let rdfs_axiom_rng_value : RDF_Graph_Executable.triple=
  {
    RDF_Graph_Executable.s = (RDF_Graph_Executable.S_IRI i_rdf_value);
    RDF_Graph_Executable.p = i_rdfs_range;
    RDF_Graph_Executable.o = (RDF_Graph_Executable.T_IRI i_rdfs_Resource)
  }
let rdfs_axiom_alt_subClassOf_container : RDF_Graph_Executable.triple=
  {
    RDF_Graph_Executable.s = (RDF_Graph_Executable.S_IRI i_rdf_Alt);
    RDF_Graph_Executable.p = i_rdfs_subClassOf;
    RDF_Graph_Executable.o = (RDF_Graph_Executable.T_IRI i_rdfs_Container)
  }
let rdfs_axiom_bag_subClassOf_container : RDF_Graph_Executable.triple=
  {
    RDF_Graph_Executable.s = (RDF_Graph_Executable.S_IRI i_rdf_Bag);
    RDF_Graph_Executable.p = i_rdfs_subClassOf;
    RDF_Graph_Executable.o = (RDF_Graph_Executable.T_IRI i_rdfs_Container)
  }
let rdfs_axiom_seq_subClassOf_container : RDF_Graph_Executable.triple=
  {
    RDF_Graph_Executable.s = (RDF_Graph_Executable.S_IRI i_rdf_Seq);
    RDF_Graph_Executable.p = i_rdfs_subClassOf;
    RDF_Graph_Executable.o = (RDF_Graph_Executable.T_IRI i_rdfs_Container)
  }
let rdfs_axiom_cmp_subClassOf_property : RDF_Graph_Executable.triple=
  {
    RDF_Graph_Executable.s =
      (RDF_Graph_Executable.S_IRI i_rdfs_ContainerMembershipProperty);
    RDF_Graph_Executable.p = i_rdfs_subClassOf;
    RDF_Graph_Executable.o = (RDF_Graph_Executable.T_IRI i_rdf_Property)
  }
let rdfs_axiom_isDefinedBy_subPropertyOf_seeAlso :
  RDF_Graph_Executable.triple=
  {
    RDF_Graph_Executable.s = (RDF_Graph_Executable.S_IRI i_rdfs_isDefinedBy);
    RDF_Graph_Executable.p = i_rdfs_subPropertyOf;
    RDF_Graph_Executable.o = (RDF_Graph_Executable.T_IRI i_rdfs_seeAlso)
  }
let rdfs_axiom_datatype_subClassOf_class : RDF_Graph_Executable.triple=
  {
    RDF_Graph_Executable.s = (RDF_Graph_Executable.S_IRI i_rdfs_Datatype);
    RDF_Graph_Executable.p = i_rdfs_subClassOf;
    RDF_Graph_Executable.o = (RDF_Graph_Executable.T_IRI i_rdfs_Class)
  }
let rdfs_axiomatic_triples : RDF_Graph_Executable.triple Prims.list=
  [rdfs_axiom_dom_type;
  rdfs_axiom_dom_domain;
  rdfs_axiom_dom_range;
  rdfs_axiom_dom_subPropertyOf;
  rdfs_axiom_dom_subClassOf;
  rdfs_axiom_dom_subject;
  rdfs_axiom_dom_predicate;
  rdfs_axiom_dom_object;
  rdfs_axiom_dom_member;
  rdfs_axiom_dom_first;
  rdfs_axiom_dom_rest;
  rdfs_axiom_dom_seeAlso;
  rdfs_axiom_dom_isDefinedBy;
  rdfs_axiom_dom_comment;
  rdfs_axiom_dom_label;
  rdfs_axiom_dom_value;
  rdfs_axiom_rng_type;
  rdfs_axiom_rng_domain;
  rdfs_axiom_rng_range;
  rdfs_axiom_rng_subPropertyOf;
  rdfs_axiom_rng_subClassOf;
  rdfs_axiom_rng_subject;
  rdfs_axiom_rng_predicate;
  rdfs_axiom_rng_object;
  rdfs_axiom_rng_member;
  rdfs_axiom_rng_first;
  rdfs_axiom_rng_rest;
  rdfs_axiom_rng_seeAlso;
  rdfs_axiom_rng_isDefinedBy;
  rdfs_axiom_rng_comment;
  rdfs_axiom_rng_label;
  rdfs_axiom_rng_value;
  rdfs_axiom_alt_subClassOf_container;
  rdfs_axiom_bag_subClassOf_container;
  rdfs_axiom_seq_subClassOf_container;
  rdfs_axiom_cmp_subClassOf_property;
  rdfs_axiom_isDefinedBy_subPropertyOf_seeAlso;
  rdfs_axiom_datatype_subClassOf_class]
let finite_axiomatic_triples : RDF_Graph_Executable.triple Prims.list=
  FStar_List_Tot_Base.op_At rdf_axiomatic_triples rdfs_axiomatic_triples
