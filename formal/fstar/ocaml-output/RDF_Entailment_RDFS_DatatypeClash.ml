open Prims
let rec mem_wf_iri (x : RDF_Term.wf_iri) (xs : RDF_Term.wf_iri Prims.list) :
  Prims.bool=
  match xs with
  | [] -> false
  | y::rest -> if x = y then true else mem_wf_iri x rest
let rec has_ill_formed_recognized_literal (g : RDF_Graph.rdf_graph)
  (recognized : RDF_Term.wf_iri Prims.list) : Prims.bool=
  match g with
  | [] -> false
  | t::rest ->
      (match t.RDF_Triple.o with
       | RDF_Term.T_Literal l ->
           if
             (mem_wf_iri l.RDF_Term.datatype recognized) &&
               (XSD_Datatypes.literal_ill_formed l.RDF_Term.datatype
                  l.RDF_Term.lexical_form)
           then true
           else has_ill_formed_recognized_literal rest recognized
       | uu___ -> has_ill_formed_recognized_literal rest recognized)
let rec exists_range_literal_mismatch (g : RDF_Graph.rdf_graph)
  (p_described : RDF_Term.wf_iri) (c : RDF_Term.wf_iri) : Prims.bool=
  match g with
  | [] -> false
  | t::rest ->
      if t.RDF_Triple.p = p_described
      then
        (match t.RDF_Triple.o with
         | RDF_Term.T_Literal l ->
             if l.RDF_Term.datatype <> c
             then true
             else exists_range_literal_mismatch rest p_described c
         | uu___ -> exists_range_literal_mismatch rest p_described c)
      else exists_range_literal_mismatch rest p_described c
let rec has_range_datatype_clash_aux (full : RDF_Graph.rdf_graph)
  (remaining : RDF_Graph.rdf_graph) (recognized : RDF_Term.wf_iri Prims.list)
  : Prims.bool=
  match remaining with
  | [] -> false
  | t::rest ->
      if t.RDF_Triple.p = RDF_Vocabulary_Axioms.i_rdfs_range
      then
        (match ((t.RDF_Triple.s), (t.RDF_Triple.o)) with
         | (RDF_Term.S_IRI p_described, RDF_Term.T_IRI c) ->
             if
               (mem_wf_iri c recognized) &&
                 (exists_range_literal_mismatch full p_described c)
             then true
             else has_range_datatype_clash_aux full rest recognized
         | (uu___, uu___1) ->
             has_range_datatype_clash_aux full rest recognized)
      else has_range_datatype_clash_aux full rest recognized
let has_range_datatype_clash (g : RDF_Graph.rdf_graph)
  (recognized : RDF_Term.wf_iri Prims.list) : Prims.bool=
  has_range_datatype_clash_aux g g recognized
let rdfs_d_inconsistent (g : RDF_Graph.rdf_graph)
  (recognized : RDF_Term.wf_iri Prims.list) : Prims.bool=
  (has_ill_formed_recognized_literal g recognized) ||
    (has_range_datatype_clash g recognized)
let wex_foo : RDF_Term.wf_iri= "http://example.org/foo"
let wex_bar : RDF_Term.wf_iri= "http://example.org/bar"
let lit_flargh_integer : RDF_Term.wf_literal=
  {
    RDF_Term.lexical_form = "flargh";
    RDF_Term.datatype = RDF_Term.xsd_integer;
    RDF_Term.lang_tag = FStar_Pervasives_Native.None;
    RDF_Term.direction = FStar_Pervasives_Native.None
  }
let lit_25_integer : RDF_Term.wf_literal=
  {
    RDF_Term.lexical_form = "25";
    RDF_Term.datatype = RDF_Term.xsd_integer;
    RDF_Term.lang_tag = FStar_Pervasives_Native.None;
    RDF_Term.direction = FStar_Pervasives_Native.None
  }
let lit_25_string : RDF_Term.wf_literal=
  {
    RDF_Term.lexical_form = "25";
    RDF_Term.datatype = RDF_Term.xsd_string;
    RDF_Term.lang_tag = FStar_Pervasives_Native.None;
    RDF_Term.direction = FStar_Pervasives_Native.None
  }
let clash_action_ill_formed : RDF_Graph.rdf_graph=
  [{
     RDF_Triple.s = (RDF_Term.S_IRI wex_foo);
     RDF_Triple.p = wex_bar;
     RDF_Triple.o = (RDF_Term.T_Literal lit_flargh_integer)
   }]
let consistent_action_well_formed : RDF_Graph.rdf_graph=
  [{
     RDF_Triple.s = (RDF_Term.S_IRI wex_foo);
     RDF_Triple.p = wex_bar;
     RDF_Triple.o = (RDF_Term.T_Literal lit_25_integer)
   }]
let clash_action_range : RDF_Graph.rdf_graph=
  [{
     RDF_Triple.s = (RDF_Term.S_IRI wex_foo);
     RDF_Triple.p = wex_bar;
     RDF_Triple.o = (RDF_Term.T_Literal lit_25_integer)
   };
  {
    RDF_Triple.s = (RDF_Term.S_IRI wex_bar);
    RDF_Triple.p = RDF_Vocabulary_Axioms.i_rdfs_range;
    RDF_Triple.o = (RDF_Term.T_IRI RDF_Term.xsd_string)
  }]
let consistent_action_range_matches : RDF_Graph.rdf_graph=
  [{
     RDF_Triple.s = (RDF_Term.S_IRI wex_foo);
     RDF_Triple.p = wex_bar;
     RDF_Triple.o = (RDF_Term.T_Literal lit_25_integer)
   };
  {
    RDF_Triple.s = (RDF_Term.S_IRI wex_bar);
    RDF_Triple.p = RDF_Vocabulary_Axioms.i_rdfs_range;
    RDF_Triple.o = (RDF_Term.T_IRI RDF_Term.xsd_integer)
  }]
let ex_datatype_subclassof : RDF_Graph.rdf_graph=
  [{
     RDF_Triple.s = (RDF_Term.S_IRI RDF_Term.xsd_integer);
     RDF_Triple.p = RDF_Vocabulary_Axioms.i_rdfs_subClassOf;
     RDF_Triple.o = (RDF_Term.T_IRI RDF_Term.xsd_decimal)
   }]
let clash_action_range_plain : RDF_Graph.rdf_graph=
  [{
     RDF_Triple.s = (RDF_Term.S_IRI wex_foo);
     RDF_Triple.p = wex_bar;
     RDF_Triple.o = (RDF_Term.T_Literal lit_25_string)
   };
  {
    RDF_Triple.s = (RDF_Term.S_IRI wex_bar);
    RDF_Triple.p = RDF_Vocabulary_Axioms.i_rdfs_range;
    RDF_Triple.o = (RDF_Term.T_IRI RDF_Term.xsd_integer)
  }]
