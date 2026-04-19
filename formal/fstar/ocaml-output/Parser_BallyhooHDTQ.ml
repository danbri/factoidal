open Prims
type hdtq_annotation_mode =
  | HQ_AnnotatedGraphs 
  | HQ_AnnotatedTriples 
let uu___is_HQ_AnnotatedGraphs (projectee : hdtq_annotation_mode) :
  Prims.bool=
  match projectee with | HQ_AnnotatedGraphs -> true | uu___ -> false
let uu___is_HQ_AnnotatedTriples (projectee : hdtq_annotation_mode) :
  Prims.bool=
  match projectee with | HQ_AnnotatedTriples -> true | uu___ -> false
type hdtq_graph_dictionary_summary =
  {
  hgds_num_graphs: Prims.nat ;
  hgds_size_strings: Prims.nat }
let __proj__Mkhdtq_graph_dictionary_summary__item__hgds_num_graphs
  (projectee : hdtq_graph_dictionary_summary) : Prims.nat=
  match projectee with
  | { hgds_num_graphs; hgds_size_strings;_} -> hgds_num_graphs
let __proj__Mkhdtq_graph_dictionary_summary__item__hgds_size_strings
  (projectee : hdtq_graph_dictionary_summary) : Prims.nat=
  match projectee with
  | { hgds_num_graphs; hgds_size_strings;_} -> hgds_size_strings
type hdtq_quad_info_summary =
  {
  hqis_num_quads: Prims.nat ;
  hqis_annotation_mode: hdtq_annotation_mode }
let __proj__Mkhdtq_quad_info_summary__item__hqis_num_quads
  (projectee : hdtq_quad_info_summary) : Prims.nat=
  match projectee with
  | { hqis_num_quads; hqis_annotation_mode;_} -> hqis_num_quads
let __proj__Mkhdtq_quad_info_summary__item__hqis_annotation_mode
  (projectee : hdtq_quad_info_summary) : hdtq_annotation_mode=
  match projectee with
  | { hqis_num_quads; hqis_annotation_mode;_} -> hqis_annotation_mode
type hdtq_artifact_summary =
  {
  hqas_hdt: Parser_BallyhooHDT.hdt_artifact_summary ;
  hqas_graph_dictionary: hdtq_graph_dictionary_summary ;
  hqas_quad_info: hdtq_quad_info_summary }
let __proj__Mkhdtq_artifact_summary__item__hqas_hdt
  (projectee : hdtq_artifact_summary) :
  Parser_BallyhooHDT.hdt_artifact_summary=
  match projectee with
  | { hqas_hdt; hqas_graph_dictionary; hqas_quad_info;_} -> hqas_hdt
let __proj__Mkhdtq_artifact_summary__item__hqas_graph_dictionary
  (projectee : hdtq_artifact_summary) : hdtq_graph_dictionary_summary=
  match projectee with
  | { hqas_hdt; hqas_graph_dictionary; hqas_quad_info;_} ->
      hqas_graph_dictionary
let __proj__Mkhdtq_artifact_summary__item__hqas_quad_info
  (projectee : hdtq_artifact_summary) : hdtq_quad_info_summary=
  match projectee with
  | { hqas_hdt; hqas_graph_dictionary; hqas_quad_info;_} -> hqas_quad_info
type hdtq_handle = unit
type hdtq_graph_ref = Prims.nat
type hdtq_bound_qp =
  {
  hqbp_s: Parser_BallyhooHDT.hdt_term_ref FStar_Pervasives_Native.option ;
  hqbp_p: Parser_BallyhooHDT.hdt_term_ref FStar_Pervasives_Native.option ;
  hqbp_o: Parser_BallyhooHDT.hdt_term_ref FStar_Pervasives_Native.option ;
  hqbp_g: hdtq_graph_ref FStar_Pervasives_Native.option }
let __proj__Mkhdtq_bound_qp__item__hqbp_s (projectee : hdtq_bound_qp) :
  Parser_BallyhooHDT.hdt_term_ref FStar_Pervasives_Native.option=
  match projectee with | { hqbp_s; hqbp_p; hqbp_o; hqbp_g;_} -> hqbp_s
let __proj__Mkhdtq_bound_qp__item__hqbp_p (projectee : hdtq_bound_qp) :
  Parser_BallyhooHDT.hdt_term_ref FStar_Pervasives_Native.option=
  match projectee with | { hqbp_s; hqbp_p; hqbp_o; hqbp_g;_} -> hqbp_p
let __proj__Mkhdtq_bound_qp__item__hqbp_o (projectee : hdtq_bound_qp) :
  Parser_BallyhooHDT.hdt_term_ref FStar_Pervasives_Native.option=
  match projectee with | { hqbp_s; hqbp_p; hqbp_o; hqbp_g;_} -> hqbp_o
let __proj__Mkhdtq_bound_qp__item__hqbp_g (projectee : hdtq_bound_qp) :
  hdtq_graph_ref FStar_Pervasives_Native.option=
  match projectee with | { hqbp_s; hqbp_p; hqbp_o; hqbp_g;_} -> hqbp_g
type hdtq_qp_row =
  {
  hqrow_s: Parser_BallyhooHDT.hdt_term_ref FStar_Pervasives_Native.option ;
  hqrow_p: Parser_BallyhooHDT.hdt_term_ref FStar_Pervasives_Native.option ;
  hqrow_o: Parser_BallyhooHDT.hdt_term_ref FStar_Pervasives_Native.option ;
  hqrow_g: hdtq_graph_ref FStar_Pervasives_Native.option }
let __proj__Mkhdtq_qp_row__item__hqrow_s (projectee : hdtq_qp_row) :
  Parser_BallyhooHDT.hdt_term_ref FStar_Pervasives_Native.option=
  match projectee with | { hqrow_s; hqrow_p; hqrow_o; hqrow_g;_} -> hqrow_s
let __proj__Mkhdtq_qp_row__item__hqrow_p (projectee : hdtq_qp_row) :
  Parser_BallyhooHDT.hdt_term_ref FStar_Pervasives_Native.option=
  match projectee with | { hqrow_s; hqrow_p; hqrow_o; hqrow_g;_} -> hqrow_p
let __proj__Mkhdtq_qp_row__item__hqrow_o (projectee : hdtq_qp_row) :
  Parser_BallyhooHDT.hdt_term_ref FStar_Pervasives_Native.option=
  match projectee with | { hqrow_s; hqrow_p; hqrow_o; hqrow_g;_} -> hqrow_o
let __proj__Mkhdtq_qp_row__item__hqrow_g (projectee : hdtq_qp_row) :
  hdtq_graph_ref FStar_Pervasives_Native.option=
  match projectee with | { hqrow_s; hqrow_p; hqrow_o; hqrow_g;_} -> hqrow_g
type hdtq_dataset_store =
  {
  hqds_artifact_path: Prims.string ;
  hqds_summary: hdtq_artifact_summary FStar_Pervasives_Native.option ;
  hqds_handle: hdtq_handle }
let __proj__Mkhdtq_dataset_store__item__hqds_artifact_path
  (projectee : hdtq_dataset_store) : Prims.string=
  match projectee with
  | { hqds_artifact_path; hqds_summary; hqds_handle;_} -> hqds_artifact_path
let __proj__Mkhdtq_dataset_store__item__hqds_summary
  (projectee : hdtq_dataset_store) :
  hdtq_artifact_summary FStar_Pervasives_Native.option=
  match projectee with
  | { hqds_artifact_path; hqds_summary; hqds_handle;_} -> hqds_summary
let __proj__Mkhdtq_dataset_store__item__hqds_handle
  (projectee : hdtq_dataset_store) : hdtq_handle=
  match projectee with
  | { hqds_artifact_path; hqds_summary; hqds_handle;_} -> hqds_handle
type hdtq_named_graph_store =
  {
  hqng_name: RDF_Graph_Executable.iri ;
  hqng_ref: hdtq_graph_ref ;
  hqng_dataset: hdtq_dataset_store }
let __proj__Mkhdtq_named_graph_store__item__hqng_name
  (projectee : hdtq_named_graph_store) : RDF_Graph_Executable.iri=
  match projectee with | { hqng_name; hqng_ref; hqng_dataset;_} -> hqng_name
let __proj__Mkhdtq_named_graph_store__item__hqng_ref
  (projectee : hdtq_named_graph_store) : hdtq_graph_ref=
  match projectee with | { hqng_name; hqng_ref; hqng_dataset;_} -> hqng_ref
let __proj__Mkhdtq_named_graph_store__item__hqng_dataset
  (projectee : hdtq_named_graph_store) : hdtq_dataset_store=
  match projectee with
  | { hqng_name; hqng_ref; hqng_dataset;_} -> hqng_dataset
let hdtq_open_dataset_store (artifact_path : Prims.string)
  (summary : hdtq_artifact_summary FStar_Pervasives_Native.option) :
  hdtq_dataset_store FStar_Pervasives_Native.option=
  failwith "Not yet implemented: Parser.BallyhooHDTQ.hdtq_open_dataset_store"
let hdtq_dataset_summary (uu___ : hdtq_dataset_store) :
  hdtq_artifact_summary FStar_Pervasives_Native.option=
  failwith "Not yet implemented: Parser.BallyhooHDTQ.hdtq_dataset_summary"
let hdtq_named_graphs (uu___ : hdtq_dataset_store) :
  hdtq_named_graph_store Prims.list=
  failwith "Not yet implemented: Parser.BallyhooHDTQ.hdtq_named_graphs"
let hdtq_lookup_named_graph (uu___ : hdtq_dataset_store)
  (uu___1 : RDF_Graph_Executable.iri) :
  hdtq_named_graph_store FStar_Pervasives_Native.option=
  failwith "Not yet implemented: Parser.BallyhooHDTQ.hdtq_lookup_named_graph"
let hdtq_encode_subject (uu___ : hdtq_dataset_store)
  (uu___1 : RDF_Graph_Executable.subject) :
  Parser_BallyhooHDT.hdt_term_ref FStar_Pervasives_Native.option=
  failwith "Not yet implemented: Parser.BallyhooHDTQ.hdtq_encode_subject"
let hdtq_encode_predicate (uu___ : hdtq_dataset_store)
  (uu___1 : RDF_Graph_Executable.wf_iri) :
  Parser_BallyhooHDT.hdt_term_ref FStar_Pervasives_Native.option=
  failwith "Not yet implemented: Parser.BallyhooHDTQ.hdtq_encode_predicate"
let hdtq_encode_object (uu___ : hdtq_dataset_store)
  (uu___1 : RDF_Graph_Executable.rdf_term) :
  Parser_BallyhooHDT.hdt_term_ref FStar_Pervasives_Native.option=
  failwith "Not yet implemented: Parser.BallyhooHDTQ.hdtq_encode_object"
let hdtq_encode_graph_name (uu___ : hdtq_dataset_store)
  (uu___1 : RDF_Graph_Executable.iri) :
  hdtq_graph_ref FStar_Pervasives_Native.option=
  failwith "Not yet implemented: Parser.BallyhooHDTQ.hdtq_encode_graph_name"
let hdtq_decode_subject (uu___ : hdtq_dataset_store)
  (uu___1 : Parser_BallyhooHDT.hdt_term_ref) : RDF_Graph_Executable.subject=
  failwith "Not yet implemented: Parser.BallyhooHDTQ.hdtq_decode_subject"
let hdtq_decode_predicate (uu___ : hdtq_dataset_store)
  (uu___1 : Parser_BallyhooHDT.hdt_term_ref) : RDF_Graph_Executable.wf_iri=
  failwith "Not yet implemented: Parser.BallyhooHDTQ.hdtq_decode_predicate"
let hdtq_decode_object (uu___ : hdtq_dataset_store)
  (uu___1 : Parser_BallyhooHDT.hdt_term_ref) : RDF_Graph_Executable.rdf_term=
  failwith "Not yet implemented: Parser.BallyhooHDTQ.hdtq_decode_object"
let hdtq_decode_graph_name (uu___ : hdtq_dataset_store)
  (uu___1 : hdtq_graph_ref) : RDF_Graph_Executable.iri=
  failwith "Not yet implemented: Parser.BallyhooHDTQ.hdtq_decode_graph_name"
let hdtq_search (uu___ : hdtq_dataset_store) (uu___1 : hdtq_bound_qp) :
  hdtq_qp_row Prims.list=
  failwith "Not yet implemented: Parser.BallyhooHDTQ.hdtq_search"
let hdtq_estimate (uu___ : hdtq_dataset_store) (uu___1 : hdtq_bound_qp) :
  Prims.nat=
  failwith "Not yet implemented: Parser.BallyhooHDTQ.hdtq_estimate"
let hdtq_predicate_present_in_graph (uu___ : hdtq_named_graph_store)
  (uu___1 : RDF_Graph_Executable.wf_iri) : Prims.bool=
  failwith
    "Not yet implemented: Parser.BallyhooHDTQ.hdtq_predicate_present_in_graph"
let hdtq_graph_candidates_for_predicate (uu___ : hdtq_dataset_store)
  (uu___1 : RDF_Graph_Executable.wf_iri) : hdtq_named_graph_store Prims.list=
  failwith
    "Not yet implemented: Parser.BallyhooHDTQ.hdtq_graph_candidates_for_predicate"
let hdtq_build_bound_qp (ds : hdtq_dataset_store)
  (s : RDF_Graph_Executable.subject FStar_Pervasives_Native.option)
  (p : RDF_Graph_Executable.wf_iri FStar_Pervasives_Native.option)
  (o : RDF_Graph_Executable.rdf_term FStar_Pervasives_Native.option)
  (g : RDF_Graph_Executable.iri FStar_Pervasives_Native.option) :
  hdtq_bound_qp=
  {
    hqbp_s =
      (match s with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some sv -> hdtq_encode_subject ds sv);
    hqbp_p =
      (match p with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some pv -> hdtq_encode_predicate ds pv);
    hqbp_o =
      (match o with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some ov -> hdtq_encode_object ds ov);
    hqbp_g =
      (match g with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some gv -> hdtq_encode_graph_name ds gv)
  }
let hdtq_row_to_quad (ds : hdtq_dataset_store) (row : hdtq_qp_row) :
  (RDF_Graph_Executable.triple * RDF_Graph_Executable.iri
    FStar_Pervasives_Native.option) FStar_Pervasives_Native.option=
  match ((row.hqrow_s), (row.hqrow_p), (row.hqrow_o)) with
  | (FStar_Pervasives_Native.Some sr, FStar_Pervasives_Native.Some pr,
     FStar_Pervasives_Native.Some orf) ->
      FStar_Pervasives_Native.Some
        ({
           RDF_Graph_Executable.s = (hdtq_decode_subject ds sr);
           RDF_Graph_Executable.p = (hdtq_decode_predicate ds pr);
           RDF_Graph_Executable.o = (hdtq_decode_object ds orf)
         },
          ((match row.hqrow_g with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some gr ->
                FStar_Pervasives_Native.Some (hdtq_decode_graph_name ds gr))))
  | uu___ -> FStar_Pervasives_Native.None
let rec hdtq_rows_to_quads (ds : hdtq_dataset_store)
  (rows : hdtq_qp_row Prims.list) :
  (RDF_Graph_Executable.triple * RDF_Graph_Executable.iri
    FStar_Pervasives_Native.option) Prims.list=
  match rows with
  | [] -> []
  | row::rest ->
      let rest' = hdtq_rows_to_quads ds rest in
      (match hdtq_row_to_quad ds row with
       | FStar_Pervasives_Native.Some q -> q :: rest'
       | FStar_Pervasives_Native.None -> rest')
let rec hdtq_named_graphs_to_bindings
  (ngs : hdtq_named_graph_store Prims.list) :
  Parser_BallyhooHDT.corpus_graph_binding Prims.list=
  match ngs with
  | [] -> []
  | ng::rest ->
      {
        Parser_BallyhooHDT.cgb_graph_name = (ng.hqng_name);
        Parser_BallyhooHDT.cgb_artifact_path =
          ((ng.hqng_dataset).hqds_artifact_path);
        Parser_BallyhooHDT.cgb_summary =
          ((match (ng.hqng_dataset).hqds_summary with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some s ->
                FStar_Pervasives_Native.Some (s.hqas_hdt)))
      } :: (hdtq_named_graphs_to_bindings rest)
