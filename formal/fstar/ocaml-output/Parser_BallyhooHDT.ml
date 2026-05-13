open Prims
type ballyhoo_order =
  | BO_SPO 
  | BO_SOP 
  | BO_PSO 
  | BO_POS 
  | BO_OSP 
  | BO_OPS 
let uu___is_BO_SPO (projectee : ballyhoo_order) : Prims.bool=
  match projectee with | BO_SPO -> true | uu___ -> false
let uu___is_BO_SOP (projectee : ballyhoo_order) : Prims.bool=
  match projectee with | BO_SOP -> true | uu___ -> false
let uu___is_BO_PSO (projectee : ballyhoo_order) : Prims.bool=
  match projectee with | BO_PSO -> true | uu___ -> false
let uu___is_BO_POS (projectee : ballyhoo_order) : Prims.bool=
  match projectee with | BO_POS -> true | uu___ -> false
let uu___is_BO_OSP (projectee : ballyhoo_order) : Prims.bool=
  match projectee with | BO_OSP -> true | uu___ -> false
let uu___is_BO_OPS (projectee : ballyhoo_order) : Prims.bool=
  match projectee with | BO_OPS -> true | uu___ -> false
type hdt_control_info =
  {
  hci_format_iri: Prims.string ;
  hci_length_hint: Prims.nat }
let __proj__Mkhdt_control_info__item__hci_format_iri
  (projectee : hdt_control_info) : Prims.string=
  match projectee with
  | { hci_format_iri; hci_length_hint;_} -> hci_format_iri
let __proj__Mkhdt_control_info__item__hci_length_hint
  (projectee : hdt_control_info) : Prims.nat=
  match projectee with
  | { hci_format_iri; hci_length_hint;_} -> hci_length_hint
type hdt_dictionary_summary =
  {
  hds_num_shared_subject_object: Prims.nat ;
  hds_num_subjects: Prims.nat ;
  hds_num_predicates: Prims.nat ;
  hds_num_objects: Prims.nat ;
  hds_size_strings: Prims.nat }
let __proj__Mkhdt_dictionary_summary__item__hds_num_shared_subject_object
  (projectee : hdt_dictionary_summary) : Prims.nat=
  match projectee with
  | { hds_num_shared_subject_object; hds_num_subjects; hds_num_predicates;
      hds_num_objects; hds_size_strings;_} -> hds_num_shared_subject_object
let __proj__Mkhdt_dictionary_summary__item__hds_num_subjects
  (projectee : hdt_dictionary_summary) : Prims.nat=
  match projectee with
  | { hds_num_shared_subject_object; hds_num_subjects; hds_num_predicates;
      hds_num_objects; hds_size_strings;_} -> hds_num_subjects
let __proj__Mkhdt_dictionary_summary__item__hds_num_predicates
  (projectee : hdt_dictionary_summary) : Prims.nat=
  match projectee with
  | { hds_num_shared_subject_object; hds_num_subjects; hds_num_predicates;
      hds_num_objects; hds_size_strings;_} -> hds_num_predicates
let __proj__Mkhdt_dictionary_summary__item__hds_num_objects
  (projectee : hdt_dictionary_summary) : Prims.nat=
  match projectee with
  | { hds_num_shared_subject_object; hds_num_subjects; hds_num_predicates;
      hds_num_objects; hds_size_strings;_} -> hds_num_objects
let __proj__Mkhdt_dictionary_summary__item__hds_size_strings
  (projectee : hdt_dictionary_summary) : Prims.nat=
  match projectee with
  | { hds_num_shared_subject_object; hds_num_subjects; hds_num_predicates;
      hds_num_objects; hds_size_strings;_} -> hds_size_strings
type hdt_triples_summary =
  {
  hts_num_triples: Prims.nat ;
  hts_order: ballyhoo_order }
let __proj__Mkhdt_triples_summary__item__hts_num_triples
  (projectee : hdt_triples_summary) : Prims.nat=
  match projectee with | { hts_num_triples; hts_order;_} -> hts_num_triples
let __proj__Mkhdt_triples_summary__item__hts_order
  (projectee : hdt_triples_summary) : ballyhoo_order=
  match projectee with | { hts_num_triples; hts_order;_} -> hts_order
type hdt_statistics = {
  hs_hdt_size: Prims.nat ;
  hs_original_size: Prims.nat }
let __proj__Mkhdt_statistics__item__hs_hdt_size (projectee : hdt_statistics)
  : Prims.nat=
  match projectee with | { hs_hdt_size; hs_original_size;_} -> hs_hdt_size
let __proj__Mkhdt_statistics__item__hs_original_size
  (projectee : hdt_statistics) : Prims.nat=
  match projectee with
  | { hs_hdt_size; hs_original_size;_} -> hs_original_size
type hdt_artifact_summary =
  {
  has_source_iri: RDF_Graph_Executable.iri FStar_Pervasives_Native.option ;
  has_dictionary: hdt_dictionary_summary ;
  has_triples: hdt_triples_summary ;
  has_statistics: hdt_statistics }
let __proj__Mkhdt_artifact_summary__item__has_source_iri
  (projectee : hdt_artifact_summary) :
  RDF_Graph_Executable.iri FStar_Pervasives_Native.option=
  match projectee with
  | { has_source_iri; has_dictionary; has_triples; has_statistics;_} ->
      has_source_iri
let __proj__Mkhdt_artifact_summary__item__has_dictionary
  (projectee : hdt_artifact_summary) : hdt_dictionary_summary=
  match projectee with
  | { has_source_iri; has_dictionary; has_triples; has_statistics;_} ->
      has_dictionary
let __proj__Mkhdt_artifact_summary__item__has_triples
  (projectee : hdt_artifact_summary) : hdt_triples_summary=
  match projectee with
  | { has_source_iri; has_dictionary; has_triples; has_statistics;_} ->
      has_triples
let __proj__Mkhdt_artifact_summary__item__has_statistics
  (projectee : hdt_artifact_summary) : hdt_statistics=
  match projectee with
  | { has_source_iri; has_dictionary; has_triples; has_statistics;_} ->
      has_statistics
type corpus_graph_binding =
  {
  cgb_graph_name: RDF_Graph_Executable.iri ;
  cgb_artifact_path: Prims.string ;
  cgb_summary: hdt_artifact_summary FStar_Pervasives_Native.option }
let __proj__Mkcorpus_graph_binding__item__cgb_graph_name
  (projectee : corpus_graph_binding) : RDF_Graph_Executable.iri=
  match projectee with
  | { cgb_graph_name; cgb_artifact_path; cgb_summary;_} -> cgb_graph_name
let __proj__Mkcorpus_graph_binding__item__cgb_artifact_path
  (projectee : corpus_graph_binding) : Prims.string=
  match projectee with
  | { cgb_graph_name; cgb_artifact_path; cgb_summary;_} -> cgb_artifact_path
let __proj__Mkcorpus_graph_binding__item__cgb_summary
  (projectee : corpus_graph_binding) :
  hdt_artifact_summary FStar_Pervasives_Native.option=
  match projectee with
  | { cgb_graph_name; cgb_artifact_path; cgb_summary;_} -> cgb_summary
type hdt_handle = unit
type hdt_term_ref = Prims.nat
type hdt_bound_tp =
  {
  hbt_s: hdt_term_ref FStar_Pervasives_Native.option ;
  hbt_p: hdt_term_ref FStar_Pervasives_Native.option ;
  hbt_o: hdt_term_ref FStar_Pervasives_Native.option }
let __proj__Mkhdt_bound_tp__item__hbt_s (projectee : hdt_bound_tp) :
  hdt_term_ref FStar_Pervasives_Native.option=
  match projectee with | { hbt_s; hbt_p; hbt_o;_} -> hbt_s
let __proj__Mkhdt_bound_tp__item__hbt_p (projectee : hdt_bound_tp) :
  hdt_term_ref FStar_Pervasives_Native.option=
  match projectee with | { hbt_s; hbt_p; hbt_o;_} -> hbt_p
let __proj__Mkhdt_bound_tp__item__hbt_o (projectee : hdt_bound_tp) :
  hdt_term_ref FStar_Pervasives_Native.option=
  match projectee with | { hbt_s; hbt_p; hbt_o;_} -> hbt_o
type hdt_tp_row =
  {
  hrow_s: hdt_term_ref FStar_Pervasives_Native.option ;
  hrow_p: hdt_term_ref FStar_Pervasives_Native.option ;
  hrow_o: hdt_term_ref FStar_Pervasives_Native.option }
let __proj__Mkhdt_tp_row__item__hrow_s (projectee : hdt_tp_row) :
  hdt_term_ref FStar_Pervasives_Native.option=
  match projectee with | { hrow_s; hrow_p; hrow_o;_} -> hrow_s
let __proj__Mkhdt_tp_row__item__hrow_p (projectee : hdt_tp_row) :
  hdt_term_ref FStar_Pervasives_Native.option=
  match projectee with | { hrow_s; hrow_p; hrow_o;_} -> hrow_p
let __proj__Mkhdt_tp_row__item__hrow_o (projectee : hdt_tp_row) :
  hdt_term_ref FStar_Pervasives_Native.option=
  match projectee with | { hrow_s; hrow_p; hrow_o;_} -> hrow_o
type hdt_graph_store =
  {
  hgs_graph_name: RDF_Graph_Executable.iri FStar_Pervasives_Native.option ;
  hgs_artifact_path: Prims.string ;
  hgs_summary: hdt_artifact_summary FStar_Pervasives_Native.option ;
  hgs_handle: hdt_handle }
let __proj__Mkhdt_graph_store__item__hgs_graph_name
  (projectee : hdt_graph_store) :
  RDF_Graph_Executable.iri FStar_Pervasives_Native.option=
  match projectee with
  | { hgs_graph_name; hgs_artifact_path; hgs_summary; hgs_handle;_} ->
      hgs_graph_name
let __proj__Mkhdt_graph_store__item__hgs_artifact_path
  (projectee : hdt_graph_store) : Prims.string=
  match projectee with
  | { hgs_graph_name; hgs_artifact_path; hgs_summary; hgs_handle;_} ->
      hgs_artifact_path
let __proj__Mkhdt_graph_store__item__hgs_summary
  (projectee : hdt_graph_store) :
  hdt_artifact_summary FStar_Pervasives_Native.option=
  match projectee with
  | { hgs_graph_name; hgs_artifact_path; hgs_summary; hgs_handle;_} ->
      hgs_summary
let __proj__Mkhdt_graph_store__item__hgs_handle (projectee : hdt_graph_store)
  : hdt_handle=
  match projectee with
  | { hgs_graph_name; hgs_artifact_path; hgs_summary; hgs_handle;_} ->
      hgs_handle
let hdt_open_graph_store
  (graph_name : RDF_Graph_Executable.iri FStar_Pervasives_Native.option)
  (artifact_path : Prims.string)
  (summary : hdt_artifact_summary FStar_Pervasives_Native.option) :
  hdt_graph_store FStar_Pervasives_Native.option=
  failwith "Not yet implemented: Parser.BallyhooHDT.hdt_open_graph_store"
let hdt_graph_summary (uu___ : hdt_graph_store) :
  hdt_artifact_summary FStar_Pervasives_Native.option=
  failwith "Not yet implemented: Parser.BallyhooHDT.hdt_graph_summary"
let hdt_encode_subject (uu___ : hdt_graph_store)
  (uu___1 : RDF_Graph_Executable.subject) :
  hdt_term_ref FStar_Pervasives_Native.option=
  failwith "Not yet implemented: Parser.BallyhooHDT.hdt_encode_subject"
let hdt_encode_predicate (uu___ : hdt_graph_store)
  (uu___1 : RDF_Graph_Executable.wf_iri) :
  hdt_term_ref FStar_Pervasives_Native.option=
  failwith "Not yet implemented: Parser.BallyhooHDT.hdt_encode_predicate"
let hdt_encode_object (uu___ : hdt_graph_store)
  (uu___1 : RDF_Graph_Executable.rdf_term) :
  hdt_term_ref FStar_Pervasives_Native.option=
  failwith "Not yet implemented: Parser.BallyhooHDT.hdt_encode_object"
let hdt_decode_subject (uu___ : hdt_graph_store) (uu___1 : hdt_term_ref) :
  RDF_Graph_Executable.subject=
  failwith "Not yet implemented: Parser.BallyhooHDT.hdt_decode_subject"
let hdt_decode_predicate (uu___ : hdt_graph_store) (uu___1 : hdt_term_ref) :
  RDF_Graph_Executable.wf_iri=
  failwith "Not yet implemented: Parser.BallyhooHDT.hdt_decode_predicate"
let hdt_decode_object (uu___ : hdt_graph_store) (uu___1 : hdt_term_ref) :
  RDF_Graph_Executable.rdf_term=
  failwith "Not yet implemented: Parser.BallyhooHDT.hdt_decode_object"
let hdt_search (uu___ : hdt_graph_store) (uu___1 : hdt_bound_tp) :
  hdt_tp_row Prims.list=
  failwith "Not yet implemented: Parser.BallyhooHDT.hdt_search"
let hdt_estimate (uu___ : hdt_graph_store) (uu___1 : hdt_bound_tp) :
  Prims.nat= failwith "Not yet implemented: Parser.BallyhooHDT.hdt_estimate"
let hdt_predicate_present (uu___ : hdt_graph_store)
  (uu___1 : RDF_Graph_Executable.wf_iri) : Prims.bool=
  failwith "Not yet implemented: Parser.BallyhooHDT.hdt_predicate_present"
let hdt_named_candidate_graphs (bindings : corpus_graph_binding Prims.list)
  (predicate_hint :
    RDF_Graph_Executable.wf_iri FStar_Pervasives_Native.option)
  : corpus_graph_binding Prims.list=
  failwith
    "Not yet implemented: Parser.BallyhooHDT.hdt_named_candidate_graphs"
let hdt_build_bound_tp (gs : hdt_graph_store)
  (s : RDF_Graph_Executable.subject FStar_Pervasives_Native.option)
  (p : RDF_Graph_Executable.wf_iri FStar_Pervasives_Native.option)
  (o : RDF_Graph_Executable.rdf_term FStar_Pervasives_Native.option) :
  hdt_bound_tp=
  {
    hbt_s =
      (match s with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some sv -> hdt_encode_subject gs sv);
    hbt_p =
      (match p with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some pv -> hdt_encode_predicate gs pv);
    hbt_o =
      (match o with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some ov -> hdt_encode_object gs ov)
  }
let hdt_row_to_triple (gs : hdt_graph_store) (row : hdt_tp_row) :
  RDF_Graph_Executable.triple FStar_Pervasives_Native.option=
  match ((row.hrow_s), (row.hrow_p), (row.hrow_o)) with
  | (FStar_Pervasives_Native.Some sr, FStar_Pervasives_Native.Some pr,
     FStar_Pervasives_Native.Some orf) ->
      FStar_Pervasives_Native.Some
        {
          RDF_Graph_Executable.s = (hdt_decode_subject gs sr);
          RDF_Graph_Executable.p = (hdt_decode_predicate gs pr);
          RDF_Graph_Executable.o = (hdt_decode_object gs orf)
        }
  | uu___ -> FStar_Pervasives_Native.None
let rec hdt_rows_to_triples (gs : hdt_graph_store)
  (rows : hdt_tp_row Prims.list) : RDF_Graph_Executable.triple Prims.list=
  match rows with
  | [] -> []
  | row::rest ->
      let rest' = hdt_rows_to_triples gs rest in
      (match hdt_row_to_triple gs row with
       | FStar_Pervasives_Native.Some t -> t :: rest'
       | FStar_Pervasives_Native.None -> rest')
let hdt_search_triples (gs : hdt_graph_store)
  (s : RDF_Graph_Executable.subject FStar_Pervasives_Native.option)
  (p : RDF_Graph_Executable.wf_iri FStar_Pervasives_Native.option)
  (o : RDF_Graph_Executable.rdf_term FStar_Pervasives_Native.option) :
  RDF_Graph_Executable.triple Prims.list=
  let bound = hdt_build_bound_tp gs s p o in
  hdt_rows_to_triples gs (hdt_search gs bound)
