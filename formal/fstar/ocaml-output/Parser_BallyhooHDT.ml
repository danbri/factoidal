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
  has_source_iri: RDF_Term.iri FStar_Pervasives_Native.option ;
  has_dictionary: hdt_dictionary_summary ;
  has_triples: hdt_triples_summary ;
  has_statistics: hdt_statistics }
let __proj__Mkhdt_artifact_summary__item__has_source_iri
  (projectee : hdt_artifact_summary) :
  RDF_Term.iri FStar_Pervasives_Native.option=
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
  cgb_graph_name: RDF_Term.iri ;
  cgb_artifact_path: Prims.string ;
  cgb_summary: hdt_artifact_summary FStar_Pervasives_Native.option }
let __proj__Mkcorpus_graph_binding__item__cgb_graph_name
  (projectee : corpus_graph_binding) : RDF_Term.iri=
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
  hgs_graph_name: RDF_Term.iri FStar_Pervasives_Native.option ;
  hgs_artifact_path: Prims.string ;
  hgs_summary: hdt_artifact_summary FStar_Pervasives_Native.option ;
  hgs_hex: Prims.string ;
  hgs_inventory: HDT_Container.hdt_inventory ;
  hgs_triples: HDT_Triples.hdt_triples_info }
let __proj__Mkhdt_graph_store__item__hgs_graph_name
  (projectee : hdt_graph_store) :
  RDF_Term.iri FStar_Pervasives_Native.option=
  match projectee with
  | { hgs_graph_name; hgs_artifact_path; hgs_summary; hgs_hex; hgs_inventory;
      hgs_triples;_} -> hgs_graph_name
let __proj__Mkhdt_graph_store__item__hgs_artifact_path
  (projectee : hdt_graph_store) : Prims.string=
  match projectee with
  | { hgs_graph_name; hgs_artifact_path; hgs_summary; hgs_hex; hgs_inventory;
      hgs_triples;_} -> hgs_artifact_path
let __proj__Mkhdt_graph_store__item__hgs_summary
  (projectee : hdt_graph_store) :
  hdt_artifact_summary FStar_Pervasives_Native.option=
  match projectee with
  | { hgs_graph_name; hgs_artifact_path; hgs_summary; hgs_hex; hgs_inventory;
      hgs_triples;_} -> hgs_summary
let __proj__Mkhdt_graph_store__item__hgs_hex (projectee : hdt_graph_store) :
  Prims.string=
  match projectee with
  | { hgs_graph_name; hgs_artifact_path; hgs_summary; hgs_hex; hgs_inventory;
      hgs_triples;_} -> hgs_hex
let __proj__Mkhdt_graph_store__item__hgs_inventory
  (projectee : hdt_graph_store) : HDT_Container.hdt_inventory=
  match projectee with
  | { hgs_graph_name; hgs_artifact_path; hgs_summary; hgs_hex; hgs_inventory;
      hgs_triples;_} -> hgs_inventory
let __proj__Mkhdt_graph_store__item__hgs_triples
  (projectee : hdt_graph_store) : HDT_Triples.hdt_triples_info=
  match projectee with
  | { hgs_graph_name; hgs_artifact_path; hgs_summary; hgs_hex; hgs_inventory;
      hgs_triples;_} -> hgs_triples
let hdt_open_graph_store
  (graph_name : RDF_Term.iri FStar_Pervasives_Native.option)
  (artifact_path : Prims.string)
  (summary : hdt_artifact_summary FStar_Pervasives_Native.option) :
  hdt_graph_store FStar_Pervasives_Native.option=
  match HDT_Container.hdt_read_inventory artifact_path with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some (hex, inv) ->
      (match HDT_Triples.hdt_read_triples hex inv with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some triples ->
           FStar_Pervasives_Native.Some
             {
               hgs_graph_name = graph_name;
               hgs_artifact_path = artifact_path;
               hgs_summary = summary;
               hgs_hex = hex;
               hgs_inventory = inv;
               hgs_triples = triples
             })
let hdt_graph_summary (gs : hdt_graph_store) :
  hdt_artifact_summary FStar_Pervasives_Native.option= gs.hgs_summary
let opt_pos_to_ref (o : Prims.pos FStar_Pervasives_Native.option) :
  hdt_term_ref FStar_Pervasives_Native.option=
  match o with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some id ->
      let id1 = id in FStar_Pervasives_Native.Some id1
let hdt_encode_subject (gs : hdt_graph_store) (subj : RDF_Term.subject) :
  hdt_term_ref FStar_Pervasives_Native.option=
  opt_pos_to_ref
    (HDT_Dictionary.hdt_term_to_id gs.hgs_hex gs.hgs_inventory
       HDT_Dictionary.Role_Subject (RDF_Graph.subject_to_term subj))
let hdt_encode_predicate (gs : hdt_graph_store) (p : RDF_Term.wf_iri) :
  hdt_term_ref FStar_Pervasives_Native.option=
  opt_pos_to_ref
    (HDT_Dictionary.hdt_term_to_id gs.hgs_hex gs.hgs_inventory
       HDT_Dictionary.Role_Predicate (RDF_Term.T_IRI p))
let hdt_encode_object (gs : hdt_graph_store) (o : RDF_Term.rdf_term) :
  hdt_term_ref FStar_Pervasives_Native.option=
  opt_pos_to_ref
    (HDT_Dictionary.hdt_term_to_id gs.hgs_hex gs.hgs_inventory
       HDT_Dictionary.Role_Object o)
let hdt_decode_error_iri : RDF_Term.wf_iri= "urn:factoidal:hdt-decode-error"
let hdt_decode_error_subject : RDF_Term.subject=
  RDF_Term.S_BNode "hdt-decode-error"
let hdt_decode_error_object : RDF_Term.rdf_term=
  RDF_Term.T_BNode "hdt-decode-error"
let hdt_decode_term (gs : hdt_graph_store) (role : HDT_Dictionary.hdt_role)
  (id : hdt_term_ref) : RDF_Term.rdf_term FStar_Pervasives_Native.option=
  if id = Prims.int_zero
  then FStar_Pervasives_Native.None
  else HDT_Dictionary.hdt_id_to_term gs.hgs_hex gs.hgs_inventory role id
let hdt_decode_subject (gs : hdt_graph_store) (id : hdt_term_ref) :
  RDF_Term.subject=
  match hdt_decode_term gs HDT_Dictionary.Role_Subject id with
  | FStar_Pervasives_Native.None -> hdt_decode_error_subject
  | FStar_Pervasives_Native.Some t ->
      (match RDF_Graph.term_to_subject t with
       | FStar_Pervasives_Native.Some s -> s
       | FStar_Pervasives_Native.None -> hdt_decode_error_subject)
let hdt_decode_predicate (gs : hdt_graph_store) (id : hdt_term_ref) :
  RDF_Term.wf_iri=
  match hdt_decode_term gs HDT_Dictionary.Role_Predicate id with
  | FStar_Pervasives_Native.Some (RDF_Term.T_IRI i) -> i
  | uu___ -> hdt_decode_error_iri
let hdt_decode_object (gs : hdt_graph_store) (id : hdt_term_ref) :
  RDF_Term.rdf_term=
  match hdt_decode_term gs HDT_Dictionary.Role_Object id with
  | FStar_Pervasives_Native.Some t -> t
  | FStar_Pervasives_Native.None -> hdt_decode_error_object
type hdt_access_path =
  | HAP_BoundSubject of Prims.pos 
  | HAP_FullScan 
let uu___is_HAP_BoundSubject (projectee : hdt_access_path) : Prims.bool=
  match projectee with | HAP_BoundSubject _0 -> true | uu___ -> false
let __proj__HAP_BoundSubject__item___0 (projectee : hdt_access_path) :
  Prims.pos= match projectee with | HAP_BoundSubject _0 -> _0
let uu___is_HAP_FullScan (projectee : hdt_access_path) : Prims.bool=
  match projectee with | HAP_FullScan -> true | uu___ -> false
let hdt_choose_access_path (bound : hdt_bound_tp) : hdt_access_path=
  match bound.hbt_s with
  | FStar_Pervasives_Native.None -> HAP_FullScan
  | FStar_Pervasives_Native.Some sid ->
      if sid > Prims.int_zero then HAP_BoundSubject sid else HAP_FullScan
let hdt_resolve_access_path (gs : hdt_graph_store) (path : hdt_access_path) :
  HDT_Triples.hdt_id_triple Prims.list FStar_Pervasives_Native.option=
  match path with
  | HAP_FullScan -> HDT_Triples.hdt_enumerate_all gs.hgs_hex gs.hgs_triples
  | HAP_BoundSubject sid ->
      (match HDT_Triples.hdt_triples_for_subject gs.hgs_hex gs.hgs_triples
               sid
       with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some pairs ->
           FStar_Pervasives_Native.Some
             (FStar_List_Tot_Base.map
                (fun po ->
                   let uu___ = po in
                   match uu___ with
                   | (p, o) ->
                       {
                         HDT_Triples.it_s = sid;
                         HDT_Triples.it_p = p;
                         HDT_Triples.it_o = o
                       }) pairs))
let hdt_id_triple_matches (bound : hdt_bound_tp)
  (t : HDT_Triples.hdt_id_triple) : Prims.bool=
  ((match bound.hbt_s with
    | FStar_Pervasives_Native.None -> true
    | FStar_Pervasives_Native.Some sid -> t.HDT_Triples.it_s = sid) &&
     (match bound.hbt_p with
      | FStar_Pervasives_Native.None -> true
      | FStar_Pervasives_Native.Some pid -> t.HDT_Triples.it_p = pid))
    &&
    (match bound.hbt_o with
     | FStar_Pervasives_Native.None -> true
     | FStar_Pervasives_Native.Some oid -> t.HDT_Triples.it_o = oid)
let hdt_id_triple_to_row (t : HDT_Triples.hdt_id_triple) : hdt_tp_row=
  {
    hrow_s = (FStar_Pervasives_Native.Some (t.HDT_Triples.it_s));
    hrow_p = (FStar_Pervasives_Native.Some (t.HDT_Triples.it_p));
    hrow_o = (FStar_Pervasives_Native.Some (t.HDT_Triples.it_o))
  }
let hdt_search (gs : hdt_graph_store) (bound : hdt_bound_tp) :
  hdt_tp_row Prims.list=
  match hdt_resolve_access_path gs (hdt_choose_access_path bound) with
  | FStar_Pervasives_Native.None -> []
  | FStar_Pervasives_Native.Some triples ->
      FStar_List_Tot_Base.map hdt_id_triple_to_row
        (FStar_List_Tot_Base.filter (hdt_id_triple_matches bound) triples)
let hdt_estimate (gs : hdt_graph_store) (bound : hdt_bound_tp) : Prims.nat=
  FStar_List_Tot_Base.length (hdt_search gs bound)
let hdt_predicate_present (gs : hdt_graph_store) (pred : RDF_Term.wf_iri) :
  Prims.bool=
  match hdt_encode_predicate gs pred with
  | FStar_Pervasives_Native.None -> false
  | FStar_Pervasives_Native.Some pid ->
      Prims.op_Negation
        ((FStar_List_Tot_Base.length
            (hdt_search gs
               {
                 hbt_s = FStar_Pervasives_Native.None;
                 hbt_p = (FStar_Pervasives_Native.Some pid);
                 hbt_o = FStar_Pervasives_Native.None
               }))
           = Prims.int_zero)
let hdt_named_candidate_graphs (bindings : corpus_graph_binding Prims.list)
  (predicate_hint : RDF_Term.wf_iri FStar_Pervasives_Native.option) :
  corpus_graph_binding Prims.list= bindings
let hdt_build_bound_tp (gs : hdt_graph_store)
  (s : RDF_Term.subject FStar_Pervasives_Native.option)
  (p : RDF_Term.wf_iri FStar_Pervasives_Native.option)
  (o : RDF_Term.rdf_term FStar_Pervasives_Native.option) : hdt_bound_tp=
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
  RDF_Triple.triple FStar_Pervasives_Native.option=
  match ((row.hrow_s), (row.hrow_p), (row.hrow_o)) with
  | (FStar_Pervasives_Native.Some sr, FStar_Pervasives_Native.Some pr,
     FStar_Pervasives_Native.Some orf) ->
      FStar_Pervasives_Native.Some
        {
          RDF_Triple.s = (hdt_decode_subject gs sr);
          RDF_Triple.p = (hdt_decode_predicate gs pr);
          RDF_Triple.o = (hdt_decode_object gs orf)
        }
  | uu___ -> FStar_Pervasives_Native.None
let rec hdt_rows_to_triples (gs : hdt_graph_store)
  (rows : hdt_tp_row Prims.list) : RDF_Triple.triple Prims.list=
  match rows with
  | [] -> []
  | row::rest ->
      let rest' = hdt_rows_to_triples gs rest in
      (match hdt_row_to_triple gs row with
       | FStar_Pervasives_Native.Some t -> t :: rest'
       | FStar_Pervasives_Native.None -> rest')
let hdt_search_triples (gs : hdt_graph_store)
  (s : RDF_Term.subject FStar_Pervasives_Native.option)
  (p : RDF_Term.wf_iri FStar_Pervasives_Native.option)
  (o : RDF_Term.rdf_term FStar_Pervasives_Native.option) :
  RDF_Triple.triple Prims.list=
  let bound = hdt_build_bound_tp gs s p o in
  hdt_rows_to_triples gs (hdt_search gs bound)
