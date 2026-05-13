open Prims
type cottas_encoding =
  | CE_Plain 
  | CE_Dictionary 
  | CE_RLE 
  | CE_Delta 
let uu___is_CE_Plain (projectee : cottas_encoding) : Prims.bool=
  match projectee with | CE_Plain -> true | uu___ -> false
let uu___is_CE_Dictionary (projectee : cottas_encoding) : Prims.bool=
  match projectee with | CE_Dictionary -> true | uu___ -> false
let uu___is_CE_RLE (projectee : cottas_encoding) : Prims.bool=
  match projectee with | CE_RLE -> true | uu___ -> false
let uu___is_CE_Delta (projectee : cottas_encoding) : Prims.bool=
  match projectee with | CE_Delta -> true | uu___ -> false
type cottas_column_kind =
  | CC_Subject 
  | CC_Predicate 
  | CC_Object 
  | CC_Graph 
let uu___is_CC_Subject (projectee : cottas_column_kind) : Prims.bool=
  match projectee with | CC_Subject -> true | uu___ -> false
let uu___is_CC_Predicate (projectee : cottas_column_kind) : Prims.bool=
  match projectee with | CC_Predicate -> true | uu___ -> false
let uu___is_CC_Object (projectee : cottas_column_kind) : Prims.bool=
  match projectee with | CC_Object -> true | uu___ -> false
let uu___is_CC_Graph (projectee : cottas_column_kind) : Prims.bool=
  match projectee with | CC_Graph -> true | uu___ -> false
type cottas_column_summary =
  {
  ccs_kind: cottas_column_kind ;
  ccs_num_values: Prims.nat ;
  ccs_null_count: Prims.nat ;
  ccs_encoding: cottas_encoding }
let __proj__Mkcottas_column_summary__item__ccs_kind
  (projectee : cottas_column_summary) : cottas_column_kind=
  match projectee with
  | { ccs_kind; ccs_num_values; ccs_null_count; ccs_encoding;_} -> ccs_kind
let __proj__Mkcottas_column_summary__item__ccs_num_values
  (projectee : cottas_column_summary) : Prims.nat=
  match projectee with
  | { ccs_kind; ccs_num_values; ccs_null_count; ccs_encoding;_} ->
      ccs_num_values
let __proj__Mkcottas_column_summary__item__ccs_null_count
  (projectee : cottas_column_summary) : Prims.nat=
  match projectee with
  | { ccs_kind; ccs_num_values; ccs_null_count; ccs_encoding;_} ->
      ccs_null_count
let __proj__Mkcottas_column_summary__item__ccs_encoding
  (projectee : cottas_column_summary) : cottas_encoding=
  match projectee with
  | { ccs_kind; ccs_num_values; ccs_null_count; ccs_encoding;_} ->
      ccs_encoding
type cottas_dictionary_summary =
  {
  cds_num_terms: Prims.nat ;
  cds_num_graphs: Prims.nat ;
  cds_bytes_strings: Prims.nat }
let __proj__Mkcottas_dictionary_summary__item__cds_num_terms
  (projectee : cottas_dictionary_summary) : Prims.nat=
  match projectee with
  | { cds_num_terms; cds_num_graphs; cds_bytes_strings;_} -> cds_num_terms
let __proj__Mkcottas_dictionary_summary__item__cds_num_graphs
  (projectee : cottas_dictionary_summary) : Prims.nat=
  match projectee with
  | { cds_num_terms; cds_num_graphs; cds_bytes_strings;_} -> cds_num_graphs
let __proj__Mkcottas_dictionary_summary__item__cds_bytes_strings
  (projectee : cottas_dictionary_summary) : Prims.nat=
  match projectee with
  | { cds_num_terms; cds_num_graphs; cds_bytes_strings;_} ->
      cds_bytes_strings
type cottas_row_group_summary =
  {
  crgs_index: Prims.nat ;
  crgs_num_rows: Prims.nat ;
  crgs_columns: cottas_column_summary Prims.list }
let __proj__Mkcottas_row_group_summary__item__crgs_index
  (projectee : cottas_row_group_summary) : Prims.nat=
  match projectee with
  | { crgs_index; crgs_num_rows; crgs_columns;_} -> crgs_index
let __proj__Mkcottas_row_group_summary__item__crgs_num_rows
  (projectee : cottas_row_group_summary) : Prims.nat=
  match projectee with
  | { crgs_index; crgs_num_rows; crgs_columns;_} -> crgs_num_rows
let __proj__Mkcottas_row_group_summary__item__crgs_columns
  (projectee : cottas_row_group_summary) : cottas_column_summary Prims.list=
  match projectee with
  | { crgs_index; crgs_num_rows; crgs_columns;_} -> crgs_columns
type cottas_artifact_summary =
  {
  cas_path: Prims.string ;
  cas_num_quads: Prims.nat ;
  cas_num_row_groups: Prims.nat ;
  cas_dictionary: cottas_dictionary_summary FStar_Pervasives_Native.option ;
  cas_row_groups: cottas_row_group_summary Prims.list }
let __proj__Mkcottas_artifact_summary__item__cas_path
  (projectee : cottas_artifact_summary) : Prims.string=
  match projectee with
  | { cas_path; cas_num_quads; cas_num_row_groups; cas_dictionary;
      cas_row_groups;_} -> cas_path
let __proj__Mkcottas_artifact_summary__item__cas_num_quads
  (projectee : cottas_artifact_summary) : Prims.nat=
  match projectee with
  | { cas_path; cas_num_quads; cas_num_row_groups; cas_dictionary;
      cas_row_groups;_} -> cas_num_quads
let __proj__Mkcottas_artifact_summary__item__cas_num_row_groups
  (projectee : cottas_artifact_summary) : Prims.nat=
  match projectee with
  | { cas_path; cas_num_quads; cas_num_row_groups; cas_dictionary;
      cas_row_groups;_} -> cas_num_row_groups
let __proj__Mkcottas_artifact_summary__item__cas_dictionary
  (projectee : cottas_artifact_summary) :
  cottas_dictionary_summary FStar_Pervasives_Native.option=
  match projectee with
  | { cas_path; cas_num_quads; cas_num_row_groups; cas_dictionary;
      cas_row_groups;_} -> cas_dictionary
let __proj__Mkcottas_artifact_summary__item__cas_row_groups
  (projectee : cottas_artifact_summary) :
  cottas_row_group_summary Prims.list=
  match projectee with
  | { cas_path; cas_num_quads; cas_num_row_groups; cas_dictionary;
      cas_row_groups;_} -> cas_row_groups
type cottas_handle = unit
type cottas_term_ref = Prims.nat
type cottas_graph_ref = Prims.nat
type cottas_bound_qp =
  {
  cbqp_s: cottas_term_ref FStar_Pervasives_Native.option ;
  cbqp_p: cottas_term_ref FStar_Pervasives_Native.option ;
  cbqp_o: cottas_term_ref FStar_Pervasives_Native.option ;
  cbqp_g: cottas_graph_ref FStar_Pervasives_Native.option }
let __proj__Mkcottas_bound_qp__item__cbqp_s (projectee : cottas_bound_qp) :
  cottas_term_ref FStar_Pervasives_Native.option=
  match projectee with | { cbqp_s; cbqp_p; cbqp_o; cbqp_g;_} -> cbqp_s
let __proj__Mkcottas_bound_qp__item__cbqp_p (projectee : cottas_bound_qp) :
  cottas_term_ref FStar_Pervasives_Native.option=
  match projectee with | { cbqp_s; cbqp_p; cbqp_o; cbqp_g;_} -> cbqp_p
let __proj__Mkcottas_bound_qp__item__cbqp_o (projectee : cottas_bound_qp) :
  cottas_term_ref FStar_Pervasives_Native.option=
  match projectee with | { cbqp_s; cbqp_p; cbqp_o; cbqp_g;_} -> cbqp_o
let __proj__Mkcottas_bound_qp__item__cbqp_g (projectee : cottas_bound_qp) :
  cottas_graph_ref FStar_Pervasives_Native.option=
  match projectee with | { cbqp_s; cbqp_p; cbqp_o; cbqp_g;_} -> cbqp_g
type cottas_qp_row =
  {
  cqpr_s: cottas_term_ref FStar_Pervasives_Native.option ;
  cqpr_p: cottas_term_ref FStar_Pervasives_Native.option ;
  cqpr_o: cottas_term_ref FStar_Pervasives_Native.option ;
  cqpr_g: cottas_graph_ref FStar_Pervasives_Native.option }
let __proj__Mkcottas_qp_row__item__cqpr_s (projectee : cottas_qp_row) :
  cottas_term_ref FStar_Pervasives_Native.option=
  match projectee with | { cqpr_s; cqpr_p; cqpr_o; cqpr_g;_} -> cqpr_s
let __proj__Mkcottas_qp_row__item__cqpr_p (projectee : cottas_qp_row) :
  cottas_term_ref FStar_Pervasives_Native.option=
  match projectee with | { cqpr_s; cqpr_p; cqpr_o; cqpr_g;_} -> cqpr_p
let __proj__Mkcottas_qp_row__item__cqpr_o (projectee : cottas_qp_row) :
  cottas_term_ref FStar_Pervasives_Native.option=
  match projectee with | { cqpr_s; cqpr_p; cqpr_o; cqpr_g;_} -> cqpr_o
let __proj__Mkcottas_qp_row__item__cqpr_g (projectee : cottas_qp_row) :
  cottas_graph_ref FStar_Pervasives_Native.option=
  match projectee with | { cqpr_s; cqpr_p; cqpr_o; cqpr_g;_} -> cqpr_g
type cottas_dataset_store =
  {
  cds_artifact_path: Prims.string ;
  cds_summary: cottas_artifact_summary FStar_Pervasives_Native.option ;
  cds_handle: cottas_handle }
let __proj__Mkcottas_dataset_store__item__cds_artifact_path
  (projectee : cottas_dataset_store) : Prims.string=
  match projectee with
  | { cds_artifact_path; cds_summary; cds_handle;_} -> cds_artifact_path
let __proj__Mkcottas_dataset_store__item__cds_summary
  (projectee : cottas_dataset_store) :
  cottas_artifact_summary FStar_Pervasives_Native.option=
  match projectee with
  | { cds_artifact_path; cds_summary; cds_handle;_} -> cds_summary
let __proj__Mkcottas_dataset_store__item__cds_handle
  (projectee : cottas_dataset_store) : cottas_handle=
  match projectee with
  | { cds_artifact_path; cds_summary; cds_handle;_} -> cds_handle
type cottas_named_graph_store =
  {
  cngs_name: RDF_Graph_Executable.iri ;
  cngs_ref: cottas_graph_ref ;
  cngs_dataset: cottas_dataset_store }
let __proj__Mkcottas_named_graph_store__item__cngs_name
  (projectee : cottas_named_graph_store) : RDF_Graph_Executable.iri=
  match projectee with | { cngs_name; cngs_ref; cngs_dataset;_} -> cngs_name
let __proj__Mkcottas_named_graph_store__item__cngs_ref
  (projectee : cottas_named_graph_store) : cottas_graph_ref=
  match projectee with | { cngs_name; cngs_ref; cngs_dataset;_} -> cngs_ref
let __proj__Mkcottas_named_graph_store__item__cngs_dataset
  (projectee : cottas_named_graph_store) : cottas_dataset_store=
  match projectee with
  | { cngs_name; cngs_ref; cngs_dataset;_} -> cngs_dataset
let cottas_open_dataset_store (artifact_path : Prims.string)
  (summary : cottas_artifact_summary FStar_Pervasives_Native.option) :
  cottas_dataset_store FStar_Pervasives_Native.option=
  failwith
    "Not yet implemented: Parser.BallyhooCOTTAS.cottas_open_dataset_store"
let cottas_dataset_summary (uu___ : cottas_dataset_store) :
  cottas_artifact_summary FStar_Pervasives_Native.option=
  failwith
    "Not yet implemented: Parser.BallyhooCOTTAS.cottas_dataset_summary"
let cottas_named_graphs (uu___ : cottas_dataset_store) :
  cottas_named_graph_store Prims.list=
  failwith "Not yet implemented: Parser.BallyhooCOTTAS.cottas_named_graphs"
let cottas_lookup_named_graph (uu___ : cottas_dataset_store)
  (uu___1 : RDF_Graph_Executable.iri) :
  cottas_named_graph_store FStar_Pervasives_Native.option=
  failwith
    "Not yet implemented: Parser.BallyhooCOTTAS.cottas_lookup_named_graph"
let cottas_encode_subject (uu___ : cottas_dataset_store)
  (uu___1 : RDF_Graph_Executable.subject) :
  cottas_term_ref FStar_Pervasives_Native.option=
  failwith "Not yet implemented: Parser.BallyhooCOTTAS.cottas_encode_subject"
let cottas_encode_predicate (uu___ : cottas_dataset_store)
  (uu___1 : RDF_Graph_Executable.wf_iri) :
  cottas_term_ref FStar_Pervasives_Native.option=
  failwith
    "Not yet implemented: Parser.BallyhooCOTTAS.cottas_encode_predicate"
let cottas_encode_object (uu___ : cottas_dataset_store)
  (uu___1 : RDF_Graph_Executable.rdf_term) :
  cottas_term_ref FStar_Pervasives_Native.option=
  failwith "Not yet implemented: Parser.BallyhooCOTTAS.cottas_encode_object"
let cottas_encode_graph_name (uu___ : cottas_dataset_store)
  (uu___1 : RDF_Graph_Executable.iri) :
  cottas_graph_ref FStar_Pervasives_Native.option=
  failwith
    "Not yet implemented: Parser.BallyhooCOTTAS.cottas_encode_graph_name"
let cottas_decode_subject (uu___ : cottas_dataset_store)
  (uu___1 : cottas_term_ref) : RDF_Graph_Executable.subject=
  failwith "Not yet implemented: Parser.BallyhooCOTTAS.cottas_decode_subject"
let cottas_decode_predicate (uu___ : cottas_dataset_store)
  (uu___1 : cottas_term_ref) : RDF_Graph_Executable.wf_iri=
  failwith
    "Not yet implemented: Parser.BallyhooCOTTAS.cottas_decode_predicate"
let cottas_decode_object (uu___ : cottas_dataset_store)
  (uu___1 : cottas_term_ref) : RDF_Graph_Executable.rdf_term=
  failwith "Not yet implemented: Parser.BallyhooCOTTAS.cottas_decode_object"
let cottas_decode_graph_name (uu___ : cottas_dataset_store)
  (uu___1 : cottas_graph_ref) : RDF_Graph_Executable.iri=
  failwith
    "Not yet implemented: Parser.BallyhooCOTTAS.cottas_decode_graph_name"
let cottas_search (uu___ : cottas_dataset_store) (uu___1 : cottas_bound_qp) :
  cottas_qp_row Prims.list=
  failwith "Not yet implemented: Parser.BallyhooCOTTAS.cottas_search"
let cottas_estimate (uu___ : cottas_dataset_store) (uu___1 : cottas_bound_qp)
  : Prims.nat=
  failwith "Not yet implemented: Parser.BallyhooCOTTAS.cottas_estimate"
let cottas_predicate_present_in_graph (uu___ : cottas_named_graph_store)
  (uu___1 : RDF_Graph_Executable.wf_iri) : Prims.bool=
  failwith
    "Not yet implemented: Parser.BallyhooCOTTAS.cottas_predicate_present_in_graph"
let cottas_graph_candidates_for_predicate (uu___ : cottas_dataset_store)
  (uu___1 : RDF_Graph_Executable.wf_iri) :
  cottas_named_graph_store Prims.list=
  failwith
    "Not yet implemented: Parser.BallyhooCOTTAS.cottas_graph_candidates_for_predicate"
let cottas_build_bound_qp (ds : cottas_dataset_store)
  (s : RDF_Graph_Executable.subject FStar_Pervasives_Native.option)
  (p : RDF_Graph_Executable.wf_iri FStar_Pervasives_Native.option)
  (o : RDF_Graph_Executable.rdf_term FStar_Pervasives_Native.option)
  (g : RDF_Graph_Executable.iri FStar_Pervasives_Native.option) :
  cottas_bound_qp=
  {
    cbqp_s =
      (match s with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some sv -> cottas_encode_subject ds sv);
    cbqp_p =
      (match p with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some pv -> cottas_encode_predicate ds pv);
    cbqp_o =
      (match o with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some ov -> cottas_encode_object ds ov);
    cbqp_g =
      (match g with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some gv -> cottas_encode_graph_name ds gv)
  }
let cottas_row_to_quad (ds : cottas_dataset_store) (row : cottas_qp_row) :
  (RDF_Graph_Executable.triple * RDF_Graph_Executable.iri
    FStar_Pervasives_Native.option) FStar_Pervasives_Native.option=
  match ((row.cqpr_s), (row.cqpr_p), (row.cqpr_o)) with
  | (FStar_Pervasives_Native.Some sr, FStar_Pervasives_Native.Some pr,
     FStar_Pervasives_Native.Some orf) ->
      FStar_Pervasives_Native.Some
        ({
           RDF_Graph_Executable.s = (cottas_decode_subject ds sr);
           RDF_Graph_Executable.p = (cottas_decode_predicate ds pr);
           RDF_Graph_Executable.o = (cottas_decode_object ds orf)
         },
          ((match row.cqpr_g with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some gr ->
                FStar_Pervasives_Native.Some (cottas_decode_graph_name ds gr))))
  | uu___ -> FStar_Pervasives_Native.None
let rec cottas_rows_to_quads (ds : cottas_dataset_store)
  (rows : cottas_qp_row Prims.list) :
  (RDF_Graph_Executable.triple * RDF_Graph_Executable.iri
    FStar_Pervasives_Native.option) Prims.list=
  match rows with
  | [] -> []
  | row::rest ->
      let rest' = cottas_rows_to_quads ds rest in
      (match cottas_row_to_quad ds row with
       | FStar_Pervasives_Native.Some q -> q :: rest'
       | FStar_Pervasives_Native.None -> rest')
