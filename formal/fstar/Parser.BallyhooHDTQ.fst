module Parser.BallyhooHDTQ

open RDF.Graph.Executable
open Parser.BallyhooHDT

// BallyhooHDTQ is the quad/dataset companion to BallyhooHDT.
// It does not yet parse HDTQ bytes directly, but it fixes the intended
// F* representation and backend boundary for quad-aware physical stores.
// The goal is to let the SPARQL dataset layer target a native dataset store
// rather than pretending all named-graph semantics must be reconstructed from
// ad hoc manifests forever.

type hdtq_annotation_mode =
  | HQ_AnnotatedGraphs
  | HQ_AnnotatedTriples

noeq type hdtq_graph_dictionary_summary = {
  hgds_num_graphs : nat;
  hgds_size_strings : nat;
}

noeq type hdtq_quad_info_summary = {
  hqis_num_quads : nat;
  hqis_annotation_mode : hdtq_annotation_mode;
}

noeq type hdtq_artifact_summary = {
  hqas_hdt : hdt_artifact_summary;
  hqas_graph_dictionary : hdtq_graph_dictionary_summary;
  hqas_quad_info : hdtq_quad_info_summary;
}

assume type hdtq_handle
type hdtq_graph_ref = nat

noeq type hdtq_bound_qp = {
  hqbp_s : option hdt_term_ref;
  hqbp_p : option hdt_term_ref;
  hqbp_o : option hdt_term_ref;
  hqbp_g : option hdtq_graph_ref;
}

noeq type hdtq_qp_row = {
  hqrow_s : option hdt_term_ref;
  hqrow_p : option hdt_term_ref;
  hqrow_o : option hdt_term_ref;
  hqrow_g : option hdtq_graph_ref;
}

noeq type hdtq_dataset_store = {
  hqds_artifact_path : string;
  hqds_summary : option hdtq_artifact_summary;
  hqds_handle : hdtq_handle;
}

noeq type hdtq_named_graph_store = {
  hqng_name : iri;
  hqng_ref : hdtq_graph_ref;
  hqng_dataset : hdtq_dataset_store;
}

assume val hdtq_open_dataset_store :
  artifact_path:string ->
  summary:option hdtq_artifact_summary ->
  Tot (option hdtq_dataset_store)

assume val hdtq_close_dataset_store :
  hdtq_dataset_store -> Tot unit

assume val hdtq_dataset_summary :
  hdtq_dataset_store -> Tot (option hdtq_artifact_summary)

assume val hdtq_named_graphs :
  hdtq_dataset_store -> Tot (list hdtq_named_graph_store)

assume val hdtq_lookup_named_graph :
  hdtq_dataset_store -> iri -> Tot (option hdtq_named_graph_store)

assume val hdtq_encode_subject :
  hdtq_dataset_store -> subject -> Tot (option hdt_term_ref)

assume val hdtq_encode_predicate :
  hdtq_dataset_store -> wf_iri -> Tot (option hdt_term_ref)

assume val hdtq_encode_object :
  hdtq_dataset_store -> rdf_term -> Tot (option hdt_term_ref)

assume val hdtq_encode_graph_name :
  hdtq_dataset_store -> iri -> Tot (option hdtq_graph_ref)

assume val hdtq_decode_subject :
  hdtq_dataset_store -> hdt_term_ref -> Tot subject

assume val hdtq_decode_predicate :
  hdtq_dataset_store -> hdt_term_ref -> Tot wf_iri

assume val hdtq_decode_object :
  hdtq_dataset_store -> hdt_term_ref -> Tot rdf_term

assume val hdtq_decode_graph_name :
  hdtq_dataset_store -> hdtq_graph_ref -> Tot iri

assume val hdtq_search :
  hdtq_dataset_store -> hdtq_bound_qp -> Tot (list hdtq_qp_row)

assume val hdtq_estimate :
  hdtq_dataset_store -> hdtq_bound_qp -> Tot nat

assume val hdtq_predicate_present_in_graph :
  hdtq_named_graph_store -> wf_iri -> Tot bool

assume val hdtq_graph_candidates_for_predicate :
  hdtq_dataset_store -> wf_iri -> Tot (list hdtq_named_graph_store)

let hdtq_build_bound_qp (ds : hdtq_dataset_store)
  (s : option subject) (p : option wf_iri) (o : option rdf_term) (g : option iri)
  : hdtq_bound_qp =
  {
    hqbp_s =
      (match s with
       | None -> None
       | Some sv -> hdtq_encode_subject ds sv);
    hqbp_p =
      (match p with
       | None -> None
       | Some pv -> hdtq_encode_predicate ds pv);
    hqbp_o =
      (match o with
       | None -> None
       | Some ov -> hdtq_encode_object ds ov);
    hqbp_g =
      (match g with
       | None -> None
       | Some gv -> hdtq_encode_graph_name ds gv);
  }

let hdtq_row_to_quad (ds : hdtq_dataset_store) (row : hdtq_qp_row)
  : option (triple & option iri) =
  match row.hqrow_s, row.hqrow_p, row.hqrow_o with
  | Some sr, Some pr, Some orf ->
    Some
      ({
        s = hdtq_decode_subject ds sr;
        p = hdtq_decode_predicate ds pr;
        o = hdtq_decode_object ds orf;
      },
       (match row.hqrow_g with
        | None -> None
        | Some gr -> Some (hdtq_decode_graph_name ds gr)))
  | _ -> None

let rec hdtq_rows_to_quads (ds : hdtq_dataset_store) (rows : list hdtq_qp_row)
  : Tot (list (triple & option iri)) (decreases rows) =
  match rows with
  | [] -> []
  | row :: rest ->
    let rest' = hdtq_rows_to_quads ds rest in
    match hdtq_row_to_quad ds row with
    | Some q -> q :: rest'
    | None -> rest'

let rec hdtq_named_graphs_to_bindings (ngs : list hdtq_named_graph_store)
  : Tot (list corpus_graph_binding) (decreases ngs) =
  match ngs with
  | [] -> []
  | ng :: rest ->
    {
      cgb_graph_name = ng.hqng_name;
      cgb_artifact_path = ng.hqng_dataset.hqds_artifact_path;
      cgb_summary =
        (match ng.hqng_dataset.hqds_summary with
         | None -> None
         | Some s -> Some s.hqas_hdt);
    } :: hdtq_named_graphs_to_bindings rest
