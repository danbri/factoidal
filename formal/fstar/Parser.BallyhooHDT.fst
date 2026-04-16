module Parser.BallyhooHDT

open RDF.Graph.Executable

// BallyhooHDT is an experimental storage/backend module.
// It does not replace the current parser stack and it does not yet provide a
// verified HDT binary parser. Its purpose is to reflect the intended HDT-backed
// graph-store boundary into F* so the SPARQL layer can target a real backend
// interface instead of assuming list-backed graphs forever.

type ballyhoo_order =
  | BO_SPO
  | BO_SOP
  | BO_PSO
  | BO_POS
  | BO_OSP
  | BO_OPS

noeq type hdt_control_info = {
  hci_format_iri : string;
  hci_length_hint : nat;
}

noeq type hdt_dictionary_summary = {
  hds_num_shared_subject_object : nat;
  hds_num_subjects : nat;
  hds_num_predicates : nat;
  hds_num_objects : nat;
  hds_size_strings : nat;
}

noeq type hdt_triples_summary = {
  hts_num_triples : nat;
  hts_order : ballyhoo_order;
}

noeq type hdt_statistics = {
  hs_hdt_size : nat;
  hs_original_size : nat;
}

noeq type hdt_artifact_summary = {
  has_source_iri : option iri;
  has_dictionary : hdt_dictionary_summary;
  has_triples : hdt_triples_summary;
  has_statistics : hdt_statistics;
}

noeq type corpus_graph_binding = {
  cgb_graph_name : iri;
  cgb_artifact_path : string;
  cgb_summary : option hdt_artifact_summary;
}

// Opaque physical handle and term references.
// The extracted backend may implement these using HDT libraries, mmap-backed
// readers, a sidecar process, or an in-memory indexed structure with HDT-like
// semantics.
assume type hdt_handle
type hdt_term_ref = nat

noeq type hdt_bound_tp = {
  hbt_s : option hdt_term_ref;
  hbt_p : option hdt_term_ref;
  hbt_o : option hdt_term_ref;
}

noeq type hdt_tp_row = {
  hrow_s : option hdt_term_ref;
  hrow_p : option hdt_term_ref;
  hrow_o : option hdt_term_ref;
}

noeq type hdt_graph_store = {
  hgs_graph_name : option iri;
  hgs_artifact_path : string;
  hgs_summary : option hdt_artifact_summary;
  hgs_handle : hdt_handle;
}

// Opening/closing and metadata inspection.
assume val hdt_open_graph_store :
  graph_name:option iri ->
  artifact_path:string ->
  summary:option hdt_artifact_summary ->
  Tot (option hdt_graph_store)

assume val hdt_close_graph_store :
  hdt_graph_store -> Tot unit

assume val hdt_graph_summary :
  hdt_graph_store -> Tot (option hdt_artifact_summary)

// Logical-to-physical term encoding.
assume val hdt_encode_subject :
  hdt_graph_store -> subject -> Tot (option hdt_term_ref)

assume val hdt_encode_predicate :
  hdt_graph_store -> wf_iri -> Tot (option hdt_term_ref)

assume val hdt_encode_object :
  hdt_graph_store -> rdf_term -> Tot (option hdt_term_ref)

// Physical-to-logical decoding.
assume val hdt_decode_subject :
  hdt_graph_store -> hdt_term_ref -> Tot subject

assume val hdt_decode_predicate :
  hdt_graph_store -> hdt_term_ref -> Tot wf_iri

assume val hdt_decode_object :
  hdt_graph_store -> hdt_term_ref -> Tot rdf_term

// Indexed triple-pattern access.
assume val hdt_search :
  hdt_graph_store -> hdt_bound_tp -> Tot (list hdt_tp_row)

assume val hdt_estimate :
  hdt_graph_store -> hdt_bound_tp -> Tot nat

// Dataset/corpus level routing hooks.
assume val hdt_predicate_present :
  hdt_graph_store -> wf_iri -> Tot bool

assume val hdt_named_candidate_graphs :
  bindings:list corpus_graph_binding ->
  predicate_hint:option wf_iri ->
  Tot (list corpus_graph_binding)

// Bridge helpers for future SPARQL backend integration.
let hdt_build_bound_tp (gs : hdt_graph_store)
  (s : option subject) (p : option wf_iri) (o : option rdf_term)
  : hdt_bound_tp =
  {
    hbt_s =
      (match s with
       | None -> None
       | Some sv -> hdt_encode_subject gs sv);
    hbt_p =
      (match p with
       | None -> None
       | Some pv -> hdt_encode_predicate gs pv);
    hbt_o =
      (match o with
       | None -> None
       | Some ov -> hdt_encode_object gs ov);
  }

let hdt_row_to_triple (gs : hdt_graph_store) (row : hdt_tp_row) : option triple =
  match row.hrow_s, row.hrow_p, row.hrow_o with
  | Some sr, Some pr, Some orf ->
    Some {
      s = hdt_decode_subject gs sr;
      p = hdt_decode_predicate gs pr;
      o = hdt_decode_object gs orf;
    }
  | _ -> None

let rec hdt_rows_to_triples (gs : hdt_graph_store) (rows : list hdt_tp_row)
  : Tot (list triple) (decreases rows) =
  match rows with
  | [] -> []
  | row :: rest ->
    let rest' = hdt_rows_to_triples gs rest in
    match hdt_row_to_triple gs row with
    | Some t -> t :: rest'
    | None -> rest'

let hdt_search_triples (gs : hdt_graph_store)
  (s : option subject) (p : option wf_iri) (o : option rdf_term)
  : list triple =
  let bound = hdt_build_bound_tp gs s p o in
  hdt_rows_to_triples gs (hdt_search gs bound)
