module Parser.BallyhooCOTTAS

open RDF.Graph.Executable

// BallyhooCOTTAS is the native F* model for a COTTAS-style columnar quad
// backend. The immediate goal is to represent the dataset/storage boundary in
// F*, not to depend on an external Python/Rust implementation as the source of
// truth.

type cottas_encoding =
  | CE_Plain
  | CE_Dictionary
  | CE_RLE
  | CE_Delta

type cottas_column_kind =
  | CC_Subject
  | CC_Predicate
  | CC_Object
  | CC_Graph

noeq type cottas_column_summary = {
  ccs_kind : cottas_column_kind;
  ccs_num_values : nat;
  ccs_null_count : nat;
  ccs_encoding : cottas_encoding;
}

noeq type cottas_dictionary_summary = {
  cds_num_terms : nat;
  cds_num_graphs : nat;
  cds_bytes_strings : nat;
}

noeq type cottas_row_group_summary = {
  crgs_index : nat;
  crgs_num_rows : nat;
  crgs_columns : list cottas_column_summary;
}

noeq type cottas_artifact_summary = {
  cas_path : string;
  cas_num_quads : nat;
  cas_num_row_groups : nat;
  cas_dictionary : option cottas_dictionary_summary;
  cas_row_groups : list cottas_row_group_summary;
}

assume type cottas_handle
type cottas_term_ref = nat
type cottas_graph_ref = nat

noeq type cottas_bound_qp = {
  cbqp_s : option cottas_term_ref;
  cbqp_p : option cottas_term_ref;
  cbqp_o : option cottas_term_ref;
  cbqp_g : option cottas_graph_ref;
}

noeq type cottas_qp_row = {
  cqpr_s : option cottas_term_ref;
  cqpr_p : option cottas_term_ref;
  cqpr_o : option cottas_term_ref;
  cqpr_g : option cottas_graph_ref;
}

noeq type cottas_dataset_store = {
  cds_artifact_path : string;
  cds_summary : option cottas_artifact_summary;
  cds_handle : cottas_handle;
}

noeq type cottas_named_graph_store = {
  cngs_name : iri;
  cngs_ref : cottas_graph_ref;
  cngs_dataset : cottas_dataset_store;
}

assume val cottas_open_dataset_store :
  artifact_path:string ->
  summary:option cottas_artifact_summary ->
  Tot (option cottas_dataset_store)

assume val cottas_close_dataset_store :
  cottas_dataset_store -> Tot unit

assume val cottas_dataset_summary :
  cottas_dataset_store -> Tot (option cottas_artifact_summary)

assume val cottas_named_graphs :
  cottas_dataset_store -> Tot (list cottas_named_graph_store)

assume val cottas_lookup_named_graph :
  cottas_dataset_store -> iri -> Tot (option cottas_named_graph_store)

assume val cottas_encode_subject :
  cottas_dataset_store -> subject -> Tot (option cottas_term_ref)

assume val cottas_encode_predicate :
  cottas_dataset_store -> wf_iri -> Tot (option cottas_term_ref)

assume val cottas_encode_object :
  cottas_dataset_store -> rdf_term -> Tot (option cottas_term_ref)

assume val cottas_encode_graph_name :
  cottas_dataset_store -> iri -> Tot (option cottas_graph_ref)

assume val cottas_decode_subject :
  cottas_dataset_store -> cottas_term_ref -> Tot subject

assume val cottas_decode_predicate :
  cottas_dataset_store -> cottas_term_ref -> Tot wf_iri

assume val cottas_decode_object :
  cottas_dataset_store -> cottas_term_ref -> Tot rdf_term

assume val cottas_decode_graph_name :
  cottas_dataset_store -> cottas_graph_ref -> Tot iri

assume val cottas_search :
  cottas_dataset_store -> cottas_bound_qp -> Tot (list cottas_qp_row)

assume val cottas_estimate :
  cottas_dataset_store -> cottas_bound_qp -> Tot nat

assume val cottas_predicate_present_in_graph :
  cottas_named_graph_store -> wf_iri -> Tot bool

assume val cottas_graph_candidates_for_predicate :
  cottas_dataset_store -> wf_iri -> Tot (list cottas_named_graph_store)

let cottas_build_bound_qp (ds : cottas_dataset_store)
  (s : option subject) (p : option wf_iri) (o : option rdf_term) (g : option iri)
  : cottas_bound_qp =
  {
    cbqp_s = (match s with | None -> None | Some sv -> cottas_encode_subject ds sv);
    cbqp_p = (match p with | None -> None | Some pv -> cottas_encode_predicate ds pv);
    cbqp_o = (match o with | None -> None | Some ov -> cottas_encode_object ds ov);
    cbqp_g = (match g with | None -> None | Some gv -> cottas_encode_graph_name ds gv);
  }

let cottas_row_to_quad (ds : cottas_dataset_store) (row : cottas_qp_row)
  : option (triple & option iri) =
  match row.cqpr_s, row.cqpr_p, row.cqpr_o with
  | Some sr, Some pr, Some orf ->
    Some
      ({
        s = cottas_decode_subject ds sr;
        p = cottas_decode_predicate ds pr;
        o = cottas_decode_object ds orf;
      },
       (match row.cqpr_g with
        | None -> None
        | Some gr -> Some (cottas_decode_graph_name ds gr)))
  | _ -> None

let rec cottas_rows_to_quads (ds : cottas_dataset_store) (rows : list cottas_qp_row)
  : Tot (list (triple & option iri)) (decreases rows) =
  match rows with
  | [] -> []
  | row :: rest ->
    let rest' = cottas_rows_to_quads ds rest in
    match cottas_row_to_quad ds row with
    | Some q -> q :: rest'
    | None -> rest'

(* ============================================================================
   On-disk COTTAS backend (issue #100 Phase 2).

   The cottas_dataset_store above holds a fully-materialised parsed-term cache
   in its OCaml runtime (subject_to_id, id_to_subject, ... hashtables, plus a
   `quads : quad_row list`). For multi-million-quad corpora that's hundreds
   of MB of parsed-term records held live for the lifetime of the server.

   The on-disk variant below represents the same data with:
     - per-column term-id arrays (dense int IDs, ~8 bytes per cell, 4 cols);
     - per-column id→string dictionaries (small: parliament has 232 distinct
       predicates, 908K subjects, 956K objects).
   Parsed RDF terms (`subject` / `wf_iri` / `rdf_term`) are decoded ONLY for
   rows that survive the term-id bound check, on-demand at query time. The
   "search" operation works entirely on integer IDs; the per-row
   `cottas_decode_*` calls happen after filtering.

   F* keeps the search algorithm; OCaml glue holds the term-id arrays and
   the id→string dictionaries (the abstract `cottas_ondisk_handle`).
   ============================================================================ *)

assume type cottas_ondisk_handle

noeq type cottas_ondisk_store = {
  cods_artifact_path : string;
  cods_summary : option cottas_artifact_summary;
  cods_handle : cottas_ondisk_handle;
}

(* Open a COTTAS file for on-disk querying. Decodes the four columns once
   into term-id arrays + id→string dictionaries; does NOT parse subject /
   predicate / object / graph terms. *)
assume val cottas_ondisk_open :
  artifact_path:string -> Tot (option cottas_ondisk_store)

assume val cottas_ondisk_close :
  cottas_ondisk_store -> Tot unit

assume val cottas_ondisk_summary :
  cottas_ondisk_store -> Tot (option cottas_artifact_summary)

(* Encode a bound triple-pattern term to its on-disk term-id, if present
   in the dictionary. Returns None when the term doesn't appear in this
   corpus at all — the caller should short-circuit to an empty result. *)
assume val cottas_ondisk_encode_subject :
  cottas_ondisk_store -> subject -> Tot (option cottas_term_ref)

assume val cottas_ondisk_encode_predicate :
  cottas_ondisk_store -> wf_iri -> Tot (option cottas_term_ref)

assume val cottas_ondisk_encode_object :
  cottas_ondisk_store -> rdf_term -> Tot (option cottas_term_ref)

assume val cottas_ondisk_encode_graph_name :
  cottas_ondisk_store -> iri -> Tot (option cottas_graph_ref)

(* On-demand decode of a term-id back to its parsed RDF term. The OCaml
   glue caches decoded terms in an LRU; repeated queries that hit the same
   subject/predicate/object pay one parse only. *)
assume val cottas_ondisk_decode_subject :
  cottas_ondisk_store -> cottas_term_ref -> Tot subject

assume val cottas_ondisk_decode_predicate :
  cottas_ondisk_store -> cottas_term_ref -> Tot wf_iri

assume val cottas_ondisk_decode_object :
  cottas_ondisk_store -> cottas_term_ref -> Tot rdf_term

assume val cottas_ondisk_decode_graph_name :
  cottas_ondisk_store -> cottas_graph_ref -> Tot iri

(* Search: walk the term-id arrays, comparing each row against the bound
   pattern. Returns the term-id rows that match — caller decodes terms
   on-demand for the surviving rows. *)
assume val cottas_ondisk_search :
  cottas_ondisk_store -> cottas_bound_qp -> Tot (list cottas_qp_row)

assume val cottas_ondisk_estimate :
  cottas_ondisk_store -> cottas_bound_qp -> Tot nat

assume val cottas_ondisk_predicate_present :
  cottas_ondisk_store -> wf_iri -> Tot bool

(* Distinct named graphs in this corpus, as (graph_iri, graph_ref) pairs.
   Used by GP_Graph dispatch when the graph is a variable. *)
assume val cottas_ondisk_named_graphs :
  cottas_ondisk_store -> Tot (list (iri & cottas_graph_ref))

(* Build a bound query-pattern from a triple-pattern + a graph-IRI bound
   (mirrors cottas_build_bound_qp but for the on-disk handle). Returns None
   when any bound term is absent from the dictionary, meaning a definitively
   empty result. *)
let cottas_ondisk_build_bound_qp_opt
  (ds : cottas_ondisk_store)
  (s : option subject) (p : option wf_iri) (o : option rdf_term) (g : option iri)
  : option cottas_bound_qp =
  let s' = match s with | None -> Some None | Some sv -> (match cottas_ondisk_encode_subject ds sv with | None -> None | Some r -> Some (Some r)) in
  let p' = match p with | None -> Some None | Some pv -> (match cottas_ondisk_encode_predicate ds pv with | None -> None | Some r -> Some (Some r)) in
  let o' = match o with | None -> Some None | Some ov -> (match cottas_ondisk_encode_object ds ov with | None -> None | Some r -> Some (Some r)) in
  let g' = match g with | None -> Some None | Some gv -> (match cottas_ondisk_encode_graph_name ds gv with | None -> None | Some r -> Some (Some r)) in
  match s', p', o', g' with
  | Some sb, Some pb, Some ob, Some gb ->
    Some { cbqp_s = sb; cbqp_p = pb; cbqp_o = ob; cbqp_g = gb }
  | _ -> None

(* Convert an on-disk term-id row to a parsed (triple & option iri).
   Returns None when the row is malformed (only when on-disk data is
   inconsistent — should not happen for well-formed COTTAS files). *)
let cottas_ondisk_row_to_quad (ds : cottas_ondisk_store) (row : cottas_qp_row)
  : option (triple & option iri) =
  match row.cqpr_s, row.cqpr_p, row.cqpr_o with
  | Some sr, Some pr, Some orf ->
    Some
      ({
        s = cottas_ondisk_decode_subject ds sr;
        p = cottas_ondisk_decode_predicate ds pr;
        o = cottas_ondisk_decode_object ds orf;
      },
       (match row.cqpr_g with
        | None -> None
        | Some gr -> Some (cottas_ondisk_decode_graph_name ds gr)))
  | _ -> None

let rec cottas_ondisk_rows_to_quads (ds : cottas_ondisk_store) (rows : list cottas_qp_row)
  : Tot (list (triple & option iri)) (decreases rows) =
  match rows with
  | [] -> []
  | row :: rest ->
    let rest' = cottas_ondisk_rows_to_quads ds rest in
    match cottas_ondisk_row_to_quad ds row with
    | Some q -> q :: rest'
    | None -> rest'
