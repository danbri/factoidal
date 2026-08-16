module Parser.BallyhooCOTTAS

open RDF.Graph.Executable
open FStar.List.Tot

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

// Graph-column bound for a query pattern against a COTTAS-shaped quad
// store (issue #267). Three explicit states, not the previous
// `option cottas_graph_ref`, which conflated "no constraint on the
// graph column" with "the caller means the default graph" — for the
// on-disk backend that conflation let a plain BGP over the default
// graph union in every named graph's rows too (see
// RDF.CottasStore.cottas_ondisk_build_bound_qp_opt /
// SPARQL11.Store.GB_CottasOnDisk).
//   - CGB_Unbound : no constraint; any row (default or named) matches.
//     Not produced by the on-disk backend post-#267 — kept for the
//     in-memory `cottas_dataset_store` / GB_COTTAS path below, which
//     has no live constructor today (dead code; SPARQL11.Store.fst
//     never builds a `GB_COTTAS`).
//   - CGB_Default : row must be a default-graph row (the on-disk
//     "DEFAULT" sentinel token, docs/cottas-format-v1.md section 6).
//   - CGB_Named r : row must belong to the named graph whose
//     dictionary ref is `r`.
type cottas_graph_bound =
  | CGB_Unbound : cottas_graph_bound
  | CGB_Default : cottas_graph_bound
  | CGB_Named   : cottas_graph_ref -> cottas_graph_bound

noeq type cottas_bound_qp = {
  cbqp_s : option cottas_term_ref;
  cbqp_p : option cottas_term_ref;
  cbqp_o : option cottas_term_ref;
  cbqp_g : cottas_graph_bound;
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

// Lifted (#448 wave 2, module 1): the OCaml realisation in
// experimental_ocaml_glue/cottas_runtime.sh was a plain linear scan over
// cottas_named_graphs matching on cngs_name -- pure list search with no I/O
// of its own. Expressed directly here so the F*-extracted body is what
// actually runs (the glue's former duplicate copy was removed to match).
let cottas_lookup_named_graph (ds : cottas_dataset_store) (name : iri)
  : Tot (option cottas_named_graph_store) =
  match find (fun ng -> ng.cngs_name = name) (cottas_named_graphs ds) with
  | None -> None
  | Some ng -> Some ng

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

// Lifted (#448 wave 2, module 1): the OCaml realisation was exactly
// `List.length (cottas_search ds bound)` -- i.e. "estimate" was already an
// EXACT count, not a heuristic, but that invariant lived only in the glue
// script's implementation, unstated in the assumed signature. Expressing it
// here makes every F* caller of cottas_estimate prove against the real
// relationship to cottas_search instead of an opaque nat.
let cottas_estimate (ds : cottas_dataset_store) (bound : cottas_bound_qp)
  : Tot nat =
  length (cottas_search ds bound)

// Lifted (#448 wave 2, module 1): the OCaml realisation was a pure
// derivation of cottas_encode_predicate + cottas_estimate -- "present"
// means "encodes to a known predicate ref AND at least one row matches
// it in this named graph" -- with no I/O beyond what those two already
// perform. Stating it here makes the presence/count relationship
// explicit instead of leaving it implicit in unassuming glue code.
let cottas_predicate_present_in_graph (ng : cottas_named_graph_store)
  (pred : wf_iri)
  : Tot bool =
  match cottas_encode_predicate ng.cngs_dataset pred with
  | None -> false
  | Some pred_ref ->
    cottas_estimate ng.cngs_dataset {
      cbqp_s = None;
      cbqp_p = Some pred_ref;
      cbqp_o = None;
      cbqp_g = CGB_Named ng.cngs_ref;
    } > 0

// Lifted (#448 wave 2, module 1): the OCaml realisation was exactly
// `filter (predicate_present_in_graph pred) (named_graphs ds)` -- a pure
// filter over cottas_named_graphs with no I/O of its own.
let cottas_graph_candidates_for_predicate (ds : cottas_dataset_store)
  (pred : wf_iri)
  : Tot (list cottas_named_graph_store) =
  filter (fun ng -> cottas_predicate_present_in_graph ng pred)
    (cottas_named_graphs ds)

let cottas_build_bound_qp (ds : cottas_dataset_store)
  (s : option subject) (p : option wf_iri) (o : option rdf_term) (g : option iri)
  : cottas_bound_qp =
  {
    cbqp_s = (match s with | None -> None | Some sv -> cottas_encode_subject ds sv);
    cbqp_p = (match p with | None -> None | Some pv -> cottas_encode_predicate ds pv);
    cbqp_o = (match o with | None -> None | Some ov -> cottas_encode_object ds ov);
    // Dead-code path (no live GB_COTTAS constructor exists — see
    // SPARQL11.Store.fst); preserved behaviour: no graph IRI given, or
    // the given IRI isn't in this corpus's dictionary, both mean
    // "no constraint" rather than "definitively empty," same as the
    // pre-#267 shape. The on-disk backend below (cottas_ondisk_build_bound_qp_opt
    // in RDF.CottasStore.fst) is the fixed, live path.
    cbqp_g = (match g with
      | None -> CGB_Unbound
      | Some gv ->
        (match cottas_encode_graph_name ds gv with
         | None -> CGB_Unbound
         | Some r -> CGB_Named r));
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

// On-disk COTTAS types and operations have moved to RDF.CottasStore.
// This module retains only the older eager-load `cottas_dataset_store`
// path. See RDF.CottasStore for the on-disk handle and the 11 lookup
// functions lifted to F* in issue #100 Phase A.
