module Parser.BallyhooHDTQ

open RDF.Graph.Executable
open Parser.BallyhooHDT
open FStar.List.Tot

// BallyhooHDTQ is the quad/dataset companion to BallyhooHDT.
// It does not yet parse HDTQ bytes directly, but it fixes the intended
// F* representation and backend boundary for quad-aware physical stores.
// The goal is to let the SPARQL dataset layer target a native dataset store
// rather than pretending all named-graph semantics must be reconstructed from
// ad hoc manifests forever.
//
// #448 wave 2, module 2 audit note: as of this pass, this module is
// SCAFFOLD ONLY — no SPARQL11.Store.fst arm, CLI path, or any other
// .fst builds an hdtq_dataset_store, and no experimental_ocaml_glue/
// script realises any hdtq_* assume val (grep for "hdtq_" in that
// directory returns nothing). Every remaining assume val below
// therefore extracts as a raw `failwith "Not yet implemented: ..."`
// stub with one exception: hdtq_close_dataset_store (Tot unit,
// unreferenced) extracts to NO symbol at all — F*'s codegen elides an
// unused, unrealised, unit-returning assume val rather than emitting
// a stub for it (contrast Parser.BallyhooHDT's *defined*
// hdt_close_graph_store, also `= ()` and also absent from its .ml for
// the same reason). If this module is ever wired up, that one call
// would be a link-time "unbound value" error, not a runtime failwith
// — worth knowing before treating "compiles" as "reachable code has a
// realisation."
//
// Despite `open Parser.BallyhooHDT` above, this module does not
// call any BallyhooHDT function (hdt_open_graph_store, hdt_search,
// hdt_encode_*, hdt_decode_*, ...) — only its *types*
// (hdt_term_ref, hdt_artifact_summary, corpus_graph_binding) are
// reused. BallyhooHDT itself carries zero assume vals as of stage 4
// (2026-07-06 program plan) and needs no further wave-2 pass; the
// open question this audit surfaces is the inverse one — whether a
// future HDTQ realisation should compose BallyhooHDT's already-
// verified per-graph reader (one hdt_graph_store per named graph) or
// target a real multi-graph HDTQ binary format directly. That design
// choice is out of scope for an assume-val audit and is left for
// whichever issue wires this module up.

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

// Kept assumed (I/O boundary), matching cottas_close_dataset_store's
// classification in the #448 wave 2 module 1 audit — a resource
// teardown call is conceptually a host effect regardless of whether
// today's (nonexistent) realisation happens to be a no-op. See the
// module-header note above: this one has no extracted symbol at all
// today, unlike its COTTAS counterpart.
assume val hdtq_close_dataset_store :
  hdtq_dataset_store -> Tot unit

// Kept assumed, NOT lifted to `ds.hqds_summary`, even though the
// record already carries that exact field. Reason (mirrors
// cottas_dataset_summary's #448 wave 2 module 1 disposition): COTTAS's
// realisation routes this call through a live, path-keyed runtime
// cache (`cache_for_store`) rather than the record field, because the
// record's `_summary` field is a snapshot taken at open time and the
// live cache is the thing a real backend would refresh from disk. A
// pure `ds.hqds_summary` projection would be correct today (no
// backend exists to disagree with it) but would silently commit this
// module to "the open-time snapshot is authoritative forever," which
// contradicts the sibling module's own choice on an identical field
// shape. Left assumed so a future realisation is free to choose
// either semantics without an F*-level lift fighting it.
assume val hdtq_dataset_summary :
  hdtq_dataset_store -> Tot (option hdtq_artifact_summary)

assume val hdtq_named_graphs :
  hdtq_dataset_store -> Tot (list hdtq_named_graph_store)

// Lifted (#448 wave 2, module 2): this module carries no OCaml glue at
// all today (`hdtq_*` has zero matches in experimental_ocaml_glue/ —
// every function below extracted as a raw `failwith "Not yet
// implemented"` stub prior to this audit), so there was no existing
// realisation whose behaviour to preserve. But the shape is a pure
// linear scan over hdtq_named_graphs matching on hqng_name, exactly
// the derivation the sibling COTTAS audit found for
// cottas_lookup_named_graph — expressed directly here for the same
// reason: the F*-extracted body is then what actually runs instead of
// an opaque assumed lookup.
let hdtq_lookup_named_graph (ds : hdtq_dataset_store) (name : iri)
  : Tot (option hdtq_named_graph_store) =
  match find (fun ng -> ng.hqng_name = name) (hdtq_named_graphs ds) with
  | None -> None
  | Some ng -> Some ng

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

// Lifted (#448 wave 2, module 2): same reasoning as
// cottas_estimate — "estimate" is exactly the length of the exact
// row list hdtq_search already computes, not an independent
// heuristic. Stating it here makes every F* caller of hdtq_estimate
// prove against the real relationship to hdtq_search instead of an
// opaque nat that a future glue realisation could silently decouple
// from hdtq_search's actual result count.
let hdtq_estimate (ds : hdtq_dataset_store) (bound : hdtq_bound_qp)
  : Tot nat =
  length (hdtq_search ds bound)

// Lifted (#448 wave 2, module 2): pure derivation of
// hdtq_encode_predicate + hdtq_estimate — "present" means "encodes to
// a known predicate ref AND at least one row matches it, scoped to
// this named graph via hqbp_g." Same shape as
// cottas_predicate_present_in_graph, simplified because hdtq_bound_qp
// uses a plain `option hdtq_graph_ref` for hqbp_g rather than
// COTTAS's three-state CGB_Unbound/CGB_Default/CGB_Named
// (`cottas_graph_bound`) — HDTQ has no separate default-graph
// sentinel to distinguish, so `Some ng.hqng_ref` is the whole
// encoding.
let hdtq_predicate_present_in_graph (ng : hdtq_named_graph_store)
  (pred : wf_iri)
  : Tot bool =
  match hdtq_encode_predicate ng.hqng_dataset pred with
  | None -> false
  | Some pred_ref ->
    hdtq_estimate ng.hqng_dataset {
      hqbp_s = None;
      hqbp_p = Some pred_ref;
      hqbp_o = None;
      hqbp_g = Some ng.hqng_ref;
    } > 0

// Lifted (#448 wave 2, module 2): pure filter over hdtq_named_graphs
// using hdtq_predicate_present_in_graph, with no I/O of its own — same
// shape as cottas_graph_candidates_for_predicate.
let hdtq_graph_candidates_for_predicate (ds : hdtq_dataset_store)
  (pred : wf_iri)
  : Tot (list hdtq_named_graph_store) =
  filter (fun ng -> hdtq_predicate_present_in_graph ng pred)
    (hdtq_named_graphs ds)

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
