module Parser.BallyhooHDT

open FStar.List.Tot
open RDF.Graph.Executable

module HC = HDT.Container
module HD = HDT.Dictionary
module HT = HDT.Triples

// BallyhooHDT is the store-boundary interface between the SPARQL
// evaluator's capability seam (SPARQL11.Store.fst's GB_HDT arm) and
// the verified HDT (Header-Dictionary-Triples) reader stages:
//   HDT.Container.fst  (stage 1 — container skeleton + section
//                        boundaries, CRC16-validated)
//   HDT.Dictionary.fst  (stage 2 — PFC dictionary decode, id<->term)
//   HDT.Triples.fst     (stage 3 — BitmapTriples SPO navigation)
//
// Stage 4 (docs/designissues/2026-07-06-hdt-program-plan.md) retires
// every assume val this module used to carry: this file previously
// shelled out to an external `hdtSearch` CLI via
// experimental_ocaml_glue/ballyhoo_hdt_runtime.sh (555 lines of
// unverified OCaml, the #253 debt). That runtime is deleted; every
// function below is ordinary Tot F* calling into stages 1-3. The
// ONLY I/O in the whole HDT reader is the file-content byte-range
// read `Parquet.Footer.parquet_read_range_hex` that stage 1 already
// reuses (HDT.Container.fst's own banner) — no HDT-specific assume
// val, no HDT-specific OCaml glue, per iron rule #11.
//
// (RDF.Store.LazyTermCache / RDF.Store.HDTTermCacheRegistry are an
// earlier, now-superseded attempt at an OCaml-side memoization layer
// for this same lookup; they are left in place, unused by the arms
// below, as the one HDT-adjacent OCaml the #253 plan flagged as
// rule-#11-acceptable if a future perf pass wants them. Stage 4 does
// not need them: `HDT.Dictionary.pfc_locate`/`pfc_extract` are
// O(log n) binary search over the PFC block heads, not a linear
// scan, so there is no correctness or big-O reason to reach for a
// cache at fixture scale — a stage-5 perf pass on corpus-scale HDT
// is the place to measure whether one earns its keep.)

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

// Term references are 1-based dictionary IDs in HDT.Dictionary's
// per-role ID space (Role_Subject / Role_Predicate / Role_Object);
// `0` is never a valid ID (HDT.Dictionary.pfc_extract/pfc_locate
// only ever return `pos`) and is used below as the "no such term"
// sentinel a total decode function must still return something for.
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

// The graph store's physical state: the hex-encoded file bytes plus
// the stage-1 container inventory and stage-3 triples-section
// inventory, both parsed once at open time. Every encode/decode/
// search call below is a pure function of this record — no mutable
// state, no external handle.
noeq type hdt_graph_store = {
  hgs_graph_name : option iri;
  hgs_artifact_path : string;
  hgs_summary : option hdt_artifact_summary;
  hgs_hex : string;
  hgs_inventory : HC.hdt_inventory;
  hgs_triples : HT.hdt_triples_info;
}

// ---------------------------------------------------------------------------
// Open/close/summary.
// ---------------------------------------------------------------------------

// Parse the container inventory (stage 1) and the triples section
// (stage 3) from `artifact_path`. `None` on any structural failure —
// wrong cookie, a CRC mismatch, truncation, or a non-PFC dictionary
// section — exactly the same loud-None contract
// `HC.hdt_read_inventory` / `HT.hdt_read_triples` already document.
let hdt_open_graph_store
  (graph_name : option iri)
  (artifact_path : string)
  (summary : option hdt_artifact_summary)
  : Tot (option hdt_graph_store) =
  match HC.hdt_read_inventory artifact_path with
  | None -> None
  | Some (hex, inv) ->
    (match HT.hdt_read_triples hex inv with
     | None -> None
     | Some triples ->
       Some {
         hgs_graph_name = graph_name;
         hgs_artifact_path = artifact_path;
         hgs_summary = summary;
         hgs_hex = hex;
         hgs_inventory = inv;
         hgs_triples = triples;
       })

// Nothing to release: the store is plain immutable data, and the
// underlying file bytes are cached process-wide by
// `Parquet.Footer`'s own OCaml realisation, keyed by path — not by
// anything this record owns.
let hdt_close_graph_store (gs : hdt_graph_store) : Tot unit = ()

let hdt_graph_summary (gs : hdt_graph_store) : Tot (option hdt_artifact_summary) =
  gs.hgs_summary

// ---------------------------------------------------------------------------
// Logical-to-physical term encoding — reverse dictionary lookup
// (HDT.Dictionary.pfc_locate, O(log n) binary search over PFC block
// heads) composed with the shared/subjects/objects ID-space
// arithmetic (HDT.Dictionary.hdt_term_to_id).
// ---------------------------------------------------------------------------

// `HD.hdt_term_to_id` returns `option pos`; the assume-val contract
// these functions used to carry is `option hdt_term_ref` (= option
// nat). Forgetting a refinement (pos -> nat) is always sound but F*
// still routes it through a subtyping VC, so the match+ascription
// below states it explicitly rather than relying on the checker to
// infer it through the `option` type constructor.
let opt_pos_to_ref (o : option pos) : Tot (option hdt_term_ref) =
  match o with
  | None -> None
  | Some (id : pos) -> Some (id <: hdt_term_ref)

let hdt_encode_subject (gs : hdt_graph_store) (subj : subject) : Tot (option hdt_term_ref) =
  opt_pos_to_ref (HD.hdt_term_to_id gs.hgs_hex gs.hgs_inventory HD.Role_Subject (subject_to_term subj))

let hdt_encode_predicate (gs : hdt_graph_store) (p : wf_iri) : Tot (option hdt_term_ref) =
  opt_pos_to_ref (HD.hdt_term_to_id gs.hgs_hex gs.hgs_inventory HD.Role_Predicate (T_IRI p))

let hdt_encode_object (gs : hdt_graph_store) (o : rdf_term) : Tot (option hdt_term_ref) =
  opt_pos_to_ref (HD.hdt_term_to_id gs.hgs_hex gs.hgs_inventory HD.Role_Object o)

// ---------------------------------------------------------------------------
// Physical-to-logical decoding — forward dictionary lookup
// (HDT.Dictionary.pfc_extract). Every caller in this module only
// ever passes an ID that came from a successful encode or from a
// stage-3 navigation result (both always valid IDs in `[1,
// hdt_role_max_id]`), so the `None`/id-0/wrong-shape branches below
// are unreachable in practice; they still need a total, well-typed
// value, since the assume-val contract these functions used to
// carry was `Tot subject` / `Tot wf_iri` / `Tot rdf_term`, not
// `Tot (option _)`.
// ---------------------------------------------------------------------------

let hdt_decode_error_iri : wf_iri =
  assert_norm (is_iri "urn:factoidal:hdt-decode-error");
  "urn:factoidal:hdt-decode-error"

let hdt_decode_error_subject : subject = S_BNode "hdt-decode-error"

let hdt_decode_error_object : rdf_term = T_BNode "hdt-decode-error"

let hdt_decode_term (gs : hdt_graph_store) (role : HD.hdt_role) (id : hdt_term_ref)
  : option rdf_term =
  if id = 0 then None
  else HD.hdt_id_to_term gs.hgs_hex gs.hgs_inventory role id

let hdt_decode_subject (gs : hdt_graph_store) (id : hdt_term_ref) : Tot subject =
  match hdt_decode_term gs HD.Role_Subject id with
  | None -> hdt_decode_error_subject
  | Some t ->
    (match term_to_subject t with
     | Some s -> s
     | None -> hdt_decode_error_subject)

let hdt_decode_predicate (gs : hdt_graph_store) (id : hdt_term_ref) : Tot wf_iri =
  match hdt_decode_term gs HD.Role_Predicate id with
  | Some (T_IRI i) -> i
  | _ -> hdt_decode_error_iri

let hdt_decode_object (gs : hdt_graph_store) (id : hdt_term_ref) : Tot rdf_term =
  match hdt_decode_term gs HD.Role_Object id with
  | Some t -> t
  | None -> hdt_decode_error_object

// ---------------------------------------------------------------------------
// The access-path decision (program-plan stage 4, "open decision 1":
// a lean HDT-shaped sibling ADT modeled on
// SPARQL.Plan.AccessPath.fst's `access_path`, NOT a generalisation of
// that COTTAS-specific ADT). Two alternatives, matching what
// HDT.Triples.fst actually offers: a bound subject gets the select-
// jump straight to its (predicate, object) pairs
// (`HT.hdt_triples_for_subject`); everything else — unbound,
// bound-P-only, bound-O-only, bound-PO — falls back to full
// enumeration (`HT.hdt_enumerate_all`) filtered post-hoc. Stage 5's
// indexed rank/select swap-in changes what `hdt_triples_for_subject`
// / `hdt_enumerate_all` cost, not this decision.
// ---------------------------------------------------------------------------

type hdt_access_path =
  | HAP_BoundSubject : pos -> hdt_access_path
  | HAP_FullScan : hdt_access_path

let hdt_choose_access_path (bound : hdt_bound_tp) : Tot hdt_access_path =
  match bound.hbt_s with
  | None -> HAP_FullScan
  | Some sid -> if sid > 0 then HAP_BoundSubject sid else HAP_FullScan

let hdt_resolve_access_path (gs : hdt_graph_store) (path : hdt_access_path)
  : Tot (option (list HT.hdt_id_triple)) =
  match path with
  | HAP_FullScan -> HT.hdt_enumerate_all gs.hgs_hex gs.hgs_triples
  | HAP_BoundSubject sid ->
    (match HT.hdt_triples_for_subject gs.hgs_hex gs.hgs_triples sid with
     | None -> None
     | Some pairs ->
       Some (List.Tot.map
         (fun (po : (nat & nat)) ->
           let (p, o) = po in
           ({ HT.it_s = sid; HT.it_p = p; HT.it_o = o } <: HT.hdt_id_triple))
         pairs))

let hdt_id_triple_matches (bound : hdt_bound_tp) (t : HT.hdt_id_triple) : Tot bool =
  (match bound.hbt_s with None -> true | Some sid -> t.HT.it_s = sid) &&
  (match bound.hbt_p with None -> true | Some pid -> t.HT.it_p = pid) &&
  (match bound.hbt_o with None -> true | Some oid -> t.HT.it_o = oid)

let hdt_id_triple_to_row (t : HT.hdt_id_triple) : Tot hdt_tp_row =
  { hrow_s = Some t.HT.it_s; hrow_p = Some t.HT.it_p; hrow_o = Some t.HT.it_o }

// ---------------------------------------------------------------------------
// Indexed triple-pattern access — the assume vals stage 4 retires.
// ---------------------------------------------------------------------------

let hdt_search (gs : hdt_graph_store) (bound : hdt_bound_tp) : Tot (list hdt_tp_row) =
  match hdt_resolve_access_path gs (hdt_choose_access_path bound) with
  | None -> []
  | Some triples ->
    List.Tot.map hdt_id_triple_to_row
      (List.Tot.filter (hdt_id_triple_matches bound) triples)

let hdt_estimate (gs : hdt_graph_store) (bound : hdt_bound_tp) : Tot nat =
  List.Tot.length (hdt_search gs bound)

// Dataset/corpus level routing hooks.
let hdt_predicate_present (gs : hdt_graph_store) (pred : wf_iri) : Tot bool =
  match hdt_encode_predicate gs pred with
  | None -> false
  | Some pid ->
    not (List.Tot.length
      (hdt_search gs { hbt_s = None; hbt_p = Some pid; hbt_o = None }) = 0)

// HDT is a single-graph (triples-only, no HDTQ) format per the
// program plan's scope; there is no per-graph predicate hint to
// filter candidates by, so every binding is always a candidate. Pure
// F* now (this used to be an `assume val`, but its only OCaml
// realisation was already the identity function regardless of
// `predicate_hint`, so there was never a real I/O or host-call
// boundary here).
let hdt_named_candidate_graphs (bindings : list corpus_graph_binding)
  (predicate_hint : option wf_iri)
  : Tot (list corpus_graph_binding) =
  bindings

// ---------------------------------------------------------------------------
// Bridge helpers for the SPARQL backend integration
// (SPARQL11.Store.fst's GB_HDT arm).
// ---------------------------------------------------------------------------

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
