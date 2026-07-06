module SPARQL11.Store

open FStar.All
open RDF.Graph.Executable
open SPARQL.FullText
open SPARQL11.Algebra
open Parser.BallyhooHDT
open Parser.BallyhooCOTTAS
open RDF.CottasStore
open RDF.Store.Capabilities
open RDF.Store.Capabilities.Cottas
open RDF.Store.Capabilities.Delta
open RML.VirtualSource

module Lh = RDF.List.Helpers
module DL = RDF.Store.Columnar.DeltaLog
module DM = RDF.Store.Columnar.DeltaMerge

// Note: this module previously imported Util.Log for in-line debug
// tracing in choose_best_tp_backend. Removed because F* erases
// Tot-unit-discarded calls regardless of how they're wrapped. The
// OCaml-side dry-runner in factoidal_explain.ml is the right place
// for explain-mode logging — it calls F*'s choose_best_tp_backend
// directly and logs each decision via Util_Log_runtime. The F*
// planner is the runtime path; the logging is glue.

// Backend-neutral store layer for SPARQL evaluation.
// The algebra remains the semantic source of truth; this module only dispatches
// physical triple-pattern access to specific backends.

noeq type graph_backend =
  | GB_List : rdf_graph -> graph_backend
  | GB_Indexed : indexed_graph -> graph_backend
  | GB_HDT : hdt_graph_store -> graph_backend
  | GB_COTTAS : cottas_dataset_store -> option iri -> graph_backend
  // issue #267: second field is a scope (DefaultOnly | NamedGraph iri),
  // not a plain `option iri` — see cottas_ondisk_dataset_backend below
  // and RDF.CottasStore.cottas_ondisk_graph_scope for why the old
  // `option iri` shape let the default-graph backend's `None` be
  // read as "no graph constraint" instead of "DEFAULT rows only."
  | GB_CottasOnDisk : cottas_ondisk_store -> cottas_ondisk_graph_scope -> graph_backend
  // Durable-UPDATE stage 3 (docs/designissues/2026-07-06-durable-update-
  // design.md, merge-on-read) / the D-overlay (2026-07-06-unified-
  // store-architecture.md §3.3): the SAME base COTTAS-on-disk store
  // and scope as GB_CottasOnDisk, plus an already-RESOLVED per-graph
  // delta (DM.delta_resolved — folded once at store-construction time,
  // see `cottas_with_delta_dataset_backend` below, not re-folded per
  // query). This is NOT a new backend in the sense §3.3 warns against —
  // its `caps_of_backend` arm below is one line, `overlay (caps_of_cottas
  // ...) delta`, delegating entirely to the existing COTTAS builder and
  // the D-overlay combinator. It exists as a `graph_backend` constructor
  // (rather than the seam's own `store`/`dataset` types) only because
  // `graph_backend`/`dataset_backend` are still what the CLI's
  // SELECT/ASK evaluator (`run_select_query_backend_dataset` et al.)
  // consumes pre-U4 — see this module's own caps_of_backend banner for
  // why `caps_of_backend` is the ONE dispatch point a new backend touches.
  | GB_CottasOnDiskDelta : cottas_ondisk_store -> cottas_ondisk_graph_scope -> DM.delta_resolved -> graph_backend
  | GB_Union : list graph_backend -> graph_backend
  // Virtual-sources Part B (docs/designissues/2026-07-06-virtual-
  // sources-design.md §3 / stage 5): a D2RQ/Ontop-style non-
  // materialized backend over an RML mapping + its already-read
  // source payloads. `caps_of_backend`'s arm below is one line,
  // `RML.VirtualSource.caps_of_rml_source rvs` — the whole pushdown
  // model (structural TriplesMap narrowing, row-level subject-template
  // pushdown, the default-graph-only v1 scope) lives in that module,
  // not here, same "one dispatch point" discipline every other
  // backend already follows.
  | GB_VirtualRML : RML.VirtualSource.rml_virtual_source -> graph_backend

noeq type named_graph_backend = {
  ngb_name : iri;
  ngb_graph : graph_backend;
}

noeq type dataset_backend = {
  dsb_default : graph_backend;
  dsb_named : list named_graph_backend;
}

(* list_graph_backend / list_dataset_backend wrappers were removed
   2026-05-16. All callers use the indexed_* variants below — same
   triples, faster lookup paths. *)

(* Wrap an rdf_graph as an indexed backend (issue #100 Phase 0). The
   index is built once at construction; subsequent backend_search calls
   on the same wrapper reuse the buckets. *)
let indexed_graph_backend (g : rdf_graph) : graph_backend =
  GB_Indexed (build_indexed g)

let indexed_dataset_backend (ds : rdf_dataset) : dataset_backend =
  {
    dsb_default = indexed_graph_backend ds.ds_default;
    dsb_named =
      List.Tot.map
        (fun (ng : named_graph) ->
          { ngb_name = ng.ng_name; ngb_graph = indexed_graph_backend ng.ng_graph })
        ds.ds_named
  }

(* 2026-07-06 (lazy per-bucket index construction): siblings of
   `indexed_graph_backend`/`indexed_dataset_backend` above that only
   build the buckets `needs` flags on (`RDF.Indexed.build_indexed_
   selective`) instead of always building all 6 (`build_indexed`). This
   is THE live path for a plain in-memory (no COTTAS/HDT) Turtle-loaded
   query — `factoidal_cli.ml`'s `build_dataset_backend` takes the
   `use_backend_exec` branch (entailment = "") for every SELECT/ASK, and
   that branch's `in_memory_backend` is exactly `indexed_dataset_backend`
   / `indexed_graph_backend` below (see that file's own banner). The
   6.3B-instruction `build_indexed` differential the decorate-sort-
   undecorate commit profiled (docs/designissues/2026-07-06-competitive-
   benchmark-results.md §7/§9) is paid HERE, once per query, for every
   SELECT/ASK regardless of whether the query's BGP ever calls
   `bucket_lookup` on the resulting buckets. `SPARQL11.Algebra
   .bucket_needs_of_pattern` computes a safe over-approximation of which
   buckets a query's own algebra tree can read (safety argument: RDF
   .Indexed.fsti's `bucket_needs` banner + `ig_search`'s `ig_built`-gated
   candidates, reused unchanged here since `caps_of_indexed` dispatches
   `sc_solve`/`sc_estimate` straight to `ig_search`/`ig_estimate`). *)
let indexed_graph_backend_for (needs : bucket_needs) (g : rdf_graph) : graph_backend =
  GB_Indexed (build_indexed_selective needs g)

let indexed_dataset_backend_for (needs : bucket_needs) (ds : rdf_dataset) : dataset_backend =
  {
    dsb_default = indexed_graph_backend_for needs ds.ds_default;
    dsb_named =
      List.Tot.map
        (fun (ng : named_graph) ->
          { ngb_name = ng.ng_name; ngb_graph = indexed_graph_backend_for needs ng.ng_graph })
        ds.ds_named
  }

(* Convenience entry point: derive `needs` from the query's own WHERE-
   clause pattern. This is the one `factoidal_cli.ml` calls. *)
let indexed_dataset_backend_for_query (p : group_graph_pattern) (ds : rdf_dataset) : dataset_backend =
  indexed_dataset_backend_for (bucket_needs_of_pattern p) ds

(* Build a dataset_backend whose default + named graphs all dispatch to
   the same on-disk COTTAS store, with named-graph dispatch using the
   stored graph IRI as the bound. The default graph is the COTTAS rows
   whose graph column carries the DEFAULT sentinel — modelled as
   `GB_CottasOnDisk _ COS_DefaultOnly` (issue #267: previously
   `GB_CottasOnDisk _ None`, which the bound layer read as "no graph
   constraint," unioning every named graph's rows into a plain
   default-graph BGP). Each named graph is a separate `GB_CottasOnDisk`
   filtering on its IRI via `COS_NamedGraph` (issue #100 Phase 2). *)
let cottas_ondisk_dataset_backend (cods : cottas_ondisk_store) : dataset_backend =
  {
    dsb_default = GB_CottasOnDisk cods COS_DefaultOnly;
    dsb_named =
      List.Tot.map
        (fun (g : (iri & cottas_graph_ref)) ->
          let (gname, _) = g in
          { ngb_name = gname; ngb_graph = GB_CottasOnDisk cods (COS_NamedGraph gname) })
        (cottas_ondisk_named_graphs cods)
  }

// ----------------------------------------------------------------------
// Durable-UPDATE stage 3 (merge-on-read) — the delta-aware store
// construction path (durable-update-design.md §5's staged table, row 3;
// unified-store-architecture.md §3.3's D-overlay). Loads a delta log
// (stage 2's already-wired ML assume vals + `DL.parse_log`, Tot),
// resolves it once per graph (`DM.fold_delta_batches`), and builds a
// `dataset_backend` whose every graph_backend is a `GB_CottasOnDiskDelta`
// — same shape as `cottas_ondisk_dataset_backend` above, plus the
// resolved delta threaded through `overlay`'s single dispatch arm.
//
// Named-graph discovery: a graph a delta CREATEs/ADDs into that the
// base COTTAS store has never seen (no rows for it at all) still needs
// a `dsb_named` entry — `DM.delta_batches_named_graphs` lists every
// graph IRI the delta mentions; any not already in the base's own
// `cottas_ondisk_named_graphs` gets a fresh `GB_CottasOnDiskDelta` whose
// base read side is simply empty for that graph (COS_NamedGraph on a
// name the base file carries no rows for is not an error — it's
// "empty base," exactly what a from-scratch named graph created purely
// by the delta log needs).
//
// `ML` because loading the log is I/O (`DL.delta_log_read_all`); every
// byte-format DECISION is `DL.parse_log`/`DM.fold_delta_batches`, both
// `Tot`, called from here as ordinary function calls (F* does not
// distinguish Tot-call-from-ML from ML-call-from-ML at the value level;
// the effect annotation only tracks what THIS function may itself do).
//
// Durable-UPDATE stage 4 (compaction, docs/designissues/2026-07-06-
// durable-update-design.md §3.3 step 5 / open decision 6):
// `compacted_epoch` is whatever `DL.parse_compacted_epoch` returned for
// the live base's `data.compacted-epoch` companion file (`None` if the
// store has never been compacted — the file doesn't exist, nothing to
// skip). Every parsed batch is filtered through
// `DL.filter_batches_since_epoch` BEFORE folding, so a delta log that
// still physically contains batches already folded into a compacted
// base (the crash window between a compaction's base-rename and its
// log-truncation, design doc §3.3 step 5) contributes nothing extra —
// this is the idempotent-replay guard, not an optimisation.
let cottas_with_delta_dataset_backend
    (cods : cottas_ondisk_store) (log_path : string) (compacted_epoch : option nat)
  : ML dataset_backend =
  let log_bytes = DL.delta_log_read_all log_path in
  let raw_batches = match DL.parse_log log_bytes with
    | Some (bs, _leftover) -> bs
    | None -> [] in
  let batches = DL.filter_batches_since_epoch compacted_epoch raw_batches in
  let base_named = cottas_ondisk_named_graphs cods in
  let default_delta = DM.fold_delta_batches batches None in
  let base_named_entries =
    List.Tot.map
      (fun (g : (iri & cottas_graph_ref)) ->
        let (gname, _) = g in
        let gdelta = DM.fold_delta_batches batches (Some gname) in
        { ngb_name = gname; ngb_graph = GB_CottasOnDiskDelta cods (COS_NamedGraph gname) gdelta })
      base_named
  in
  let base_names = List.Tot.map (fun (g : (iri & cottas_graph_ref)) -> fst g) base_named in
  let delta_only_names =
    List.Tot.filter
      (fun (gi : iri) -> not (List.Tot.existsb (fun (bn : iri) -> bn = gi) base_names))
      (DM.delta_batches_named_graphs batches)
  in
  let delta_only_entries =
    List.Tot.map
      (fun (gname : iri) ->
        let gdelta = DM.fold_delta_batches batches (Some gname) in
        { ngb_name = gname; ngb_graph = GB_CottasOnDiskDelta cods (COS_NamedGraph gname) gdelta })
      delta_only_names
  in
  {
    dsb_default = GB_CottasOnDiskDelta cods COS_DefaultOnly default_delta;
    dsb_named = List.Tot.append base_named_entries delta_only_entries;
  }

// Aleph6 (issue #100, demo prep): LIMIT-pushdown truncation helper.
// The COTTAS-on-disk backend stops walking once `limit` matched rows are
// accumulated (real pushdown, wired through caps_of_cottas below);
// non-disk backends fall back to this simple truncation since their
// search is already in-memory and cheap. Also used directly by
// eval_limit_single_tp further down.
let rec list_take_n (#a:Type) (n : nat) (xs : list a)
  : Tot (list a) (decreases n) =
  if n = 0 then []
  else
    match xs with
    | [] -> []
    | hd :: tl -> hd :: list_take_n (n - 1) tl

// ----------------------------------------------------------------------
// Stage U2 (docs/designissues/2026-07-06-unified-store-architecture.md):
// the six backend_* dispatchers below used to `match gb with` directly,
// one arm per graph_backend constructor, with a GB_Union recursion twin
// apiece (union_backend_search_acc, union_backend_search_limited_acc,
// union_backend_estimate, union_backend_count_exact,
// union_backend_predicate_present, union_backend_decode_failure — 12
// functions total, the design doc's §1.1 audit — now deleted, not
// commented out). `caps_of_backend` below is the ONE place that still
// consults the `graph_backend` tag: it builds a
// `RDF.Store.Capabilities.store_caps` record, dispatching on the
// constructor exactly once, and every backend_* function below becomes
// a one-line field projection through it.
//
// GB_Indexed and GB_CottasOnDisk reuse the U1 builders verbatim
// (`caps_of_indexed` / `caps_of_cottas`, RDF.Store.Capabilities[.Cottas]
// — design doc §3.1/§3.2). GB_List, GB_HDT, and the dead in-memory
// GB_COTTAS path (RDF.CottasStore.fst:1681 names it "the dead in-memory
// GB_COTTAS path" — no live construction site, same for GB_List, see
// the comment at `indexed_graph_backend` above) get their own inline
// builders here, because RDF.Store.Capabilities intentionally ships
// only the in-memory-via-RDF.Indexed and COTTAS-on-disk builders
// (keeping that module Unix/HDT/COTTAS-import-free per its own §6.2
// mitigation) — this module already imports Parser.BallyhooHDT /
// Parser.BallyhooCOTTAS / RDF.CottasStore, so it is the natural home
// for the three constructors the design doc didn't scope a builder for.
// GB_Union folds its members' caps through `union_caps` (§4 of the
// doc): the six union twins collapse into that one combinator plus the
// `caps_of_backend_list` structural-mapping helper below.
//
// Every field below is the EXACT same underlying call the old
// per-constructor match arm made — byte-identical behaviour, not a
// re-derivation. Where a field's realisation differs textually from
// the old arm (e.g. GB_List/GB_HDT/GB_COTTAS's sc_solve_limited, which
// didn't have their own old arm — they fell through backend_search_
// limited's wildcard `_ -> list_take_n limit (backend_search gb b)`),
// the comment inline says so.
let rec caps_of_backend (gb : graph_backend) : Tot store_caps (decreases gb) =
  match gb with
  | GB_List g ->
    // Old arms: backend_search/backend_estimate -> store_search/
    // store_estimate (graph_to_store g) directly; backend_count_exact
    // fell through its wildcard (-> backend_estimate); predicate_present
    // had its own GB_List arm computing the same backend_estimate
    // {bp=Some pred}>0 shape; decode_failure fell through its wildcard
    // (-> false). solve_limited had no GB_List arm -> the wildcard
    // `list_take_n limit (backend_search gb b)`.
    let st = graph_to_store g in
    {
      sc_flags = {
        scf_supports_named_graphs = false;
        scf_supports_update = false;
        scf_streaming_shapes = true;
        scf_estimate_is_exact = true;
        scf_can_report_decode_fail = false;
      };
      sc_solve = (fun b -> store_search st b);
      sc_solve_limited = (fun b n -> list_take_n n (store_search st b));
      sc_estimate = (fun b -> store_estimate st b);
      sc_count_exact = (fun b -> store_estimate st b);
      sc_predicate_present =
        (fun pred -> store_estimate st ({ bs = None; bp = Some pred; bo = None }) > 0);
      sc_decode_failure = (fun () -> false);
    }
  | GB_Indexed ig -> caps_of_indexed ig
  | GB_HDT hgs ->
    // Old arms: backend_search -> hdt_search_triples; backend_estimate
    // -> hdt_estimate (hdt_build_bound_tp ...); backend_count_exact fell
    // through its wildcard (-> backend_estimate); predicate_present ->
    // hdt_predicate_present directly; decode_failure fell through its
    // wildcard (-> false); solve_limited had no GB_HDT arm -> the
    // wildcard truncation.
    {
      sc_flags = {
        scf_supports_named_graphs = false;
        scf_supports_update = false;
        scf_streaming_shapes = true;
        scf_estimate_is_exact = true;
        scf_can_report_decode_fail = false;
      };
      sc_solve = (fun b -> hdt_search_triples hgs b.bs b.bp b.bo);
      sc_solve_limited = (fun b n -> list_take_n n (hdt_search_triples hgs b.bs b.bp b.bo));
      sc_estimate = (fun b -> hdt_estimate hgs (hdt_build_bound_tp hgs b.bs b.bp b.bo));
      sc_count_exact = (fun b -> hdt_estimate hgs (hdt_build_bound_tp hgs b.bs b.bp b.bo));
      sc_predicate_present = (fun pred -> hdt_predicate_present hgs pred);
      sc_decode_failure = (fun () -> false);
    }
  | GB_COTTAS cds graph_name ->
    // Old arms: backend_search -> cottas_search + the fst-projection of
    // cottas_rows_to_quads; backend_estimate -> cottas_estimate;
    // backend_count_exact fell through its wildcard (-> backend_
    // estimate); predicate_present had its own GB_COTTAS arm computing
    // the same backend_estimate {bp=Some pred}>0 shape (i.e. the same
    // cottas_estimate call with bs/bo cleared); decode_failure fell
    // through its wildcard (-> false); solve_limited had no GB_COTTAS
    // arm -> the wildcard truncation.
    {
      sc_flags = {
        scf_supports_named_graphs = true;
        scf_supports_update = false;
        scf_streaming_shapes = true;
        scf_estimate_is_exact = true;
        scf_can_report_decode_fail = false;
      };
      sc_solve =
        (fun b ->
          let rows = cottas_search cds (cottas_build_bound_qp cds b.bs b.bp b.bo graph_name) in
          List.Tot.map fst (cottas_rows_to_quads cds rows));
      sc_solve_limited =
        (fun b n ->
          let rows = cottas_search cds (cottas_build_bound_qp cds b.bs b.bp b.bo graph_name) in
          list_take_n n (List.Tot.map fst (cottas_rows_to_quads cds rows)));
      sc_estimate =
        (fun b -> cottas_estimate cds (cottas_build_bound_qp cds b.bs b.bp b.bo graph_name));
      sc_count_exact =
        (fun b -> cottas_estimate cds (cottas_build_bound_qp cds b.bs b.bp b.bo graph_name));
      sc_predicate_present =
        (fun pred ->
          cottas_estimate cds (cottas_build_bound_qp cds None (Some pred) None graph_name) > 0);
      sc_decode_failure = (fun () -> false);
    }
  | GB_CottasOnDisk cods scope -> caps_of_cottas cods scope
  // Stage 3 D-overlay (see the constructor's own comment above): the
  // seam's whole point is that adding this backend touches ONLY this
  // arm — `overlay` (RDF.Store.Capabilities.Delta.fst) is the entire
  // realisation, reusing the unmodified COTTAS builder as its base.
  | GB_CottasOnDiskDelta cods scope delta -> overlay (caps_of_cottas cods scope) delta
  | GB_Union members -> union_caps (caps_of_backend_list members)
  | GB_VirtualRML rvs -> RML.VirtualSource.caps_of_rml_source rvs

// Structural twin of caps_of_backend over a list. Replaces the six
// union_* recursion twins: union_caps (RDF.Store.Capabilities.fst) IS
// the design doc's single combinator (§4); this is the small mapping
// helper that gets caps_of_backend's per-constructor output into the
// `list store_caps` shape union_caps consumes, mirroring how the old
// union_backend_* family recursed `member :: rest` one graph_backend
// at a time.
and caps_of_backend_list (members : list graph_backend) : Tot (list store_caps) (decreases members) =
  match members with
  | [] -> []
  | m :: rest -> caps_of_backend m :: caps_of_backend_list rest

// ----------------------------------------------------------------------
// The six backend_* dispatchers. Each is now a one-line forwarder
// through caps_of_backend's single dispatch point (design doc §5, U2).
// Byte-identical behaviour to the pre-U2 per-constructor match — see
// caps_of_backend's per-constructor comments above, and
// RDF.Store.Capabilities.fst / RDF.Store.Capabilities.Cottas.fst's own
// per-field comments for the GB_Indexed / GB_CottasOnDisk cases, and
// RDF.Store.Capabilities.fst's union_caps/union_solve_limited for the
// GB_Union case (including the real per-member LIMIT-pushdown fix that
// stage U2 made to union_caps's sc_solve_limited — see that module's
// disclosed adjustment #4).
// ----------------------------------------------------------------------
let backend_search (gb : graph_backend) (b : triple_pattern_bound) : list triple =
  (caps_of_backend gb).sc_solve b

let backend_search_limited (gb : graph_backend) (b : triple_pattern_bound) (limit : nat)
  : Tot (list triple) =
  (caps_of_backend gb).sc_solve_limited b limit

let backend_estimate (gb : graph_backend) (b : triple_pattern_bound) : nat =
  (caps_of_backend gb).sc_estimate b

let backend_count_exact (gb : graph_backend) (b : triple_pattern_bound) : Tot nat =
  (caps_of_backend gb).sc_count_exact b

let backend_predicate_present (gb : graph_backend) (pred : wf_iri) : Tot bool =
  (caps_of_backend gb).sc_predicate_present pred

// Durable-UPDATE stage 4 (compaction, docs/designissues/2026-07-06-
// durable-update-design.md §5 row 4 / §4.3): materialize a whole
// `dataset_backend` — default graph plus every named graph, base rows
// composed with any live delta via whichever `graph_backend` arm each
// one is (GB_CottasOnDisk, GB_CottasOnDiskDelta via `overlay`, GB_Union,
// ...) — into a plain in-memory `rdf_dataset`. Reuses the exact
// `backend_search gb { bs = None; bp = None; bo = None }` "unbound
// scan" shape already used above (GP_PropertyPath's materialised-graph
// fallback, issue #268) rather than inventing a second way to read
// "every triple in this backend." The result is fed to
// `RDF.Canonical.canonical_nquads` (existing, Tot, already what
// bin/factoidal-dump-nq/factoidal_dump_nq.ml uses) by the compaction
// orchestrator to get plain N-Quads text for corpus_pipeline.py's
// EXISTING import pipeline (rule #15: no new store-writing logic) —
// this function's whole job is the "read back everything, base ⊕
// delta, as one rdf_dataset" step, not serialization or I/O.
let materialize_dataset_backend (dsb : dataset_backend) : Tot rdf_dataset =
  let unbound : triple_pattern_bound = { bs = None; bp = None; bo = None } in
  {
    ds_default = backend_search dsb.dsb_default unbound;
    ds_named =
      List.Tot.map
        (fun (ngb : named_graph_backend) ->
          { ng_name = ngb.ngb_name; ng_graph = backend_search ngb.ngb_graph unbound })
        dsb.dsb_named;
  }

// Issue #269: did evaluating this backend involve a COTTAS on-disk
// artifact with a column that failed to decode (e.g. an RLE_DICTIONARY
// page the reader can't handle)? `backend_search` / `eval_pattern_backend`
// silently treat an undecodable row group as contributing zero rows
// (sound for callers that only consume the ROWS), so a genuinely empty
// result and a decode failure are indistinguishable downstream — exactly
// the ambiguity that let `ASK { ?s ?p ?o }` answer `false` instead of
// erroring on a corpus it could not fully read. Callers that treat an
// empty solution set as a meaningful answer (ASK) must check this first.
let backend_decode_failure (gb : graph_backend) : Tot bool =
  (caps_of_backend gb).sc_decode_failure ()

let rec lookup_named_backend (name : iri) (named : list named_graph_backend)
  : Tot (option graph_backend) (decreases named) =
  match named with
  | [] -> None
  | ng :: rest ->
    if ng.ngb_name = name then Some ng.ngb_graph else lookup_named_backend name rest

// U1.5 amendment (owner requirement, 2026-07-06: "the db must support
// full named graphs too, not just triples" — landed alongside U2, not
// deferred to U4). Builds RDF.Store.Capabilities.dataset_caps — the
// store_caps-shaped SIBLING of this module's own dataset_backend — by
// running caps_of_backend once over the default graph and once per
// named graph. No new per-backend logic: every field of the result IS
// caps_of_backend applied to a `graph_backend` this module already
// had, exactly the discipline caps_of_backend itself follows one level
// down. This does NOT replace dataset_backend/named_graph_backend or
// change lookup_named_backend/eval_pattern_backend's GP_Graph routing
// above — it is an additional, equivalence-tested view (see
// tests/unit/store_capabilities_unit.ml's "GB_Union"/dataset section)
// proving named-graph resolution agrees between the two routes.
//
// Residual (see RDF.Store.Capabilities.fst's own banner above
// `dataset_caps`, and the task report): this is still a per-graph
// TRIPLE-shaped composition — a `GRAPH ?g` caller still enumerates
// `dsc_named` and calls `sc_solve` once per graph, same cost shape as
// `named_candidate_backends` + `Lh.concatMap_tr` below. A quad-native
// `sc_solve_quad` that pushes an unbound graph term into one on-disk
// walk is unimplemented, scoped as U2.5.
let dataset_caps_of_backend (dsb : dataset_backend) : Tot dataset_caps =
  {
    dsc_default = caps_of_backend dsb.dsb_default;
    dsc_named =
      List.Tot.map
        (fun (ngb : named_graph_backend) -> (ngb.ngb_name, caps_of_backend ngb.ngb_graph))
        dsb.dsb_named;
  }

let eval_single_tp_backend_default (tp : triple_pattern) (gb : graph_backend) (mu : solution_mapping)
  : solution_sequence =
  let bound = {
    bs = bound_subject_of_pattern tp.tp_s mu;
    bp = bound_predicate_of_pattern tp.tp_p mu;
    bo = bound_object_of_pattern tp.tp_o mu;
  } in
  let candidates = backend_search gb bound in
  list_filter_map (fun t -> tp_match tp t mu) candidates

// Fulltext SPARQL slice 1 dispatch point (design doc §3, backend-neutral
// path — what the CLI/HTTP binaries actually exercise). Same shape as
// SPARQL11.Algebra's `eval_fulltext_tp_store` twin, over `backend_search`
// instead of `store_search` so it works identically across GB_List,
// GB_Indexed, GB_HDT, GB_COTTAS(OnDisk[Delta]), and GB_Union — no new
// `graph_backend` constructor (design doc §7 open decision 2 left
// unresolved; slice 1 needs no wrapper since the index is query-time-only,
// no on-disk companion file per §6).
let eval_fulltext_tp_backend (ftq : SPARQL.FullText.fulltext_query) (tp : triple_pattern)
  (gb : graph_backend) (mu : solution_mapping) : solution_sequence =
  let bound = { bs = None; bp = ftq.ftq_field; bo = None } in
  let candidates = backend_search gb bound in
  let matched =
    List.Tot.filter (fun (t : triple) -> SPARQL.FullText.object_matches_query ftq t.o) candidates in
  let limited =
    match ftq.ftq_limit with
    | Some n -> list_take_n n matched
    | None -> matched in
  list_filter_map (fun t -> try_bind_subject tp.tp_s t.s mu) limited

let eval_single_tp_backend (tp : triple_pattern) (gb : graph_backend) (mu : solution_mapping)
  : solution_sequence =
  match tp.tp_p with
  | PT_IRI pred ->
    if pred = SPARQL.FullText.fulltext_query_pred then
      match tp.tp_o with
      | PT_Literal args_lit ->
        (match SPARQL.FullText.decode_fulltext_literal args_lit with
         | Some ftq -> eval_fulltext_tp_backend ftq tp gb mu
         | None -> eval_single_tp_backend_default tp gb mu)
      | _ -> eval_single_tp_backend_default tp gb mu
    else eval_single_tp_backend_default tp gb mu
  | _ -> eval_single_tp_backend_default tp gb mu

// Compact bound-shape descriptor. Encodes which positions have a
let estimate_tp_backend_mu (tp : triple_pattern) (gb : graph_backend) (mu : solution_mapping) : nat =
  backend_estimate gb {
    bs = bound_subject_of_pattern tp.tp_s mu;
    bp = bound_predicate_of_pattern tp.tp_p mu;
    bo = bound_object_of_pattern tp.tp_o mu;
  }

// F* planner. Stays pure (Tot). Logging is the OCaml-side dry-runner's
// job (factoidal_explain.ml calls choose_best_tp_backend recursively
// and logs each decision via Util_Log_runtime). Earlier attempt to
// embed Util.Log calls IN this F* function was reverted: F* erases
// `Tot unit` returning calls in unused-result position, regardless of
// whether they're assume-val or `let`-bodied. The clean split:
// PLANNING in F*, LOGGING in OCaml glue.
let rec choose_best_tp_backend (patterns : bgp) (gb : graph_backend) (mu : solution_mapping)
  : Tot (option (triple_pattern * bgp)) (decreases patterns) =
  match patterns with
  | [] -> None
  | tp :: rest ->
    match choose_best_tp_backend rest gb mu with
    | None -> Some (tp, [])
    | Some (best, remaining) ->
      if estimate_tp_backend_mu tp gb mu <= estimate_tp_backend_mu best gb mu
      then Some (tp, rest)
      else Some (best, tp :: remaining)

let rec pattern_predicate_hint (p : group_graph_pattern)
  : Tot (option wf_iri) (decreases p) =
  match p with
  | GP_BGP [] -> None
  | GP_BGP (tp :: _) ->
    (match tp.tp_p with
     | PT_IRI pred -> Some pred
     | _ -> None)
  | GP_Filter _ p' -> pattern_predicate_hint p'
  | GP_Bind _ _ p' -> pattern_predicate_hint p'
  | GP_Graph _ p' -> pattern_predicate_hint p'
  | GP_Join p1 _ -> pattern_predicate_hint p1
  | GP_LeftJoin p1 _ _ -> pattern_predicate_hint p1
  | GP_Union p1 _ -> pattern_predicate_hint p1
  | GP_Minus p1 _ -> pattern_predicate_hint p1
  | GP_Lateral p1 _ -> pattern_predicate_hint p1
  | GP_Empty -> None
  | GP_Values _ _ -> None
  | GP_Service _ _ _ -> None
  | GP_ServiceVar _ _ _ -> None
  | GP_SubSelect _ -> None
  | GP_PropertyPath _ _ _ -> None

let named_candidate_backends (named : list named_graph_backend) (predicate_hint : option wf_iri)
  : list named_graph_backend =
  match predicate_hint with
  | None -> named
  | Some pred ->
    List.Tot.filter (fun ngb -> backend_predicate_present ngb.ngb_graph pred) named

// Tail-rec concatMap helper. F* stdlib `List.Tot.concatMap` is non-tail-rec
// (recurses, then `append`s), so on a 3M-element solution list (e.g. first
// BGP pattern matching the entire COTTAS dataset) the outer recursion alone
// blows the macOS main-thread stack. Sin7 fix (2026-04-26): walk `next`
// tail-recursively, using `List.Tot.rev_acc` to splice each per-mu result
// list into a reversed accumulator. Order preserved (rev once at the end).
let rec eval_bgp_concatmap_acc
  (rest : bgp) (gb : graph_backend) (next : solution_sequence)
  (fuel : nat) (acc_rev : solution_sequence)
  : Tot solution_sequence (decreases %[fuel; 1; next]) =
  match next with
  | [] -> acc_rev
  | mu' :: more ->
    let part = eval_bgp_backend_from_mu_fuel rest gb mu' fuel in
    eval_bgp_concatmap_acc rest gb more fuel (List.Tot.rev_acc part acc_rev)

and eval_bgp_backend_from_mu_fuel
  (patterns : bgp) (gb : graph_backend) (mu : solution_mapping) (fuel : nat)
  : Tot solution_sequence (decreases %[fuel; 0; ([] <: solution_sequence)]) =
  if fuel = 0 then [mu]
  else
    match patterns with
    | [] -> [mu]
    | _ ->
      match choose_best_tp_backend patterns gb mu with
      | None -> [mu]
      | Some (tp, rest) ->
        let next = eval_single_tp_backend tp gb mu in
        List.Tot.rev (eval_bgp_concatmap_acc rest gb next (fuel - 1) [])

let eval_bgp_backend (patterns : bgp) (gb : graph_backend) : solution_sequence =
  eval_bgp_backend_from_mu_fuel patterns gb sm_empty (List.Tot.length patterns + 1)

// ----------------------------------------------------------------------
// Aleph6 (issue #100, demo prep): query-shape detectors and fast paths.
//
// These pattern-match the SPARQL AST for two demo-critical query shapes:
//
//   1. Streaming COUNT(*): SELECT (COUNT(*) AS ?n) WHERE { tp } with no
//      GROUP BY, no DISTINCT, no FILTER above the BGP. Calls
//      `backend_estimate` directly instead of materialising 3M+ rows
//      and counting them.
//
//   2. LIMIT pushdown: SELECT ?vars WHERE { tp } LIMIT k with no
//      DISTINCT/ORDER BY/aggregates/etc. Uses
//      `backend_search_limited` so the COTTAS-on-disk walker stops at
//      `k` rows.
//
// Both fast paths are SEMANTICS-PRESERVING: when the detector matches,
// the returned solution sequence equals what the materialise path
// would produce. Detectors are conservative — anything they don't
// recognise falls through to the existing materialise path.
// ----------------------------------------------------------------------

// Helper: extract the single triple pattern of a 1-tp BGP, modulo no
// FILTER/BIND/JOIN wrappers that change semantics. Returns None if the
// pattern isn't a single-tp BGP.
let extract_single_tp_bgp (p : group_graph_pattern) : option triple_pattern =
  match p with
  | GP_BGP [tp] -> Some tp
  | _ -> None

// Helper: detect the COUNT(*) shape of a SELECT clause.
// Matches SI_Expr (E_Aggregate Agg_Count false (E_Var "*" | E_BoolLit true)) v.
// COUNT(DISTINCT *) is NOT matched (distinct=false required) — it needs
// row materialisation for the dedup pass.
let detect_count_star_select (sel : select_clause) : option var_name =
  match sel with
  | Select_Vars [SI_Expr e v] ->
    (match e with
     | E_Aggregate Agg_Count distinct sub_e ->
       if distinct then None
       else
         (match sub_e with
          | E_Var "*" -> Some v
          | E_BoolLit true -> Some v
          | _ -> None)
     | _ -> None)
  | _ -> None

// Roadmap-item-4 follow-up (issue #297, 2026-07-06): extract a
// single-tp BGP that is EITHER bare OR wrapped in exactly one
// `GRAPH <constant-iri> { ... }` layer. Returns
// `Some (tp, None)` for a bare `GP_BGP [tp]` (evaluate against the
// query's current graph backend, unchanged behaviour) or
// `Some (tp, Some g)` for `GRAPH <g> { tp }` with a CONSTANT graph IRI
// (evaluate against the dataset's named backend for `g`).
//
// Deliberately does NOT match `GRAPH ?g { tp }` (an unbound graph
// variable). Per SPARQL 1.1 dataset semantics an unbound ?g ranges
// over EVERY named graph; a non-grouped `COUNT(*)` over that shape
// must SUM `backend_count_exact` across every named graph — a
// fundamentally different evaluation shape (one sum over N backends)
// than the "one graph_backend, one exact count" this fast path
// assumes, and not a mechanical widening of the detector. (The
// GROUP-BY-?g sibling above, `detect_streaming_count_group_by_graph`,
// legitimately needs the PER-GRAPH breakdown rather than a sum, so it
// already has its own dedicated path.) Left as future work; falls
// through to the materialise path here, which is correct, just not
// fast for this one shape.
let extract_single_tp_bgp_scoped (p : group_graph_pattern)
  : option (triple_pattern & option wf_iri) =
  match p with
  | GP_BGP [tp] -> Some (tp, None)
  | GP_Graph (PT_IRI g) (GP_BGP [tp]) -> Some (tp, Some g)
  | _ -> None

// Detect the streaming-COUNT(*) shape of a whole query and return the
// alias variable name, the triple pattern, and (issue #297) an
// optional constant graph IRI when the pattern is `GRAPH <g> { tp }`
// rather than a bare BGP. Conservative — bails out on any modifier
// that would change the count (DISTINCT, ORDER BY, HAVING, GROUP BY,
// VALUES, etc.).
let detect_streaming_count_star (q : query) : option (var_name & triple_pattern & option wf_iri) =
  match q.q_form with
  | QF_Select sel ->
    (match detect_count_star_select sel with
     | None -> None
     | Some v ->
       if Some? q.q_group_by then None
       else if Some? q.q_having then None
       else if Some? q.q_values then None
       else if q.q_modifier.sm_distinct then None
       else if q.q_modifier.sm_reduced then None
       else if Some? q.q_modifier.sm_order_by then None
       else
         (match extract_single_tp_bgp_scoped q.q_pattern with
          | None -> None
          | Some (tp, scope) -> Some (v, tp, scope)))
  | _ -> None

// Build the one-row solution sequence for COUNT(*) = n.
let count_star_solution (alias : var_name) (n : nat) : solution_sequence =
  let lit_term : rdf_term = T_Literal {
    lexical_form = string_of_int n;
    datatype = xsd_integer;
    lang_tag = None;
  } in
  [ sm_bind alias lit_term sm_empty ]

// Detect:  SELECT ?g (COUNT(*) AS ?n) WHERE { GRAPH ?g { ?s ?p ?o } }
//          GROUP BY ?g  [ORDER BY ?...  LIMIT/OFFSET]
// Returns (graph_var, count_alias) when the shape matches.
//
// Allowed modifiers: ORDER BY (sorted post-aggregate via sort_solutions),
//   LIMIT/OFFSET (sliced via slice_solutions).
// Rejected modifiers: HAVING, VALUES, DISTINCT, REDUCED — any of these
//   requires row materialisation and the streaming count is unsound.
//
// The inner BGP must be a single triple pattern with all three terms
// being VARIABLES, all DISTINCT from each other, and all DISTINCT from
// the graph variable ?g. Without that distinctness check, queries like
//   GRAPH ?g { ?g ?p ?o }   -- ?g now also bound from subject column
//   GRAPH ?g { ?s ?p ?s }   -- ?s appears twice; equality constraint
// would still match, but the streaming estimate counts the whole graph
// without honouring those equality constraints, returning a wrong
// (over-)count. (Reviewer 2026-05-01.)
let detect_streaming_count_group_by_graph (q : query)
  : option (var_name & var_name) =
  match q.q_form with
  | QF_Select (Select_Vars items) ->
    if Some? q.q_having then None
    else if Some? q.q_values then None
    else if q.q_modifier.sm_distinct then None
    else if q.q_modifier.sm_reduced then None
    else
      // SELECT must be exactly: SI_Var ?g, SI_Expr (COUNT(*) AS ?n)
      (match items with
       | [SI_Var gv; SI_Expr count_e nv] ->
         (match count_e with
          | E_Aggregate Agg_Count false sub_e ->
            let count_ok = match sub_e with
              | E_Var "*" -> true
              | E_BoolLit true -> true
              | _ -> false in
            if not count_ok then None
            else
              // GROUP BY exactly [GC_Var gv]
              (match q.q_group_by with
               | Some [GC_Var gbv] ->
                 if gbv <> gv then None
                 else
                   // WHERE: GP_Graph (PT_Var gv) (GP_BGP [tp]) where tp is
                   // (PS_Var s, PT_Var p, PT_Var o), all PAIRWISE DISTINCT
                   // and all distinct from gv.
                   (match q.q_pattern with
                    | GP_Graph (PT_Var graph_v) inner ->
                      if graph_v <> gv then None
                      else
                        (match extract_single_tp_bgp inner with
                         | None -> None
                         | Some tp ->
                           (match tp.tp_s, tp.tp_p, tp.tp_o with
                            | PS_Var sv, PT_Var pv, PT_Var ov ->
                              // Pairwise-distinct check: rejects shapes like
                              // ?g/?p/?o or ?s/?p/?s that would carry an
                              // implicit equality constraint the estimate
                              // does not honour.
                              if sv = gv || pv = gv || ov = gv then None
                              else if sv = pv || sv = ov || pv = ov then None
                              else Some (gv, nv)
                            | _ -> None))
                    | _ -> None)
               | _ -> None)
          | _ -> None)
       | _ -> None)
  | _ -> None

// Build the per-graph solutions for the GROUP BY ?g COUNT(*) fast path.
// One row per named graph: ?g = graph IRI, ?count_alias = backend_estimate.
//
// Tail-recursive accumulator form (reviewer 2026-05-01): the prior
// straight-recursive shape blew JS's ~10K stack on lifesci-class
// datasets if a future caller passed in many named graphs. Same
// pattern as the bucket_replace tail-rec fix in #119.
let rec count_group_by_graph_solutions_acc
  (graph_var : var_name)
  (count_alias : var_name)
  (acc : solution_sequence)
  (named : list named_graph_backend)
  : Tot solution_sequence (decreases named) =
  match named with
  | [] -> List.Tot.rev acc
  | ngb :: rest ->
    let bound : triple_pattern_bound = { bs = None; bp = None; bo = None } in
    // Exact, not estimate: this count IS the query result (E1 bug).
    let cnt = backend_count_exact ngb.ngb_graph bound in
    let lit_term : rdf_term = T_Literal {
      lexical_form = string_of_int cnt;
      datatype = xsd_integer;
      lang_tag = None;
    } in
    let mu0 = sm_bind count_alias lit_term sm_empty in
    let mu = if is_iri ngb.ngb_name
             then sm_bind graph_var (T_IRI ngb.ngb_name) mu0
             else mu0 in
    count_group_by_graph_solutions_acc graph_var count_alias (mu :: acc) rest

let count_group_by_graph_solutions
  (graph_var : var_name)
  (count_alias : var_name)
  (named : list named_graph_backend)
  : solution_sequence =
  count_group_by_graph_solutions_acc graph_var count_alias [] named

// Detect the LIMIT-pushdown shape: SELECT ?vars WHERE { single tp }
// [LIMIT k]  with no DISTINCT / ORDER BY / OFFSET / GROUP BY / HAVING /
// VALUES / aggregates. Returns (triple_pattern, limit) when matched.
let detect_limit_single_tp (q : query) : option (triple_pattern & nat) =
  match q.q_form with
  | QF_Select sel ->
    if select_has_aggregates sel then None
    else if Some? q.q_group_by then None
    else if Some? q.q_having then None
    else if Some? q.q_values then None
    else if q.q_modifier.sm_distinct then None
    else if q.q_modifier.sm_reduced then None
    else if Some? q.q_modifier.sm_order_by then None
    else if Some? q.q_modifier.sm_offset then None
    else
      (match q.q_modifier.sm_limit with
       | None -> None
       | Some k ->
         (match extract_single_tp_bgp q.q_pattern with
          | None -> None
          | Some tp -> Some (tp, k)))
  | _ -> None

// Run the LIMIT-pushdown path. Builds a triple_pattern_bound (no mu),
// calls backend_search_limited, projects to the SELECT clause's vars.
let eval_limit_single_tp (sel : select_clause) (tp : triple_pattern)
  (gb : graph_backend) (limit : nat) : solution_sequence =
  let bound = {
    bs = bound_subject_of_pattern tp.tp_s sm_empty;
    bp = bound_predicate_of_pattern tp.tp_p sm_empty;
    bo = bound_object_of_pattern tp.tp_o sm_empty;
  } in
  let candidates = backend_search_limited gb bound limit in
  let omega = list_filter_map (fun t -> tp_match tp t sm_empty) candidates in
  let omega' = list_take_n limit omega in
  match sel with
  | Select_Vars items -> project_solutions (select_item_vars items) omega'
  | Select_All -> omega'

let rec eval_pattern_backend (base : option wf_iri) (p : group_graph_pattern) (gb : graph_backend) (dsb : dataset_backend)
  : Tot solution_sequence (decreases p) =
  match p with
  | GP_BGP bgp ->
    eval_bgp_backend bgp gb

  | GP_Join p1 p2 ->
    join (eval_pattern_backend base p1 gb dsb) (eval_pattern_backend base p2 gb dsb)

  | GP_LeftJoin p1 p2 filter_e ->
    left_join base (eval_pattern_backend base p1 gb dsb) (eval_pattern_backend base p2 gb dsb) filter_e

  | GP_Filter e p' ->
    filter_solutions_fwd base e (eval_pattern_backend base p' gb dsb)

  | GP_Union p1 p2 ->
    union (eval_pattern_backend base p1 gb dsb) (eval_pattern_backend base p2 gb dsb)

  | GP_Minus p1 p2 ->
    minus (eval_pattern_backend base p1 gb dsb) (eval_pattern_backend base p2 gb dsb)

  | GP_Lateral p1 p2 ->
    // P1 LATERAL { P2 }: correlated per-row evaluation, backend-native
    // path. `eval_pattern_backend` is mutually recursive (via `and`)
    // with `eval_select_query_backend_on_graph`/`_bgp` and its
    // `decreases p` obligation only lets it recurse into structural
    // subterms of `p` — a per-row SUBSTITUTED p2 is not one, so a direct
    // `eval_pattern_backend base p2' gb dsb` call here would not
    // typecheck (same obstacle GP_SubSelect works around by staying
    // inside the mutual group with a `query`-shaped subterm; a lateral
    // substitution manufactures a brand-new pattern, not a subterm).
    // Rather than add a new assume val to break the cycle, reuse the
    // exact "materialize this backend, then delegate to the in-memory
    // algebra evaluator" device issue #268 already established for
    // GP_PropertyPath just below (same backend_search unbound-scan
    // shape, same rationale: correctness first, backend-native fast
    // path is a follow-up). This is still backend-neutral BY
    // CONSTRUCTION: `backend_search`/`materialize_dataset_backend` are
    // the same store-capability seam every GB_* constructor already
    // dispatches through (GB_List/GB_Indexed/GB_HDT/GB_COTTAS/
    // GB_CottasOnDisk/GB_CottasOnDiskDelta/GB_Union), so in-memory and
    // on-disk COTTAS queries reach `lateral_substitute` +
    // `eval_pattern` identically.
    let omega1 = eval_pattern_backend base p1 gb dsb in
    let ds0 = materialize_dataset_backend dsb in
    let g_current = backend_search gb { bs = None; bp = None; bo = None } in
    let ds = { ds0 with ds_default = g_current } in
    Lh.concatMap_tr
      (fun mu1 ->
        let p2' = lateral_substitute mu1 p2 in
        let omega2 = eval_pattern base p2' g_current ds in
        list_filter_map
          (fun mu2 -> if sm_compatible mu1 mu2 then Some (sm_merge mu1 mu2) else None)
          omega2)
      omega1

  | GP_Empty ->
    [sm_empty]

  | GP_Bind e v p' ->
    let omega = eval_pattern_backend base p' gb dsb in
    List.Tot.map
      (fun mu ->
        match er_to_term (eval_expr_fwd base e mu) with
        | Some t ->
          (match sm_lookup v mu with
           | Some _ -> mu
           | None -> sm_bind v t mu)
        | None -> mu)
      omega

  | GP_Values vars rows ->
    eval_values vars rows

  | GP_Graph gt p' ->
    (match gt with
     | PT_IRI name ->
       (match lookup_named_backend name dsb.dsb_named with
        | Some ngb -> eval_pattern_backend base p' ngb dsb
        | None -> [])
     | PT_Var v ->
       let candidates = named_candidate_backends dsb.dsb_named (pattern_predicate_hint p') in
       Lh.concatMap_tr
         (fun (ngb : named_graph_backend) ->
           let ng_results = eval_pattern_backend base p' ngb.ngb_graph dsb in
           if is_iri ngb.ngb_name then
             List.Tot.map (fun mu -> sm_bind v (T_IRI ngb.ngb_name) mu) ng_results
           else ng_results)
         candidates
     | _ ->
       eval_pattern_backend base p' gb dsb)

  | GP_Service _ _ _ ->
    []

  | GP_ServiceVar _ _ _ ->
    (* Variable-endpoint federated query — backend evaluator does not currently
       implement service dispatch. Issue #57 Phase 3 (Tet): full per-solution
       handling lives in the in-memory eval_pattern_store path. *)
    []

  | GP_SubSelect q ->
    (match eval_select_query_backend_on_graph q gb dsb with
     | Some omega -> omega
     | None -> [])

  | GP_PropertyPath ps pp pt ->
    // Issue #268: this case used to return [] unconditionally, so
    // property-path queries (`knows+`, `knows/name`, …) silently
    // evaluated empty on the CLI/HTTP (backend) path while the
    // in-memory algebra path (eval_pattern_store's GP_PropertyPath
    // arm, SPARQL11.Algebra.fst ~2242) implemented them correctly —
    // dashboard-invisible, since the W3C runner exercises the
    // in-memory path.
    //
    // Fix: materialise the CURRENT graph backend's triples via an
    // unbound backend_search, then delegate to the exact same
    // path-evaluation logic the algebra path uses:
    // `eval_property_path_fwd` (forward-declared in SPARQL11.Algebra,
    // realised to the concrete `eval_property_path` via
    // 62_forward_ref_wiring.sh) plus `path_result_to_solutions`, plus
    // the issue #66 Zero* reflexive-pair fixup so ZeroOrMore/ZeroOrOne
    // constants that appear nowhere in the data still get their
    // reflexive match. `backend_search gb { bs = None; bp = None;
    // bo = None }` already returns `list triple`, which IS `rdf_graph`
    // (`RDF.Graph.Executable.rdf_graph = list triple`) — no
    // graph_to_store / build_indexed wrapping needed, since
    // eval_property_path_fwd walks a plain triple list, not an
    // indexed shape.
    //
    // perf: this walks the WHOLE graph/backend for every property-path
    // pattern — same cost class as an unbound BGP scan. The
    // COTTAS-on-disk backend pays a full row-group decode per call.
    // A faster on-disk path (BFS/DFS over an indexed adjacency without
    // materialising every triple) is a follow-up; correctness first
    // per issue #268.
    let materialized_graph : rdf_graph =
      backend_search gb { bs = None; bp = None; bo = None } in
    let pairs = eval_property_path_fwd pp materialized_graph in
    let pairs =
      match pp with
      | PP_ZeroOrMore _ | PP_ZeroOrOne _ ->
        let constant_terms : list rdf_term =
          Lh.append_tr
            (match ps with
             | PS_IRI i   -> [T_IRI i]
             | PS_BNode b -> [T_BNode b]
             | PS_Var _   -> [])
            (match pt with
             | PT_IRI i     -> [T_IRI i]
             | PT_BNode b   -> [T_BNode b]
             | PT_Literal l -> [T_Literal l]
             | PT_Var _     -> [])
        in
        let has_reflexive (t : rdf_term) : bool =
          List.Tot.existsb
            (fun (pair : rdf_term * rdf_term) ->
              let (s, o) = pair in
              rdf_term_eq s t && rdf_term_eq o t)
            pairs
        in
        let new_terms = List.Tot.filter (fun t -> not (has_reflexive t)) constant_terms in
        let new_reflexive = List.Tot.map (fun (n : rdf_term) -> (n, n)) new_terms in
        Lh.append_tr pairs new_reflexive
      | _ -> pairs
    in
    path_result_to_solutions ps pt pairs

and eval_select_query_backend_bgp (q : query) (gb : graph_backend)
  : option solution_sequence =
  let base = q.q_base in
  match q.q_form, q.q_pattern with
  | QF_Select sel, GP_BGP bgp ->
    let omega0 = eval_bgp_backend bgp gb in
    let omega = match q.q_values with
      | None -> omega0
      | Some vals -> join omega0 vals in
    let needs_grouping = match q.q_group_by with
      | Some _ -> true
      | None -> select_has_aggregates sel in
    if needs_grouping then None
    else
      let omega' = match sel with
        | Select_Vars items -> eval_select_items base items omega []
        | Select_All -> omega in
      let ordered = match q.q_modifier.sm_order_by with
        | None -> omega'
        | Some o -> sort_solutions base o omega' in
      let projected = match sel with
        | Select_Vars items -> project_solutions (select_item_vars items) ordered
        | Select_All -> ordered in
      let deduped =
        if q.q_modifier.sm_distinct then distinct_solutions projected
        else if q.q_modifier.sm_reduced then reduced_solutions projected
        else projected in
      Some (slice_solutions q.q_modifier.sm_offset q.q_modifier.sm_limit deduped)
  | _ -> None

and eval_select_query_backend_on_graph (q : query) (gb : graph_backend) (dsb : dataset_backend)
  : option solution_sequence =
  // Aleph6: streaming COUNT-star fast-path. Calls backend_estimate
  // directly (one walk, no per-row materialisation). Semantics-
  // preserving: equivalent to materialising and counting.
  match detect_streaming_count_star q with
  | Some (alias, tp, graph_scope) ->
    let bound = {
      bs = bound_subject_of_pattern tp.tp_s sm_empty;
      bp = bound_predicate_of_pattern tp.tp_p sm_empty;
      bo = bound_object_of_pattern tp.tp_o sm_empty;
    } in
    // Exact, not estimate: this count IS the query result (E1 bug).
    // Issue #297: a `GRAPH <g> { tp }`-shaped COUNT (constant `g`,
    // caught by `extract_single_tp_bgp_scoped` above) must count
    // against the NAMED backend for `g`, not the caller's current
    // `gb` — exactly what `eval_pattern_backend`'s own
    // `GP_Graph (PT_IRI name)` arm does for the materialise path
    // (`lookup_named_backend`, `[]`/0 on an unknown graph name).
    let n = match graph_scope with
      | None -> backend_count_exact gb bound
      | Some g ->
        (match lookup_named_backend g dsb.dsb_named with
         | Some ngb -> backend_count_exact ngb bound
         | None -> 0) in
    let omega = count_star_solution alias n in
    Some (slice_solutions q.q_modifier.sm_offset q.q_modifier.sm_limit omega)
  | None ->
    // Aleph6: LIMIT-pushdown fast-path. SELECT vars WHERE single-tp LIMIT k.
    let limit_match : option (triple_pattern & nat) =
      match q.q_form with
      | QF_Select _ -> detect_limit_single_tp q
      | _ -> None in
    (match limit_match with
     | Some (tp, k) ->
       (match q.q_form with
        | QF_Select sel -> Some (eval_limit_single_tp sel tp gb k)
        | _ -> None)
     | None ->
    // Materialise path: original implementation, inlined here so that
    // F*'s totality checker can see the q.q_pattern structural decrease
    // for the recursive eval_pattern_backend call.
    match q.q_form with
    | QF_Select sel ->
      let base = q.q_base in
      let omega0 = eval_pattern_backend base q.q_pattern gb dsb in
      let omega = match q.q_values with
        | None -> omega0
        | Some vals -> join omega0 vals in
      let needs_grouping = match q.q_group_by with
        | Some _ -> true
        | None -> select_has_aggregates sel in
      if needs_grouping then
        let groups = match q.q_group_by with
          | Some conds -> group_by base conds omega
          | None -> implicit_group omega in
        let filtered_groups = match q.q_having with
          | Some conditions -> having_filter base conditions groups
          | None -> groups in
        let omega' = match sel with
          | Select_Vars items -> aggregate_groups base items filtered_groups
          | Select_All ->
            List.Tot.map (fun (grp : group) ->
              match grp.g_solutions with
              | mu :: _ -> mu
              | [] -> sm_empty) filtered_groups in
        let ordered = match q.q_modifier.sm_order_by with
          | None -> omega'
          | Some o -> sort_solutions base o omega' in
        let deduped =
          if q.q_modifier.sm_distinct then distinct_solutions ordered
          else if q.q_modifier.sm_reduced then reduced_solutions ordered
          else ordered in
        Some (slice_solutions q.q_modifier.sm_offset q.q_modifier.sm_limit deduped)
      else
        let omega' = match sel with
          | Select_Vars items -> eval_select_items base items omega []
          | Select_All -> omega in
        let ordered = match q.q_modifier.sm_order_by with
          | None -> omega'
          | Some o -> sort_solutions base o omega' in
        let projected = match sel with
          | Select_Vars items -> project_solutions (select_item_vars items) ordered
          | Select_All -> ordered in
        let deduped =
          if q.q_modifier.sm_distinct then distinct_solutions projected
          else if q.q_modifier.sm_reduced then reduced_solutions projected
          else projected in
        Some (slice_solutions q.q_modifier.sm_offset q.q_modifier.sm_limit deduped)
    | _ -> None)

and eval_select_query_backend_dataset (q : query) (dsb : dataset_backend)
  : option solution_sequence =
  // Bet5: streaming COUNT(*) GROUP BY ?g over named graphs. One
  // backend_estimate call per named graph, no per-row materialisation.
  // Semantics-preserving for the matched shape: each named graph
  // contributes exactly one ?g=iri / ?n=count row.
  match detect_streaming_count_group_by_graph q with
  | Some (graph_var, count_alias) ->
    let omega = count_group_by_graph_solutions graph_var count_alias dsb.dsb_named in
    // Apply ORDER BY post-aggregation if present. The result set is
    // bounded by the number of named graphs (small, typically < 100),
    // so sorting cost is negligible compared to the saved BGP eval.
    let ordered = match q.q_modifier.sm_order_by with
      | None   -> omega
      | Some o -> sort_solutions q.q_base o omega in
    Some (slice_solutions q.q_modifier.sm_offset q.q_modifier.sm_limit ordered)
  | None ->
    eval_select_query_backend_on_graph q dsb.dsb_default dsb

and eval_ask_query_backend_dataset (q : query) (dsb : dataset_backend)
  : option bool =
  match q.q_form with
  | QF_Ask ->
    let omega0 = eval_pattern_backend q.q_base q.q_pattern dsb.dsb_default dsb in
    let omega = match q.q_values with
      | None -> omega0
      | Some vals -> join omega0 vals in
    (match omega with
     | [] ->
       // Issue #269: an empty solution set is only a valid `false`
       // answer if every COTTAS on-disk backend touched by this query
       // decoded cleanly. A column that failed to decode (e.g. an
       // RLE_DICTIONARY page the reader can't handle) silently
       // contributes zero rows through `eval_pattern_backend` /
       // `backend_search` — sound for row-consuming callers, but ASK
       // reads "zero rows" as the answer `false`, which would turn a
       // read failure into a wrong answer with a clean exit. Report
       // "no boolean" (None) instead — the same signal the CLI/HTTP
       // consumers already treat as a query-evaluation error for the
       // backend ASK path.
       let named_backends = List.Tot.map
         (fun (ngb : named_graph_backend) -> ngb.ngb_graph) dsb.dsb_named in
       // Stage U2: union_backend_decode_failure is gone (folded into
       // caps_of_backend/union_caps); the OR-over-members shape is now
       // List.Tot.existsb over backend_decode_failure, same semantics
       // (a boolean OR doesn't care about accumulation order).
       if backend_decode_failure dsb.dsb_default ||
          List.Tot.existsb backend_decode_failure named_backends
       then None
       else Some false
     | _ -> Some true)
  | _ -> None

// Priority 2c (Jena basic-probe regression): the algebra path rewrites
// blank-node pattern terms to variables at its entry
// (eval_select_query, SPARQL11.Algebra); the backend path never did,
// so bnode-pattern SELECT/ASK matched zero rows via the CLI's default
// route. The rewrite cannot live inside the mutually recursive group
// above — replacing q_pattern breaks its termination metric — so these
// top-level entries do it once and delegate. Consumers call these.
let run_select_query_backend_dataset (q : query) (dsb : dataset_backend)
  : option solution_sequence =
  eval_select_query_backend_dataset
    ({ q with q_pattern = rewrite_query_bnodes_pattern q.q_pattern }) dsb

let run_ask_query_backend_dataset (q : query) (dsb : dataset_backend)
  : option bool =
  eval_ask_query_backend_dataset
    ({ q with q_pattern = rewrite_query_bnodes_pattern q.q_pattern }) dsb
