module RDF.Store.Capabilities

(* Unified store-capability seam — stage U1 of
   docs/designissues/2026-07-06-unified-store-architecture.md.

   One typed record of already-existing backend entry points, read by
   the planner/evaluator instead of matching on the `graph_backend`
   tag (SPARQL11.Store.fst:23-34). This module introduces ONLY the
   types + the in-memory builder; no caller is rewired yet (that is
   stage U2 — see the doc's migration table, §5). The COTTAS-on-disk
   builder lives in the sibling module `RDF.Store.Capabilities.Cottas`
   (not here) so that THIS module stays Unix/mmap-free and safe to
   list in the JS/wasm build (design doc §6.2's mitigation: "the
   record type and the in-memory builder are Unix-free; the
   COTTAS/HDT builders live in their own modules").

   DAG position / transitional import (design doc §5.7): the record's
   `sc_solve`/`sc_estimate`/`sc_count_exact` fields all take
   `triple_pattern_bound`, an AST/term type that foundational-core-
   refactor step 4 will extract out of `SPARQL11.Algebra.fst` into a
   new `SPARQL.Terms.fst`. Step 4 has not landed yet, so — exactly as
   the design doc's own contingency spells out — this module opens
   `SPARQL11.Algebra` transitionally instead of `SPARQL.Terms`. This
   keeps `RDF.Store.Capabilities` BELOW `SPARQL11.Store` in the module
   DAG (`SPARQL11.Algebra` does not import `SPARQL11.Store`), the same
   position `SPARQL.Plan.Streamable` already holds (that module's own
   banner, SPARQL.Plan.Streamable.fst:118-122). When step 4 lands this
   becomes a one-line `open` swap, per the doc.

   Adjustments from the design doc's F* sketch (§2), disclosed per
   task instructions:
     1. The sketch's `open SPARQL.Terms` is `open RDF.Graph.Executable`
        + `open SPARQL11.Algebra` here (transitional import above; the
        `RDF.Graph.Executable` open is required alongside
        `SPARQL11.Algebra` because F* does not chain a module's own
        `open`s to a third importer — `SPARQL.Plan.Streamable` opens
        both for the same reason, see its lines 87-88).
     2. `store_write_caps`'s `swc_apply_delta`/`swc_delta_stats` still
        reference `RDF.Store.Columnar.DeltaLog` (aliased `DL`, exactly
        as the sketch has it) — that module is mid-flight under a
        sibling task (DeltaLog stage 2) but its public `delta_entry`
        type is already in-tree and stable enough to reference.
     3. `sc_solve_limited`'s stated default realisation
        (`list_take_n n (sc_solve b)`) reuses
        `SPARQL11.Store.list_take_n`, which this module cannot import
        (it would invert the DAG edge above). `caps_take_n` below is a
        local, verified copy of the same total function — the same
        "duplicate rather than import upward" trade the design doc
        already accepts for the two streaming-shape detector families
        (§1.2), not new logic.
     4. `union_caps` is written per §4 ("one `store_caps` whose
        `sc_solve` concatenates the members'") and open decision 2
        (§7): it builds a READ-ONLY `store_caps` (no `store`-level
        combinator, no write semantics for a federation). It is
        UNTESTED in this stage — U1's equivalence-test floor (task
        item 3) covers only the two single-backend builders; wiring
        and testing `union_caps` is U2/U4 territory (design doc §4,
        "the six `union_*` twins fold into `union_caps`").
*)

open FStar.List.Tot
open RDF.Graph.Executable
open SPARQL11.Algebra

open FStar.All

module DL = RDF.Store.Columnar.DeltaLog

// --------------------------------------------------------------------
// Advertised capability flags. The planner/evaluator reads THESE
// instead of matching on a backend tag. Each answers a policy question
// the six tag-dispatchers (SPARQL11.Store.fst §1.1) answer by
// construction today. Verbatim from the design doc's sketch (§2).
// --------------------------------------------------------------------
noeq type store_caps_flags = {
  // Can this store hold named graphs, or only a default graph? A single
  // HDT 1.0 file is triples-only (hdt-program-plan "Out of scope");
  // COTTAS carries a graph column (cottas-format-v1 §6).
  scf_supports_named_graphs : bool;

  // Does this store have a durable write path (the write seam below)?
  // In-memory and COTTAS+delta: yes. HDT and a bare COTTAS base: no.
  scf_supports_update       : bool;

  // Can it answer a bounded COUNT-star/ASK without materialising rows?
  // Governs whether SPARQL.Plan.Streamable's plan is dispatched here.
  scf_streaming_shapes      : bool;

  // Is sc_estimate exact, or a join-order hint that may approximate?
  // GB_List/GB_Indexed: exact (backend_count_exact wildcard falls back
  // to backend_estimate, SPARQL11.Store.fst:236). GB_CottasOnDisk: not
  // exact (bounds-present branch approximates, SPARQL11.Store.fst:217).
  scf_estimate_is_exact     : bool;

  // Can it distinguish "genuinely empty" from "column I could not
  // decode" (issue #269)? Only the columnar on-disk reader can.
  scf_can_report_decode_fail : bool;
}

// --------------------------------------------------------------------
// The READ seam. Every backend realises it. Each field is the entry
// point that backend ALREADY has; the record is the one indirection
// that replaces `match gb with`.
// --------------------------------------------------------------------
noeq type store_caps = {
  sc_flags : store_caps_flags;

  // Streaming pattern solve: bounds in, matched triples out. The result
  // is the backend's own already-decoded triples; the evaluator never
  // sees rows/cells/dictionary ids. Realises backend_search's arm
  // (SPARQL11.Store.fst:103).
  sc_solve : triple_pattern_bound -> Tot (list triple);

  // LIMIT-pushdown solve. A backend with real pushdown overrides
  // (COTTAS on-disk, RDF.CottasStore.fst:1626); the default realisation
  // is `caps_take_n n (sc_solve b)`, exactly the current non-disk
  // wildcard (SPARQL11.Store.fst:185-188).
  sc_solve_limited : triple_pattern_bound -> nat -> Tot (list triple);

  // Join-order estimate; MAY approximate iff scf_estimate_is_exact=false.
  // Realises backend_estimate (SPARQL11.Store.fst:197).
  sc_estimate : triple_pattern_bound -> Tot nat;

  // Exact count for result-producing callers (COUNT-star, per-graph
  // GROUP BY). Realises backend_count_exact (SPARQL11.Store.fst:229);
  // the in-memory default IS sc_estimate.
  sc_count_exact : triple_pattern_bound -> Tot nat;

  // Predicate-presence short-circuit (Bloom/dictionary probe). Realises
  // backend_predicate_present (SPARQL11.Store.fst:246).
  sc_predicate_present : wf_iri -> Tot bool;

  // Did a read touch a column this reader could not decode? Only a
  // columnar reader returns true; the default is a constant `false`,
  // the current non-disk wildcard (SPARQL11.Store.fst:296). Realises
  // backend_decode_failure (SPARQL11.Store.fst:290).
  sc_decode_failure : unit -> Tot bool;
}

// --------------------------------------------------------------------
// The WRITE seam. ONLY a read-write backend constructs this. A
// read-only backend advertises scf_supports_update=false and carries
// None: a read-only store never allocates a delta log, and the
// in-memory store never runs the fsync/rename protocol.
// --------------------------------------------------------------------
noeq type store_write_caps = {
  // Apply one committed SPARQL Update request's ops and return the
  // post-update READ seam. For COTTAS+delta this appends+fsyncs a
  // DL.delta_batch and returns base (+) delta (durable-update
  // §3.3/§4.1); for the in-memory store it rebuilds the indexed_graph.
  // ML because durability is I/O; the byte layout it writes is F*
  // (DL.serialize_*).
  swc_apply_delta : list DL.delta_entry -> ML store_caps;

  // Optional planner input: exact count of delta entries matching a
  // bound (durable-update §4.4). None just after compaction (empty
  // delta), so a store with no delta pays nothing.
  swc_delta_stats : option (triple_pattern_bound -> Tot nat);
}

// A store is its read seam plus, iff read-write, its write seam.
noeq type store = {
  st_read  : store_caps;
  st_write : option store_write_caps;   // Some iff sc_flags.scf_supports_update
}

// --------------------------------------------------------------------
// Local copy of SPARQL11.Store.fst's `list_take_n` (adjustment #3
// above): same total truncation function, duplicated because this
// module sits below SPARQL11.Store in the DAG and cannot import it.
// --------------------------------------------------------------------
let rec caps_take_n (#a:Type) (n : nat) (xs : list a)
  : Tot (list a) (decreases n) =
  if n = 0 then []
  else
    match xs with
    | [] -> []
    | hd :: tl -> hd :: caps_take_n (n - 1) tl

// --------------------------------------------------------------------
// union_caps (design doc §4 / §7 open decision 2): a read-only
// combinator over a list of read seams. Mirrors the union_backend_*
// family's per-field arithmetic (SPARQL11.Store.fst:94-296) without
// introducing a `GB_Union`-shaped constructor. UNTESTED in stage U1
// (adjustment #4 above) — no caller builds a union today.
// --------------------------------------------------------------------
let rec union_solve (members : list store_caps) (b : triple_pattern_bound)
  : Tot (list triple) (decreases members) =
  match members with
  | [] -> []
  | m :: rest -> m.sc_solve b @ union_solve rest b

let rec union_estimate (members : list store_caps) (b : triple_pattern_bound)
  : Tot nat (decreases members) =
  match members with
  | [] -> 0
  | m :: rest -> m.sc_estimate b + union_estimate rest b

let rec union_count_exact (members : list store_caps) (b : triple_pattern_bound)
  : Tot nat (decreases members) =
  match members with
  | [] -> 0
  | m :: rest -> m.sc_count_exact b + union_count_exact rest b

let rec union_predicate_present (members : list store_caps) (pred : wf_iri)
  : Tot bool (decreases members) =
  match members with
  | [] -> false
  | m :: rest -> if m.sc_predicate_present pred then true else union_predicate_present rest pred

let rec union_decode_failure (members : list store_caps)
  : Tot bool (decreases members) =
  match members with
  | [] -> false
  | m :: rest -> m.sc_decode_failure () || union_decode_failure rest

let union_caps (members : list store_caps) : Tot store_caps =
  {
    sc_flags = {
      scf_supports_named_graphs = true;
      scf_supports_update = false;   // read-side federation only (§7 open decision 2)
      scf_streaming_shapes = true;
      scf_estimate_is_exact = false; // sum of possibly-inexact members is not claimed exact
      scf_can_report_decode_fail = true;
    };
    sc_solve = (fun b -> union_solve members b);
    sc_solve_limited = (fun b n -> caps_take_n n (union_solve members b));
    sc_estimate = (fun b -> union_estimate members b);
    sc_count_exact = (fun b -> union_count_exact members b);
    sc_predicate_present = (fun pred -> union_predicate_present members pred);
    sc_decode_failure = (fun () -> union_decode_failure members);
  }

// ======================================================================
// Builder: in-memory backend via RDF.Indexed (design doc §3.1).
// Every field wraps the SAME functions `SPARQL11.Store.fst`'s
// GB_Indexed arms call today — zero new logic.
// ======================================================================
let caps_of_indexed (ig : indexed_graph) : Tot store_caps =
  {
    sc_flags = {
      scf_supports_named_graphs = true;   // a dataset is default + named indexed_graphs
      scf_supports_update = true;         // rebuild via RDF.Indexed.build_indexed
      scf_streaming_shapes = true;
      scf_estimate_is_exact = true;
      scf_can_report_decode_fail = false;
    };
    sc_solve = (fun b -> ig_search ig b);
    sc_solve_limited = (fun b n -> caps_take_n n (ig_search ig b));
    sc_estimate = (fun b -> ig_estimate ig b);
    sc_count_exact = (fun b -> ig_estimate ig b);  // in-memory estimate is already exact
    sc_predicate_present =
      (fun pred -> ig_estimate ig ({ bs = None; bp = Some pred; bo = None }) > 0);
    sc_decode_failure = (fun () -> false);
  }
