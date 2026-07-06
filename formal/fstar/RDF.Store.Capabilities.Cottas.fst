module RDF.Store.Capabilities.Cottas

(* COTTAS-on-disk `store_caps` builder — stage U1 of
   docs/designissues/2026-07-06-unified-store-architecture.md, §3.2.

   Split out of `RDF.Store.Capabilities` on purpose (task justification,
   also anticipated by the design doc's own §6.2 risk mitigation:
   "the record type and the in-memory builder are Unix-free; the
   COTTAS/HDT builders live in their own modules ... already excluded
   from the browser build"). `RDF.CottasStore` reaches the mmap/file-
   range `assume val`s that the jsoo build cannot link; keeping this
   builder in its own module means a future JS/wasm module list can
   include `RDF.Store.Capabilities` (types + in-memory builder) while
   excluding this file, exactly as it excludes `RDF.CottasStore` today.

   Every field below wraps the SAME entry points the `GB_CottasOnDisk`
   arms of SPARQL11.Store.fst's six dispatchers call today (§1.5 /
   §3.2 table of the design doc) — zero new logic, one-to-one mapping.
   This is the base (read-only) COTTAS capability set: `scf_supports_
   update = false`, matching design doc §3.2 ("The bare COTTAS base
   carries st_write = None"). The read-write COTTAS+delta view is a
   later `overlay` composition (design doc §3.3 / stage D-overlay), not
   this builder.
*)

open RDF.Graph.Executable
open SPARQL11.Algebra
open RDF.CottasStore
open RDF.Store.Capabilities

let caps_of_cottas (cods : cottas_ondisk_store) (scope : cottas_ondisk_graph_scope)
  : Tot store_caps =
  {
    sc_flags = {
      scf_supports_named_graphs = true;   // COTTAS carries a graph column (cottas-format-v1 §6)
      scf_supports_update = false;        // bare COTTAS base is read-only (design doc §3.2)
      scf_streaming_shapes = true;
      scf_estimate_is_exact = false;      // bounds-present branch approximates (SPARQL11.Store.fst:217)
      scf_can_report_decode_fail = true;
    };

    // Realises the GB_CottasOnDisk arm of backend_search
    // (SPARQL11.Store.fst:114-126).
    // 2026-07-06: `cottas_ondisk_search[_limited]` now return
    // `cottas_qp_row_tok` (raw column strings), not the id-based
    // `cottas_qp_row` — a matched row's subject/predicate/object no
    // longer round-trips through the corpus-wide `ondisk_lookup_*_id_
    // global`/Bet7 tables (see RDF.CottasStore.fst's `cottas_qp_row_tok`
    // banner comment for the profiling that motivated this). Consumed
    // here via `cottas_ondisk_rows_tok_to_triples`, the tok-shaped
    // sibling of the old `cottas_ondisk_rows_to_triples`.
    sc_solve =
      (fun b ->
        match cottas_ondisk_build_bound_qp_opt cods b.bs b.bp b.bo scope with
        | None -> []
        | Some bound -> cottas_ondisk_rows_tok_to_triples (cottas_ondisk_search cods bound));

    // Real LIMIT pushdown — realises the GB_CottasOnDisk arm of
    // backend_search_limited (SPARQL11.Store.fst:171-179).
    sc_solve_limited =
      (fun b n ->
        match cottas_ondisk_build_bound_qp_opt cods b.bs b.bp b.bo scope with
        | None -> []
        | Some bound -> cottas_ondisk_rows_tok_to_triples (cottas_ondisk_search_limited cods bound n));

    // Realises the GB_CottasOnDisk arm of backend_estimate
    // (SPARQL11.Store.fst:207-210).
    sc_estimate =
      (fun b ->
        match cottas_ondisk_build_bound_qp_opt cods b.bs b.bp b.bo scope with
        | None -> 0
        | Some bound -> cottas_ondisk_estimate cods bound);

    // Realises the GB_CottasOnDisk arm of backend_count_exact
    // (SPARQL11.Store.fst:231-234).
    sc_count_exact =
      (fun b ->
        match cottas_ondisk_build_bound_qp_opt cods b.bs b.bp b.bo scope with
        | None -> 0
        | Some bound -> cottas_ondisk_count_exact cods bound);

    // Realises the GB_CottasOnDisk arm of backend_predicate_present
    // (SPARQL11.Store.fst:269-270) — note the existing dispatcher
    // ignores the graph scope here too; this wrapper matches that
    // exactly rather than "fixing" it (zero new logic).
    sc_predicate_present = (fun pred -> cottas_ondisk_predicate_present cods pred);

    // Realises the GB_CottasOnDisk arm of backend_decode_failure
    // (SPARQL11.Store.fst:292-293).
    sc_decode_failure = (fun () -> cottas_ondisk_has_decode_failure cods.cods_handle);
  }
