open Prims
let caps_of_cottas (cods : RDF_CottasStore.cottas_ondisk_store)
  (scope : RDF_CottasStore.cottas_ondisk_graph_scope) :
  RDF_Store_Capabilities.store_caps=
  {
    RDF_Store_Capabilities.sc_flags =
      {
        RDF_Store_Capabilities.scf_supports_named_graphs = true;
        RDF_Store_Capabilities.scf_supports_update = false;
        RDF_Store_Capabilities.scf_streaming_shapes = true;
        RDF_Store_Capabilities.scf_estimate_is_exact = false;
        RDF_Store_Capabilities.scf_can_report_decode_fail = true
      };
    RDF_Store_Capabilities.sc_solve =
      (fun b ->
         let bound =
           RDF_CottasStore.cottas_ondisk_build_bound_qp_tok
             b.SPARQL11_Algebra.bs b.SPARQL11_Algebra.bp
             b.SPARQL11_Algebra.bo scope in
         RDF_CottasStore.cottas_ondisk_rows_tok_to_triples
           (RDF_CottasStore.cottas_ondisk_search_tok cods bound));
    RDF_Store_Capabilities.sc_solve_limited =
      (fun b n ->
         let bound =
           RDF_CottasStore.cottas_ondisk_build_bound_qp_tok
             b.SPARQL11_Algebra.bs b.SPARQL11_Algebra.bp
             b.SPARQL11_Algebra.bo scope in
         RDF_CottasStore.cottas_ondisk_rows_tok_to_triples
           (RDF_CottasStore.cottas_ondisk_search_limited_tok cods bound n));
    RDF_Store_Capabilities.sc_estimate =
      (fun b ->
         let bound =
           RDF_CottasStore.cottas_ondisk_build_bound_qp_tok
             b.SPARQL11_Algebra.bs b.SPARQL11_Algebra.bp
             b.SPARQL11_Algebra.bo scope in
         RDF_CottasStore.cottas_ondisk_estimate_tok cods bound);
    RDF_Store_Capabilities.sc_count_exact =
      (fun b ->
         let bound =
           RDF_CottasStore.cottas_ondisk_build_bound_qp_tok
             b.SPARQL11_Algebra.bs b.SPARQL11_Algebra.bp
             b.SPARQL11_Algebra.bo scope in
         RDF_CottasStore.cottas_ondisk_count_exact_tok cods bound);
    RDF_Store_Capabilities.sc_predicate_present =
      (fun pred -> RDF_CottasStore.cottas_ondisk_predicate_present cods pred);
    RDF_Store_Capabilities.sc_decode_failure =
      (fun uu___ ->
         RDF_CottasStore.cottas_ondisk_has_decode_failure
           cods.RDF_CottasStore.cods_handle)
  }
