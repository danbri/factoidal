open Prims
let rec delta_caps_take_n : 'a . Prims.nat -> 'a Prims.list -> 'a Prims.list
  =
  fun n xs ->
    if n = Prims.int_zero
    then []
    else
      (match xs with
       | [] -> []
       | hd::tl -> hd :: (delta_caps_take_n (n - Prims.int_one) tl))
let overlay (base : RDF_Store_Capabilities.store_caps)
  (delta : RDF_Store_Columnar_DeltaMerge.delta_resolved) :
  RDF_Store_Capabilities.store_caps=
  if RDF_Store_Columnar_DeltaMerge.delta_resolved_is_empty delta
  then
    {
      RDF_Store_Capabilities.sc_flags =
        (let uu___ = base.RDF_Store_Capabilities.sc_flags in
         {
           RDF_Store_Capabilities.scf_supports_named_graphs =
             (uu___.RDF_Store_Capabilities.scf_supports_named_graphs);
           RDF_Store_Capabilities.scf_supports_update = true;
           RDF_Store_Capabilities.scf_streaming_shapes =
             (uu___.RDF_Store_Capabilities.scf_streaming_shapes);
           RDF_Store_Capabilities.scf_estimate_is_exact =
             (uu___.RDF_Store_Capabilities.scf_estimate_is_exact);
           RDF_Store_Capabilities.scf_can_report_decode_fail =
             (uu___.RDF_Store_Capabilities.scf_can_report_decode_fail)
         });
      RDF_Store_Capabilities.sc_solve =
        (base.RDF_Store_Capabilities.sc_solve);
      RDF_Store_Capabilities.sc_solve_limited =
        (base.RDF_Store_Capabilities.sc_solve_limited);
      RDF_Store_Capabilities.sc_estimate =
        (base.RDF_Store_Capabilities.sc_estimate);
      RDF_Store_Capabilities.sc_count_exact =
        (base.RDF_Store_Capabilities.sc_count_exact);
      RDF_Store_Capabilities.sc_predicate_present =
        (base.RDF_Store_Capabilities.sc_predicate_present);
      RDF_Store_Capabilities.sc_decode_failure =
        (base.RDF_Store_Capabilities.sc_decode_failure)
    }
  else
    {
      RDF_Store_Capabilities.sc_flags =
        ((let uu___1 = base.RDF_Store_Capabilities.sc_flags in
          {
            RDF_Store_Capabilities.scf_supports_named_graphs =
              (uu___1.RDF_Store_Capabilities.scf_supports_named_graphs);
            RDF_Store_Capabilities.scf_supports_update = true;
            RDF_Store_Capabilities.scf_streaming_shapes =
              (uu___1.RDF_Store_Capabilities.scf_streaming_shapes);
            RDF_Store_Capabilities.scf_estimate_is_exact =
              (uu___1.RDF_Store_Capabilities.scf_estimate_is_exact);
            RDF_Store_Capabilities.scf_can_report_decode_fail =
              (uu___1.RDF_Store_Capabilities.scf_can_report_decode_fail)
          }));
      RDF_Store_Capabilities.sc_solve =
        ((fun b ->
            RDF_Store_Columnar_DeltaMerge.merge_on_read
              (base.RDF_Store_Capabilities.sc_solve b) delta b));
      RDF_Store_Capabilities.sc_solve_limited =
        ((fun b n ->
            delta_caps_take_n n
              (RDF_Store_Columnar_DeltaMerge.merge_on_read
                 (base.RDF_Store_Capabilities.sc_solve b) delta b)));
      RDF_Store_Capabilities.sc_estimate =
        ((fun b ->
            (base.RDF_Store_Capabilities.sc_estimate b) +
              (RDF_Store_Columnar_DeltaMerge.delta_matching_count delta b)));
      RDF_Store_Capabilities.sc_count_exact =
        ((fun b ->
            FStar_List_Tot_Base.length
              (RDF_Store_Columnar_DeltaMerge.merge_on_read
                 (base.RDF_Store_Capabilities.sc_solve b) delta b)));
      RDF_Store_Capabilities.sc_predicate_present =
        ((fun pred ->
            (base.RDF_Store_Capabilities.sc_predicate_present pred) ||
              (RDF_Store_Columnar_DeltaMerge.delta_added_has_predicate
                 delta.RDF_Store_Columnar_DeltaMerge.dr_added pred)));
      RDF_Store_Capabilities.sc_decode_failure =
        (base.RDF_Store_Capabilities.sc_decode_failure)
    }
