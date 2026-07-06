open Prims
type graph_backend =
  | GB_List of RDF_Graph.rdf_graph 
  | GB_Indexed of RDF_Indexed.indexed_graph 
  | GB_HDT of Parser_BallyhooHDT.hdt_graph_store 
  | GB_COTTAS of Parser_BallyhooCOTTAS.cottas_dataset_store * RDF_Term.iri
  FStar_Pervasives_Native.option 
  | GB_CottasOnDisk of RDF_CottasStore.cottas_ondisk_store *
  RDF_CottasStore.cottas_ondisk_graph_scope 
  | GB_CottasOnDiskDelta of RDF_CottasStore.cottas_ondisk_store *
  RDF_CottasStore.cottas_ondisk_graph_scope *
  RDF_Store_Columnar_DeltaMerge.delta_resolved 
  | GB_Union of graph_backend Prims.list 
let uu___is_GB_List (projectee : graph_backend) : Prims.bool=
  match projectee with | GB_List _0 -> true | uu___ -> false
let __proj__GB_List__item___0 (projectee : graph_backend) :
  RDF_Graph.rdf_graph= match projectee with | GB_List _0 -> _0
let uu___is_GB_Indexed (projectee : graph_backend) : Prims.bool=
  match projectee with | GB_Indexed _0 -> true | uu___ -> false
let __proj__GB_Indexed__item___0 (projectee : graph_backend) :
  RDF_Indexed.indexed_graph= match projectee with | GB_Indexed _0 -> _0
let uu___is_GB_HDT (projectee : graph_backend) : Prims.bool=
  match projectee with | GB_HDT _0 -> true | uu___ -> false
let __proj__GB_HDT__item___0 (projectee : graph_backend) :
  Parser_BallyhooHDT.hdt_graph_store= match projectee with | GB_HDT _0 -> _0
let uu___is_GB_COTTAS (projectee : graph_backend) : Prims.bool=
  match projectee with | GB_COTTAS (_0, _1) -> true | uu___ -> false
let __proj__GB_COTTAS__item___0 (projectee : graph_backend) :
  Parser_BallyhooCOTTAS.cottas_dataset_store=
  match projectee with | GB_COTTAS (_0, _1) -> _0
let __proj__GB_COTTAS__item___1 (projectee : graph_backend) :
  RDF_Term.iri FStar_Pervasives_Native.option=
  match projectee with | GB_COTTAS (_0, _1) -> _1
let uu___is_GB_CottasOnDisk (projectee : graph_backend) : Prims.bool=
  match projectee with | GB_CottasOnDisk (_0, _1) -> true | uu___ -> false
let __proj__GB_CottasOnDisk__item___0 (projectee : graph_backend) :
  RDF_CottasStore.cottas_ondisk_store=
  match projectee with | GB_CottasOnDisk (_0, _1) -> _0
let __proj__GB_CottasOnDisk__item___1 (projectee : graph_backend) :
  RDF_CottasStore.cottas_ondisk_graph_scope=
  match projectee with | GB_CottasOnDisk (_0, _1) -> _1
let uu___is_GB_CottasOnDiskDelta (projectee : graph_backend) : Prims.bool=
  match projectee with
  | GB_CottasOnDiskDelta (_0, _1, _2) -> true
  | uu___ -> false
let __proj__GB_CottasOnDiskDelta__item___0 (projectee : graph_backend) :
  RDF_CottasStore.cottas_ondisk_store=
  match projectee with | GB_CottasOnDiskDelta (_0, _1, _2) -> _0
let __proj__GB_CottasOnDiskDelta__item___1 (projectee : graph_backend) :
  RDF_CottasStore.cottas_ondisk_graph_scope=
  match projectee with | GB_CottasOnDiskDelta (_0, _1, _2) -> _1
let __proj__GB_CottasOnDiskDelta__item___2 (projectee : graph_backend) :
  RDF_Store_Columnar_DeltaMerge.delta_resolved=
  match projectee with | GB_CottasOnDiskDelta (_0, _1, _2) -> _2
let uu___is_GB_Union (projectee : graph_backend) : Prims.bool=
  match projectee with | GB_Union _0 -> true | uu___ -> false
let __proj__GB_Union__item___0 (projectee : graph_backend) :
  graph_backend Prims.list= match projectee with | GB_Union _0 -> _0
type named_graph_backend =
  {
  ngb_name: RDF_Term.iri ;
  ngb_graph: graph_backend }
let __proj__Mknamed_graph_backend__item__ngb_name
  (projectee : named_graph_backend) : RDF_Term.iri=
  match projectee with | { ngb_name; ngb_graph;_} -> ngb_name
let __proj__Mknamed_graph_backend__item__ngb_graph
  (projectee : named_graph_backend) : graph_backend=
  match projectee with | { ngb_name; ngb_graph;_} -> ngb_graph
type dataset_backend =
  {
  dsb_default: graph_backend ;
  dsb_named: named_graph_backend Prims.list }
let __proj__Mkdataset_backend__item__dsb_default
  (projectee : dataset_backend) : graph_backend=
  match projectee with | { dsb_default; dsb_named;_} -> dsb_default
let __proj__Mkdataset_backend__item__dsb_named (projectee : dataset_backend)
  : named_graph_backend Prims.list=
  match projectee with | { dsb_default; dsb_named;_} -> dsb_named
let indexed_graph_backend (g : RDF_Graph.rdf_graph) : graph_backend=
  GB_Indexed (RDF_Indexed.build_indexed g)
let indexed_dataset_backend (ds : RDF_Graph.rdf_dataset) : dataset_backend=
  {
    dsb_default = (indexed_graph_backend ds.RDF_Graph.ds_default);
    dsb_named =
      (FStar_List_Tot_Base.map
         (fun ng ->
            {
              ngb_name = (ng.RDF_Graph.ng_name);
              ngb_graph = (indexed_graph_backend ng.RDF_Graph.ng_graph)
            }) ds.RDF_Graph.ds_named)
  }
let cottas_ondisk_dataset_backend
  (cods : RDF_CottasStore.cottas_ondisk_store) : dataset_backend=
  {
    dsb_default = (GB_CottasOnDisk (cods, RDF_CottasStore.COS_DefaultOnly));
    dsb_named =
      (FStar_List_Tot_Base.map
         (fun g ->
            let uu___ = g in
            match uu___ with
            | (gname, uu___1) ->
                {
                  ngb_name = gname;
                  ngb_graph =
                    (GB_CottasOnDisk
                       (cods, (RDF_CottasStore.COS_NamedGraph gname)))
                }) (RDF_CottasStore.cottas_ondisk_named_graphs cods))
  }
let cottas_with_delta_dataset_backend
  (cods : RDF_CottasStore.cottas_ondisk_store) (log_path : Prims.string)
  (compacted_epoch : Prims.nat FStar_Pervasives_Native.option) :
  dataset_backend=
  let log_bytes = RDF_Store_Columnar_DeltaLog.delta_log_read_all log_path in
  let raw_batches =
    match RDF_Store_Columnar_DeltaLog.parse_log log_bytes with
    | FStar_Pervasives_Native.Some (bs, _leftover) -> bs
    | FStar_Pervasives_Native.None -> [] in
  let batches =
    RDF_Store_Columnar_DeltaLog.filter_batches_since_epoch compacted_epoch
      raw_batches in
  let base_named = RDF_CottasStore.cottas_ondisk_named_graphs cods in
  let default_delta =
    RDF_Store_Columnar_DeltaMerge.fold_delta_batches batches
      FStar_Pervasives_Native.None in
  let base_named_entries =
    FStar_List_Tot_Base.map
      (fun g ->
         let uu___ = g in
         match uu___ with
         | (gname, uu___1) ->
             let gdelta =
               RDF_Store_Columnar_DeltaMerge.fold_delta_batches batches
                 (FStar_Pervasives_Native.Some gname) in
             {
               ngb_name = gname;
               ngb_graph =
                 (GB_CottasOnDiskDelta
                    (cods, (RDF_CottasStore.COS_NamedGraph gname), gdelta))
             }) base_named in
  let base_names =
    FStar_List_Tot_Base.map (fun g -> FStar_Pervasives_Native.fst g)
      base_named in
  let delta_only_names =
    FStar_List_Tot_Base.filter
      (fun gi ->
         Prims.op_Negation
           (FStar_List_Tot_Base.existsb (fun bn -> bn = gi) base_names))
      (RDF_Store_Columnar_DeltaMerge.delta_batches_named_graphs batches) in
  let delta_only_entries =
    FStar_List_Tot_Base.map
      (fun gname ->
         let gdelta =
           RDF_Store_Columnar_DeltaMerge.fold_delta_batches batches
             (FStar_Pervasives_Native.Some gname) in
         {
           ngb_name = gname;
           ngb_graph =
             (GB_CottasOnDiskDelta
                (cods, (RDF_CottasStore.COS_NamedGraph gname), gdelta))
         }) delta_only_names in
  {
    dsb_default =
      (GB_CottasOnDiskDelta
         (cods, RDF_CottasStore.COS_DefaultOnly, default_delta));
    dsb_named =
      (FStar_List_Tot_Base.append base_named_entries delta_only_entries)
  }
let rec list_take_n : 'a . Prims.nat -> 'a Prims.list -> 'a Prims.list =
  fun n xs ->
    if n = Prims.int_zero
    then []
    else
      (match xs with
       | [] -> []
       | hd::tl -> hd :: (list_take_n (n - Prims.int_one) tl))
let rec caps_of_backend (gb : graph_backend) :
  RDF_Store_Capabilities.store_caps=
  match gb with
  | GB_List g ->
      let st = SPARQL11_Algebra.graph_to_store g in
      {
        RDF_Store_Capabilities.sc_flags =
          {
            RDF_Store_Capabilities.scf_supports_named_graphs = false;
            RDF_Store_Capabilities.scf_supports_update = false;
            RDF_Store_Capabilities.scf_streaming_shapes = true;
            RDF_Store_Capabilities.scf_estimate_is_exact = true;
            RDF_Store_Capabilities.scf_can_report_decode_fail = false
          };
        RDF_Store_Capabilities.sc_solve =
          ((fun b -> SPARQL11_Algebra.store_search st b));
        RDF_Store_Capabilities.sc_solve_limited =
          ((fun b n -> list_take_n n (SPARQL11_Algebra.store_search st b)));
        RDF_Store_Capabilities.sc_estimate =
          ((fun b -> SPARQL11_Algebra.store_estimate st b));
        RDF_Store_Capabilities.sc_count_exact =
          ((fun b -> SPARQL11_Algebra.store_estimate st b));
        RDF_Store_Capabilities.sc_predicate_present =
          ((fun pred ->
              (SPARQL11_Algebra.store_estimate st
                 {
                   SPARQL11_Algebra.bs = FStar_Pervasives_Native.None;
                   SPARQL11_Algebra.bp = (FStar_Pervasives_Native.Some pred);
                   SPARQL11_Algebra.bo = FStar_Pervasives_Native.None
                 })
                > Prims.int_zero));
        RDF_Store_Capabilities.sc_decode_failure = ((fun uu___ -> false))
      }
  | GB_Indexed ig -> RDF_Store_Capabilities.caps_of_indexed ig
  | GB_HDT hgs ->
      {
        RDF_Store_Capabilities.sc_flags =
          {
            RDF_Store_Capabilities.scf_supports_named_graphs = false;
            RDF_Store_Capabilities.scf_supports_update = false;
            RDF_Store_Capabilities.scf_streaming_shapes = true;
            RDF_Store_Capabilities.scf_estimate_is_exact = true;
            RDF_Store_Capabilities.scf_can_report_decode_fail = false
          };
        RDF_Store_Capabilities.sc_solve =
          ((fun b ->
              Parser_BallyhooHDT.hdt_search_triples hgs b.SPARQL11_Algebra.bs
                b.SPARQL11_Algebra.bp b.SPARQL11_Algebra.bo));
        RDF_Store_Capabilities.sc_solve_limited =
          ((fun b n ->
              list_take_n n
                (Parser_BallyhooHDT.hdt_search_triples hgs
                   b.SPARQL11_Algebra.bs b.SPARQL11_Algebra.bp
                   b.SPARQL11_Algebra.bo)));
        RDF_Store_Capabilities.sc_estimate =
          ((fun b ->
              Parser_BallyhooHDT.hdt_estimate hgs
                (Parser_BallyhooHDT.hdt_build_bound_tp hgs
                   b.SPARQL11_Algebra.bs b.SPARQL11_Algebra.bp
                   b.SPARQL11_Algebra.bo)));
        RDF_Store_Capabilities.sc_count_exact =
          ((fun b ->
              Parser_BallyhooHDT.hdt_estimate hgs
                (Parser_BallyhooHDT.hdt_build_bound_tp hgs
                   b.SPARQL11_Algebra.bs b.SPARQL11_Algebra.bp
                   b.SPARQL11_Algebra.bo)));
        RDF_Store_Capabilities.sc_predicate_present =
          ((fun pred -> Parser_BallyhooHDT.hdt_predicate_present hgs pred));
        RDF_Store_Capabilities.sc_decode_failure = ((fun uu___ -> false))
      }
  | GB_COTTAS (cds, graph_name) ->
      {
        RDF_Store_Capabilities.sc_flags =
          {
            RDF_Store_Capabilities.scf_supports_named_graphs = true;
            RDF_Store_Capabilities.scf_supports_update = false;
            RDF_Store_Capabilities.scf_streaming_shapes = true;
            RDF_Store_Capabilities.scf_estimate_is_exact = true;
            RDF_Store_Capabilities.scf_can_report_decode_fail = false
          };
        RDF_Store_Capabilities.sc_solve =
          ((fun b ->
              let rows =
                Parser_BallyhooCOTTAS.cottas_search cds
                  (Parser_BallyhooCOTTAS.cottas_build_bound_qp cds
                     b.SPARQL11_Algebra.bs b.SPARQL11_Algebra.bp
                     b.SPARQL11_Algebra.bo graph_name) in
              FStar_List_Tot_Base.map FStar_Pervasives_Native.fst
                (Parser_BallyhooCOTTAS.cottas_rows_to_quads cds rows)));
        RDF_Store_Capabilities.sc_solve_limited =
          ((fun b n ->
              let rows =
                Parser_BallyhooCOTTAS.cottas_search cds
                  (Parser_BallyhooCOTTAS.cottas_build_bound_qp cds
                     b.SPARQL11_Algebra.bs b.SPARQL11_Algebra.bp
                     b.SPARQL11_Algebra.bo graph_name) in
              list_take_n n
                (FStar_List_Tot_Base.map FStar_Pervasives_Native.fst
                   (Parser_BallyhooCOTTAS.cottas_rows_to_quads cds rows))));
        RDF_Store_Capabilities.sc_estimate =
          ((fun b ->
              Parser_BallyhooCOTTAS.cottas_estimate cds
                (Parser_BallyhooCOTTAS.cottas_build_bound_qp cds
                   b.SPARQL11_Algebra.bs b.SPARQL11_Algebra.bp
                   b.SPARQL11_Algebra.bo graph_name)));
        RDF_Store_Capabilities.sc_count_exact =
          ((fun b ->
              Parser_BallyhooCOTTAS.cottas_estimate cds
                (Parser_BallyhooCOTTAS.cottas_build_bound_qp cds
                   b.SPARQL11_Algebra.bs b.SPARQL11_Algebra.bp
                   b.SPARQL11_Algebra.bo graph_name)));
        RDF_Store_Capabilities.sc_predicate_present =
          ((fun pred ->
              (Parser_BallyhooCOTTAS.cottas_estimate cds
                 (Parser_BallyhooCOTTAS.cottas_build_bound_qp cds
                    FStar_Pervasives_Native.None
                    (FStar_Pervasives_Native.Some pred)
                    FStar_Pervasives_Native.None graph_name))
                > Prims.int_zero));
        RDF_Store_Capabilities.sc_decode_failure = ((fun uu___ -> false))
      }
  | GB_CottasOnDisk (cods, scope) ->
      RDF_Store_Capabilities_Cottas.caps_of_cottas cods scope
  | GB_CottasOnDiskDelta (cods, scope, delta) ->
      RDF_Store_Capabilities_Delta.overlay
        (RDF_Store_Capabilities_Cottas.caps_of_cottas cods scope) delta
  | GB_Union members ->
      RDF_Store_Capabilities.union_caps (caps_of_backend_list members)
and caps_of_backend_list (members : graph_backend Prims.list) :
  RDF_Store_Capabilities.store_caps Prims.list=
  match members with
  | [] -> []
  | m::rest -> (caps_of_backend m) :: (caps_of_backend_list rest)
let backend_search (gb : graph_backend)
  (b : SPARQL11_Algebra.triple_pattern_bound) : RDF_Triple.triple Prims.list=
  (caps_of_backend gb).RDF_Store_Capabilities.sc_solve b
let backend_search_limited (gb : graph_backend)
  (b : SPARQL11_Algebra.triple_pattern_bound) (limit : Prims.nat) :
  RDF_Triple.triple Prims.list=
  (caps_of_backend gb).RDF_Store_Capabilities.sc_solve_limited b limit
let backend_estimate (gb : graph_backend)
  (b : SPARQL11_Algebra.triple_pattern_bound) : Prims.nat=
  (caps_of_backend gb).RDF_Store_Capabilities.sc_estimate b
let backend_count_exact (gb : graph_backend)
  (b : SPARQL11_Algebra.triple_pattern_bound) : Prims.nat=
  (caps_of_backend gb).RDF_Store_Capabilities.sc_count_exact b
let backend_predicate_present (gb : graph_backend) (pred : RDF_Term.wf_iri) :
  Prims.bool=
  (caps_of_backend gb).RDF_Store_Capabilities.sc_predicate_present pred
let materialize_dataset_backend (dsb : dataset_backend) :
  RDF_Graph.rdf_dataset=
  let unbound =
    {
      SPARQL11_Algebra.bs = FStar_Pervasives_Native.None;
      SPARQL11_Algebra.bp = FStar_Pervasives_Native.None;
      SPARQL11_Algebra.bo = FStar_Pervasives_Native.None
    } in
  {
    RDF_Graph.ds_default = (backend_search dsb.dsb_default unbound);
    RDF_Graph.ds_named =
      (FStar_List_Tot_Base.map
         (fun ngb ->
            {
              RDF_Graph.ng_name = (ngb.ngb_name);
              RDF_Graph.ng_graph = (backend_search ngb.ngb_graph unbound)
            }) dsb.dsb_named)
  }
let backend_decode_failure (gb : graph_backend) : Prims.bool=
  (caps_of_backend gb).RDF_Store_Capabilities.sc_decode_failure ()
let rec lookup_named_backend (name : RDF_Term.iri)
  (named : named_graph_backend Prims.list) :
  graph_backend FStar_Pervasives_Native.option=
  match named with
  | [] -> FStar_Pervasives_Native.None
  | ng::rest ->
      if ng.ngb_name = name
      then FStar_Pervasives_Native.Some (ng.ngb_graph)
      else lookup_named_backend name rest
let dataset_caps_of_backend (dsb : dataset_backend) :
  RDF_Store_Capabilities.dataset_caps=
  {
    RDF_Store_Capabilities.dsc_default = (caps_of_backend dsb.dsb_default);
    RDF_Store_Capabilities.dsc_named =
      (FStar_List_Tot_Base.map
         (fun ngb -> ((ngb.ngb_name), (caps_of_backend ngb.ngb_graph)))
         dsb.dsb_named)
  }
let eval_single_tp_backend (tp : SPARQL11_Algebra.triple_pattern)
  (gb : graph_backend) (mu : RDF_Graph_Executable.solution_mapping) :
  SPARQL11_Algebra.solution_sequence=
  let bound =
    {
      SPARQL11_Algebra.bs =
        (SPARQL11_Algebra.bound_subject_of_pattern tp.SPARQL11_Algebra.tp_s
           mu);
      SPARQL11_Algebra.bp =
        (SPARQL11_Algebra.bound_predicate_of_pattern tp.SPARQL11_Algebra.tp_p
           mu);
      SPARQL11_Algebra.bo =
        (SPARQL11_Algebra.bound_object_of_pattern tp.SPARQL11_Algebra.tp_o mu)
    } in
  let candidates = backend_search gb bound in
  SPARQL11_Algebra.list_filter_map
    (fun t -> SPARQL11_Algebra.tp_match tp t mu) candidates
let estimate_tp_backend_mu (tp : SPARQL11_Algebra.triple_pattern)
  (gb : graph_backend) (mu : RDF_Graph_Executable.solution_mapping) :
  Prims.nat=
  backend_estimate gb
    {
      SPARQL11_Algebra.bs =
        (SPARQL11_Algebra.bound_subject_of_pattern tp.SPARQL11_Algebra.tp_s
           mu);
      SPARQL11_Algebra.bp =
        (SPARQL11_Algebra.bound_predicate_of_pattern tp.SPARQL11_Algebra.tp_p
           mu);
      SPARQL11_Algebra.bo =
        (SPARQL11_Algebra.bound_object_of_pattern tp.SPARQL11_Algebra.tp_o mu)
    }
let rec choose_best_tp_backend (patterns : SPARQL11_Algebra.bgp)
  (gb : graph_backend) (mu : RDF_Graph_Executable.solution_mapping) :
  (SPARQL11_Algebra.triple_pattern * SPARQL11_Algebra.bgp)
    FStar_Pervasives_Native.option=
  match patterns with
  | [] -> FStar_Pervasives_Native.None
  | tp::rest ->
      (match choose_best_tp_backend rest gb mu with
       | FStar_Pervasives_Native.None ->
           FStar_Pervasives_Native.Some (tp, [])
       | FStar_Pervasives_Native.Some (best, remaining) ->
           if
             (estimate_tp_backend_mu tp gb mu) <=
               (estimate_tp_backend_mu best gb mu)
           then FStar_Pervasives_Native.Some (tp, rest)
           else FStar_Pervasives_Native.Some (best, (tp :: remaining)))
let rec pattern_predicate_hint (p : SPARQL11_Algebra.group_graph_pattern) :
  RDF_Term.wf_iri FStar_Pervasives_Native.option=
  match p with
  | SPARQL11_Algebra.GP_BGP [] -> FStar_Pervasives_Native.None
  | SPARQL11_Algebra.GP_BGP (tp::uu___) ->
      (match tp.SPARQL11_Algebra.tp_p with
       | SPARQL11_Algebra.PT_IRI pred -> FStar_Pervasives_Native.Some pred
       | uu___1 -> FStar_Pervasives_Native.None)
  | SPARQL11_Algebra.GP_Filter (uu___, p') -> pattern_predicate_hint p'
  | SPARQL11_Algebra.GP_Bind (uu___, uu___1, p') -> pattern_predicate_hint p'
  | SPARQL11_Algebra.GP_Graph (uu___, p') -> pattern_predicate_hint p'
  | SPARQL11_Algebra.GP_Join (p1, uu___) -> pattern_predicate_hint p1
  | SPARQL11_Algebra.GP_LeftJoin (p1, uu___, uu___1) ->
      pattern_predicate_hint p1
  | SPARQL11_Algebra.GP_Union (p1, uu___) -> pattern_predicate_hint p1
  | SPARQL11_Algebra.GP_Minus (p1, uu___) -> pattern_predicate_hint p1
  | SPARQL11_Algebra.GP_Empty -> FStar_Pervasives_Native.None
  | SPARQL11_Algebra.GP_Values (uu___, uu___1) ->
      FStar_Pervasives_Native.None
  | SPARQL11_Algebra.GP_Service (uu___, uu___1, uu___2) ->
      FStar_Pervasives_Native.None
  | SPARQL11_Algebra.GP_ServiceVar (uu___, uu___1, uu___2) ->
      FStar_Pervasives_Native.None
  | SPARQL11_Algebra.GP_SubSelect uu___ -> FStar_Pervasives_Native.None
  | SPARQL11_Algebra.GP_PropertyPath (uu___, uu___1, uu___2) ->
      FStar_Pervasives_Native.None
let named_candidate_backends (named : named_graph_backend Prims.list)
  (predicate_hint : RDF_Term.wf_iri FStar_Pervasives_Native.option) :
  named_graph_backend Prims.list=
  match predicate_hint with
  | FStar_Pervasives_Native.None -> named
  | FStar_Pervasives_Native.Some pred ->
      FStar_List_Tot_Base.filter
        (fun ngb -> backend_predicate_present ngb.ngb_graph pred) named
let rec eval_bgp_concatmap_acc (rest : SPARQL11_Algebra.bgp)
  (gb : graph_backend) (next : SPARQL11_Algebra.solution_sequence)
  (fuel : Prims.nat) (acc_rev : SPARQL11_Algebra.solution_sequence) :
  SPARQL11_Algebra.solution_sequence=
  match next with
  | [] -> acc_rev
  | mu'::more ->
      let part = eval_bgp_backend_from_mu_fuel rest gb mu' fuel in
      eval_bgp_concatmap_acc rest gb more fuel
        (FStar_List_Tot_Base.rev_acc part acc_rev)
and eval_bgp_backend_from_mu_fuel (patterns : SPARQL11_Algebra.bgp)
  (gb : graph_backend) (mu : RDF_Graph_Executable.solution_mapping)
  (fuel : Prims.nat) : SPARQL11_Algebra.solution_sequence=
  if fuel = Prims.int_zero
  then [mu]
  else
    (match patterns with
     | [] -> [mu]
     | uu___1 ->
         (match choose_best_tp_backend patterns gb mu with
          | FStar_Pervasives_Native.None -> [mu]
          | FStar_Pervasives_Native.Some (tp, rest) ->
              let next = eval_single_tp_backend tp gb mu in
              FStar_List_Tot_Base.rev
                (eval_bgp_concatmap_acc rest gb next (fuel - Prims.int_one)
                   [])))
let eval_bgp_backend (patterns : SPARQL11_Algebra.bgp) (gb : graph_backend) :
  SPARQL11_Algebra.solution_sequence=
  eval_bgp_backend_from_mu_fuel patterns gb SPARQL11_Algebra.sm_empty
    ((FStar_List_Tot_Base.length patterns) + Prims.int_one)
let extract_single_tp_bgp (p : SPARQL11_Algebra.group_graph_pattern) :
  SPARQL11_Algebra.triple_pattern FStar_Pervasives_Native.option=
  match p with
  | SPARQL11_Algebra.GP_BGP (tp::[]) -> FStar_Pervasives_Native.Some tp
  | uu___ -> FStar_Pervasives_Native.None
let detect_count_star_select (sel : SPARQL11_Algebra.select_clause) :
  SPARQL11_Algebra.var_name FStar_Pervasives_Native.option=
  match sel with
  | SPARQL11_Algebra.Select_Vars ((SPARQL11_Algebra.SI_Expr (e, v))::[]) ->
      (match e with
       | SPARQL11_Algebra.E_Aggregate
           (SPARQL11_Algebra.Agg_Count, distinct, sub_e) ->
           if distinct
           then FStar_Pervasives_Native.None
           else
             (match sub_e with
              | SPARQL11_Algebra.E_Var "*" -> FStar_Pervasives_Native.Some v
              | SPARQL11_Algebra.E_BoolLit true ->
                  FStar_Pervasives_Native.Some v
              | uu___1 -> FStar_Pervasives_Native.None)
       | uu___ -> FStar_Pervasives_Native.None)
  | uu___ -> FStar_Pervasives_Native.None
let extract_single_tp_bgp_scoped (p : SPARQL11_Algebra.group_graph_pattern) :
  (SPARQL11_Algebra.triple_pattern * RDF_Term.wf_iri
    FStar_Pervasives_Native.option) FStar_Pervasives_Native.option=
  match p with
  | SPARQL11_Algebra.GP_BGP (tp::[]) ->
      FStar_Pervasives_Native.Some (tp, FStar_Pervasives_Native.None)
  | SPARQL11_Algebra.GP_Graph
      (SPARQL11_Algebra.PT_IRI g, SPARQL11_Algebra.GP_BGP (tp::[])) ->
      FStar_Pervasives_Native.Some (tp, (FStar_Pervasives_Native.Some g))
  | uu___ -> FStar_Pervasives_Native.None
let detect_streaming_count_star (q : SPARQL11_Algebra.query) :
  (SPARQL11_Algebra.var_name * SPARQL11_Algebra.triple_pattern *
    RDF_Term.wf_iri FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.option=
  match q.SPARQL11_Algebra.q_form with
  | SPARQL11_Algebra.QF_Select sel ->
      (match detect_count_star_select sel with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some v ->
           if
             FStar_Pervasives_Native.uu___is_Some
               q.SPARQL11_Algebra.q_group_by
           then FStar_Pervasives_Native.None
           else
             if
               FStar_Pervasives_Native.uu___is_Some
                 q.SPARQL11_Algebra.q_having
             then FStar_Pervasives_Native.None
             else
               if
                 FStar_Pervasives_Native.uu___is_Some
                   q.SPARQL11_Algebra.q_values
               then FStar_Pervasives_Native.None
               else
                 if
                   (q.SPARQL11_Algebra.q_modifier).SPARQL11_Algebra.sm_distinct
                 then FStar_Pervasives_Native.None
                 else
                   if
                     (q.SPARQL11_Algebra.q_modifier).SPARQL11_Algebra.sm_reduced
                   then FStar_Pervasives_Native.None
                   else
                     if
                       FStar_Pervasives_Native.uu___is_Some
                         (q.SPARQL11_Algebra.q_modifier).SPARQL11_Algebra.sm_order_by
                     then FStar_Pervasives_Native.None
                     else
                       (match extract_single_tp_bgp_scoped
                                q.SPARQL11_Algebra.q_pattern
                        with
                        | FStar_Pervasives_Native.None ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some (tp, scope) ->
                            FStar_Pervasives_Native.Some (v, tp, scope)))
  | uu___ -> FStar_Pervasives_Native.None
let count_star_solution (alias : SPARQL11_Algebra.var_name) (n : Prims.nat) :
  SPARQL11_Algebra.solution_sequence=
  let lit_term =
    RDF_Term.T_Literal
      {
        RDF_Term.lexical_form = (Prims.string_of_int n);
        RDF_Term.datatype = RDF_Term.xsd_integer;
        RDF_Term.lang_tag = FStar_Pervasives_Native.None
      } in
  [SPARQL11_Algebra.sm_bind alias lit_term SPARQL11_Algebra.sm_empty]
let detect_streaming_count_group_by_graph (q : SPARQL11_Algebra.query) :
  (SPARQL11_Algebra.var_name * SPARQL11_Algebra.var_name)
    FStar_Pervasives_Native.option=
  match q.SPARQL11_Algebra.q_form with
  | SPARQL11_Algebra.QF_Select (SPARQL11_Algebra.Select_Vars items) ->
      if FStar_Pervasives_Native.uu___is_Some q.SPARQL11_Algebra.q_having
      then FStar_Pervasives_Native.None
      else
        if FStar_Pervasives_Native.uu___is_Some q.SPARQL11_Algebra.q_values
        then FStar_Pervasives_Native.None
        else
          if (q.SPARQL11_Algebra.q_modifier).SPARQL11_Algebra.sm_distinct
          then FStar_Pervasives_Native.None
          else
            if (q.SPARQL11_Algebra.q_modifier).SPARQL11_Algebra.sm_reduced
            then FStar_Pervasives_Native.None
            else
              (match items with
               | (SPARQL11_Algebra.SI_Var gv)::(SPARQL11_Algebra.SI_Expr
                   (count_e, nv))::[] ->
                   (match count_e with
                    | SPARQL11_Algebra.E_Aggregate
                        (SPARQL11_Algebra.Agg_Count, false, sub_e) ->
                        let count_ok =
                          match sub_e with
                          | SPARQL11_Algebra.E_Var "*" -> true
                          | SPARQL11_Algebra.E_BoolLit true -> true
                          | uu___4 -> false in
                        if Prims.op_Negation count_ok
                        then FStar_Pervasives_Native.None
                        else
                          (match q.SPARQL11_Algebra.q_group_by with
                           | FStar_Pervasives_Native.Some
                               ((SPARQL11_Algebra.GC_Var gbv)::[]) ->
                               if gbv <> gv
                               then FStar_Pervasives_Native.None
                               else
                                 (match q.SPARQL11_Algebra.q_pattern with
                                  | SPARQL11_Algebra.GP_Graph
                                      (SPARQL11_Algebra.PT_Var graph_v,
                                       inner)
                                      ->
                                      if graph_v <> gv
                                      then FStar_Pervasives_Native.None
                                      else
                                        (match extract_single_tp_bgp inner
                                         with
                                         | FStar_Pervasives_Native.None ->
                                             FStar_Pervasives_Native.None
                                         | FStar_Pervasives_Native.Some tp ->
                                             (match ((tp.SPARQL11_Algebra.tp_s),
                                                      (tp.SPARQL11_Algebra.tp_p),
                                                      (tp.SPARQL11_Algebra.tp_o))
                                              with
                                              | (SPARQL11_Algebra.PS_Var sv,
                                                 SPARQL11_Algebra.PT_Var pv,
                                                 SPARQL11_Algebra.PT_Var ov)
                                                  ->
                                                  if
                                                    ((sv = gv) || (pv = gv))
                                                      || (ov = gv)
                                                  then
                                                    FStar_Pervasives_Native.None
                                                  else
                                                    if
                                                      ((sv = pv) || (sv = ov))
                                                        || (pv = ov)
                                                    then
                                                      FStar_Pervasives_Native.None
                                                    else
                                                      FStar_Pervasives_Native.Some
                                                        (gv, nv)
                                              | uu___7 ->
                                                  FStar_Pervasives_Native.None))
                                  | uu___6 -> FStar_Pervasives_Native.None)
                           | uu___5 -> FStar_Pervasives_Native.None)
                    | uu___4 -> FStar_Pervasives_Native.None)
               | uu___4 -> FStar_Pervasives_Native.None)
  | uu___ -> FStar_Pervasives_Native.None
let rec count_group_by_graph_solutions_acc
  (graph_var : SPARQL11_Algebra.var_name)
  (count_alias : SPARQL11_Algebra.var_name)
  (acc : SPARQL11_Algebra.solution_sequence)
  (named : named_graph_backend Prims.list) :
  SPARQL11_Algebra.solution_sequence=
  match named with
  | [] -> FStar_List_Tot_Base.rev acc
  | ngb::rest ->
      let bound =
        {
          SPARQL11_Algebra.bs = FStar_Pervasives_Native.None;
          SPARQL11_Algebra.bp = FStar_Pervasives_Native.None;
          SPARQL11_Algebra.bo = FStar_Pervasives_Native.None
        } in
      let cnt = backend_count_exact ngb.ngb_graph bound in
      let lit_term =
        RDF_Term.T_Literal
          {
            RDF_Term.lexical_form = (Prims.string_of_int cnt);
            RDF_Term.datatype = RDF_Term.xsd_integer;
            RDF_Term.lang_tag = FStar_Pervasives_Native.None
          } in
      let mu0 =
        SPARQL11_Algebra.sm_bind count_alias lit_term
          SPARQL11_Algebra.sm_empty in
      let mu =
        if RDF_Term.is_iri ngb.ngb_name
        then
          SPARQL11_Algebra.sm_bind graph_var (RDF_Term.T_IRI (ngb.ngb_name))
            mu0
        else mu0 in
      count_group_by_graph_solutions_acc graph_var count_alias (mu :: acc)
        rest
let count_group_by_graph_solutions (graph_var : SPARQL11_Algebra.var_name)
  (count_alias : SPARQL11_Algebra.var_name)
  (named : named_graph_backend Prims.list) :
  SPARQL11_Algebra.solution_sequence=
  count_group_by_graph_solutions_acc graph_var count_alias [] named
let detect_limit_single_tp (q : SPARQL11_Algebra.query) :
  (SPARQL11_Algebra.triple_pattern * Prims.nat)
    FStar_Pervasives_Native.option=
  match q.SPARQL11_Algebra.q_form with
  | SPARQL11_Algebra.QF_Select sel ->
      if SPARQL11_Algebra.select_has_aggregates sel
      then FStar_Pervasives_Native.None
      else
        if FStar_Pervasives_Native.uu___is_Some q.SPARQL11_Algebra.q_group_by
        then FStar_Pervasives_Native.None
        else
          if FStar_Pervasives_Native.uu___is_Some q.SPARQL11_Algebra.q_having
          then FStar_Pervasives_Native.None
          else
            if
              FStar_Pervasives_Native.uu___is_Some
                q.SPARQL11_Algebra.q_values
            then FStar_Pervasives_Native.None
            else
              if (q.SPARQL11_Algebra.q_modifier).SPARQL11_Algebra.sm_distinct
              then FStar_Pervasives_Native.None
              else
                if
                  (q.SPARQL11_Algebra.q_modifier).SPARQL11_Algebra.sm_reduced
                then FStar_Pervasives_Native.None
                else
                  if
                    FStar_Pervasives_Native.uu___is_Some
                      (q.SPARQL11_Algebra.q_modifier).SPARQL11_Algebra.sm_order_by
                  then FStar_Pervasives_Native.None
                  else
                    if
                      FStar_Pervasives_Native.uu___is_Some
                        (q.SPARQL11_Algebra.q_modifier).SPARQL11_Algebra.sm_offset
                    then FStar_Pervasives_Native.None
                    else
                      (match (q.SPARQL11_Algebra.q_modifier).SPARQL11_Algebra.sm_limit
                       with
                       | FStar_Pervasives_Native.None ->
                           FStar_Pervasives_Native.None
                       | FStar_Pervasives_Native.Some k ->
                           (match extract_single_tp_bgp
                                    q.SPARQL11_Algebra.q_pattern
                            with
                            | FStar_Pervasives_Native.None ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some tp ->
                                FStar_Pervasives_Native.Some (tp, k)))
  | uu___ -> FStar_Pervasives_Native.None
let eval_limit_single_tp (sel : SPARQL11_Algebra.select_clause)
  (tp : SPARQL11_Algebra.triple_pattern) (gb : graph_backend)
  (limit : Prims.nat) : SPARQL11_Algebra.solution_sequence=
  let bound =
    {
      SPARQL11_Algebra.bs =
        (SPARQL11_Algebra.bound_subject_of_pattern tp.SPARQL11_Algebra.tp_s
           SPARQL11_Algebra.sm_empty);
      SPARQL11_Algebra.bp =
        (SPARQL11_Algebra.bound_predicate_of_pattern tp.SPARQL11_Algebra.tp_p
           SPARQL11_Algebra.sm_empty);
      SPARQL11_Algebra.bo =
        (SPARQL11_Algebra.bound_object_of_pattern tp.SPARQL11_Algebra.tp_o
           SPARQL11_Algebra.sm_empty)
    } in
  let candidates = backend_search_limited gb bound limit in
  let omega =
    SPARQL11_Algebra.list_filter_map
      (fun t -> SPARQL11_Algebra.tp_match tp t SPARQL11_Algebra.sm_empty)
      candidates in
  let omega' = list_take_n limit omega in
  match sel with
  | SPARQL11_Algebra.Select_Vars items ->
      SPARQL11_Algebra.project_solutions
        (SPARQL11_Algebra.select_item_vars items) omega'
  | SPARQL11_Algebra.Select_All -> omega'
let rec eval_pattern_backend
  (base : RDF_Term.wf_iri FStar_Pervasives_Native.option)
  (p : SPARQL11_Algebra.group_graph_pattern) (gb : graph_backend)
  (dsb : dataset_backend) : SPARQL11_Algebra.solution_sequence=
  match p with
  | SPARQL11_Algebra.GP_BGP bgp -> eval_bgp_backend bgp gb
  | SPARQL11_Algebra.GP_Join (p1, p2) ->
      SPARQL11_Algebra.join (eval_pattern_backend base p1 gb dsb)
        (eval_pattern_backend base p2 gb dsb)
  | SPARQL11_Algebra.GP_LeftJoin (p1, p2, filter_e) ->
      SPARQL11_Algebra.left_join base (eval_pattern_backend base p1 gb dsb)
        (eval_pattern_backend base p2 gb dsb) filter_e
  | SPARQL11_Algebra.GP_Filter (e, p') ->
      SPARQL11_Algebra.filter_solutions_fwd base e
        (eval_pattern_backend base p' gb dsb)
  | SPARQL11_Algebra.GP_Union (p1, p2) ->
      SPARQL11_Algebra.union (eval_pattern_backend base p1 gb dsb)
        (eval_pattern_backend base p2 gb dsb)
  | SPARQL11_Algebra.GP_Minus (p1, p2) ->
      SPARQL11_Algebra.minus (eval_pattern_backend base p1 gb dsb)
        (eval_pattern_backend base p2 gb dsb)
  | SPARQL11_Algebra.GP_Empty -> [SPARQL11_Algebra.sm_empty]
  | SPARQL11_Algebra.GP_Bind (e, v, p') ->
      let omega = eval_pattern_backend base p' gb dsb in
      FStar_List_Tot_Base.map
        (fun mu ->
           match SPARQL11_Algebra.er_to_term
                   (SPARQL11_Algebra.eval_expr_fwd base e mu)
           with
           | FStar_Pervasives_Native.Some t ->
               (match SPARQL11_Algebra.sm_lookup v mu with
                | FStar_Pervasives_Native.Some uu___ -> mu
                | FStar_Pervasives_Native.None ->
                    SPARQL11_Algebra.sm_bind v t mu)
           | FStar_Pervasives_Native.None -> mu) omega
  | SPARQL11_Algebra.GP_Values (vars, rows) ->
      SPARQL11_Algebra.eval_values vars rows
  | SPARQL11_Algebra.GP_Graph (gt, p') ->
      (match gt with
       | SPARQL11_Algebra.PT_IRI name ->
           (match lookup_named_backend name dsb.dsb_named with
            | FStar_Pervasives_Native.Some ngb ->
                eval_pattern_backend base p' ngb dsb
            | FStar_Pervasives_Native.None -> [])
       | SPARQL11_Algebra.PT_Var v ->
           let candidates =
             named_candidate_backends dsb.dsb_named
               (pattern_predicate_hint p') in
           RDF_List_Helpers.concatMap_tr
             (fun ngb ->
                let ng_results =
                  eval_pattern_backend base p' ngb.ngb_graph dsb in
                if RDF_Term.is_iri ngb.ngb_name
                then
                  FStar_List_Tot_Base.map
                    (fun mu ->
                       SPARQL11_Algebra.sm_bind v
                         (RDF_Term.T_IRI (ngb.ngb_name)) mu) ng_results
                else ng_results) candidates
       | uu___ -> eval_pattern_backend base p' gb dsb)
  | SPARQL11_Algebra.GP_Service (uu___, uu___1, uu___2) -> []
  | SPARQL11_Algebra.GP_ServiceVar (uu___, uu___1, uu___2) -> []
  | SPARQL11_Algebra.GP_SubSelect q ->
      (match eval_select_query_backend_on_graph q gb dsb with
       | FStar_Pervasives_Native.Some omega -> omega
       | FStar_Pervasives_Native.None -> [])
  | SPARQL11_Algebra.GP_PropertyPath (ps, pp, pt) ->
      let materialized_graph =
        backend_search gb
          {
            SPARQL11_Algebra.bs = FStar_Pervasives_Native.None;
            SPARQL11_Algebra.bp = FStar_Pervasives_Native.None;
            SPARQL11_Algebra.bo = FStar_Pervasives_Native.None
          } in
      let pairs =
        SPARQL11_Algebra.eval_property_path_fwd pp materialized_graph in
      let pairs1 =
        match pp with
        | SPARQL11_Algebra.PP_ZeroOrMore uu___ ->
            let constant_terms =
              RDF_List_Helpers.append_tr
                (match ps with
                 | SPARQL11_Algebra.PS_IRI i -> [RDF_Term.T_IRI i]
                 | SPARQL11_Algebra.PS_BNode b -> [RDF_Term.T_BNode b]
                 | SPARQL11_Algebra.PS_Var uu___1 -> [])
                (match pt with
                 | SPARQL11_Algebra.PT_IRI i -> [RDF_Term.T_IRI i]
                 | SPARQL11_Algebra.PT_BNode b -> [RDF_Term.T_BNode b]
                 | SPARQL11_Algebra.PT_Literal l -> [RDF_Term.T_Literal l]
                 | SPARQL11_Algebra.PT_Var uu___1 -> []) in
            let has_reflexive t =
              FStar_List_Tot_Base.existsb
                (fun pair ->
                   let uu___1 = pair in
                   match uu___1 with
                   | (s, o) ->
                       (RDF_Term.rdf_term_eq s t) &&
                         (RDF_Term.rdf_term_eq o t)) pairs in
            let new_terms =
              FStar_List_Tot_Base.filter
                (fun t -> Prims.op_Negation (has_reflexive t)) constant_terms in
            let new_reflexive =
              FStar_List_Tot_Base.map (fun n -> (n, n)) new_terms in
            RDF_List_Helpers.append_tr pairs new_reflexive
        | SPARQL11_Algebra.PP_ZeroOrOne uu___ ->
            let constant_terms =
              RDF_List_Helpers.append_tr
                (match ps with
                 | SPARQL11_Algebra.PS_IRI i -> [RDF_Term.T_IRI i]
                 | SPARQL11_Algebra.PS_BNode b -> [RDF_Term.T_BNode b]
                 | SPARQL11_Algebra.PS_Var uu___1 -> [])
                (match pt with
                 | SPARQL11_Algebra.PT_IRI i -> [RDF_Term.T_IRI i]
                 | SPARQL11_Algebra.PT_BNode b -> [RDF_Term.T_BNode b]
                 | SPARQL11_Algebra.PT_Literal l -> [RDF_Term.T_Literal l]
                 | SPARQL11_Algebra.PT_Var uu___1 -> []) in
            let has_reflexive t =
              FStar_List_Tot_Base.existsb
                (fun pair ->
                   let uu___1 = pair in
                   match uu___1 with
                   | (s, o) ->
                       (RDF_Term.rdf_term_eq s t) &&
                         (RDF_Term.rdf_term_eq o t)) pairs in
            let new_terms =
              FStar_List_Tot_Base.filter
                (fun t -> Prims.op_Negation (has_reflexive t)) constant_terms in
            let new_reflexive =
              FStar_List_Tot_Base.map (fun n -> (n, n)) new_terms in
            RDF_List_Helpers.append_tr pairs new_reflexive
        | uu___ -> pairs in
      SPARQL11_Algebra.path_result_to_solutions ps pt pairs1
and eval_select_query_backend_bgp (q : SPARQL11_Algebra.query)
  (gb : graph_backend) :
  SPARQL11_Algebra.solution_sequence FStar_Pervasives_Native.option=
  let base = q.SPARQL11_Algebra.q_base in
  match ((q.SPARQL11_Algebra.q_form), (q.SPARQL11_Algebra.q_pattern)) with
  | (SPARQL11_Algebra.QF_Select sel, SPARQL11_Algebra.GP_BGP bgp) ->
      let omega0 = eval_bgp_backend bgp gb in
      let omega =
        match q.SPARQL11_Algebra.q_values with
        | FStar_Pervasives_Native.None -> omega0
        | FStar_Pervasives_Native.Some vals ->
            SPARQL11_Algebra.join omega0 vals in
      let needs_grouping =
        match q.SPARQL11_Algebra.q_group_by with
        | FStar_Pervasives_Native.Some uu___ -> true
        | FStar_Pervasives_Native.None ->
            SPARQL11_Algebra.select_has_aggregates sel in
      if needs_grouping
      then FStar_Pervasives_Native.None
      else
        (let omega' =
           match sel with
           | SPARQL11_Algebra.Select_Vars items ->
               SPARQL11_Algebra.eval_select_items base items omega []
           | SPARQL11_Algebra.Select_All -> omega in
         let ordered =
           match (q.SPARQL11_Algebra.q_modifier).SPARQL11_Algebra.sm_order_by
           with
           | FStar_Pervasives_Native.None -> omega'
           | FStar_Pervasives_Native.Some o ->
               SPARQL11_Algebra.sort_solutions base o omega' in
         let projected =
           match sel with
           | SPARQL11_Algebra.Select_Vars items ->
               SPARQL11_Algebra.project_solutions
                 (SPARQL11_Algebra.select_item_vars items) ordered
           | SPARQL11_Algebra.Select_All -> ordered in
         let deduped =
           if (q.SPARQL11_Algebra.q_modifier).SPARQL11_Algebra.sm_distinct
           then SPARQL11_Algebra.distinct_solutions projected
           else
             if (q.SPARQL11_Algebra.q_modifier).SPARQL11_Algebra.sm_reduced
             then SPARQL11_Algebra.reduced_solutions projected
             else projected in
         FStar_Pervasives_Native.Some
           (SPARQL11_Algebra.slice_solutions
              (q.SPARQL11_Algebra.q_modifier).SPARQL11_Algebra.sm_offset
              (q.SPARQL11_Algebra.q_modifier).SPARQL11_Algebra.sm_limit
              deduped))
  | uu___ -> FStar_Pervasives_Native.None
and eval_select_query_backend_on_graph (q : SPARQL11_Algebra.query)
  (gb : graph_backend) (dsb : dataset_backend) :
  SPARQL11_Algebra.solution_sequence FStar_Pervasives_Native.option=
  match detect_streaming_count_star q with
  | FStar_Pervasives_Native.Some (alias, tp, graph_scope) ->
      let bound =
        {
          SPARQL11_Algebra.bs =
            (SPARQL11_Algebra.bound_subject_of_pattern
               tp.SPARQL11_Algebra.tp_s SPARQL11_Algebra.sm_empty);
          SPARQL11_Algebra.bp =
            (SPARQL11_Algebra.bound_predicate_of_pattern
               tp.SPARQL11_Algebra.tp_p SPARQL11_Algebra.sm_empty);
          SPARQL11_Algebra.bo =
            (SPARQL11_Algebra.bound_object_of_pattern
               tp.SPARQL11_Algebra.tp_o SPARQL11_Algebra.sm_empty)
        } in
      let n =
        match graph_scope with
        | FStar_Pervasives_Native.None -> backend_count_exact gb bound
        | FStar_Pervasives_Native.Some g ->
            (match lookup_named_backend g dsb.dsb_named with
             | FStar_Pervasives_Native.Some ngb ->
                 backend_count_exact ngb bound
             | FStar_Pervasives_Native.None -> Prims.int_zero) in
      let omega = count_star_solution alias n in
      FStar_Pervasives_Native.Some
        (SPARQL11_Algebra.slice_solutions
           (q.SPARQL11_Algebra.q_modifier).SPARQL11_Algebra.sm_offset
           (q.SPARQL11_Algebra.q_modifier).SPARQL11_Algebra.sm_limit omega)
  | FStar_Pervasives_Native.None ->
      let limit_match =
        match q.SPARQL11_Algebra.q_form with
        | SPARQL11_Algebra.QF_Select uu___ -> detect_limit_single_tp q
        | uu___ -> FStar_Pervasives_Native.None in
      (match limit_match with
       | FStar_Pervasives_Native.Some (tp, k) ->
           (match q.SPARQL11_Algebra.q_form with
            | SPARQL11_Algebra.QF_Select sel ->
                FStar_Pervasives_Native.Some
                  (eval_limit_single_tp sel tp gb k)
            | uu___ -> FStar_Pervasives_Native.None)
       | FStar_Pervasives_Native.None ->
           (match q.SPARQL11_Algebra.q_form with
            | SPARQL11_Algebra.QF_Select sel ->
                let base = q.SPARQL11_Algebra.q_base in
                let omega0 =
                  eval_pattern_backend base q.SPARQL11_Algebra.q_pattern gb
                    dsb in
                let omega =
                  match q.SPARQL11_Algebra.q_values with
                  | FStar_Pervasives_Native.None -> omega0
                  | FStar_Pervasives_Native.Some vals ->
                      SPARQL11_Algebra.join omega0 vals in
                let needs_grouping =
                  match q.SPARQL11_Algebra.q_group_by with
                  | FStar_Pervasives_Native.Some uu___ -> true
                  | FStar_Pervasives_Native.None ->
                      SPARQL11_Algebra.select_has_aggregates sel in
                if needs_grouping
                then
                  let groups =
                    match q.SPARQL11_Algebra.q_group_by with
                    | FStar_Pervasives_Native.Some conds ->
                        SPARQL11_Algebra.group_by base conds omega
                    | FStar_Pervasives_Native.None ->
                        SPARQL11_Algebra.implicit_group omega in
                  let filtered_groups =
                    match q.SPARQL11_Algebra.q_having with
                    | FStar_Pervasives_Native.Some conditions ->
                        SPARQL11_Algebra.having_filter base conditions groups
                    | FStar_Pervasives_Native.None -> groups in
                  let omega' =
                    match sel with
                    | SPARQL11_Algebra.Select_Vars items ->
                        SPARQL11_Algebra.aggregate_groups base items
                          filtered_groups
                    | SPARQL11_Algebra.Select_All ->
                        FStar_List_Tot_Base.map
                          (fun grp ->
                             match grp.SPARQL11_Algebra.g_solutions with
                             | mu::uu___ -> mu
                             | [] -> SPARQL11_Algebra.sm_empty)
                          filtered_groups in
                  let ordered =
                    match (q.SPARQL11_Algebra.q_modifier).SPARQL11_Algebra.sm_order_by
                    with
                    | FStar_Pervasives_Native.None -> omega'
                    | FStar_Pervasives_Native.Some o ->
                        SPARQL11_Algebra.sort_solutions base o omega' in
                  let deduped =
                    if
                      (q.SPARQL11_Algebra.q_modifier).SPARQL11_Algebra.sm_distinct
                    then SPARQL11_Algebra.distinct_solutions ordered
                    else
                      if
                        (q.SPARQL11_Algebra.q_modifier).SPARQL11_Algebra.sm_reduced
                      then SPARQL11_Algebra.reduced_solutions ordered
                      else ordered in
                  FStar_Pervasives_Native.Some
                    (SPARQL11_Algebra.slice_solutions
                       (q.SPARQL11_Algebra.q_modifier).SPARQL11_Algebra.sm_offset
                       (q.SPARQL11_Algebra.q_modifier).SPARQL11_Algebra.sm_limit
                       deduped)
                else
                  (let omega' =
                     match sel with
                     | SPARQL11_Algebra.Select_Vars items ->
                         SPARQL11_Algebra.eval_select_items base items omega
                           []
                     | SPARQL11_Algebra.Select_All -> omega in
                   let ordered =
                     match (q.SPARQL11_Algebra.q_modifier).SPARQL11_Algebra.sm_order_by
                     with
                     | FStar_Pervasives_Native.None -> omega'
                     | FStar_Pervasives_Native.Some o ->
                         SPARQL11_Algebra.sort_solutions base o omega' in
                   let projected =
                     match sel with
                     | SPARQL11_Algebra.Select_Vars items ->
                         SPARQL11_Algebra.project_solutions
                           (SPARQL11_Algebra.select_item_vars items) ordered
                     | SPARQL11_Algebra.Select_All -> ordered in
                   let deduped =
                     if
                       (q.SPARQL11_Algebra.q_modifier).SPARQL11_Algebra.sm_distinct
                     then SPARQL11_Algebra.distinct_solutions projected
                     else
                       if
                         (q.SPARQL11_Algebra.q_modifier).SPARQL11_Algebra.sm_reduced
                       then SPARQL11_Algebra.reduced_solutions projected
                       else projected in
                   FStar_Pervasives_Native.Some
                     (SPARQL11_Algebra.slice_solutions
                        (q.SPARQL11_Algebra.q_modifier).SPARQL11_Algebra.sm_offset
                        (q.SPARQL11_Algebra.q_modifier).SPARQL11_Algebra.sm_limit
                        deduped))
            | uu___ -> FStar_Pervasives_Native.None))
and eval_select_query_backend_dataset (q : SPARQL11_Algebra.query)
  (dsb : dataset_backend) :
  SPARQL11_Algebra.solution_sequence FStar_Pervasives_Native.option=
  match detect_streaming_count_group_by_graph q with
  | FStar_Pervasives_Native.Some (graph_var, count_alias) ->
      let omega =
        count_group_by_graph_solutions graph_var count_alias dsb.dsb_named in
      let ordered =
        match (q.SPARQL11_Algebra.q_modifier).SPARQL11_Algebra.sm_order_by
        with
        | FStar_Pervasives_Native.None -> omega
        | FStar_Pervasives_Native.Some o ->
            SPARQL11_Algebra.sort_solutions q.SPARQL11_Algebra.q_base o omega in
      FStar_Pervasives_Native.Some
        (SPARQL11_Algebra.slice_solutions
           (q.SPARQL11_Algebra.q_modifier).SPARQL11_Algebra.sm_offset
           (q.SPARQL11_Algebra.q_modifier).SPARQL11_Algebra.sm_limit ordered)
  | FStar_Pervasives_Native.None ->
      eval_select_query_backend_on_graph q dsb.dsb_default dsb
and eval_ask_query_backend_dataset (q : SPARQL11_Algebra.query)
  (dsb : dataset_backend) : Prims.bool FStar_Pervasives_Native.option=
  match q.SPARQL11_Algebra.q_form with
  | SPARQL11_Algebra.QF_Ask ->
      let omega0 =
        eval_pattern_backend q.SPARQL11_Algebra.q_base
          q.SPARQL11_Algebra.q_pattern dsb.dsb_default dsb in
      let omega =
        match q.SPARQL11_Algebra.q_values with
        | FStar_Pervasives_Native.None -> omega0
        | FStar_Pervasives_Native.Some vals ->
            SPARQL11_Algebra.join omega0 vals in
      (match omega with
       | [] ->
           let named_backends =
             FStar_List_Tot_Base.map (fun ngb -> ngb.ngb_graph) dsb.dsb_named in
           if
             (backend_decode_failure dsb.dsb_default) ||
               (FStar_List_Tot_Base.existsb backend_decode_failure
                  named_backends)
           then FStar_Pervasives_Native.None
           else FStar_Pervasives_Native.Some false
       | uu___ -> FStar_Pervasives_Native.Some true)
  | uu___ -> FStar_Pervasives_Native.None
let run_select_query_backend_dataset (q : SPARQL11_Algebra.query)
  (dsb : dataset_backend) :
  SPARQL11_Algebra.solution_sequence FStar_Pervasives_Native.option=
  eval_select_query_backend_dataset
    {
      SPARQL11_Algebra.q_base = (q.SPARQL11_Algebra.q_base);
      SPARQL11_Algebra.q_prefixes = (q.SPARQL11_Algebra.q_prefixes);
      SPARQL11_Algebra.q_form = (q.SPARQL11_Algebra.q_form);
      SPARQL11_Algebra.q_dataset = (q.SPARQL11_Algebra.q_dataset);
      SPARQL11_Algebra.q_pattern =
        (SPARQL11_Algebra.rewrite_query_bnodes_pattern
           q.SPARQL11_Algebra.q_pattern);
      SPARQL11_Algebra.q_group_by = (q.SPARQL11_Algebra.q_group_by);
      SPARQL11_Algebra.q_having = (q.SPARQL11_Algebra.q_having);
      SPARQL11_Algebra.q_modifier = (q.SPARQL11_Algebra.q_modifier);
      SPARQL11_Algebra.q_values = (q.SPARQL11_Algebra.q_values)
    } dsb
let run_ask_query_backend_dataset (q : SPARQL11_Algebra.query)
  (dsb : dataset_backend) : Prims.bool FStar_Pervasives_Native.option=
  eval_ask_query_backend_dataset
    {
      SPARQL11_Algebra.q_base = (q.SPARQL11_Algebra.q_base);
      SPARQL11_Algebra.q_prefixes = (q.SPARQL11_Algebra.q_prefixes);
      SPARQL11_Algebra.q_form = (q.SPARQL11_Algebra.q_form);
      SPARQL11_Algebra.q_dataset = (q.SPARQL11_Algebra.q_dataset);
      SPARQL11_Algebra.q_pattern =
        (SPARQL11_Algebra.rewrite_query_bnodes_pattern
           q.SPARQL11_Algebra.q_pattern);
      SPARQL11_Algebra.q_group_by = (q.SPARQL11_Algebra.q_group_by);
      SPARQL11_Algebra.q_having = (q.SPARQL11_Algebra.q_having);
      SPARQL11_Algebra.q_modifier = (q.SPARQL11_Algebra.q_modifier);
      SPARQL11_Algebra.q_values = (q.SPARQL11_Algebra.q_values)
    } dsb
