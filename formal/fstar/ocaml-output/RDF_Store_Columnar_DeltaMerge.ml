open Prims
type delta_resolved =
  {
  dr_cleared: Prims.bool ;
  dr_added: RDF_Triple.triple Prims.list ;
  dr_removed: RDF_Triple.triple Prims.list }
let __proj__Mkdelta_resolved__item__dr_cleared (projectee : delta_resolved) :
  Prims.bool=
  match projectee with | { dr_cleared; dr_added; dr_removed;_} -> dr_cleared
let __proj__Mkdelta_resolved__item__dr_added (projectee : delta_resolved) :
  RDF_Triple.triple Prims.list=
  match projectee with | { dr_cleared; dr_added; dr_removed;_} -> dr_added
let __proj__Mkdelta_resolved__item__dr_removed (projectee : delta_resolved) :
  RDF_Triple.triple Prims.list=
  match projectee with | { dr_cleared; dr_added; dr_removed;_} -> dr_removed
let delta_resolved_empty : delta_resolved=
  { dr_cleared = false; dr_added = []; dr_removed = [] }
let delta_resolved_cleared : delta_resolved=
  { dr_cleared = true; dr_added = []; dr_removed = [] }
let delta_resolved_is_empty (dr : delta_resolved) : Prims.bool=
  ((Prims.op_Negation dr.dr_cleared) &&
     (match dr.dr_added with | [] -> true | uu___ -> false))
    && (match dr.dr_removed with | [] -> true | uu___ -> false)
let apply_entry_to_delta
  (graph_key : RDF_Term.iri FStar_Pervasives_Native.option)
  (dr : delta_resolved) (e : RDF_Store_Columnar_DeltaLog.delta_entry) :
  delta_resolved=
  match e with
  | RDF_Store_Columnar_DeltaLog.DE_Add (q, g) ->
      if g = graph_key
      then
        {
          dr_cleared = (dr.dr_cleared);
          dr_added = (RDF_Graph.graph_add q dr.dr_added);
          dr_removed = (RDF_Graph_Executable.graph_remove q dr.dr_removed)
        }
      else dr
  | RDF_Store_Columnar_DeltaLog.DE_Remove (q, g) ->
      if g = graph_key
      then
        {
          dr_cleared = (dr.dr_cleared);
          dr_added = (RDF_Graph_Executable.graph_remove q dr.dr_added);
          dr_removed = (RDF_Graph.graph_add q dr.dr_removed)
        }
      else dr
  | RDF_Store_Columnar_DeltaLog.DE_Clear g ->
      if g = graph_key then delta_resolved_cleared else dr
  | RDF_Store_Columnar_DeltaLog.DE_Drop g ->
      if (FStar_Pervasives_Native.Some g) = graph_key
      then delta_resolved_cleared
      else dr
  | RDF_Store_Columnar_DeltaLog.DE_Create uu___ -> dr
let rec fold_entries_for_graph
  (graph_key : RDF_Term.iri FStar_Pervasives_Native.option)
  (entries : RDF_Store_Columnar_DeltaLog.delta_entry Prims.list)
  (acc : delta_resolved) : delta_resolved=
  match entries with
  | [] -> acc
  | e::rest ->
      fold_entries_for_graph graph_key rest
        (apply_entry_to_delta graph_key acc e)
let fold_delta_batches
  (batches : RDF_Store_Columnar_DeltaLog.delta_batch Prims.list)
  (graph_key : RDF_Term.iri FStar_Pervasives_Native.option) : delta_resolved=
  fold_entries_for_graph graph_key
    (FStar_List_Tot_Base.concatMap
       (fun b -> b.RDF_Store_Columnar_DeltaLog.db_ops) batches)
    delta_resolved_empty
let entry_graph_mentions (e : RDF_Store_Columnar_DeltaLog.delta_entry) :
  RDF_Term.iri Prims.list=
  match e with
  | RDF_Store_Columnar_DeltaLog.DE_Add (uu___, g) ->
      (match g with
       | FStar_Pervasives_Native.None -> []
       | FStar_Pervasives_Native.Some gi -> [gi])
  | RDF_Store_Columnar_DeltaLog.DE_Remove (uu___, g) ->
      (match g with
       | FStar_Pervasives_Native.None -> []
       | FStar_Pervasives_Native.Some gi -> [gi])
  | RDF_Store_Columnar_DeltaLog.DE_Clear g ->
      (match g with
       | FStar_Pervasives_Native.None -> []
       | FStar_Pervasives_Native.Some gi -> [gi])
  | RDF_Store_Columnar_DeltaLog.DE_Drop g -> [g]
  | RDF_Store_Columnar_DeltaLog.DE_Create g -> [g]
let rec dedup_iri_acc (seen : RDF_Term.iri Prims.list)
  (xs : RDF_Term.iri Prims.list) : RDF_Term.iri Prims.list=
  match xs with
  | [] -> seen
  | x::rest ->
      if FStar_List_Tot_Base.mem x seen
      then dedup_iri_acc seen rest
      else dedup_iri_acc (FStar_List_Tot_Base.op_At seen [x]) rest
let delta_batches_named_graphs
  (batches : RDF_Store_Columnar_DeltaLog.delta_batch Prims.list) :
  RDF_Term.iri Prims.list=
  let all_mentions =
    FStar_List_Tot_Base.concatMap
      (fun b ->
         FStar_List_Tot_Base.concatMap entry_graph_mentions
           b.RDF_Store_Columnar_DeltaLog.db_ops) batches in
  dedup_iri_acc [] all_mentions
let filter_tombstoned (base_results : RDF_Triple.triple Prims.list)
  (dr : delta_resolved) : RDF_Triple.triple Prims.list=
  if dr.dr_cleared
  then []
  else
    FStar_List_Tot_Base.filter
      (fun t -> Prims.op_Negation (RDF_Graph.mem_triple t dr.dr_removed))
      base_results
let merge_on_read (base_results : RDF_Triple.triple Prims.list)
  (dr : delta_resolved) (b : SPARQL11_Algebra.triple_pattern_bound) :
  RDF_Triple.triple Prims.list=
  let survivors = filter_tombstoned base_results dr in
  let additions = SPARQL11_Algebra.triple_matches_bound b dr.dr_added in
  FStar_List_Tot_Base.op_At survivors additions
let delta_matching_count (dr : delta_resolved)
  (b : SPARQL11_Algebra.triple_pattern_bound) : Prims.nat=
  FStar_List_Tot_Base.length
    (SPARQL11_Algebra.triple_matches_bound b dr.dr_added)
let tombstoned_count (dr : delta_resolved)
  (base_results : RDF_Triple.triple Prims.list) : Prims.nat=
  if dr.dr_cleared
  then FStar_List_Tot_Base.length base_results
  else
    FStar_List_Tot_Base.length
      (FStar_List_Tot_Base.filter
         (fun t -> RDF_Graph.mem_triple t dr.dr_removed) base_results)
let rec delta_added_has_predicate (added : RDF_Triple.triple Prims.list)
  (pred : RDF_Term.wf_iri) : Prims.bool=
  match added with
  | [] -> false
  | t::rest ->
      (t.RDF_Triple.p = pred) || (delta_added_has_predicate rest pred)
let apply_entry_ref_step
  (graph_key : RDF_Term.iri FStar_Pervasives_Native.option)
  (g : RDF_Graph.rdf_graph) (e : RDF_Store_Columnar_DeltaLog.delta_entry) :
  RDF_Graph.rdf_graph=
  match e with
  | RDF_Store_Columnar_DeltaLog.DE_Add (q, gr) ->
      if gr = graph_key then RDF_Graph.graph_add q g else g
  | RDF_Store_Columnar_DeltaLog.DE_Remove (q, gr) ->
      if gr = graph_key then RDF_Graph_Executable.graph_remove q g else g
  | RDF_Store_Columnar_DeltaLog.DE_Clear gr ->
      if gr = graph_key then [] else g
  | RDF_Store_Columnar_DeltaLog.DE_Drop gr ->
      if (FStar_Pervasives_Native.Some gr) = graph_key then [] else g
  | RDF_Store_Columnar_DeltaLog.DE_Create uu___ -> g
let rec apply_entries_ref
  (graph_key : RDF_Term.iri FStar_Pervasives_Native.option)
  (g : RDF_Graph.rdf_graph)
  (entries : RDF_Store_Columnar_DeltaLog.delta_entry Prims.list) :
  RDF_Graph.rdf_graph=
  match entries with
  | [] -> g
  | e::rest ->
      apply_entries_ref graph_key (apply_entry_ref_step graph_key g e) rest
let bound_matches (b : SPARQL11_Algebra.triple_pattern_bound)
  (t : RDF_Triple.triple) : Prims.bool=
  ((match b.SPARQL11_Algebra.bs with
    | FStar_Pervasives_Native.None -> true
    | FStar_Pervasives_Native.Some s -> RDF_Term.subject_eq s t.RDF_Triple.s)
     &&
     (match b.SPARQL11_Algebra.bp with
      | FStar_Pervasives_Native.None -> true
      | FStar_Pervasives_Native.Some p -> p = t.RDF_Triple.p))
    &&
    (match b.SPARQL11_Algebra.bo with
     | FStar_Pervasives_Native.None -> true
     | FStar_Pervasives_Native.Some o ->
         RDF_Term.rdf_term_eq o t.RDF_Triple.o)
type ('guref, 'gubase, 'dr) state_agrees = unit
let quad_to_add
  (q : (RDF_Term.wf_iri FStar_Pervasives_Native.option * RDF_Triple.triple))
  : RDF_Store_Columnar_DeltaLog.delta_entry=
  let uu___ = q in
  match uu___ with
  | (g, t) ->
      let g' =
        match g with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some gi -> FStar_Pervasives_Native.Some gi in
      RDF_Store_Columnar_DeltaLog.DE_Add (t, g')
let quad_to_remove
  (q : (RDF_Term.wf_iri FStar_Pervasives_Native.option * RDF_Triple.triple))
  : RDF_Store_Columnar_DeltaLog.delta_entry=
  let uu___ = q in
  match uu___ with
  | (g, t) ->
      let g' =
        match g with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some gi -> FStar_Pervasives_Native.Some gi in
      RDF_Store_Columnar_DeltaLog.DE_Remove (t, g')
let op_to_delta_entries (request_salt : Prims.string)
  (op : SPARQL11_Algebra.update_op) :
  RDF_Store_Columnar_DeltaLog.delta_entry Prims.list
    FStar_Pervasives_Native.option=
  match op with
  | SPARQL11_Algebra.U_InsertData g ->
      let quads =
        SPARQL11_Algebra.collect_quads FStar_Pervasives_Native.None g in
      let prefix = FStar_String.concat "" ["_insdata_"; request_salt] in
      let renamed =
        FStar_List_Tot_Base.map (SPARQL11_Algebra.rename_quad_bnodes prefix)
          quads in
      FStar_Pervasives_Native.Some
        (FStar_List_Tot_Base.map quad_to_add renamed)
  | SPARQL11_Algebra.U_DeleteData g ->
      let quads =
        SPARQL11_Algebra.filter_no_bnode_quads
          (SPARQL11_Algebra.collect_quads FStar_Pervasives_Native.None g) in
      FStar_Pervasives_Native.Some
        (FStar_List_Tot_Base.map quad_to_remove quads)
  | SPARQL11_Algebra.U_Clear (_silent, SPARQL11_Algebra.GR_Default) ->
      FStar_Pervasives_Native.Some
        [RDF_Store_Columnar_DeltaLog.DE_Clear FStar_Pervasives_Native.None]
  | SPARQL11_Algebra.U_Clear (_silent, SPARQL11_Algebra.GR_Graph iri) ->
      FStar_Pervasives_Native.Some
        [RDF_Store_Columnar_DeltaLog.DE_Clear
           (FStar_Pervasives_Native.Some iri)]
  | SPARQL11_Algebra.U_Clear (_silent, SPARQL11_Algebra.GR_Named) ->
      FStar_Pervasives_Native.None
  | SPARQL11_Algebra.U_Clear (_silent, SPARQL11_Algebra.GR_All) ->
      FStar_Pervasives_Native.None
  | SPARQL11_Algebra.U_Drop (_silent, SPARQL11_Algebra.GR_Default) ->
      FStar_Pervasives_Native.Some
        [RDF_Store_Columnar_DeltaLog.DE_Clear FStar_Pervasives_Native.None]
  | SPARQL11_Algebra.U_Drop (_silent, SPARQL11_Algebra.GR_Graph iri) ->
      FStar_Pervasives_Native.Some [RDF_Store_Columnar_DeltaLog.DE_Drop iri]
  | SPARQL11_Algebra.U_Drop (_silent, SPARQL11_Algebra.GR_Named) ->
      FStar_Pervasives_Native.None
  | SPARQL11_Algebra.U_Drop (_silent, SPARQL11_Algebra.GR_All) ->
      FStar_Pervasives_Native.None
  | SPARQL11_Algebra.U_Create (_silent, iri) ->
      FStar_Pervasives_Native.Some
        [RDF_Store_Columnar_DeltaLog.DE_Create iri]
  | SPARQL11_Algebra.U_DeleteWhere uu___ -> FStar_Pervasives_Native.None
  | SPARQL11_Algebra.U_Modify (uu___, uu___1, uu___2, uu___3, uu___4) ->
      FStar_Pervasives_Native.None
  | SPARQL11_Algebra.U_Copy (uu___, uu___1, uu___2) ->
      FStar_Pervasives_Native.None
  | SPARQL11_Algebra.U_Move (uu___, uu___1, uu___2) ->
      FStar_Pervasives_Native.None
  | SPARQL11_Algebra.U_Add (uu___, uu___1, uu___2) ->
      FStar_Pervasives_Native.None
  | SPARQL11_Algebra.U_Load (uu___, uu___1, uu___2) ->
      FStar_Pervasives_Native.None
let rec update_ops_to_delta_entries (request_salt : Prims.string)
  (ops : SPARQL11_Algebra.update_op Prims.list) :
  RDF_Store_Columnar_DeltaLog.delta_entry Prims.list
    FStar_Pervasives_Native.option=
  match ops with
  | [] -> FStar_Pervasives_Native.Some []
  | op::rest ->
      (match op_to_delta_entries request_salt op with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some es ->
           (match update_ops_to_delta_entries request_salt rest with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some es' ->
                FStar_Pervasives_Native.Some
                  (FStar_List_Tot_Base.op_At es es')))
let gsp_put_to_delta_entries
  (graph_key : RDF_Term.iri FStar_Pervasives_Native.option)
  (g : RDF_Graph.rdf_graph) :
  RDF_Store_Columnar_DeltaLog.delta_entry Prims.list=
  (RDF_Store_Columnar_DeltaLog.DE_Clear graph_key) ::
  (FStar_List_Tot_Base.map
     (fun t -> RDF_Store_Columnar_DeltaLog.DE_Add (t, graph_key)) g)
let gsp_post_to_delta_entries
  (graph_key : RDF_Term.iri FStar_Pervasives_Native.option)
  (g : RDF_Graph.rdf_graph) :
  RDF_Store_Columnar_DeltaLog.delta_entry Prims.list=
  FStar_List_Tot_Base.map
    (fun t -> RDF_Store_Columnar_DeltaLog.DE_Add (t, graph_key)) g
let gsp_delete_to_delta_entries
  (graph_key : RDF_Term.iri FStar_Pervasives_Native.option) :
  RDF_Store_Columnar_DeltaLog.delta_entry Prims.list=
  [RDF_Store_Columnar_DeltaLog.DE_Clear graph_key]
