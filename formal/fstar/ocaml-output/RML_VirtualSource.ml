open Prims
type rml_source_data =
  | RSD_Json of Parser_JSON.json_val 
  | RSD_Csv of Prims.string 
  | RSD_None 
let uu___is_RSD_Json (projectee : rml_source_data) : Prims.bool=
  match projectee with | RSD_Json _0 -> true | uu___ -> false
let __proj__RSD_Json__item___0 (projectee : rml_source_data) :
  Parser_JSON.json_val= match projectee with | RSD_Json _0 -> _0
let uu___is_RSD_Csv (projectee : rml_source_data) : Prims.bool=
  match projectee with | RSD_Csv _0 -> true | uu___ -> false
let __proj__RSD_Csv__item___0 (projectee : rml_source_data) : Prims.string=
  match projectee with | RSD_Csv _0 -> _0
let uu___is_RSD_None (projectee : rml_source_data) : Prims.bool=
  match projectee with | RSD_None -> true | uu___ -> false
type rml_sources = (RML_Mapping.node_ref * rml_source_data) Prims.list
type rml_virtual_source =
  {
  rvs_doc: RML_Mapping.mapping_document ;
  rvs_sources: rml_sources ;
  rvs_base_iri: Prims.string FStar_Pervasives_Native.option }
let __proj__Mkrml_virtual_source__item__rvs_doc
  (projectee : rml_virtual_source) : RML_Mapping.mapping_document=
  match projectee with | { rvs_doc; rvs_sources; rvs_base_iri;_} -> rvs_doc
let __proj__Mkrml_virtual_source__item__rvs_sources
  (projectee : rml_virtual_source) : rml_sources=
  match projectee with
  | { rvs_doc; rvs_sources; rvs_base_iri;_} -> rvs_sources
let __proj__Mkrml_virtual_source__item__rvs_base_iri
  (projectee : rml_virtual_source) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | { rvs_doc; rvs_sources; rvs_base_iri;_} -> rvs_base_iri
let json_iterate_filtered (root : Parser_JSON.json_val)
  (iterator : Prims.string) (pred : RML_Sources.source_row -> Prims.bool) :
  RML_Sources.source_row Prims.list=
  FStar_List_Tot_Base.filter pred (RML_Sources.json_iterate root iterator)
let csv_iterate_filtered (csv_text : Prims.string)
  (null_values : Prims.string Prims.list)
  (pred : RML_Sources.source_row -> Prims.bool) :
  RML_Sources.source_row Prims.list=
  FStar_List_Tot_Base.filter pred
    (RML_Sources.csv_iterate csv_text null_values)
let single_pm_could_match (p : RDF_Term.wf_iri) (pm : RML_Mapping.term_map) :
  Prims.bool=
  match pm.RML_Mapping.tmap_form with
  | RML_Mapping.TMF_Constant (RDF_Term.T_IRI i) -> i = p
  | RML_Mapping.TMF_Constant uu___ -> false
  | uu___ -> true
let pom_predicate_could_match (p : RDF_Term.wf_iri)
  (pom : RML_Mapping.predicate_object_map) : Prims.bool=
  FStar_List_Tot_Base.existsb (single_pm_could_match p)
    pom.RML_Mapping.pom_predicates
let classes_could_match_predicate (p : RDF_Term.wf_iri)
  (classes : RDF_Term.wf_iri Prims.list) : Prims.bool=
  match classes with | [] -> false | uu___ -> p = RDFS_Closure.rdf_type
let bp_could_match (b_bp : RDF_Term.wf_iri FStar_Pervasives_Native.option)
  (sm_classes : RDF_Term.wf_iri Prims.list)
  (poms : RML_Mapping.predicate_object_map Prims.list) : Prims.bool=
  match b_bp with
  | FStar_Pervasives_Native.None -> true
  | FStar_Pervasives_Native.Some p ->
      (classes_could_match_predicate p sm_classes) ||
        (FStar_List_Tot_Base.existsb (pom_predicate_could_match p) poms)
let sm_term_could_match_subject
  (b_bs : RDF_Term.subject FStar_Pervasives_Native.option)
  (sm_term : RML_Mapping.term_map) : Prims.bool=
  match b_bs with
  | FStar_Pervasives_Native.None -> true
  | FStar_Pervasives_Native.Some s ->
      (match sm_term.RML_Mapping.tmap_form with
       | RML_Mapping.TMF_Constant t ->
           (match RML_Eval.subject_of_rdf_term t with
            | FStar_Pervasives_Native.Some s' -> RDF_Term.subject_eq s s'
            | FStar_Pervasives_Native.None -> false)
       | uu___ -> true)
let triples_map_could_match (b : SPARQL11_Algebra.triple_pattern_bound)
  (tmap : RML_Mapping.triples_map) : Prims.bool=
  match tmap.RML_Mapping.tm_subject_map with
  | FStar_Pervasives_Native.None -> false
  | FStar_Pervasives_Native.Some sm ->
      (sm_term_could_match_subject b.SPARQL11_Algebra.bs
         sm.RML_Mapping.sm_term)
        &&
        (bp_could_match b.SPARQL11_Algebra.bp sm.RML_Mapping.sm_classes
           tmap.RML_Mapping.tm_predicate_object_maps)
let row_matches_bound_subject
  (b_bs : RDF_Term.subject FStar_Pervasives_Native.option)
  (sm_term : RML_Mapping.term_map)
  (base_iri : Prims.string FStar_Pervasives_Native.option)
  (row : RML_Sources.source_row) : Prims.bool=
  match b_bs with
  | FStar_Pervasives_Native.None -> true
  | FStar_Pervasives_Native.Some s ->
      (match sm_term.RML_Mapping.tmap_form with
       | RML_Mapping.TMF_Constant uu___ -> true
       | uu___ ->
           FStar_List_Tot_Base.existsb
             (fun t ->
                match RML_Eval.subject_of_rdf_term t with
                | FStar_Pervasives_Native.Some s' -> RDF_Term.subject_eq s s'
                | FStar_Pervasives_Native.None -> false)
             (RML_Eval.eval_term_map RML_Eval.MR_Subject sm_term row
                "#virtualsource_pushdown_probe" base_iri))
let rows_for_map_pushed_down (b : SPARQL11_Algebra.triple_pattern_bound)
  (tmap : RML_Mapping.triples_map) (sm : RML_Mapping.subject_map_t)
  (data : rml_source_data)
  (default_base_iri : Prims.string FStar_Pervasives_Native.option) :
  RML_Sources.source_row Prims.list=
  let base_iri =
    match tmap.RML_Mapping.tm_base_iri with
    | FStar_Pervasives_Native.Some x -> FStar_Pervasives_Native.Some x
    | FStar_Pervasives_Native.None -> default_base_iri in
  let pred row =
    row_matches_bound_subject b.SPARQL11_Algebra.bs sm.RML_Mapping.sm_term
      base_iri row in
  match ((tmap.RML_Mapping.tm_logical_source), data) with
  | (FStar_Pervasives_Native.Some ls, RSD_Json root) ->
      (match ls.RML_Mapping.ls_reference_formulation with
       | FStar_Pervasives_Native.Some (RML_Mapping.RF_JSONPath) ->
           let iterator =
             match ls.RML_Mapping.ls_iterator with
             | FStar_Pervasives_Native.Some it -> it
             | FStar_Pervasives_Native.None -> "$" in
           json_iterate_filtered root iterator pred
       | uu___ -> [])
  | (FStar_Pervasives_Native.Some ls, RSD_Csv text) ->
      (match ls.RML_Mapping.ls_reference_formulation with
       | FStar_Pervasives_Native.Some (RML_Mapping.RF_CSV) ->
           csv_iterate_filtered text ls.RML_Mapping.ls_null_values pred
       | uu___ -> [])
  | uu___ -> []
let solve_one_map (b : SPARQL11_Algebra.triple_pattern_bound)
  (tmap : RML_Mapping.triples_map) (sources : rml_sources)
  (default_base_iri : Prims.string FStar_Pervasives_Native.option) :
  RDF_Triple.triple Prims.list=
  match tmap.RML_Mapping.tm_subject_map with
  | FStar_Pervasives_Native.None -> []
  | FStar_Pervasives_Native.Some sm ->
      (match FStar_List_Tot_Base.assoc tmap.RML_Mapping.tm_id sources with
       | FStar_Pervasives_Native.None -> []
       | FStar_Pervasives_Native.Some data ->
           let rows =
             rows_for_map_pushed_down b tmap sm data default_base_iri in
           let placed = RML_Eval.eval_triples_map tmap rows default_base_iri in
           (RML_Eval.place_into_dataset RDF_Graph.empty_dataset placed).RDF_Graph.ds_default)
let rec dedupe_triples_acc (ts : RDF_Triple.triple Prims.list)
  (acc_rev : RDF_Triple.triple Prims.list) : RDF_Triple.triple Prims.list=
  match ts with
  | [] -> FStar_List_Tot_Base.rev acc_rev
  | t::rest ->
      if
        FStar_List_Tot_Base.existsb (fun u -> RDF_Triple.triple_eq u t)
          acc_rev
      then dedupe_triples_acc rest acc_rev
      else dedupe_triples_acc rest (t :: acc_rev)
let rml_solve (doc : RML_Mapping.mapping_document) (sources : rml_sources)
  (default_base_iri : Prims.string FStar_Pervasives_Native.option)
  (b : SPARQL11_Algebra.triple_pattern_bound) : RDF_Triple.triple Prims.list=
  let candidates =
    FStar_List_Tot_Base.filter (triples_map_could_match b)
      doc.RML_Mapping.md_triples_maps in
  let raw =
    FStar_List_Tot_Base.concatMap
      (fun tm -> solve_one_map b tm sources default_base_iri) candidates in
  dedupe_triples_acc (SPARQL11_Algebra.triple_matches_bound b raw) []
let rows_considered_for_map (b : SPARQL11_Algebra.triple_pattern_bound)
  (tmap : RML_Mapping.triples_map) (sources : rml_sources)
  (default_base_iri : Prims.string FStar_Pervasives_Native.option) :
  Prims.nat=
  match tmap.RML_Mapping.tm_subject_map with
  | FStar_Pervasives_Native.None -> Prims.int_zero
  | FStar_Pervasives_Native.Some sm ->
      (match FStar_List_Tot_Base.assoc tmap.RML_Mapping.tm_id sources with
       | FStar_Pervasives_Native.None -> Prims.int_zero
       | FStar_Pervasives_Native.Some data ->
           FStar_List_Tot_Base.length
             (rows_for_map_pushed_down b tmap sm data default_base_iri))
let rml_solve_trace (doc : RML_Mapping.mapping_document)
  (sources : rml_sources)
  (default_base_iri : Prims.string FStar_Pervasives_Native.option)
  (b : SPARQL11_Algebra.triple_pattern_bound) :
  (RML_Mapping.node_ref * Prims.nat) Prims.list=
  FStar_List_Tot_Base.map
    (fun tm ->
       ((tm.RML_Mapping.tm_id),
         (rows_considered_for_map b tm sources default_base_iri)))
    (FStar_List_Tot_Base.filter (triples_map_could_match b)
       doc.RML_Mapping.md_triples_maps)
let rec vs_take_n : 'a . Prims.nat -> 'a Prims.list -> 'a Prims.list =
  fun n xs ->
    if n = Prims.int_zero
    then []
    else
      (match xs with
       | [] -> []
       | hd::tl -> hd :: (vs_take_n (n - Prims.int_one) tl))
let caps_of_rml_source (rvs : rml_virtual_source) :
  RDF_Store_Capabilities.store_caps=
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
      (fun b -> rml_solve rvs.rvs_doc rvs.rvs_sources rvs.rvs_base_iri b);
    RDF_Store_Capabilities.sc_solve_limited =
      (fun b n ->
         vs_take_n n
           (rml_solve rvs.rvs_doc rvs.rvs_sources rvs.rvs_base_iri b));
    RDF_Store_Capabilities.sc_estimate =
      (fun b ->
         FStar_List_Tot_Base.length
           (rml_solve rvs.rvs_doc rvs.rvs_sources rvs.rvs_base_iri b));
    RDF_Store_Capabilities.sc_count_exact =
      (fun b ->
         FStar_List_Tot_Base.length
           (rml_solve rvs.rvs_doc rvs.rvs_sources rvs.rvs_base_iri b));
    RDF_Store_Capabilities.sc_predicate_present =
      (fun pred ->
         (FStar_List_Tot_Base.length
            (rml_solve rvs.rvs_doc rvs.rvs_sources rvs.rvs_base_iri
               {
                 SPARQL11_Algebra.bs = FStar_Pervasives_Native.None;
                 SPARQL11_Algebra.bp = (FStar_Pervasives_Native.Some pred);
                 SPARQL11_Algebra.bo = FStar_Pervasives_Native.None
               }))
           > Prims.int_zero);
    RDF_Store_Capabilities.sc_decode_failure = (fun uu___ -> false)
  }
