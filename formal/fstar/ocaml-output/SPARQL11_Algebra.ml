open Prims
let lit_lexical (l : RDF_Term.wf_literal) : Prims.string=
  l.RDF_Term.lexical_form
let lit_datatype (l : RDF_Term.wf_literal) : RDF_Term.wf_iri=
  l.RDF_Term.datatype
let lit_lang (l : RDF_Term.wf_literal) :
  Prims.string FStar_Pervasives_Native.option= l.RDF_Term.lang_tag
let lit_direction (l : RDF_Term.wf_literal) :
  RDF_Term.text_direction FStar_Pervasives_Native.option=
  l.RDF_Term.direction
let iri_to_string (i : RDF_Term.wf_iri) : Prims.string= i
let string_to_iri (s : Prims.string) :
  RDF_Term.wf_iri FStar_Pervasives_Native.option=
  if RDF_Term.is_iri s
  then FStar_Pervasives_Native.Some s
  else FStar_Pervasives_Native.None
let rdf_langString : RDF_Term.wf_iri= RDF_Term.rdf_lang_string
let xsd_float : RDF_Term.wf_iri= "http://www.w3.org/2001/XMLSchema#float"
let xsd_dateTime : RDF_Term.wf_iri=
  "http://www.w3.org/2001/XMLSchema#dateTime"
let xsd_date : RDF_Term.wf_iri= "http://www.w3.org/2001/XMLSchema#date"
let xsd_time : RDF_Term.wf_iri= "http://www.w3.org/2001/XMLSchema#time"
let xsd_duration : RDF_Term.wf_iri=
  "http://www.w3.org/2001/XMLSchema#duration"
let xsd_dayTimeDuration : RDF_Term.wf_iri=
  "http://www.w3.org/2001/XMLSchema#dayTimeDuration"
let xsd_yearMonthDuration : RDF_Term.wf_iri=
  "http://www.w3.org/2001/XMLSchema#yearMonthDuration"
let sm_empty : RDF_Graph_Executable.solution_mapping= []
let sm_lookup (v : Prims.string) (mu : RDF_Graph_Executable.solution_mapping)
  : RDF_Term.rdf_term FStar_Pervasives_Native.option=
  RDF_List_Helpers.assoc_tr v mu
let sm_bind (v : Prims.string) (t : RDF_Term.rdf_term)
  (mu : RDF_Graph_Executable.solution_mapping) :
  RDF_Graph_Executable.solution_mapping= (v, t) :: mu
let sm_bind_if_compatible (v : Prims.string) (t : RDF_Term.rdf_term)
  (mu : RDF_Graph_Executable.solution_mapping) :
  RDF_Graph_Executable.solution_mapping FStar_Pervasives_Native.option=
  match sm_lookup v mu with
  | FStar_Pervasives_Native.Some existing ->
      if RDF_Term.rdf_term_eq existing t
      then FStar_Pervasives_Native.Some mu
      else FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.None ->
      FStar_Pervasives_Native.Some (sm_bind v t mu)
let sm_domain (mu : RDF_Graph_Executable.solution_mapping) :
  Prims.string Prims.list=
  FStar_List_Tot_Base.map FStar_Pervasives_Native.fst mu
let rec sm_compatible (mu1 : RDF_Graph_Executable.solution_mapping)
  (mu2 : RDF_Graph_Executable.solution_mapping) : Prims.bool=
  match mu1 with
  | [] -> true
  | (v, t)::rest ->
      (match FStar_List_Tot_Base.assoc v mu2 with
       | FStar_Pervasives_Native.None -> sm_compatible rest mu2
       | FStar_Pervasives_Native.Some t2 ->
           (RDF_Term.rdf_term_eq t t2) && (sm_compatible rest mu2))
let rec sm_merge_aux (mu1 : RDF_Graph_Executable.solution_mapping)
  (mu2 : RDF_Graph_Executable.solution_mapping) :
  RDF_Graph_Executable.solution_mapping=
  match mu2 with
  | [] -> mu1
  | (v, t)::rest ->
      if
        FStar_Pervasives_Native.uu___is_Some
          (FStar_List_Tot_Base.assoc v mu1)
      then sm_merge_aux mu1 rest
      else sm_merge_aux ((v, t) :: mu1) rest
let sm_merge (mu1 : RDF_Graph_Executable.solution_mapping)
  (mu2 : RDF_Graph_Executable.solution_mapping) :
  RDF_Graph_Executable.solution_mapping= sm_merge_aux mu1 mu2
type triple_pattern_bound =
  {
  bs: RDF_Term.subject FStar_Pervasives_Native.option ;
  bp: RDF_Term.wf_iri FStar_Pervasives_Native.option ;
  bo: RDF_Term.rdf_term FStar_Pervasives_Native.option }
let __proj__Mktriple_pattern_bound__item__bs
  (projectee : triple_pattern_bound) :
  RDF_Term.subject FStar_Pervasives_Native.option=
  match projectee with | { bs; bp; bo;_} -> bs
let __proj__Mktriple_pattern_bound__item__bp
  (projectee : triple_pattern_bound) :
  RDF_Term.wf_iri FStar_Pervasives_Native.option=
  match projectee with | { bs; bp; bo;_} -> bp
let __proj__Mktriple_pattern_bound__item__bo
  (projectee : triple_pattern_bound) :
  RDF_Term.rdf_term FStar_Pervasives_Native.option=
  match projectee with | { bs; bp; bo;_} -> bo
type graph_store =
  {
  gs_graph: RDF_Graph.rdf_graph ;
  gs_indexed: RDF_Indexed.indexed_graph }
let __proj__Mkgraph_store__item__gs_graph (projectee : graph_store) :
  RDF_Graph.rdf_graph=
  match projectee with | { gs_graph; gs_indexed;_} -> gs_graph
let __proj__Mkgraph_store__item__gs_indexed (projectee : graph_store) :
  RDF_Indexed.indexed_graph=
  match projectee with | { gs_graph; gs_indexed;_} -> gs_indexed
type named_graph_store = {
  ngs_name: RDF_Term.iri ;
  ngs_store: graph_store }
let __proj__Mknamed_graph_store__item__ngs_name
  (projectee : named_graph_store) : RDF_Term.iri=
  match projectee with | { ngs_name; ngs_store;_} -> ngs_name
let __proj__Mknamed_graph_store__item__ngs_store
  (projectee : named_graph_store) : graph_store=
  match projectee with | { ngs_name; ngs_store;_} -> ngs_store
type rdf_dataset_store =
  {
  dss_default: graph_store ;
  dss_named: named_graph_store Prims.list }
let __proj__Mkrdf_dataset_store__item__dss_default
  (projectee : rdf_dataset_store) : graph_store=
  match projectee with | { dss_default; dss_named;_} -> dss_default
let __proj__Mkrdf_dataset_store__item__dss_named
  (projectee : rdf_dataset_store) : named_graph_store Prims.list=
  match projectee with | { dss_default; dss_named;_} -> dss_named
let graph_to_store (g : RDF_Graph.rdf_graph) : graph_store=
  { gs_graph = g; gs_indexed = (RDF_Indexed.build_indexed g) }
let dataset_to_store (ds : RDF_Graph.rdf_dataset) : rdf_dataset_store=
  {
    dss_default = (graph_to_store ds.RDF_Graph.ds_default);
    dss_named =
      (FStar_List_Tot_Base.map
         (fun ng ->
            {
              ngs_name = (ng.RDF_Graph.ng_name);
              ngs_store = (graph_to_store ng.RDF_Graph.ng_graph)
            }) ds.RDF_Graph.ds_named)
  }
let store_to_dataset (dss : rdf_dataset_store) : RDF_Graph.rdf_dataset=
  {
    RDF_Graph.ds_default = ((dss.dss_default).gs_graph);
    RDF_Graph.ds_named =
      (FStar_List_Tot_Base.map
         (fun ngs ->
            {
              RDF_Graph.ng_name = (ngs.ngs_name);
              RDF_Graph.ng_graph = ((ngs.ngs_store).gs_graph)
            }) dss.dss_named)
  }
let rec triple_matches_bound_acc (b : triple_pattern_bound)
  (ts : RDF_Triple.triple Prims.list) (acc : RDF_Triple.triple Prims.list) :
  RDF_Triple.triple Prims.list=
  match ts with
  | [] -> acc
  | t::rest ->
      let subj_ok =
        match b.bs with
        | FStar_Pervasives_Native.None -> true
        | FStar_Pervasives_Native.Some s ->
            RDF_Term.subject_eq s t.RDF_Triple.s in
      let pred_ok =
        match b.bp with
        | FStar_Pervasives_Native.None -> true
        | FStar_Pervasives_Native.Some p -> p = t.RDF_Triple.p in
      let obj_ok =
        match b.bo with
        | FStar_Pervasives_Native.None -> true
        | FStar_Pervasives_Native.Some o ->
            RDF_Term.rdf_term_eq o t.RDF_Triple.o in
      if (subj_ok && pred_ok) && obj_ok
      then triple_matches_bound_acc b rest (t :: acc)
      else triple_matches_bound_acc b rest acc
let triple_matches_bound (b : triple_pattern_bound)
  (ts : RDF_Triple.triple Prims.list) : RDF_Triple.triple Prims.list=
  FStar_List_Tot_Base.rev (triple_matches_bound_acc b ts [])
let pick_smaller_bucket
  (a : RDF_Triple.triple Prims.list FStar_Pervasives_Native.option)
  (b : RDF_Triple.triple Prims.list FStar_Pervasives_Native.option) :
  RDF_Triple.triple Prims.list FStar_Pervasives_Native.option=
  match (a, b) with
  | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) ->
      FStar_Pervasives_Native.None
  | (FStar_Pervasives_Native.Some uu___, FStar_Pervasives_Native.None) -> a
  | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.Some uu___) -> b
  | (FStar_Pervasives_Native.Some la, FStar_Pervasives_Native.Some lb) ->
      if (FStar_List_Tot_Base.length la) <= (FStar_List_Tot_Base.length lb)
      then FStar_Pervasives_Native.Some la
      else FStar_Pervasives_Native.Some lb
let ig_search (ig : RDF_Indexed.indexed_graph) (b : triple_pattern_bound) :
  RDF_Triple.triple Prims.list=
  let pred_b =
    match b.bp with
    | FStar_Pervasives_Native.Some p ->
        if (ig.RDF_Indexed.ig_built).RDF_Indexed.bn_pred
        then
          FStar_Pervasives_Native.Some
            (RDF_Indexed.bucket_lookup ig.RDF_Indexed.ig_pred p)
        else FStar_Pervasives_Native.None
    | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None in
  let subj_b =
    match b.bs with
    | FStar_Pervasives_Native.Some s ->
        if (ig.RDF_Indexed.ig_built).RDF_Indexed.bn_subj
        then
          FStar_Pervasives_Native.Some
            (RDF_Indexed.bucket_lookup ig.RDF_Indexed.ig_subj
               (RDF_Indexed.subject_to_key s))
        else FStar_Pervasives_Native.None
    | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None in
  let obj_b =
    match b.bo with
    | FStar_Pervasives_Native.Some o ->
        if (ig.RDF_Indexed.ig_built).RDF_Indexed.bn_obj
        then
          (match RDF_Indexed.term_to_key_opt o with
           | FStar_Pervasives_Native.Some k ->
               FStar_Pervasives_Native.Some
                 (RDF_Indexed.bucket_lookup ig.RDF_Indexed.ig_obj k)
           | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
        else FStar_Pervasives_Native.None
    | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None in
  let sp_b =
    match ((b.bs), (b.bp)) with
    | (FStar_Pervasives_Native.Some s, FStar_Pervasives_Native.Some p) ->
        if (ig.RDF_Indexed.ig_built).RDF_Indexed.bn_sp
        then
          FStar_Pervasives_Native.Some
            (RDF_Indexed.bucket_lookup ig.RDF_Indexed.ig_sp
               (RDF_Indexed.sp_key s p))
        else FStar_Pervasives_Native.None
    | uu___ -> FStar_Pervasives_Native.None in
  let po_b =
    match ((b.bp), (b.bo)) with
    | (FStar_Pervasives_Native.Some p, FStar_Pervasives_Native.Some o) ->
        if (ig.RDF_Indexed.ig_built).RDF_Indexed.bn_po
        then
          (match RDF_Indexed.po_key_opt p o with
           | FStar_Pervasives_Native.Some k ->
               FStar_Pervasives_Native.Some
                 (RDF_Indexed.bucket_lookup ig.RDF_Indexed.ig_po k)
           | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
        else FStar_Pervasives_Native.None
    | uu___ -> FStar_Pervasives_Native.None in
  let so_b =
    match ((b.bs), (b.bo)) with
    | (FStar_Pervasives_Native.Some s, FStar_Pervasives_Native.Some o) ->
        if (ig.RDF_Indexed.ig_built).RDF_Indexed.bn_so
        then
          (match RDF_Indexed.so_key_opt s o with
           | FStar_Pervasives_Native.Some k ->
               FStar_Pervasives_Native.Some
                 (RDF_Indexed.bucket_lookup ig.RDF_Indexed.ig_so k)
           | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
        else FStar_Pervasives_Native.None
    | uu___ -> FStar_Pervasives_Native.None in
  let compound = pick_smaller_bucket (pick_smaller_bucket sp_b po_b) so_b in
  let single = pick_smaller_bucket (pick_smaller_bucket pred_b subj_b) obj_b in
  let candidate = pick_smaller_bucket compound single in
  let pool =
    match candidate with
    | FStar_Pervasives_Native.Some bucket -> bucket
    | FStar_Pervasives_Native.None -> ig.RDF_Indexed.ig_triples in
  triple_matches_bound b pool
let ig_estimate (ig : RDF_Indexed.indexed_graph) (b : triple_pattern_bound) :
  Prims.nat=
  match ((b.bs), (b.bp), (b.bo)) with
  | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None,
     FStar_Pervasives_Native.None) ->
      FStar_List_Tot_Base.length ig.RDF_Indexed.ig_triples
  | uu___ -> FStar_List_Tot_Base.length (ig_search ig b)
let store_search (g : graph_store) (b : triple_pattern_bound) :
  RDF_Triple.triple Prims.list= ig_search g.gs_indexed b
let store_estimate (g : graph_store) (b : triple_pattern_bound) : Prims.nat=
  ig_estimate g.gs_indexed b
let rec lookup_named_store (name : RDF_Term.iri)
  (named : named_graph_store Prims.list) :
  graph_store FStar_Pervasives_Native.option=
  match named with
  | [] -> FStar_Pervasives_Native.None
  | ng::rest ->
      if ng.ngs_name = name
      then FStar_Pervasives_Native.Some (ng.ngs_store)
      else lookup_named_store name rest
type var_name = Prims.string
type pattern_term =
  | PT_Var of var_name 
  | PT_IRI of RDF_Term.wf_iri 
  | PT_BNode of RDF_Term.bnode_id 
  | PT_Literal of RDF_Term.wf_literal 
  | PT_TripleTerm of pattern_term * pattern_term * pattern_term 
let uu___is_PT_Var (projectee : pattern_term) : Prims.bool=
  match projectee with | PT_Var _0 -> true | uu___ -> false
let __proj__PT_Var__item___0 (projectee : pattern_term) : var_name=
  match projectee with | PT_Var _0 -> _0
let uu___is_PT_IRI (projectee : pattern_term) : Prims.bool=
  match projectee with | PT_IRI _0 -> true | uu___ -> false
let __proj__PT_IRI__item___0 (projectee : pattern_term) : RDF_Term.wf_iri=
  match projectee with | PT_IRI _0 -> _0
let uu___is_PT_BNode (projectee : pattern_term) : Prims.bool=
  match projectee with | PT_BNode _0 -> true | uu___ -> false
let __proj__PT_BNode__item___0 (projectee : pattern_term) :
  RDF_Term.bnode_id= match projectee with | PT_BNode _0 -> _0
let uu___is_PT_Literal (projectee : pattern_term) : Prims.bool=
  match projectee with | PT_Literal _0 -> true | uu___ -> false
let __proj__PT_Literal__item___0 (projectee : pattern_term) :
  RDF_Term.wf_literal= match projectee with | PT_Literal _0 -> _0
let uu___is_PT_TripleTerm (projectee : pattern_term) : Prims.bool=
  match projectee with | PT_TripleTerm (_0, _1, _2) -> true | uu___ -> false
let __proj__PT_TripleTerm__item___0 (projectee : pattern_term) :
  pattern_term= match projectee with | PT_TripleTerm (_0, _1, _2) -> _0
let __proj__PT_TripleTerm__item___1 (projectee : pattern_term) :
  pattern_term= match projectee with | PT_TripleTerm (_0, _1, _2) -> _1
let __proj__PT_TripleTerm__item___2 (projectee : pattern_term) :
  pattern_term= match projectee with | PT_TripleTerm (_0, _1, _2) -> _2
type pattern_subject =
  | PS_Var of var_name 
  | PS_IRI of RDF_Term.wf_iri 
  | PS_BNode of RDF_Term.bnode_id 
  | PS_TripleTerm of pattern_term * pattern_term * pattern_term 
let uu___is_PS_Var (projectee : pattern_subject) : Prims.bool=
  match projectee with | PS_Var _0 -> true | uu___ -> false
let __proj__PS_Var__item___0 (projectee : pattern_subject) : var_name=
  match projectee with | PS_Var _0 -> _0
let uu___is_PS_IRI (projectee : pattern_subject) : Prims.bool=
  match projectee with | PS_IRI _0 -> true | uu___ -> false
let __proj__PS_IRI__item___0 (projectee : pattern_subject) : RDF_Term.wf_iri=
  match projectee with | PS_IRI _0 -> _0
let uu___is_PS_BNode (projectee : pattern_subject) : Prims.bool=
  match projectee with | PS_BNode _0 -> true | uu___ -> false
let __proj__PS_BNode__item___0 (projectee : pattern_subject) :
  RDF_Term.bnode_id= match projectee with | PS_BNode _0 -> _0
let uu___is_PS_TripleTerm (projectee : pattern_subject) : Prims.bool=
  match projectee with | PS_TripleTerm (_0, _1, _2) -> true | uu___ -> false
let __proj__PS_TripleTerm__item___0 (projectee : pattern_subject) :
  pattern_term= match projectee with | PS_TripleTerm (_0, _1, _2) -> _0
let __proj__PS_TripleTerm__item___1 (projectee : pattern_subject) :
  pattern_term= match projectee with | PS_TripleTerm (_0, _1, _2) -> _1
let __proj__PS_TripleTerm__item___2 (projectee : pattern_subject) :
  pattern_term= match projectee with | PS_TripleTerm (_0, _1, _2) -> _2
type triple_pattern =
  {
  tp_s: pattern_subject ;
  tp_p: pattern_term ;
  tp_o: pattern_term }
let __proj__Mktriple_pattern__item__tp_s (projectee : triple_pattern) :
  pattern_subject= match projectee with | { tp_s; tp_p; tp_o;_} -> tp_s
let __proj__Mktriple_pattern__item__tp_p (projectee : triple_pattern) :
  pattern_term= match projectee with | { tp_s; tp_p; tp_o;_} -> tp_p
let __proj__Mktriple_pattern__item__tp_o (projectee : triple_pattern) :
  pattern_term= match projectee with | { tp_s; tp_p; tp_o;_} -> tp_o
let term_to_subject_opt (t : RDF_Term.rdf_term) :
  RDF_Term.subject FStar_Pervasives_Native.option=
  match t with
  | RDF_Term.T_IRI i -> FStar_Pervasives_Native.Some (RDF_Term.S_IRI i)
  | RDF_Term.T_BNode b -> FStar_Pervasives_Native.Some (RDF_Term.S_BNode b)
  | uu___ -> FStar_Pervasives_Native.None
let bound_subject_of_pattern (ps : pattern_subject)
  (mu : RDF_Graph_Executable.solution_mapping) :
  RDF_Term.subject FStar_Pervasives_Native.option=
  match ps with
  | PS_IRI i -> FStar_Pervasives_Native.Some (RDF_Term.S_IRI i)
  | PS_BNode b -> FStar_Pervasives_Native.Some (RDF_Term.S_BNode b)
  | PS_TripleTerm (uu___, uu___1, uu___2) -> FStar_Pervasives_Native.None
  | PS_Var v ->
      (match sm_lookup v mu with
       | FStar_Pervasives_Native.Some (RDF_Term.T_IRI i) ->
           FStar_Pervasives_Native.Some (RDF_Term.S_IRI i)
       | FStar_Pervasives_Native.Some (RDF_Term.T_BNode b) ->
           FStar_Pervasives_Native.Some (RDF_Term.S_BNode b)
       | FStar_Pervasives_Native.Some (RDF_Term.T_Literal uu___) ->
           FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some (RDF_Term.T_TripleTerm
           (uu___, uu___1, uu___2)) -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
let bound_predicate_of_pattern (pt : pattern_term)
  (mu : RDF_Graph_Executable.solution_mapping) :
  RDF_Term.wf_iri FStar_Pervasives_Native.option=
  match pt with
  | PT_IRI i -> FStar_Pervasives_Native.Some i
  | PT_BNode uu___ -> FStar_Pervasives_Native.None
  | PT_Literal uu___ -> FStar_Pervasives_Native.None
  | PT_TripleTerm (uu___, uu___1, uu___2) -> FStar_Pervasives_Native.None
  | PT_Var v ->
      (match sm_lookup v mu with
       | FStar_Pervasives_Native.Some (RDF_Term.T_IRI i) ->
           FStar_Pervasives_Native.Some i
       | FStar_Pervasives_Native.Some (RDF_Term.T_BNode uu___) ->
           FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some (RDF_Term.T_Literal uu___) ->
           FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some (RDF_Term.T_TripleTerm
           (uu___, uu___1, uu___2)) -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
let rec bound_object_of_pattern (pt : pattern_term)
  (mu : RDF_Graph_Executable.solution_mapping) :
  RDF_Term.rdf_term FStar_Pervasives_Native.option=
  match pt with
  | PT_IRI i -> FStar_Pervasives_Native.Some (RDF_Term.T_IRI i)
  | PT_BNode b -> FStar_Pervasives_Native.Some (RDF_Term.T_BNode b)
  | PT_Literal l -> FStar_Pervasives_Native.Some (RDF_Term.T_Literal l)
  | PT_Var v -> sm_lookup v mu
  | PT_TripleTerm (ps, pp, po) ->
      (match bound_object_of_pattern ps mu with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some sterm ->
           (match term_to_subject_opt sterm with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some ssub ->
                (match bound_object_of_pattern pp mu with
                 | FStar_Pervasives_Native.Some (RDF_Term.T_IRI ppi) ->
                     (match bound_object_of_pattern po mu with
                      | FStar_Pervasives_Native.None ->
                          FStar_Pervasives_Native.None
                      | FStar_Pervasives_Native.Some oterm ->
                          FStar_Pervasives_Native.Some
                            (RDF_Term.T_TripleTerm (ssub, ppi, oterm)))
                 | uu___ -> FStar_Pervasives_Native.None)))
let pattern_subject_eq (a : pattern_subject) (b : pattern_subject) :
  Prims.bool=
  match (a, b) with
  | (PS_Var v1, PS_Var v2) -> v1 = v2
  | (PS_IRI i1, PS_IRI i2) -> i1 = i2
  | (PS_BNode b1, PS_BNode b2) -> b1 = b2
  | (uu___, uu___1) -> false
let rec pattern_term_eq (a : pattern_term) (b : pattern_term) : Prims.bool=
  match (a, b) with
  | (PT_Var v1, PT_Var v2) -> v1 = v2
  | (PT_IRI i1, PT_IRI i2) -> i1 = i2
  | (PT_BNode b1, PT_BNode b2) -> b1 = b2
  | (PT_Literal l1, PT_Literal l2) -> RDF_Term.literal_eq l1 l2
  | (PT_TripleTerm (s1, p1, o1), PT_TripleTerm (s2, p2, o2)) ->
      ((pattern_term_eq s1 s2) && (pattern_term_eq p1 p2)) &&
        (pattern_term_eq o1 o2)
  | (uu___, uu___1) -> false
let triple_pattern_eq (a : triple_pattern) (b : triple_pattern) : Prims.bool=
  ((pattern_subject_eq a.tp_s b.tp_s) && (pattern_term_eq a.tp_p b.tp_p)) &&
    (pattern_term_eq a.tp_o b.tp_o)
type bgp = triple_pattern Prims.list
type comp_op =
  | CmpEq 
  | CmpNe 
  | CmpLt 
  | CmpGt 
  | CmpLe 
  | CmpGe 
let uu___is_CmpEq (projectee : comp_op) : Prims.bool=
  match projectee with | CmpEq -> true | uu___ -> false
let uu___is_CmpNe (projectee : comp_op) : Prims.bool=
  match projectee with | CmpNe -> true | uu___ -> false
let uu___is_CmpLt (projectee : comp_op) : Prims.bool=
  match projectee with | CmpLt -> true | uu___ -> false
let uu___is_CmpGt (projectee : comp_op) : Prims.bool=
  match projectee with | CmpGt -> true | uu___ -> false
let uu___is_CmpLe (projectee : comp_op) : Prims.bool=
  match projectee with | CmpLe -> true | uu___ -> false
let uu___is_CmpGe (projectee : comp_op) : Prims.bool=
  match projectee with | CmpGe -> true | uu___ -> false
type arith_op =
  | Add 
  | Sub 
  | Mul 
  | Div 
let uu___is_Add (projectee : arith_op) : Prims.bool=
  match projectee with | Add -> true | uu___ -> false
let uu___is_Sub (projectee : arith_op) : Prims.bool=
  match projectee with | Sub -> true | uu___ -> false
let uu___is_Mul (projectee : arith_op) : Prims.bool=
  match projectee with | Mul -> true | uu___ -> false
let uu___is_Div (projectee : arith_op) : Prims.bool=
  match projectee with | Div -> true | uu___ -> false
type aggregate_fn =
  | Agg_Count 
  | Agg_Sum 
  | Agg_Min 
  | Agg_Max 
  | Agg_Avg 
  | Agg_GroupConcat of Prims.string FStar_Pervasives_Native.option 
  | Agg_Sample 
let uu___is_Agg_Count (projectee : aggregate_fn) : Prims.bool=
  match projectee with | Agg_Count -> true | uu___ -> false
let uu___is_Agg_Sum (projectee : aggregate_fn) : Prims.bool=
  match projectee with | Agg_Sum -> true | uu___ -> false
let uu___is_Agg_Min (projectee : aggregate_fn) : Prims.bool=
  match projectee with | Agg_Min -> true | uu___ -> false
let uu___is_Agg_Max (projectee : aggregate_fn) : Prims.bool=
  match projectee with | Agg_Max -> true | uu___ -> false
let uu___is_Agg_Avg (projectee : aggregate_fn) : Prims.bool=
  match projectee with | Agg_Avg -> true | uu___ -> false
let uu___is_Agg_GroupConcat (projectee : aggregate_fn) : Prims.bool=
  match projectee with | Agg_GroupConcat _0 -> true | uu___ -> false
let __proj__Agg_GroupConcat__item___0 (projectee : aggregate_fn) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with | Agg_GroupConcat _0 -> _0
let uu___is_Agg_Sample (projectee : aggregate_fn) : Prims.bool=
  match projectee with | Agg_Sample -> true | uu___ -> false
type expr =
  | E_Var of var_name 
  | E_IRI of RDF_Term.wf_iri 
  | E_Literal of RDF_Term.wf_literal 
  | E_BoolLit of Prims.bool 
  | E_NumericLit of Prims.int 
  | E_DecimalLit of Prims.string 
  | E_DoubleLit of Prims.string 
  | E_Arith of arith_op * expr * expr 
  | E_UnaryMinus of expr 
  | E_UnaryPlus of expr 
  | E_Compare of comp_op * expr * expr 
  | E_And of expr * expr 
  | E_Or of expr * expr 
  | E_Not of expr 
  | E_IsIRI of expr 
  | E_IsBlank of expr 
  | E_IsLiteral of expr 
  | E_IsNumeric of expr 
  | E_Str of expr 
  | E_Lang of expr 
  | E_Datatype of expr 
  | E_IRI_fn of expr 
  | E_HasLang of expr 
  | E_HasLangDir of expr 
  | E_LangDir of expr 
  | E_StrDt of expr * expr 
  | E_StrLang of expr * expr 
  | E_StrLangDir of expr * expr * expr 
  | E_Bound of var_name 
  | E_If of expr * expr * expr 
  | E_Coalesce of expr Prims.list 
  | E_In of expr * expr Prims.list 
  | E_NotIn of expr * expr Prims.list 
  | E_StrLen of expr 
  | E_Substr of expr * expr * expr FStar_Pervasives_Native.option 
  | E_UCase of expr 
  | E_LCase of expr 
  | E_StrStarts of expr * expr 
  | E_StrEnds of expr * expr 
  | E_Contains of expr * expr 
  | E_StrBefore of expr * expr 
  | E_StrAfter of expr * expr 
  | E_Concat of expr Prims.list 
  | E_EncodeForUri of expr 
  | E_Replace of expr * expr * expr * expr FStar_Pervasives_Native.option 
  | E_Regex of expr * expr * expr FStar_Pervasives_Native.option 
  | E_Abs of expr 
  | E_Round of expr 
  | E_Ceil of expr 
  | E_Floor of expr 
  | E_MD5 of expr 
  | E_SHA1 of expr 
  | E_SHA256 of expr 
  | E_SHA384 of expr 
  | E_SHA512 of expr 
  | E_Now 
  | E_Year of expr 
  | E_Month of expr 
  | E_Day of expr 
  | E_Hours of expr 
  | E_Minutes of expr 
  | E_Seconds of expr 
  | E_Timezone of expr 
  | E_Tz of expr 
  | E_SameTerm of expr * expr 
  | E_Exists of group_graph_pattern 
  | E_NotExists of group_graph_pattern 
  | E_Aggregate of aggregate_fn * Prims.bool * expr 
  | E_FunctionCall of RDF_Term.wf_iri * expr Prims.list 
  | E_TripleTerm of expr * expr * expr 
  | E_TTSubject of expr 
  | E_TTPredicate of expr 
  | E_TTObject of expr 
  | E_IsTriple of expr 
and property_path =
  | PP_IRI of RDF_Term.wf_iri 
  | PP_Inverse of property_path 
  | PP_Sequence of property_path * property_path 
  | PP_Alternative of property_path * property_path 
  | PP_ZeroOrMore of property_path 
  | PP_OneOrMore of property_path 
  | PP_ZeroOrOne of property_path 
  | PP_NegatedSet of property_path Prims.list 
and group_graph_pattern =
  | GP_BGP of bgp 
  | GP_Join of group_graph_pattern * group_graph_pattern 
  | GP_LeftJoin of group_graph_pattern * group_graph_pattern * expr 
  | GP_Filter of expr * group_graph_pattern 
  | GP_Union of group_graph_pattern * group_graph_pattern 
  | GP_Graph of pattern_term * group_graph_pattern 
  | GP_Minus of group_graph_pattern * group_graph_pattern 
  | GP_Lateral of group_graph_pattern * group_graph_pattern 
  | GP_Bind of expr * var_name * group_graph_pattern 
  | GP_Values of var_name Prims.list * RDF_Term.rdf_term
  FStar_Pervasives_Native.option Prims.list Prims.list 
  | GP_Service of RDF_Term.wf_iri * group_graph_pattern * Prims.bool 
  | GP_ServiceVar of var_name * group_graph_pattern * Prims.bool 
  | GP_SubSelect of query 
  | GP_PropertyPath of pattern_subject * property_path * pattern_term 
  | GP_Empty 
and order_condition =
  | OC_Asc of expr 
  | OC_Desc of expr 
and solution_modifier =
  {
  sm_order_by: order_condition Prims.list FStar_Pervasives_Native.option ;
  sm_distinct: Prims.bool ;
  sm_reduced: Prims.bool ;
  sm_offset: Prims.nat FStar_Pervasives_Native.option ;
  sm_limit: Prims.nat FStar_Pervasives_Native.option }
and select_item =
  | SI_Var of var_name 
  | SI_Expr of expr * var_name 
and select_clause =
  | Select_Vars of select_item Prims.list 
  | Select_All 
and group_condition =
  | GC_Var of var_name 
  | GC_Expr of expr * var_name FStar_Pervasives_Native.option 
  | GC_BuiltIn of expr 
and query_form =
  | QF_Select of select_clause 
  | QF_Construct of triple_pattern Prims.list 
  | QF_Ask 
  | QF_Describe of pattern_term Prims.list 
and dataset_clause =
  | DC_Default of RDF_Term.wf_iri 
  | DC_Named of RDF_Term.wf_iri 
and query =
  {
  q_base: RDF_Term.wf_iri FStar_Pervasives_Native.option ;
  q_prefixes: (Prims.string * RDF_Term.wf_iri) Prims.list ;
  q_form: query_form ;
  q_dataset: dataset_clause Prims.list ;
  q_pattern: group_graph_pattern ;
  q_group_by: group_condition Prims.list FStar_Pervasives_Native.option ;
  q_having: expr Prims.list FStar_Pervasives_Native.option ;
  q_modifier: solution_modifier ;
  q_values:
    (var_name * RDF_Term.rdf_term) Prims.list Prims.list
      FStar_Pervasives_Native.option
    }
let uu___is_E_Var (projectee : expr) : Prims.bool=
  match projectee with | E_Var _0 -> true | uu___ -> false
let __proj__E_Var__item___0 (projectee : expr) : var_name=
  match projectee with | E_Var _0 -> _0
let uu___is_E_IRI (projectee : expr) : Prims.bool=
  match projectee with | E_IRI _0 -> true | uu___ -> false
let __proj__E_IRI__item___0 (projectee : expr) : RDF_Term.wf_iri=
  match projectee with | E_IRI _0 -> _0
let uu___is_E_Literal (projectee : expr) : Prims.bool=
  match projectee with | E_Literal _0 -> true | uu___ -> false
let __proj__E_Literal__item___0 (projectee : expr) : RDF_Term.wf_literal=
  match projectee with | E_Literal _0 -> _0
let uu___is_E_BoolLit (projectee : expr) : Prims.bool=
  match projectee with | E_BoolLit _0 -> true | uu___ -> false
let __proj__E_BoolLit__item___0 (projectee : expr) : Prims.bool=
  match projectee with | E_BoolLit _0 -> _0
let uu___is_E_NumericLit (projectee : expr) : Prims.bool=
  match projectee with | E_NumericLit _0 -> true | uu___ -> false
let __proj__E_NumericLit__item___0 (projectee : expr) : Prims.int=
  match projectee with | E_NumericLit _0 -> _0
let uu___is_E_DecimalLit (projectee : expr) : Prims.bool=
  match projectee with | E_DecimalLit _0 -> true | uu___ -> false
let __proj__E_DecimalLit__item___0 (projectee : expr) : Prims.string=
  match projectee with | E_DecimalLit _0 -> _0
let uu___is_E_DoubleLit (projectee : expr) : Prims.bool=
  match projectee with | E_DoubleLit _0 -> true | uu___ -> false
let __proj__E_DoubleLit__item___0 (projectee : expr) : Prims.string=
  match projectee with | E_DoubleLit _0 -> _0
let uu___is_E_Arith (projectee : expr) : Prims.bool=
  match projectee with | E_Arith (_0, _1, _2) -> true | uu___ -> false
let __proj__E_Arith__item___0 (projectee : expr) : arith_op=
  match projectee with | E_Arith (_0, _1, _2) -> _0
let __proj__E_Arith__item___1 (projectee : expr) : expr=
  match projectee with | E_Arith (_0, _1, _2) -> _1
let __proj__E_Arith__item___2 (projectee : expr) : expr=
  match projectee with | E_Arith (_0, _1, _2) -> _2
let uu___is_E_UnaryMinus (projectee : expr) : Prims.bool=
  match projectee with | E_UnaryMinus _0 -> true | uu___ -> false
let __proj__E_UnaryMinus__item___0 (projectee : expr) : expr=
  match projectee with | E_UnaryMinus _0 -> _0
let uu___is_E_UnaryPlus (projectee : expr) : Prims.bool=
  match projectee with | E_UnaryPlus _0 -> true | uu___ -> false
let __proj__E_UnaryPlus__item___0 (projectee : expr) : expr=
  match projectee with | E_UnaryPlus _0 -> _0
let uu___is_E_Compare (projectee : expr) : Prims.bool=
  match projectee with | E_Compare (_0, _1, _2) -> true | uu___ -> false
let __proj__E_Compare__item___0 (projectee : expr) : comp_op=
  match projectee with | E_Compare (_0, _1, _2) -> _0
let __proj__E_Compare__item___1 (projectee : expr) : expr=
  match projectee with | E_Compare (_0, _1, _2) -> _1
let __proj__E_Compare__item___2 (projectee : expr) : expr=
  match projectee with | E_Compare (_0, _1, _2) -> _2
let uu___is_E_And (projectee : expr) : Prims.bool=
  match projectee with | E_And (_0, _1) -> true | uu___ -> false
let __proj__E_And__item___0 (projectee : expr) : expr=
  match projectee with | E_And (_0, _1) -> _0
let __proj__E_And__item___1 (projectee : expr) : expr=
  match projectee with | E_And (_0, _1) -> _1
let uu___is_E_Or (projectee : expr) : Prims.bool=
  match projectee with | E_Or (_0, _1) -> true | uu___ -> false
let __proj__E_Or__item___0 (projectee : expr) : expr=
  match projectee with | E_Or (_0, _1) -> _0
let __proj__E_Or__item___1 (projectee : expr) : expr=
  match projectee with | E_Or (_0, _1) -> _1
let uu___is_E_Not (projectee : expr) : Prims.bool=
  match projectee with | E_Not _0 -> true | uu___ -> false
let __proj__E_Not__item___0 (projectee : expr) : expr=
  match projectee with | E_Not _0 -> _0
let uu___is_E_IsIRI (projectee : expr) : Prims.bool=
  match projectee with | E_IsIRI _0 -> true | uu___ -> false
let __proj__E_IsIRI__item___0 (projectee : expr) : expr=
  match projectee with | E_IsIRI _0 -> _0
let uu___is_E_IsBlank (projectee : expr) : Prims.bool=
  match projectee with | E_IsBlank _0 -> true | uu___ -> false
let __proj__E_IsBlank__item___0 (projectee : expr) : expr=
  match projectee with | E_IsBlank _0 -> _0
let uu___is_E_IsLiteral (projectee : expr) : Prims.bool=
  match projectee with | E_IsLiteral _0 -> true | uu___ -> false
let __proj__E_IsLiteral__item___0 (projectee : expr) : expr=
  match projectee with | E_IsLiteral _0 -> _0
let uu___is_E_IsNumeric (projectee : expr) : Prims.bool=
  match projectee with | E_IsNumeric _0 -> true | uu___ -> false
let __proj__E_IsNumeric__item___0 (projectee : expr) : expr=
  match projectee with | E_IsNumeric _0 -> _0
let uu___is_E_Str (projectee : expr) : Prims.bool=
  match projectee with | E_Str _0 -> true | uu___ -> false
let __proj__E_Str__item___0 (projectee : expr) : expr=
  match projectee with | E_Str _0 -> _0
let uu___is_E_Lang (projectee : expr) : Prims.bool=
  match projectee with | E_Lang _0 -> true | uu___ -> false
let __proj__E_Lang__item___0 (projectee : expr) : expr=
  match projectee with | E_Lang _0 -> _0
let uu___is_E_Datatype (projectee : expr) : Prims.bool=
  match projectee with | E_Datatype _0 -> true | uu___ -> false
let __proj__E_Datatype__item___0 (projectee : expr) : expr=
  match projectee with | E_Datatype _0 -> _0
let uu___is_E_IRI_fn (projectee : expr) : Prims.bool=
  match projectee with | E_IRI_fn _0 -> true | uu___ -> false
let __proj__E_IRI_fn__item___0 (projectee : expr) : expr=
  match projectee with | E_IRI_fn _0 -> _0
let uu___is_E_HasLang (projectee : expr) : Prims.bool=
  match projectee with | E_HasLang _0 -> true | uu___ -> false
let __proj__E_HasLang__item___0 (projectee : expr) : expr=
  match projectee with | E_HasLang _0 -> _0
let uu___is_E_HasLangDir (projectee : expr) : Prims.bool=
  match projectee with | E_HasLangDir _0 -> true | uu___ -> false
let __proj__E_HasLangDir__item___0 (projectee : expr) : expr=
  match projectee with | E_HasLangDir _0 -> _0
let uu___is_E_LangDir (projectee : expr) : Prims.bool=
  match projectee with | E_LangDir _0 -> true | uu___ -> false
let __proj__E_LangDir__item___0 (projectee : expr) : expr=
  match projectee with | E_LangDir _0 -> _0
let uu___is_E_StrDt (projectee : expr) : Prims.bool=
  match projectee with | E_StrDt (_0, _1) -> true | uu___ -> false
let __proj__E_StrDt__item___0 (projectee : expr) : expr=
  match projectee with | E_StrDt (_0, _1) -> _0
let __proj__E_StrDt__item___1 (projectee : expr) : expr=
  match projectee with | E_StrDt (_0, _1) -> _1
let uu___is_E_StrLang (projectee : expr) : Prims.bool=
  match projectee with | E_StrLang (_0, _1) -> true | uu___ -> false
let __proj__E_StrLang__item___0 (projectee : expr) : expr=
  match projectee with | E_StrLang (_0, _1) -> _0
let __proj__E_StrLang__item___1 (projectee : expr) : expr=
  match projectee with | E_StrLang (_0, _1) -> _1
let uu___is_E_StrLangDir (projectee : expr) : Prims.bool=
  match projectee with | E_StrLangDir (_0, _1, _2) -> true | uu___ -> false
let __proj__E_StrLangDir__item___0 (projectee : expr) : expr=
  match projectee with | E_StrLangDir (_0, _1, _2) -> _0
let __proj__E_StrLangDir__item___1 (projectee : expr) : expr=
  match projectee with | E_StrLangDir (_0, _1, _2) -> _1
let __proj__E_StrLangDir__item___2 (projectee : expr) : expr=
  match projectee with | E_StrLangDir (_0, _1, _2) -> _2
let uu___is_E_Bound (projectee : expr) : Prims.bool=
  match projectee with | E_Bound _0 -> true | uu___ -> false
let __proj__E_Bound__item___0 (projectee : expr) : var_name=
  match projectee with | E_Bound _0 -> _0
let uu___is_E_If (projectee : expr) : Prims.bool=
  match projectee with | E_If (_0, _1, _2) -> true | uu___ -> false
let __proj__E_If__item___0 (projectee : expr) : expr=
  match projectee with | E_If (_0, _1, _2) -> _0
let __proj__E_If__item___1 (projectee : expr) : expr=
  match projectee with | E_If (_0, _1, _2) -> _1
let __proj__E_If__item___2 (projectee : expr) : expr=
  match projectee with | E_If (_0, _1, _2) -> _2
let uu___is_E_Coalesce (projectee : expr) : Prims.bool=
  match projectee with | E_Coalesce _0 -> true | uu___ -> false
let __proj__E_Coalesce__item___0 (projectee : expr) : expr Prims.list=
  match projectee with | E_Coalesce _0 -> _0
let uu___is_E_In (projectee : expr) : Prims.bool=
  match projectee with | E_In (_0, _1) -> true | uu___ -> false
let __proj__E_In__item___0 (projectee : expr) : expr=
  match projectee with | E_In (_0, _1) -> _0
let __proj__E_In__item___1 (projectee : expr) : expr Prims.list=
  match projectee with | E_In (_0, _1) -> _1
let uu___is_E_NotIn (projectee : expr) : Prims.bool=
  match projectee with | E_NotIn (_0, _1) -> true | uu___ -> false
let __proj__E_NotIn__item___0 (projectee : expr) : expr=
  match projectee with | E_NotIn (_0, _1) -> _0
let __proj__E_NotIn__item___1 (projectee : expr) : expr Prims.list=
  match projectee with | E_NotIn (_0, _1) -> _1
let uu___is_E_StrLen (projectee : expr) : Prims.bool=
  match projectee with | E_StrLen _0 -> true | uu___ -> false
let __proj__E_StrLen__item___0 (projectee : expr) : expr=
  match projectee with | E_StrLen _0 -> _0
let uu___is_E_Substr (projectee : expr) : Prims.bool=
  match projectee with | E_Substr (_0, _1, _2) -> true | uu___ -> false
let __proj__E_Substr__item___0 (projectee : expr) : expr=
  match projectee with | E_Substr (_0, _1, _2) -> _0
let __proj__E_Substr__item___1 (projectee : expr) : expr=
  match projectee with | E_Substr (_0, _1, _2) -> _1
let __proj__E_Substr__item___2 (projectee : expr) :
  expr FStar_Pervasives_Native.option=
  match projectee with | E_Substr (_0, _1, _2) -> _2
let uu___is_E_UCase (projectee : expr) : Prims.bool=
  match projectee with | E_UCase _0 -> true | uu___ -> false
let __proj__E_UCase__item___0 (projectee : expr) : expr=
  match projectee with | E_UCase _0 -> _0
let uu___is_E_LCase (projectee : expr) : Prims.bool=
  match projectee with | E_LCase _0 -> true | uu___ -> false
let __proj__E_LCase__item___0 (projectee : expr) : expr=
  match projectee with | E_LCase _0 -> _0
let uu___is_E_StrStarts (projectee : expr) : Prims.bool=
  match projectee with | E_StrStarts (_0, _1) -> true | uu___ -> false
let __proj__E_StrStarts__item___0 (projectee : expr) : expr=
  match projectee with | E_StrStarts (_0, _1) -> _0
let __proj__E_StrStarts__item___1 (projectee : expr) : expr=
  match projectee with | E_StrStarts (_0, _1) -> _1
let uu___is_E_StrEnds (projectee : expr) : Prims.bool=
  match projectee with | E_StrEnds (_0, _1) -> true | uu___ -> false
let __proj__E_StrEnds__item___0 (projectee : expr) : expr=
  match projectee with | E_StrEnds (_0, _1) -> _0
let __proj__E_StrEnds__item___1 (projectee : expr) : expr=
  match projectee with | E_StrEnds (_0, _1) -> _1
let uu___is_E_Contains (projectee : expr) : Prims.bool=
  match projectee with | E_Contains (_0, _1) -> true | uu___ -> false
let __proj__E_Contains__item___0 (projectee : expr) : expr=
  match projectee with | E_Contains (_0, _1) -> _0
let __proj__E_Contains__item___1 (projectee : expr) : expr=
  match projectee with | E_Contains (_0, _1) -> _1
let uu___is_E_StrBefore (projectee : expr) : Prims.bool=
  match projectee with | E_StrBefore (_0, _1) -> true | uu___ -> false
let __proj__E_StrBefore__item___0 (projectee : expr) : expr=
  match projectee with | E_StrBefore (_0, _1) -> _0
let __proj__E_StrBefore__item___1 (projectee : expr) : expr=
  match projectee with | E_StrBefore (_0, _1) -> _1
let uu___is_E_StrAfter (projectee : expr) : Prims.bool=
  match projectee with | E_StrAfter (_0, _1) -> true | uu___ -> false
let __proj__E_StrAfter__item___0 (projectee : expr) : expr=
  match projectee with | E_StrAfter (_0, _1) -> _0
let __proj__E_StrAfter__item___1 (projectee : expr) : expr=
  match projectee with | E_StrAfter (_0, _1) -> _1
let uu___is_E_Concat (projectee : expr) : Prims.bool=
  match projectee with | E_Concat _0 -> true | uu___ -> false
let __proj__E_Concat__item___0 (projectee : expr) : expr Prims.list=
  match projectee with | E_Concat _0 -> _0
let uu___is_E_EncodeForUri (projectee : expr) : Prims.bool=
  match projectee with | E_EncodeForUri _0 -> true | uu___ -> false
let __proj__E_EncodeForUri__item___0 (projectee : expr) : expr=
  match projectee with | E_EncodeForUri _0 -> _0
let uu___is_E_Replace (projectee : expr) : Prims.bool=
  match projectee with | E_Replace (_0, _1, _2, _3) -> true | uu___ -> false
let __proj__E_Replace__item___0 (projectee : expr) : expr=
  match projectee with | E_Replace (_0, _1, _2, _3) -> _0
let __proj__E_Replace__item___1 (projectee : expr) : expr=
  match projectee with | E_Replace (_0, _1, _2, _3) -> _1
let __proj__E_Replace__item___2 (projectee : expr) : expr=
  match projectee with | E_Replace (_0, _1, _2, _3) -> _2
let __proj__E_Replace__item___3 (projectee : expr) :
  expr FStar_Pervasives_Native.option=
  match projectee with | E_Replace (_0, _1, _2, _3) -> _3
let uu___is_E_Regex (projectee : expr) : Prims.bool=
  match projectee with | E_Regex (_0, _1, _2) -> true | uu___ -> false
let __proj__E_Regex__item___0 (projectee : expr) : expr=
  match projectee with | E_Regex (_0, _1, _2) -> _0
let __proj__E_Regex__item___1 (projectee : expr) : expr=
  match projectee with | E_Regex (_0, _1, _2) -> _1
let __proj__E_Regex__item___2 (projectee : expr) :
  expr FStar_Pervasives_Native.option=
  match projectee with | E_Regex (_0, _1, _2) -> _2
let uu___is_E_Abs (projectee : expr) : Prims.bool=
  match projectee with | E_Abs _0 -> true | uu___ -> false
let __proj__E_Abs__item___0 (projectee : expr) : expr=
  match projectee with | E_Abs _0 -> _0
let uu___is_E_Round (projectee : expr) : Prims.bool=
  match projectee with | E_Round _0 -> true | uu___ -> false
let __proj__E_Round__item___0 (projectee : expr) : expr=
  match projectee with | E_Round _0 -> _0
let uu___is_E_Ceil (projectee : expr) : Prims.bool=
  match projectee with | E_Ceil _0 -> true | uu___ -> false
let __proj__E_Ceil__item___0 (projectee : expr) : expr=
  match projectee with | E_Ceil _0 -> _0
let uu___is_E_Floor (projectee : expr) : Prims.bool=
  match projectee with | E_Floor _0 -> true | uu___ -> false
let __proj__E_Floor__item___0 (projectee : expr) : expr=
  match projectee with | E_Floor _0 -> _0
let uu___is_E_MD5 (projectee : expr) : Prims.bool=
  match projectee with | E_MD5 _0 -> true | uu___ -> false
let __proj__E_MD5__item___0 (projectee : expr) : expr=
  match projectee with | E_MD5 _0 -> _0
let uu___is_E_SHA1 (projectee : expr) : Prims.bool=
  match projectee with | E_SHA1 _0 -> true | uu___ -> false
let __proj__E_SHA1__item___0 (projectee : expr) : expr=
  match projectee with | E_SHA1 _0 -> _0
let uu___is_E_SHA256 (projectee : expr) : Prims.bool=
  match projectee with | E_SHA256 _0 -> true | uu___ -> false
let __proj__E_SHA256__item___0 (projectee : expr) : expr=
  match projectee with | E_SHA256 _0 -> _0
let uu___is_E_SHA384 (projectee : expr) : Prims.bool=
  match projectee with | E_SHA384 _0 -> true | uu___ -> false
let __proj__E_SHA384__item___0 (projectee : expr) : expr=
  match projectee with | E_SHA384 _0 -> _0
let uu___is_E_SHA512 (projectee : expr) : Prims.bool=
  match projectee with | E_SHA512 _0 -> true | uu___ -> false
let __proj__E_SHA512__item___0 (projectee : expr) : expr=
  match projectee with | E_SHA512 _0 -> _0
let uu___is_E_Now (projectee : expr) : Prims.bool=
  match projectee with | E_Now -> true | uu___ -> false
let uu___is_E_Year (projectee : expr) : Prims.bool=
  match projectee with | E_Year _0 -> true | uu___ -> false
let __proj__E_Year__item___0 (projectee : expr) : expr=
  match projectee with | E_Year _0 -> _0
let uu___is_E_Month (projectee : expr) : Prims.bool=
  match projectee with | E_Month _0 -> true | uu___ -> false
let __proj__E_Month__item___0 (projectee : expr) : expr=
  match projectee with | E_Month _0 -> _0
let uu___is_E_Day (projectee : expr) : Prims.bool=
  match projectee with | E_Day _0 -> true | uu___ -> false
let __proj__E_Day__item___0 (projectee : expr) : expr=
  match projectee with | E_Day _0 -> _0
let uu___is_E_Hours (projectee : expr) : Prims.bool=
  match projectee with | E_Hours _0 -> true | uu___ -> false
let __proj__E_Hours__item___0 (projectee : expr) : expr=
  match projectee with | E_Hours _0 -> _0
let uu___is_E_Minutes (projectee : expr) : Prims.bool=
  match projectee with | E_Minutes _0 -> true | uu___ -> false
let __proj__E_Minutes__item___0 (projectee : expr) : expr=
  match projectee with | E_Minutes _0 -> _0
let uu___is_E_Seconds (projectee : expr) : Prims.bool=
  match projectee with | E_Seconds _0 -> true | uu___ -> false
let __proj__E_Seconds__item___0 (projectee : expr) : expr=
  match projectee with | E_Seconds _0 -> _0
let uu___is_E_Timezone (projectee : expr) : Prims.bool=
  match projectee with | E_Timezone _0 -> true | uu___ -> false
let __proj__E_Timezone__item___0 (projectee : expr) : expr=
  match projectee with | E_Timezone _0 -> _0
let uu___is_E_Tz (projectee : expr) : Prims.bool=
  match projectee with | E_Tz _0 -> true | uu___ -> false
let __proj__E_Tz__item___0 (projectee : expr) : expr=
  match projectee with | E_Tz _0 -> _0
let uu___is_E_SameTerm (projectee : expr) : Prims.bool=
  match projectee with | E_SameTerm (_0, _1) -> true | uu___ -> false
let __proj__E_SameTerm__item___0 (projectee : expr) : expr=
  match projectee with | E_SameTerm (_0, _1) -> _0
let __proj__E_SameTerm__item___1 (projectee : expr) : expr=
  match projectee with | E_SameTerm (_0, _1) -> _1
let uu___is_E_Exists (projectee : expr) : Prims.bool=
  match projectee with | E_Exists _0 -> true | uu___ -> false
let __proj__E_Exists__item___0 (projectee : expr) : group_graph_pattern=
  match projectee with | E_Exists _0 -> _0
let uu___is_E_NotExists (projectee : expr) : Prims.bool=
  match projectee with | E_NotExists _0 -> true | uu___ -> false
let __proj__E_NotExists__item___0 (projectee : expr) : group_graph_pattern=
  match projectee with | E_NotExists _0 -> _0
let uu___is_E_Aggregate (projectee : expr) : Prims.bool=
  match projectee with | E_Aggregate (_0, _1, _2) -> true | uu___ -> false
let __proj__E_Aggregate__item___0 (projectee : expr) : aggregate_fn=
  match projectee with | E_Aggregate (_0, _1, _2) -> _0
let __proj__E_Aggregate__item___1 (projectee : expr) : Prims.bool=
  match projectee with | E_Aggregate (_0, _1, _2) -> _1
let __proj__E_Aggregate__item___2 (projectee : expr) : expr=
  match projectee with | E_Aggregate (_0, _1, _2) -> _2
let uu___is_E_FunctionCall (projectee : expr) : Prims.bool=
  match projectee with | E_FunctionCall (_0, _1) -> true | uu___ -> false
let __proj__E_FunctionCall__item___0 (projectee : expr) : RDF_Term.wf_iri=
  match projectee with | E_FunctionCall (_0, _1) -> _0
let __proj__E_FunctionCall__item___1 (projectee : expr) : expr Prims.list=
  match projectee with | E_FunctionCall (_0, _1) -> _1
let uu___is_E_TripleTerm (projectee : expr) : Prims.bool=
  match projectee with | E_TripleTerm (_0, _1, _2) -> true | uu___ -> false
let __proj__E_TripleTerm__item___0 (projectee : expr) : expr=
  match projectee with | E_TripleTerm (_0, _1, _2) -> _0
let __proj__E_TripleTerm__item___1 (projectee : expr) : expr=
  match projectee with | E_TripleTerm (_0, _1, _2) -> _1
let __proj__E_TripleTerm__item___2 (projectee : expr) : expr=
  match projectee with | E_TripleTerm (_0, _1, _2) -> _2
let uu___is_E_TTSubject (projectee : expr) : Prims.bool=
  match projectee with | E_TTSubject _0 -> true | uu___ -> false
let __proj__E_TTSubject__item___0 (projectee : expr) : expr=
  match projectee with | E_TTSubject _0 -> _0
let uu___is_E_TTPredicate (projectee : expr) : Prims.bool=
  match projectee with | E_TTPredicate _0 -> true | uu___ -> false
let __proj__E_TTPredicate__item___0 (projectee : expr) : expr=
  match projectee with | E_TTPredicate _0 -> _0
let uu___is_E_TTObject (projectee : expr) : Prims.bool=
  match projectee with | E_TTObject _0 -> true | uu___ -> false
let __proj__E_TTObject__item___0 (projectee : expr) : expr=
  match projectee with | E_TTObject _0 -> _0
let uu___is_E_IsTriple (projectee : expr) : Prims.bool=
  match projectee with | E_IsTriple _0 -> true | uu___ -> false
let __proj__E_IsTriple__item___0 (projectee : expr) : expr=
  match projectee with | E_IsTriple _0 -> _0
let uu___is_PP_IRI (projectee : property_path) : Prims.bool=
  match projectee with | PP_IRI _0 -> true | uu___ -> false
let __proj__PP_IRI__item___0 (projectee : property_path) : RDF_Term.wf_iri=
  match projectee with | PP_IRI _0 -> _0
let uu___is_PP_Inverse (projectee : property_path) : Prims.bool=
  match projectee with | PP_Inverse _0 -> true | uu___ -> false
let __proj__PP_Inverse__item___0 (projectee : property_path) : property_path=
  match projectee with | PP_Inverse _0 -> _0
let uu___is_PP_Sequence (projectee : property_path) : Prims.bool=
  match projectee with | PP_Sequence (_0, _1) -> true | uu___ -> false
let __proj__PP_Sequence__item___0 (projectee : property_path) :
  property_path= match projectee with | PP_Sequence (_0, _1) -> _0
let __proj__PP_Sequence__item___1 (projectee : property_path) :
  property_path= match projectee with | PP_Sequence (_0, _1) -> _1
let uu___is_PP_Alternative (projectee : property_path) : Prims.bool=
  match projectee with | PP_Alternative (_0, _1) -> true | uu___ -> false
let __proj__PP_Alternative__item___0 (projectee : property_path) :
  property_path= match projectee with | PP_Alternative (_0, _1) -> _0
let __proj__PP_Alternative__item___1 (projectee : property_path) :
  property_path= match projectee with | PP_Alternative (_0, _1) -> _1
let uu___is_PP_ZeroOrMore (projectee : property_path) : Prims.bool=
  match projectee with | PP_ZeroOrMore _0 -> true | uu___ -> false
let __proj__PP_ZeroOrMore__item___0 (projectee : property_path) :
  property_path= match projectee with | PP_ZeroOrMore _0 -> _0
let uu___is_PP_OneOrMore (projectee : property_path) : Prims.bool=
  match projectee with | PP_OneOrMore _0 -> true | uu___ -> false
let __proj__PP_OneOrMore__item___0 (projectee : property_path) :
  property_path= match projectee with | PP_OneOrMore _0 -> _0
let uu___is_PP_ZeroOrOne (projectee : property_path) : Prims.bool=
  match projectee with | PP_ZeroOrOne _0 -> true | uu___ -> false
let __proj__PP_ZeroOrOne__item___0 (projectee : property_path) :
  property_path= match projectee with | PP_ZeroOrOne _0 -> _0
let uu___is_PP_NegatedSet (projectee : property_path) : Prims.bool=
  match projectee with | PP_NegatedSet _0 -> true | uu___ -> false
let __proj__PP_NegatedSet__item___0 (projectee : property_path) :
  property_path Prims.list= match projectee with | PP_NegatedSet _0 -> _0
let uu___is_GP_BGP (projectee : group_graph_pattern) : Prims.bool=
  match projectee with | GP_BGP _0 -> true | uu___ -> false
let __proj__GP_BGP__item___0 (projectee : group_graph_pattern) : bgp=
  match projectee with | GP_BGP _0 -> _0
let uu___is_GP_Join (projectee : group_graph_pattern) : Prims.bool=
  match projectee with | GP_Join (_0, _1) -> true | uu___ -> false
let __proj__GP_Join__item___0 (projectee : group_graph_pattern) :
  group_graph_pattern= match projectee with | GP_Join (_0, _1) -> _0
let __proj__GP_Join__item___1 (projectee : group_graph_pattern) :
  group_graph_pattern= match projectee with | GP_Join (_0, _1) -> _1
let uu___is_GP_LeftJoin (projectee : group_graph_pattern) : Prims.bool=
  match projectee with | GP_LeftJoin (_0, _1, _2) -> true | uu___ -> false
let __proj__GP_LeftJoin__item___0 (projectee : group_graph_pattern) :
  group_graph_pattern= match projectee with | GP_LeftJoin (_0, _1, _2) -> _0
let __proj__GP_LeftJoin__item___1 (projectee : group_graph_pattern) :
  group_graph_pattern= match projectee with | GP_LeftJoin (_0, _1, _2) -> _1
let __proj__GP_LeftJoin__item___2 (projectee : group_graph_pattern) : 
  expr= match projectee with | GP_LeftJoin (_0, _1, _2) -> _2
let uu___is_GP_Filter (projectee : group_graph_pattern) : Prims.bool=
  match projectee with | GP_Filter (_0, _1) -> true | uu___ -> false
let __proj__GP_Filter__item___0 (projectee : group_graph_pattern) : expr=
  match projectee with | GP_Filter (_0, _1) -> _0
let __proj__GP_Filter__item___1 (projectee : group_graph_pattern) :
  group_graph_pattern= match projectee with | GP_Filter (_0, _1) -> _1
let uu___is_GP_Union (projectee : group_graph_pattern) : Prims.bool=
  match projectee with | GP_Union (_0, _1) -> true | uu___ -> false
let __proj__GP_Union__item___0 (projectee : group_graph_pattern) :
  group_graph_pattern= match projectee with | GP_Union (_0, _1) -> _0
let __proj__GP_Union__item___1 (projectee : group_graph_pattern) :
  group_graph_pattern= match projectee with | GP_Union (_0, _1) -> _1
let uu___is_GP_Graph (projectee : group_graph_pattern) : Prims.bool=
  match projectee with | GP_Graph (_0, _1) -> true | uu___ -> false
let __proj__GP_Graph__item___0 (projectee : group_graph_pattern) :
  pattern_term= match projectee with | GP_Graph (_0, _1) -> _0
let __proj__GP_Graph__item___1 (projectee : group_graph_pattern) :
  group_graph_pattern= match projectee with | GP_Graph (_0, _1) -> _1
let uu___is_GP_Minus (projectee : group_graph_pattern) : Prims.bool=
  match projectee with | GP_Minus (_0, _1) -> true | uu___ -> false
let __proj__GP_Minus__item___0 (projectee : group_graph_pattern) :
  group_graph_pattern= match projectee with | GP_Minus (_0, _1) -> _0
let __proj__GP_Minus__item___1 (projectee : group_graph_pattern) :
  group_graph_pattern= match projectee with | GP_Minus (_0, _1) -> _1
let uu___is_GP_Lateral (projectee : group_graph_pattern) : Prims.bool=
  match projectee with | GP_Lateral (_0, _1) -> true | uu___ -> false
let __proj__GP_Lateral__item___0 (projectee : group_graph_pattern) :
  group_graph_pattern= match projectee with | GP_Lateral (_0, _1) -> _0
let __proj__GP_Lateral__item___1 (projectee : group_graph_pattern) :
  group_graph_pattern= match projectee with | GP_Lateral (_0, _1) -> _1
let uu___is_GP_Bind (projectee : group_graph_pattern) : Prims.bool=
  match projectee with | GP_Bind (_0, _1, _2) -> true | uu___ -> false
let __proj__GP_Bind__item___0 (projectee : group_graph_pattern) : expr=
  match projectee with | GP_Bind (_0, _1, _2) -> _0
let __proj__GP_Bind__item___1 (projectee : group_graph_pattern) : var_name=
  match projectee with | GP_Bind (_0, _1, _2) -> _1
let __proj__GP_Bind__item___2 (projectee : group_graph_pattern) :
  group_graph_pattern= match projectee with | GP_Bind (_0, _1, _2) -> _2
let uu___is_GP_Values (projectee : group_graph_pattern) : Prims.bool=
  match projectee with | GP_Values (_0, _1) -> true | uu___ -> false
let __proj__GP_Values__item___0 (projectee : group_graph_pattern) :
  var_name Prims.list= match projectee with | GP_Values (_0, _1) -> _0
let __proj__GP_Values__item___1 (projectee : group_graph_pattern) :
  RDF_Term.rdf_term FStar_Pervasives_Native.option Prims.list Prims.list=
  match projectee with | GP_Values (_0, _1) -> _1
let uu___is_GP_Service (projectee : group_graph_pattern) : Prims.bool=
  match projectee with | GP_Service (_0, _1, _2) -> true | uu___ -> false
let __proj__GP_Service__item___0 (projectee : group_graph_pattern) :
  RDF_Term.wf_iri= match projectee with | GP_Service (_0, _1, _2) -> _0
let __proj__GP_Service__item___1 (projectee : group_graph_pattern) :
  group_graph_pattern= match projectee with | GP_Service (_0, _1, _2) -> _1
let __proj__GP_Service__item___2 (projectee : group_graph_pattern) :
  Prims.bool= match projectee with | GP_Service (_0, _1, _2) -> _2
let uu___is_GP_ServiceVar (projectee : group_graph_pattern) : Prims.bool=
  match projectee with | GP_ServiceVar (_0, _1, _2) -> true | uu___ -> false
let __proj__GP_ServiceVar__item___0 (projectee : group_graph_pattern) :
  var_name= match projectee with | GP_ServiceVar (_0, _1, _2) -> _0
let __proj__GP_ServiceVar__item___1 (projectee : group_graph_pattern) :
  group_graph_pattern=
  match projectee with | GP_ServiceVar (_0, _1, _2) -> _1
let __proj__GP_ServiceVar__item___2 (projectee : group_graph_pattern) :
  Prims.bool= match projectee with | GP_ServiceVar (_0, _1, _2) -> _2
let uu___is_GP_SubSelect (projectee : group_graph_pattern) : Prims.bool=
  match projectee with | GP_SubSelect _0 -> true | uu___ -> false
let __proj__GP_SubSelect__item___0 (projectee : group_graph_pattern) : 
  query= match projectee with | GP_SubSelect _0 -> _0
let uu___is_GP_PropertyPath (projectee : group_graph_pattern) : Prims.bool=
  match projectee with
  | GP_PropertyPath (_0, _1, _2) -> true
  | uu___ -> false
let __proj__GP_PropertyPath__item___0 (projectee : group_graph_pattern) :
  pattern_subject= match projectee with | GP_PropertyPath (_0, _1, _2) -> _0
let __proj__GP_PropertyPath__item___1 (projectee : group_graph_pattern) :
  property_path= match projectee with | GP_PropertyPath (_0, _1, _2) -> _1
let __proj__GP_PropertyPath__item___2 (projectee : group_graph_pattern) :
  pattern_term= match projectee with | GP_PropertyPath (_0, _1, _2) -> _2
let uu___is_GP_Empty (projectee : group_graph_pattern) : Prims.bool=
  match projectee with | GP_Empty -> true | uu___ -> false
let uu___is_OC_Asc (projectee : order_condition) : Prims.bool=
  match projectee with | OC_Asc _0 -> true | uu___ -> false
let __proj__OC_Asc__item___0 (projectee : order_condition) : expr=
  match projectee with | OC_Asc _0 -> _0
let uu___is_OC_Desc (projectee : order_condition) : Prims.bool=
  match projectee with | OC_Desc _0 -> true | uu___ -> false
let __proj__OC_Desc__item___0 (projectee : order_condition) : expr=
  match projectee with | OC_Desc _0 -> _0
let __proj__Mksolution_modifier__item__sm_order_by
  (projectee : solution_modifier) :
  order_condition Prims.list FStar_Pervasives_Native.option=
  match projectee with
  | { sm_order_by; sm_distinct; sm_reduced; sm_offset; sm_limit;_} ->
      sm_order_by
let __proj__Mksolution_modifier__item__sm_distinct
  (projectee : solution_modifier) : Prims.bool=
  match projectee with
  | { sm_order_by; sm_distinct; sm_reduced; sm_offset; sm_limit;_} ->
      sm_distinct
let __proj__Mksolution_modifier__item__sm_reduced
  (projectee : solution_modifier) : Prims.bool=
  match projectee with
  | { sm_order_by; sm_distinct; sm_reduced; sm_offset; sm_limit;_} ->
      sm_reduced
let __proj__Mksolution_modifier__item__sm_offset
  (projectee : solution_modifier) : Prims.nat FStar_Pervasives_Native.option=
  match projectee with
  | { sm_order_by; sm_distinct; sm_reduced; sm_offset; sm_limit;_} ->
      sm_offset
let __proj__Mksolution_modifier__item__sm_limit
  (projectee : solution_modifier) : Prims.nat FStar_Pervasives_Native.option=
  match projectee with
  | { sm_order_by; sm_distinct; sm_reduced; sm_offset; sm_limit;_} ->
      sm_limit
let uu___is_SI_Var (projectee : select_item) : Prims.bool=
  match projectee with | SI_Var _0 -> true | uu___ -> false
let __proj__SI_Var__item___0 (projectee : select_item) : var_name=
  match projectee with | SI_Var _0 -> _0
let uu___is_SI_Expr (projectee : select_item) : Prims.bool=
  match projectee with | SI_Expr (_0, _1) -> true | uu___ -> false
let __proj__SI_Expr__item___0 (projectee : select_item) : expr=
  match projectee with | SI_Expr (_0, _1) -> _0
let __proj__SI_Expr__item___1 (projectee : select_item) : var_name=
  match projectee with | SI_Expr (_0, _1) -> _1
let uu___is_Select_Vars (projectee : select_clause) : Prims.bool=
  match projectee with | Select_Vars _0 -> true | uu___ -> false
let __proj__Select_Vars__item___0 (projectee : select_clause) :
  select_item Prims.list= match projectee with | Select_Vars _0 -> _0
let uu___is_Select_All (projectee : select_clause) : Prims.bool=
  match projectee with | Select_All -> true | uu___ -> false
let uu___is_GC_Var (projectee : group_condition) : Prims.bool=
  match projectee with | GC_Var _0 -> true | uu___ -> false
let __proj__GC_Var__item___0 (projectee : group_condition) : var_name=
  match projectee with | GC_Var _0 -> _0
let uu___is_GC_Expr (projectee : group_condition) : Prims.bool=
  match projectee with | GC_Expr (_0, _1) -> true | uu___ -> false
let __proj__GC_Expr__item___0 (projectee : group_condition) : expr=
  match projectee with | GC_Expr (_0, _1) -> _0
let __proj__GC_Expr__item___1 (projectee : group_condition) :
  var_name FStar_Pervasives_Native.option=
  match projectee with | GC_Expr (_0, _1) -> _1
let uu___is_GC_BuiltIn (projectee : group_condition) : Prims.bool=
  match projectee with | GC_BuiltIn _0 -> true | uu___ -> false
let __proj__GC_BuiltIn__item___0 (projectee : group_condition) : expr=
  match projectee with | GC_BuiltIn _0 -> _0
let uu___is_QF_Select (projectee : query_form) : Prims.bool=
  match projectee with | QF_Select _0 -> true | uu___ -> false
let __proj__QF_Select__item___0 (projectee : query_form) : select_clause=
  match projectee with | QF_Select _0 -> _0
let uu___is_QF_Construct (projectee : query_form) : Prims.bool=
  match projectee with | QF_Construct _0 -> true | uu___ -> false
let __proj__QF_Construct__item___0 (projectee : query_form) :
  triple_pattern Prims.list= match projectee with | QF_Construct _0 -> _0
let uu___is_QF_Ask (projectee : query_form) : Prims.bool=
  match projectee with | QF_Ask -> true | uu___ -> false
let uu___is_QF_Describe (projectee : query_form) : Prims.bool=
  match projectee with | QF_Describe _0 -> true | uu___ -> false
let __proj__QF_Describe__item___0 (projectee : query_form) :
  pattern_term Prims.list= match projectee with | QF_Describe _0 -> _0
let uu___is_DC_Default (projectee : dataset_clause) : Prims.bool=
  match projectee with | DC_Default _0 -> true | uu___ -> false
let __proj__DC_Default__item___0 (projectee : dataset_clause) :
  RDF_Term.wf_iri= match projectee with | DC_Default _0 -> _0
let uu___is_DC_Named (projectee : dataset_clause) : Prims.bool=
  match projectee with | DC_Named _0 -> true | uu___ -> false
let __proj__DC_Named__item___0 (projectee : dataset_clause) :
  RDF_Term.wf_iri= match projectee with | DC_Named _0 -> _0
let __proj__Mkquery__item__q_base (projectee : query) :
  RDF_Term.wf_iri FStar_Pervasives_Native.option=
  match projectee with
  | { q_base; q_prefixes; q_form; q_dataset; q_pattern; q_group_by; q_having;
      q_modifier; q_values;_} -> q_base
let __proj__Mkquery__item__q_prefixes (projectee : query) :
  (Prims.string * RDF_Term.wf_iri) Prims.list=
  match projectee with
  | { q_base; q_prefixes; q_form; q_dataset; q_pattern; q_group_by; q_having;
      q_modifier; q_values;_} -> q_prefixes
let __proj__Mkquery__item__q_form (projectee : query) : query_form=
  match projectee with
  | { q_base; q_prefixes; q_form; q_dataset; q_pattern; q_group_by; q_having;
      q_modifier; q_values;_} -> q_form
let __proj__Mkquery__item__q_dataset (projectee : query) :
  dataset_clause Prims.list=
  match projectee with
  | { q_base; q_prefixes; q_form; q_dataset; q_pattern; q_group_by; q_having;
      q_modifier; q_values;_} -> q_dataset
let __proj__Mkquery__item__q_pattern (projectee : query) :
  group_graph_pattern=
  match projectee with
  | { q_base; q_prefixes; q_form; q_dataset; q_pattern; q_group_by; q_having;
      q_modifier; q_values;_} -> q_pattern
let __proj__Mkquery__item__q_group_by (projectee : query) :
  group_condition Prims.list FStar_Pervasives_Native.option=
  match projectee with
  | { q_base; q_prefixes; q_form; q_dataset; q_pattern; q_group_by; q_having;
      q_modifier; q_values;_} -> q_group_by
let __proj__Mkquery__item__q_having (projectee : query) :
  expr Prims.list FStar_Pervasives_Native.option=
  match projectee with
  | { q_base; q_prefixes; q_form; q_dataset; q_pattern; q_group_by; q_having;
      q_modifier; q_values;_} -> q_having
let __proj__Mkquery__item__q_modifier (projectee : query) :
  solution_modifier=
  match projectee with
  | { q_base; q_prefixes; q_form; q_dataset; q_pattern; q_group_by; q_having;
      q_modifier; q_values;_} -> q_modifier
let __proj__Mkquery__item__q_values (projectee : query) :
  (var_name * RDF_Term.rdf_term) Prims.list Prims.list
    FStar_Pervasives_Native.option=
  match projectee with
  | { q_base; q_prefixes; q_form; q_dataset; q_pattern; q_group_by; q_having;
      q_modifier; q_values;_} -> q_values
type having_condition = expr
let query_with_prebound_values (q : query)
  (vals : (var_name * RDF_Term.rdf_term) Prims.list Prims.list) : query=
  {
    q_base = (q.q_base);
    q_prefixes = (q.q_prefixes);
    q_form = (q.q_form);
    q_dataset = (q.q_dataset);
    q_pattern = (q.q_pattern);
    q_group_by = (q.q_group_by);
    q_having = (q.q_having);
    q_modifier = (q.q_modifier);
    q_values = (FStar_Pervasives_Native.Some vals)
  }
let query_form_of (q : query) : query_form= q.q_form
let query_pattern_of (q : query) : group_graph_pattern= q.q_pattern
let query_values_of (q : query) :
  (var_name * RDF_Term.rdf_term) Prims.list Prims.list
    FStar_Pervasives_Native.option=
  q.q_values
let query_with_pattern (q : query) (p : group_graph_pattern) : query=
  {
    q_base = (q.q_base);
    q_prefixes = (q.q_prefixes);
    q_form = (q.q_form);
    q_dataset = (q.q_dataset);
    q_pattern = p;
    q_group_by = (q.q_group_by);
    q_having = (q.q_having);
    q_modifier = (q.q_modifier);
    q_values = (q.q_values)
  }
type graph_ref =
  | GR_Default 
  | GR_Named 
  | GR_All 
  | GR_Graph of RDF_Term.wf_iri 
let uu___is_GR_Default (projectee : graph_ref) : Prims.bool=
  match projectee with | GR_Default -> true | uu___ -> false
let uu___is_GR_Named (projectee : graph_ref) : Prims.bool=
  match projectee with | GR_Named -> true | uu___ -> false
let uu___is_GR_All (projectee : graph_ref) : Prims.bool=
  match projectee with | GR_All -> true | uu___ -> false
let uu___is_GR_Graph (projectee : graph_ref) : Prims.bool=
  match projectee with | GR_Graph _0 -> true | uu___ -> false
let __proj__GR_Graph__item___0 (projectee : graph_ref) : RDF_Term.wf_iri=
  match projectee with | GR_Graph _0 -> _0
type update_op =
  | U_Load of Prims.bool * RDF_Term.wf_iri * RDF_Term.wf_iri
  FStar_Pervasives_Native.option 
  | U_Clear of Prims.bool * graph_ref 
  | U_Drop of Prims.bool * graph_ref 
  | U_Create of Prims.bool * RDF_Term.wf_iri 
  | U_Add of Prims.bool * graph_ref * graph_ref 
  | U_Move of Prims.bool * graph_ref * graph_ref 
  | U_Copy of Prims.bool * graph_ref * graph_ref 
  | U_InsertData of group_graph_pattern 
  | U_DeleteData of group_graph_pattern 
  | U_DeleteWhere of group_graph_pattern 
  | U_Modify of RDF_Term.wf_iri FStar_Pervasives_Native.option *
  group_graph_pattern FStar_Pervasives_Native.option * group_graph_pattern
  FStar_Pervasives_Native.option * dataset_clause Prims.list *
  group_graph_pattern 
let uu___is_U_Load (projectee : update_op) : Prims.bool=
  match projectee with | U_Load (_0, _1, _2) -> true | uu___ -> false
let __proj__U_Load__item___0 (projectee : update_op) : Prims.bool=
  match projectee with | U_Load (_0, _1, _2) -> _0
let __proj__U_Load__item___1 (projectee : update_op) : RDF_Term.wf_iri=
  match projectee with | U_Load (_0, _1, _2) -> _1
let __proj__U_Load__item___2 (projectee : update_op) :
  RDF_Term.wf_iri FStar_Pervasives_Native.option=
  match projectee with | U_Load (_0, _1, _2) -> _2
let uu___is_U_Clear (projectee : update_op) : Prims.bool=
  match projectee with | U_Clear (_0, _1) -> true | uu___ -> false
let __proj__U_Clear__item___0 (projectee : update_op) : Prims.bool=
  match projectee with | U_Clear (_0, _1) -> _0
let __proj__U_Clear__item___1 (projectee : update_op) : graph_ref=
  match projectee with | U_Clear (_0, _1) -> _1
let uu___is_U_Drop (projectee : update_op) : Prims.bool=
  match projectee with | U_Drop (_0, _1) -> true | uu___ -> false
let __proj__U_Drop__item___0 (projectee : update_op) : Prims.bool=
  match projectee with | U_Drop (_0, _1) -> _0
let __proj__U_Drop__item___1 (projectee : update_op) : graph_ref=
  match projectee with | U_Drop (_0, _1) -> _1
let uu___is_U_Create (projectee : update_op) : Prims.bool=
  match projectee with | U_Create (_0, _1) -> true | uu___ -> false
let __proj__U_Create__item___0 (projectee : update_op) : Prims.bool=
  match projectee with | U_Create (_0, _1) -> _0
let __proj__U_Create__item___1 (projectee : update_op) : RDF_Term.wf_iri=
  match projectee with | U_Create (_0, _1) -> _1
let uu___is_U_Add (projectee : update_op) : Prims.bool=
  match projectee with | U_Add (_0, _1, _2) -> true | uu___ -> false
let __proj__U_Add__item___0 (projectee : update_op) : Prims.bool=
  match projectee with | U_Add (_0, _1, _2) -> _0
let __proj__U_Add__item___1 (projectee : update_op) : graph_ref=
  match projectee with | U_Add (_0, _1, _2) -> _1
let __proj__U_Add__item___2 (projectee : update_op) : graph_ref=
  match projectee with | U_Add (_0, _1, _2) -> _2
let uu___is_U_Move (projectee : update_op) : Prims.bool=
  match projectee with | U_Move (_0, _1, _2) -> true | uu___ -> false
let __proj__U_Move__item___0 (projectee : update_op) : Prims.bool=
  match projectee with | U_Move (_0, _1, _2) -> _0
let __proj__U_Move__item___1 (projectee : update_op) : graph_ref=
  match projectee with | U_Move (_0, _1, _2) -> _1
let __proj__U_Move__item___2 (projectee : update_op) : graph_ref=
  match projectee with | U_Move (_0, _1, _2) -> _2
let uu___is_U_Copy (projectee : update_op) : Prims.bool=
  match projectee with | U_Copy (_0, _1, _2) -> true | uu___ -> false
let __proj__U_Copy__item___0 (projectee : update_op) : Prims.bool=
  match projectee with | U_Copy (_0, _1, _2) -> _0
let __proj__U_Copy__item___1 (projectee : update_op) : graph_ref=
  match projectee with | U_Copy (_0, _1, _2) -> _1
let __proj__U_Copy__item___2 (projectee : update_op) : graph_ref=
  match projectee with | U_Copy (_0, _1, _2) -> _2
let uu___is_U_InsertData (projectee : update_op) : Prims.bool=
  match projectee with | U_InsertData _0 -> true | uu___ -> false
let __proj__U_InsertData__item___0 (projectee : update_op) :
  group_graph_pattern= match projectee with | U_InsertData _0 -> _0
let uu___is_U_DeleteData (projectee : update_op) : Prims.bool=
  match projectee with | U_DeleteData _0 -> true | uu___ -> false
let __proj__U_DeleteData__item___0 (projectee : update_op) :
  group_graph_pattern= match projectee with | U_DeleteData _0 -> _0
let uu___is_U_DeleteWhere (projectee : update_op) : Prims.bool=
  match projectee with | U_DeleteWhere _0 -> true | uu___ -> false
let __proj__U_DeleteWhere__item___0 (projectee : update_op) :
  group_graph_pattern= match projectee with | U_DeleteWhere _0 -> _0
let uu___is_U_Modify (projectee : update_op) : Prims.bool=
  match projectee with
  | U_Modify (_0, _1, _2, _3, _4) -> true
  | uu___ -> false
let __proj__U_Modify__item___0 (projectee : update_op) :
  RDF_Term.wf_iri FStar_Pervasives_Native.option=
  match projectee with | U_Modify (_0, _1, _2, _3, _4) -> _0
let __proj__U_Modify__item___1 (projectee : update_op) :
  group_graph_pattern FStar_Pervasives_Native.option=
  match projectee with | U_Modify (_0, _1, _2, _3, _4) -> _1
let __proj__U_Modify__item___2 (projectee : update_op) :
  group_graph_pattern FStar_Pervasives_Native.option=
  match projectee with | U_Modify (_0, _1, _2, _3, _4) -> _2
let __proj__U_Modify__item___3 (projectee : update_op) :
  dataset_clause Prims.list=
  match projectee with | U_Modify (_0, _1, _2, _3, _4) -> _3
let __proj__U_Modify__item___4 (projectee : update_op) : group_graph_pattern=
  match projectee with | U_Modify (_0, _1, _2, _3, _4) -> _4
type sparql_update =
  {
  u_base: RDF_Term.wf_iri FStar_Pervasives_Native.option ;
  u_prefixes: (Prims.string * RDF_Term.wf_iri) Prims.list ;
  u_ops: update_op Prims.list }
let __proj__Mksparql_update__item__u_base (projectee : sparql_update) :
  RDF_Term.wf_iri FStar_Pervasives_Native.option=
  match projectee with | { u_base; u_prefixes; u_ops;_} -> u_base
let __proj__Mksparql_update__item__u_prefixes (projectee : sparql_update) :
  (Prims.string * RDF_Term.wf_iri) Prims.list=
  match projectee with | { u_base; u_prefixes; u_ops;_} -> u_prefixes
let __proj__Mksparql_update__item__u_ops (projectee : sparql_update) :
  update_op Prims.list=
  match projectee with | { u_base; u_prefixes; u_ops;_} -> u_ops
let rec list_filter_map_acc :
  'a 'b .
    ('a -> 'b FStar_Pervasives_Native.option) ->
      'a Prims.list -> 'b Prims.list -> 'b Prims.list
  =
  fun f l acc ->
    match l with
    | [] -> acc
    | x::xs ->
        (match f x with
         | FStar_Pervasives_Native.Some y ->
             list_filter_map_acc f xs (y :: acc)
         | FStar_Pervasives_Native.None -> list_filter_map_acc f xs acc)
let list_filter_map (f : 'a -> 'b FStar_Pervasives_Native.option)
  (l : 'a Prims.list) : 'b Prims.list=
  FStar_List_Tot_Base.rev (list_filter_map_acc f l [])
let rec list_is_prefix : 'a . 'a Prims.list -> 'a Prims.list -> Prims.bool =
  fun prefix lst ->
    match (prefix, lst) with
    | ([], uu___) -> true
    | (uu___, []) -> false
    | (x::xs, y::ys) -> (x = y) && (list_is_prefix xs ys)
let rec list_contains_sublist :
  'a . 'a Prims.list -> 'a Prims.list -> Prims.bool =
  fun needle haystack ->
    match haystack with
    | [] -> Prims.uu___is_Nil needle
    | uu___::rest ->
        (list_is_prefix needle haystack) ||
          (list_contains_sublist needle rest)
let rec list_drop : 'a . Prims.nat -> 'a Prims.list -> 'a Prims.list =
  fun n l ->
    if n = Prims.int_zero
    then l
    else
      (match l with
       | [] -> []
       | uu___1::tl -> list_drop (n - Prims.int_one) tl)
let rec list_take : 'a . Prims.nat -> 'a Prims.list -> 'a Prims.list =
  fun n l ->
    if n = Prims.int_zero
    then []
    else
      (match l with
       | [] -> []
       | hd::tl -> hd :: (list_take (n - Prims.int_one) tl))
let string_contains (s : Prims.string) (sub : Prims.string) : Prims.bool=
  list_contains_sublist (FStar_String.list_of_string sub)
    (FStar_String.list_of_string s)
let string_starts_with (s : Prims.string) (prefix : Prims.string) :
  Prims.bool=
  list_is_prefix (FStar_String.list_of_string prefix)
    (FStar_String.list_of_string s)
let string_ends_with (s : Prims.string) (suffix : Prims.string) : Prims.bool=
  list_is_prefix
    (FStar_List_Tot_Base.rev (FStar_String.list_of_string suffix))
    (FStar_List_Tot_Base.rev (FStar_String.list_of_string s))
let string_length (s : Prims.string) : Prims.nat= FStar_String.strlen s
let string_substring (s : Prims.string) (start : Prims.nat)
  (len : Prims.nat FStar_Pervasives_Native.option) : Prims.string=
  let slen = FStar_String.strlen s in
  let start' = if start >= slen then slen else start in
  let actual_len =
    match len with
    | FStar_Pervasives_Native.Some l ->
        if (start' + l) > slen then slen - start' else l
    | FStar_Pervasives_Native.None -> slen - start' in
  if (actual_len = Prims.int_zero) || (start' >= slen)
  then ""
  else FStar_String.sub s start' actual_len
module Uucp_case_runtime = struct
  (* Issue #250: Unicode-aware UCASE()/LCASE() via `uucp`.
     `cmap_utf_8` is uucp's own documented recipe (uucp.mli,
     "Default case conversion on UTF-8 strings") for applying a
     per-Uchar case map across a UTF-8-encoded OCaml string. Invalid
     UTF-8 byte sequences decode to U+FFFD (replacement character)
     rather than raising -- SPARQL literals are already validated
     UTF-8 by the F*-side lexical-form parser, so this path is a
     defensive fallback, not the common case. *)
  let cmap_utf_8 (cmap : Uchar.t -> [ `Self | `Uchars of Uchar.t list ]) (s : string) : string =
    (* SPARQL11_Algebra.ml opens `Prims` at file scope, which rebinds
       `(+)`/`(-)`/etc. to Z.add/Z.sub (F*'s Prims.int/nat are
       unbounded, extracted via zarith). `String.get_utf_8_uchar`
       and `Buffer`/`Uchar` all need native OCaml `int`, so re-open
       `Stdlib` locally to get the native operators back -- same
       pattern already used in 63_regex_hash_uuid_stubs.sh's glue in
       this same file. *)
    let open Stdlib in
    let rec loop buf s i max =
      if i > max then Buffer.contents buf
      else begin
        let dec = String.get_utf_8_uchar s i in
        let u = Uchar.utf_decode_uchar dec in
        (match cmap u with
         | `Self -> Buffer.add_utf_8_uchar buf u
         | `Uchars us -> List.iter (Buffer.add_utf_8_uchar buf) us);
        loop buf s (i + Uchar.utf_decode_length dec) max
      end
    in
    let buf = Buffer.create (String.length s * 2) in
    if String.length s = 0 then "" else loop buf s 0 (String.length s - 1)

  let uppercase_utf_8 (s : string) : string = cmap_utf_8 Uucp.Case.Map.to_upper s
  let lowercase_utf_8 (s : string) : string = cmap_utf_8 Uucp.Case.Map.to_lower s
end

let string_uppercase_unicode (s : Prims.string) : Prims.string=
  Uucp_case_runtime.uppercase_utf_8 s
let string_lowercase_unicode (s : Prims.string) : Prims.string=
  Uucp_case_runtime.lowercase_utf_8 s
let string_upper (s : Prims.string) : Prims.string=
  string_uppercase_unicode s
let string_lower (s : Prims.string) : Prims.string=
  string_lowercase_unicode s
let is_numeric_datatype (dt : RDF_Term.wf_iri) : Prims.bool=
  (((dt = RDF_Term.xsd_integer) || (dt = RDF_Term.xsd_decimal)) ||
     (dt = RDF_Term.xsd_double))
    || (dt = xsd_float)
let mk_plain_literal (s : Prims.string) : RDF_Term.wf_literal=
  {
    RDF_Term.lexical_form = s;
    RDF_Term.datatype = RDF_Term.xsd_string;
    RDF_Term.lang_tag = FStar_Pervasives_Native.None;
    RDF_Term.direction = FStar_Pervasives_Native.None
  }
type eval_result =
  | ER_Term of RDF_Term.rdf_term 
  | ER_Bool of Prims.bool 
  | ER_Num of Prims.int 
  | ER_Dec of Prims.string 
  | ER_Dbl of Prims.string 
  | ER_Error 
let uu___is_ER_Term (projectee : eval_result) : Prims.bool=
  match projectee with | ER_Term _0 -> true | uu___ -> false
let __proj__ER_Term__item___0 (projectee : eval_result) : RDF_Term.rdf_term=
  match projectee with | ER_Term _0 -> _0
let uu___is_ER_Bool (projectee : eval_result) : Prims.bool=
  match projectee with | ER_Bool _0 -> true | uu___ -> false
let __proj__ER_Bool__item___0 (projectee : eval_result) : Prims.bool=
  match projectee with | ER_Bool _0 -> _0
let uu___is_ER_Num (projectee : eval_result) : Prims.bool=
  match projectee with | ER_Num _0 -> true | uu___ -> false
let __proj__ER_Num__item___0 (projectee : eval_result) : Prims.int=
  match projectee with | ER_Num _0 -> _0
let uu___is_ER_Dec (projectee : eval_result) : Prims.bool=
  match projectee with | ER_Dec _0 -> true | uu___ -> false
let __proj__ER_Dec__item___0 (projectee : eval_result) : Prims.string=
  match projectee with | ER_Dec _0 -> _0
let uu___is_ER_Dbl (projectee : eval_result) : Prims.bool=
  match projectee with | ER_Dbl _0 -> true | uu___ -> false
let __proj__ER_Dbl__item___0 (projectee : eval_result) : Prims.string=
  match projectee with | ER_Dbl _0 -> _0
let uu___is_ER_Error (projectee : eval_result) : Prims.bool=
  match projectee with | ER_Error -> true | uu___ -> false
let ebv_checked (v : eval_result) :
  Prims.bool FStar_Pervasives_Native.option=
  match v with
  | ER_Bool b -> FStar_Pervasives_Native.Some b
  | ER_Num n -> FStar_Pervasives_Native.Some (n <> Prims.int_zero)
  | ER_Dec s ->
      FStar_Pervasives_Native.Some
        (((s <> "0") && (s <> "0.0")) && (s <> ""))
  | ER_Dbl s ->
      FStar_Pervasives_Native.Some
        ((((s <> "0") && (s <> "0.0")) && (s <> "NaN")) && (s <> ""))
  | ER_Term (RDF_Term.T_Literal l) ->
      if (lit_datatype l) = RDF_Term.xsd_boolean
      then
        FStar_Pervasives_Native.Some
          (((lit_lexical l) = "true") || ((lit_lexical l) = "1"))
      else
        if (lit_datatype l) = RDF_Term.xsd_string
        then
          FStar_Pervasives_Native.Some
            ((FStar_String.strlen (lit_lexical l)) > Prims.int_zero)
        else
          if is_numeric_datatype (lit_datatype l)
          then
            FStar_Pervasives_Native.Some
              ((((lit_lexical l) <> "0") && ((lit_lexical l) <> "0.0")) &&
                 ((lit_lexical l) <> ""))
          else FStar_Pervasives_Native.None
  | ER_Term uu___ -> FStar_Pervasives_Native.None
  | ER_Error -> FStar_Pervasives_Native.None
let ebv (v : eval_result) : Prims.bool=
  match ebv_checked v with
  | FStar_Pervasives_Native.Some b -> b
  | FStar_Pervasives_Native.None -> false
let bool_and_checked (a : Prims.bool FStar_Pervasives_Native.option)
  (b : Prims.bool FStar_Pervasives_Native.option) :
  Prims.bool FStar_Pervasives_Native.option=
  match (a, b) with
  | (FStar_Pervasives_Native.Some false, uu___) ->
      FStar_Pervasives_Native.Some false
  | (uu___, FStar_Pervasives_Native.Some false) ->
      FStar_Pervasives_Native.Some false
  | (FStar_Pervasives_Native.Some true, FStar_Pervasives_Native.Some true) ->
      FStar_Pervasives_Native.Some true
  | (uu___, uu___1) -> FStar_Pervasives_Native.None
let bool_or_checked (a : Prims.bool FStar_Pervasives_Native.option)
  (b : Prims.bool FStar_Pervasives_Native.option) :
  Prims.bool FStar_Pervasives_Native.option=
  match (a, b) with
  | (FStar_Pervasives_Native.Some true, uu___) ->
      FStar_Pervasives_Native.Some true
  | (uu___, FStar_Pervasives_Native.Some true) ->
      FStar_Pervasives_Native.Some true
  | (FStar_Pervasives_Native.Some false, FStar_Pervasives_Native.Some false)
      -> FStar_Pervasives_Native.Some false
  | (uu___, uu___1) -> FStar_Pervasives_Native.None
let bool_not_checked (a : Prims.bool FStar_Pervasives_Native.option) :
  Prims.bool FStar_Pervasives_Native.option=
  match a with
  | FStar_Pervasives_Native.Some b ->
      FStar_Pervasives_Native.Some (Prims.op_Negation b)
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
let er_to_term (v : eval_result) :
  RDF_Term.rdf_term FStar_Pervasives_Native.option=
  match v with
  | ER_Term t -> FStar_Pervasives_Native.Some t
  | ER_Bool true ->
      FStar_Pervasives_Native.Some
        (RDF_Term.T_Literal
           {
             RDF_Term.lexical_form = "true";
             RDF_Term.datatype = RDF_Term.xsd_boolean;
             RDF_Term.lang_tag = FStar_Pervasives_Native.None;
             RDF_Term.direction = FStar_Pervasives_Native.None
           })
  | ER_Bool false ->
      FStar_Pervasives_Native.Some
        (RDF_Term.T_Literal
           {
             RDF_Term.lexical_form = "false";
             RDF_Term.datatype = RDF_Term.xsd_boolean;
             RDF_Term.lang_tag = FStar_Pervasives_Native.None;
             RDF_Term.direction = FStar_Pervasives_Native.None
           })
  | ER_Num n ->
      FStar_Pervasives_Native.Some
        (RDF_Term.T_Literal
           {
             RDF_Term.lexical_form = (Prims.string_of_int n);
             RDF_Term.datatype = RDF_Term.xsd_integer;
             RDF_Term.lang_tag = FStar_Pervasives_Native.None;
             RDF_Term.direction = FStar_Pervasives_Native.None
           })
  | ER_Dec s ->
      FStar_Pervasives_Native.Some
        (RDF_Term.T_Literal
           {
             RDF_Term.lexical_form = s;
             RDF_Term.datatype = RDF_Term.xsd_decimal;
             RDF_Term.lang_tag = FStar_Pervasives_Native.None;
             RDF_Term.direction = FStar_Pervasives_Native.None
           })
  | ER_Dbl s ->
      FStar_Pervasives_Native.Some
        (RDF_Term.T_Literal
           {
             RDF_Term.lexical_form = s;
             RDF_Term.datatype = RDF_Term.xsd_double;
             RDF_Term.lang_tag = FStar_Pervasives_Native.None;
             RDF_Term.direction = FStar_Pervasives_Native.None
           })
  | ER_Error -> FStar_Pervasives_Native.None
let er_to_string (v : eval_result) :
  Prims.string FStar_Pervasives_Native.option=
  match v with
  | ER_Term (RDF_Term.T_Literal l) ->
      FStar_Pervasives_Native.Some (lit_lexical l)
  | ER_Term (RDF_Term.T_IRI i) ->
      FStar_Pervasives_Native.Some (iri_to_string i)
  | ER_Num n -> FStar_Pervasives_Native.Some (Prims.string_of_int n)
  | ER_Dec s -> FStar_Pervasives_Native.Some s
  | ER_Dbl s -> FStar_Pervasives_Native.Some s
  | ER_Bool b -> FStar_Pervasives_Native.Some (if b then "true" else "false")
  | uu___ -> FStar_Pervasives_Native.None
let er_string (s : Prims.string) : eval_result=
  ER_Term (RDF_Term.T_Literal (mk_plain_literal s))
let er_string_info (v : eval_result) :
  (Prims.string * Prims.string FStar_Pervasives_Native.option * Prims.string)
    FStar_Pervasives_Native.option=
  match v with
  | ER_Term (RDF_Term.T_Literal l) ->
      FStar_Pervasives_Native.Some
        ((lit_lexical l), (l.RDF_Term.lang_tag), (l.RDF_Term.datatype))
  | ER_Num n ->
      FStar_Pervasives_Native.Some
        ((Prims.string_of_int n), FStar_Pervasives_Native.None,
          RDF_Term.xsd_integer)
  | ER_Dec s ->
      FStar_Pervasives_Native.Some
        (s, FStar_Pervasives_Native.None, RDF_Term.xsd_decimal)
  | ER_Dbl s ->
      FStar_Pervasives_Native.Some
        (s, FStar_Pervasives_Native.None, RDF_Term.xsd_double)
  | ER_Bool b ->
      FStar_Pervasives_Native.Some
        ((if b then "true" else "false"), FStar_Pervasives_Native.None,
          RDF_Term.xsd_boolean)
  | uu___ -> FStar_Pervasives_Native.None
let er_direction (v : eval_result) :
  RDF_Term.text_direction FStar_Pervasives_Native.option=
  match v with
  | ER_Term (RDF_Term.T_Literal l) -> l.RDF_Term.direction
  | uu___ -> FStar_Pervasives_Native.None
let er_string_preserve (s : Prims.string)
  (lang : Prims.string FStar_Pervasives_Native.option) (dt : Prims.string) :
  eval_result=
  if RDF_Term.is_iri dt
  then
    match lang with
    | FStar_Pervasives_Native.None ->
        (if
           (dt <> RDF_Term.rdf_lang_string) &&
             (dt <> RDF_Term.rdf_dir_lang_string)
         then
           ER_Term
             (RDF_Term.T_Literal
                {
                  RDF_Term.lexical_form = s;
                  RDF_Term.datatype = dt;
                  RDF_Term.lang_tag = FStar_Pervasives_Native.None;
                  RDF_Term.direction = FStar_Pervasives_Native.None
                })
         else er_string s)
    | FStar_Pervasives_Native.Some l ->
        (if dt = RDF_Term.rdf_lang_string
         then
           ER_Term
             (RDF_Term.T_Literal
                {
                  RDF_Term.lexical_form = s;
                  RDF_Term.datatype = dt;
                  RDF_Term.lang_tag = (FStar_Pervasives_Native.Some l);
                  RDF_Term.direction = FStar_Pervasives_Native.None
                })
         else er_string s)
  else er_string s
let int_div_decimal (a : Prims.int) (b : Prims.int) : Prims.string=
  if b = Prims.int_zero
  then "0.0"
  else
    (let scale_factor = (Prims.parse_int "10000000000000000") in
     let scaled = a * scale_factor in
     let result = if b = Prims.int_zero then Prims.int_zero else scaled / b in
     let abs_r =
       if result < Prims.int_zero then Prims.int_zero - result else result in
     let sign = if result < Prims.int_zero then "-" else "" in
     let int_part =
       if scale_factor = Prims.int_zero
       then Prims.int_zero
       else abs_r / scale_factor in
     let frac_part = abs_r - (int_part * scale_factor) in
     if frac_part = Prims.int_zero
     then
       Prims.strcat sign (Prims.strcat (Prims.string_of_int int_part) ".0")
     else
       (let frac_str = Prims.string_of_int frac_part in
        let frac_len = FStar_String.strlen frac_str in
        let rec make_zeros_simple n =
          if n = Prims.int_zero
          then ""
          else Prims.strcat "0" (make_zeros_simple (n - Prims.int_one)) in
        let padded =
          if frac_len < (Prims.of_int (16))
          then
            Prims.strcat (make_zeros_simple ((Prims.of_int (16)) - frac_len))
              frac_str
          else frac_str in
        let chars = FStar_String.list_of_string padded in
        let rec strip_tz cs =
          match cs with
          | [] -> [FStar_Char.char_of_int (Prims.of_int (48))]
          | uu___2 ->
              let rev_cs = FStar_List_Tot_Base.rev cs in
              let rec drop_zeros rs =
                match rs with
                | c::rest ->
                    if (FStar_Char.int_of_char c) = (Prims.of_int (48))
                    then drop_zeros rest
                    else rs
                | [] -> [FStar_Char.char_of_int (Prims.of_int (48))] in
              FStar_List_Tot_Base.rev (drop_zeros rev_cs) in
        let trimmed = FStar_String.string_of_list (strip_tz chars) in
        Prims.strcat sign
          (Prims.strcat (Prims.string_of_int int_part)
             (Prims.strcat "." trimmed))))
let eval_arith_int (op : arith_op) (a : Prims.int) (b : Prims.int) :
  eval_result=
  match op with
  | Add -> ER_Num (a + b)
  | Sub -> ER_Num (a - b)
  | Mul -> ER_Num (a * b)
  | Div ->
      if b = Prims.int_zero then ER_Error else ER_Dec (int_div_decimal a b)
let er_to_datetime_lex (v : eval_result) :
  Prims.string FStar_Pervasives_Native.option=
  match v with
  | ER_Term (RDF_Term.T_Literal l) ->
      if (lit_datatype l) = xsd_dateTime
      then FStar_Pervasives_Native.Some (lit_lexical l)
      else FStar_Pervasives_Native.None
  | uu___ -> FStar_Pervasives_Native.None
let rec zip_bindings (vars : var_name Prims.list)
  (terms : RDF_Term.rdf_term FStar_Pervasives_Native.option Prims.list)
  (acc : RDF_Graph_Executable.solution_mapping) :
  RDF_Graph_Executable.solution_mapping=
  match (vars, terms) with
  | (v::vs, (FStar_Pervasives_Native.Some t)::ts) ->
      zip_bindings vs ts (sm_bind v t acc)
  | (uu___::vs, uu___1::ts) -> zip_bindings vs ts acc
  | (uu___, uu___1) -> acc
let eval_values (vars : var_name Prims.list)
  (rows :
    RDF_Term.rdf_term FStar_Pervasives_Native.option Prims.list Prims.list)
  : RDF_Graph_Executable.solution_mapping Prims.list=
  FStar_List_Tot_Base.map (fun row -> zip_bindings vars row sm_empty) rows
let apply_comp_op (cmp : Prims.int) (op : comp_op) : Prims.bool=
  match op with
  | CmpEq -> cmp = Prims.int_zero
  | CmpNe -> cmp <> Prims.int_zero
  | CmpLt -> cmp < Prims.int_zero
  | CmpGt -> cmp > Prims.int_zero
  | CmpLe -> cmp <= Prims.int_zero
  | CmpGe -> cmp >= Prims.int_zero
let int_compare (a : Prims.int) (b : Prims.int) : Prims.int=
  if a < b
  then (Prims.of_int (-1))
  else if a = b then Prims.int_zero else Prims.int_one
let fn_isIRI (v : eval_result) : eval_result=
  match v with
  | ER_Term (RDF_Term.T_IRI uu___) -> ER_Bool true
  | ER_Error -> ER_Error
  | uu___ -> ER_Bool false
let fn_isBlank (v : eval_result) : eval_result=
  match v with
  | ER_Term (RDF_Term.T_BNode uu___) -> ER_Bool true
  | ER_Error -> ER_Error
  | uu___ -> ER_Bool false
let fn_isLiteral (v : eval_result) : eval_result=
  match v with
  | ER_Term (RDF_Term.T_Literal uu___) -> ER_Bool true
  | ER_Num uu___ -> ER_Bool true
  | ER_Dec uu___ -> ER_Bool true
  | ER_Dbl uu___ -> ER_Bool true
  | ER_Bool uu___ -> ER_Bool true
  | ER_Error -> ER_Error
  | uu___ -> ER_Bool false
let fn_isNumeric (v : eval_result) : eval_result=
  match v with
  | ER_Num uu___ -> ER_Bool true
  | ER_Dec uu___ -> ER_Bool true
  | ER_Dbl uu___ -> ER_Bool true
  | ER_Term (RDF_Term.T_Literal l) ->
      ER_Bool (is_numeric_datatype (lit_datatype l))
  | ER_Error -> ER_Error
  | uu___ -> ER_Bool false
let fn_str (v : eval_result) : eval_result=
  match v with
  | ER_Term (RDF_Term.T_IRI i) ->
      ER_Term (RDF_Term.T_Literal (mk_plain_literal (iri_to_string i)))
  | ER_Term (RDF_Term.T_Literal l) ->
      ER_Term (RDF_Term.T_Literal (mk_plain_literal (lit_lexical l)))
  | ER_Term (RDF_Term.T_BNode b) ->
      ER_Term (RDF_Term.T_Literal (mk_plain_literal b))
  | ER_Num n ->
      ER_Term (RDF_Term.T_Literal (mk_plain_literal (Prims.string_of_int n)))
  | ER_Dec s -> ER_Term (RDF_Term.T_Literal (mk_plain_literal s))
  | ER_Dbl s -> ER_Term (RDF_Term.T_Literal (mk_plain_literal s))
  | ER_Bool b ->
      ER_Term
        (RDF_Term.T_Literal
           {
             RDF_Term.lexical_form = (if b then "true" else "false");
             RDF_Term.datatype = RDF_Term.xsd_boolean;
             RDF_Term.lang_tag = FStar_Pervasives_Native.None;
             RDF_Term.direction = FStar_Pervasives_Native.None
           })
  | ER_Term (RDF_Term.T_TripleTerm (uu___, uu___1, uu___2)) -> ER_Error
  | ER_Error -> ER_Error
let fn_lang (v : eval_result) : eval_result=
  match v with
  | ER_Term (RDF_Term.T_Literal l) ->
      (match lit_lang l with
       | FStar_Pervasives_Native.Some tag ->
           ER_Term (RDF_Term.T_Literal (mk_plain_literal tag))
       | FStar_Pervasives_Native.None ->
           ER_Term (RDF_Term.T_Literal (mk_plain_literal "")))
  | ER_Num uu___ -> ER_Term (RDF_Term.T_Literal (mk_plain_literal ""))
  | ER_Dec uu___ -> ER_Term (RDF_Term.T_Literal (mk_plain_literal ""))
  | ER_Dbl uu___ -> ER_Term (RDF_Term.T_Literal (mk_plain_literal ""))
  | ER_Bool uu___ -> ER_Term (RDF_Term.T_Literal (mk_plain_literal ""))
  | uu___ -> ER_Error
let fn_datatype (v : eval_result) : eval_result=
  match v with
  | ER_Term (RDF_Term.T_Literal l) ->
      ER_Term (RDF_Term.T_IRI (lit_datatype l))
  | ER_Num uu___ -> ER_Term (RDF_Term.T_IRI RDF_Term.xsd_integer)
  | ER_Dec uu___ -> ER_Term (RDF_Term.T_IRI RDF_Term.xsd_decimal)
  | ER_Dbl uu___ -> ER_Term (RDF_Term.T_IRI RDF_Term.xsd_double)
  | ER_Bool uu___ -> ER_Term (RDF_Term.T_IRI RDF_Term.xsd_boolean)
  | uu___ -> ER_Error
let fn_haslang (v : eval_result) : eval_result=
  match v with
  | ER_Error -> ER_Error
  | ER_Term (RDF_Term.T_Literal l) ->
      ER_Bool (FStar_Pervasives_Native.uu___is_Some (lit_lang l))
  | uu___ -> ER_Bool false
let fn_haslangdir (v : eval_result) : eval_result=
  match v with
  | ER_Error -> ER_Error
  | ER_Term (RDF_Term.T_Literal l) ->
      ER_Bool (FStar_Pervasives_Native.uu___is_Some (lit_direction l))
  | uu___ -> ER_Bool false
let text_direction_to_string (d : RDF_Term.text_direction) : Prims.string=
  match d with | RDF_Term.Dir_LTR -> "ltr" | RDF_Term.Dir_RTL -> "rtl"
let parse_text_direction (s : Prims.string) :
  RDF_Term.text_direction FStar_Pervasives_Native.option=
  if s = "ltr"
  then FStar_Pervasives_Native.Some RDF_Term.Dir_LTR
  else
    if s = "rtl"
    then FStar_Pervasives_Native.Some RDF_Term.Dir_RTL
    else FStar_Pervasives_Native.None
let fn_langdir (v : eval_result) : eval_result=
  match v with
  | ER_Term (RDF_Term.T_Literal l) ->
      (match lit_direction l with
       | FStar_Pervasives_Native.Some d ->
           ER_Term
             (RDF_Term.T_Literal
                (mk_plain_literal (text_direction_to_string d)))
       | FStar_Pervasives_Native.None ->
           ER_Term (RDF_Term.T_Literal (mk_plain_literal "")))
  | ER_Num uu___ -> ER_Term (RDF_Term.T_Literal (mk_plain_literal ""))
  | ER_Dec uu___ -> ER_Term (RDF_Term.T_Literal (mk_plain_literal ""))
  | ER_Dbl uu___ -> ER_Term (RDF_Term.T_Literal (mk_plain_literal ""))
  | ER_Bool uu___ -> ER_Term (RDF_Term.T_Literal (mk_plain_literal ""))
  | uu___ -> ER_Error
let rec find_substring_pos_aux :
  'a .
    'a Prims.list ->
      'a Prims.list -> Prims.nat -> Prims.nat FStar_Pervasives_Native.option
  =
  fun needle haystack pos ->
    match haystack with
    | [] ->
        if Prims.uu___is_Nil needle
        then FStar_Pervasives_Native.Some pos
        else FStar_Pervasives_Native.None
    | uu___::rest ->
        if list_is_prefix needle haystack
        then FStar_Pervasives_Native.Some pos
        else find_substring_pos_aux needle rest (pos + Prims.int_one)
let find_substring_pos (needle : FStar_String.char Prims.list)
  (haystack : FStar_String.char Prims.list) :
  Prims.nat FStar_Pervasives_Native.option=
  find_substring_pos_aux needle haystack Prims.int_zero
let string_before (s : Prims.string) (arg : Prims.string) : Prims.string=
  if (FStar_String.strlen arg) = Prims.int_zero
  then ""
  else
    (let s_chars = FStar_String.list_of_string s in
     let arg_chars = FStar_String.list_of_string arg in
     match find_substring_pos arg_chars s_chars with
     | FStar_Pervasives_Native.None -> ""
     | FStar_Pervasives_Native.Some pos ->
         if pos = Prims.int_zero
         then ""
         else
           FStar_String.string_of_list
             (FStar_Pervasives_Native.fst
                (FStar_List_Tot_Base.splitAt pos s_chars)))
let string_after (s : Prims.string) (arg : Prims.string) : Prims.string=
  if (FStar_String.strlen arg) = Prims.int_zero
  then s
  else
    (let s_chars = FStar_String.list_of_string s in
     let arg_chars = FStar_String.list_of_string arg in
     let arg_len = FStar_List_Tot_Base.length arg_chars in
     match find_substring_pos arg_chars s_chars with
     | FStar_Pervasives_Native.None -> ""
     | FStar_Pervasives_Native.Some pos ->
         FStar_String.string_of_list
           (FStar_Pervasives_Native.snd
              (FStar_List_Tot_Base.splitAt (pos + arg_len) s_chars)))
let string_concat (args : Prims.string Prims.list) : Prims.string=
  FStar_String.concat "" args
let nibble_to_hex (n : Prims.nat) : FStar_Char.char=
  if n < (Prims.of_int (10))
  then FStar_Char.char_of_int (n + (Prims.of_int (48)))
  else
    FStar_Char.char_of_int ((n - (Prims.of_int (10))) + (Prims.of_int (65)))
let is_uri_unreserved (c : FStar_Char.char) : Prims.bool=
  let code = FStar_Char.int_of_char c in
  (((((((code >= (Prims.of_int (65))) && (code <= (Prims.of_int (90)))) ||
         ((code >= (Prims.of_int (97))) && (code <= (Prims.of_int (122)))))
        || ((code >= (Prims.of_int (48))) && (code <= (Prims.of_int (57)))))
       || (code = (Prims.of_int (45))))
      || (code = (Prims.of_int (95))))
     || (code = (Prims.of_int (46))))
    || (code = (Prims.of_int (126)))
let percent_encode_byte (b : Prims.nat) : FStar_Char.char Prims.list=
  let hi = b / (Prims.of_int (16)) in
  let lo = (mod) b (Prims.of_int (16)) in
  [FStar_Char.char_of_int (Prims.of_int (37));
  nibble_to_hex hi;
  nibble_to_hex lo]
let percent_encode_char (c : FStar_Char.char) : FStar_Char.char Prims.list=
  let code = FStar_Char.int_of_char c in
  if code < (Prims.of_int (0x80))
  then percent_encode_byte code
  else
    if code < (Prims.of_int (0x800))
    then
      (let b1 = (Prims.of_int (0xC0)) + (code / (Prims.of_int (64))) in
       let b2 = (Prims.of_int (0x80)) + ((mod) code (Prims.of_int (64))) in
       RDF_List_Helpers.append_tr (percent_encode_byte b1)
         (percent_encode_byte b2))
    else
      if code < (Prims.parse_int "0x10000")
      then
        (let b1 = (Prims.of_int (0xE0)) + (code / (Prims.of_int (4096))) in
         let b2 =
           (Prims.of_int (0x80)) +
             ((mod) (code / (Prims.of_int (64))) (Prims.of_int (64))) in
         let b3 = (Prims.of_int (0x80)) + ((mod) code (Prims.of_int (64))) in
         RDF_List_Helpers.append_tr (percent_encode_byte b1)
           (RDF_List_Helpers.append_tr (percent_encode_byte b2)
              (percent_encode_byte b3)))
      else
        (let b1 = (Prims.of_int (0xF0)) + (code / (Prims.parse_int "262144")) in
         let b2 =
           (Prims.of_int (0x80)) +
             ((mod) (code / (Prims.of_int (4096))) (Prims.of_int (64))) in
         let b3 =
           (Prims.of_int (0x80)) +
             ((mod) (code / (Prims.of_int (64))) (Prims.of_int (64))) in
         let b4 = (Prims.of_int (0x80)) + ((mod) code (Prims.of_int (64))) in
         RDF_List_Helpers.append_tr (percent_encode_byte b1)
           (RDF_List_Helpers.append_tr (percent_encode_byte b2)
              (RDF_List_Helpers.append_tr (percent_encode_byte b3)
                 (percent_encode_byte b4))))
let rec encode_uri_chars (cs : FStar_Char.char Prims.list) :
  FStar_Char.char Prims.list=
  match cs with
  | [] -> []
  | c::rest ->
      if is_uri_unreserved c
      then c :: (encode_uri_chars rest)
      else
        RDF_List_Helpers.append_tr (percent_encode_char c)
          (encode_uri_chars rest)
let string_encode_uri (s : Prims.string) : Prims.string=
  FStar_String.string_of_list
    (encode_uri_chars (FStar_String.list_of_string s))
let rec replace_first (haystack : FStar_Char.char Prims.list)
  (pattern : FStar_Char.char Prims.list)
  (replacement : FStar_Char.char Prims.list) : FStar_Char.char Prims.list=
  match haystack with
  | [] -> []
  | hd::tl ->
      if list_is_prefix pattern haystack
      then
        RDF_List_Helpers.append_tr replacement
          (list_drop (FStar_List_Tot_Base.length pattern) haystack)
      else hd :: (replace_first tl pattern replacement)
let rec replace_all_chars_fuel (haystack : FStar_Char.char Prims.list)
  (pattern : FStar_Char.char Prims.list)
  (replacement : FStar_Char.char Prims.list) (fuel : Prims.nat) :
  FStar_Char.char Prims.list=
  if fuel = Prims.int_zero
  then haystack
  else
    if list_contains_sublist pattern haystack
    then
      replace_all_chars_fuel (replace_first haystack pattern replacement)
        pattern replacement (fuel - Prims.int_one)
    else haystack
let replace_all_chars (haystack : FStar_Char.char Prims.list)
  (pattern : FStar_Char.char Prims.list)
  (replacement : FStar_Char.char Prims.list) : FStar_Char.char Prims.list=
  if Prims.uu___is_Nil pattern
  then haystack
  else
    replace_all_chars_fuel haystack pattern replacement
      (FStar_List_Tot_Base.length haystack)
let string_replace_literal (s : Prims.string) (pattern : Prims.string)
  (replacement : Prims.string)
  (_flags : Prims.string FStar_Pervasives_Native.option) : Prims.string=
  if (FStar_String.strlen pattern) = Prims.int_zero
  then s
  else
    FStar_String.string_of_list
      (replace_all_chars (FStar_String.list_of_string s)
         (FStar_String.list_of_string pattern)
         (FStar_String.list_of_string replacement))
let rx_cp_caret : Prims.nat= (Prims.of_int (0x5E))
let rx_cp_dollar : Prims.nat= (Prims.of_int (0x24))
let rx_cp_backslash : Prims.nat= (Prims.of_int (0x5C))
let rx_cp_lbracket : Prims.nat= (Prims.of_int (0x5B))
let rx_cp_rbracket : Prims.nat= (Prims.of_int (0x5D))
let rx_flag_has (flags : Prims.string FStar_Pervasives_Native.option)
  (ch : FStar_Char.char) : Prims.bool=
  match flags with
  | FStar_Pervasives_Native.None -> false
  | FStar_Pervasives_Native.Some f ->
      FStar_List_Tot_Base.mem ch (FStar_String.list_of_string f)
let rx_is_ws (c : Prims.nat) : Prims.bool=
  (((c = (Prims.of_int (0x09))) || (c = (Prims.of_int (0x0A)))) ||
     (c = (Prims.of_int (0x0D))))
    || (c = (Prims.of_int (0x20)))
let rec rx_strip_ws (cps : Prims.nat Prims.list) (in_class : Prims.bool) :
  Prims.nat Prims.list=
  match cps with
  | [] -> []
  | c::t ->
      if c = rx_cp_backslash
      then
        (match t with
         | c2::t2 -> c :: c2 :: (rx_strip_ws t2 in_class)
         | [] -> [c])
      else
        if (c = rx_cp_lbracket) && (Prims.op_Negation in_class)
        then c :: (rx_strip_ws t true)
        else
          if (c = rx_cp_rbracket) && in_class
          then c :: (rx_strip_ws t false)
          else
            if (rx_is_ws c) && (Prims.op_Negation in_class)
            then rx_strip_ws t in_class
            else c :: (rx_strip_ws t in_class)
let rx_begin_sentinel : Prims.nat= Regex_Syntax.max_codepoint + Prims.int_one
let rx_end_sentinel : Prims.nat=
  Regex_Syntax.max_codepoint + (Prims.of_int (2))
let rec rx_replace_anchors (cps : Prims.nat Prims.list)
  (in_class : Prims.bool) : Prims.nat Prims.list=
  match cps with
  | [] -> []
  | c::t ->
      if c = rx_cp_backslash
      then
        (match t with
         | c2::t2 -> c :: c2 :: (rx_replace_anchors t2 in_class)
         | [] -> [c])
      else
        if (c = rx_cp_lbracket) && (Prims.op_Negation in_class)
        then c :: (rx_replace_anchors t true)
        else
          if (c = rx_cp_rbracket) && in_class
          then c :: (rx_replace_anchors t false)
          else
            if (c = rx_cp_caret) && (Prims.op_Negation in_class)
            then rx_begin_sentinel :: (rx_replace_anchors t in_class)
            else
              if (c = rx_cp_dollar) && (Prims.op_Negation in_class)
              then rx_end_sentinel :: (rx_replace_anchors t in_class)
              else c :: (rx_replace_anchors t in_class)
let rx_nonsent : Regex_Syntax.regex=
  Regex_Syntax.R_Ranges [(Prims.int_zero, Regex_Syntax.max_codepoint)]
let rx_gap_left : Regex_Syntax.regex=
  Regex_Syntax.R_Alt
    (Regex_Syntax.R_Eps,
      (Regex_Syntax.R_Cat
         ((Regex_Syntax.R_Ranges [(rx_begin_sentinel, rx_begin_sentinel)]),
           (Regex_Syntax.R_Star rx_nonsent))))
let rx_gap_right : Regex_Syntax.regex=
  Regex_Syntax.R_Alt
    (Regex_Syntax.R_Eps,
      (Regex_Syntax.R_Cat
         ((Regex_Syntax.R_Star rx_nonsent),
           (Regex_Syntax.R_Ranges [(rx_end_sentinel, rx_end_sentinel)]))))
let rec rx_literal_regex (cps : Prims.nat Prims.list) : Regex_Syntax.regex=
  match cps with
  | [] -> Regex_Syntax.R_Eps
  | c::[] -> Regex_Syntax.R_Ranges [(c, c)]
  | c::t ->
      Regex_Syntax.R_Cat
        ((Regex_Syntax.R_Ranges [(c, c)]), (rx_literal_regex t))
let rx_ci_extra (lo : Prims.nat) (hi : Prims.nat) :
  (Prims.nat * Prims.nat) Prims.list=
  let up_lo =
    if lo > (Prims.of_int (0x41)) then lo else (Prims.of_int (0x41)) in
  let up_hi =
    if hi < (Prims.of_int (0x5A)) then hi else (Prims.of_int (0x5A)) in
  let img_lower =
    if up_lo <= up_hi
    then [((up_lo + (Prims.of_int (0x20))), (up_hi + (Prims.of_int (0x20))))]
    else [] in
  let lo_lo =
    if lo > (Prims.of_int (0x61)) then lo else (Prims.of_int (0x61)) in
  let lo_hi =
    if hi < (Prims.of_int (0x7A)) then hi else (Prims.of_int (0x7A)) in
  let img_upper =
    if lo_lo <= lo_hi
    then [((lo_lo - (Prims.of_int (0x20))), (lo_hi - (Prims.of_int (0x20))))]
    else [] in
  FStar_List_Tot_Base.op_At img_lower img_upper
let rec rx_ci_ranges (rs : (Prims.nat * Prims.nat) Prims.list) :
  (Prims.nat * Prims.nat) Prims.list=
  match rs with
  | [] -> []
  | (lo, hi)::t -> (lo, hi) ::
      (FStar_List_Tot_Base.op_At (rx_ci_extra lo hi) (rx_ci_ranges t))
let rec rx_fold_ci (r : Regex_Syntax.regex) : Regex_Syntax.regex=
  match r with
  | Regex_Syntax.R_Empty -> Regex_Syntax.R_Empty
  | Regex_Syntax.R_Eps -> Regex_Syntax.R_Eps
  | Regex_Syntax.R_Ranges rs -> Regex_Syntax.R_Ranges (rx_ci_ranges rs)
  | Regex_Syntax.R_Cat (a, b) ->
      Regex_Syntax.R_Cat ((rx_fold_ci a), (rx_fold_ci b))
  | Regex_Syntax.R_Alt (a, b) ->
      Regex_Syntax.R_Alt ((rx_fold_ci a), (rx_fold_ci b))
  | Regex_Syntax.R_And (a, b) ->
      Regex_Syntax.R_And ((rx_fold_ci a), (rx_fold_ci b))
  | Regex_Syntax.R_Not a -> Regex_Syntax.R_Not (rx_fold_ci a)
  | Regex_Syntax.R_Star a -> Regex_Syntax.R_Star (rx_fold_ci a)
let rec rx_dotall (r : Regex_Syntax.regex) : Regex_Syntax.regex=
  match r with
  | Regex_Syntax.R_Empty -> Regex_Syntax.R_Empty
  | Regex_Syntax.R_Eps -> Regex_Syntax.R_Eps
  | Regex_Syntax.R_Ranges uu___ ->
      if r = Regex_XSDPattern.dot_regex then Regex_Exec.any_char else r
  | Regex_Syntax.R_Cat (a, b) ->
      Regex_Syntax.R_Cat ((rx_dotall a), (rx_dotall b))
  | Regex_Syntax.R_Alt (a, b) ->
      Regex_Syntax.R_Alt ((rx_dotall a), (rx_dotall b))
  | Regex_Syntax.R_And (a, b) ->
      Regex_Syntax.R_And ((rx_dotall a), (rx_dotall b))
  | Regex_Syntax.R_Not a -> Regex_Syntax.R_Not (rx_dotall a)
  | Regex_Syntax.R_Star a -> Regex_Syntax.R_Star (rx_dotall a)
let regex_match (text : Prims.string) (pattern : Prims.string)
  (flags : Prims.string FStar_Pervasives_Native.option) : Prims.bool=
  let has_i = rx_flag_has flags 105 in
  let has_s = rx_flag_has flags 115 in
  let has_x = rx_flag_has flags 120 in
  let has_q = rx_flag_has flags 113 in
  let input_cps = Regex_XSDPattern.cps_of_string text in
  let pat_cps0 = Regex_XSDPattern.cps_of_string pattern in
  if has_q
  then
    let core0 = rx_literal_regex pat_cps0 in
    let core = if has_i then rx_fold_ci core0 else core0 in
    Regex_Exec.matches_norm
      (Regex_Syntax.R_Cat
         (Regex_Exec.dot_star,
           (Regex_Syntax.R_Cat (core, Regex_Exec.dot_star)))) input_cps
  else
    (let pat_cps1 = if has_x then rx_strip_ws pat_cps0 false else pat_cps0 in
     let pat_cps = rx_replace_anchors pat_cps1 false in
     match Regex_XSDPattern.parse_cps pat_cps with
     | FStar_Pervasives_Native.None -> false
     | FStar_Pervasives_Native.Some r0 ->
         let r1 = if has_s then rx_dotall r0 else r0 in
         let r2 = if has_i then rx_fold_ci r1 else r1 in
         let m =
           Regex_Syntax.R_Cat
             (rx_gap_left, (Regex_Syntax.R_Cat (r2, rx_gap_right))) in
         let wrapped = rx_begin_sentinel ::
           (FStar_List_Tot_Base.append input_cps [rx_end_sentinel]) in
         Regex_Exec.matches_norm m wrapped)
let rx_safe_char (n : Prims.nat) : FStar_Char.char=
  if
    (n < (Prims.of_int (0xD7FF))) ||
      ((n >= (Prims.of_int (0xE000))) && (n <= (Prims.parse_int "0x10FFFF")))
  then FStar_Char.char_of_int n
  else FStar_Char.char_of_int (Prims.of_int (0xFFFD))
let rx_string_of_cps (cps : Prims.nat Prims.list) : Prims.string=
  FStar_String.string_of_list (FStar_List_Tot_Base.map rx_safe_char cps)
let rec rx_take (k : Prims.nat) (w : Prims.nat Prims.list) :
  Prims.nat Prims.list=
  match w with
  | [] -> []
  | c::t ->
      if k = Prims.int_zero then [] else c :: (rx_take (k - Prims.int_one) t)
let rec rx_drop (k : Prims.nat) (w : Prims.nat Prims.list) :
  Prims.nat Prims.list=
  match w with
  | [] -> []
  | uu___::t ->
      if k = Prims.int_zero then w else rx_drop (k - Prims.int_one) t
let rx_slice (w : Prims.nat Prims.list) (s : Prims.nat) (e : Prims.nat) :
  Prims.nat Prims.list= if e > s then rx_take (e - s) (rx_drop s w) else []
let rec rx_leaf_ends_from (r : Regex_Syntax.regex) (w : Prims.nat Prims.list)
  (k : Prims.nat) : Prims.nat Prims.list=
  let here = if Regex_Syntax.nullable r then [k] else [] in
  match w with
  | [] -> here
  | c::rest ->
      if r = Regex_Syntax.R_Empty
      then here
      else
        FStar_List_Tot_Base.append here
          (rx_leaf_ends_from (Regex_Exec.nderiv c r) rest (k + Prims.int_one))
let rx_leaf_ends (r : Regex_Syntax.regex) (w : Prims.nat Prims.list) :
  Prims.nat Prims.list= rx_leaf_ends_from r w Prims.int_zero
let rec rx_list_max_opt (xs : Prims.nat Prims.list) :
  Prims.nat FStar_Pervasives_Native.option=
  match xs with
  | [] -> FStar_Pervasives_Native.None
  | x::t ->
      (match rx_list_max_opt t with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.Some x
       | FStar_Pervasives_Native.Some m ->
           FStar_Pervasives_Native.Some (if x > m then x else m))
let rx_longest_end (pr : Regex_Syntax.regex) (suffix : Prims.nat Prims.list)
  : Prims.nat FStar_Pervasives_Native.option=
  rx_list_max_opt (rx_leaf_ends pr suffix)
type rx_cre =
  | RC_Leaf of Regex_Syntax.regex 
  | RC_Eps 
  | RC_Cat of rx_cre * rx_cre 
  | RC_Alt of rx_cre * rx_cre 
  | RC_Star of rx_cre 
  | RC_Group of Prims.nat * rx_cre 
let uu___is_RC_Leaf (projectee : rx_cre) : Prims.bool=
  match projectee with | RC_Leaf _0 -> true | uu___ -> false
let __proj__RC_Leaf__item___0 (projectee : rx_cre) : Regex_Syntax.regex=
  match projectee with | RC_Leaf _0 -> _0
let uu___is_RC_Eps (projectee : rx_cre) : Prims.bool=
  match projectee with | RC_Eps -> true | uu___ -> false
let uu___is_RC_Cat (projectee : rx_cre) : Prims.bool=
  match projectee with | RC_Cat (_0, _1) -> true | uu___ -> false
let __proj__RC_Cat__item___0 (projectee : rx_cre) : rx_cre=
  match projectee with | RC_Cat (_0, _1) -> _0
let __proj__RC_Cat__item___1 (projectee : rx_cre) : rx_cre=
  match projectee with | RC_Cat (_0, _1) -> _1
let uu___is_RC_Alt (projectee : rx_cre) : Prims.bool=
  match projectee with | RC_Alt (_0, _1) -> true | uu___ -> false
let __proj__RC_Alt__item___0 (projectee : rx_cre) : rx_cre=
  match projectee with | RC_Alt (_0, _1) -> _0
let __proj__RC_Alt__item___1 (projectee : rx_cre) : rx_cre=
  match projectee with | RC_Alt (_0, _1) -> _1
let uu___is_RC_Star (projectee : rx_cre) : Prims.bool=
  match projectee with | RC_Star _0 -> true | uu___ -> false
let __proj__RC_Star__item___0 (projectee : rx_cre) : rx_cre=
  match projectee with | RC_Star _0 -> _0
let uu___is_RC_Group (projectee : rx_cre) : Prims.bool=
  match projectee with | RC_Group (_0, _1) -> true | uu___ -> false
let __proj__RC_Group__item___0 (projectee : rx_cre) : Prims.nat=
  match projectee with | RC_Group (_0, _1) -> _0
let __proj__RC_Group__item___1 (projectee : rx_cre) : rx_cre=
  match projectee with | RC_Group (_0, _1) -> _1
let rec rx_cre_size (r : rx_cre) : Prims.nat=
  match r with
  | RC_Leaf uu___ -> Prims.int_one
  | RC_Eps -> Prims.int_one
  | RC_Cat (a, b) -> (Prims.int_one + (rx_cre_size a)) + (rx_cre_size b)
  | RC_Alt (a, b) -> (Prims.int_one + (rx_cre_size a)) + (rx_cre_size b)
  | RC_Star a -> Prims.int_one + (rx_cre_size a)
  | RC_Group (uu___, a) -> Prims.int_one + (rx_cre_size a)
let rec rx_cre_fold_ci (r : rx_cre) : rx_cre=
  match r with
  | RC_Leaf x -> RC_Leaf (rx_fold_ci x)
  | RC_Eps -> RC_Eps
  | RC_Cat (a, b) -> RC_Cat ((rx_cre_fold_ci a), (rx_cre_fold_ci b))
  | RC_Alt (a, b) -> RC_Alt ((rx_cre_fold_ci a), (rx_cre_fold_ci b))
  | RC_Star a -> RC_Star (rx_cre_fold_ci a)
  | RC_Group (n, a) -> RC_Group (n, (rx_cre_fold_ci a))
let rec rx_cre_dotall (r : rx_cre) : rx_cre=
  match r with
  | RC_Leaf x -> RC_Leaf (rx_dotall x)
  | RC_Eps -> RC_Eps
  | RC_Cat (a, b) -> RC_Cat ((rx_cre_dotall a), (rx_cre_dotall b))
  | RC_Alt (a, b) -> RC_Alt ((rx_cre_dotall a), (rx_cre_dotall b))
  | RC_Star a -> RC_Star (rx_cre_dotall a)
  | RC_Group (n, a) -> RC_Group (n, (rx_cre_dotall a))
let rec rx_cre_repeat_exact (r : rx_cre) (n : Prims.nat) : rx_cre=
  if n = Prims.int_zero
  then RC_Eps
  else RC_Cat (r, (rx_cre_repeat_exact r (n - Prims.int_one)))
let rec rx_cre_repeat_opt (r : rx_cre) (k : Prims.nat) : rx_cre=
  if k = Prims.int_zero
  then RC_Eps
  else
    RC_Cat ((RC_Alt (r, RC_Eps)), (rx_cre_repeat_opt r (k - Prims.int_one)))
let rx_cparse_brace (r : rx_cre) (t : Prims.nat Prims.list) :
  (rx_cre * Prims.nat Prims.list) FStar_Pervasives_Native.option=
  match Regex_XSDPattern.read_uint t with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some (n, t1) ->
      (match t1 with
       | c::t2 ->
           if c = Regex_XSDPattern.cp_rbrace
           then FStar_Pervasives_Native.Some ((rx_cre_repeat_exact r n), t2)
           else
             if c = Regex_XSDPattern.cp_comma
             then
               (match t2 with
                | c2::t3 ->
                    if c2 = Regex_XSDPattern.cp_rbrace
                    then
                      FStar_Pervasives_Native.Some
                        ((RC_Cat ((rx_cre_repeat_exact r n), (RC_Star r))),
                          t3)
                    else
                      (match Regex_XSDPattern.read_uint t2 with
                       | FStar_Pervasives_Native.None ->
                           FStar_Pervasives_Native.None
                       | FStar_Pervasives_Native.Some (m, t3') ->
                           (match t3' with
                            | c3::t4 ->
                                if
                                  (c3 = Regex_XSDPattern.cp_rbrace) &&
                                    (m >= n)
                                then
                                  FStar_Pervasives_Native.Some
                                    ((RC_Cat
                                        ((rx_cre_repeat_exact r n),
                                          (rx_cre_repeat_opt r (m - n)))),
                                      t4)
                                else FStar_Pervasives_Native.None
                            | [] -> FStar_Pervasives_Native.None))
                | [] -> FStar_Pervasives_Native.None)
             else FStar_Pervasives_Native.None
       | [] -> FStar_Pervasives_Native.None)
let rx_cparse_quant (r : rx_cre) (rest : Prims.nat Prims.list) :
  (rx_cre * Prims.nat Prims.list) FStar_Pervasives_Native.option=
  match rest with
  | [] -> FStar_Pervasives_Native.Some (r, rest)
  | q::t ->
      if q = Regex_XSDPattern.cp_star
      then
        FStar_Pervasives_Native.Some
          ((RC_Star r), (Regex_XSDPattern.skip_lazy t))
      else
        if q = Regex_XSDPattern.cp_plus
        then
          FStar_Pervasives_Native.Some
            ((RC_Cat (r, (RC_Star r))), (Regex_XSDPattern.skip_lazy t))
        else
          if q = Regex_XSDPattern.cp_question
          then
            FStar_Pervasives_Native.Some
              ((RC_Alt (r, RC_Eps)), (Regex_XSDPattern.skip_lazy t))
          else
            if q = Regex_XSDPattern.cp_lbrace
            then
              (match rx_cparse_brace r t with
               | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some (r', t') ->
                   FStar_Pervasives_Native.Some
                     (r', (Regex_XSDPattern.skip_lazy t')))
            else FStar_Pervasives_Native.Some (r, rest)
let rec rx_cparse_alt (fuel : Prims.nat) (input : Prims.nat Prims.list)
  (g : Prims.nat) :
  (rx_cre * Prims.nat Prims.list * Prims.nat) FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (match rx_cparse_seq (fuel - Prims.int_one) input g with
     | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
     | FStar_Pervasives_Native.Some (r1, rest, g1) ->
         (match rest with
          | c::t ->
              if c = Regex_XSDPattern.cp_pipe
              then
                (match rx_cparse_alt (fuel - Prims.int_one) t g1 with
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.None
                 | FStar_Pervasives_Native.Some (r2, rest2, g2) ->
                     FStar_Pervasives_Native.Some
                       ((RC_Alt (r1, r2)), rest2, g2))
              else FStar_Pervasives_Native.Some (r1, rest, g1)
          | [] -> FStar_Pervasives_Native.Some (r1, rest, g1)))
and rx_cparse_seq (fuel : Prims.nat) (input : Prims.nat Prims.list)
  (g : Prims.nat) :
  (rx_cre * Prims.nat Prims.list * Prims.nat) FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (match input with
     | [] -> FStar_Pervasives_Native.Some (RC_Eps, [], g)
     | h::uu___1 ->
         if
           (h = Regex_XSDPattern.cp_pipe) || (h = Regex_XSDPattern.cp_rparen)
         then FStar_Pervasives_Native.Some (RC_Eps, input, g)
         else
           (match rx_cparse_rep (fuel - Prims.int_one) input g with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (r1, rest, g1) ->
                (match rest with
                 | [] -> FStar_Pervasives_Native.Some (r1, [], g1)
                 | h2::uu___3 ->
                     if
                       (h2 = Regex_XSDPattern.cp_pipe) ||
                         (h2 = Regex_XSDPattern.cp_rparen)
                     then FStar_Pervasives_Native.Some (r1, rest, g1)
                     else
                       (match rx_cparse_seq (fuel - Prims.int_one) rest g1
                        with
                        | FStar_Pervasives_Native.None ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some (r2, rest2, g2) ->
                            FStar_Pervasives_Native.Some
                              ((RC_Cat (r1, r2)), rest2, g2)))))
and rx_cparse_rep (fuel : Prims.nat) (input : Prims.nat Prims.list)
  (g : Prims.nat) :
  (rx_cre * Prims.nat Prims.list * Prims.nat) FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (match rx_cparse_atom (fuel - Prims.int_one) input g with
     | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
     | FStar_Pervasives_Native.Some (r, rest, g1) ->
         (match rx_cparse_quant r rest with
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (r', rest') ->
              FStar_Pervasives_Native.Some (r', rest', g1)))
and rx_cparse_atom (fuel : Prims.nat) (input : Prims.nat Prims.list)
  (g : Prims.nat) :
  (rx_cre * Prims.nat Prims.list * Prims.nat) FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (match input with
     | [] -> FStar_Pervasives_Native.None
     | h::t ->
         if h = Regex_XSDPattern.cp_lparen
         then rx_cparse_group (fuel - Prims.int_one) t g
         else
           if h = Regex_XSDPattern.cp_lbracket
           then
             (match Regex_XSDPattern.parse_class t with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some (r, rest) ->
                  FStar_Pervasives_Native.Some ((RC_Leaf r), rest, g))
           else
             if h = Regex_XSDPattern.cp_dot
             then
               FStar_Pervasives_Native.Some
                 ((RC_Leaf Regex_XSDPattern.dot_regex), t, g)
             else
               if h = Regex_XSDPattern.cp_caret
               then FStar_Pervasives_Native.Some (RC_Eps, t, g)
               else
                 if h = Regex_XSDPattern.cp_dollar
                 then FStar_Pervasives_Native.Some (RC_Eps, t, g)
                 else
                   if h = Regex_XSDPattern.cp_backslash
                   then
                     (match t with
                      | [] -> FStar_Pervasives_Native.None
                      | letter::t2 ->
                          (match Regex_XSDPattern.parse_escape_atom letter t2
                           with
                           | FStar_Pervasives_Native.None ->
                               FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some (r, rest) ->
                               FStar_Pervasives_Native.Some
                                 ((RC_Leaf r), rest, g)))
                   else
                     if Regex_XSDPattern.is_atom_meta h
                     then FStar_Pervasives_Native.None
                     else
                       FStar_Pervasives_Native.Some
                         ((RC_Leaf (Regex_XSDPattern.single h)), t, g))
and rx_cparse_group (fuel : Prims.nat) (t : Prims.nat Prims.list)
  (g : Prims.nat) :
  (rx_cre * Prims.nat Prims.list * Prims.nat) FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (match t with
     | q::c::t2 ->
         if
           (q = Regex_XSDPattern.cp_question) &&
             (c = Regex_XSDPattern.cp_colon)
         then rx_cparse_noncap (fuel - Prims.int_one) t2 g
         else
           if q = Regex_XSDPattern.cp_question
           then FStar_Pervasives_Native.None
           else rx_cparse_cap (fuel - Prims.int_one) t g
     | q::uu___1 ->
         if q = Regex_XSDPattern.cp_question
         then FStar_Pervasives_Native.None
         else rx_cparse_cap (fuel - Prims.int_one) t g
     | [] -> FStar_Pervasives_Native.None)
and rx_cparse_cap (fuel : Prims.nat) (t : Prims.nat Prims.list)
  (g : Prims.nat) :
  (rx_cre * Prims.nat Prims.list * Prims.nat) FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (match rx_cparse_alt (fuel - Prims.int_one) t (g + Prims.int_one) with
     | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
     | FStar_Pervasives_Native.Some (r, rest, g') ->
         (match rest with
          | c::t2 ->
              if c = Regex_XSDPattern.cp_rparen
              then FStar_Pervasives_Native.Some ((RC_Group (g, r)), t2, g')
              else FStar_Pervasives_Native.None
          | [] -> FStar_Pervasives_Native.None))
and rx_cparse_noncap (fuel : Prims.nat) (t : Prims.nat Prims.list)
  (g : Prims.nat) :
  (rx_cre * Prims.nat Prims.list * Prims.nat) FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (match rx_cparse_alt (fuel - Prims.int_one) t g with
     | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
     | FStar_Pervasives_Native.Some (r, rest, g') ->
         (match rest with
          | c::t2 ->
              if c = Regex_XSDPattern.cp_rparen
              then FStar_Pervasives_Native.Some (r, t2, g')
              else FStar_Pervasives_Native.None
          | [] -> FStar_Pervasives_Native.None))
let rx_parse_capturing (cps : Prims.nat Prims.list) :
  rx_cre FStar_Pervasives_Native.option=
  let fuel =
    (Prims.of_int (16)) *
      ((FStar_List_Tot_Base.length cps) + (Prims.of_int (4))) in
  match rx_cparse_alt fuel cps Prims.int_one with
  | FStar_Pervasives_Native.Some (r, [], uu___) ->
      FStar_Pervasives_Native.Some r
  | uu___ -> FStar_Pervasives_Native.None
let rec rx_cmatch (fuel : Prims.nat) (r : rx_cre) (w : Prims.nat Prims.list)
  (pos : Prims.nat) :
  (Prims.nat Prims.list * Prims.nat * (Prims.nat * Prims.nat * Prims.nat)
    Prims.list) Prims.list=
  if fuel = Prims.int_zero
  then []
  else
    (match r with
     | RC_Eps -> [(w, pos, [])]
     | RC_Leaf x ->
         FStar_List_Tot_Base.map
           (fun k -> let ep = pos + k in ((rx_drop k w), ep, []))
           (rx_leaf_ends x w)
     | RC_Cat (a, b) ->
         FStar_List_Tot_Base.concatMap
           (fun oa ->
              let uu___1 = oa in
              match uu___1 with
              | (resta, epa, capa) ->
                  FStar_List_Tot_Base.map
                    (fun ob ->
                       let uu___2 = ob in
                       match uu___2 with
                       | (restb, epb, capb) ->
                           (restb, epb,
                             (FStar_List_Tot_Base.append capa capb)))
                    (rx_cmatch (fuel - Prims.int_one) b resta epa))
           (rx_cmatch (fuel - Prims.int_one) a w pos)
     | RC_Alt (a, b) ->
         FStar_List_Tot_Base.append
           (rx_cmatch (fuel - Prims.int_one) a w pos)
           (rx_cmatch (fuel - Prims.int_one) b w pos)
     | RC_Group (n, inner) ->
         FStar_List_Tot_Base.map
           (fun o ->
              let uu___1 = o in
              match uu___1 with
              | (rest, ep, caps) -> (rest, ep, ((n, pos, ep) :: caps)))
           (rx_cmatch (fuel - Prims.int_one) inner w pos)
     | RC_Star inner -> (w, pos, []) ::
         (FStar_List_Tot_Base.concatMap
            (fun oi ->
               let uu___1 = oi in
               match uu___1 with
               | (rest, ep, capi) ->
                   if
                     (FStar_List_Tot_Base.length rest) <
                       (FStar_List_Tot_Base.length w)
                   then
                     FStar_List_Tot_Base.map
                       (fun o2 ->
                          let uu___2 = o2 in
                          match uu___2 with
                          | (rest2, ep2, cap2) ->
                              (rest2, ep2,
                                (FStar_List_Tot_Base.append capi cap2)))
                       (rx_cmatch (fuel - Prims.int_one) (RC_Star inner) rest
                          ep)
                   else []) (rx_cmatch (fuel - Prims.int_one) inner w pos)))
let rec rx_pick_caps
  (outs :
    (Prims.nat Prims.list * Prims.nat * (Prims.nat * Prims.nat * Prims.nat)
      Prims.list) Prims.list)
  (target : Prims.nat) : (Prims.nat * Prims.nat * Prims.nat) Prims.list=
  match outs with
  | [] -> []
  | (uu___, ep, caps)::t ->
      if ep = target then caps else rx_pick_caps t target
let rec rx_find_cap (caps : (Prims.nat * Prims.nat * Prims.nat) Prims.list)
  (n : Prims.nat) : (Prims.nat * Prims.nat) FStar_Pervasives_Native.option=
  match caps with
  | [] -> FStar_Pervasives_Native.None
  | (gnum, s, e)::t ->
      if gnum = n
      then FStar_Pervasives_Native.Some (s, e)
      else rx_find_cap t n
let rx_group_text (input : Prims.nat Prims.list)
  (caps : (Prims.nat * Prims.nat * Prims.nat) Prims.list) (n : Prims.nat) :
  Prims.nat Prims.list=
  match rx_find_cap caps n with
  | FStar_Pervasives_Native.None -> []
  | FStar_Pervasives_Native.Some (s, e) -> rx_slice input s e
let rec rx_expand_template (rep : Prims.nat Prims.list)
  (input : Prims.nat Prims.list) (mstart : Prims.nat) (mend : Prims.nat)
  (caps : (Prims.nat * Prims.nat * Prims.nat) Prims.list) :
  Prims.nat Prims.list=
  match rep with
  | [] -> []
  | c::t ->
      if c = rx_cp_backslash
      then
        (match t with
         | c2::t2 -> c2 :: (rx_expand_template t2 input mstart mend caps)
         | [] -> [c])
      else
        if c = (Prims.of_int (0x24))
        then
          (match t with
           | d::t2 ->
               if
                 (d >= (Prims.of_int (0x30))) && (d <= (Prims.of_int (0x39)))
               then
                 let gnum = d - (Prims.of_int (0x30)) in
                 let gt =
                   if gnum = Prims.int_zero
                   then rx_slice input mstart mend
                   else rx_group_text input caps gnum in
                 FStar_List_Tot_Base.append gt
                   (rx_expand_template t2 input mstart mend caps)
               else c :: (rx_expand_template t input mstart mend caps)
           | [] -> [c])
        else c :: (rx_expand_template t input mstart mend caps)
let rec rx_template_has_group (rep : Prims.nat Prims.list) : Prims.bool=
  match rep with
  | [] -> false
  | c::t ->
      if c = rx_cp_backslash
      then
        (match t with | uu___::t2 -> rx_template_has_group t2 | [] -> false)
      else
        if c = (Prims.of_int (0x24))
        then
          (match t with
           | d::uu___1 ->
               if
                 (d >= (Prims.of_int (0x30))) && (d <= (Prims.of_int (0x39)))
               then true
               else rx_template_has_group t
           | [] -> false)
        else rx_template_has_group t
let rx_cmatch_fuel (cre : rx_cre) (suffix : Prims.nat Prims.list) :
  Prims.nat=
  ((rx_cre_size cre) + Prims.int_one) *
    ((FStar_List_Tot_Base.length suffix) + (Prims.of_int (2)))
let rec rx_replace_loop (fuel : Prims.nat) (pr : Regex_Syntax.regex)
  (cre_opt : rx_cre FStar_Pervasives_Native.option)
  (rep : Prims.nat Prims.list) (input_all : Prims.nat Prims.list)
  (suffix : Prims.nat Prims.list) (pos : Prims.nat) : Prims.nat Prims.list=
  if fuel = Prims.int_zero
  then suffix
  else
    (match suffix with
     | [] -> []
     | c::rest ->
         (match rx_longest_end pr suffix with
          | FStar_Pervasives_Native.None -> c ::
              (rx_replace_loop (fuel - Prims.int_one) pr cre_opt rep
                 input_all rest (pos + Prims.int_one))
          | FStar_Pervasives_Native.Some len ->
              if len = Prims.int_zero
              then c ::
                (rx_replace_loop (fuel - Prims.int_one) pr cre_opt rep
                   input_all rest (pos + Prims.int_one))
              else
                (let mend = pos + len in
                 let caps =
                   match cre_opt with
                   | FStar_Pervasives_Native.None -> []
                   | FStar_Pervasives_Native.Some cre ->
                       rx_pick_caps
                         (rx_cmatch (rx_cmatch_fuel cre suffix) cre suffix
                            pos) mend in
                 let expanded =
                   rx_expand_template rep input_all pos mend caps in
                 let new_suffix = rx_drop len suffix in
                 FStar_List_Tot_Base.append expanded
                   (rx_replace_loop (fuel - Prims.int_one) pr cre_opt rep
                      input_all new_suffix mend))))
let regex_replace (text : Prims.string) (pattern : Prims.string)
  (replacement : Prims.string)
  (flags : Prims.string FStar_Pervasives_Native.option) : Prims.string=
  let has_i = rx_flag_has flags 105 in
  let has_s = rx_flag_has flags 115 in
  let has_x = rx_flag_has flags 120 in
  let has_q = rx_flag_has flags 113 in
  let input_cps = Regex_XSDPattern.cps_of_string text in
  let rep_cps = Regex_XSDPattern.cps_of_string replacement in
  let pat_cps0 = Regex_XSDPattern.cps_of_string pattern in
  let fuel = (FStar_List_Tot_Base.length input_cps) + Prims.int_one in
  if has_q
  then
    let core0 = rx_literal_regex pat_cps0 in
    let pr = if has_i then rx_fold_ci core0 else core0 in
    rx_string_of_cps
      (rx_replace_loop fuel pr FStar_Pervasives_Native.None rep_cps input_cps
         input_cps Prims.int_zero)
  else
    (let pat_cps1 = if has_x then rx_strip_ws pat_cps0 false else pat_cps0 in
     match Regex_XSDPattern.parse_cps pat_cps1 with
     | FStar_Pervasives_Native.None -> text
     | FStar_Pervasives_Native.Some r0 ->
         let r1 = if has_s then rx_dotall r0 else r0 in
         let pr = if has_i then rx_fold_ci r1 else r1 in
         let cre_opt =
           if rx_template_has_group rep_cps
           then
             match rx_parse_capturing pat_cps1 with
             | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some cre0 ->
                 let cre1 = if has_s then rx_cre_dotall cre0 else cre0 in
                 FStar_Pervasives_Native.Some
                   ((if has_i then rx_cre_fold_ci cre1 else cre1))
           else FStar_Pervasives_Native.None in
         rx_string_of_cps
           (rx_replace_loop fuel pr cre_opt rep_cps input_cps input_cps
              Prims.int_zero))
let string_replace (s : Prims.string) (pattern : Prims.string)
  (replacement : Prims.string)
  (flags : Prims.string FStar_Pervasives_Native.option) : Prims.string=
  regex_replace s pattern replacement flags
let fn_substr_spec (s : Prims.string) (start : Prims.nat)
  (len : Prims.nat FStar_Pervasives_Native.option) : Prims.string=
  let idx =
    if start > Prims.int_zero then start - Prims.int_one else Prims.int_zero in
  string_substring s idx len
let fn_strdt (lex : Prims.string) (dt : RDF_Term.wf_iri) : RDF_Term.rdf_term=
  if (dt = RDF_Term.rdf_lang_string) || (dt = RDF_Term.rdf_dir_lang_string)
  then
    RDF_Term.T_Literal
      {
        RDF_Term.lexical_form = lex;
        RDF_Term.datatype = RDF_Term.xsd_string;
        RDF_Term.lang_tag = FStar_Pervasives_Native.None;
        RDF_Term.direction = FStar_Pervasives_Native.None
      }
  else
    RDF_Term.T_Literal
      {
        RDF_Term.lexical_form = lex;
        RDF_Term.datatype = dt;
        RDF_Term.lang_tag = FStar_Pervasives_Native.None;
        RDF_Term.direction = FStar_Pervasives_Native.None
      }
let fn_strlang (lex : Prims.string) (lang : Prims.string) :
  RDF_Term.rdf_term=
  RDF_Term.T_Literal
    {
      RDF_Term.lexical_form = lex;
      RDF_Term.datatype = RDF_Term.rdf_lang_string;
      RDF_Term.lang_tag = (FStar_Pervasives_Native.Some lang);
      RDF_Term.direction = FStar_Pervasives_Native.None
    }
let fn_strlangdir (lex : Prims.string) (lang : Prims.string)
  (dir : RDF_Term.text_direction) : RDF_Term.rdf_term=
  RDF_Term.T_Literal
    {
      RDF_Term.lexical_form = lex;
      RDF_Term.datatype = RDF_Term.rdf_dir_lang_string;
      RDF_Term.lang_tag = (FStar_Pervasives_Native.Some lang);
      RDF_Term.direction = (FStar_Pervasives_Native.Some dir)
    }
let same_term (t1 : RDF_Term.rdf_term) (t2 : RDF_Term.rdf_term) : Prims.bool=
  RDF_Term.rdf_term_eq t1 t2
let fn_langMatches_spec (tag : Prims.string) (range : Prims.string) :
  Prims.bool=
  if range = "*"
  then (FStar_String.strlen tag) > Prims.int_zero
  else
    (let ltag = string_lower tag in
     let lrange = string_lower range in
     (ltag = lrange) || (string_starts_with ltag (Prims.strcat lrange "-")))
let hash_md5 (s : Prims.string) : Prims.string=
  Fstar_pure_hashes.md5 s
let hash_sha1 (s : Prims.string) : Prims.string=
  Fstar_pure_hashes.sha1 s
let hash_sha256 (s : Prims.string) : Prims.string=
  Fstar_pure_hashes.sha256 s
let hash_sha384 (s : Prims.string) : Prims.string=
  Fstar_pure_hashes.sha384 s
let hash_sha512 (s : Prims.string) : Prims.string=
  Fstar_pure_hashes.sha512 s
let fx_now_cache : Prims.string ref = ref ""
let fx_current_datetime (uu___ : unit) : Prims.string=
  let open Stdlib in
  if !fx_now_cache <> "" then !fx_now_cache
  else begin
    let t = Unix.gmtime (Unix.gettimeofday ()) in
    let s = Printf.sprintf "%04d-%02d-%02dT%02d:%02d:%02dZ"
      (t.Unix.tm_year + 1900) (t.Unix.tm_mon + 1) t.Unix.tm_mday
      t.Unix.tm_hour t.Unix.tm_min t.Unix.tm_sec in
    fx_now_cache := s; s
  end
let fx_key_row : Prims.string=
  Prims.strcat
    (FStar_String.string_of_list [FStar_Char.char_of_int Prims.int_one])
    "fx_row"
let fx_key_occ : Prims.string=
  Prims.strcat
    (FStar_String.string_of_list [FStar_Char.char_of_int Prims.int_one])
    "fx_occ"
let fx_ctx_get (key : Prims.string)
  (mu : RDF_Graph_Executable.solution_mapping) :
  Prims.string FStar_Pervasives_Native.option=
  match RDF_List_Helpers.assoc_tr key mu with
  | FStar_Pervasives_Native.Some (RDF_Term.T_Literal l) ->
      FStar_Pervasives_Native.Some (l.RDF_Term.lexical_form)
  | uu___ -> FStar_Pervasives_Native.None
let fx_ctx_put (row : Prims.string) (occ : Prims.string)
  (mu : RDF_Graph_Executable.solution_mapping) :
  RDF_Graph_Executable.solution_mapping=
  (fx_key_row,
    (RDF_Term.T_Literal
       {
         RDF_Term.lexical_form = row;
         RDF_Term.datatype = RDF_Term.xsd_string;
         RDF_Term.lang_tag = FStar_Pervasives_Native.None;
         RDF_Term.direction = FStar_Pervasives_Native.None
       }))
  ::
  (fx_key_occ,
    (RDF_Term.T_Literal
       {
         RDF_Term.lexical_form = occ;
         RDF_Term.datatype = RDF_Term.xsd_string;
         RDF_Term.lang_tag = FStar_Pervasives_Native.None;
         RDF_Term.direction = FStar_Pervasives_Native.None
       }))
  :: mu
let rec fx_take_pad (n : Prims.nat) (l : FStar_Char.char Prims.list) :
  FStar_Char.char Prims.list=
  if n = Prims.int_zero
  then []
  else
    (match l with
     | [] -> (FStar_Char.char_of_int (Prims.of_int (48))) ::
         (fx_take_pad (n - Prims.int_one) [])
     | c::cs -> c :: (fx_take_pad (n - Prims.int_one) cs))
let rec fx_ldrop (n : Prims.nat) (l : FStar_Char.char Prims.list) :
  FStar_Char.char Prims.list=
  if n = Prims.int_zero
  then l
  else
    (match l with | [] -> [] | uu___1::cs -> fx_ldrop (n - Prims.int_one) cs)
let fx_uuid_of_seed (seed : Prims.string) : Prims.string=
  let cs =
    fx_take_pad (Prims.of_int (32))
      (FStar_String.list_of_string (hash_sha256 seed)) in
  let s l = FStar_String.string_of_list l in
  let g1 = s (fx_take_pad (Prims.of_int (8)) cs) in
  let r1 = fx_ldrop (Prims.of_int (8)) cs in
  let g2 = s (fx_take_pad (Prims.of_int (4)) r1) in
  let r2 = fx_ldrop (Prims.of_int (4)) r1 in
  let g3 = s (fx_take_pad (Prims.of_int (4)) r2) in
  let r3 = fx_ldrop (Prims.of_int (4)) r2 in
  let g4 = s (fx_take_pad (Prims.of_int (4)) r3) in
  let r4 = fx_ldrop (Prims.of_int (4)) r3 in
  let g5 = s (fx_take_pad (Prims.of_int (12)) r4) in
  Prims.strcat g1
    (Prims.strcat "-"
       (Prims.strcat g2
          (Prims.strcat "-"
             (Prims.strcat g3
                (Prims.strcat "-" (Prims.strcat g4 (Prims.strcat "-" g5)))))))
let fx_bnode_of_seed (seed : Prims.string) : Prims.string=
  Prims.strcat "_:fxbn" (hash_sha256 seed)
let int_abs (n : Prims.int) : Prims.int=
  if n >= Prims.int_zero then n else Prims.int_zero - n
let char_to_digit (c : FStar_Char.char) :
  Prims.int FStar_Pervasives_Native.option=
  let n = FStar_Char.int_of_char c in
  if (n >= (Prims.of_int (48))) && (n <= (Prims.of_int (57)))
  then FStar_Pervasives_Native.Some (n - (Prims.of_int (48)))
  else FStar_Pervasives_Native.None
let rec parse_int_chars (chars : FStar_Char.char Prims.list)
  (acc : Prims.int) : Prims.int FStar_Pervasives_Native.option=
  match chars with
  | [] -> FStar_Pervasives_Native.Some acc
  | c::rest ->
      (match char_to_digit c with
       | FStar_Pervasives_Native.Some d ->
           parse_int_chars rest ((acc * (Prims.of_int (10))) + d)
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
let parse_int_string (s : Prims.string) :
  Prims.int FStar_Pervasives_Native.option=
  match FStar_String.list_of_string s with
  | [] -> FStar_Pervasives_Native.None
  | chars ->
      if
        (FStar_List_Tot_Base.hd chars) =
          (FStar_Char.char_of_int (Prims.of_int (45)))
      then
        (match parse_int_chars (FStar_List_Tot_Base.tl chars) Prims.int_zero
         with
         | FStar_Pervasives_Native.Some n ->
             FStar_Pervasives_Native.Some (Prims.int_zero - n)
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
      else parse_int_chars chars Prims.int_zero
let rec all_zeros (cs : FStar_Char.char Prims.list) : Prims.bool=
  match cs with
  | [] -> true
  | c::rest ->
      ((FStar_Char.int_of_char c) = (Prims.of_int (48))) && (all_zeros rest)
let rec list_take_while :
  'a . ('a -> Prims.bool) -> 'a Prims.list -> 'a Prims.list =
  fun f l ->
    match l with
    | [] -> []
    | x::xs -> if f x then x :: (list_take_while f xs) else []
let rec list_drop_while :
  'a . ('a -> Prims.bool) -> 'a Prims.list -> 'a Prims.list =
  fun f l ->
    match l with
    | [] -> []
    | x::xs -> if f x then list_drop_while f xs else x :: xs
let split_decimal (s : Prims.string) :
  (Prims.int FStar_Pervasives_Native.option * FStar_Char.char Prims.list *
    Prims.bool)=
  let chars = FStar_String.list_of_string s in
  let dot = FStar_Char.char_of_int (Prims.of_int (46)) in
  let before = list_take_while (fun c -> c <> dot) chars in
  let after_with_dot = list_drop_while (fun c -> c <> dot) chars in
  let has_dot = Prims.op_Negation (Prims.uu___is_Nil after_with_dot) in
  let frac = if has_dot then FStar_List_Tot_Base.tl after_with_dot else [] in
  let int_part = parse_int_string (FStar_String.string_of_list before) in
  (int_part, frac, has_dot)
let int_floor (s : Prims.string) : Prims.int=
  let uu___ = split_decimal s in
  match uu___ with
  | (int_part, frac, has_dot) ->
      (match int_part with
       | FStar_Pervasives_Native.None -> Prims.int_zero
       | FStar_Pervasives_Native.Some n ->
           if (Prims.op_Negation has_dot) || (all_zeros frac)
           then n
           else if n >= Prims.int_zero then n else n - Prims.int_one)
let int_ceil (s : Prims.string) : Prims.int=
  let uu___ = split_decimal s in
  match uu___ with
  | (int_part, frac, has_dot) ->
      (match int_part with
       | FStar_Pervasives_Native.None -> Prims.int_zero
       | FStar_Pervasives_Native.Some n ->
           if (Prims.op_Negation has_dot) || (all_zeros frac)
           then n
           else if n >= Prims.int_zero then n + Prims.int_one else n)
let int_round (s : Prims.string) : Prims.int=
  let uu___ = split_decimal s in
  match uu___ with
  | (int_part, frac, has_dot) ->
      (match int_part with
       | FStar_Pervasives_Native.None -> Prims.int_zero
       | FStar_Pervasives_Native.Some n ->
           if
             ((Prims.op_Negation has_dot) || (Prims.uu___is_Nil frac)) ||
               (all_zeros frac)
           then n
           else
             (let first_digit_code =
                FStar_Char.int_of_char (FStar_List_Tot_Base.hd frac) in
              if first_digit_code >= (Prims.of_int (53))
              then
                (if n >= Prims.int_zero
                 then n + Prims.int_one
                 else n - Prims.int_one)
              else n))
type num_kind =
  | NK_Int 
  | NK_Dec 
  | NK_Dbl 
let uu___is_NK_Int (projectee : num_kind) : Prims.bool=
  match projectee with | NK_Int -> true | uu___ -> false
let uu___is_NK_Dec (projectee : num_kind) : Prims.bool=
  match projectee with | NK_Dec -> true | uu___ -> false
let uu___is_NK_Dbl (projectee : num_kind) : Prims.bool=
  match projectee with | NK_Dbl -> true | uu___ -> false
let promote_kind (a : num_kind) (b : num_kind) : num_kind=
  match (a, b) with
  | (NK_Dbl, uu___) -> NK_Dbl
  | (uu___, NK_Dbl) -> NK_Dbl
  | (NK_Dec, uu___) -> NK_Dec
  | (uu___, NK_Dec) -> NK_Dec
  | (uu___, uu___1) -> NK_Int
let rec pow10 (n : Prims.nat) : Prims.int=
  if n = Prims.int_zero
  then Prims.int_one
  else (Prims.of_int (10)) * (pow10 (n - Prims.int_one))
let rec make_zeros (n : Prims.nat) : Prims.string=
  if n = Prims.int_zero
  then ""
  else Prims.strcat "0" (make_zeros (n - Prims.int_one))
let pad_left_zeros (s : Prims.string) (target : Prims.nat) : Prims.string=
  let len = FStar_String.strlen s in
  if len >= target then s else Prims.strcat (make_zeros (target - len)) s
let strip_trailing_zeros_chars (cs : FStar_Char.char Prims.list) :
  FStar_Char.char Prims.list=
  match cs with
  | [] -> []
  | uu___ ->
      let rev = FStar_List_Tot_Base.rev cs in
      let zero_c = FStar_Char.char_of_int (Prims.of_int (48)) in
      let stripped = list_drop_while (fun c -> c = zero_c) rev in
      if Prims.uu___is_Nil stripped
      then [zero_c]
      else FStar_List_Tot_Base.rev stripped
let parse_to_scaled (s : Prims.string) :
  (Prims.int * Prims.nat) FStar_Pervasives_Native.option=
  let uu___ = split_decimal s in
  match uu___ with
  | (ip, frac, has_dot) ->
      (match ip with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some int_part ->
           let scale = FStar_List_Tot_Base.length frac in
           if scale = Prims.int_zero
           then FStar_Pervasives_Native.Some (int_part, Prims.int_zero)
           else
             (let frac_digits = FStar_String.string_of_list frac in
              match parse_int_string frac_digits with
              | FStar_Pervasives_Native.None ->
                  FStar_Pervasives_Native.Some
                    ((int_part * (pow10 scale)), scale)
              | FStar_Pervasives_Native.Some f ->
                  let is_neg =
                    (int_part < Prims.int_zero) ||
                      (((int_part = Prims.int_zero) &&
                          ((FStar_String.strlen s) > Prims.int_zero))
                         &&
                         ((FStar_String.sub s Prims.int_zero Prims.int_one) =
                            "-")) in
                  let abs_scaled =
                    ((int_abs int_part) * (pow10 scale)) + (int_abs f) in
                  FStar_Pervasives_Native.Some
                    ((if is_neg
                      then Prims.int_zero - abs_scaled
                      else abs_scaled), scale)))
let parse_double_to_scaled (s : Prims.string) :
  (Prims.int * Prims.nat) FStar_Pervasives_Native.option=
  let chars = FStar_String.list_of_string s in
  let e_upper = FStar_Char.char_of_int (Prims.of_int (69)) in
  let e_lower = FStar_Char.char_of_int (Prims.of_int (101)) in
  let before_e =
    list_take_while (fun c -> (c <> e_upper) && (c <> e_lower)) chars in
  let after_e_with =
    list_drop_while (fun c -> (c <> e_upper) && (c <> e_lower)) chars in
  if Prims.uu___is_Nil after_e_with
  then parse_to_scaled s
  else
    (let exp_chars = FStar_List_Tot_Base.tl after_e_with in
     let mantissa_str = FStar_String.string_of_list before_e in
     let exp_str = FStar_String.string_of_list exp_chars in
     match ((parse_to_scaled mantissa_str), (parse_int_string exp_str)) with
     | (FStar_Pervasives_Native.Some (mval, mscale),
        FStar_Pervasives_Native.Some exp) ->
         let effective_scale = mscale - exp in
         if effective_scale <= Prims.int_zero
         then
           FStar_Pervasives_Native.Some
             ((mval * (pow10 (Prims.int_zero - effective_scale))),
               Prims.int_zero)
         else FStar_Pervasives_Native.Some (mval, effective_scale)
     | (uu___1, uu___2) -> FStar_Pervasives_Native.None)
let format_scaled_value (value : Prims.int) (scale : Prims.nat) :
  Prims.string=
  if scale = Prims.int_zero
  then Prims.string_of_int value
  else
    (let is_neg = value < Prims.int_zero in
     let abs_val = int_abs value in
     let p = pow10 scale in
     if p = Prims.int_zero
     then Prims.string_of_int value
     else
       (let int_part = abs_val / p in
        let frac_part = abs_val - (int_part * p) in
        let frac_str = pad_left_zeros (Prims.string_of_int frac_part) scale in
        let sign = if is_neg then "-" else "" in
        Prims.strcat sign
          (Prims.strcat (Prims.string_of_int int_part)
             (Prims.strcat "." frac_str))))
let strip_trailing_decimal_zeros (s : Prims.string) : Prims.string=
  let chars = FStar_String.list_of_string s in
  let dot = FStar_Char.char_of_int (Prims.of_int (46)) in
  let before_dot = list_take_while (fun c -> c <> dot) chars in
  let after_dot_with = list_drop_while (fun c -> c <> dot) chars in
  if Prims.uu___is_Nil after_dot_with
  then s
  else
    (let frac = FStar_List_Tot_Base.tl after_dot_with in
     let stripped = strip_trailing_zeros_chars frac in
     Prims.strcat (FStar_String.string_of_list before_dot)
       (Prims.strcat "." (FStar_String.string_of_list stripped)))
let rec count_digits (n : Prims.nat) : Prims.nat=
  if n < (Prims.of_int (10))
  then Prims.int_one
  else Prims.int_one + (count_digits (n / (Prims.of_int (10))))
let format_as_double (value : Prims.int) (scale : Prims.nat) : Prims.string=
  if value = Prims.int_zero
  then "0E0"
  else
    (let is_neg = value < Prims.int_zero in
     let abs_val = int_abs value in
     let ndigits = count_digits abs_val in
     let exp = (ndigits - Prims.int_one) - scale in
     let mantissa_scale = ndigits - Prims.int_one in
     let mantissa_str = format_scaled_value abs_val mantissa_scale in
     let stripped = strip_trailing_decimal_zeros mantissa_str in
     let with_dot =
       if string_contains stripped "."
       then stripped
       else Prims.strcat stripped ".0" in
     let sign = if is_neg then "-" else "" in
     Prims.strcat sign
       (Prims.strcat with_dot (Prims.strcat "E" (Prims.string_of_int exp))))
let er_to_numeric (v : eval_result) :
  (Prims.int * Prims.nat * num_kind) FStar_Pervasives_Native.option=
  match v with
  | ER_Num n -> FStar_Pervasives_Native.Some (n, Prims.int_zero, NK_Int)
  | ER_Dec s ->
      (match parse_to_scaled s with
       | FStar_Pervasives_Native.Some (sv, ss) ->
           FStar_Pervasives_Native.Some (sv, ss, NK_Dec)
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
  | ER_Dbl s ->
      (match parse_double_to_scaled s with
       | FStar_Pervasives_Native.Some (sv, ss) ->
           FStar_Pervasives_Native.Some (sv, ss, NK_Dbl)
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
  | uu___ -> FStar_Pervasives_Native.None
let numeric_compare (a : eval_result) (b : eval_result) :
  Prims.int FStar_Pervasives_Native.option=
  match ((er_to_numeric a), (er_to_numeric b)) with
  | (FStar_Pervasives_Native.Some (v1, s1, uu___),
     FStar_Pervasives_Native.Some (v2, s2, uu___1)) ->
      let uu___2 =
        if s1 >= s2
        then (v1, (v2 * (pow10 (s1 - s2))))
        else ((v1 * (pow10 (s2 - s1))), v2) in
      (match uu___2 with
       | (nv1, nv2) -> FStar_Pervasives_Native.Some (int_compare nv1 nv2))
  | (uu___, uu___1) -> FStar_Pervasives_Native.None
let er_numeric_lexical (v : eval_result) : Prims.string=
  match v with
  | ER_Num n -> Prims.string_of_int n
  | ER_Dec s -> s
  | ER_Dbl s -> s
  | uu___ -> ""
let literal_promote (l : RDF_Term.wf_literal) : eval_result=
  if (lit_datatype l) = RDF_Term.xsd_integer
  then
    match parse_int_string (lit_lexical l) with
    | FStar_Pervasives_Native.Some n -> ER_Num n
    | FStar_Pervasives_Native.None -> ER_Term (RDF_Term.T_Literal l)
  else
    if (lit_datatype l) = RDF_Term.xsd_decimal
    then ER_Dec (lit_lexical l)
    else
      if
        ((lit_datatype l) = RDF_Term.xsd_double) ||
          ((lit_datatype l) = xsd_float)
      then ER_Dbl (lit_lexical l)
      else
        if (lit_datatype l) = RDF_Term.xsd_boolean
        then ER_Bool (((lit_lexical l) = "true") || ((lit_lexical l) = "1"))
        else ER_Term (RDF_Term.T_Literal l)
let literal_value_eq_numeric (l1 : RDF_Term.wf_literal)
  (l2 : RDF_Term.wf_literal) : Prims.bool=
  if
    (is_numeric_datatype (lit_datatype l1)) ||
      (is_numeric_datatype (lit_datatype l2))
  then
    match numeric_compare (literal_promote l1) (literal_promote l2) with
    | FStar_Pervasives_Native.Some cmp -> cmp = Prims.int_zero
    | FStar_Pervasives_Native.None -> false
  else RDF_Term.literal_eq l1 l2
let rec triple_term_value_eq (t1 : RDF_Term.rdf_term)
  (t2 : RDF_Term.rdf_term) : Prims.bool=
  match (t1, t2) with
  | (RDF_Term.T_IRI i1, RDF_Term.T_IRI i2) -> i1 = i2
  | (RDF_Term.T_BNode b1, RDF_Term.T_BNode b2) -> b1 = b2
  | (RDF_Term.T_Literal l1, RDF_Term.T_Literal l2) ->
      literal_value_eq_numeric l1 l2
  | (RDF_Term.T_TripleTerm (s1, p1, o1), RDF_Term.T_TripleTerm (s2, p2, o2))
      ->
      ((RDF_Term.subject_eq s1 s2) && (p1 = p2)) &&
        (triple_term_value_eq o1 o2)
  | (uu___, uu___1) -> false
let value_compare (v1 : eval_result) (v2 : eval_result) (op : comp_op) :
  Prims.bool FStar_Pervasives_Native.option=
  match (v1, v2) with
  | (ER_Num uu___, ER_Num uu___1) ->
      (match numeric_compare v1 v2 with
       | FStar_Pervasives_Native.Some cmp ->
           FStar_Pervasives_Native.Some (apply_comp_op cmp op)
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
  | (ER_Num uu___, ER_Dec uu___1) ->
      (match numeric_compare v1 v2 with
       | FStar_Pervasives_Native.Some cmp ->
           FStar_Pervasives_Native.Some (apply_comp_op cmp op)
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
  | (ER_Num uu___, ER_Dbl uu___1) ->
      (match numeric_compare v1 v2 with
       | FStar_Pervasives_Native.Some cmp ->
           FStar_Pervasives_Native.Some (apply_comp_op cmp op)
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
  | (ER_Dec uu___, ER_Num uu___1) ->
      (match numeric_compare v1 v2 with
       | FStar_Pervasives_Native.Some cmp ->
           FStar_Pervasives_Native.Some (apply_comp_op cmp op)
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
  | (ER_Dec uu___, ER_Dec uu___1) ->
      (match numeric_compare v1 v2 with
       | FStar_Pervasives_Native.Some cmp ->
           FStar_Pervasives_Native.Some (apply_comp_op cmp op)
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
  | (ER_Dec uu___, ER_Dbl uu___1) ->
      (match numeric_compare v1 v2 with
       | FStar_Pervasives_Native.Some cmp ->
           FStar_Pervasives_Native.Some (apply_comp_op cmp op)
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
  | (ER_Dbl uu___, ER_Num uu___1) ->
      (match numeric_compare v1 v2 with
       | FStar_Pervasives_Native.Some cmp ->
           FStar_Pervasives_Native.Some (apply_comp_op cmp op)
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
  | (ER_Dbl uu___, ER_Dec uu___1) ->
      (match numeric_compare v1 v2 with
       | FStar_Pervasives_Native.Some cmp ->
           FStar_Pervasives_Native.Some (apply_comp_op cmp op)
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
  | (ER_Dbl uu___, ER_Dbl uu___1) ->
      (match numeric_compare v1 v2 with
       | FStar_Pervasives_Native.Some cmp ->
           FStar_Pervasives_Native.Some (apply_comp_op cmp op)
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
  | (ER_Bool a, ER_Bool b) ->
      let ia = if a then Prims.int_one else Prims.int_zero in
      let ib = if b then Prims.int_one else Prims.int_zero in
      FStar_Pervasives_Native.Some (apply_comp_op (int_compare ia ib) op)
  | (ER_Term (RDF_Term.T_IRI i1), ER_Term (RDF_Term.T_IRI i2)) ->
      FStar_Pervasives_Native.Some
        (apply_comp_op
           (FStar_String.compare (iri_to_string i1) (iri_to_string i2)) op)
  | (ER_Term (RDF_Term.T_Literal l1), ER_Term (RDF_Term.T_Literal l2)) ->
      if (lit_datatype l1) = (lit_datatype l2)
      then
        (if (lit_lang l1) = (lit_lang l2)
         then
           FStar_Pervasives_Native.Some
             (apply_comp_op
                (FStar_String.compare (lit_lexical l1) (lit_lexical l2)) op)
         else
           (match op with
            | CmpEq -> FStar_Pervasives_Native.Some false
            | CmpNe -> FStar_Pervasives_Native.Some true
            | uu___1 -> FStar_Pervasives_Native.None))
      else FStar_Pervasives_Native.None
  | (ER_Term (RDF_Term.T_TripleTerm (s1, p1, o1)), ER_Term
     (RDF_Term.T_TripleTerm (s2, p2, o2))) ->
      (match op with
       | CmpEq ->
           FStar_Pervasives_Native.Some
             (triple_term_value_eq (RDF_Term.T_TripleTerm (s1, p1, o1))
                (RDF_Term.T_TripleTerm (s2, p2, o2)))
       | CmpNe ->
           FStar_Pervasives_Native.Some
             (Prims.op_Negation
                (triple_term_value_eq (RDF_Term.T_TripleTerm (s1, p1, o1))
                   (RDF_Term.T_TripleTerm (s2, p2, o2))))
       | uu___ -> FStar_Pervasives_Native.None)
  | (ER_Error, uu___) -> FStar_Pervasives_Native.None
  | (uu___, ER_Error) -> FStar_Pervasives_Native.None
  | (uu___, uu___1) -> FStar_Pervasives_Native.None
let add_scaled (v1 : Prims.int) (s1 : Prims.nat) (v2 : Prims.int)
  (s2 : Prims.nat) : (Prims.int * Prims.nat)=
  if s1 >= s2
  then ((v1 + (v2 * (pow10 (s1 - s2)))), s1)
  else (((v1 * (pow10 (s2 - s1))) + v2), s2)
let rec sum_numeric_acc (vals : eval_result Prims.list) (acc_val : Prims.int)
  (acc_scale : Prims.nat) (acc_kind : num_kind) (acc_count : Prims.nat) :
  (Prims.int * Prims.nat * num_kind * Prims.nat)=
  match vals with
  | [] -> (acc_val, acc_scale, acc_kind, acc_count)
  | v::rest ->
      (match er_to_numeric v with
       | FStar_Pervasives_Native.Some (nv, ns, nk) ->
           let uu___ = add_scaled acc_val acc_scale nv ns in
           (match uu___ with
            | (sv, ss) ->
                sum_numeric_acc rest sv ss (promote_kind acc_kind nk)
                  (acc_count + Prims.int_one))
       | FStar_Pervasives_Native.None ->
           sum_numeric_acc rest acc_val acc_scale acc_kind acc_count)
let format_numeric_result (value : Prims.int) (scale : Prims.nat)
  (kind : num_kind) : eval_result=
  match kind with
  | NK_Int ->
      if scale = Prims.int_zero
      then ER_Num value
      else
        (let p = pow10 scale in
         if p = Prims.int_zero then ER_Num value else ER_Num (value / p))
  | NK_Dec ->
      let raw = format_scaled_value value scale in
      ER_Dec (strip_trailing_decimal_zeros raw)
  | NK_Dbl -> ER_Dbl (format_as_double value scale)
let sum_numeric (vals : eval_result Prims.list) : eval_result=
  let uu___ =
    sum_numeric_acc vals Prims.int_zero Prims.int_zero NK_Int Prims.int_zero in
  match uu___ with
  | (v, s, k, c) ->
      if c = Prims.int_zero
      then ER_Num Prims.int_zero
      else format_numeric_result v s k
let rec count_numeric (vals : eval_result Prims.list) : Prims.nat=
  match vals with
  | [] -> Prims.int_zero
  | v::rest ->
      (match er_to_numeric v with
       | FStar_Pervasives_Native.Some uu___ ->
           Prims.int_one + (count_numeric rest)
       | FStar_Pervasives_Native.None -> count_numeric rest)
let avg_numeric (vals : eval_result Prims.list) : eval_result=
  let uu___ =
    sum_numeric_acc vals Prims.int_zero Prims.int_zero NK_Int Prims.int_zero in
  match uu___ with
  | (sum_val, sum_scale, kind, count) ->
      if count = Prims.int_zero
      then ER_Num Prims.int_zero
      else
        (let result_kind = if uu___is_NK_Int kind then NK_Dec else kind in
         let extra = (Prims.of_int (10)) in
         let extended = sum_val * (pow10 extra) in
         let divided =
           if count = Prims.int_zero
           then Prims.int_zero
           else extended / count in
         let result_scale = sum_scale + extra in
         let raw = format_scaled_value divided result_scale in
         let stripped = strip_trailing_decimal_zeros raw in
         match result_kind with
         | NK_Dbl -> ER_Dbl (format_as_double divided result_scale)
         | uu___2 -> ER_Dec stripped)
let dt_year (s : Prims.string) : Prims.int FStar_Pervasives_Native.option=
  let len = FStar_String.strlen s in
  if len < (Prims.of_int (4))
  then FStar_Pervasives_Native.None
  else
    parse_int_string (FStar_String.sub s Prims.int_zero (Prims.of_int (4)))
let dt_month (s : Prims.string) : Prims.int FStar_Pervasives_Native.option=
  let len = FStar_String.strlen s in
  if len < (Prims.of_int (7))
  then FStar_Pervasives_Native.None
  else
    parse_int_string
      (FStar_String.sub s (Prims.of_int (5)) (Prims.of_int (2)))
let dt_day (s : Prims.string) : Prims.int FStar_Pervasives_Native.option=
  let len = FStar_String.strlen s in
  if len < (Prims.of_int (10))
  then FStar_Pervasives_Native.None
  else
    parse_int_string
      (FStar_String.sub s (Prims.of_int (8)) (Prims.of_int (2)))
let dt_hours (s : Prims.string) : Prims.int FStar_Pervasives_Native.option=
  let len = FStar_String.strlen s in
  if len < (Prims.of_int (13))
  then FStar_Pervasives_Native.None
  else
    parse_int_string
      (FStar_String.sub s (Prims.of_int (11)) (Prims.of_int (2)))
let dt_minutes (s : Prims.string) : Prims.int FStar_Pervasives_Native.option=
  let len = FStar_String.strlen s in
  if len < (Prims.of_int (16))
  then FStar_Pervasives_Native.None
  else
    parse_int_string
      (FStar_String.sub s (Prims.of_int (14)) (Prims.of_int (2)))
let strip_leading_zeros_num (s : Prims.string) : Prims.string=
  let chars = FStar_String.list_of_string s in
  let zero_code = (Prims.of_int (48)) in
  let rec skip_zeros cs =
    match cs with
    | c::rest ->
        if (FStar_Char.int_of_char c) = zero_code
        then
          (match rest with
           | [] -> cs
           | c2::uu___ ->
               let c2i = FStar_Char.int_of_char c2 in
               if c2i = (Prims.of_int (46)) then cs else skip_zeros rest)
        else cs
    | [] -> [FStar_Char.char_of_int zero_code] in
  FStar_String.string_of_list (skip_zeros chars)
let dt_seconds (s : Prims.string) :
  Prims.string FStar_Pervasives_Native.option=
  let len = FStar_String.strlen s in
  if len < (Prims.of_int (19))
  then FStar_Pervasives_Native.None
  else
    (let chars = FStar_String.list_of_string s in
     let after_17 = list_drop (Prims.of_int (17)) chars in
     let rec find_end cs count =
       match cs with
       | [] -> count
       | c::rest ->
           let ci = FStar_Char.int_of_char c in
           if
             ((ci = (Prims.of_int (90))) || (ci = (Prims.of_int (43)))) ||
               (ci = (Prims.of_int (45)))
           then count
           else find_end rest (count + Prims.int_one) in
     let sec_len = find_end after_17 Prims.int_zero in
     if sec_len = Prims.int_zero
     then FStar_Pervasives_Native.None
     else
       if ((Prims.of_int (17)) + sec_len) <= (FStar_String.strlen s)
       then
         FStar_Pervasives_Native.Some
           (strip_leading_zeros_num
              (FStar_String.sub s (Prims.of_int (17)) sec_len))
       else FStar_Pervasives_Native.None)
let dt_timezone (s : Prims.string) :
  Prims.string FStar_Pervasives_Native.option=
  let len = FStar_String.strlen s in
  if len < (Prims.of_int (19))
  then FStar_Pervasives_Native.None
  else
    (let last_char = FStar_String.index s (len - Prims.int_one) in
     if (FStar_Char.int_of_char last_char) = (Prims.of_int (90))
     then FStar_Pervasives_Native.Some "PT0S"
     else
       (let chars = FStar_String.list_of_string s in
        let rec find_tz cs pos =
          match cs with
          | [] -> FStar_Pervasives_Native.None
          | c::rest ->
              let ci = FStar_Char.int_of_char c in
              if
                (pos >= (Prims.of_int (19))) &&
                  ((ci = (Prims.of_int (43))) || (ci = (Prims.of_int (45))))
              then FStar_Pervasives_Native.Some pos
              else find_tz rest (pos + Prims.int_one) in
        match find_tz chars Prims.int_zero with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.Some ""
        | FStar_Pervasives_Native.Some pos ->
            if len >= (pos + (Prims.of_int (6)))
            then
              let sign = FStar_String.index s pos in
              let sign_str =
                if (FStar_Char.int_of_char sign) = (Prims.of_int (45))
                then "-"
                else "" in
              let h_str =
                FStar_String.sub s (pos + Prims.int_one) (Prims.of_int (2)) in
              let m_str =
                FStar_String.sub s (pos + (Prims.of_int (4)))
                  (Prims.of_int (2)) in
              (match ((parse_int_string h_str), (parse_int_string m_str))
               with
               | (FStar_Pervasives_Native.Some h,
                  FStar_Pervasives_Native.Some m) ->
                   if m = Prims.int_zero
                   then
                     FStar_Pervasives_Native.Some
                       (Prims.strcat sign_str
                          (Prims.strcat "PT"
                             (Prims.strcat (Prims.string_of_int h) "H")))
                   else
                     FStar_Pervasives_Native.Some
                       (Prims.strcat sign_str
                          (Prims.strcat "PT"
                             (Prims.strcat (Prims.string_of_int h)
                                (Prims.strcat "H"
                                   (Prims.strcat (Prims.string_of_int m) "M")))))
               | (uu___2, uu___3) -> FStar_Pervasives_Native.None)
            else FStar_Pervasives_Native.None))
let dt_tz (s : Prims.string) : Prims.string FStar_Pervasives_Native.option=
  let len = FStar_String.strlen s in
  if len < (Prims.of_int (19))
  then FStar_Pervasives_Native.None
  else
    (let last_char = FStar_String.index s (len - Prims.int_one) in
     if (FStar_Char.int_of_char last_char) = (Prims.of_int (90))
     then FStar_Pervasives_Native.Some "Z"
     else
       (let chars = FStar_String.list_of_string s in
        let rec find_tz_pos cs pos =
          match cs with
          | [] -> FStar_Pervasives_Native.None
          | c::rest ->
              let ci = FStar_Char.int_of_char c in
              if
                (pos >= (Prims.of_int (19))) &&
                  ((ci = (Prims.of_int (43))) || (ci = (Prims.of_int (45))))
              then FStar_Pervasives_Native.Some pos
              else find_tz_pos rest (pos + Prims.int_one) in
        match find_tz_pos chars Prims.int_zero with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.Some ""
        | FStar_Pervasives_Native.Some pos ->
            if pos < len
            then
              FStar_Pervasives_Native.Some
                (FStar_String.sub s pos (len - pos))
            else FStar_Pervasives_Native.None))
let resolve_iri (base : RDF_Term.wf_iri) (relative : Prims.string) :
  RDF_Term.wf_iri= SPARQL11_IRI_Resolve.resolve_iri base relative
let resolve_query_iri (base : RDF_Term.wf_iri FStar_Pervasives_Native.option)
  (rel : Prims.string) : RDF_Term.wf_iri FStar_Pervasives_Native.option=
  SPARQL11_IRI_Resolve.resolve_query_iri base rel
let rec unescape_chars (cs : FStar_String.char Prims.list) :
  FStar_String.char Prims.list=
  match cs with
  | [] -> []
  | c1::rest ->
      if c1 = (FStar_Char.char_of_int (Prims.of_int (92)))
      then
        (match rest with
         | [] -> [c1]
         | c2::rest' ->
             let code = FStar_Char.int_of_char c2 in
             if code = (Prims.of_int (92))
             then (FStar_Char.char_of_int (Prims.of_int (92))) ::
               (unescape_chars rest')
             else
               if code = (Prims.of_int (110))
               then (FStar_Char.char_of_int (Prims.of_int (10))) ::
                 (unescape_chars rest')
               else
                 if code = (Prims.of_int (114))
                 then (FStar_Char.char_of_int (Prims.of_int (13))) ::
                   (unescape_chars rest')
                 else
                   if code = (Prims.of_int (116))
                   then (FStar_Char.char_of_int (Prims.of_int (9))) ::
                     (unescape_chars rest')
                   else
                     if code = (Prims.of_int (34))
                     then (FStar_Char.char_of_int (Prims.of_int (34))) ::
                       (unescape_chars rest')
                     else
                       if code = (Prims.of_int (39))
                       then (FStar_Char.char_of_int (Prims.of_int (39))) ::
                         (unescape_chars rest')
                       else c1 :: c2 :: (unescape_chars rest'))
      else c1 :: (unescape_chars rest)
let unescape_sparql_string (s : Prims.string) : Prims.string=
  FStar_String.string_of_list
    (unescape_chars (FStar_String.list_of_string s))
let fn_regex_spec (s : Prims.string) (pattern : Prims.string)
  (flags : Prims.string FStar_Pervasives_Native.option) : Prims.bool=
  regex_match s (unescape_sparql_string pattern) flags
type solution_sequence = RDF_Graph_Executable.solution_mapping Prims.list
let subject_to_term (s : RDF_Term.subject) : RDF_Term.rdf_term=
  match s with
  | RDF_Term.S_IRI i -> RDF_Term.T_IRI i
  | RDF_Term.S_BNode b -> RDF_Term.T_BNode b
let try_bind_subject (ps : pattern_subject) (s : RDF_Term.subject)
  (mu : RDF_Graph_Executable.solution_mapping) :
  RDF_Graph_Executable.solution_mapping FStar_Pervasives_Native.option=
  match ps with
  | PS_IRI i ->
      (match s with
       | RDF_Term.S_IRI i' ->
           if i = i'
           then FStar_Pervasives_Native.Some mu
           else FStar_Pervasives_Native.None
       | uu___ -> FStar_Pervasives_Native.None)
  | PS_BNode b ->
      (match s with
       | RDF_Term.S_BNode b' ->
           if b = b'
           then FStar_Pervasives_Native.Some mu
           else FStar_Pervasives_Native.None
       | uu___ -> FStar_Pervasives_Native.None)
  | PS_TripleTerm (uu___, uu___1, uu___2) -> FStar_Pervasives_Native.None
  | PS_Var v ->
      let term = subject_to_term s in
      (match sm_lookup v mu with
       | FStar_Pervasives_Native.Some existing ->
           if RDF_Term.rdf_term_eq existing term
           then FStar_Pervasives_Native.Some mu
           else FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.None ->
           FStar_Pervasives_Native.Some (sm_bind v term mu))
let rec try_bind_term (pt : pattern_term) (t : RDF_Term.rdf_term)
  (mu : RDF_Graph_Executable.solution_mapping) :
  RDF_Graph_Executable.solution_mapping FStar_Pervasives_Native.option=
  match pt with
  | PT_IRI i ->
      (match t with
       | RDF_Term.T_IRI i' ->
           if i = i'
           then FStar_Pervasives_Native.Some mu
           else FStar_Pervasives_Native.None
       | uu___ -> FStar_Pervasives_Native.None)
  | PT_BNode b ->
      (match t with
       | RDF_Term.T_BNode b' ->
           if b = b'
           then FStar_Pervasives_Native.Some mu
           else FStar_Pervasives_Native.None
       | uu___ -> FStar_Pervasives_Native.None)
  | PT_Literal l ->
      (match t with
       | RDF_Term.T_Literal l' ->
           if RDF_Term.literal_eq l l'
           then FStar_Pervasives_Native.Some mu
           else FStar_Pervasives_Native.None
       | uu___ -> FStar_Pervasives_Native.None)
  | PT_TripleTerm (ps, pp, po) ->
      (match t with
       | RDF_Term.T_TripleTerm (s, p, o) ->
           (match try_bind_term ps (subject_to_term s) mu with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some mu1 ->
                (match try_bind_term pp (RDF_Term.T_IRI p) mu1 with
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.None
                 | FStar_Pervasives_Native.Some mu2 -> try_bind_term po o mu2))
       | uu___ -> FStar_Pervasives_Native.None)
  | PT_Var v ->
      (match sm_lookup v mu with
       | FStar_Pervasives_Native.Some existing ->
           if RDF_Term.rdf_term_eq existing t
           then FStar_Pervasives_Native.Some mu
           else FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.None ->
           FStar_Pervasives_Native.Some (sm_bind v t mu))
let pattern_term_matches (pt : pattern_term) (t : RDF_Term.rdf_term)
  (mu : RDF_Graph_Executable.solution_mapping) : Prims.bool=
  FStar_Pervasives_Native.uu___is_Some (try_bind_term pt t mu)
let pattern_subject_matches (ps : pattern_subject) (s : RDF_Term.subject)
  (mu : RDF_Graph_Executable.solution_mapping) : Prims.bool=
  FStar_Pervasives_Native.uu___is_Some (try_bind_subject ps s mu)
let tp_match (tp : triple_pattern) (t : RDF_Triple.triple)
  (mu : RDF_Graph_Executable.solution_mapping) :
  RDF_Graph_Executable.solution_mapping FStar_Pervasives_Native.option=
  match try_bind_subject tp.tp_s t.RDF_Triple.s mu with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some mu1 ->
      (match try_bind_term tp.tp_p (RDF_Term.T_IRI (t.RDF_Triple.p)) mu1 with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some mu2 ->
           try_bind_term tp.tp_o t.RDF_Triple.o mu2)
let eval_single_tp_store_default (tp : triple_pattern) (gs : graph_store)
  (mu : RDF_Graph_Executable.solution_mapping) : solution_sequence=
  let bound =
    {
      bs = (bound_subject_of_pattern tp.tp_s mu);
      bp = (bound_predicate_of_pattern tp.tp_p mu);
      bo = (bound_object_of_pattern tp.tp_o mu)
    } in
  let candidates = store_search gs bound in
  list_filter_map (fun t -> tp_match tp t mu) candidates
let eval_fulltext_tp_store (ftq : SPARQL_FullText.fulltext_query)
  (tp : triple_pattern) (gs : graph_store)
  (mu : RDF_Graph_Executable.solution_mapping) : solution_sequence=
  let bound =
    {
      bs = FStar_Pervasives_Native.None;
      bp = (ftq.SPARQL_FullText.ftq_field);
      bo = FStar_Pervasives_Native.None
    } in
  let candidates = store_search gs bound in
  let matched =
    FStar_List_Tot_Base.filter
      (fun t -> SPARQL_FullText.object_matches_query ftq t.RDF_Triple.o)
      candidates in
  let limited =
    match ftq.SPARQL_FullText.ftq_limit with
    | FStar_Pervasives_Native.Some n -> list_take n matched
    | FStar_Pervasives_Native.None -> matched in
  list_filter_map (fun t -> try_bind_subject tp.tp_s t.RDF_Triple.s mu)
    limited
let eval_single_tp_store (tp : triple_pattern) (gs : graph_store)
  (mu : RDF_Graph_Executable.solution_mapping) : solution_sequence=
  match tp.tp_p with
  | PT_IRI pred ->
      if pred = SPARQL_FullText.fulltext_query_pred
      then
        (match tp.tp_o with
         | PT_Literal args_lit ->
             (match SPARQL_FullText.decode_fulltext_literal args_lit with
              | FStar_Pervasives_Native.Some ftq ->
                  eval_fulltext_tp_store ftq tp gs mu
              | FStar_Pervasives_Native.None ->
                  eval_single_tp_store_default tp gs mu)
         | uu___ -> eval_single_tp_store_default tp gs mu)
      else eval_single_tp_store_default tp gs mu
  | uu___ -> eval_single_tp_store_default tp gs mu
let estimate_tp_store_mu (tp : triple_pattern) (gs : graph_store)
  (mu : RDF_Graph_Executable.solution_mapping) : Prims.nat=
  store_estimate gs
    {
      bs = (bound_subject_of_pattern tp.tp_s mu);
      bp = (bound_predicate_of_pattern tp.tp_p mu);
      bo = (bound_object_of_pattern tp.tp_o mu)
    }
let rec choose_best_tp (patterns : bgp) (gs : graph_store)
  (mu : RDF_Graph_Executable.solution_mapping) :
  (triple_pattern * bgp) FStar_Pervasives_Native.option=
  match patterns with
  | [] -> FStar_Pervasives_Native.None
  | tp::rest ->
      (match choose_best_tp rest gs mu with
       | FStar_Pervasives_Native.None ->
           FStar_Pervasives_Native.Some (tp, [])
       | FStar_Pervasives_Native.Some (best, remaining) ->
           if
             (estimate_tp_store_mu tp gs mu) <=
               (estimate_tp_store_mu best gs mu)
           then FStar_Pervasives_Native.Some (tp, rest)
           else FStar_Pervasives_Native.Some (best, (tp :: remaining)))
let rec eval_bgp_store_from_mu_fuel (patterns : bgp) (gs : graph_store)
  (mu : RDF_Graph_Executable.solution_mapping) (fuel : Prims.nat) :
  solution_sequence=
  if fuel = Prims.int_zero
  then [mu]
  else
    (match patterns with
     | [] -> [mu]
     | uu___1 ->
         (match choose_best_tp patterns gs mu with
          | FStar_Pervasives_Native.None -> [mu]
          | FStar_Pervasives_Native.Some (tp, rest) ->
              let next = eval_single_tp_store tp gs mu in
              RDF_List_Helpers.concatMap_tr
                (fun mu' ->
                   eval_bgp_store_from_mu_fuel rest gs mu'
                     (fuel - Prims.int_one)) next))
let eval_bgp_store (patterns : bgp) (gs : graph_store) : solution_sequence=
  eval_bgp_store_from_mu_fuel patterns gs sm_empty
    ((FStar_List_Tot_Base.length patterns) + Prims.int_one)
let eval_bgp (patterns : bgp) (g : RDF_Graph.rdf_graph) : solution_sequence=
  eval_bgp_store patterns (graph_to_store g)
let rec vars_intersect (vs1 : var_name Prims.list)
  (vs2 : var_name Prims.list) : var_name Prims.list=
  match vs1 with
  | [] -> []
  | v::rest ->
      if FStar_List_Tot_Base.mem v vs2
      then v :: (vars_intersect rest vs2)
      else vars_intersect rest vs2
let rec sm_join_key (vars : var_name Prims.list)
  (mu : RDF_Graph_Executable.solution_mapping) :
  Prims.string FStar_Pervasives_Native.option=
  match vars with
  | [] -> FStar_Pervasives_Native.Some ""
  | v::rest ->
      (match ((sm_lookup v mu), (sm_join_key rest mu)) with
       | (FStar_Pervasives_Native.Some t, FStar_Pervasives_Native.Some
          rest_key) ->
           FStar_Pervasives_Native.Some
             (Prims.strcat
                (RDF_NQuads_Serialize.nq_term_to_string
                   (RDF_Term.join_canon_term t))
                (Prims.strcat RDF_Indexed.unit_sep rest_key))
       | (uu___, uu___1) -> FStar_Pervasives_Native.None)
type join_index =
  {
  ji_keyed: RDF_Graph_Executable.solution_mapping RDF_Indexed.bucket_tree ;
  ji_wildcard: RDF_Graph_Executable.solution_mapping Prims.list }
let __proj__Mkjoin_index__item__ji_keyed (projectee : join_index) :
  RDF_Graph_Executable.solution_mapping RDF_Indexed.bucket_tree=
  match projectee with | { ji_keyed; ji_wildcard;_} -> ji_keyed
let __proj__Mkjoin_index__item__ji_wildcard (projectee : join_index) :
  RDF_Graph_Executable.solution_mapping Prims.list=
  match projectee with | { ji_keyed; ji_wildcard;_} -> ji_wildcard
let build_join_index (vars : var_name Prims.list) (omega : solution_sequence)
  : join_index=
  let decorated =
    FStar_List_Tot_Base.map (fun mu -> ((sm_join_key vars mu), mu)) omega in
  let sorted =
    FStar_List_Tot_Base.sortWith RDF_Indexed.cmp_by_decorated_key decorated in
  let grouped =
    FStar_List_Tot_Base.rev
      (RDF_Indexed.group_sorted_decorated_aux sorted
         FStar_Pervasives_Native.None [] []) in
  let wildcard =
    list_filter_map
      (fun mu ->
         if (sm_join_key vars mu) = FStar_Pervasives_Native.None
         then FStar_Pervasives_Native.Some mu
         else FStar_Pervasives_Native.None) omega in
  {
    ji_keyed = (RDF_Indexed.sorted_list_to_tree grouped);
    ji_wildcard = wildcard
  }
let join_candidates (idx : join_index) (vars : var_name Prims.list)
  (mu : RDF_Graph_Executable.solution_mapping) :
  RDF_Graph_Executable.solution_mapping Prims.list=
  match sm_join_key vars mu with
  | FStar_Pervasives_Native.Some k ->
      RDF_List_Helpers.append_tr idx.ji_wildcard
        (RDF_Indexed.bucket_lookup idx.ji_keyed k)
  | FStar_Pervasives_Native.None ->
      RDF_List_Helpers.append_tr idx.ji_wildcard
        (RDF_Indexed.bucket_tree_values idx.ji_keyed)
let join_nested_loop (omega1 : solution_sequence)
  (omega2 : solution_sequence) : solution_sequence=
  RDF_List_Helpers.concatMap_tr
    (fun mu1 ->
       list_filter_map
         (fun mu2 ->
            if sm_compatible mu1 mu2
            then FStar_Pervasives_Native.Some (sm_merge mu1 mu2)
            else FStar_Pervasives_Native.None) omega2) omega1
let join (omega1 : solution_sequence) (omega2 : solution_sequence) :
  solution_sequence=
  match (omega1, omega2) with
  | ([], uu___) -> []
  | (uu___, []) -> []
  | (mu1_0::uu___, mu2_0::uu___1) ->
      let vars = vars_intersect (sm_domain mu1_0) (sm_domain mu2_0) in
      if vars = []
      then join_nested_loop omega1 omega2
      else
        (let build_is_omega1 =
           (FStar_List_Tot_Base.length omega1) <=
             (FStar_List_Tot_Base.length omega2) in
         let uu___3 =
           if build_is_omega1 then (omega1, omega2) else (omega2, omega1) in
         match uu___3 with
         | (build_omega, probe_omega) ->
             let idx = build_join_index vars build_omega in
             RDF_List_Helpers.concatMap_tr
               (fun mu_probe ->
                  let candidates = join_candidates idx vars mu_probe in
                  list_filter_map
                    (fun mu_build ->
                       let uu___4 =
                         if build_is_omega1
                         then (mu_build, mu_probe)
                         else (mu_probe, mu_build) in
                       match uu___4 with
                       | (mu1, mu2) ->
                           if sm_compatible mu1 mu2
                           then
                             FStar_Pervasives_Native.Some (sm_merge mu1 mu2)
                           else FStar_Pervasives_Native.None) candidates)
               probe_omega)
let lateral_subst_pattern_term (mu : RDF_Graph_Executable.solution_mapping)
  (pt : pattern_term) : pattern_term=
  match pt with
  | PT_Var v ->
      (match sm_lookup v mu with
       | FStar_Pervasives_Native.Some (RDF_Term.T_IRI i) -> PT_IRI i
       | FStar_Pervasives_Native.Some (RDF_Term.T_BNode b) -> PT_BNode b
       | FStar_Pervasives_Native.Some (RDF_Term.T_Literal l) -> PT_Literal l
       | FStar_Pervasives_Native.Some (RDF_Term.T_TripleTerm
           (uu___, uu___1, uu___2)) -> PT_Var v
       | FStar_Pervasives_Native.None -> PT_Var v)
  | uu___ -> pt
let lateral_subst_pattern_subject
  (mu : RDF_Graph_Executable.solution_mapping) (ps : pattern_subject) :
  pattern_subject=
  match ps with
  | PS_Var v ->
      (match sm_lookup v mu with
       | FStar_Pervasives_Native.Some (RDF_Term.T_IRI i) -> PS_IRI i
       | FStar_Pervasives_Native.Some (RDF_Term.T_BNode b) -> PS_BNode b
       | FStar_Pervasives_Native.Some (RDF_Term.T_Literal uu___) -> PS_Var v
       | FStar_Pervasives_Native.Some (RDF_Term.T_TripleTerm
           (uu___, uu___1, uu___2)) -> PS_Var v
       | FStar_Pervasives_Native.None -> PS_Var v)
  | uu___ -> ps
let lateral_subst_triple_pattern (mu : RDF_Graph_Executable.solution_mapping)
  (tp : triple_pattern) : triple_pattern=
  {
    tp_s = (lateral_subst_pattern_subject mu tp.tp_s);
    tp_p = (lateral_subst_pattern_term mu tp.tp_p);
    tp_o = (lateral_subst_pattern_term mu tp.tp_o)
  }
let lateral_subst_bgp (mu : RDF_Graph_Executable.solution_mapping) (b : bgp)
  : bgp= FStar_List_Tot_Base.map (lateral_subst_triple_pattern mu) b
let rec lateral_assignable_vars (p : group_graph_pattern) :
  var_name Prims.list=
  match p with
  | GP_Bind (uu___, v, p1) -> v :: (lateral_assignable_vars p1)
  | GP_Values (vars, uu___) -> vars
  | GP_SubSelect q ->
      (match q.q_form with
       | QF_Select (Select_Vars items) ->
           list_filter_map
             (fun item ->
                match item with
                | SI_Var uu___ -> FStar_Pervasives_Native.None
                | SI_Expr (uu___, v) -> FStar_Pervasives_Native.Some v) items
       | QF_Select (Select_All) -> lateral_assignable_vars q.q_pattern
       | uu___ -> [])
  | GP_Join (p1, p2) ->
      FStar_List_Tot_Base.op_At (lateral_assignable_vars p1)
        (lateral_assignable_vars p2)
  | GP_LeftJoin (p1, p2, uu___) ->
      FStar_List_Tot_Base.op_At (lateral_assignable_vars p1)
        (lateral_assignable_vars p2)
  | GP_Union (p1, p2) ->
      FStar_List_Tot_Base.op_At (lateral_assignable_vars p1)
        (lateral_assignable_vars p2)
  | GP_Lateral (p1, p2) ->
      FStar_List_Tot_Base.op_At (lateral_assignable_vars p1)
        (lateral_assignable_vars p2)
  | GP_Filter (uu___, p1) -> lateral_assignable_vars p1
  | GP_Graph (uu___, p1) -> lateral_assignable_vars p1
  | GP_Minus (p1, uu___) -> lateral_assignable_vars p1
  | GP_Service (uu___, p1, uu___1) -> lateral_assignable_vars p1
  | GP_ServiceVar (uu___, p1, uu___1) -> lateral_assignable_vars p1
  | GP_BGP uu___ -> []
  | GP_PropertyPath (uu___, uu___1, uu___2) -> []
  | GP_Empty -> []
let lateral_subselect_visible_vars (q : query) :
  var_name Prims.list FStar_Pervasives_Native.option=
  match q.q_form with
  | QF_Select (Select_Vars items) ->
      FStar_Pervasives_Native.Some
        (FStar_List_Tot_Base.map
           (fun item ->
              match item with | SI_Var v -> v | SI_Expr (uu___, v) -> v)
           items)
  | QF_Select (Select_All) -> FStar_Pervasives_Native.None
  | uu___ -> FStar_Pervasives_Native.Some []
let lateral_subselect_visible_mu (mu : RDF_Graph_Executable.solution_mapping)
  (q : query) : RDF_Graph_Executable.solution_mapping=
  let mu_visible =
    match lateral_subselect_visible_vars q with
    | FStar_Pervasives_Native.None -> mu
    | FStar_Pervasives_Native.Some vis ->
        FStar_List_Tot_Base.filter
          (fun b ->
             FStar_List_Tot_Base.existsb
               (fun v -> v = (FStar_Pervasives_Native.fst b)) vis) mu in
  let shadowed = lateral_assignable_vars q.q_pattern in
  FStar_List_Tot_Base.filter
    (fun b ->
       Prims.op_Negation
         (FStar_List_Tot_Base.existsb
            (fun s -> s = (FStar_Pervasives_Native.fst b)) shadowed))
    mu_visible
let rec lateral_substitute (mu : RDF_Graph_Executable.solution_mapping)
  (p : group_graph_pattern) : group_graph_pattern=
  match p with
  | GP_BGP b -> GP_BGP (lateral_subst_bgp mu b)
  | GP_Join (p1, p2) ->
      GP_Join ((lateral_substitute mu p1), (lateral_substitute mu p2))
  | GP_LeftJoin (p1, p2, e) ->
      GP_LeftJoin ((lateral_substitute mu p1), (lateral_substitute mu p2), e)
  | GP_Filter (e, p1) -> GP_Filter (e, (lateral_substitute mu p1))
  | GP_Union (p1, p2) ->
      GP_Union ((lateral_substitute mu p1), (lateral_substitute mu p2))
  | GP_Graph (gt, p1) ->
      GP_Graph
        ((lateral_subst_pattern_term mu gt), (lateral_substitute mu p1))
  | GP_Minus (p1, p2) ->
      GP_Minus ((lateral_substitute mu p1), (lateral_substitute mu p2))
  | GP_Bind (e, v, p1) -> GP_Bind (e, v, (lateral_substitute mu p1))
  | GP_Values (vars, rows) -> GP_Values (vars, rows)
  | GP_Service (iri, p1, silent) ->
      GP_Service (iri, (lateral_substitute mu p1), silent)
  | GP_ServiceVar (v, p1, silent) ->
      (match sm_lookup v mu with
       | FStar_Pervasives_Native.Some (RDF_Term.T_IRI iri) ->
           if RDF_Term.is_iri iri
           then GP_Service (iri, (lateral_substitute mu p1), silent)
           else GP_ServiceVar (v, (lateral_substitute mu p1), silent)
       | uu___ -> GP_ServiceVar (v, (lateral_substitute mu p1), silent))
  | GP_SubSelect q ->
      GP_SubSelect
        {
          q_base = (q.q_base);
          q_prefixes = (q.q_prefixes);
          q_form = (q.q_form);
          q_dataset = (q.q_dataset);
          q_pattern =
            (lateral_substitute (lateral_subselect_visible_mu mu q)
               q.q_pattern);
          q_group_by = (q.q_group_by);
          q_having = (q.q_having);
          q_modifier = (q.q_modifier);
          q_values = (q.q_values)
        }
  | GP_PropertyPath (ps, pp, pt) ->
      GP_PropertyPath
        ((lateral_subst_pattern_subject mu ps), pp,
          (lateral_subst_pattern_term mu pt))
  | GP_Lateral (p1, p2) ->
      GP_Lateral ((lateral_substitute mu p1), (lateral_substitute mu p2))
  | GP_Empty -> GP_Empty
let lateral_wrap_as_query (p : group_graph_pattern) : query=
  {
    q_base = FStar_Pervasives_Native.None;
    q_prefixes = [];
    q_form = (QF_Select Select_All);
    q_dataset = [];
    q_pattern = p;
    q_group_by = FStar_Pervasives_Native.None;
    q_having = FStar_Pervasives_Native.None;
    q_modifier =
      {
        sm_order_by = FStar_Pervasives_Native.None;
        sm_distinct = false;
        sm_reduced = false;
        sm_offset = FStar_Pervasives_Native.None;
        sm_limit = FStar_Pervasives_Native.None
      };
    q_values = FStar_Pervasives_Native.None
  }
let rec pattern_has_binding_source (p : group_graph_pattern) : Prims.bool=
  match p with
  | GP_Bind (uu___, uu___1, uu___2) -> true
  | GP_Values (uu___, uu___1) -> true
  | GP_SubSelect uu___ -> true
  | GP_Service (uu___, uu___1, uu___2) -> true
  | GP_ServiceVar (uu___, uu___1, uu___2) -> true
  | GP_Lateral (uu___, uu___1) -> true
  | GP_BGP uu___ -> false
  | GP_PropertyPath (uu___, uu___1, uu___2) -> false
  | GP_Empty -> false
  | GP_Join (p1, p2) ->
      (pattern_has_binding_source p1) || (pattern_has_binding_source p2)
  | GP_Union (p1, p2) ->
      (pattern_has_binding_source p1) || (pattern_has_binding_source p2)
  | GP_Minus (p1, p2) ->
      (pattern_has_binding_source p1) || (pattern_has_binding_source p2)
  | GP_LeftJoin (p1, p2, uu___) ->
      (pattern_has_binding_source p1) || (pattern_has_binding_source p2)
  | GP_Filter (uu___, p1) -> pattern_has_binding_source p1
  | GP_Graph (uu___, p1) -> pattern_has_binding_source p1
let rec pattern_term_var (pt : pattern_term) : var_name Prims.list=
  match pt with
  | PT_Var v -> [v]
  | PT_IRI uu___ -> []
  | PT_BNode uu___ -> []
  | PT_Literal uu___ -> []
  | PT_TripleTerm (s, p, o) ->
      FStar_List_Tot_Base.op_At (pattern_term_var s)
        (FStar_List_Tot_Base.op_At (pattern_term_var p) (pattern_term_var o))
let pattern_subject_var (ps : pattern_subject) : var_name Prims.list=
  match ps with
  | PS_Var v -> [v]
  | PS_IRI uu___ -> []
  | PS_BNode uu___ -> []
  | PS_TripleTerm (uu___, uu___1, uu___2) -> []
let tp_vars (tp : triple_pattern) : var_name Prims.list=
  FStar_List_Tot_Base.op_At (pattern_subject_var tp.tp_s)
    (FStar_List_Tot_Base.op_At (pattern_term_var tp.tp_p)
       (pattern_term_var tp.tp_o))
let rec bgp_vars (b : bgp) : var_name Prims.list=
  match b with
  | [] -> []
  | tp::rest -> FStar_List_Tot_Base.op_At (tp_vars tp) (bgp_vars rest)
let rec pattern_var_occurrences (p : group_graph_pattern) :
  var_name Prims.list=
  match p with
  | GP_BGP b -> bgp_vars b
  | GP_PropertyPath (ps, uu___, pt) ->
      FStar_List_Tot_Base.op_At (pattern_subject_var ps)
        (pattern_term_var pt)
  | GP_Join (p1, p2) ->
      FStar_List_Tot_Base.op_At (pattern_var_occurrences p1)
        (pattern_var_occurrences p2)
  | GP_Union (p1, p2) ->
      FStar_List_Tot_Base.op_At (pattern_var_occurrences p1)
        (pattern_var_occurrences p2)
  | GP_Minus (p1, p2) ->
      FStar_List_Tot_Base.op_At (pattern_var_occurrences p1)
        (pattern_var_occurrences p2)
  | GP_LeftJoin (p1, p2, uu___) ->
      FStar_List_Tot_Base.op_At (pattern_var_occurrences p1)
        (pattern_var_occurrences p2)
  | GP_Filter (uu___, p1) -> pattern_var_occurrences p1
  | GP_Graph (uu___, p1) -> pattern_var_occurrences p1
  | GP_Bind (uu___, uu___1, uu___2) -> []
  | GP_Values (uu___, uu___1) -> []
  | GP_SubSelect uu___ -> []
  | GP_Service (uu___, uu___1, uu___2) -> []
  | GP_ServiceVar (uu___, uu___1, uu___2) -> []
  | GP_Lateral (uu___, uu___1) -> []
  | GP_Empty -> []
let var_is_shared (occ : var_name Prims.list) (v : var_name) : Prims.bool=
  (FStar_List_Tot_Base.length
     (FStar_List_Tot_Base.filter (fun x -> x = v) occ))
    >= (Prims.of_int (2))
let subj_boundable (occ : var_name Prims.list) (ps : pattern_subject) :
  Prims.bool=
  match ps with
  | PS_IRI uu___ -> true
  | PS_BNode uu___ -> true
  | PS_Var v -> var_is_shared occ v
  | PS_TripleTerm (uu___, uu___1, uu___2) -> false
let term_boundable (occ : var_name Prims.list) (pt : pattern_term) :
  Prims.bool=
  match pt with
  | PT_IRI uu___ -> true
  | PT_BNode uu___ -> true
  | PT_Literal uu___ -> true
  | PT_Var v -> var_is_shared occ v
  | PT_TripleTerm (uu___, uu___1, uu___2) -> false
let tp_bucket_needs (occ : var_name Prims.list) (tp : triple_pattern) :
  RDF_Indexed.bucket_needs=
  let s_ok = subj_boundable occ tp.tp_s in
  let p_ok = term_boundable occ tp.tp_p in
  let o_ok = term_boundable occ tp.tp_o in
  {
    RDF_Indexed.bn_pred = p_ok;
    RDF_Indexed.bn_subj = s_ok;
    RDF_Indexed.bn_obj = o_ok;
    RDF_Indexed.bn_sp = (s_ok && p_ok);
    RDF_Indexed.bn_po = (p_ok && o_ok);
    RDF_Indexed.bn_so = (s_ok && o_ok)
  }
let rec bgp_bucket_needs (occ : var_name Prims.list) (b : bgp) :
  RDF_Indexed.bucket_needs=
  match b with
  | [] -> RDF_Indexed.no_bucket_needs
  | tp::rest ->
      RDF_Indexed.bucket_needs_or (tp_bucket_needs occ tp)
        (bgp_bucket_needs occ rest)
let rec pattern_bucket_needs (occ : var_name Prims.list)
  (p : group_graph_pattern) : RDF_Indexed.bucket_needs=
  match p with
  | GP_BGP b -> bgp_bucket_needs occ b
  | GP_PropertyPath (uu___, uu___1, uu___2) -> RDF_Indexed.no_bucket_needs
  | GP_Join (p1, p2) ->
      RDF_Indexed.bucket_needs_or (pattern_bucket_needs occ p1)
        (pattern_bucket_needs occ p2)
  | GP_Union (p1, p2) ->
      RDF_Indexed.bucket_needs_or (pattern_bucket_needs occ p1)
        (pattern_bucket_needs occ p2)
  | GP_Minus (p1, p2) ->
      RDF_Indexed.bucket_needs_or (pattern_bucket_needs occ p1)
        (pattern_bucket_needs occ p2)
  | GP_LeftJoin (p1, p2, uu___) ->
      RDF_Indexed.bucket_needs_or (pattern_bucket_needs occ p1)
        (pattern_bucket_needs occ p2)
  | GP_Filter (uu___, p1) -> pattern_bucket_needs occ p1
  | GP_Graph (uu___, p1) -> pattern_bucket_needs occ p1
  | GP_Bind (uu___, uu___1, uu___2) -> RDF_Indexed.all_bucket_needs
  | GP_Values (uu___, uu___1) -> RDF_Indexed.all_bucket_needs
  | GP_SubSelect uu___ -> RDF_Indexed.all_bucket_needs
  | GP_Service (uu___, uu___1, uu___2) -> RDF_Indexed.all_bucket_needs
  | GP_ServiceVar (uu___, uu___1, uu___2) -> RDF_Indexed.all_bucket_needs
  | GP_Lateral (uu___, uu___1) -> RDF_Indexed.all_bucket_needs
  | GP_Empty -> RDF_Indexed.no_bucket_needs
let bucket_needs_of_pattern (p : group_graph_pattern) :
  RDF_Indexed.bucket_needs=
  if pattern_has_binding_source p
  then RDF_Indexed.all_bucket_needs
  else pattern_bucket_needs (pattern_var_occurrences p) p
let rec expr_vars (e : expr) : var_name Prims.list=
  match e with
  | E_Var v -> [v]
  | E_IRI uu___ -> []
  | E_Literal uu___ -> []
  | E_BoolLit uu___ -> []
  | E_NumericLit uu___ -> []
  | E_DecimalLit uu___ -> []
  | E_DoubleLit uu___ -> []
  | E_Arith (uu___, e1, e2) ->
      FStar_List_Tot_Base.op_At (expr_vars e1) (expr_vars e2)
  | E_UnaryMinus e1 -> expr_vars e1
  | E_UnaryPlus e1 -> expr_vars e1
  | E_Compare (uu___, e1, e2) ->
      FStar_List_Tot_Base.op_At (expr_vars e1) (expr_vars e2)
  | E_And (e1, e2) -> FStar_List_Tot_Base.op_At (expr_vars e1) (expr_vars e2)
  | E_Or (e1, e2) -> FStar_List_Tot_Base.op_At (expr_vars e1) (expr_vars e2)
  | E_Not e1 -> expr_vars e1
  | E_IsIRI e1 -> expr_vars e1
  | E_IsBlank e1 -> expr_vars e1
  | E_IsLiteral e1 -> expr_vars e1
  | E_IsNumeric e1 -> expr_vars e1
  | E_Str e1 -> expr_vars e1
  | E_Lang e1 -> expr_vars e1
  | E_Datatype e1 -> expr_vars e1
  | E_IRI_fn e1 -> expr_vars e1
  | E_HasLang e1 -> expr_vars e1
  | E_HasLangDir e1 -> expr_vars e1
  | E_LangDir e1 -> expr_vars e1
  | E_StrDt (e1, e2) ->
      FStar_List_Tot_Base.op_At (expr_vars e1) (expr_vars e2)
  | E_StrLang (e1, e2) ->
      FStar_List_Tot_Base.op_At (expr_vars e1) (expr_vars e2)
  | E_StrLangDir (e1, e2, e3) ->
      FStar_List_Tot_Base.op_At (expr_vars e1)
        (FStar_List_Tot_Base.op_At (expr_vars e2) (expr_vars e3))
  | E_Bound v -> [v]
  | E_If (c, t, f) ->
      FStar_List_Tot_Base.op_At (expr_vars c)
        (FStar_List_Tot_Base.op_At (expr_vars t) (expr_vars f))
  | E_Coalesce es -> expr_list_vars es
  | E_In (e1, es) ->
      FStar_List_Tot_Base.op_At (expr_vars e1) (expr_list_vars es)
  | E_NotIn (e1, es) ->
      FStar_List_Tot_Base.op_At (expr_vars e1) (expr_list_vars es)
  | E_StrLen e1 -> expr_vars e1
  | E_Substr (e1, e2, e3_opt) ->
      FStar_List_Tot_Base.op_At (expr_vars e1)
        (FStar_List_Tot_Base.op_At (expr_vars e2) (expr_opt_vars e3_opt))
  | E_UCase e1 -> expr_vars e1
  | E_LCase e1 -> expr_vars e1
  | E_StrStarts (e1, e2) ->
      FStar_List_Tot_Base.op_At (expr_vars e1) (expr_vars e2)
  | E_StrEnds (e1, e2) ->
      FStar_List_Tot_Base.op_At (expr_vars e1) (expr_vars e2)
  | E_Contains (e1, e2) ->
      FStar_List_Tot_Base.op_At (expr_vars e1) (expr_vars e2)
  | E_StrBefore (e1, e2) ->
      FStar_List_Tot_Base.op_At (expr_vars e1) (expr_vars e2)
  | E_StrAfter (e1, e2) ->
      FStar_List_Tot_Base.op_At (expr_vars e1) (expr_vars e2)
  | E_Concat es -> expr_list_vars es
  | E_EncodeForUri e1 -> expr_vars e1
  | E_Replace (e1, e2, e3, e4_opt) ->
      FStar_List_Tot_Base.op_At (expr_vars e1)
        (FStar_List_Tot_Base.op_At (expr_vars e2)
           (FStar_List_Tot_Base.op_At (expr_vars e3) (expr_opt_vars e4_opt)))
  | E_Regex (e1, e2, e3_opt) ->
      FStar_List_Tot_Base.op_At (expr_vars e1)
        (FStar_List_Tot_Base.op_At (expr_vars e2) (expr_opt_vars e3_opt))
  | E_Abs e1 -> expr_vars e1
  | E_Round e1 -> expr_vars e1
  | E_Ceil e1 -> expr_vars e1
  | E_Floor e1 -> expr_vars e1
  | E_MD5 e1 -> expr_vars e1
  | E_SHA1 e1 -> expr_vars e1
  | E_SHA256 e1 -> expr_vars e1
  | E_SHA384 e1 -> expr_vars e1
  | E_SHA512 e1 -> expr_vars e1
  | E_Now -> []
  | E_Year e1 -> expr_vars e1
  | E_Month e1 -> expr_vars e1
  | E_Day e1 -> expr_vars e1
  | E_Hours e1 -> expr_vars e1
  | E_Minutes e1 -> expr_vars e1
  | E_Seconds e1 -> expr_vars e1
  | E_Timezone e1 -> expr_vars e1
  | E_Tz e1 -> expr_vars e1
  | E_SameTerm (e1, e2) ->
      FStar_List_Tot_Base.op_At (expr_vars e1) (expr_vars e2)
  | E_Exists p -> pattern_all_vars p
  | E_NotExists p -> pattern_all_vars p
  | E_Aggregate (uu___, uu___1, e1) -> expr_vars e1
  | E_FunctionCall (uu___, es) -> expr_list_vars es
  | E_TripleTerm (a, b, c) ->
      FStar_List_Tot_Base.op_At (expr_vars a)
        (FStar_List_Tot_Base.op_At (expr_vars b) (expr_vars c))
  | E_TTSubject e1 -> expr_vars e1
  | E_TTPredicate e1 -> expr_vars e1
  | E_TTObject e1 -> expr_vars e1
  | E_IsTriple e1 -> expr_vars e1
and expr_list_vars (es : expr Prims.list) : var_name Prims.list=
  match es with
  | [] -> []
  | e::rest -> FStar_List_Tot_Base.op_At (expr_vars e) (expr_list_vars rest)
and expr_opt_vars (eo : expr FStar_Pervasives_Native.option) :
  var_name Prims.list=
  match eo with
  | FStar_Pervasives_Native.None -> []
  | FStar_Pervasives_Native.Some e -> expr_vars e
and pattern_all_vars (p : group_graph_pattern) : var_name Prims.list=
  match p with
  | GP_BGP b -> bgp_vars b
  | GP_Join (p1, p2) ->
      FStar_List_Tot_Base.op_At (pattern_all_vars p1) (pattern_all_vars p2)
  | GP_Union (p1, p2) ->
      FStar_List_Tot_Base.op_At (pattern_all_vars p1) (pattern_all_vars p2)
  | GP_Minus (p1, p2) ->
      FStar_List_Tot_Base.op_At (pattern_all_vars p1) (pattern_all_vars p2)
  | GP_Lateral (p1, p2) ->
      FStar_List_Tot_Base.op_At (pattern_all_vars p1) (pattern_all_vars p2)
  | GP_LeftJoin (p1, p2, e) ->
      FStar_List_Tot_Base.op_At (pattern_all_vars p1)
        (FStar_List_Tot_Base.op_At (pattern_all_vars p2) (expr_vars e))
  | GP_Filter (e, p1) ->
      FStar_List_Tot_Base.op_At (expr_vars e) (pattern_all_vars p1)
  | GP_Graph (pt, p1) ->
      FStar_List_Tot_Base.op_At (pattern_term_var pt) (pattern_all_vars p1)
  | GP_Bind (e, v, p1) ->
      FStar_List_Tot_Base.op_At (expr_vars e) (v :: (pattern_all_vars p1))
  | GP_Values (vs, _rows) -> vs
  | GP_Service (uu___, p1, uu___1) -> pattern_all_vars p1
  | GP_ServiceVar (v, p1, uu___) -> v :: (pattern_all_vars p1)
  | GP_SubSelect q -> query_all_vars q
  | GP_PropertyPath (ps, uu___, pt) ->
      FStar_List_Tot_Base.op_At (pattern_subject_var ps)
        (pattern_term_var pt)
  | GP_Empty -> []
and query_all_vars (q : query) : var_name Prims.list=
  FStar_List_Tot_Base.op_At (pattern_all_vars q.q_pattern)
    (FStar_List_Tot_Base.op_At (query_form_all_vars q.q_form)
       (FStar_List_Tot_Base.op_At
          (match q.q_group_by with
           | FStar_Pervasives_Native.None -> []
           | FStar_Pervasives_Native.Some gcs -> group_conditions_vars gcs)
          (FStar_List_Tot_Base.op_At
             (match q.q_having with
              | FStar_Pervasives_Native.None -> []
              | FStar_Pervasives_Native.Some hs -> expr_list_vars hs)
             (FStar_List_Tot_Base.op_At
                (match (q.q_modifier).sm_order_by with
                 | FStar_Pervasives_Native.None -> []
                 | FStar_Pervasives_Native.Some ocs ->
                     order_conditions_vars ocs)
                (match q.q_values with
                 | FStar_Pervasives_Native.None -> []
                 | FStar_Pervasives_Native.Some rows -> values_rows_vars rows)))))
and query_form_all_vars (qf : query_form) : var_name Prims.list=
  match qf with
  | QF_Select sc -> select_clause_vars sc
  | QF_Construct tps -> bgp_vars tps
  | QF_Ask -> []
  | QF_Describe pts -> pattern_terms_vars pts
and select_clause_vars (sc : select_clause) : var_name Prims.list=
  match sc with
  | Select_All -> []
  | Select_Vars items -> select_items_all_vars items
and select_items_all_vars (items : select_item Prims.list) :
  var_name Prims.list=
  match items with
  | [] -> []
  | (SI_Var v)::rest -> v :: (select_items_all_vars rest)
  | (SI_Expr (e, v))::rest ->
      FStar_List_Tot_Base.op_At (expr_vars e) (v ::
        (select_items_all_vars rest))
and group_conditions_vars (gcs : group_condition Prims.list) :
  var_name Prims.list=
  match gcs with
  | [] -> []
  | (GC_Var v)::rest -> v :: (group_conditions_vars rest)
  | (GC_Expr (e, alias))::rest ->
      FStar_List_Tot_Base.op_At (expr_vars e)
        (FStar_List_Tot_Base.op_At
           (match alias with
            | FStar_Pervasives_Native.Some a -> [a]
            | FStar_Pervasives_Native.None -> [])
           (group_conditions_vars rest))
  | (GC_BuiltIn e)::rest ->
      FStar_List_Tot_Base.op_At (expr_vars e) (group_conditions_vars rest)
and order_conditions_vars (ocs : order_condition Prims.list) :
  var_name Prims.list=
  match ocs with
  | [] -> []
  | (OC_Asc e)::rest ->
      FStar_List_Tot_Base.op_At (expr_vars e) (order_conditions_vars rest)
  | (OC_Desc e)::rest ->
      FStar_List_Tot_Base.op_At (expr_vars e) (order_conditions_vars rest)
and pattern_terms_vars (pts : pattern_term Prims.list) : var_name Prims.list=
  match pts with
  | [] -> []
  | pt::rest ->
      FStar_List_Tot_Base.op_At (pattern_term_var pt)
        (pattern_terms_vars rest)
and values_rows_vars
  (rows : (var_name * RDF_Term.rdf_term) Prims.list Prims.list) :
  var_name Prims.list=
  match rows with
  | [] -> []
  | row::rest ->
      FStar_List_Tot_Base.op_At (values_row_vars row) (values_rows_vars rest)
and values_row_vars (row : (var_name * RDF_Term.rdf_term) Prims.list) :
  var_name Prims.list=
  match row with | [] -> [] | (v, uu___)::rest -> v :: (values_row_vars rest)
let rec pattern_filter_bind_vars (p : group_graph_pattern) :
  var_name Prims.list=
  match p with
  | GP_BGP uu___ -> []
  | GP_PropertyPath (uu___, uu___1, uu___2) -> []
  | GP_Join (p1, p2) ->
      FStar_List_Tot_Base.op_At (pattern_filter_bind_vars p1)
        (pattern_filter_bind_vars p2)
  | GP_Union (p1, p2) ->
      FStar_List_Tot_Base.op_At (pattern_filter_bind_vars p1)
        (pattern_filter_bind_vars p2)
  | GP_Minus (p1, p2) ->
      FStar_List_Tot_Base.op_At (pattern_filter_bind_vars p1)
        (pattern_filter_bind_vars p2)
  | GP_Lateral (p1, p2) ->
      FStar_List_Tot_Base.op_At (pattern_filter_bind_vars p1)
        (pattern_filter_bind_vars p2)
  | GP_LeftJoin (p1, p2, e) ->
      FStar_List_Tot_Base.op_At (pattern_filter_bind_vars p1)
        (FStar_List_Tot_Base.op_At (pattern_filter_bind_vars p2)
           (expr_vars e))
  | GP_Filter (e, p1) ->
      FStar_List_Tot_Base.op_At (expr_vars e) (pattern_filter_bind_vars p1)
  | GP_Graph (uu___, p1) -> pattern_filter_bind_vars p1
  | GP_Bind (e, _v, p1) ->
      FStar_List_Tot_Base.op_At (expr_vars e) (pattern_filter_bind_vars p1)
  | GP_Values (vs, _rows) -> vs
  | GP_Service (uu___, p1, uu___1) -> pattern_filter_bind_vars p1
  | GP_ServiceVar (v, p1, uu___) -> v :: (pattern_filter_bind_vars p1)
  | GP_SubSelect q -> query_all_vars q
  | GP_Empty -> []
let rec select_item_vars_full (items : select_item Prims.list) :
  var_name Prims.list=
  match items with
  | [] -> []
  | (SI_Var v)::rest -> v :: (select_item_vars_full rest)
  | (SI_Expr (e, v))::rest ->
      FStar_List_Tot_Base.op_At (expr_vars e) (v ::
        (select_item_vars_full rest))
let query_clause_vars (q : query) : var_name Prims.list=
  FStar_List_Tot_Base.op_At (pattern_filter_bind_vars q.q_pattern)
    (FStar_List_Tot_Base.op_At
       (match q.q_group_by with
        | FStar_Pervasives_Native.None -> []
        | FStar_Pervasives_Native.Some gcs -> group_conditions_vars gcs)
       (FStar_List_Tot_Base.op_At
          (match q.q_having with
           | FStar_Pervasives_Native.None -> []
           | FStar_Pervasives_Native.Some hs -> expr_list_vars hs)
          (match (q.q_modifier).sm_order_by with
           | FStar_Pervasives_Native.None -> []
           | FStar_Pervasives_Native.Some ocs -> order_conditions_vars ocs)))
let query_live_vars (q : query) : var_name Prims.list=
  match q.q_form with
  | QF_Select (Select_All) -> query_all_vars q
  | QF_Select (Select_Vars items) ->
      FStar_List_Tot_Base.op_At (select_item_vars_full items)
        (query_clause_vars q)
  | QF_Construct uu___ -> query_all_vars q
  | QF_Ask -> query_all_vars q
  | QF_Describe uu___ -> query_all_vars q
let col_need_for_tp (occ : var_name Prims.list) (live : var_name Prims.list)
  (tp : triple_pattern) : RDF_Graph_Executable.col_need=
  let needs_var v = (FStar_List_Tot_Base.mem v live) || (var_is_shared occ v) in
  {
    RDF_Graph_Executable.cn_s =
      (match tp.tp_s with
       | PS_Var v -> needs_var v
       | PS_IRI uu___ -> false
       | PS_BNode uu___ -> false
       | PS_TripleTerm (uu___, uu___1, uu___2) -> true);
    RDF_Graph_Executable.cn_p =
      (match tp.tp_p with
       | PT_Var v -> needs_var v
       | PT_IRI uu___ -> false
       | PT_BNode uu___ -> false
       | PT_Literal uu___ -> false
       | PT_TripleTerm (uu___, uu___1, uu___2) -> true);
    RDF_Graph_Executable.cn_o =
      (match tp.tp_o with
       | PT_Var v -> needs_var v
       | PT_IRI uu___ -> false
       | PT_BNode uu___ -> false
       | PT_Literal uu___ -> false
       | PT_TripleTerm (uu___, uu___1, uu___2) -> true)
  }
let graph_to_store_for (p : group_graph_pattern) (g : RDF_Graph.rdf_graph) :
  graph_store=
  {
    gs_graph = g;
    gs_indexed =
      (RDF_Indexed.build_indexed_selective (bucket_needs_of_pattern p) g)
  }
let dataset_to_store_for (p : group_graph_pattern)
  (ds : RDF_Graph.rdf_dataset) : rdf_dataset_store=
  {
    dss_default = (graph_to_store_for p ds.RDF_Graph.ds_default);
    dss_named =
      (FStar_List_Tot_Base.map
         (fun ng ->
            {
              ngs_name = (ng.RDF_Graph.ng_name);
              ngs_store = (graph_to_store_for p ng.RDF_Graph.ng_graph)
            }) ds.RDF_Graph.ds_named)
  }
let strip_leading_plus (s : Prims.string) : Prims.string=
  if (FStar_String.strlen s) > Prims.int_zero
  then
    let chars = FStar_String.list_of_string s in
    match chars with
    | c::rest ->
        (if c = (FStar_Char.char_of_int (Prims.of_int (43)))
         then FStar_String.string_of_list rest
         else s)
    | [] -> s
  else s
let eval_xsd_cast (v : eval_result) (target_type : Prims.string)
  (full_iri : Prims.string) : eval_result=
  let get_lex =
    match v with
    | ER_Num n -> FStar_Pervasives_Native.Some (Prims.string_of_int n)
    | ER_Dec s -> FStar_Pervasives_Native.Some s
    | ER_Dbl s -> FStar_Pervasives_Native.Some s
    | ER_Bool b ->
        FStar_Pervasives_Native.Some (if b then "true" else "false")
    | ER_Term (RDF_Term.T_Literal l) ->
        FStar_Pervasives_Native.Some (lit_lexical l)
    | ER_Term (RDF_Term.T_IRI i) ->
        FStar_Pervasives_Native.Some (iri_to_string i)
    | uu___ -> FStar_Pervasives_Native.None in
  match get_lex with
  | FStar_Pervasives_Native.None -> ER_Error
  | FStar_Pervasives_Native.Some lex0 ->
      let lex =
        if (target_type = "string") || (target_type = "boolean")
        then lex0
        else strip_leading_plus lex0 in
      if target_type = "integer"
      then
        (match v with
         | ER_Bool b -> ER_Num (if b then Prims.int_one else Prims.int_zero)
         | uu___ ->
             (match parse_int_string lex with
              | FStar_Pervasives_Native.Some n -> ER_Num n
              | FStar_Pervasives_Native.None ->
                  (match parse_double_to_scaled lex with
                   | FStar_Pervasives_Native.Some (sv, sc) ->
                       let divisor = pow10 sc in
                       if divisor = Prims.int_zero
                       then ER_Num Prims.int_zero
                       else
                         (let raw = sv / divisor in
                          let remainder = sv - (raw * divisor) in
                          if
                            (sv < Prims.int_zero) &&
                              (remainder <> Prims.int_zero)
                          then ER_Num (raw + Prims.int_one)
                          else ER_Num raw)
                   | FStar_Pervasives_Native.None ->
                       let uu___1 = split_decimal lex in
                       (match uu___1 with
                        | (ip, uu___2, uu___3) ->
                            (match ip with
                             | FStar_Pervasives_Native.Some n -> ER_Num n
                             | FStar_Pervasives_Native.None -> ER_Error)))))
      else
        if target_type = "decimal"
        then
          (match v with
           | ER_Bool b -> ER_Dec (if b then "1.0" else "0.0")
           | ER_Num n -> ER_Dec (Prims.strcat (Prims.string_of_int n) ".0")
           | ER_Dec uu___1 -> ER_Dec lex
           | uu___1 ->
               (match parse_to_scaled lex with
                | FStar_Pervasives_Native.Some uu___2 -> ER_Dec lex
                | FStar_Pervasives_Native.None ->
                    (match parse_double_to_scaled lex with
                     | FStar_Pervasives_Native.Some (sv, sc) ->
                         let divisor = pow10 sc in
                         if divisor = Prims.int_zero
                         then ER_Dec "0.0"
                         else
                           if ((mod) sv divisor) = Prims.int_zero
                           then
                             ER_Dec
                               (Prims.strcat
                                  (Prims.string_of_int (sv / divisor)) ".0")
                           else ER_Dec lex
                     | FStar_Pervasives_Native.None ->
                         (match parse_int_string lex with
                          | FStar_Pervasives_Native.Some n ->
                              ER_Dec
                                (Prims.strcat (Prims.string_of_int n) ".0")
                          | FStar_Pervasives_Native.None -> ER_Error))))
        else
          if target_type = "double"
          then
            (match v with
             | ER_Bool b -> ER_Dbl (if b then "1.0E0" else "0.0E0")
             | ER_Num n ->
                 ER_Dbl (Prims.strcat (Prims.string_of_int n) ".0E0")
             | ER_Dbl uu___2 -> ER_Dbl lex
             | ER_Dec uu___2 ->
                 (match parse_to_scaled lex with
                  | FStar_Pervasives_Native.Some uu___3 -> ER_Dbl lex
                  | FStar_Pervasives_Native.None -> ER_Error)
             | uu___2 ->
                 (match parse_double_to_scaled lex with
                  | FStar_Pervasives_Native.Some uu___3 -> ER_Dbl lex
                  | FStar_Pervasives_Native.None ->
                      (match parse_to_scaled lex with
                       | FStar_Pervasives_Native.Some uu___3 -> ER_Dbl lex
                       | FStar_Pervasives_Native.None ->
                           (match parse_int_string lex with
                            | FStar_Pervasives_Native.Some n ->
                                ER_Dbl
                                  (Prims.strcat (Prims.string_of_int n)
                                     ".0E0")
                            | FStar_Pervasives_Native.None -> ER_Error))))
          else
            if target_type = "float"
            then
              (let mk_float s =
                 ER_Term
                   (RDF_Term.T_Literal
                      {
                        RDF_Term.lexical_form = s;
                        RDF_Term.datatype = xsd_float;
                        RDF_Term.lang_tag = FStar_Pervasives_Native.None;
                        RDF_Term.direction = FStar_Pervasives_Native.None
                      }) in
               let canon_int_float n =
                 if n = Prims.int_zero
                 then "0.0"
                 else Prims.strcat (Prims.string_of_int n) ".0" in
               let try_canon_dbl s =
                 match parse_double_to_scaled s with
                 | FStar_Pervasives_Native.Some (sv, sc) ->
                     let p = pow10 sc in
                     if
                       (p > Prims.int_zero) &&
                         (((mod) sv p) = Prims.int_zero)
                     then
                       FStar_Pervasives_Native.Some
                         (canon_int_float (sv / p))
                     else FStar_Pervasives_Native.None
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.None in
               match v with
               | ER_Bool b -> mk_float (if b then "1.0E0" else "0E0")
               | ER_Num n ->
                   mk_float
                     (if n = Prims.int_zero
                      then "0"
                      else Prims.strcat (Prims.string_of_int n) ".0")
               | ER_Dbl uu___3 ->
                   (match try_canon_dbl lex with
                    | FStar_Pervasives_Native.Some canon -> mk_float canon
                    | FStar_Pervasives_Native.None -> mk_float lex)
               | ER_Dec uu___3 ->
                   (match parse_to_scaled lex with
                    | FStar_Pervasives_Native.Some uu___4 -> mk_float lex
                    | FStar_Pervasives_Native.None -> ER_Error)
               | uu___3 ->
                   (match parse_double_to_scaled lex with
                    | FStar_Pervasives_Native.Some uu___4 -> mk_float lex
                    | FStar_Pervasives_Native.None ->
                        (match parse_to_scaled lex with
                         | FStar_Pervasives_Native.Some uu___4 ->
                             mk_float lex
                         | FStar_Pervasives_Native.None ->
                             (match parse_int_string lex with
                              | FStar_Pervasives_Native.Some n ->
                                  mk_float
                                    (Prims.strcat (Prims.string_of_int n)
                                       ".0E0")
                              | FStar_Pervasives_Native.None -> ER_Error))))
            else
              if target_type = "boolean"
              then
                (match v with
                 | ER_Num n -> ER_Bool (n <> Prims.int_zero)
                 | ER_Dec uu___4 ->
                     (match parse_to_scaled lex with
                      | FStar_Pervasives_Native.Some (sv, uu___5) ->
                          ER_Bool (sv <> Prims.int_zero)
                      | FStar_Pervasives_Native.None ->
                          (match parse_double_to_scaled lex with
                           | FStar_Pervasives_Native.Some (sv, uu___5) ->
                               ER_Bool (sv <> Prims.int_zero)
                           | FStar_Pervasives_Native.None -> ER_Error))
                 | ER_Dbl uu___4 ->
                     (match parse_to_scaled lex with
                      | FStar_Pervasives_Native.Some (sv, uu___5) ->
                          ER_Bool (sv <> Prims.int_zero)
                      | FStar_Pervasives_Native.None ->
                          (match parse_double_to_scaled lex with
                           | FStar_Pervasives_Native.Some (sv, uu___5) ->
                               ER_Bool (sv <> Prims.int_zero)
                           | FStar_Pervasives_Native.None -> ER_Error))
                 | ER_Bool b -> ER_Bool b
                 | uu___4 ->
                     if (lex = "true") || (lex = "1")
                     then ER_Bool true
                     else
                       if (lex = "false") || (lex = "0")
                       then ER_Bool false
                       else
                         (match parse_int_string lex with
                          | FStar_Pervasives_Native.Some n ->
                              ER_Bool (n <> Prims.int_zero)
                          | FStar_Pervasives_Native.None ->
                              (match parse_to_scaled lex with
                               | FStar_Pervasives_Native.Some (sv, uu___7) ->
                                   ER_Bool (sv <> Prims.int_zero)
                               | FStar_Pervasives_Native.None -> ER_Error)))
              else
                if target_type = "string"
                then
                  (match v with
                   | ER_Num uu___5 -> er_string lex
                   | ER_Dec uu___5 ->
                       (match parse_to_scaled lex with
                        | FStar_Pervasives_Native.Some (sv, sc) ->
                            let divisor = pow10 sc in
                            if
                              (divisor > Prims.int_zero) &&
                                (((mod) sv divisor) = Prims.int_zero)
                            then
                              er_string (Prims.string_of_int (sv / divisor))
                            else er_string lex
                        | FStar_Pervasives_Native.None -> er_string lex)
                   | ER_Dbl uu___5 ->
                       (match parse_double_to_scaled lex with
                        | FStar_Pervasives_Native.Some (sv, sc) ->
                            let divisor = pow10 sc in
                            if
                              (divisor > Prims.int_zero) &&
                                (((mod) sv divisor) = Prims.int_zero)
                            then
                              er_string (Prims.string_of_int (sv / divisor))
                            else er_string lex
                        | FStar_Pervasives_Native.None -> er_string lex)
                   | uu___5 -> er_string lex)
                else
                  if
                    ((RDF_Term.is_iri full_iri) &&
                       (full_iri <> RDF_Term.rdf_lang_string))
                      && (full_iri <> RDF_Term.rdf_dir_lang_string)
                  then
                    ER_Term
                      (RDF_Term.T_Literal
                         {
                           RDF_Term.lexical_form = lex;
                           RDF_Term.datatype = full_iri;
                           RDF_Term.lang_tag = FStar_Pervasives_Native.None;
                           RDF_Term.direction = FStar_Pervasives_Native.None
                         })
                  else ER_Error
let er_to_geo_wkt (v : eval_result) :
  RDF_Geo_Types.geo_wkt_value FStar_Pervasives_Native.option=
  match er_string_info v with
  | FStar_Pervasives_Native.Some (s, uu___, dt) ->
      if dt = RDF_Geo_Types.geo_wktLiteral
      then Parser_WKT.parse_wkt_literal s
      else FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
let geo_bool_result (b : Prims.bool FStar_Pervasives_Native.option) :
  eval_result=
  match b with
  | FStar_Pervasives_Native.Some bb -> ER_Bool bb
  | FStar_Pervasives_Native.None -> ER_Error
let geo_double_result (v : RDF_Geo_Types.geo_scaled) : eval_result=
  ER_Term
    (RDF_Term.T_Literal
       {
         RDF_Term.lexical_form = (RDF_Geo_Types.gs_to_string v);
         RDF_Term.datatype = RDF_Term.xsd_double;
         RDF_Term.lang_tag = FStar_Pervasives_Native.None;
         RDF_Term.direction = FStar_Pervasives_Native.None
       })
let geo_wkt_result (v : RDF_Geo_Types.geo_wkt_value) : eval_result=
  ER_Term
    (RDF_Term.T_Literal
       {
         RDF_Term.lexical_form = (Parser_WKT.serialize_wkt_value v);
         RDF_Term.datatype = RDF_Geo_Types.geo_wktLiteral;
         RDF_Term.lang_tag = FStar_Pervasives_Native.None;
         RDF_Term.direction = FStar_Pervasives_Native.None
       })
let eval_geof_predicate (name : Prims.string)
  (a : RDF_Geo_Types.geo_wkt_value) (b : RDF_Geo_Types.geo_wkt_value) :
  eval_result FStar_Pervasives_Native.option=
  let go f = geo_bool_result (RDF_Geo_Topology.geo_wkt_predicate f a b) in
  if name = "sfEquals"
  then FStar_Pervasives_Native.Some (go RDF_Geo_Topology.sf_equals)
  else
    if name = "sfDisjoint"
    then FStar_Pervasives_Native.Some (go RDF_Geo_Topology.sf_disjoint)
    else
      if name = "sfIntersects"
      then FStar_Pervasives_Native.Some (go RDF_Geo_Topology.sf_intersects)
      else
        if name = "sfTouches"
        then FStar_Pervasives_Native.Some (go RDF_Geo_Topology.sf_touches)
        else
          if name = "sfWithin"
          then FStar_Pervasives_Native.Some (go RDF_Geo_Topology.sf_within)
          else
            if name = "sfContains"
            then
              FStar_Pervasives_Native.Some (go RDF_Geo_Topology.sf_contains)
            else
              if name = "sfOverlaps"
              then
                FStar_Pervasives_Native.Some
                  (go RDF_Geo_Topology.sf_overlaps)
              else
                if name = "sfCrosses"
                then
                  FStar_Pervasives_Native.Some
                    (go RDF_Geo_Topology.sf_crosses)
                else FStar_Pervasives_Native.None
let eval_geof_call (iri_s : Prims.string) (arg_vals : eval_result Prims.list)
  : eval_result=
  let ns_len = FStar_String.strlen RDF_Geo_Types.geof_ns in
  if
    Prims.op_Negation
      (((FStar_String.strlen iri_s) > ns_len) &&
         ((FStar_String.sub iri_s Prims.int_zero ns_len) =
            RDF_Geo_Types.geof_ns))
  then ER_Error
  else
    (let name =
       FStar_String.sub iri_s ns_len ((FStar_String.strlen iri_s) - ns_len) in
     match arg_vals with
     | a::b::[] ->
         (match ((er_to_geo_wkt a), (er_to_geo_wkt b)) with
          | (FStar_Pervasives_Native.Some wa, FStar_Pervasives_Native.Some
             wb) ->
              (match eval_geof_predicate name wa wb with
               | FStar_Pervasives_Native.Some r -> r
               | FStar_Pervasives_Native.None ->
                   if name = "distance"
                   then
                     (if
                        RDF_Geo_Topology.geo_crs_compatible
                          wa.RDF_Geo_Types.gw_crs wb.RDF_Geo_Types.gw_crs
                      then
                        match RDF_Geo_Functions.geo_distance
                                wa.RDF_Geo_Types.gw_geom
                                wb.RDF_Geo_Types.gw_geom
                        with
                        | FStar_Pervasives_Native.Some d ->
                            geo_double_result d
                        | FStar_Pervasives_Native.None -> ER_Error
                      else ER_Error)
                   else ER_Error)
          | (uu___1, uu___2) -> ER_Error)
     | a::[] ->
         if name = "envelope"
         then
           (match er_to_geo_wkt a with
            | FStar_Pervasives_Native.Some wa ->
                (match RDF_Geo_Functions.geo_envelope
                         wa.RDF_Geo_Types.gw_geom
                 with
                 | FStar_Pervasives_Native.Some env ->
                     geo_wkt_result
                       {
                         RDF_Geo_Types.gw_crs = (wa.RDF_Geo_Types.gw_crs);
                         RDF_Geo_Types.gw_geom = env
                       }
                 | FStar_Pervasives_Native.None -> ER_Error)
            | FStar_Pervasives_Native.None -> ER_Error)
         else ER_Error
     | uu___1 -> ER_Error)
(* Extension-function registry -- issue #463 (SPARQL 1.1 s17.6).
   Global table of host-supplied closures keyed by absolute function
   IRI. Populated by the npm-entry JS bridge (Comunica-style
   extensionFunctions) or by native registrants (unit tests, future
   CLI plug-ins). All dispatch DECISIONS live in F*: the E_FunctionCall
   arm consults this hook last and maps None to ER_Error, the
   spec-required unsupported-function error. The closure type uses
   stdlib option for registrant ergonomics; conversion to the
   extracted FStar_Pervasives_Native.option happens here. *)
let extension_function_table : (string, eval_result list -> eval_result option) Hashtbl.t =
  Hashtbl.create 16
let extension_function_register (iri : string) (f : eval_result list -> eval_result option) : unit =
  Hashtbl.replace extension_function_table iri f
let extension_function_unregister (iri : string) : unit =
  Hashtbl.remove extension_function_table iri
let extension_function_clear () : unit =
  Hashtbl.clear extension_function_table
let extension_function_call (iri : Prims.string) (args : eval_result Prims.list)
  : eval_result FStar_Pervasives_Native.option =
  match Hashtbl.find_opt extension_function_table iri with
  | None -> FStar_Pervasives_Native.None
  | Some f ->
    (match f args with
     | Some r -> FStar_Pervasives_Native.Some r
     | None -> FStar_Pervasives_Native.None)
let rec eval_expr_with_base
  (base : RDF_Term.wf_iri FStar_Pervasives_Native.option) (e : expr)
  (mu : RDF_Graph_Executable.solution_mapping) : eval_result=
  match e with
  | E_Var v ->
      (match sm_lookup v mu with
       | FStar_Pervasives_Native.Some (RDF_Term.T_Literal l) ->
           if (lit_datatype l) = RDF_Term.xsd_integer
           then
             (match parse_int_string (lit_lexical l) with
              | FStar_Pervasives_Native.Some n -> ER_Num n
              | FStar_Pervasives_Native.None ->
                  ER_Term (RDF_Term.T_Literal l))
           else
             if (lit_datatype l) = RDF_Term.xsd_decimal
             then ER_Dec (lit_lexical l)
             else
               if
                 ((lit_datatype l) = RDF_Term.xsd_double) ||
                   ((lit_datatype l) = xsd_float)
               then ER_Dbl (lit_lexical l)
               else
                 if (lit_datatype l) = RDF_Term.xsd_boolean
                 then
                   ER_Bool
                     (((lit_lexical l) = "true") || ((lit_lexical l) = "1"))
                 else ER_Term (RDF_Term.T_Literal l)
       | FStar_Pervasives_Native.Some t -> ER_Term t
       | FStar_Pervasives_Native.None -> ER_Error)
  | E_IRI i -> ER_Term (RDF_Term.T_IRI i)
  | E_Literal l -> ER_Term (RDF_Term.T_Literal l)
  | E_BoolLit b -> ER_Bool b
  | E_NumericLit n -> ER_Num n
  | E_DecimalLit s -> ER_Dec s
  | E_DoubleLit s -> ER_Dbl s
  | E_Arith (op, e1, e2) ->
      let v1 = eval_expr_with_base base e1 mu in
      let v2 = eval_expr_with_base base e2 mu in
      (match (v1, v2) with
       | (ER_Num a, ER_Num b) -> eval_arith_int op a b
       | uu___ ->
           (match ((er_to_numeric v1), (er_to_numeric v2)) with
            | (FStar_Pervasives_Native.Some (a, sa, ka),
               FStar_Pervasives_Native.Some (b, sb, kb)) ->
                let result_kind = promote_kind ka kb in
                let result_kind1 =
                  if (uu___is_Div op) && (uu___is_NK_Int result_kind)
                  then NK_Dec
                  else result_kind in
                (match op with
                 | Add ->
                     let uu___1 = add_scaled a sa b sb in
                     (match uu___1 with
                      | (rv, rs) -> format_numeric_result rv rs result_kind1)
                 | Sub ->
                     let uu___1 =
                       if sa >= sb
                       then (a, (b * (pow10 (sa - sb))))
                       else ((a * (pow10 (sb - sa))), b) in
                     (match uu___1 with
                      | (ra, rb) ->
                          let rs = if sa >= sb then sa else sb in
                          format_numeric_result (ra - rb) rs result_kind1)
                 | Mul ->
                     let rv = a * b in
                     let rs = sa + sb in
                     format_numeric_result rv rs result_kind1
                 | Div ->
                     if b = Prims.int_zero
                     then ER_Error
                     else
                       (let extra = (Prims.of_int (10)) in
                        let extended = a * (pow10 (sb + extra)) in
                        let divisor = b * (pow10 sa) in
                        if divisor = Prims.int_zero
                        then ER_Error
                        else
                          format_numeric_result (extended / divisor) extra
                            result_kind1))
            | (uu___1, uu___2) -> ER_Error))
  | E_UnaryMinus e1 ->
      (match eval_expr_with_base base e1 mu with
       | ER_Num n -> ER_Num (Prims.int_zero - n)
       | ER_Dec s ->
           if
             (string_starts_with s "-") &&
               ((FStar_String.strlen s) > Prims.int_one)
           then
             ER_Dec
               (FStar_String.sub s Prims.int_one
                  ((FStar_String.strlen s) - Prims.int_one))
           else
             if string_starts_with s "-"
             then ER_Dec "0"
             else ER_Dec (FStar_String.concat "" ["-"; s])
       | ER_Dbl s ->
           if
             (string_starts_with s "-") &&
               ((FStar_String.strlen s) > Prims.int_one)
           then
             ER_Dbl
               (FStar_String.sub s Prims.int_one
                  ((FStar_String.strlen s) - Prims.int_one))
           else
             if string_starts_with s "-"
             then ER_Dbl "0"
             else ER_Dbl (FStar_String.concat "" ["-"; s])
       | uu___ -> ER_Error)
  | E_UnaryPlus e1 -> eval_expr_with_base base e1 mu
  | E_Compare (op, e1, e2) ->
      (match value_compare (eval_expr_with_base base e1 mu)
               (eval_expr_with_base base e2 mu) op
       with
       | FStar_Pervasives_Native.Some b -> ER_Bool b
       | FStar_Pervasives_Native.None -> ER_Error)
  | E_And (e1, e2) ->
      (match bool_and_checked (ebv_checked (eval_expr_with_base base e1 mu))
               (ebv_checked (eval_expr_with_base base e2 mu))
       with
       | FStar_Pervasives_Native.Some b -> ER_Bool b
       | FStar_Pervasives_Native.None -> ER_Error)
  | E_Or (e1, e2) ->
      (match bool_or_checked (ebv_checked (eval_expr_with_base base e1 mu))
               (ebv_checked (eval_expr_with_base base e2 mu))
       with
       | FStar_Pervasives_Native.Some b -> ER_Bool b
       | FStar_Pervasives_Native.None -> ER_Error)
  | E_Not e1 ->
      (match bool_not_checked (ebv_checked (eval_expr_with_base base e1 mu))
       with
       | FStar_Pervasives_Native.Some b -> ER_Bool b
       | FStar_Pervasives_Native.None -> ER_Error)
  | E_IsIRI e1 -> fn_isIRI (eval_expr_with_base base e1 mu)
  | E_IsBlank e1 -> fn_isBlank (eval_expr_with_base base e1 mu)
  | E_IsLiteral e1 -> fn_isLiteral (eval_expr_with_base base e1 mu)
  | E_IsNumeric e1 -> fn_isNumeric (eval_expr_with_base base e1 mu)
  | E_Str e1 -> fn_str (eval_expr_with_base base e1 mu)
  | E_Lang e1 -> fn_lang (eval_expr_with_base base e1 mu)
  | E_Datatype e1 -> fn_datatype (eval_expr_with_base base e1 mu)
  | E_HasLang e1 -> fn_haslang (eval_expr_with_base base e1 mu)
  | E_HasLangDir e1 -> fn_haslangdir (eval_expr_with_base base e1 mu)
  | E_LangDir e1 -> fn_langdir (eval_expr_with_base base e1 mu)
  | E_IRI_fn e1 ->
      (match eval_expr_with_base base e1 mu with
       | ER_Term (RDF_Term.T_IRI i) -> ER_Term (RDF_Term.T_IRI i)
       | ER_Term (RDF_Term.T_Literal l) ->
           let s = lit_lexical l in
           (match base with
            | FStar_Pervasives_Native.Some b ->
                ER_Term (RDF_Term.T_IRI (resolve_iri b s))
            | FStar_Pervasives_Native.None ->
                (match string_to_iri s with
                 | FStar_Pervasives_Native.Some i ->
                     ER_Term (RDF_Term.T_IRI i)
                 | FStar_Pervasives_Native.None -> ER_Error))
       | uu___ -> ER_Error)
  | E_StrDt (e1, e2) ->
      (match ((er_to_string (eval_expr_with_base base e1 mu)),
               (eval_expr_with_base base e2 mu))
       with
       | (FStar_Pervasives_Native.Some s, ER_Term (RDF_Term.T_IRI dt)) ->
           ER_Term (fn_strdt s dt)
       | (uu___, uu___1) -> ER_Error)
  | E_StrLang (e1, e2) ->
      let v1 = eval_expr_with_base base e1 mu in
      (match (v1, (er_to_string (eval_expr_with_base base e2 mu))) with
       | (ER_Term (RDF_Term.T_Literal l), FStar_Pervasives_Native.Some lang)
           ->
           if
             (((lit_datatype l) = RDF_Term.xsd_string) ||
                ((lit_datatype l) = ""))
               && (l.RDF_Term.lang_tag = FStar_Pervasives_Native.None)
           then ER_Term (fn_strlang (lit_lexical l) lang)
           else ER_Error
       | (uu___, uu___1) -> ER_Error)
  | E_StrLangDir (e1, e2, e3) ->
      let v1 = eval_expr_with_base base e1 mu in
      (match (v1, (er_to_string (eval_expr_with_base base e2 mu)),
               (er_to_string (eval_expr_with_base base e3 mu)))
       with
       | (ER_Term (RDF_Term.T_Literal l), FStar_Pervasives_Native.Some lang,
          FStar_Pervasives_Native.Some dirstr) ->
           if
             ((((lit_datatype l) = RDF_Term.xsd_string) ||
                 ((lit_datatype l) = ""))
                && (l.RDF_Term.lang_tag = FStar_Pervasives_Native.None))
               && ((FStar_String.strlen lang) > Prims.int_zero)
           then
             (match parse_text_direction dirstr with
              | FStar_Pervasives_Native.Some d ->
                  ER_Term (fn_strlangdir (lit_lexical l) lang d)
              | FStar_Pervasives_Native.None -> ER_Error)
           else ER_Error
       | (uu___, uu___1, uu___2) -> ER_Error)
  | E_Bound v ->
      ER_Bool (FStar_Pervasives_Native.uu___is_Some (sm_lookup v mu))
  | E_If (cond, then_e, else_e) ->
      if ebv (eval_expr_with_base base cond mu)
      then eval_expr_with_base base then_e mu
      else eval_expr_with_base base else_e mu
  | E_Coalesce es -> eval_coalesce_with_base base es mu
  | E_In (ev, es) ->
      let v = eval_expr_with_base base ev mu in
      eval_in_with_base base v es mu
  | E_NotIn (ev, es) ->
      let v = eval_expr_with_base base ev mu in
      (match eval_in_with_base base v es mu with
       | ER_Bool b -> ER_Bool (Prims.op_Negation b)
       | other -> other)
  | E_StrLen e1 ->
      (match er_to_string (eval_expr_with_base base e1 mu) with
       | FStar_Pervasives_Native.Some s -> ER_Num (string_length s)
       | FStar_Pervasives_Native.None -> ER_Error)
  | E_Substr (e1, e2, e3_opt) ->
      let v1 = eval_expr_with_base base e1 mu in
      (match ((er_string_info v1), (eval_expr_with_base base e2 mu)) with
       | (FStar_Pervasives_Native.Some (s, lang, dt), ER_Num start) ->
           if start < Prims.int_zero
           then ER_Error
           else
             (let len_opt =
                match e3_opt with
                | FStar_Pervasives_Native.Some e3 ->
                    (match eval_expr_with_base base e3 mu with
                     | ER_Num n ->
                         if n >= Prims.int_zero
                         then FStar_Pervasives_Native.Some n
                         else FStar_Pervasives_Native.None
                     | uu___1 -> FStar_Pervasives_Native.None)
                | FStar_Pervasives_Native.None ->
                    FStar_Pervasives_Native.None in
              er_string_preserve (fn_substr_spec s start len_opt) lang dt)
       | (uu___, uu___1) -> ER_Error)
  | E_UCase e1 ->
      let v1 = eval_expr_with_base base e1 mu in
      (match er_string_info v1 with
       | FStar_Pervasives_Native.Some (s, lang, dt) ->
           er_string_preserve (string_upper s) lang dt
       | FStar_Pervasives_Native.None -> ER_Error)
  | E_LCase e1 ->
      let v1 = eval_expr_with_base base e1 mu in
      (match er_string_info v1 with
       | FStar_Pervasives_Native.Some (s, lang, dt) ->
           er_string_preserve (string_lower s) lang dt
       | FStar_Pervasives_Native.None -> ER_Error)
  | E_StrStarts (e1, e2) ->
      (match ((er_to_string (eval_expr_with_base base e1 mu)),
               (er_to_string (eval_expr_with_base base e2 mu)))
       with
       | (FStar_Pervasives_Native.Some s, FStar_Pervasives_Native.Some
          prefix) -> ER_Bool (string_starts_with s prefix)
       | (uu___, uu___1) -> ER_Error)
  | E_StrEnds (e1, e2) ->
      (match ((er_to_string (eval_expr_with_base base e1 mu)),
               (er_to_string (eval_expr_with_base base e2 mu)))
       with
       | (FStar_Pervasives_Native.Some s, FStar_Pervasives_Native.Some
          suffix) -> ER_Bool (string_ends_with s suffix)
       | (uu___, uu___1) -> ER_Error)
  | E_Contains (e1, e2) ->
      (match ((er_to_string (eval_expr_with_base base e1 mu)),
               (er_to_string (eval_expr_with_base base e2 mu)))
       with
       | (FStar_Pervasives_Native.Some s, FStar_Pervasives_Native.Some sub)
           -> ER_Bool (string_contains s sub)
       | (uu___, uu___1) -> ER_Error)
  | E_StrBefore (e1, e2) ->
      let v1 = eval_expr_with_base base e1 mu in
      let v2 = eval_expr_with_base base e2 mu in
      (match ((er_string_info v1), (er_string_info v2)) with
       | (FStar_Pervasives_Native.Some (s, lang1, dt1),
          FStar_Pervasives_Native.Some (arg, lang2, dt2)) ->
           let compatible =
             (((((FStar_Pervasives_Native.uu___is_None lang1) &&
                   (FStar_Pervasives_Native.uu___is_None lang2))
                  ||
                  ((((FStar_Pervasives_Native.uu___is_None lang1) &&
                       (dt1 = RDF_Term.xsd_string))
                      && (FStar_Pervasives_Native.uu___is_None lang2))
                     && (dt2 = RDF_Term.xsd_string)))
                 ||
                 (((FStar_Pervasives_Native.uu___is_Some lang1) &&
                     (FStar_Pervasives_Native.uu___is_None lang2))
                    &&
                    ((dt2 = RDF_Term.xsd_string) || (dt2 = rdf_langString))))
                ||
                (((FStar_Pervasives_Native.uu___is_None lang1) &&
                    (dt1 = RDF_Term.xsd_string))
                   && (FStar_Pervasives_Native.uu___is_Some lang2)))
               ||
               (((FStar_Pervasives_Native.uu___is_Some lang1) &&
                   (FStar_Pervasives_Native.uu___is_Some lang2))
                  && (lang1 = lang2)) in
           if Prims.op_Negation compatible
           then ER_Error
           else
             if (FStar_String.strlen arg) = Prims.int_zero
             then er_string_preserve "" lang1 dt1
             else
               (let result = string_before s arg in
                if
                  ((FStar_String.strlen result) = Prims.int_zero) &&
                    (Prims.op_Negation (string_contains s arg))
                then er_string ""
                else er_string_preserve result lang1 dt1)
       | (uu___, uu___1) -> ER_Error)
  | E_StrAfter (e1, e2) ->
      let v1 = eval_expr_with_base base e1 mu in
      let v2 = eval_expr_with_base base e2 mu in
      (match ((er_string_info v1), (er_string_info v2)) with
       | (FStar_Pervasives_Native.Some (s, lang1, dt1),
          FStar_Pervasives_Native.Some (arg, lang2, dt2)) ->
           let compatible =
             (((((FStar_Pervasives_Native.uu___is_None lang1) &&
                   (FStar_Pervasives_Native.uu___is_None lang2))
                  ||
                  ((((FStar_Pervasives_Native.uu___is_None lang1) &&
                       (dt1 = RDF_Term.xsd_string))
                      && (FStar_Pervasives_Native.uu___is_None lang2))
                     && (dt2 = RDF_Term.xsd_string)))
                 ||
                 (((FStar_Pervasives_Native.uu___is_Some lang1) &&
                     (FStar_Pervasives_Native.uu___is_None lang2))
                    &&
                    ((dt2 = RDF_Term.xsd_string) || (dt2 = rdf_langString))))
                ||
                (((FStar_Pervasives_Native.uu___is_None lang1) &&
                    (dt1 = RDF_Term.xsd_string))
                   && (FStar_Pervasives_Native.uu___is_Some lang2)))
               ||
               (((FStar_Pervasives_Native.uu___is_Some lang1) &&
                   (FStar_Pervasives_Native.uu___is_Some lang2))
                  && (lang1 = lang2)) in
           if Prims.op_Negation compatible
           then ER_Error
           else
             if (FStar_String.strlen arg) = Prims.int_zero
             then er_string_preserve s lang1 dt1
             else
               (let result = string_after s arg in
                if
                  ((FStar_String.strlen result) = Prims.int_zero) &&
                    (Prims.op_Negation (string_contains s arg))
                then er_string ""
                else er_string_preserve result lang1 dt1)
       | (uu___, uu___1) -> ER_Error)
  | E_Concat es -> eval_concat_with_base base es mu
  | E_EncodeForUri e1 ->
      (match er_to_string (eval_expr_with_base base e1 mu) with
       | FStar_Pervasives_Native.Some s -> er_string (string_encode_uri s)
       | FStar_Pervasives_Native.None -> ER_Error)
  | E_Replace (e1, e2, e3, e4_opt) ->
      let v1 = eval_expr_with_base base e1 mu in
      (match ((er_string_info v1),
               (er_to_string (eval_expr_with_base base e2 mu)),
               (er_to_string (eval_expr_with_base base e3 mu)))
       with
       | (FStar_Pervasives_Native.Some (s, lang, dt),
          FStar_Pervasives_Native.Some pat, FStar_Pervasives_Native.Some rep)
           ->
           let flags =
             match e4_opt with
             | FStar_Pervasives_Native.Some e4 ->
                 er_to_string (eval_expr_with_base base e4 mu)
             | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None in
           er_string_preserve (string_replace s pat rep flags) lang dt
       | (uu___, uu___1, uu___2) -> ER_Error)
  | E_Regex (e1, e2, e3_opt) ->
      (match ((er_to_string (eval_expr_with_base base e1 mu)),
               (er_to_string (eval_expr_with_base base e2 mu)))
       with
       | (FStar_Pervasives_Native.Some s, FStar_Pervasives_Native.Some pat)
           ->
           let flags =
             match e3_opt with
             | FStar_Pervasives_Native.Some e3 ->
                 er_to_string (eval_expr_with_base base e3 mu)
             | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None in
           ER_Bool (fn_regex_spec s pat flags)
       | (uu___, uu___1) -> ER_Error)
  | E_Abs e1 ->
      (match eval_expr_with_base base e1 mu with
       | ER_Num n -> ER_Num (int_abs n)
       | ER_Dec s ->
           if
             ((FStar_String.strlen s) > Prims.int_zero) &&
               ((FStar_String.index s Prims.int_zero) =
                  (FStar_Char.char_of_int (Prims.of_int (45))))
           then
             ER_Dec
               (FStar_String.sub s Prims.int_one
                  ((FStar_String.strlen s) - Prims.int_one))
           else ER_Dec s
       | ER_Dbl s ->
           if
             ((FStar_String.strlen s) > Prims.int_zero) &&
               ((FStar_String.index s Prims.int_zero) =
                  (FStar_Char.char_of_int (Prims.of_int (45))))
           then
             ER_Dbl
               (FStar_String.sub s Prims.int_one
                  ((FStar_String.strlen s) - Prims.int_one))
           else ER_Dbl s
       | uu___ -> ER_Error)
  | E_Round e1 ->
      (match eval_expr_with_base base e1 mu with
       | ER_Num n -> ER_Num n
       | ER_Dec s -> ER_Dec (Prims.string_of_int (int_round s))
       | ER_Dbl s -> ER_Dbl (Prims.string_of_int (int_round s))
       | uu___ -> ER_Error)
  | E_Ceil e1 ->
      (match eval_expr_with_base base e1 mu with
       | ER_Num n -> ER_Num n
       | ER_Dec s -> ER_Dec (Prims.string_of_int (int_ceil s))
       | ER_Dbl s -> ER_Dbl (Prims.string_of_int (int_ceil s))
       | uu___ -> ER_Error)
  | E_Floor e1 ->
      (match eval_expr_with_base base e1 mu with
       | ER_Num n -> ER_Num n
       | ER_Dec s -> ER_Dec (Prims.string_of_int (int_floor s))
       | ER_Dbl s -> ER_Dbl (Prims.string_of_int (int_floor s))
       | uu___ -> ER_Error)
  | E_MD5 e1 ->
      (match er_to_string (eval_expr_with_base base e1 mu) with
       | FStar_Pervasives_Native.Some s -> er_string (hash_md5 s)
       | FStar_Pervasives_Native.None -> ER_Error)
  | E_SHA1 e1 ->
      (match er_to_string (eval_expr_with_base base e1 mu) with
       | FStar_Pervasives_Native.Some s -> er_string (hash_sha1 s)
       | FStar_Pervasives_Native.None -> ER_Error)
  | E_SHA256 e1 ->
      (match er_to_string (eval_expr_with_base base e1 mu) with
       | FStar_Pervasives_Native.Some s -> er_string (hash_sha256 s)
       | FStar_Pervasives_Native.None -> ER_Error)
  | E_SHA384 e1 ->
      (match er_to_string (eval_expr_with_base base e1 mu) with
       | FStar_Pervasives_Native.Some s -> er_string (hash_sha384 s)
       | FStar_Pervasives_Native.None -> ER_Error)
  | E_SHA512 e1 ->
      (match er_to_string (eval_expr_with_base base e1 mu) with
       | FStar_Pervasives_Native.Some s -> er_string (hash_sha512 s)
       | FStar_Pervasives_Native.None -> ER_Error)
  | E_Now ->
      ER_Term
        (RDF_Term.T_Literal
           {
             RDF_Term.lexical_form = (fx_current_datetime ());
             RDF_Term.datatype = xsd_dateTime;
             RDF_Term.lang_tag = FStar_Pervasives_Native.None;
             RDF_Term.direction = FStar_Pervasives_Native.None
           })
  | E_Year e1 ->
      (match er_to_datetime_lex (eval_expr_with_base base e1 mu) with
       | FStar_Pervasives_Native.Some s ->
           (match dt_year s with
            | FStar_Pervasives_Native.Some n -> ER_Num n
            | FStar_Pervasives_Native.None -> ER_Error)
       | FStar_Pervasives_Native.None -> ER_Error)
  | E_Month e1 ->
      (match er_to_datetime_lex (eval_expr_with_base base e1 mu) with
       | FStar_Pervasives_Native.Some s ->
           (match dt_month s with
            | FStar_Pervasives_Native.Some n -> ER_Num n
            | FStar_Pervasives_Native.None -> ER_Error)
       | FStar_Pervasives_Native.None -> ER_Error)
  | E_Day e1 ->
      (match er_to_datetime_lex (eval_expr_with_base base e1 mu) with
       | FStar_Pervasives_Native.Some s ->
           (match dt_day s with
            | FStar_Pervasives_Native.Some n -> ER_Num n
            | FStar_Pervasives_Native.None -> ER_Error)
       | FStar_Pervasives_Native.None -> ER_Error)
  | E_Hours e1 ->
      (match er_to_datetime_lex (eval_expr_with_base base e1 mu) with
       | FStar_Pervasives_Native.Some s ->
           (match dt_hours s with
            | FStar_Pervasives_Native.Some n -> ER_Num n
            | FStar_Pervasives_Native.None -> ER_Error)
       | FStar_Pervasives_Native.None -> ER_Error)
  | E_Minutes e1 ->
      (match er_to_datetime_lex (eval_expr_with_base base e1 mu) with
       | FStar_Pervasives_Native.Some s ->
           (match dt_minutes s with
            | FStar_Pervasives_Native.Some n -> ER_Num n
            | FStar_Pervasives_Native.None -> ER_Error)
       | FStar_Pervasives_Native.None -> ER_Error)
  | E_Seconds e1 ->
      (match er_to_datetime_lex (eval_expr_with_base base e1 mu) with
       | FStar_Pervasives_Native.Some s ->
           (match dt_seconds s with
            | FStar_Pervasives_Native.Some ds -> ER_Dec ds
            | FStar_Pervasives_Native.None -> ER_Error)
       | FStar_Pervasives_Native.None -> ER_Error)
  | E_Timezone e1 ->
      (match er_to_datetime_lex (eval_expr_with_base base e1 mu) with
       | FStar_Pervasives_Native.Some s ->
           (match dt_timezone s with
            | FStar_Pervasives_Native.Some "" -> ER_Error
            | FStar_Pervasives_Native.Some tz ->
                ER_Term
                  (RDF_Term.T_Literal
                     {
                       RDF_Term.lexical_form = tz;
                       RDF_Term.datatype = xsd_dayTimeDuration;
                       RDF_Term.lang_tag = FStar_Pervasives_Native.None;
                       RDF_Term.direction = FStar_Pervasives_Native.None
                     })
            | FStar_Pervasives_Native.None -> ER_Error)
       | FStar_Pervasives_Native.None -> ER_Error)
  | E_Tz e1 ->
      (match er_to_datetime_lex (eval_expr_with_base base e1 mu) with
       | FStar_Pervasives_Native.Some s ->
           (match dt_tz s with
            | FStar_Pervasives_Native.Some tz -> er_string tz
            | FStar_Pervasives_Native.None -> ER_Error)
       | FStar_Pervasives_Native.None -> ER_Error)
  | E_SameTerm (e1, e2) ->
      (match ((eval_expr_with_base base e1 mu),
               (eval_expr_with_base base e2 mu))
       with
       | (ER_Term t1, ER_Term t2) -> ER_Bool (same_term t1 t2)
       | (ER_Num a, ER_Num b) -> ER_Bool (a = b)
       | (ER_Dec a, ER_Dec b) -> ER_Bool (a = b)
       | (ER_Dbl a, ER_Dbl b) -> ER_Bool (a = b)
       | (ER_Bool a, ER_Bool b) -> ER_Bool (a = b)
       | (uu___, uu___1) -> ER_Bool false)
  | E_Exists uu___ -> ER_Error
  | E_NotExists uu___ -> ER_Error
  | E_TripleTerm (es, ep, eo) ->
      (match ((er_to_term (eval_expr_with_base base es mu)),
               (er_to_term (eval_expr_with_base base ep mu)),
               (er_to_term (eval_expr_with_base base eo mu)))
       with
       | (FStar_Pervasives_Native.Some sterm, FStar_Pervasives_Native.Some
          (RDF_Term.T_IRI p), FStar_Pervasives_Native.Some oterm) ->
           (match term_to_subject_opt sterm with
            | FStar_Pervasives_Native.Some ssub ->
                ER_Term (RDF_Term.T_TripleTerm (ssub, p, oterm))
            | FStar_Pervasives_Native.None -> ER_Error)
       | (uu___, uu___1, uu___2) -> ER_Error)
  | E_TTSubject e1 ->
      (match eval_expr_with_base base e1 mu with
       | ER_Term (RDF_Term.T_TripleTerm (s, uu___, uu___1)) ->
           ER_Term (subject_to_term s)
       | uu___ -> ER_Error)
  | E_TTPredicate e1 ->
      (match eval_expr_with_base base e1 mu with
       | ER_Term (RDF_Term.T_TripleTerm (uu___, p, uu___1)) ->
           ER_Term (RDF_Term.T_IRI p)
       | uu___ -> ER_Error)
  | E_TTObject e1 ->
      (match eval_expr_with_base base e1 mu with
       | ER_Term (RDF_Term.T_TripleTerm (uu___, uu___1, o)) -> ER_Term o
       | uu___ -> ER_Error)
  | E_IsTriple e1 ->
      (match eval_expr_with_base base e1 mu with
       | ER_Error -> ER_Error
       | ER_Term (RDF_Term.T_TripleTerm (uu___, uu___1, uu___2)) ->
           ER_Bool true
       | uu___ -> ER_Bool false)
  | E_Aggregate (uu___, uu___1, uu___2) -> ER_Error
  | E_FunctionCall (iri, args) ->
      let iri_s = iri_to_string iri in
      if iri_s = "http://www.w3.org/2005/xpath-functions#langMatches"
      then
        (match args with
         | e1::e2::[] ->
             (match ((er_to_string (eval_expr_with_base base e1 mu)),
                      (er_to_string (eval_expr_with_base base e2 mu)))
              with
              | (FStar_Pervasives_Native.Some tag,
                 FStar_Pervasives_Native.Some range) ->
                  ER_Bool (fn_langMatches_spec tag range)
              | (uu___, uu___1) -> ER_Error)
         | uu___ -> ER_Error)
      else
        if iri_s = "http://www.w3.org/2005/xpath-functions#rand"
        then ER_Dbl "0.5"
        else
          if iri_s = "http://www.w3.org/2005/xpath-functions#uuid"
          then
            (let row =
               match fx_ctx_get fx_key_row mu with
               | FStar_Pervasives_Native.Some r -> r
               | FStar_Pervasives_Native.None -> "" in
             let occ =
               match fx_ctx_get fx_key_occ mu with
               | FStar_Pervasives_Native.Some o -> o
               | FStar_Pervasives_Native.None -> "" in
             let uuid_iri =
               Prims.strcat "urn:uuid:"
                 (fx_uuid_of_seed
                    (Prims.strcat "u|"
                       (Prims.strcat row (Prims.strcat "|" occ)))) in
             if RDF_Term.is_iri uuid_iri
             then ER_Term (RDF_Term.T_IRI uuid_iri)
             else ER_Error)
          else
            if iri_s = "http://www.w3.org/2005/xpath-functions#struuid"
            then
              (let row =
                 match fx_ctx_get fx_key_row mu with
                 | FStar_Pervasives_Native.Some r -> r
                 | FStar_Pervasives_Native.None -> "" in
               let occ =
                 match fx_ctx_get fx_key_occ mu with
                 | FStar_Pervasives_Native.Some o -> o
                 | FStar_Pervasives_Native.None -> "" in
               er_string
                 (fx_uuid_of_seed
                    (Prims.strcat "u|"
                       (Prims.strcat row (Prims.strcat "|" occ)))))
            else
              if iri_s = "http://www.w3.org/2005/xpath-functions#bnode"
              then
                (let row =
                   match fx_ctx_get fx_key_row mu with
                   | FStar_Pervasives_Native.Some r -> r
                   | FStar_Pervasives_Native.None -> "" in
                 match args with
                 | [] ->
                     let occ =
                       match fx_ctx_get fx_key_occ mu with
                       | FStar_Pervasives_Native.Some o -> o
                       | FStar_Pervasives_Native.None -> "" in
                     ER_Term
                       (RDF_Term.T_BNode
                          (fx_bnode_of_seed
                             (Prims.strcat "n|"
                                (Prims.strcat row (Prims.strcat "|" occ)))))
                 | e1::[] ->
                     (match er_to_string (eval_expr_with_base base e1 mu)
                      with
                      | FStar_Pervasives_Native.Some s ->
                          ER_Term
                            (RDF_Term.T_BNode
                               (fx_bnode_of_seed
                                  (Prims.strcat "s|"
                                     (Prims.strcat row (Prims.strcat "|" s)))))
                      | FStar_Pervasives_Native.None -> ER_Error)
                 | uu___4 -> ER_Error)
              else
                if
                  ((FStar_String.strlen iri_s) >
                     (FStar_String.strlen RDF_Geo_Types.geof_ns))
                    &&
                    ((FStar_String.sub iri_s Prims.int_zero
                        (FStar_String.strlen RDF_Geo_Types.geof_ns))
                       = RDF_Geo_Types.geof_ns)
                then
                  eval_geof_call iri_s
                    (eval_geof_args_with_base base args mu)
                else
                  (let xsd_ns = "http://www.w3.org/2001/XMLSchema#" in
                   if
                     ((FStar_String.strlen iri_s) >
                        (FStar_String.strlen xsd_ns))
                       &&
                       ((FStar_String.sub iri_s Prims.int_zero
                           (FStar_String.strlen xsd_ns))
                          = xsd_ns)
                   then
                     match args with
                     | e1::[] ->
                         let v = eval_expr_with_base base e1 mu in
                         let target_type =
                           FStar_String.sub iri_s
                             (FStar_String.strlen xsd_ns)
                             ((FStar_String.strlen iri_s) -
                                (FStar_String.strlen xsd_ns)) in
                         eval_xsd_cast v target_type iri_s
                     | uu___6 -> ER_Error
                   else
                     (match extension_function_call iri_s
                              (eval_geof_args_with_base base args mu)
                      with
                      | FStar_Pervasives_Native.Some r -> r
                      | FStar_Pervasives_Native.None -> ER_Error))
and eval_coalesce_with_base
  (base : RDF_Term.wf_iri FStar_Pervasives_Native.option)
  (es : expr Prims.list) (mu : RDF_Graph_Executable.solution_mapping) :
  eval_result=
  match es with
  | [] -> ER_Error
  | e::rest ->
      (match eval_expr_with_base base e mu with
       | ER_Error -> eval_coalesce_with_base base rest mu
       | v -> v)
and eval_geof_args_with_base
  (base : RDF_Term.wf_iri FStar_Pervasives_Native.option)
  (es : expr Prims.list) (mu : RDF_Graph_Executable.solution_mapping) :
  eval_result Prims.list=
  match es with
  | [] -> []
  | e::rest -> (eval_expr_with_base base e mu) ::
      (eval_geof_args_with_base base rest mu)
and eval_in_with_base (base : RDF_Term.wf_iri FStar_Pervasives_Native.option)
  (v : eval_result) (es : expr Prims.list)
  (mu : RDF_Graph_Executable.solution_mapping) : eval_result=
  match es with
  | [] -> ER_Bool false
  | e::rest ->
      (match value_compare v (eval_expr_with_base base e mu) CmpEq with
       | FStar_Pervasives_Native.Some true -> ER_Bool true
       | uu___ -> eval_in_with_base base v rest mu)
and eval_concat_with_base
  (base : RDF_Term.wf_iri FStar_Pervasives_Native.option)
  (es : expr Prims.list) (mu : RDF_Graph_Executable.solution_mapping) :
  eval_result=
  match es with
  | [] -> er_string ""
  | e::[] ->
      let v = eval_expr_with_base base e mu in
      (match er_string_info v with
       | FStar_Pervasives_Native.Some (s, lang, dt) ->
           (match (lang, (er_direction v)) with
            | (FStar_Pervasives_Native.Some l1, FStar_Pervasives_Native.Some
               d) ->
                ER_Term
                  (RDF_Term.T_Literal
                     {
                       RDF_Term.lexical_form = s;
                       RDF_Term.datatype = RDF_Term.rdf_dir_lang_string;
                       RDF_Term.lang_tag = (FStar_Pervasives_Native.Some l1);
                       RDF_Term.direction = (FStar_Pervasives_Native.Some d)
                     })
            | (uu___, uu___1) -> er_string_preserve s lang dt)
       | FStar_Pervasives_Native.None -> ER_Error)
  | e::rest ->
      let v = eval_expr_with_base base e mu in
      (match er_string_info v with
       | FStar_Pervasives_Native.Some (s, lang, dt) ->
           (match eval_concat_with_base base rest mu with
            | ER_Term (RDF_Term.T_Literal l) ->
                let combined = Prims.strcat s (lit_lexical l) in
                (match (lang, (l.RDF_Term.lang_tag)) with
                 | (FStar_Pervasives_Native.Some l1,
                    FStar_Pervasives_Native.Some l2) ->
                     if (string_lower l1) = (string_lower l2)
                     then
                       (match ((er_direction v), (l.RDF_Term.direction)) with
                        | (FStar_Pervasives_Native.Some d1,
                           FStar_Pervasives_Native.Some d2) ->
                            if d1 = d2
                            then
                              ER_Term
                                (RDF_Term.T_Literal
                                   {
                                     RDF_Term.lexical_form = combined;
                                     RDF_Term.datatype =
                                       RDF_Term.rdf_dir_lang_string;
                                     RDF_Term.lang_tag =
                                       (FStar_Pervasives_Native.Some l1);
                                     RDF_Term.direction =
                                       (FStar_Pervasives_Native.Some d1)
                                   })
                            else er_string combined
                        | (FStar_Pervasives_Native.None,
                           FStar_Pervasives_Native.None) ->
                            ER_Term
                              (RDF_Term.T_Literal
                                 {
                                   RDF_Term.lexical_form = combined;
                                   RDF_Term.datatype =
                                     RDF_Term.rdf_lang_string;
                                   RDF_Term.lang_tag =
                                     (FStar_Pervasives_Native.Some l1);
                                   RDF_Term.direction =
                                     FStar_Pervasives_Native.None
                                 })
                        | (uu___, uu___1) -> er_string combined)
                     else er_string combined
                 | (FStar_Pervasives_Native.None,
                    FStar_Pervasives_Native.None) ->
                     if dt = l.RDF_Term.datatype
                     then
                       ER_Term
                         (RDF_Term.T_Literal
                            {
                              RDF_Term.lexical_form = combined;
                              RDF_Term.datatype = dt;
                              RDF_Term.lang_tag =
                                FStar_Pervasives_Native.None;
                              RDF_Term.direction =
                                FStar_Pervasives_Native.None
                            })
                     else er_string combined
                 | (uu___, uu___1) -> er_string combined)
            | ER_Error -> ER_Error
            | uu___ -> ER_Error)
       | FStar_Pervasives_Native.None -> ER_Error)
let eval_expr_ebv (base : RDF_Term.wf_iri FStar_Pervasives_Native.option)
  (e : expr) (mu : RDF_Graph_Executable.solution_mapping) : Prims.bool=
  ebv (eval_expr_with_base base e mu)
let eval_expr_fwd (base : RDF_Term.wf_iri FStar_Pervasives_Native.option)
  (e : expr) (mu : RDF_Graph_Executable.solution_mapping) : eval_result=
  eval_expr_with_base base e mu
type path_result_fwd = (RDF_Term.rdf_term * RDF_Term.rdf_term) Prims.list
let eval_property_path_fwd_ref :
  (property_path ->
    RDF_Graph.rdf_graph -> path_result_fwd) Stdlib.ref=
  Stdlib.ref (fun _ _ -> [])
let eval_property_path_fwd (p : property_path)
  (g : RDF_Graph.rdf_graph) : path_result_fwd=
  !eval_property_path_fwd_ref p g
(* SERVICE endpoint resolver -- issue #57.
   Global table populated by the test runner from qt:serviceData
   manifest declarations. Lookup is keyed on the absolute IRI string
   of the endpoint. The value type is deliberately left unannotated:
   `graph_to_store g` below pins it to whatever module currently
   owns `rdf_graph` (RDF.Graph.Executable is being split into
   RDF.Term/RDF.Triple/RDF.Graph; the qualifier has already moved
   once) without this patch needing to track the split.

   2026-07-06: a static-table MISS falls back to
   `Service_wrap_hook.resolver` (virtual-sources design doc Stages 1-2,
   issue #57 family) before returning None -- see that file's banner
   and this patch's own header comment for why the fallback is a
   forward-ref hook cell rather than a direct call into the wrap+
   resolver module. *)
let service_endpoint_table = Hashtbl.create 16
let service_endpoint_register (iri : Prims.string) g : unit =
  Hashtbl.replace service_endpoint_table iri g
let service_endpoint_clear () : unit =
  Hashtbl.clear service_endpoint_table
let service_endpoint_lookup (iri : Prims.string) : graph_store FStar_Pervasives_Native.option=
  match Hashtbl.find_opt service_endpoint_table iri with
  | Some g -> FStar_Pervasives_Native.Some (graph_to_store g)
  | None ->
    (match !Service_wrap_hook.resolver iri with
     | Some g -> FStar_Pervasives_Native.Some (graph_to_store g)
     | None -> FStar_Pervasives_Native.None)
let path_result_to_solutions (ps : pattern_subject) (pt : pattern_term)
  (pairs : path_result_fwd) : solution_sequence=
  list_filter_map
    (fun pair ->
       let uu___ = pair in
       match uu___ with
       | (s, o) ->
           let mu_s =
             match ps with
             | PS_Var v -> FStar_Pervasives_Native.Some [(v, s)]
             | PS_IRI i ->
                 if RDF_Term.rdf_term_eq (RDF_Term.T_IRI i) s
                 then FStar_Pervasives_Native.Some []
                 else FStar_Pervasives_Native.None
             | PS_BNode b ->
                 if RDF_Term.rdf_term_eq (RDF_Term.T_BNode b) s
                 then FStar_Pervasives_Native.Some []
                 else FStar_Pervasives_Native.None
             | PS_TripleTerm (uu___1, uu___2, uu___3) ->
                 FStar_Pervasives_Native.None in
           (match mu_s with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some bindings_s ->
                let mu_o =
                  match pt with
                  | PT_Var v ->
                      (match FStar_List_Tot_Base.assoc v bindings_s with
                       | FStar_Pervasives_Native.Some existing ->
                           if RDF_Term.rdf_term_eq existing o
                           then FStar_Pervasives_Native.Some bindings_s
                           else FStar_Pervasives_Native.None
                       | FStar_Pervasives_Native.None ->
                           FStar_Pervasives_Native.Some ((v, o) ::
                             bindings_s))
                  | PT_IRI i ->
                      if RDF_Term.rdf_term_eq (RDF_Term.T_IRI i) o
                      then FStar_Pervasives_Native.Some bindings_s
                      else FStar_Pervasives_Native.None
                  | PT_BNode b ->
                      if RDF_Term.rdf_term_eq (RDF_Term.T_BNode b) o
                      then FStar_Pervasives_Native.Some bindings_s
                      else FStar_Pervasives_Native.None
                  | PT_Literal l ->
                      if RDF_Term.rdf_term_eq (RDF_Term.T_Literal l) o
                      then FStar_Pervasives_Native.Some bindings_s
                      else FStar_Pervasives_Native.None
                  | PT_TripleTerm (uu___1, uu___2, uu___3) ->
                      FStar_Pervasives_Native.None in
                mu_o)) pairs
let left_join (base : RDF_Term.wf_iri FStar_Pervasives_Native.option)
  (omega1 : solution_sequence) (omega2 : solution_sequence)
  (filter_expr : expr) : solution_sequence=
  match (omega1, omega2) with
  | ([], uu___) -> []
  | (uu___, []) -> omega1
  | (mu1_0::uu___, mu2_0::uu___1) ->
      let vars = vars_intersect (sm_domain mu1_0) (sm_domain mu2_0) in
      if vars = []
      then
        RDF_List_Helpers.concatMap_tr
          (fun mu1 ->
             let joins =
               list_filter_map
                 (fun mu2 ->
                    if sm_compatible mu1 mu2
                    then
                      let merged = sm_merge mu1 mu2 in
                      (if eval_expr_ebv base filter_expr merged
                       then FStar_Pervasives_Native.Some merged
                       else FStar_Pervasives_Native.None)
                    else FStar_Pervasives_Native.None) omega2 in
             if (FStar_List_Tot_Base.length joins) > Prims.int_zero
             then joins
             else [mu1]) omega1
      else
        (let idx = build_join_index vars omega2 in
         RDF_List_Helpers.concatMap_tr
           (fun mu1 ->
              let candidates = join_candidates idx vars mu1 in
              let joins =
                list_filter_map
                  (fun mu2 ->
                     if sm_compatible mu1 mu2
                     then
                       let merged = sm_merge mu1 mu2 in
                       (if eval_expr_ebv base filter_expr merged
                        then FStar_Pervasives_Native.Some merged
                        else FStar_Pervasives_Native.None)
                     else FStar_Pervasives_Native.None) candidates in
              if (FStar_List_Tot_Base.length joins) > Prims.int_zero
              then joins
              else [mu1]) omega1)
let rec expr_has_existential (e : expr) : Prims.bool=
  match e with
  | E_Exists uu___ -> true
  | E_NotExists uu___ -> true
  | E_Var uu___ -> false
  | E_IRI uu___ -> false
  | E_Literal uu___ -> false
  | E_BoolLit uu___ -> false
  | E_NumericLit uu___ -> false
  | E_DecimalLit uu___ -> false
  | E_DoubleLit uu___ -> false
  | E_Bound uu___ -> false
  | E_Now -> false
  | E_Arith (uu___, e1, e2) ->
      (expr_has_existential e1) || (expr_has_existential e2)
  | E_Compare (uu___, e1, e2) ->
      (expr_has_existential e1) || (expr_has_existential e2)
  | E_And (e1, e2) -> (expr_has_existential e1) || (expr_has_existential e2)
  | E_Or (e1, e2) -> (expr_has_existential e1) || (expr_has_existential e2)
  | E_StrDt (e1, e2) ->
      (expr_has_existential e1) || (expr_has_existential e2)
  | E_StrLang (e1, e2) ->
      (expr_has_existential e1) || (expr_has_existential e2)
  | E_StrStarts (e1, e2) ->
      (expr_has_existential e1) || (expr_has_existential e2)
  | E_StrEnds (e1, e2) ->
      (expr_has_existential e1) || (expr_has_existential e2)
  | E_Contains (e1, e2) ->
      (expr_has_existential e1) || (expr_has_existential e2)
  | E_StrBefore (e1, e2) ->
      (expr_has_existential e1) || (expr_has_existential e2)
  | E_StrAfter (e1, e2) ->
      (expr_has_existential e1) || (expr_has_existential e2)
  | E_SameTerm (e1, e2) ->
      (expr_has_existential e1) || (expr_has_existential e2)
  | E_UnaryMinus e1 -> expr_has_existential e1
  | E_UnaryPlus e1 -> expr_has_existential e1
  | E_Not e1 -> expr_has_existential e1
  | E_IsIRI e1 -> expr_has_existential e1
  | E_IsBlank e1 -> expr_has_existential e1
  | E_IsLiteral e1 -> expr_has_existential e1
  | E_IsNumeric e1 -> expr_has_existential e1
  | E_Str e1 -> expr_has_existential e1
  | E_Lang e1 -> expr_has_existential e1
  | E_Datatype e1 -> expr_has_existential e1
  | E_IRI_fn e1 -> expr_has_existential e1
  | E_HasLang e1 -> expr_has_existential e1
  | E_HasLangDir e1 -> expr_has_existential e1
  | E_LangDir e1 -> expr_has_existential e1
  | E_StrLen e1 -> expr_has_existential e1
  | E_UCase e1 -> expr_has_existential e1
  | E_LCase e1 -> expr_has_existential e1
  | E_EncodeForUri e1 -> expr_has_existential e1
  | E_Abs e1 -> expr_has_existential e1
  | E_Round e1 -> expr_has_existential e1
  | E_Ceil e1 -> expr_has_existential e1
  | E_Floor e1 -> expr_has_existential e1
  | E_MD5 e1 -> expr_has_existential e1
  | E_SHA1 e1 -> expr_has_existential e1
  | E_SHA256 e1 -> expr_has_existential e1
  | E_SHA384 e1 -> expr_has_existential e1
  | E_SHA512 e1 -> expr_has_existential e1
  | E_Year e1 -> expr_has_existential e1
  | E_Month e1 -> expr_has_existential e1
  | E_Day e1 -> expr_has_existential e1
  | E_Hours e1 -> expr_has_existential e1
  | E_Minutes e1 -> expr_has_existential e1
  | E_Seconds e1 -> expr_has_existential e1
  | E_Timezone e1 -> expr_has_existential e1
  | E_Tz e1 -> expr_has_existential e1
  | E_Aggregate (uu___, uu___1, e1) -> expr_has_existential e1
  | E_TTSubject e1 -> expr_has_existential e1
  | E_TTPredicate e1 -> expr_has_existential e1
  | E_TTObject e1 -> expr_has_existential e1
  | E_IsTriple e1 -> expr_has_existential e1
  | E_StrLangDir (e1, e2, e3) ->
      ((expr_has_existential e1) || (expr_has_existential e2)) ||
        (expr_has_existential e3)
  | E_If (e1, e2, e3) ->
      ((expr_has_existential e1) || (expr_has_existential e2)) ||
        (expr_has_existential e3)
  | E_TripleTerm (e1, e2, e3) ->
      ((expr_has_existential e1) || (expr_has_existential e2)) ||
        (expr_has_existential e3)
  | E_Coalesce es -> expr_list_has_existential es
  | E_Concat es -> expr_list_has_existential es
  | E_FunctionCall (uu___, es) -> expr_list_has_existential es
  | E_In (e1, es) ->
      (expr_has_existential e1) || (expr_list_has_existential es)
  | E_NotIn (e1, es) ->
      (expr_has_existential e1) || (expr_list_has_existential es)
  | E_Substr (e1, e2, e3o) ->
      ((expr_has_existential e1) || (expr_has_existential e2)) ||
        (expr_opt_has_existential e3o)
  | E_Regex (e1, e2, e3o) ->
      ((expr_has_existential e1) || (expr_has_existential e2)) ||
        (expr_opt_has_existential e3o)
  | E_Replace (e1, e2, e3, e4o) ->
      (((expr_has_existential e1) || (expr_has_existential e2)) ||
         (expr_has_existential e3))
        || (expr_opt_has_existential e4o)
and expr_list_has_existential (es : expr Prims.list) : Prims.bool=
  match es with
  | [] -> false
  | e::rest -> (expr_has_existential e) || (expr_list_has_existential rest)
and expr_opt_has_existential (eo : expr FStar_Pervasives_Native.option) :
  Prims.bool=
  match eo with
  | FStar_Pervasives_Native.None -> false
  | FStar_Pervasives_Native.Some e -> expr_has_existential e
let filter_solutions_fwd
  (base : RDF_Term.wf_iri FStar_Pervasives_Native.option) (e : expr)
  (omega : solution_sequence) : solution_sequence=
  FStar_List_Tot_Base.filter (eval_expr_ebv base e) omega
let union (omega1 : solution_sequence) (omega2 : solution_sequence) :
  solution_sequence= RDF_List_Helpers.append_tr omega1 omega2
let rec domains_disjoint (mu1 : RDF_Graph_Executable.solution_mapping)
  (mu2 : RDF_Graph_Executable.solution_mapping) : Prims.bool=
  match mu1 with
  | [] -> true
  | (v, uu___)::rest ->
      (Prims.op_Negation
         (FStar_Pervasives_Native.uu___is_Some
            (FStar_List_Tot_Base.assoc v mu2)))
        && (domains_disjoint rest mu2)
let minus (omega1 : solution_sequence) (omega2 : solution_sequence) :
  solution_sequence=
  FStar_List_Tot_Base.filter
    (fun mu1 ->
       Prims.op_Negation
         (FStar_List_Tot_Base.existsb
            (fun mu2 ->
               (sm_compatible mu1 mu2) &&
                 (Prims.op_Negation (domains_disjoint mu1 mu2))) omega2))
    omega1
let rec fx_bind_rows (base : RDF_Term.wf_iri FStar_Pervasives_Native.option)
  (e : expr) (v : var_name) (omega : solution_sequence) (i : Prims.nat) :
  solution_sequence=
  match omega with
  | [] -> []
  | mu::rest ->
      let mu_ctx = fx_ctx_put (Prims.string_of_int i) v mu in
      let row =
        match er_to_term (eval_expr_fwd base e mu_ctx) with
        | FStar_Pervasives_Native.Some t ->
            (match sm_lookup v mu with
             | FStar_Pervasives_Native.Some uu___ -> mu
             | FStar_Pervasives_Native.None -> sm_bind v t mu)
        | FStar_Pervasives_Native.None -> mu in
      row :: (fx_bind_rows base e v rest (i + Prims.int_one))
let substitute_pattern_term (mu : RDF_Graph_Executable.solution_mapping)
  (pt : pattern_term) : pattern_term=
  match pt with
  | PT_Var v ->
      (match sm_lookup v mu with
       | FStar_Pervasives_Native.Some (RDF_Term.T_IRI i) -> PT_IRI i
       | FStar_Pervasives_Native.Some (RDF_Term.T_BNode b) -> PT_BNode b
       | FStar_Pervasives_Native.Some (RDF_Term.T_Literal l) -> PT_Literal l
       | FStar_Pervasives_Native.Some (RDF_Term.T_TripleTerm
           (uu___, uu___1, uu___2)) -> PT_Var v
       | FStar_Pervasives_Native.None -> PT_Var v)
  | uu___ -> pt
let substitute_pattern_subject (mu : RDF_Graph_Executable.solution_mapping)
  (ps : pattern_subject) : pattern_subject=
  match ps with
  | PS_Var v ->
      (match sm_lookup v mu with
       | FStar_Pervasives_Native.Some (RDF_Term.T_IRI i) -> PS_IRI i
       | FStar_Pervasives_Native.Some (RDF_Term.T_BNode b) -> PS_BNode b
       | FStar_Pervasives_Native.Some (RDF_Term.T_Literal uu___) -> PS_Var v
       | FStar_Pervasives_Native.Some (RDF_Term.T_TripleTerm
           (uu___, uu___1, uu___2)) -> PS_Var v
       | FStar_Pervasives_Native.None -> PS_Var v)
  | uu___ -> ps
let substitute_triple_pattern (mu : RDF_Graph_Executable.solution_mapping)
  (tp : triple_pattern) : triple_pattern=
  {
    tp_s = (substitute_pattern_subject mu tp.tp_s);
    tp_p = (substitute_pattern_term mu tp.tp_p);
    tp_o = (substitute_pattern_term mu tp.tp_o)
  }
let substitute_bgp (mu : RDF_Graph_Executable.solution_mapping) (b : bgp) :
  bgp= FStar_List_Tot_Base.map (substitute_triple_pattern mu) b
let rec pattern_size (p : group_graph_pattern) : Prims.nat=
  match p with
  | GP_BGP uu___ -> Prims.int_one
  | GP_Join (p1, p2) ->
      (Prims.int_one + (pattern_size p1)) + (pattern_size p2)
  | GP_LeftJoin (p1, p2, e) ->
      ((Prims.int_one + (pattern_size p1)) + (pattern_size p2)) +
        (expr_size e)
  | GP_Filter (e, p1) -> (Prims.int_one + (expr_size e)) + (pattern_size p1)
  | GP_Union (p1, p2) ->
      (Prims.int_one + (pattern_size p1)) + (pattern_size p2)
  | GP_Graph (uu___, p1) -> Prims.int_one + (pattern_size p1)
  | GP_Minus (p1, p2) ->
      (Prims.int_one + (pattern_size p1)) + (pattern_size p2)
  | GP_Lateral (p1, p2) ->
      (Prims.int_one + (pattern_size p1)) + (pattern_size p2)
  | GP_Bind (e, uu___, p1) ->
      (Prims.int_one + (expr_size e)) + (pattern_size p1)
  | GP_Values (uu___, uu___1) -> Prims.int_one
  | GP_Service (uu___, p1, uu___1) -> Prims.int_one + (pattern_size p1)
  | GP_ServiceVar (uu___, p1, uu___1) -> Prims.int_one + (pattern_size p1)
  | GP_SubSelect q -> Prims.int_one + (query_size q)
  | GP_PropertyPath (uu___, uu___1, uu___2) -> Prims.int_one
  | GP_Empty -> Prims.int_one
and expr_size (e : expr) : Prims.nat=
  match e with
  | E_Var uu___ -> Prims.int_one
  | E_IRI uu___ -> Prims.int_one
  | E_Literal uu___ -> Prims.int_one
  | E_BoolLit uu___ -> Prims.int_one
  | E_NumericLit uu___ -> Prims.int_one
  | E_DecimalLit uu___ -> Prims.int_one
  | E_DoubleLit uu___ -> Prims.int_one
  | E_Bound uu___ -> Prims.int_one
  | E_Now -> Prims.int_one
  | E_Arith (uu___, e1, e2) ->
      (Prims.int_one + (expr_size e1)) + (expr_size e2)
  | E_Compare (uu___, e1, e2) ->
      (Prims.int_one + (expr_size e1)) + (expr_size e2)
  | E_And (e1, e2) -> (Prims.int_one + (expr_size e1)) + (expr_size e2)
  | E_Or (e1, e2) -> (Prims.int_one + (expr_size e1)) + (expr_size e2)
  | E_StrDt (e1, e2) -> (Prims.int_one + (expr_size e1)) + (expr_size e2)
  | E_StrLang (e1, e2) -> (Prims.int_one + (expr_size e1)) + (expr_size e2)
  | E_StrStarts (e1, e2) -> (Prims.int_one + (expr_size e1)) + (expr_size e2)
  | E_StrEnds (e1, e2) -> (Prims.int_one + (expr_size e1)) + (expr_size e2)
  | E_Contains (e1, e2) -> (Prims.int_one + (expr_size e1)) + (expr_size e2)
  | E_StrBefore (e1, e2) -> (Prims.int_one + (expr_size e1)) + (expr_size e2)
  | E_StrAfter (e1, e2) -> (Prims.int_one + (expr_size e1)) + (expr_size e2)
  | E_SameTerm (e1, e2) -> (Prims.int_one + (expr_size e1)) + (expr_size e2)
  | E_UnaryMinus e1 -> Prims.int_one + (expr_size e1)
  | E_UnaryPlus e1 -> Prims.int_one + (expr_size e1)
  | E_Not e1 -> Prims.int_one + (expr_size e1)
  | E_IsIRI e1 -> Prims.int_one + (expr_size e1)
  | E_IsBlank e1 -> Prims.int_one + (expr_size e1)
  | E_IsLiteral e1 -> Prims.int_one + (expr_size e1)
  | E_IsNumeric e1 -> Prims.int_one + (expr_size e1)
  | E_Str e1 -> Prims.int_one + (expr_size e1)
  | E_Lang e1 -> Prims.int_one + (expr_size e1)
  | E_Datatype e1 -> Prims.int_one + (expr_size e1)
  | E_IRI_fn e1 -> Prims.int_one + (expr_size e1)
  | E_HasLang e1 -> Prims.int_one + (expr_size e1)
  | E_HasLangDir e1 -> Prims.int_one + (expr_size e1)
  | E_LangDir e1 -> Prims.int_one + (expr_size e1)
  | E_StrLen e1 -> Prims.int_one + (expr_size e1)
  | E_UCase e1 -> Prims.int_one + (expr_size e1)
  | E_LCase e1 -> Prims.int_one + (expr_size e1)
  | E_EncodeForUri e1 -> Prims.int_one + (expr_size e1)
  | E_Abs e1 -> Prims.int_one + (expr_size e1)
  | E_Round e1 -> Prims.int_one + (expr_size e1)
  | E_Ceil e1 -> Prims.int_one + (expr_size e1)
  | E_Floor e1 -> Prims.int_one + (expr_size e1)
  | E_MD5 e1 -> Prims.int_one + (expr_size e1)
  | E_SHA1 e1 -> Prims.int_one + (expr_size e1)
  | E_SHA256 e1 -> Prims.int_one + (expr_size e1)
  | E_SHA384 e1 -> Prims.int_one + (expr_size e1)
  | E_SHA512 e1 -> Prims.int_one + (expr_size e1)
  | E_Year e1 -> Prims.int_one + (expr_size e1)
  | E_Month e1 -> Prims.int_one + (expr_size e1)
  | E_Day e1 -> Prims.int_one + (expr_size e1)
  | E_Hours e1 -> Prims.int_one + (expr_size e1)
  | E_Minutes e1 -> Prims.int_one + (expr_size e1)
  | E_Seconds e1 -> Prims.int_one + (expr_size e1)
  | E_Timezone e1 -> Prims.int_one + (expr_size e1)
  | E_Tz e1 -> Prims.int_one + (expr_size e1)
  | E_Aggregate (uu___, uu___1, e1) -> Prims.int_one + (expr_size e1)
  | E_TTSubject e1 -> Prims.int_one + (expr_size e1)
  | E_TTPredicate e1 -> Prims.int_one + (expr_size e1)
  | E_TTObject e1 -> Prims.int_one + (expr_size e1)
  | E_IsTriple e1 -> Prims.int_one + (expr_size e1)
  | E_StrLangDir (e1, e2, e3) ->
      ((Prims.int_one + (expr_size e1)) + (expr_size e2)) + (expr_size e3)
  | E_If (e1, e2, e3) ->
      ((Prims.int_one + (expr_size e1)) + (expr_size e2)) + (expr_size e3)
  | E_TripleTerm (e1, e2, e3) ->
      ((Prims.int_one + (expr_size e1)) + (expr_size e2)) + (expr_size e3)
  | E_Coalesce es -> Prims.int_one + (expr_list_size es)
  | E_Concat es -> Prims.int_one + (expr_list_size es)
  | E_FunctionCall (uu___, es) -> Prims.int_one + (expr_list_size es)
  | E_In (e1, es) -> (Prims.int_one + (expr_size e1)) + (expr_list_size es)
  | E_NotIn (e1, es) ->
      (Prims.int_one + (expr_size e1)) + (expr_list_size es)
  | E_Substr (e1, e2, e3o) ->
      ((Prims.int_one + (expr_size e1)) + (expr_size e2)) +
        (expr_opt_size e3o)
  | E_Regex (e1, e2, e3o) ->
      ((Prims.int_one + (expr_size e1)) + (expr_size e2)) +
        (expr_opt_size e3o)
  | E_Replace (e1, e2, e3, e4o) ->
      (((Prims.int_one + (expr_size e1)) + (expr_size e2)) + (expr_size e3))
        + (expr_opt_size e4o)
  | E_Exists p -> Prims.int_one + (pattern_size p)
  | E_NotExists p -> Prims.int_one + (pattern_size p)
and expr_list_size (es : expr Prims.list) : Prims.nat=
  match es with
  | [] -> Prims.int_zero
  | hd::tl -> (Prims.int_one + (expr_size hd)) + (expr_list_size tl)
and expr_opt_size (eo : expr FStar_Pervasives_Native.option) : Prims.nat=
  match eo with
  | FStar_Pervasives_Native.None -> Prims.int_zero
  | FStar_Pervasives_Native.Some e -> Prims.int_one + (expr_size e)
and query_size (q : query) : Prims.nat=
  Prims.int_one + (pattern_size q.q_pattern)
let rec substitute_pattern (mu : RDF_Graph_Executable.solution_mapping)
  (p : group_graph_pattern) : group_graph_pattern=
  match p with
  | GP_BGP b -> GP_BGP (substitute_bgp mu b)
  | GP_Join (p1, p2) ->
      GP_Join ((substitute_pattern mu p1), (substitute_pattern mu p2))
  | GP_LeftJoin (p1, p2, e) ->
      GP_LeftJoin ((substitute_pattern mu p1), (substitute_pattern mu p2), e)
  | GP_Filter (e, p1) -> GP_Filter (e, (substitute_pattern mu p1))
  | GP_Union (p1, p2) ->
      GP_Union ((substitute_pattern mu p1), (substitute_pattern mu p2))
  | GP_Graph (gt, p1) ->
      GP_Graph ((substitute_pattern_term mu gt), (substitute_pattern mu p1))
  | GP_Minus (p1, p2) ->
      GP_Minus ((substitute_pattern mu p1), (substitute_pattern mu p2))
  | GP_Lateral (p1, p2) ->
      GP_Lateral ((substitute_pattern mu p1), (substitute_pattern mu p2))
  | GP_Bind (e, v, p1) -> GP_Bind (e, v, (substitute_pattern mu p1))
  | GP_Values (vars, rows) -> GP_Values (vars, rows)
  | GP_Service (iri, p1, silent) -> GP_Service (iri, p1, silent)
  | GP_ServiceVar (v, p1, silent) ->
      (match sm_lookup v mu with
       | FStar_Pervasives_Native.Some (RDF_Term.T_IRI iri) ->
           if RDF_Term.is_iri iri
           then GP_Service (iri, (substitute_pattern mu p1), silent)
           else GP_ServiceVar (v, (substitute_pattern mu p1), silent)
       | uu___ -> GP_ServiceVar (v, (substitute_pattern mu p1), silent))
  | GP_SubSelect q -> GP_SubSelect q
  | GP_PropertyPath (ps, pp, pt) ->
      GP_PropertyPath
        ((substitute_pattern_subject mu ps), pp,
          (substitute_pattern_term mu pt))
  | GP_Empty -> GP_Empty
type group = {
  g_key: eval_result Prims.list ;
  g_solutions: solution_sequence }
let __proj__Mkgroup__item__g_key (projectee : group) :
  eval_result Prims.list=
  match projectee with | { g_key; g_solutions;_} -> g_key
let __proj__Mkgroup__item__g_solutions (projectee : group) :
  solution_sequence=
  match projectee with | { g_key; g_solutions;_} -> g_solutions
let eval_group_condition
  (base : RDF_Term.wf_iri FStar_Pervasives_Native.option)
  (gc : group_condition) (mu : RDF_Graph_Executable.solution_mapping) :
  eval_result=
  match gc with
  | GC_Var v ->
      (match sm_lookup v mu with
       | FStar_Pervasives_Native.Some t -> ER_Term t
       | FStar_Pervasives_Native.None -> ER_Error)
  | GC_Expr (e, uu___) -> eval_expr_with_base base e mu
  | GC_BuiltIn e -> eval_expr_with_base base e mu
let eval_group_key (base : RDF_Term.wf_iri FStar_Pervasives_Native.option)
  (conds : group_condition Prims.list)
  (mu : RDF_Graph_Executable.solution_mapping) : eval_result Prims.list=
  FStar_List_Tot_Base.map (fun gc -> eval_group_condition base gc mu) conds
let literal_order (l1 : RDF_Term.wf_literal) (l2 : RDF_Term.wf_literal) :
  Prims.int=
  let dc = FStar_String.compare (lit_datatype l1) (lit_datatype l2) in
  if dc <> Prims.int_zero
  then dc
  else
    (let lc = FStar_String.compare (lit_lexical l1) (lit_lexical l2) in
     if lc <> Prims.int_zero
     then lc
     else
       (match ((lit_lang l1), (lit_lang l2)) with
        | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) ->
            Prims.int_zero
        | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.Some uu___2)
            -> (Prims.of_int (-1))
        | (FStar_Pervasives_Native.Some uu___2, FStar_Pervasives_Native.None)
            -> Prims.int_one
        | (FStar_Pervasives_Native.Some t1, FStar_Pervasives_Native.Some t2)
            -> FStar_String.compare t1 t2))
let subject_order (s1 : RDF_Term.subject) (s2 : RDF_Term.subject) :
  Prims.int=
  match (s1, s2) with
  | (RDF_Term.S_BNode x, RDF_Term.S_BNode y) -> FStar_String.compare x y
  | (RDF_Term.S_IRI x, RDF_Term.S_IRI y) ->
      FStar_String.compare (iri_to_string x) (iri_to_string y)
  | (RDF_Term.S_BNode uu___, RDF_Term.S_IRI uu___1) -> (Prims.of_int (-1))
  | (RDF_Term.S_IRI uu___, RDF_Term.S_BNode uu___1) -> Prims.int_one
let term_rank (t : RDF_Term.rdf_term) : Prims.int=
  match t with
  | RDF_Term.T_BNode uu___ -> Prims.int_one
  | RDF_Term.T_IRI uu___ -> (Prims.of_int (2))
  | RDF_Term.T_Literal uu___ -> (Prims.of_int (7))
  | RDF_Term.T_TripleTerm (uu___, uu___1, uu___2) -> (Prims.of_int (8))
let rec term_order (t1 : RDF_Term.rdf_term) (t2 : RDF_Term.rdf_term) :
  Prims.int=
  let r1 = term_rank t1 in
  let r2 = term_rank t2 in
  if r1 < r2
  then (Prims.of_int (-1))
  else
    if r1 > r2
    then Prims.int_one
    else
      (match (t1, t2) with
       | (RDF_Term.T_BNode x, RDF_Term.T_BNode y) -> FStar_String.compare x y
       | (RDF_Term.T_IRI x, RDF_Term.T_IRI y) ->
           FStar_String.compare (iri_to_string x) (iri_to_string y)
       | (RDF_Term.T_Literal l1, RDF_Term.T_Literal l2) ->
           literal_order l1 l2
       | (RDF_Term.T_TripleTerm (s1, p1, o1), RDF_Term.T_TripleTerm
          (s2, p2, o2)) ->
           let sc = subject_order s1 s2 in
           if sc <> Prims.int_zero
           then sc
           else
             (let pc =
                FStar_String.compare (iri_to_string p1) (iri_to_string p2) in
              if pc <> Prims.int_zero then pc else term_order o1 o2)
       | (uu___2, uu___3) -> Prims.int_zero)
let er_rank (v : eval_result) : Prims.int=
  match v with
  | ER_Error -> Prims.int_zero
  | ER_Term (RDF_Term.T_BNode uu___) -> Prims.int_one
  | ER_Term (RDF_Term.T_IRI uu___) -> (Prims.of_int (2))
  | ER_Bool uu___ -> (Prims.of_int (3))
  | ER_Num uu___ -> (Prims.of_int (4))
  | ER_Dec uu___ -> (Prims.of_int (4))
  | ER_Dbl uu___ -> (Prims.of_int (4))
  | ER_Term (RDF_Term.T_Literal uu___) -> (Prims.of_int (7))
  | ER_Term (RDF_Term.T_TripleTerm (uu___, uu___1, uu___2)) ->
      (Prims.of_int (8))
let sparql_order_numeric (a : eval_result) (b : eval_result) : Prims.int=
  match numeric_compare a b with
  | FStar_Pervasives_Native.Some cmp -> cmp
  | FStar_Pervasives_Native.None ->
      (match ((er_to_numeric a), (er_to_numeric b)) with
       | (FStar_Pervasives_Native.Some uu___, FStar_Pervasives_Native.None)
           -> (Prims.of_int (-1))
       | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.Some uu___)
           -> Prims.int_one
       | (uu___, uu___1) ->
           FStar_String.compare (er_numeric_lexical a) (er_numeric_lexical b))
let sparql_order (a : eval_result) (b : eval_result) : Prims.int=
  let ra = er_rank a in
  let rb = er_rank b in
  if ra < rb
  then (Prims.of_int (-1))
  else
    if ra > rb
    then Prims.int_one
    else
      (match (a, b) with
       | (ER_Error, ER_Error) -> Prims.int_zero
       | (ER_Term (RDF_Term.T_BNode x), ER_Term (RDF_Term.T_BNode y)) ->
           FStar_String.compare x y
       | (ER_Term (RDF_Term.T_IRI x), ER_Term (RDF_Term.T_IRI y)) ->
           FStar_String.compare (iri_to_string x) (iri_to_string y)
       | (ER_Bool x, ER_Bool y) ->
           int_compare (if x then Prims.int_one else Prims.int_zero)
             (if y then Prims.int_one else Prims.int_zero)
       | (ER_Num uu___2, uu___3) -> sparql_order_numeric a b
       | (ER_Dec uu___2, uu___3) -> sparql_order_numeric a b
       | (ER_Dbl uu___2, uu___3) -> sparql_order_numeric a b
       | (ER_Term (RDF_Term.T_Literal l1), ER_Term (RDF_Term.T_Literal l2))
           -> literal_order l1 l2
       | (ER_Term (RDF_Term.T_TripleTerm (s1, p1, o1)), ER_Term
          (RDF_Term.T_TripleTerm (s2, p2, o2))) ->
           term_order (RDF_Term.T_TripleTerm (s1, p1, o1))
             (RDF_Term.T_TripleTerm (s2, p2, o2))
       | (uu___2, uu___3) -> Prims.int_zero)
let er_equal (a : eval_result) (b : eval_result) : Prims.bool=
  (sparql_order a b) = Prims.int_zero
let rec keys_equal (k1 : eval_result Prims.list)
  (k2 : eval_result Prims.list) : Prims.bool=
  match (k1, k2) with
  | ([], []) -> true
  | (a::rest1, b::rest2) -> (er_equal a b) && (keys_equal rest1 rest2)
  | (uu___, uu___1) -> false
let rec find_group (key : eval_result Prims.list) (groups : group Prims.list)
  :
  (group Prims.list * group * group Prims.list)
    FStar_Pervasives_Native.option=
  match groups with
  | [] -> FStar_Pervasives_Native.None
  | g::rest ->
      if keys_equal key g.g_key
      then FStar_Pervasives_Native.Some ([], g, rest)
      else
        (match find_group key rest with
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some (before, found, after) ->
             FStar_Pervasives_Native.Some ((g :: before), found, after))
let add_to_groups (key : eval_result Prims.list)
  (mu : RDF_Graph_Executable.solution_mapping) (groups : group Prims.list) :
  group Prims.list=
  let uu___ =
    FStar_List_Tot_Base.fold_left
      (fun acc_f g ->
         let uu___1 = acc_f in
         match uu___1 with
         | (acc, f) ->
             if (Prims.op_Negation f) && (keys_equal key g.g_key)
             then
               let g' =
                 { g_key = (g.g_key); g_solutions = (mu :: (g.g_solutions)) } in
               ((g' :: acc), true)
             else ((g :: acc), f)) ([], false) groups in
  match uu___ with
  | (rev_groups, found) ->
      let ordered = FStar_List_Tot_Base.rev rev_groups in
      if found
      then ordered
      else
        RDF_List_Helpers.append_tr ordered
          [{ g_key = key; g_solutions = [mu] }]
let extend_with_group_aliases
  (base : RDF_Term.wf_iri FStar_Pervasives_Native.option)
  (conds : group_condition Prims.list)
  (mu : RDF_Graph_Executable.solution_mapping) :
  RDF_Graph_Executable.solution_mapping=
  FStar_List_Tot_Base.fold_left
    (fun acc gc ->
       match gc with
       | GC_Expr (e, FStar_Pervasives_Native.Some v) ->
           let r = eval_expr_with_base base e mu in
           (match er_to_term r with
            | FStar_Pervasives_Native.Some t -> sm_bind v t acc
            | FStar_Pervasives_Native.None -> acc)
       | uu___ -> acc) mu conds
let group_by (base : RDF_Term.wf_iri FStar_Pervasives_Native.option)
  (conds : group_condition Prims.list) (omega : solution_sequence) :
  group Prims.list=
  let groups_reversed =
    FStar_List_Tot_Base.fold_left
      (fun groups mu ->
         let key = eval_group_key base conds mu in
         let mu' = extend_with_group_aliases base conds mu in
         add_to_groups key mu' groups) [] omega in
  FStar_List_Tot_Base.map
    (fun g ->
       {
         g_key = (g.g_key);
         g_solutions = (FStar_List_Tot_Base.rev g.g_solutions)
       }) groups_reversed
let implicit_group (omega : solution_sequence) : group Prims.list=
  [{ g_key = []; g_solutions = omega }]
let eval_over_group (base : RDF_Term.wf_iri FStar_Pervasives_Native.option)
  (e : expr) (g : group) : eval_result Prims.list=
  FStar_List_Tot_Base.map (fun mu -> eval_expr_with_base base e mu)
    g.g_solutions
let filter_non_error (vals : eval_result Prims.list) :
  eval_result Prims.list=
  FStar_List_Tot_Base.filter
    (fun v -> Prims.op_Negation (uu___is_ER_Error v)) vals
let rec dedup_er_acc (acc : eval_result Prims.list)
  (vals : eval_result Prims.list) : eval_result Prims.list=
  match vals with
  | [] -> acc
  | v::rest ->
      if FStar_List_Tot_Base.existsb (fun x -> er_equal v x) acc
      then dedup_er_acc acc rest
      else dedup_er_acc (v :: acc) rest
let dedup_er (vals : eval_result Prims.list) : eval_result Prims.list=
  FStar_List_Tot_Base.rev (dedup_er_acc [] vals)
let find_min (vals : eval_result Prims.list) : eval_result=
  match vals with
  | [] -> ER_Error
  | v::rest ->
      FStar_List_Tot_Base.fold_left
        (fun acc x ->
           if (sparql_order x acc) <= Prims.int_zero then x else acc) v rest
let find_max (vals : eval_result Prims.list) : eval_result=
  match vals with
  | [] -> ER_Error
  | v::rest ->
      FStar_List_Tot_Base.fold_left
        (fun acc x ->
           if (sparql_order x acc) >= Prims.int_zero then x else acc) v rest
let rec collect_strings_acc (acc : Prims.string Prims.list)
  (vals : eval_result Prims.list) : Prims.string Prims.list=
  match vals with
  | [] -> FStar_List_Tot_Base.rev acc
  | v::rest ->
      (match er_to_string v with
       | FStar_Pervasives_Native.Some s ->
           collect_strings_acc (s :: acc) rest
       | FStar_Pervasives_Native.None -> collect_strings_acc acc rest)
let collect_strings (vals : eval_result Prims.list) :
  Prims.string Prims.list= collect_strings_acc [] vals
let rec first_non_error (vals : eval_result Prims.list) : eval_result=
  match vals with
  | [] -> ER_Error
  | v::rest -> if uu___is_ER_Error v then first_non_error rest else v
let eval_aggregate (base : RDF_Term.wf_iri FStar_Pervasives_Native.option)
  (fn : aggregate_fn) (distinct : Prims.bool) (e : expr) (g : group) :
  eval_result=
  match fn with
  | Agg_Count ->
      (match e with
       | E_Var "*" ->
           if distinct
           then
             let sols = g.g_solutions in
             let to_key mu =
               FStar_String.concat "|"
                 (FStar_List_Tot_Base.map
                    (fun p ->
                       Prims.strcat (FStar_Pervasives_Native.fst p)
                         (Prims.strcat "="
                            (match FStar_Pervasives_Native.snd p with
                             | RDF_Term.T_IRI i -> i
                             | RDF_Term.T_BNode b -> b
                             | RDF_Term.T_Literal l ->
                                 Prims.strcat (lit_lexical l)
                                   (Prims.strcat "^^" (lit_datatype l))
                             | RDF_Term.T_TripleTerm (uu___, uu___1, uu___2)
                                 ->
                                 RDF_NQuads_Serialize.nq_term_to_string
                                   (FStar_Pervasives_Native.snd p)))) mu) in
             let dedup_strings_tr keys =
               FStar_List_Tot_Base.fold_left
                 (fun seen k ->
                    if FStar_List_Tot_Base.existsb (fun s -> s = k) seen
                    then seen
                    else k :: seen) [] keys in
             ER_Num
               (FStar_List_Tot_Base.length
                  (dedup_strings_tr (FStar_List_Tot_Base.map to_key sols)))
           else ER_Num (FStar_List_Tot_Base.length g.g_solutions)
       | E_BoolLit true ->
           if distinct
           then
             let sols = g.g_solutions in
             let to_key mu =
               FStar_String.concat "|"
                 (FStar_List_Tot_Base.map
                    (fun p ->
                       Prims.strcat (FStar_Pervasives_Native.fst p)
                         (Prims.strcat "="
                            (match FStar_Pervasives_Native.snd p with
                             | RDF_Term.T_IRI i -> i
                             | RDF_Term.T_BNode b -> b
                             | RDF_Term.T_Literal l ->
                                 Prims.strcat (lit_lexical l)
                                   (Prims.strcat "^^" (lit_datatype l))
                             | RDF_Term.T_TripleTerm (uu___, uu___1, uu___2)
                                 ->
                                 RDF_NQuads_Serialize.nq_term_to_string
                                   (FStar_Pervasives_Native.snd p)))) mu) in
             let dedup_strings_tr keys =
               FStar_List_Tot_Base.fold_left
                 (fun seen k ->
                    if FStar_List_Tot_Base.existsb (fun s -> s = k) seen
                    then seen
                    else k :: seen) [] keys in
             ER_Num
               (FStar_List_Tot_Base.length
                  (dedup_strings_tr (FStar_List_Tot_Base.map to_key sols)))
           else ER_Num (FStar_List_Tot_Base.length g.g_solutions)
       | uu___ ->
           let vals = filter_non_error (eval_over_group base e g) in
           let vals1 = if distinct then dedup_er vals else vals in
           ER_Num (FStar_List_Tot_Base.length vals1))
  | Agg_Sum ->
      let raw_vals = eval_over_group base e g in
      let vals = filter_non_error raw_vals in
      let vals1 = if distinct then dedup_er vals else vals in
      if
        FStar_List_Tot_Base.existsb
          (fun v -> FStar_Pervasives_Native.uu___is_None (er_to_numeric v))
          vals1
      then ER_Error
      else sum_numeric vals1
  | Agg_Avg ->
      let raw_vals = eval_over_group base e g in
      let vals = filter_non_error raw_vals in
      let vals1 = if distinct then dedup_er vals else vals in
      if
        FStar_List_Tot_Base.existsb
          (fun v -> FStar_Pervasives_Native.uu___is_None (er_to_numeric v))
          vals1
      then ER_Error
      else avg_numeric vals1
  | Agg_Min ->
      let vals = filter_non_error (eval_over_group base e g) in
      let vals1 = if distinct then dedup_er vals else vals in find_min vals1
  | Agg_Max ->
      let vals = filter_non_error (eval_over_group base e g) in
      let vals1 = if distinct then dedup_er vals else vals in find_max vals1
  | Agg_GroupConcat sep_opt ->
      let vals = filter_non_error (eval_over_group base e g) in
      let vals1 = if distinct then dedup_er vals else vals in
      let sep =
        match sep_opt with
        | FStar_Pervasives_Native.Some s -> s
        | FStar_Pervasives_Native.None -> " " in
      let strs = collect_strings vals1 in
      ER_Term
        (RDF_Term.T_Literal (mk_plain_literal (FStar_String.concat sep strs)))
  | Agg_Sample -> let vals = eval_over_group base e g in first_non_error vals
let rec rewrite_aggregates
  (base : RDF_Term.wf_iri FStar_Pervasives_Native.option) (e : expr)
  (g : group) : expr=
  match e with
  | E_Aggregate (fn, distinct, sub_e) ->
      let r = eval_aggregate base fn distinct sub_e g in
      (match r with
       | ER_Num n -> E_NumericLit n
       | ER_Bool b -> E_BoolLit b
       | ER_Dec s -> E_DecimalLit s
       | ER_Dbl d -> E_DoubleLit d
       | ER_Term t ->
           (match t with
            | RDF_Term.T_IRI i -> E_IRI i
            | RDF_Term.T_Literal l -> E_Literal l
            | uu___ -> E_BoolLit false)
       | ER_Error -> E_Var "_:error:")
  | E_Compare (op, e1, e2) ->
      E_Compare
        (op, (rewrite_aggregates base e1 g), (rewrite_aggregates base e2 g))
  | E_And (e1, e2) ->
      E_And ((rewrite_aggregates base e1 g), (rewrite_aggregates base e2 g))
  | E_Or (e1, e2) ->
      E_Or ((rewrite_aggregates base e1 g), (rewrite_aggregates base e2 g))
  | E_Arith (op, e1, e2) ->
      E_Arith
        (op, (rewrite_aggregates base e1 g), (rewrite_aggregates base e2 g))
  | E_Not e1 -> E_Not (rewrite_aggregates base e1 g)
  | uu___ -> e
let having_filter (base : RDF_Term.wf_iri FStar_Pervasives_Native.option)
  (conditions : having_condition Prims.list) (groups : group Prims.list) :
  group Prims.list=
  FStar_List_Tot_Base.filter
    (fun g ->
       let mu = match g.g_solutions with | mu1::uu___ -> mu1 | [] -> sm_empty in
       FStar_List_Tot_Base.for_all
         (fun cond ->
            let rewritten = rewrite_aggregates base cond g in
            ebv (eval_expr_with_base base rewritten mu)) conditions) groups
let eval_expr_in_group
  (base : RDF_Term.wf_iri FStar_Pervasives_Native.option) (e : expr)
  (g : group) : eval_result=
  let rewritten = rewrite_aggregates base e g in
  match g.g_solutions with
  | mu::uu___ -> eval_expr_with_base base rewritten mu
  | [] -> eval_expr_with_base base rewritten sm_empty
let eval_select_item_group
  (base : RDF_Term.wf_iri FStar_Pervasives_Native.option)
  (item : select_item) (g : group) :
  (var_name * RDF_Term.rdf_term) FStar_Pervasives_Native.option=
  match item with
  | SI_Var v ->
      (match g.g_solutions with
       | mu::uu___ ->
           (match sm_lookup v mu with
            | FStar_Pervasives_Native.Some t ->
                FStar_Pervasives_Native.Some (v, t)
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
       | [] -> FStar_Pervasives_Native.None)
  | SI_Expr (e, v) ->
      let r = eval_expr_in_group base e g in
      (match er_to_term r with
       | FStar_Pervasives_Native.Some t ->
           FStar_Pervasives_Native.Some (v, t)
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
let aggregate_group (base : RDF_Term.wf_iri FStar_Pervasives_Native.option)
  (items : select_item Prims.list) (g : group) :
  RDF_Graph_Executable.solution_mapping=
  list_filter_map (fun item -> eval_select_item_group base item g) items
let aggregate_groups (base : RDF_Term.wf_iri FStar_Pervasives_Native.option)
  (items : select_item Prims.list) (groups : group Prims.list) :
  solution_sequence=
  FStar_List_Tot_Base.map (aggregate_group base items) groups
let rec expr_has_aggregate (e : expr) : Prims.bool=
  match e with
  | E_Aggregate (uu___, uu___1, uu___2) -> true
  | E_Arith (uu___, e1, e2) ->
      (expr_has_aggregate e1) || (expr_has_aggregate e2)
  | E_Compare (uu___, e1, e2) ->
      (expr_has_aggregate e1) || (expr_has_aggregate e2)
  | E_And (e1, e2) -> (expr_has_aggregate e1) || (expr_has_aggregate e2)
  | E_Or (e1, e2) -> (expr_has_aggregate e1) || (expr_has_aggregate e2)
  | E_Not e1 -> expr_has_aggregate e1
  | E_UnaryMinus e1 -> expr_has_aggregate e1
  | E_UnaryPlus e1 -> expr_has_aggregate e1
  | E_If (c, t, f) ->
      ((expr_has_aggregate c) || (expr_has_aggregate t)) ||
        (expr_has_aggregate f)
  | uu___ -> false
let rec expr_has_ungrouped_var (is_grp : var_name -> Prims.bool) (e : expr) :
  Prims.bool=
  match e with
  | E_Var v -> Prims.op_Negation (is_grp v)
  | E_Aggregate (uu___, uu___1, uu___2) -> false
  | E_Arith (uu___, e1, e2) ->
      (expr_has_ungrouped_var is_grp e1) ||
        (expr_has_ungrouped_var is_grp e2)
  | E_Compare (uu___, e1, e2) ->
      (expr_has_ungrouped_var is_grp e1) ||
        (expr_has_ungrouped_var is_grp e2)
  | E_And (e1, e2) ->
      (expr_has_ungrouped_var is_grp e1) ||
        (expr_has_ungrouped_var is_grp e2)
  | E_Or (e1, e2) ->
      (expr_has_ungrouped_var is_grp e1) ||
        (expr_has_ungrouped_var is_grp e2)
  | E_Not e1 -> expr_has_ungrouped_var is_grp e1
  | E_UnaryMinus e1 -> expr_has_ungrouped_var is_grp e1
  | E_UnaryPlus e1 -> expr_has_ungrouped_var is_grp e1
  | E_If (c, t, f) ->
      ((expr_has_ungrouped_var is_grp c) || (expr_has_ungrouped_var is_grp t))
        || (expr_has_ungrouped_var is_grp f)
  | E_Str e1 -> expr_has_ungrouped_var is_grp e1
  | E_Lang e1 -> expr_has_ungrouped_var is_grp e1
  | E_Datatype e1 -> expr_has_ungrouped_var is_grp e1
  | E_IRI_fn e1 -> expr_has_ungrouped_var is_grp e1
  | E_HasLang e1 -> expr_has_ungrouped_var is_grp e1
  | E_HasLangDir e1 -> expr_has_ungrouped_var is_grp e1
  | E_LangDir e1 -> expr_has_ungrouped_var is_grp e1
  | E_IsIRI e1 -> expr_has_ungrouped_var is_grp e1
  | E_IsBlank e1 -> expr_has_ungrouped_var is_grp e1
  | E_IsLiteral e1 -> expr_has_ungrouped_var is_grp e1
  | E_IsNumeric e1 -> expr_has_ungrouped_var is_grp e1
  | E_StrDt (e1, e2) ->
      (expr_has_ungrouped_var is_grp e1) ||
        (expr_has_ungrouped_var is_grp e2)
  | E_StrLang (e1, e2) ->
      (expr_has_ungrouped_var is_grp e1) ||
        (expr_has_ungrouped_var is_grp e2)
  | E_StrLangDir (e1, e2, e3) ->
      ((expr_has_ungrouped_var is_grp e1) ||
         (expr_has_ungrouped_var is_grp e2))
        || (expr_has_ungrouped_var is_grp e3)
  | uu___ -> false
let select_item_has_aggregate (item : select_item) : Prims.bool=
  match item with
  | SI_Var uu___ -> false
  | SI_Expr (e, uu___) -> expr_has_aggregate e
let select_has_aggregates (sel : select_clause) : Prims.bool=
  match sel with
  | Select_All -> false
  | Select_Vars items ->
      FStar_List_Tot_Base.existsb select_item_has_aggregate items
let compare_on_condition
  (base : RDF_Term.wf_iri FStar_Pervasives_Native.option)
  (c : order_condition) (mu1 : RDF_Graph_Executable.solution_mapping)
  (mu2 : RDF_Graph_Executable.solution_mapping) : Prims.int=
  match c with
  | OC_Asc e ->
      sparql_order (eval_expr_with_base base e mu1)
        (eval_expr_with_base base e mu2)
  | OC_Desc e ->
      sparql_order (eval_expr_with_base base e mu2)
        (eval_expr_with_base base e mu1)
let rec compare_on_conditions
  (base : RDF_Term.wf_iri FStar_Pervasives_Native.option)
  (conds : order_condition Prims.list)
  (mu1 : RDF_Graph_Executable.solution_mapping)
  (mu2 : RDF_Graph_Executable.solution_mapping) : Prims.int=
  match conds with
  | [] -> Prims.int_zero
  | c::rest ->
      let r = compare_on_condition base c mu1 mu2 in
      if r <> Prims.int_zero
      then r
      else compare_on_conditions base rest mu1 mu2
let sort_solutions (base : RDF_Term.wf_iri FStar_Pervasives_Native.option)
  (conds : order_condition Prims.list) (omega : solution_sequence) :
  solution_sequence=
  FStar_List_Tot_Base.sortWith (compare_on_conditions base conds) omega
let rec sm_submap (m1 : RDF_Graph_Executable.solution_mapping)
  (m2 : RDF_Graph_Executable.solution_mapping) : Prims.bool=
  match m1 with
  | [] -> true
  | (v, t)::r ->
      (match sm_lookup v m2 with
       | FStar_Pervasives_Native.Some t2 ->
           (RDF_Term.rdf_term_eq t t2) && (sm_submap r m2)
       | FStar_Pervasives_Native.None -> false)
let sm_equal (m1 : RDF_Graph_Executable.solution_mapping)
  (m2 : RDF_Graph_Executable.solution_mapping) : Prims.bool=
  (sm_submap m1 m2) && (sm_submap m2 m1)
let rec sm_mem (mu : RDF_Graph_Executable.solution_mapping)
  (l : RDF_Graph_Executable.solution_mapping Prims.list) : Prims.bool=
  match l with | [] -> false | hd::tl -> (sm_equal mu hd) || (sm_mem mu tl)
let rec list_deduplicate_sm_acc
  (l : RDF_Graph_Executable.solution_mapping Prims.list)
  (acc : RDF_Graph_Executable.solution_mapping Prims.list) :
  RDF_Graph_Executable.solution_mapping Prims.list=
  match l with
  | [] -> acc
  | x::xs ->
      if sm_mem x xs
      then list_deduplicate_sm_acc xs acc
      else list_deduplicate_sm_acc xs (x :: acc)
let list_deduplicate_sm
  (l : RDF_Graph_Executable.solution_mapping Prims.list) :
  RDF_Graph_Executable.solution_mapping Prims.list=
  FStar_List_Tot_Base.rev (list_deduplicate_sm_acc l [])
let distinct_solutions (omega : solution_sequence) : solution_sequence=
  list_deduplicate_sm omega
let reduced_solutions (omega : solution_sequence) : solution_sequence= omega
let slice_solutions (offset : Prims.nat FStar_Pervasives_Native.option)
  (limit : Prims.nat FStar_Pervasives_Native.option)
  (omega : solution_sequence) : solution_sequence=
  let after_offset =
    match offset with
    | FStar_Pervasives_Native.None -> omega
    | FStar_Pervasives_Native.Some n -> list_drop n omega in
  match limit with
  | FStar_Pervasives_Native.None -> after_offset
  | FStar_Pervasives_Native.Some n -> list_take n after_offset
let rec project (vars : var_name Prims.list)
  (mu : RDF_Graph_Executable.solution_mapping) :
  RDF_Graph_Executable.solution_mapping=
  match mu with
  | [] -> []
  | (v, t)::rest ->
      if FStar_List_Tot_Base.mem v vars
      then (v, t) :: (project vars rest)
      else project vars rest
let rec project_solutions_acc (vars : var_name Prims.list)
  (omega : solution_sequence) (acc : solution_sequence) : solution_sequence=
  match omega with
  | [] -> acc
  | mu::rest -> project_solutions_acc vars rest ((project vars mu) :: acc)
let project_solutions (vars : var_name Prims.list)
  (omega : solution_sequence) : solution_sequence=
  FStar_List_Tot_Base.rev (project_solutions_acc vars omega [])
let eval_select_item (base : RDF_Term.wf_iri FStar_Pervasives_Native.option)
  (row : Prims.string) (occ : Prims.string) (item : select_item)
  (mu : RDF_Graph_Executable.solution_mapping) (g : RDF_Graph.rdf_graph) :
  RDF_Graph_Executable.solution_mapping=
  match item with
  | SI_Var uu___ -> mu
  | SI_Expr (e, v) ->
      let r = eval_expr_with_base base e (fx_ctx_put row occ mu) in
      (match er_to_term r with
       | FStar_Pervasives_Native.Some t -> sm_bind v t mu
       | FStar_Pervasives_Native.None -> mu)
let rec eval_select_items_row
  (base : RDF_Term.wf_iri FStar_Pervasives_Native.option)
  (row : Prims.string) (i : Prims.nat) (items : select_item Prims.list)
  (mu : RDF_Graph_Executable.solution_mapping) (g : RDF_Graph.rdf_graph) :
  RDF_Graph_Executable.solution_mapping=
  match items with
  | [] -> mu
  | item::rest ->
      let mu' = eval_select_item base row (Prims.string_of_int i) item mu g in
      eval_select_items_row base row (i + Prims.int_one) rest mu' g
let rec eval_select_items_rows_acc
  (base : RDF_Term.wf_iri FStar_Pervasives_Native.option) (r : Prims.nat)
  (omega : solution_sequence) (items : select_item Prims.list)
  (g : RDF_Graph.rdf_graph) (acc : solution_sequence) : solution_sequence=
  match omega with
  | [] -> acc
  | mu::rest ->
      let mu' =
        eval_select_items_row base (Prims.string_of_int r) Prims.int_zero
          items mu g in
      eval_select_items_rows_acc base (r + Prims.int_one) rest items g (mu'
        :: acc)
let eval_select_items_rows
  (base : RDF_Term.wf_iri FStar_Pervasives_Native.option) (r : Prims.nat)
  (omega : solution_sequence) (items : select_item Prims.list)
  (g : RDF_Graph.rdf_graph) : solution_sequence=
  FStar_List_Tot_Base.rev
    (eval_select_items_rows_acc base r omega items g [])
let eval_select_items (base : RDF_Term.wf_iri FStar_Pervasives_Native.option)
  (items : select_item Prims.list) (omega : solution_sequence)
  (g : RDF_Graph.rdf_graph) : solution_sequence=
  eval_select_items_rows base Prims.int_zero omega items g
let select_item_vars (items : select_item Prims.list) : var_name Prims.list=
  FStar_List_Tot_Base.map
    (fun item -> match item with | SI_Var v -> v | SI_Expr (uu___, v) -> v)
    items
let rec rewrite_query_bnode_term (pt : pattern_term) : pattern_term=
  match pt with
  | PT_BNode b -> PT_Var (Prims.strcat "_bnode_" b)
  | PT_TripleTerm (s, p, o) ->
      PT_TripleTerm
        ((rewrite_query_bnode_term s), (rewrite_query_bnode_term p),
          (rewrite_query_bnode_term o))
  | uu___ -> pt
let rewrite_query_bnode_subject (ps : pattern_subject) : pattern_subject=
  match ps with
  | PS_BNode b -> PS_Var (Prims.strcat "_bnode_" b)
  | uu___ -> ps
let rewrite_query_bnode_tp (tp : triple_pattern) : triple_pattern=
  {
    tp_s = (rewrite_query_bnode_subject tp.tp_s);
    tp_p = (rewrite_query_bnode_term tp.tp_p);
    tp_o = (rewrite_query_bnode_term tp.tp_o)
  }
let rec rewrite_query_bnodes_pattern (p : group_graph_pattern) :
  group_graph_pattern=
  match p with
  | GP_BGP bgp1 ->
      GP_BGP (FStar_List_Tot_Base.map rewrite_query_bnode_tp bgp1)
  | GP_Join (p1, p2) ->
      GP_Join
        ((rewrite_query_bnodes_pattern p1),
          (rewrite_query_bnodes_pattern p2))
  | GP_LeftJoin (p1, p2, e) ->
      GP_LeftJoin
        ((rewrite_query_bnodes_pattern p1),
          (rewrite_query_bnodes_pattern p2), e)
  | GP_Filter (e, p1) -> GP_Filter (e, (rewrite_query_bnodes_pattern p1))
  | GP_Union (p1, p2) ->
      GP_Union
        ((rewrite_query_bnodes_pattern p1),
          (rewrite_query_bnodes_pattern p2))
  | GP_Graph (gt, p1) ->
      GP_Graph
        ((rewrite_query_bnode_term gt), (rewrite_query_bnodes_pattern p1))
  | GP_Minus (p1, p2) ->
      GP_Minus
        ((rewrite_query_bnodes_pattern p1),
          (rewrite_query_bnodes_pattern p2))
  | GP_Lateral (p1, p2) ->
      GP_Lateral
        ((rewrite_query_bnodes_pattern p1),
          (rewrite_query_bnodes_pattern p2))
  | GP_Bind (e, v, p1) -> GP_Bind (e, v, (rewrite_query_bnodes_pattern p1))
  | GP_SubSelect q ->
      GP_SubSelect
        {
          q_base = (q.q_base);
          q_prefixes = (q.q_prefixes);
          q_form = (q.q_form);
          q_dataset = (q.q_dataset);
          q_pattern = (rewrite_query_bnodes_pattern q.q_pattern);
          q_group_by = (q.q_group_by);
          q_having = (q.q_having);
          q_modifier = (q.q_modifier);
          q_values = (q.q_values)
        }
  | GP_PropertyPath (s, pp, o) ->
      GP_PropertyPath
        ((rewrite_query_bnode_subject s), pp, (rewrite_query_bnode_term o))
  | uu___ -> p
let is_synthetic_bnode_var (v : var_name) : Prims.bool=
  string_starts_with v "_bnode_"
let strip_synthetic_bnode_vars_mu
  (mu : RDF_Graph_Executable.solution_mapping) :
  RDF_Graph_Executable.solution_mapping=
  FStar_List_Tot_Base.filter
    (fun uu___ ->
       match uu___ with
       | (v, uu___1) -> Prims.op_Negation (is_synthetic_bnode_var v)) mu
let strip_synthetic_bnode_vars (omega : solution_sequence) :
  solution_sequence=
  FStar_List_Tot_Base.map strip_synthetic_bnode_vars_mu omega
let rec q_dataset_default_iris (dcs : dataset_clause Prims.list) :
  RDF_Term.wf_iri Prims.list=
  match dcs with
  | [] -> []
  | (DC_Default i)::rest -> i :: (q_dataset_default_iris rest)
  | (DC_Named uu___)::rest -> q_dataset_default_iris rest
let rec q_dataset_named_iris (dcs : dataset_clause Prims.list) :
  RDF_Term.wf_iri Prims.list=
  match dcs with
  | [] -> []
  | (DC_Named i)::rest -> i :: (q_dataset_named_iris rest)
  | (DC_Default uu___)::rest -> q_dataset_named_iris rest
let rec q_union_named_graphs_by_iri (iris : RDF_Term.wf_iri Prims.list)
  (named : RDF_Graph.named_graph Prims.list) : RDF_Graph.rdf_graph=
  match iris with
  | [] -> RDF_Graph.empty_graph
  | i::rest ->
      let g =
        match RDF_Graph.lookup_named_graph i named with
        | FStar_Pervasives_Native.Some g1 -> g1
        | FStar_Pervasives_Native.None -> RDF_Graph.empty_graph in
      RDF_Graph_Executable.graph_union g
        (q_union_named_graphs_by_iri rest named)
let rec q_named_graphs_by_iri (iris : RDF_Term.wf_iri Prims.list)
  (named : RDF_Graph.named_graph Prims.list) :
  RDF_Graph.named_graph Prims.list=
  match iris with
  | [] -> []
  | i::rest ->
      let g =
        match RDF_Graph.lookup_named_graph i named with
        | FStar_Pervasives_Native.Some g1 -> g1
        | FStar_Pervasives_Native.None -> RDF_Graph.empty_graph in
      { RDF_Graph.ng_name = i; RDF_Graph.ng_graph = g } ::
        (q_named_graphs_by_iri rest named)
let apply_query_dataset (dcs : dataset_clause Prims.list)
  (g : RDF_Graph.rdf_graph) (ds : RDF_Graph.rdf_dataset) :
  (RDF_Graph.rdf_graph * RDF_Graph.rdf_dataset)=
  match dcs with
  | [] -> (g, ds)
  | uu___ ->
      let def_iris = q_dataset_default_iris dcs in
      let nam_iris = q_dataset_named_iris dcs in
      let new_def =
        q_union_named_graphs_by_iri def_iris ds.RDF_Graph.ds_named in
      let new_named = q_named_graphs_by_iri nam_iris ds.RDF_Graph.ds_named in
      (new_def,
        { RDF_Graph.ds_default = new_def; RDF_Graph.ds_named = new_named })
let rec substitute_existentials
  (base : RDF_Term.wf_iri FStar_Pervasives_Native.option) (e : expr)
  (mu : RDF_Graph_Executable.solution_mapping) (g : RDF_Graph.rdf_graph)
  (ds : RDF_Graph.rdf_dataset) : expr=
  match e with
  | E_Exists p -> E_BoolLit (eval_exists base p mu g ds)
  | E_NotExists p ->
      E_BoolLit (Prims.op_Negation (eval_exists base p mu g ds))
  | E_Arith (op, e1, e2) ->
      E_Arith
        (op, (substitute_existentials base e1 mu g ds),
          (substitute_existentials base e2 mu g ds))
  | E_UnaryMinus e1 -> E_UnaryMinus (substitute_existentials base e1 mu g ds)
  | E_UnaryPlus e1 -> E_UnaryPlus (substitute_existentials base e1 mu g ds)
  | E_Compare (op, e1, e2) ->
      E_Compare
        (op, (substitute_existentials base e1 mu g ds),
          (substitute_existentials base e2 mu g ds))
  | E_And (e1, e2) ->
      E_And
        ((substitute_existentials base e1 mu g ds),
          (substitute_existentials base e2 mu g ds))
  | E_Or (e1, e2) ->
      E_Or
        ((substitute_existentials base e1 mu g ds),
          (substitute_existentials base e2 mu g ds))
  | E_Not e1 -> E_Not (substitute_existentials base e1 mu g ds)
  | E_IsIRI e1 -> E_IsIRI (substitute_existentials base e1 mu g ds)
  | E_IsBlank e1 -> E_IsBlank (substitute_existentials base e1 mu g ds)
  | E_IsLiteral e1 -> E_IsLiteral (substitute_existentials base e1 mu g ds)
  | E_IsNumeric e1 -> E_IsNumeric (substitute_existentials base e1 mu g ds)
  | E_Str e1 -> E_Str (substitute_existentials base e1 mu g ds)
  | E_Lang e1 -> E_Lang (substitute_existentials base e1 mu g ds)
  | E_Datatype e1 -> E_Datatype (substitute_existentials base e1 mu g ds)
  | E_IRI_fn e1 -> E_IRI_fn (substitute_existentials base e1 mu g ds)
  | E_HasLang e1 -> E_HasLang (substitute_existentials base e1 mu g ds)
  | E_HasLangDir e1 -> E_HasLangDir (substitute_existentials base e1 mu g ds)
  | E_LangDir e1 -> E_LangDir (substitute_existentials base e1 mu g ds)
  | E_StrDt (e1, e2) ->
      E_StrDt
        ((substitute_existentials base e1 mu g ds),
          (substitute_existentials base e2 mu g ds))
  | E_StrLang (e1, e2) ->
      E_StrLang
        ((substitute_existentials base e1 mu g ds),
          (substitute_existentials base e2 mu g ds))
  | E_StrLangDir (e1, e2, e3) ->
      E_StrLangDir
        ((substitute_existentials base e1 mu g ds),
          (substitute_existentials base e2 mu g ds),
          (substitute_existentials base e3 mu g ds))
  | E_If (c, t, f) ->
      E_If
        ((substitute_existentials base c mu g ds),
          (substitute_existentials base t mu g ds),
          (substitute_existentials base f mu g ds))
  | E_Coalesce es ->
      E_Coalesce (substitute_existentials_list base es mu g ds)
  | E_In (ev, es) ->
      E_In
        ((substitute_existentials base ev mu g ds),
          (substitute_existentials_list base es mu g ds))
  | E_NotIn (ev, es) ->
      E_NotIn
        ((substitute_existentials base ev mu g ds),
          (substitute_existentials_list base es mu g ds))
  | E_StrLen e1 -> E_StrLen (substitute_existentials base e1 mu g ds)
  | E_Substr (e1, e2, e3_opt) ->
      E_Substr
        ((substitute_existentials base e1 mu g ds),
          (substitute_existentials base e2 mu g ds),
          (substitute_existentials_opt base e3_opt mu g ds))
  | E_UCase e1 -> E_UCase (substitute_existentials base e1 mu g ds)
  | E_LCase e1 -> E_LCase (substitute_existentials base e1 mu g ds)
  | E_StrStarts (e1, e2) ->
      E_StrStarts
        ((substitute_existentials base e1 mu g ds),
          (substitute_existentials base e2 mu g ds))
  | E_StrEnds (e1, e2) ->
      E_StrEnds
        ((substitute_existentials base e1 mu g ds),
          (substitute_existentials base e2 mu g ds))
  | E_Contains (e1, e2) ->
      E_Contains
        ((substitute_existentials base e1 mu g ds),
          (substitute_existentials base e2 mu g ds))
  | E_StrBefore (e1, e2) ->
      E_StrBefore
        ((substitute_existentials base e1 mu g ds),
          (substitute_existentials base e2 mu g ds))
  | E_StrAfter (e1, e2) ->
      E_StrAfter
        ((substitute_existentials base e1 mu g ds),
          (substitute_existentials base e2 mu g ds))
  | E_Concat es -> E_Concat (substitute_existentials_list base es mu g ds)
  | E_EncodeForUri e1 ->
      E_EncodeForUri (substitute_existentials base e1 mu g ds)
  | E_Replace (e1, e2, e3, e4_opt) ->
      E_Replace
        ((substitute_existentials base e1 mu g ds),
          (substitute_existentials base e2 mu g ds),
          (substitute_existentials base e3 mu g ds),
          (substitute_existentials_opt base e4_opt mu g ds))
  | E_Regex (e1, e2, e3_opt) ->
      E_Regex
        ((substitute_existentials base e1 mu g ds),
          (substitute_existentials base e2 mu g ds),
          (substitute_existentials_opt base e3_opt mu g ds))
  | E_Abs e1 -> E_Abs (substitute_existentials base e1 mu g ds)
  | E_Round e1 -> E_Round (substitute_existentials base e1 mu g ds)
  | E_Ceil e1 -> E_Ceil (substitute_existentials base e1 mu g ds)
  | E_Floor e1 -> E_Floor (substitute_existentials base e1 mu g ds)
  | E_MD5 e1 -> E_MD5 (substitute_existentials base e1 mu g ds)
  | E_SHA1 e1 -> E_SHA1 (substitute_existentials base e1 mu g ds)
  | E_SHA256 e1 -> E_SHA256 (substitute_existentials base e1 mu g ds)
  | E_SHA384 e1 -> E_SHA384 (substitute_existentials base e1 mu g ds)
  | E_SHA512 e1 -> E_SHA512 (substitute_existentials base e1 mu g ds)
  | E_Year e1 -> E_Year (substitute_existentials base e1 mu g ds)
  | E_Month e1 -> E_Month (substitute_existentials base e1 mu g ds)
  | E_Day e1 -> E_Day (substitute_existentials base e1 mu g ds)
  | E_Hours e1 -> E_Hours (substitute_existentials base e1 mu g ds)
  | E_Minutes e1 -> E_Minutes (substitute_existentials base e1 mu g ds)
  | E_Seconds e1 -> E_Seconds (substitute_existentials base e1 mu g ds)
  | E_Timezone e1 -> E_Timezone (substitute_existentials base e1 mu g ds)
  | E_Tz e1 -> E_Tz (substitute_existentials base e1 mu g ds)
  | E_SameTerm (e1, e2) ->
      E_SameTerm
        ((substitute_existentials base e1 mu g ds),
          (substitute_existentials base e2 mu g ds))
  | E_Aggregate (fn, dist, e1) ->
      E_Aggregate (fn, dist, (substitute_existentials base e1 mu g ds))
  | E_FunctionCall (iri, args) ->
      E_FunctionCall (iri, (substitute_existentials_list base args mu g ds))
  | E_TripleTerm (a, b, c) ->
      E_TripleTerm
        ((substitute_existentials base a mu g ds),
          (substitute_existentials base b mu g ds),
          (substitute_existentials base c mu g ds))
  | E_TTSubject e1 -> E_TTSubject (substitute_existentials base e1 mu g ds)
  | E_TTPredicate e1 ->
      E_TTPredicate (substitute_existentials base e1 mu g ds)
  | E_TTObject e1 -> E_TTObject (substitute_existentials base e1 mu g ds)
  | E_IsTriple e1 -> E_IsTriple (substitute_existentials base e1 mu g ds)
  | uu___ -> e
and substitute_existentials_list
  (base : RDF_Term.wf_iri FStar_Pervasives_Native.option)
  (es : expr Prims.list) (mu : RDF_Graph_Executable.solution_mapping)
  (g : RDF_Graph.rdf_graph) (ds : RDF_Graph.rdf_dataset) : expr Prims.list=
  match es with
  | [] -> []
  | hd::tl -> (substitute_existentials base hd mu g ds) ::
      (substitute_existentials_list base tl mu g ds)
and substitute_existentials_opt
  (base : RDF_Term.wf_iri FStar_Pervasives_Native.option)
  (eo : expr FStar_Pervasives_Native.option)
  (mu : RDF_Graph_Executable.solution_mapping) (g : RDF_Graph.rdf_graph)
  (ds : RDF_Graph.rdf_dataset) : expr FStar_Pervasives_Native.option=
  match eo with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some e ->
      FStar_Pervasives_Native.Some (substitute_existentials base e mu g ds)
and filter_solutions_with_graph
  (base : RDF_Term.wf_iri FStar_Pervasives_Native.option) (e : expr)
  (omega : solution_sequence) (g : RDF_Graph.rdf_graph)
  (ds : RDF_Graph.rdf_dataset) : solution_sequence=
  FStar_List_Tot_Base.filter
    (fun mu ->
       let e' = substitute_existentials base e mu g ds in
       eval_expr_ebv base e' mu) omega
and left_join_with_graph
  (base : RDF_Term.wf_iri FStar_Pervasives_Native.option)
  (omega1 : solution_sequence) (omega2 : solution_sequence)
  (filter_expr : expr) (g : RDF_Graph.rdf_graph) (ds : RDF_Graph.rdf_dataset)
  : solution_sequence=
  match (omega1, omega2) with
  | ([], uu___) -> []
  | (uu___, []) -> omega1
  | (mu1_0::uu___, mu2_0::uu___1) ->
      let vars = vars_intersect (sm_domain mu1_0) (sm_domain mu2_0) in
      if vars = []
      then
        RDF_List_Helpers.concatMap_tr
          (fun mu1 ->
             let joins =
               list_filter_map
                 (fun mu2 ->
                    if sm_compatible mu1 mu2
                    then
                      let merged = sm_merge mu1 mu2 in
                      let e' =
                        substitute_existentials base filter_expr merged g ds in
                      (if eval_expr_ebv base e' merged
                       then FStar_Pervasives_Native.Some merged
                       else FStar_Pervasives_Native.None)
                    else FStar_Pervasives_Native.None) omega2 in
             if (FStar_List_Tot_Base.length joins) > Prims.int_zero
             then joins
             else [mu1]) omega1
      else
        (let idx = build_join_index vars omega2 in
         RDF_List_Helpers.concatMap_tr
           (fun mu1 ->
              let candidates = join_candidates idx vars mu1 in
              let joins =
                list_filter_map
                  (fun mu2 ->
                     if sm_compatible mu1 mu2
                     then
                       let merged = sm_merge mu1 mu2 in
                       let e' =
                         substitute_existentials base filter_expr merged g ds in
                       (if eval_expr_ebv base e' merged
                        then FStar_Pervasives_Native.Some merged
                        else FStar_Pervasives_Native.None)
                     else FStar_Pervasives_Native.None) candidates in
              if (FStar_List_Tot_Base.length joins) > Prims.int_zero
              then joins
              else [mu1]) omega1)
and eval_pattern_store
  (base : RDF_Term.wf_iri FStar_Pervasives_Native.option)
  (p : group_graph_pattern) (gs : graph_store) (dss : rdf_dataset_store) :
  solution_sequence=
  match p with
  | GP_BGP bgp1 -> eval_bgp_store bgp1 gs
  | GP_Join (p1, GP_ServiceVar (v, inner, silent)) ->
      let omega1 = eval_pattern_store base p1 gs dss in
      RDF_List_Helpers.concatMap_tr
        (fun mu ->
           match sm_lookup v mu with
           | FStar_Pervasives_Native.Some (RDF_Term.T_IRI iri) ->
               if RDF_Term.is_iri iri
               then
                 (match service_endpoint_lookup iri with
                  | FStar_Pervasives_Native.Some remote_gs ->
                      let omega2 =
                        eval_pattern_store base inner remote_gs dss in
                      RDF_List_Helpers.concatMap_tr
                        (fun mu2 ->
                           if sm_compatible mu mu2
                           then [sm_merge mu mu2]
                           else []) omega2
                  | FStar_Pervasives_Native.None ->
                      if silent then [mu] else [])
               else if silent then [mu] else []
           | uu___ -> if silent then [mu] else []) omega1
  | GP_Join (GP_ServiceVar (v, inner, silent), p2) ->
      let omega2 = eval_pattern_store base p2 gs dss in
      RDF_List_Helpers.concatMap_tr
        (fun mu ->
           match sm_lookup v mu with
           | FStar_Pervasives_Native.Some (RDF_Term.T_IRI iri) ->
               if RDF_Term.is_iri iri
               then
                 (match service_endpoint_lookup iri with
                  | FStar_Pervasives_Native.Some remote_gs ->
                      let omega1 =
                        eval_pattern_store base inner remote_gs dss in
                      RDF_List_Helpers.concatMap_tr
                        (fun mu1 ->
                           if sm_compatible mu mu1
                           then [sm_merge mu mu1]
                           else []) omega1
                  | FStar_Pervasives_Native.None ->
                      if silent then [mu] else [])
               else if silent then [mu] else []
           | uu___ -> if silent then [mu] else []) omega2
  | GP_Join (p1, p2) ->
      join (eval_pattern_store base p1 gs dss)
        (eval_pattern_store base p2 gs dss)
  | GP_LeftJoin (p1, p2, filter_e) ->
      left_join_with_graph base (eval_pattern_store base p1 gs dss)
        (eval_pattern_store base p2 gs dss) filter_e gs.gs_graph
        (store_to_dataset dss)
  | GP_Filter (e, p') ->
      let omega = eval_pattern_store base p' gs dss in
      filter_solutions_with_graph base e omega gs.gs_graph
        (store_to_dataset dss)
  | GP_Union (p1, p2) ->
      union (eval_pattern_store base p1 gs dss)
        (eval_pattern_store base p2 gs dss)
  | GP_Minus (p1, p2) ->
      minus (eval_pattern_store base p1 gs dss)
        (eval_pattern_store base p2 gs dss)
  | GP_Lateral (p1, p2) ->
      let omega1 = eval_pattern_store base p1 gs dss in
      RDF_List_Helpers.concatMap_tr
        (fun mu1 ->
           let p2' = lateral_substitute mu1 p2 in
           let omega2 =
             eval_select_query (lateral_wrap_as_query p2') gs.gs_graph
               (store_to_dataset dss) in
           list_filter_map
             (fun mu2 ->
                if sm_compatible mu1 mu2
                then FStar_Pervasives_Native.Some (sm_merge mu1 mu2)
                else FStar_Pervasives_Native.None) omega2) omega1
  | GP_Empty -> [sm_empty]
  | GP_Bind (e, v, p') ->
      let omega = eval_pattern_store base p' gs dss in
      fx_bind_rows base e v omega Prims.int_zero
  | GP_Values (vars, rows) -> eval_values vars rows
  | GP_Graph (gt, p') ->
      (match gt with
       | PT_IRI name ->
           (match lookup_named_store name dss.dss_named with
            | FStar_Pervasives_Native.Some ngs ->
                eval_pattern_store base p' ngs dss
            | FStar_Pervasives_Native.None -> [])
       | PT_Var v ->
           RDF_List_Helpers.concatMap_tr
             (fun ngs ->
                let ng_results = eval_pattern_store base p' ngs.ngs_store dss in
                if RDF_Term.is_iri ngs.ngs_name
                then
                  RDF_List_Helpers.concatMap_tr
                    (fun mu ->
                       match sm_bind_if_compatible v
                               (RDF_Term.T_IRI (ngs.ngs_name)) mu
                       with
                       | FStar_Pervasives_Native.Some mu' -> [mu']
                       | FStar_Pervasives_Native.None -> []) ng_results
                else ng_results) dss.dss_named
       | uu___ -> eval_pattern_store base p' gs dss)
  | GP_Service (iri, p', silent) ->
      (match service_endpoint_lookup iri with
       | FStar_Pervasives_Native.Some remote_gs ->
           eval_pattern_store base p' remote_gs dss
       | FStar_Pervasives_Native.None -> if silent then [[]] else [])
  | GP_ServiceVar (uu___, uu___1, silent) -> if silent then [[]] else []
  | GP_SubSelect q -> eval_select_query q gs.gs_graph (store_to_dataset dss)
  | GP_PropertyPath (ps, pp, pt) ->
      let pairs = eval_property_path_fwd pp gs.gs_graph in
      let pairs1 =
        match pp with
        | PP_ZeroOrMore uu___ ->
            let constant_terms =
              RDF_List_Helpers.append_tr
                (match ps with
                 | PS_IRI i -> [RDF_Term.T_IRI i]
                 | PS_BNode b -> [RDF_Term.T_BNode b]
                 | PS_Var uu___1 -> []
                 | PS_TripleTerm (uu___1, uu___2, uu___3) -> [])
                (match pt with
                 | PT_IRI i -> [RDF_Term.T_IRI i]
                 | PT_BNode b -> [RDF_Term.T_BNode b]
                 | PT_Literal l -> [RDF_Term.T_Literal l]
                 | PT_Var uu___1 -> []
                 | PT_TripleTerm (uu___1, uu___2, uu___3) -> []) in
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
        | PP_ZeroOrOne uu___ ->
            let constant_terms =
              RDF_List_Helpers.append_tr
                (match ps with
                 | PS_IRI i -> [RDF_Term.T_IRI i]
                 | PS_BNode b -> [RDF_Term.T_BNode b]
                 | PS_Var uu___1 -> []
                 | PS_TripleTerm (uu___1, uu___2, uu___3) -> [])
                (match pt with
                 | PT_IRI i -> [RDF_Term.T_IRI i]
                 | PT_BNode b -> [RDF_Term.T_BNode b]
                 | PT_Literal l -> [RDF_Term.T_Literal l]
                 | PT_Var uu___1 -> []
                 | PT_TripleTerm (uu___1, uu___2, uu___3) -> []) in
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
      path_result_to_solutions ps pt pairs1
and eval_exists (base : RDF_Term.wf_iri FStar_Pervasives_Native.option)
  (pattern : group_graph_pattern)
  (mu : RDF_Graph_Executable.solution_mapping) (graph : RDF_Graph.rdf_graph)
  (ds : RDF_Graph.rdf_dataset) : Prims.bool=
  let substituted = substitute_pattern mu pattern in
  (FStar_List_Tot_Base.length
     (eval_pattern_store base substituted
        (graph_to_store_for substituted graph)
        (dataset_to_store_for substituted ds)))
    > Prims.int_zero
and eval_select_query (q : query) (g : RDF_Graph.rdf_graph)
  (ds : RDF_Graph.rdf_dataset) : solution_sequence=
  let uu___ = apply_query_dataset q.q_dataset g ds in
  match uu___ with
  | (g1, ds1) ->
      let q1 =
        {
          q_base = (q.q_base);
          q_prefixes = (q.q_prefixes);
          q_form = (q.q_form);
          q_dataset = (q.q_dataset);
          q_pattern = (rewrite_query_bnodes_pattern q.q_pattern);
          q_group_by = (q.q_group_by);
          q_having = (q.q_having);
          q_modifier = (q.q_modifier);
          q_values = (q.q_values)
        } in
      let base = q1.q_base in
      (match q1.q_form with
       | QF_Select sel ->
           let omega0 =
             eval_pattern_store base q1.q_pattern
               (graph_to_store_for q1.q_pattern g1)
               (dataset_to_store_for q1.q_pattern ds1) in
           let omega =
             match q1.q_values with
             | FStar_Pervasives_Native.None -> omega0
             | FStar_Pervasives_Native.Some vals -> join omega0 vals in
           let needs_grouping =
             match q1.q_group_by with
             | FStar_Pervasives_Native.Some uu___1 -> true
             | FStar_Pervasives_Native.None -> select_has_aggregates sel in
           if needs_grouping
           then
             let groups =
               match q1.q_group_by with
               | FStar_Pervasives_Native.Some conds ->
                   group_by base conds omega
               | FStar_Pervasives_Native.None -> implicit_group omega in
             let filtered_groups =
               match q1.q_having with
               | FStar_Pervasives_Native.Some conditions ->
                   having_filter base conditions groups
               | FStar_Pervasives_Native.None -> groups in
             let omega' =
               match sel with
               | Select_Vars items ->
                   aggregate_groups base items filtered_groups
               | Select_All ->
                   let reps =
                     FStar_List_Tot_Base.map
                       (fun grp ->
                          match grp.g_solutions with
                          | mu::uu___1 -> mu
                          | [] -> sm_empty) filtered_groups in
                   strip_synthetic_bnode_vars reps in
             let ordered =
               match (q1.q_modifier).sm_order_by with
               | FStar_Pervasives_Native.None -> omega'
               | FStar_Pervasives_Native.Some o ->
                   sort_solutions base o omega' in
             let deduped =
               if (q1.q_modifier).sm_distinct
               then distinct_solutions ordered
               else
                 if (q1.q_modifier).sm_reduced
                 then reduced_solutions ordered
                 else ordered in
             slice_solutions (q1.q_modifier).sm_offset
               (q1.q_modifier).sm_limit deduped
           else
             (let omega' =
                match sel with
                | Select_Vars items -> eval_select_items base items omega g1
                | Select_All -> omega in
              let ordered =
                match (q1.q_modifier).sm_order_by with
                | FStar_Pervasives_Native.None -> omega'
                | FStar_Pervasives_Native.Some o ->
                    sort_solutions base o omega' in
              let projected =
                match sel with
                | Select_Vars items ->
                    project_solutions (select_item_vars items) ordered
                | Select_All -> strip_synthetic_bnode_vars ordered in
              let deduped =
                if (q1.q_modifier).sm_distinct
                then distinct_solutions projected
                else
                  if (q1.q_modifier).sm_reduced
                  then reduced_solutions projected
                  else projected in
              slice_solutions (q1.q_modifier).sm_offset
                (q1.q_modifier).sm_limit deduped)
       | QF_Construct uu___1 -> []
       | QF_Ask -> []
       | QF_Describe uu___1 -> [])
let eval_pattern (base : RDF_Term.wf_iri FStar_Pervasives_Native.option)
  (p : group_graph_pattern) (g : RDF_Graph.rdf_graph)
  (ds : RDF_Graph.rdf_dataset) : solution_sequence=
  eval_pattern_store base p (graph_to_store_for p g)
    (dataset_to_store_for p ds)
let rec collect_vars_from_row (row : RDF_Graph_Executable.solution_mapping)
  (acc : var_name Prims.list) : var_name Prims.list=
  match row with
  | [] -> acc
  | (v, uu___)::rest ->
      if FStar_List_Tot_Base.mem v acc
      then collect_vars_from_row rest acc
      else collect_vars_from_row rest (v :: acc)
let rec collect_distinct_vars_in_order_acc (omega : solution_sequence)
  (acc : var_name Prims.list) : var_name Prims.list=
  match omega with
  | [] -> acc
  | row::rest ->
      collect_distinct_vars_in_order_acc rest (collect_vars_from_row row acc)
let collect_distinct_vars_in_order (omega : solution_sequence) :
  var_name Prims.list=
  FStar_List_Tot_Base.rev (collect_distinct_vars_in_order_acc omega [])
let is_rewrite_internal_var (v : var_name) : Prims.bool=
  ((((((string_starts_with v "_sv_") || (string_starts_with v "_av_")) ||
        (string_starts_with v "_mc_"))
       || (string_starts_with v "_mxc_"))
      || (string_starts_with v "_mxqc1_"))
     || (string_starts_with v "_exc_"))
    || (string_starts_with v "_co_")
let strip_rewrite_internal_vars_mu
  (mu : RDF_Graph_Executable.solution_mapping) :
  RDF_Graph_Executable.solution_mapping=
  FStar_List_Tot_Base.filter
    (fun uu___ ->
       match uu___ with
       | (v, uu___1) -> Prims.op_Negation (is_rewrite_internal_var v)) mu
let strip_rewrite_internal_vars (omega : solution_sequence) :
  solution_sequence=
  FStar_List_Tot_Base.map strip_rewrite_internal_vars_mu omega
let eval_ask_query (q : query) (g : RDF_Graph.rdf_graph)
  (ds : RDF_Graph.rdf_dataset) : Prims.bool=
  let uu___ = apply_query_dataset q.q_dataset g ds in
  match uu___ with
  | (g1, ds1) ->
      let base = q.q_base in
      (match q.q_form with
       | QF_Ask ->
           let omega0 = eval_pattern base q.q_pattern g1 ds1 in
           let omega =
             match q.q_values with
             | FStar_Pervasives_Native.None -> omega0
             | FStar_Pervasives_Native.Some vals -> join omega0 vals in
           (match omega with | [] -> false | uu___1 -> true)
       | uu___1 -> false)
let fresh_bnode_for (sol_ix : Prims.nat) (template_label : Prims.string) :
  RDF_Term.bnode_id=
  Prims.strcat "tpl_"
    (Prims.strcat (Prims.string_of_int sol_ix)
       (Prims.strcat "_" template_label))
let construct_subject (ps : pattern_subject)
  (mu : RDF_Graph_Executable.solution_mapping) (sol_ix : Prims.nat) :
  RDF_Term.subject FStar_Pervasives_Native.option=
  match ps with
  | PS_IRI i -> FStar_Pervasives_Native.Some (RDF_Term.S_IRI i)
  | PS_BNode b ->
      FStar_Pervasives_Native.Some
        (RDF_Term.S_BNode (fresh_bnode_for sol_ix b))
  | PS_TripleTerm (uu___, uu___1, uu___2) -> FStar_Pervasives_Native.None
  | PS_Var v ->
      (match sm_lookup v mu with
       | FStar_Pervasives_Native.Some (RDF_Term.T_IRI i) ->
           FStar_Pervasives_Native.Some (RDF_Term.S_IRI i)
       | FStar_Pervasives_Native.Some (RDF_Term.T_BNode b) ->
           FStar_Pervasives_Native.Some (RDF_Term.S_BNode b)
       | FStar_Pervasives_Native.Some (RDF_Term.T_Literal uu___) ->
           FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some (RDF_Term.T_TripleTerm
           (uu___, uu___1, uu___2)) -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
let construct_predicate (pt : pattern_term)
  (mu : RDF_Graph_Executable.solution_mapping) :
  RDF_Term.wf_iri FStar_Pervasives_Native.option=
  match pt with
  | PT_IRI i -> FStar_Pervasives_Native.Some i
  | PT_BNode uu___ -> FStar_Pervasives_Native.None
  | PT_Literal uu___ -> FStar_Pervasives_Native.None
  | PT_TripleTerm (uu___, uu___1, uu___2) -> FStar_Pervasives_Native.None
  | PT_Var v ->
      (match sm_lookup v mu with
       | FStar_Pervasives_Native.Some (RDF_Term.T_IRI i) ->
           FStar_Pervasives_Native.Some i
       | uu___ -> FStar_Pervasives_Native.None)
let rec construct_object (pt : pattern_term)
  (mu : RDF_Graph_Executable.solution_mapping) (sol_ix : Prims.nat) :
  RDF_Term.rdf_term FStar_Pervasives_Native.option=
  match pt with
  | PT_IRI i -> FStar_Pervasives_Native.Some (RDF_Term.T_IRI i)
  | PT_BNode b ->
      FStar_Pervasives_Native.Some
        (RDF_Term.T_BNode (fresh_bnode_for sol_ix b))
  | PT_Literal l -> FStar_Pervasives_Native.Some (RDF_Term.T_Literal l)
  | PT_Var v -> sm_lookup v mu
  | PT_TripleTerm (ps, pp, po) ->
      (match construct_object ps mu sol_ix with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some sterm ->
           (match term_to_subject_opt sterm with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some ssub ->
                (match construct_object pp mu sol_ix with
                 | FStar_Pervasives_Native.Some (RDF_Term.T_IRI ppi) ->
                     (match construct_object po mu sol_ix with
                      | FStar_Pervasives_Native.None ->
                          FStar_Pervasives_Native.None
                      | FStar_Pervasives_Native.Some oterm ->
                          FStar_Pervasives_Native.Some
                            (RDF_Term.T_TripleTerm (ssub, ppi, oterm)))
                 | uu___ -> FStar_Pervasives_Native.None)))
let instantiate_template (template : triple_pattern Prims.list)
  (mu : RDF_Graph_Executable.solution_mapping) (sol_ix : Prims.nat) :
  RDF_Triple.triple Prims.list=
  FStar_List_Tot_Base.fold_left
    (fun acc tp ->
       match construct_subject tp.tp_s mu sol_ix with
       | FStar_Pervasives_Native.None -> acc
       | FStar_Pervasives_Native.Some s ->
           (match construct_predicate tp.tp_p mu with
            | FStar_Pervasives_Native.None -> acc
            | FStar_Pervasives_Native.Some p ->
                (match construct_object tp.tp_o mu sol_ix with
                 | FStar_Pervasives_Native.None -> acc
                 | FStar_Pervasives_Native.Some o ->
                     { RDF_Triple.s = s; RDF_Triple.p = p; RDF_Triple.o = o }
                     :: acc))) [] template
let rec instantiate_solutions (template : triple_pattern Prims.list)
  (mus : solution_sequence) (ix : Prims.nat) : RDF_Triple.triple Prims.list=
  match mus with
  | [] -> []
  | mu::rest ->
      let here = instantiate_template template mu ix in
      let later = instantiate_solutions template rest (ix + Prims.int_one) in
      FStar_List_Tot_Base.append here later
let dedup_triples (ts : RDF_Triple.triple Prims.list) :
  RDF_Triple.triple Prims.list=
  let acc =
    FStar_List_Tot_Base.fold_left
      (fun acc1 t -> if RDF_Graph.mem_triple t acc1 then acc1 else t :: acc1)
      [] ts in
  FStar_List_Tot_Base.rev acc
let eval_construct_query (q : query) (g : RDF_Graph.rdf_graph)
  (ds : RDF_Graph.rdf_dataset) : RDF_Triple.triple Prims.list=
  let uu___ = apply_query_dataset q.q_dataset g ds in
  match uu___ with
  | (g1, ds1) ->
      let q1 =
        {
          q_base = (q.q_base);
          q_prefixes = (q.q_prefixes);
          q_form = (q.q_form);
          q_dataset = (q.q_dataset);
          q_pattern = (rewrite_query_bnodes_pattern q.q_pattern);
          q_group_by = (q.q_group_by);
          q_having = (q.q_having);
          q_modifier = (q.q_modifier);
          q_values = (q.q_values)
        } in
      let base = q1.q_base in
      (match q1.q_form with
       | QF_Construct template ->
           let omega0 = eval_pattern base q1.q_pattern g1 ds1 in
           let omega =
             match q1.q_values with
             | FStar_Pervasives_Native.None -> omega0
             | FStar_Pervasives_Native.Some vals -> join omega0 vals in
           let limited =
             slice_solutions (q1.q_modifier).sm_offset
               (q1.q_modifier).sm_limit omega in
           dedup_triples
             (instantiate_solutions template limited Prims.int_zero)
       | uu___1 -> [])
type path_result = (RDF_Term.rdf_term * RDF_Term.rdf_term) Prims.list
let is_not_literal (t : RDF_Term.rdf_term) : Prims.bool=
  match t with | RDF_Term.T_Literal uu___ -> false | uu___ -> true
let path_pair_eq (p1 : (RDF_Term.rdf_term * RDF_Term.rdf_term))
  (p2 : (RDF_Term.rdf_term * RDF_Term.rdf_term)) : Prims.bool=
  let uu___ = p1 in
  match uu___ with
  | (a1, b1) ->
      let uu___1 = p2 in
      (match uu___1 with
       | (a2, b2) ->
           (RDF_Term.rdf_term_eq a1 a2) && (RDF_Term.rdf_term_eq b1 b2))
let rec list_dedup_by :
  'a . ('a -> 'a -> Prims.bool) -> 'a Prims.list -> 'a Prims.list =
  fun eq l ->
    match l with
    | [] -> []
    | x::xs ->
        if FStar_List_Tot_Base.existsb (eq x) xs
        then list_dedup_by eq xs
        else x :: (list_dedup_by eq xs)
let dedup_path (pairs : path_result) : path_result=
  list_dedup_by path_pair_eq pairs
let rec negated_direct_iris (ps : property_path Prims.list) :
  RDF_Term.wf_iri Prims.list=
  match ps with
  | [] -> []
  | (PP_IRI i)::rest -> i :: (negated_direct_iris rest)
  | uu___::rest -> negated_direct_iris rest
let rec negated_inverse_iris (ps : property_path Prims.list) :
  RDF_Term.wf_iri Prims.list=
  match ps with
  | [] -> []
  | (PP_Inverse (PP_IRI i))::rest -> i :: (negated_inverse_iris rest)
  | uu___::rest -> negated_inverse_iris rest
let rec iri_in_list (iri : RDF_Term.wf_iri)
  (iris : RDF_Term.wf_iri Prims.list) : Prims.bool=
  match iris with
  | [] -> false
  | hd::tl -> if hd = iri then true else iri_in_list iri tl
let graph_nodes (g : RDF_Graph.rdf_graph) : RDF_Term.rdf_term Prims.list=
  let subj_nodes =
    FStar_List_Tot_Base.map (fun t -> subject_to_term t.RDF_Triple.s) g in
  let obj_nodes = FStar_List_Tot_Base.map (fun t -> t.RDF_Triple.o) g in
  let pairs =
    dedup_path
      (FStar_List_Tot_Base.map (fun n -> (n, n))
         (RDF_List_Helpers.append_tr subj_nodes obj_nodes)) in
  FStar_List_Tot_Base.map FStar_Pervasives_Native.fst pairs
let rec eval_property_path (p : property_path) (g : RDF_Graph.rdf_graph) :
  path_result=
  match p with
  | PP_IRI iri ->
      RDF_List_Helpers.concatMap_tr
        (fun t ->
           if t.RDF_Triple.p = iri
           then [((subject_to_term t.RDF_Triple.s), (t.RDF_Triple.o))]
           else []) g
  | PP_Inverse pp ->
      let pairs = eval_property_path pp g in
      RDF_List_Helpers.concatMap_tr
        (fun pair ->
           let uu___ = pair in
           match uu___ with
           | (s, o) -> if is_not_literal o then [(o, s)] else []) pairs
  | PP_Sequence (p1, p2) ->
      let r1 = eval_property_path p1 g in
      let r2 = eval_property_path p2 g in
      RDF_List_Helpers.concatMap_tr
        (fun pair1 ->
           let uu___ = pair1 in
           match uu___ with
           | (s, mid1) ->
               RDF_List_Helpers.concatMap_tr
                 (fun pair2 ->
                    let uu___1 = pair2 in
                    match uu___1 with
                    | (mid2, o) ->
                        if RDF_Term.rdf_term_eq mid1 mid2
                        then [(s, o)]
                        else []) r2) r1
  | PP_Alternative (p1, p2) ->
      RDF_List_Helpers.append_tr (eval_property_path p1 g)
        (eval_property_path p2 g)
  | PP_ZeroOrOne pp ->
      let reflexive =
        FStar_List_Tot_Base.map (fun n -> (n, n)) (graph_nodes g) in
      let step = eval_property_path pp g in
      dedup_path (RDF_List_Helpers.append_tr reflexive step)
  | PP_ZeroOrMore pp ->
      let nodes = graph_nodes g in
      let reflexive = FStar_List_Tot_Base.map (fun n -> (n, n)) nodes in
      let step = eval_property_path pp g in
      let extend current =
        let new_pairs =
          RDF_List_Helpers.concatMap_tr
            (fun pair1 ->
               let uu___ = pair1 in
               match uu___ with
               | (s, mid) ->
                   RDF_List_Helpers.concatMap_tr
                     (fun pair2 ->
                        let uu___1 = pair2 in
                        match uu___1 with
                        | (mid2, o) ->
                            if RDF_Term.rdf_term_eq mid mid2
                            then [(s, o)]
                            else []) step) current in
        dedup_path (RDF_List_Helpers.append_tr current new_pairs) in
      let max_iter = FStar_List_Tot_Base.length nodes in
      let rec fixpoint current fuel =
        if fuel = Prims.int_zero
        then current
        else
          (let next = extend current in
           if
             (FStar_List_Tot_Base.length next) =
               (FStar_List_Tot_Base.length current)
           then current
           else fixpoint next (fuel - Prims.int_one)) in
      fixpoint (dedup_path (RDF_List_Helpers.append_tr reflexive step))
        max_iter
  | PP_OneOrMore pp ->
      let nodes = graph_nodes g in
      let step = eval_property_path pp g in
      let extend current =
        let new_pairs =
          RDF_List_Helpers.concatMap_tr
            (fun pair1 ->
               let uu___ = pair1 in
               match uu___ with
               | (s, mid) ->
                   RDF_List_Helpers.concatMap_tr
                     (fun pair2 ->
                        let uu___1 = pair2 in
                        match uu___1 with
                        | (mid2, o) ->
                            if RDF_Term.rdf_term_eq mid mid2
                            then [(s, o)]
                            else []) step) current in
        dedup_path (RDF_List_Helpers.append_tr current new_pairs) in
      let max_iter = FStar_List_Tot_Base.length nodes in
      let rec fixpoint current fuel =
        if fuel = Prims.int_zero
        then current
        else
          (let next = extend current in
           if
             (FStar_List_Tot_Base.length next) =
               (FStar_List_Tot_Base.length current)
           then current
           else fixpoint next (fuel - Prims.int_one)) in
      fixpoint step max_iter
  | PP_NegatedSet ps ->
      let excluded_direct = negated_direct_iris ps in
      let excluded_inverse = negated_inverse_iris ps in
      let has_direct =
        (FStar_List_Tot_Base.length excluded_direct) > Prims.int_zero in
      let has_inverse =
        (FStar_List_Tot_Base.length excluded_inverse) > Prims.int_zero in
      let direct_pairs =
        if has_inverse && (Prims.op_Negation has_direct)
        then []
        else
          RDF_List_Helpers.concatMap_tr
            (fun t ->
               if iri_in_list t.RDF_Triple.p excluded_direct
               then []
               else [((subject_to_term t.RDF_Triple.s), (t.RDF_Triple.o))]) g in
      let inverse_pairs =
        if has_direct && (Prims.op_Negation has_inverse)
        then []
        else
          RDF_List_Helpers.concatMap_tr
            (fun t ->
               if iri_in_list t.RDF_Triple.p excluded_inverse
               then []
               else [((t.RDF_Triple.o), (subject_to_term t.RDF_Triple.s))]) g in
      RDF_List_Helpers.append_tr direct_pairs inverse_pairs
let () = eval_property_path_fwd_ref := eval_property_path
type numeric_precision =
  | NP_Integer 
  | NP_Decimal 
  | NP_Float 
  | NP_Double 
let uu___is_NP_Integer (projectee : numeric_precision) : Prims.bool=
  match projectee with | NP_Integer -> true | uu___ -> false
let uu___is_NP_Decimal (projectee : numeric_precision) : Prims.bool=
  match projectee with | NP_Decimal -> true | uu___ -> false
let uu___is_NP_Float (projectee : numeric_precision) : Prims.bool=
  match projectee with | NP_Float -> true | uu___ -> false
let uu___is_NP_Double (projectee : numeric_precision) : Prims.bool=
  match projectee with | NP_Double -> true | uu___ -> false
let numeric_precision_of (dt : RDF_Term.wf_iri) :
  numeric_precision FStar_Pervasives_Native.option=
  if dt = RDF_Term.xsd_integer
  then FStar_Pervasives_Native.Some NP_Integer
  else
    if dt = RDF_Term.xsd_decimal
    then FStar_Pervasives_Native.Some NP_Decimal
    else
      if dt = xsd_float
      then FStar_Pervasives_Native.Some NP_Float
      else
        if dt = RDF_Term.xsd_double
        then FStar_Pervasives_Native.Some NP_Double
        else FStar_Pervasives_Native.None
let promote_numeric (a : numeric_precision) (b : numeric_precision) :
  numeric_precision=
  match (a, b) with
  | (NP_Double, uu___) -> NP_Double
  | (uu___, NP_Double) -> NP_Double
  | (NP_Float, uu___) -> NP_Float
  | (uu___, NP_Float) -> NP_Float
  | (NP_Decimal, uu___) -> NP_Decimal
  | (uu___, NP_Decimal) -> NP_Decimal
  | (NP_Integer, NP_Integer) -> NP_Integer
let promoted_datatype (p : numeric_precision) : RDF_Term.wf_iri=
  match p with
  | NP_Integer -> RDF_Term.xsd_integer
  | NP_Decimal -> RDF_Term.xsd_decimal
  | NP_Float -> xsd_float
  | NP_Double -> RDF_Term.xsd_double
type cast_target =
  | Cast_Integer 
  | Cast_Decimal 
  | Cast_Float 
  | Cast_Double 
  | Cast_String 
  | Cast_Boolean 
  | Cast_DateTime 
let uu___is_Cast_Integer (projectee : cast_target) : Prims.bool=
  match projectee with | Cast_Integer -> true | uu___ -> false
let uu___is_Cast_Decimal (projectee : cast_target) : Prims.bool=
  match projectee with | Cast_Decimal -> true | uu___ -> false
let uu___is_Cast_Float (projectee : cast_target) : Prims.bool=
  match projectee with | Cast_Float -> true | uu___ -> false
let uu___is_Cast_Double (projectee : cast_target) : Prims.bool=
  match projectee with | Cast_Double -> true | uu___ -> false
let uu___is_Cast_String (projectee : cast_target) : Prims.bool=
  match projectee with | Cast_String -> true | uu___ -> false
let uu___is_Cast_Boolean (projectee : cast_target) : Prims.bool=
  match projectee with | Cast_Boolean -> true | uu___ -> false
let uu___is_Cast_DateTime (projectee : cast_target) : Prims.bool=
  match projectee with | Cast_DateTime -> true | uu___ -> false
let xsd_cast (v : eval_result) (target : cast_target) :
  eval_result FStar_Pervasives_Native.option=
  match target with
  | Cast_Integer ->
      (match v with
       | ER_Num uu___ -> FStar_Pervasives_Native.Some v
       | ER_Bool true -> FStar_Pervasives_Native.Some (ER_Num Prims.int_one)
       | ER_Bool false ->
           FStar_Pervasives_Native.Some (ER_Num Prims.int_zero)
       | ER_Dec s ->
           (match parse_int_string s with
            | FStar_Pervasives_Native.Some n ->
                FStar_Pervasives_Native.Some (ER_Num n)
            | FStar_Pervasives_Native.None ->
                let chars = FStar_String.list_of_string s in
                let before_dot =
                  list_take_while
                    (fun c ->
                       c <> (FStar_Char.char_of_int (Prims.of_int (46))))
                    chars in
                (match parse_int_string
                         (FStar_String.string_of_list before_dot)
                 with
                 | FStar_Pervasives_Native.Some n ->
                     FStar_Pervasives_Native.Some (ER_Num n)
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.None))
       | ER_Dbl s ->
           (match parse_int_string s with
            | FStar_Pervasives_Native.Some n ->
                FStar_Pervasives_Native.Some (ER_Num n)
            | FStar_Pervasives_Native.None ->
                let chars = FStar_String.list_of_string s in
                let before_dot =
                  list_take_while
                    (fun c ->
                       c <> (FStar_Char.char_of_int (Prims.of_int (46))))
                    chars in
                (match parse_int_string
                         (FStar_String.string_of_list before_dot)
                 with
                 | FStar_Pervasives_Native.Some n ->
                     FStar_Pervasives_Native.Some (ER_Num n)
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.None))
       | ER_Term (RDF_Term.T_Literal l) ->
           if
             ((lit_datatype l) = RDF_Term.xsd_integer) ||
               ((lit_datatype l) = RDF_Term.xsd_string)
           then
             (match parse_int_string (lit_lexical l) with
              | FStar_Pervasives_Native.Some n ->
                  FStar_Pervasives_Native.Some (ER_Num n)
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
           else
             if (lit_datatype l) = RDF_Term.xsd_boolean
             then
               (if ((lit_lexical l) = "true") || ((lit_lexical l) = "1")
                then FStar_Pervasives_Native.Some (ER_Num Prims.int_one)
                else
                  if ((lit_lexical l) = "false") || ((lit_lexical l) = "0")
                  then FStar_Pervasives_Native.Some (ER_Num Prims.int_zero)
                  else FStar_Pervasives_Native.None)
             else
               if
                 (((lit_datatype l) = RDF_Term.xsd_decimal) ||
                    ((lit_datatype l) = RDF_Term.xsd_double))
                   || ((lit_datatype l) = xsd_float)
               then
                 (let chars = FStar_String.list_of_string (lit_lexical l) in
                  let before_dot =
                    list_take_while
                      (fun c ->
                         c <> (FStar_Char.char_of_int (Prims.of_int (46))))
                      chars in
                  match parse_int_string
                          (FStar_String.string_of_list before_dot)
                  with
                  | FStar_Pervasives_Native.Some n ->
                      FStar_Pervasives_Native.Some (ER_Num n)
                  | FStar_Pervasives_Native.None ->
                      FStar_Pervasives_Native.None)
               else FStar_Pervasives_Native.None
       | uu___ -> FStar_Pervasives_Native.None)
  | Cast_Decimal ->
      (match v with
       | ER_Dec uu___ -> FStar_Pervasives_Native.Some v
       | ER_Num n ->
           FStar_Pervasives_Native.Some
             (ER_Dec (Prims.strcat (Prims.string_of_int n) ".0"))
       | ER_Bool true -> FStar_Pervasives_Native.Some (ER_Dec "1.0")
       | ER_Bool false -> FStar_Pervasives_Native.Some (ER_Dec "0.0")
       | ER_Dbl s -> FStar_Pervasives_Native.Some (ER_Dec s)
       | ER_Term (RDF_Term.T_Literal l) ->
           if
             ((lit_datatype l) = RDF_Term.xsd_decimal) ||
               ((lit_datatype l) = RDF_Term.xsd_string)
           then FStar_Pervasives_Native.Some (ER_Dec (lit_lexical l))
           else
             if (lit_datatype l) = RDF_Term.xsd_integer
             then
               (match parse_int_string (lit_lexical l) with
                | FStar_Pervasives_Native.Some n ->
                    FStar_Pervasives_Native.Some
                      (ER_Dec (Prims.strcat (Prims.string_of_int n) ".0"))
                | FStar_Pervasives_Native.None ->
                    FStar_Pervasives_Native.None)
             else
               if (lit_datatype l) = RDF_Term.xsd_boolean
               then
                 (if ((lit_lexical l) = "true") || ((lit_lexical l) = "1")
                  then FStar_Pervasives_Native.Some (ER_Dec "1.0")
                  else
                    if ((lit_lexical l) = "false") || ((lit_lexical l) = "0")
                    then FStar_Pervasives_Native.Some (ER_Dec "0.0")
                    else FStar_Pervasives_Native.None)
               else FStar_Pervasives_Native.None
       | uu___ -> FStar_Pervasives_Native.None)
  | Cast_Double ->
      (match v with
       | ER_Dbl uu___ -> FStar_Pervasives_Native.Some v
       | ER_Num n ->
           FStar_Pervasives_Native.Some
             (ER_Dbl (Prims.strcat (Prims.string_of_int n) ".0E0"))
       | ER_Dec s -> FStar_Pervasives_Native.Some (ER_Dbl s)
       | ER_Bool true -> FStar_Pervasives_Native.Some (ER_Dbl "1.0E0")
       | ER_Bool false -> FStar_Pervasives_Native.Some (ER_Dbl "0.0E0")
       | ER_Term (RDF_Term.T_Literal l) ->
           if
             ((((lit_datatype l) = RDF_Term.xsd_double) ||
                 ((lit_datatype l) = xsd_float))
                || ((lit_datatype l) = RDF_Term.xsd_decimal))
               || ((lit_datatype l) = RDF_Term.xsd_string)
           then FStar_Pervasives_Native.Some (ER_Dbl (lit_lexical l))
           else
             if (lit_datatype l) = RDF_Term.xsd_integer
             then
               (match parse_int_string (lit_lexical l) with
                | FStar_Pervasives_Native.Some n ->
                    FStar_Pervasives_Native.Some
                      (ER_Dbl (Prims.strcat (Prims.string_of_int n) ".0E0"))
                | FStar_Pervasives_Native.None ->
                    FStar_Pervasives_Native.None)
             else
               if (lit_datatype l) = RDF_Term.xsd_boolean
               then
                 (if ((lit_lexical l) = "true") || ((lit_lexical l) = "1")
                  then FStar_Pervasives_Native.Some (ER_Dbl "1.0E0")
                  else
                    if ((lit_lexical l) = "false") || ((lit_lexical l) = "0")
                    then FStar_Pervasives_Native.Some (ER_Dbl "0.0E0")
                    else FStar_Pervasives_Native.None)
               else FStar_Pervasives_Native.None
       | uu___ -> FStar_Pervasives_Native.None)
  | Cast_Float ->
      (match v with
       | ER_Dbl uu___ -> FStar_Pervasives_Native.Some v
       | ER_Num n ->
           FStar_Pervasives_Native.Some
             (ER_Dbl (Prims.strcat (Prims.string_of_int n) ".0E0"))
       | ER_Dec s -> FStar_Pervasives_Native.Some (ER_Dbl s)
       | ER_Bool true -> FStar_Pervasives_Native.Some (ER_Dbl "1.0E0")
       | ER_Bool false -> FStar_Pervasives_Native.Some (ER_Dbl "0.0E0")
       | ER_Term (RDF_Term.T_Literal l) ->
           if
             ((((lit_datatype l) = RDF_Term.xsd_double) ||
                 ((lit_datatype l) = xsd_float))
                || ((lit_datatype l) = RDF_Term.xsd_decimal))
               || ((lit_datatype l) = RDF_Term.xsd_string)
           then FStar_Pervasives_Native.Some (ER_Dbl (lit_lexical l))
           else
             if (lit_datatype l) = RDF_Term.xsd_integer
             then
               (match parse_int_string (lit_lexical l) with
                | FStar_Pervasives_Native.Some n ->
                    FStar_Pervasives_Native.Some
                      (ER_Dbl (Prims.strcat (Prims.string_of_int n) ".0E0"))
                | FStar_Pervasives_Native.None ->
                    FStar_Pervasives_Native.None)
             else
               if (lit_datatype l) = RDF_Term.xsd_boolean
               then
                 (if ((lit_lexical l) = "true") || ((lit_lexical l) = "1")
                  then FStar_Pervasives_Native.Some (ER_Dbl "1.0E0")
                  else
                    if ((lit_lexical l) = "false") || ((lit_lexical l) = "0")
                    then FStar_Pervasives_Native.Some (ER_Dbl "0.0E0")
                    else FStar_Pervasives_Native.None)
               else FStar_Pervasives_Native.None
       | uu___ -> FStar_Pervasives_Native.None)
  | Cast_String ->
      (match v with
       | ER_Num n ->
           FStar_Pervasives_Native.Some (er_string (Prims.string_of_int n))
       | ER_Dec s -> FStar_Pervasives_Native.Some (er_string s)
       | ER_Dbl s -> FStar_Pervasives_Native.Some (er_string s)
       | ER_Bool true -> FStar_Pervasives_Native.Some (er_string "true")
       | ER_Bool false -> FStar_Pervasives_Native.Some (er_string "false")
       | ER_Term (RDF_Term.T_IRI i) ->
           FStar_Pervasives_Native.Some (er_string (iri_to_string i))
       | ER_Term (RDF_Term.T_Literal l) ->
           FStar_Pervasives_Native.Some (er_string (lit_lexical l))
       | ER_Term (RDF_Term.T_BNode uu___) -> FStar_Pervasives_Native.None
       | ER_Term (RDF_Term.T_TripleTerm (uu___, uu___1, uu___2)) ->
           FStar_Pervasives_Native.None
       | ER_Error -> FStar_Pervasives_Native.None)
  | Cast_Boolean ->
      (match v with
       | ER_Bool uu___ -> FStar_Pervasives_Native.Some v
       | ER_Num n ->
           FStar_Pervasives_Native.Some (ER_Bool (n <> Prims.int_zero))
       | ER_Dec s ->
           FStar_Pervasives_Native.Some
             (ER_Bool ((s <> "0") && (s <> "0.0")))
       | ER_Dbl s ->
           FStar_Pervasives_Native.Some
             (ER_Bool (((s <> "0") && (s <> "0.0")) && (s <> "0.0E0")))
       | ER_Term (RDF_Term.T_Literal l) ->
           if (lit_datatype l) = RDF_Term.xsd_boolean
           then
             (if ((lit_lexical l) = "true") || ((lit_lexical l) = "1")
              then FStar_Pervasives_Native.Some (ER_Bool true)
              else
                if ((lit_lexical l) = "false") || ((lit_lexical l) = "0")
                then FStar_Pervasives_Native.Some (ER_Bool false)
                else FStar_Pervasives_Native.None)
           else
             if (lit_datatype l) = RDF_Term.xsd_string
             then
               (if ((lit_lexical l) = "true") || ((lit_lexical l) = "1")
                then FStar_Pervasives_Native.Some (ER_Bool true)
                else
                  if ((lit_lexical l) = "false") || ((lit_lexical l) = "0")
                  then FStar_Pervasives_Native.Some (ER_Bool false)
                  else FStar_Pervasives_Native.None)
             else
               if (lit_datatype l) = RDF_Term.xsd_integer
               then
                 (match parse_int_string (lit_lexical l) with
                  | FStar_Pervasives_Native.Some n ->
                      FStar_Pervasives_Native.Some
                        (ER_Bool (n <> Prims.int_zero))
                  | FStar_Pervasives_Native.None ->
                      FStar_Pervasives_Native.None)
               else FStar_Pervasives_Native.None
       | uu___ -> FStar_Pervasives_Native.None)
  | Cast_DateTime ->
      (match v with
       | ER_Term (RDF_Term.T_Literal l) ->
           if (lit_datatype l) = xsd_dateTime
           then FStar_Pervasives_Native.Some v
           else
             if (lit_datatype l) = RDF_Term.xsd_string
             then
               FStar_Pervasives_Native.Some
                 (ER_Term
                    (RDF_Term.T_Literal
                       {
                         RDF_Term.lexical_form = (lit_lexical l);
                         RDF_Term.datatype = xsd_dateTime;
                         RDF_Term.lang_tag = FStar_Pervasives_Native.None;
                         RDF_Term.direction = FStar_Pervasives_Native.None
                       }))
             else FStar_Pervasives_Native.None
       | uu___ -> FStar_Pervasives_Native.None)
let tp_has_var (v : var_name) (tp : triple_pattern) : Prims.bool=
  ((match tp.tp_s with | PS_Var sv -> sv = v | uu___ -> false) ||
     (match tp.tp_p with | PT_Var pv -> pv = v | uu___ -> false))
    || (match tp.tp_o with | PT_Var ov -> ov = v | uu___ -> false)
let rec bgp_has_var (v : var_name) (b : bgp) : Prims.bool=
  match b with
  | [] -> false
  | tp::rest -> (tp_has_var v tp) || (bgp_has_var v rest)
let rec ggp_has_var (v : var_name) (p : group_graph_pattern) : Prims.bool=
  match p with
  | GP_BGP b -> bgp_has_var v b
  | GP_Join (p1, p2) -> (ggp_has_var v p1) || (ggp_has_var v p2)
  | GP_LeftJoin (p1, p2, uu___) -> (ggp_has_var v p1) || (ggp_has_var v p2)
  | GP_Filter (uu___, p1) -> ggp_has_var v p1
  | GP_Union (p1, p2) -> (ggp_has_var v p1) || (ggp_has_var v p2)
  | GP_Graph (uu___, p1) -> ggp_has_var v p1
  | GP_Minus (p1, p2) -> (ggp_has_var v p1) || (ggp_has_var v p2)
  | GP_Lateral (p1, p2) -> (ggp_has_var v p1) || (ggp_has_var v p2)
  | GP_Bind (uu___, bv, p1) -> (bv = v) || (ggp_has_var v p1)
  | GP_Values (vars, uu___) ->
      FStar_List_Tot_Base.existsb (fun vn -> vn = v) vars
  | GP_Service (uu___, p1, uu___1) -> ggp_has_var v p1
  | GP_ServiceVar (sv, p1, uu___) -> (sv = v) || (ggp_has_var v p1)
  | GP_SubSelect q ->
      (match q.q_form with
       | QF_Select (Select_Vars items) ->
           FStar_List_Tot_Base.existsb
             (fun item ->
                match item with
                | SI_Var sv -> sv = v
                | SI_Expr (uu___, sv) -> sv = v) items
       | QF_Select (Select_All) -> false
       | uu___ -> false)
  | GP_PropertyPath (ps, uu___, pt) ->
      (match ps with | PS_Var sv -> sv = v | uu___1 -> false) ||
        ((match pt with | PT_Var tv -> tv = v | uu___1 -> false))
  | GP_Empty -> false
let filter_solutions (base : RDF_Term.wf_iri FStar_Pervasives_Native.option)
  (e : expr) (omega : solution_sequence) : solution_sequence=
  FStar_List_Tot_Base.filter (eval_expr_ebv base e) omega
let rec count_named_triples (ngs : RDF_Graph.named_graph Prims.list) :
  Prims.nat=
  match ngs with
  | [] -> Prims.int_zero
  | ng::rest ->
      (FStar_List_Tot_Base.length ng.RDF_Graph.ng_graph) +
        (count_named_triples rest)
let dataset_triple_count (ds : RDF_Graph.rdf_dataset) : Prims.nat=
  (FStar_List_Tot_Base.length ds.RDF_Graph.ds_default) +
    (count_named_triples ds.RDF_Graph.ds_named)
let ps_to_subject_concrete (ps : pattern_subject) :
  RDF_Term.subject FStar_Pervasives_Native.option=
  match ps with
  | PS_IRI i -> FStar_Pervasives_Native.Some (RDF_Term.S_IRI i)
  | PS_BNode b -> FStar_Pervasives_Native.Some (RDF_Term.S_BNode b)
  | PS_Var uu___ -> FStar_Pervasives_Native.None
  | PS_TripleTerm (uu___, uu___1, uu___2) -> FStar_Pervasives_Native.None
let pt_to_iri_concrete (pt : pattern_term) :
  RDF_Term.wf_iri FStar_Pervasives_Native.option=
  match pt with
  | PT_IRI i -> FStar_Pervasives_Native.Some i
  | uu___ -> FStar_Pervasives_Native.None
let rec pt_to_term_concrete (pt : pattern_term) :
  RDF_Term.rdf_term FStar_Pervasives_Native.option=
  match pt with
  | PT_IRI i -> FStar_Pervasives_Native.Some (RDF_Term.T_IRI i)
  | PT_BNode b -> FStar_Pervasives_Native.Some (RDF_Term.T_BNode b)
  | PT_Literal l -> FStar_Pervasives_Native.Some (RDF_Term.T_Literal l)
  | PT_Var uu___ -> FStar_Pervasives_Native.None
  | PT_TripleTerm (ps, pp, po) ->
      (match pt_to_term_concrete ps with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some sterm ->
           (match term_to_subject_opt sterm with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some ssub ->
                (match pt_to_iri_concrete pp with
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.None
                 | FStar_Pervasives_Native.Some ppi ->
                     (match pt_to_term_concrete po with
                      | FStar_Pervasives_Native.None ->
                          FStar_Pervasives_Native.None
                      | FStar_Pervasives_Native.Some oterm ->
                          FStar_Pervasives_Native.Some
                            (RDF_Term.T_TripleTerm (ssub, ppi, oterm))))))
let tp_to_triple_concrete (tp : triple_pattern) :
  RDF_Triple.triple FStar_Pervasives_Native.option=
  match ps_to_subject_concrete tp.tp_s with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some s ->
      (match pt_to_iri_concrete tp.tp_p with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some p ->
           (match pt_to_term_concrete tp.tp_o with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some o ->
                FStar_Pervasives_Native.Some
                  { RDF_Triple.s = s; RDF_Triple.p = p; RDF_Triple.o = o }))
let rec bgp_to_triples_concrete (b : bgp) : RDF_Triple.triple Prims.list=
  match b with
  | [] -> []
  | tp::rest ->
      let rest_ts = bgp_to_triples_concrete rest in
      (match tp_to_triple_concrete tp with
       | FStar_Pervasives_Native.None -> rest_ts
       | FStar_Pervasives_Native.Some t -> t :: rest_ts)
let rec collect_quads
  (outer : RDF_Term.wf_iri FStar_Pervasives_Native.option)
  (g : group_graph_pattern) :
  (RDF_Term.wf_iri FStar_Pervasives_Native.option * RDF_Triple.triple)
    Prims.list=
  match g with
  | GP_Empty -> []
  | GP_BGP b ->
      let ts = bgp_to_triples_concrete b in
      FStar_List_Tot_Base.map (fun t -> (outer, t)) ts
  | GP_Join (a, b) ->
      RDF_List_Helpers.append_tr (collect_quads outer a)
        (collect_quads outer b)
  | GP_Graph (gt, inner) ->
      (match gt with
       | PT_IRI g_iri ->
           collect_quads (FStar_Pervasives_Native.Some g_iri) inner
       | uu___ -> collect_quads outer inner)
  | uu___ -> []
let rename_quad_bnodes (prefix : Prims.string)
  (q : (RDF_Term.wf_iri FStar_Pervasives_Native.option * RDF_Triple.triple))
  : (RDF_Term.wf_iri FStar_Pervasives_Native.option * RDF_Triple.triple)=
  let uu___ = q in
  match uu___ with
  | (g_opt, t) ->
      (g_opt, (RDF_Graph_Executable.rename_triple_bnodes prefix t))
let rec upsert_named_graph (name : RDF_Term.iri) (t : RDF_Triple.triple)
  (named : RDF_Graph.named_graph Prims.list) :
  RDF_Graph.named_graph Prims.list=
  match named with
  | [] -> [{ RDF_Graph.ng_name = name; RDF_Graph.ng_graph = [t] }]
  | ng::rest ->
      if ng.RDF_Graph.ng_name = name
      then
        {
          RDF_Graph.ng_name = (ng.RDF_Graph.ng_name);
          RDF_Graph.ng_graph = (RDF_Graph.graph_add t ng.RDF_Graph.ng_graph)
        } :: rest
      else ng :: (upsert_named_graph name t rest)
let insert_quad (ds : RDF_Graph.rdf_dataset)
  (q : (RDF_Term.wf_iri FStar_Pervasives_Native.option * RDF_Triple.triple))
  : RDF_Graph.rdf_dataset=
  let uu___ = q in
  match uu___ with
  | (g_opt, t) ->
      (match g_opt with
       | FStar_Pervasives_Native.None ->
           {
             RDF_Graph.ds_default =
               (RDF_Graph.graph_add t ds.RDF_Graph.ds_default);
             RDF_Graph.ds_named = (ds.RDF_Graph.ds_named)
           }
       | FStar_Pervasives_Native.Some g_iri ->
           {
             RDF_Graph.ds_default = (ds.RDF_Graph.ds_default);
             RDF_Graph.ds_named =
               (upsert_named_graph g_iri t ds.RDF_Graph.ds_named)
           })
let rec insert_quads (ds : RDF_Graph.rdf_dataset)
  (qs :
    (RDF_Term.wf_iri FStar_Pervasives_Native.option * RDF_Triple.triple)
      Prims.list)
  : RDF_Graph.rdf_dataset=
  match qs with | [] -> ds | q::rest -> insert_quads (insert_quad ds q) rest
let apply_insert_data (request_salt : Prims.string)
  (ds : RDF_Graph.rdf_dataset) (ggp : group_graph_pattern) :
  RDF_Graph.rdf_dataset=
  let quads = collect_quads FStar_Pervasives_Native.None ggp in
  let prefix = FStar_String.concat "" ["_insdata_"; request_salt] in
  let renamed = FStar_List_Tot_Base.map (rename_quad_bnodes prefix) quads in
  insert_quads ds renamed
let triple_has_bnode (t : RDF_Triple.triple) : Prims.bool=
  (match t.RDF_Triple.s with
   | RDF_Term.S_BNode uu___ -> true
   | uu___ -> false) ||
    (match t.RDF_Triple.o with
     | RDF_Term.T_BNode uu___ -> true
     | uu___ -> false)
let quad_has_bnode
  (q : (RDF_Term.wf_iri FStar_Pervasives_Native.option * RDF_Triple.triple))
  : Prims.bool= triple_has_bnode (FStar_Pervasives_Native.snd q)
let rec filter_no_bnode_quads
  (qs :
    (RDF_Term.wf_iri FStar_Pervasives_Native.option * RDF_Triple.triple)
      Prims.list)
  :
  (RDF_Term.wf_iri FStar_Pervasives_Native.option * RDF_Triple.triple)
    Prims.list=
  match qs with
  | [] -> []
  | q::rest ->
      if quad_has_bnode q
      then filter_no_bnode_quads rest
      else q :: (filter_no_bnode_quads rest)
let rec remove_from_named_graph (name : RDF_Term.iri) (t : RDF_Triple.triple)
  (named : RDF_Graph.named_graph Prims.list) :
  RDF_Graph.named_graph Prims.list=
  match named with
  | [] -> []
  | ng::rest ->
      if ng.RDF_Graph.ng_name = name
      then
        {
          RDF_Graph.ng_name = (ng.RDF_Graph.ng_name);
          RDF_Graph.ng_graph =
            (RDF_Graph_Executable.graph_remove t ng.RDF_Graph.ng_graph)
        } :: rest
      else ng :: (remove_from_named_graph name t rest)
let delete_quad (ds : RDF_Graph.rdf_dataset)
  (q : (RDF_Term.wf_iri FStar_Pervasives_Native.option * RDF_Triple.triple))
  : RDF_Graph.rdf_dataset=
  let uu___ = q in
  match uu___ with
  | (g_opt, t) ->
      (match g_opt with
       | FStar_Pervasives_Native.None ->
           {
             RDF_Graph.ds_default =
               (RDF_Graph_Executable.graph_remove t ds.RDF_Graph.ds_default);
             RDF_Graph.ds_named = (ds.RDF_Graph.ds_named)
           }
       | FStar_Pervasives_Native.Some g_iri ->
           {
             RDF_Graph.ds_default = (ds.RDF_Graph.ds_default);
             RDF_Graph.ds_named =
               (remove_from_named_graph g_iri t ds.RDF_Graph.ds_named)
           })
let rec delete_quads (ds : RDF_Graph.rdf_dataset)
  (qs :
    (RDF_Term.wf_iri FStar_Pervasives_Native.option * RDF_Triple.triple)
      Prims.list)
  : RDF_Graph.rdf_dataset=
  match qs with | [] -> ds | q::rest -> delete_quads (delete_quad ds q) rest
let apply_delete_data (ds : RDF_Graph.rdf_dataset)
  (ggp : group_graph_pattern) : RDF_Graph.rdf_dataset=
  let quads = collect_quads FStar_Pervasives_Native.None ggp in
  let clean = filter_no_bnode_quads quads in delete_quads ds clean
let instantiate_tp (tp : triple_pattern)
  (mu : RDF_Graph_Executable.solution_mapping) :
  RDF_Triple.triple FStar_Pervasives_Native.option=
  match bound_subject_of_pattern tp.tp_s mu with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some s ->
      (match bound_predicate_of_pattern tp.tp_p mu with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some p ->
           (match bound_object_of_pattern tp.tp_o mu with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some o ->
                FStar_Pervasives_Native.Some
                  { RDF_Triple.s = s; RDF_Triple.p = p; RDF_Triple.o = o }))
let rec instantiate_bgp (b : bgp)
  (mu : RDF_Graph_Executable.solution_mapping) :
  RDF_Triple.triple Prims.list=
  match b with
  | [] -> []
  | tp::rest ->
      let rest_ts = instantiate_bgp rest mu in
      (match instantiate_tp tp mu with
       | FStar_Pervasives_Native.None -> rest_ts
       | FStar_Pervasives_Native.Some t -> t :: rest_ts)
let fresh_bnode_for_op (op_salt : Prims.string) (sol_ix : Prims.nat)
  (label : Prims.string) : RDF_Term.bnode_id=
  FStar_String.concat ""
    [op_salt; "_sm"; Prims.string_of_int sol_ix; "_"; label]
let bound_subject_of_pattern_freshen (op_salt : Prims.string)
  (sol_ix : Prims.nat) (ps : pattern_subject)
  (mu : RDF_Graph_Executable.solution_mapping) :
  RDF_Term.subject FStar_Pervasives_Native.option=
  match ps with
  | PS_IRI i -> FStar_Pervasives_Native.Some (RDF_Term.S_IRI i)
  | PS_BNode b ->
      FStar_Pervasives_Native.Some
        (RDF_Term.S_BNode (fresh_bnode_for_op op_salt sol_ix b))
  | PS_TripleTerm (uu___, uu___1, uu___2) -> FStar_Pervasives_Native.None
  | PS_Var v ->
      (match sm_lookup v mu with
       | FStar_Pervasives_Native.Some (RDF_Term.T_IRI i) ->
           FStar_Pervasives_Native.Some (RDF_Term.S_IRI i)
       | FStar_Pervasives_Native.Some (RDF_Term.T_BNode b) ->
           FStar_Pervasives_Native.Some (RDF_Term.S_BNode b)
       | FStar_Pervasives_Native.Some (RDF_Term.T_Literal uu___) ->
           FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some (RDF_Term.T_TripleTerm
           (uu___, uu___1, uu___2)) -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
let rec bound_object_of_pattern_freshen (op_salt : Prims.string)
  (sol_ix : Prims.nat) (pt : pattern_term)
  (mu : RDF_Graph_Executable.solution_mapping) :
  RDF_Term.rdf_term FStar_Pervasives_Native.option=
  match pt with
  | PT_IRI i -> FStar_Pervasives_Native.Some (RDF_Term.T_IRI i)
  | PT_BNode b ->
      FStar_Pervasives_Native.Some
        (RDF_Term.T_BNode (fresh_bnode_for_op op_salt sol_ix b))
  | PT_Literal l -> FStar_Pervasives_Native.Some (RDF_Term.T_Literal l)
  | PT_Var v -> sm_lookup v mu
  | PT_TripleTerm (ps, pp, po) ->
      (match bound_object_of_pattern_freshen op_salt sol_ix ps mu with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some sterm ->
           (match term_to_subject_opt sterm with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some ssub ->
                (match bound_object_of_pattern_freshen op_salt sol_ix pp mu
                 with
                 | FStar_Pervasives_Native.Some (RDF_Term.T_IRI ppi) ->
                     (match bound_object_of_pattern_freshen op_salt sol_ix po
                              mu
                      with
                      | FStar_Pervasives_Native.None ->
                          FStar_Pervasives_Native.None
                      | FStar_Pervasives_Native.Some oterm ->
                          FStar_Pervasives_Native.Some
                            (RDF_Term.T_TripleTerm (ssub, ppi, oterm)))
                 | uu___ -> FStar_Pervasives_Native.None)))
let instantiate_tp_freshen (op_salt : Prims.string) (sol_ix : Prims.nat)
  (tp : triple_pattern) (mu : RDF_Graph_Executable.solution_mapping) :
  RDF_Triple.triple FStar_Pervasives_Native.option=
  match bound_subject_of_pattern_freshen op_salt sol_ix tp.tp_s mu with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some s ->
      (match bound_predicate_of_pattern tp.tp_p mu with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some p ->
           (match bound_object_of_pattern_freshen op_salt sol_ix tp.tp_o mu
            with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some o ->
                FStar_Pervasives_Native.Some
                  { RDF_Triple.s = s; RDF_Triple.p = p; RDF_Triple.o = o }))
let rec instantiate_bgp_freshen (op_salt : Prims.string) (sol_ix : Prims.nat)
  (b : bgp) (mu : RDF_Graph_Executable.solution_mapping) :
  RDF_Triple.triple Prims.list=
  match b with
  | [] -> []
  | tp::rest ->
      let rest_ts = instantiate_bgp_freshen op_salt sol_ix rest mu in
      (match instantiate_tp_freshen op_salt sol_ix tp mu with
       | FStar_Pervasives_Native.None -> rest_ts
       | FStar_Pervasives_Native.Some t -> t :: rest_ts)
let rec instantiate_ggp_quads
  (outer : RDF_Term.wf_iri FStar_Pervasives_Native.option)
  (g : group_graph_pattern) (mu : RDF_Graph_Executable.solution_mapping) :
  (RDF_Term.wf_iri FStar_Pervasives_Native.option * RDF_Triple.triple)
    Prims.list=
  match g with
  | GP_Empty -> []
  | GP_BGP b ->
      let ts = instantiate_bgp b mu in
      FStar_List_Tot_Base.map (fun t -> (outer, t)) ts
  | GP_Join (a, b) ->
      RDF_List_Helpers.append_tr (instantiate_ggp_quads outer a mu)
        (instantiate_ggp_quads outer b mu)
  | GP_Graph (gt, inner) ->
      (match bound_predicate_of_pattern gt mu with
       | FStar_Pervasives_Native.Some g_iri ->
           instantiate_ggp_quads (FStar_Pervasives_Native.Some g_iri) inner
             mu
       | FStar_Pervasives_Native.None -> instantiate_ggp_quads outer inner mu)
  | uu___ -> []
let rec instantiate_ggp_quads_freshen (op_salt : Prims.string)
  (sol_ix : Prims.nat)
  (outer : RDF_Term.wf_iri FStar_Pervasives_Native.option)
  (g : group_graph_pattern) (mu : RDF_Graph_Executable.solution_mapping) :
  (RDF_Term.wf_iri FStar_Pervasives_Native.option * RDF_Triple.triple)
    Prims.list=
  match g with
  | GP_Empty -> []
  | GP_BGP b ->
      let ts = instantiate_bgp_freshen op_salt sol_ix b mu in
      FStar_List_Tot_Base.map (fun t -> (outer, t)) ts
  | GP_Join (a, b) ->
      RDF_List_Helpers.append_tr
        (instantiate_ggp_quads_freshen op_salt sol_ix outer a mu)
        (instantiate_ggp_quads_freshen op_salt sol_ix outer b mu)
  | GP_Graph (gt, inner) ->
      (match bound_predicate_of_pattern gt mu with
       | FStar_Pervasives_Native.Some g_iri ->
           instantiate_ggp_quads_freshen op_salt sol_ix
             (FStar_Pervasives_Native.Some g_iri) inner mu
       | FStar_Pervasives_Native.None ->
           instantiate_ggp_quads_freshen op_salt sol_ix outer inner mu)
  | uu___ -> []
let rec instantiate_ggp_all
  (outer : RDF_Term.wf_iri FStar_Pervasives_Native.option)
  (g : group_graph_pattern) (mus : solution_sequence) :
  (RDF_Term.wf_iri FStar_Pervasives_Native.option * RDF_Triple.triple)
    Prims.list=
  match mus with
  | [] -> []
  | mu::rest ->
      RDF_List_Helpers.append_tr (instantiate_ggp_quads outer g mu)
        (instantiate_ggp_all outer g rest)
let apply_delete_where (ds : RDF_Graph.rdf_dataset)
  (ggp : group_graph_pattern) : RDF_Graph.rdf_dataset=
  let rewritten = rewrite_query_bnodes_pattern ggp in
  let mus =
    eval_pattern FStar_Pervasives_Native.None rewritten
      ds.RDF_Graph.ds_default ds in
  let quads = instantiate_ggp_all FStar_Pervasives_Native.None rewritten mus in
  delete_quads ds quads
let rec using_default_iris (dcs : dataset_clause Prims.list) :
  RDF_Term.wf_iri Prims.list=
  match dcs with
  | [] -> []
  | (DC_Default i)::rest -> i :: (using_default_iris rest)
  | (DC_Named uu___)::rest -> using_default_iris rest
let rec using_named_iris (dcs : dataset_clause Prims.list) :
  RDF_Term.wf_iri Prims.list=
  match dcs with
  | [] -> []
  | (DC_Named i)::rest -> i :: (using_named_iris rest)
  | (DC_Default uu___)::rest -> using_named_iris rest
let rec union_named_graphs_by_iri (iris : RDF_Term.wf_iri Prims.list)
  (named : RDF_Graph.named_graph Prims.list) : RDF_Graph.rdf_graph=
  match iris with
  | [] -> RDF_Graph.empty_graph
  | i::rest ->
      let g =
        match RDF_Graph.lookup_named_graph i named with
        | FStar_Pervasives_Native.Some g1 -> g1
        | FStar_Pervasives_Native.None -> RDF_Graph.empty_graph in
      RDF_Graph_Executable.graph_union g
        (union_named_graphs_by_iri rest named)
let rec named_graphs_by_iri (iris : RDF_Term.wf_iri Prims.list)
  (named : RDF_Graph.named_graph Prims.list) :
  RDF_Graph.named_graph Prims.list=
  match iris with
  | [] -> []
  | i::rest ->
      let g =
        match RDF_Graph.lookup_named_graph i named with
        | FStar_Pervasives_Native.Some g1 -> g1
        | FStar_Pervasives_Native.None -> RDF_Graph.empty_graph in
      { RDF_Graph.ng_name = i; RDF_Graph.ng_graph = g } ::
        (named_graphs_by_iri rest named)
let build_where_dataset (ds : RDF_Graph.rdf_dataset)
  (with_iri : RDF_Term.wf_iri FStar_Pervasives_Native.option)
  (using : dataset_clause Prims.list) : RDF_Graph.rdf_dataset=
  match using with
  | [] ->
      (match with_iri with
       | FStar_Pervasives_Native.None -> ds
       | FStar_Pervasives_Native.Some g ->
           let def_g =
             match RDF_Graph.lookup_named_graph g ds.RDF_Graph.ds_named with
             | FStar_Pervasives_Native.Some x -> x
             | FStar_Pervasives_Native.None -> RDF_Graph.empty_graph in
           {
             RDF_Graph.ds_default = def_g;
             RDF_Graph.ds_named = (ds.RDF_Graph.ds_named)
           })
  | uu___ ->
      let def_iris = using_default_iris using in
      let nam_iris = using_named_iris using in
      let def_g = union_named_graphs_by_iri def_iris ds.RDF_Graph.ds_named in
      let nam = named_graphs_by_iri nam_iris ds.RDF_Graph.ds_named in
      { RDF_Graph.ds_default = def_g; RDF_Graph.ds_named = nam }
let redirect_default_quad
  (with_iri : RDF_Term.wf_iri FStar_Pervasives_Native.option)
  (q : (RDF_Term.wf_iri FStar_Pervasives_Native.option * RDF_Triple.triple))
  : (RDF_Term.wf_iri FStar_Pervasives_Native.option * RDF_Triple.triple)=
  let uu___ = q in
  match uu___ with
  | (g_opt, t) ->
      (match (g_opt, with_iri) with
       | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.Some g) ->
           ((FStar_Pervasives_Native.Some g), t)
       | (uu___1, uu___2) -> (g_opt, t))
let rec redirect_default_quads
  (with_iri : RDF_Term.wf_iri FStar_Pervasives_Native.option)
  (qs :
    (RDF_Term.wf_iri FStar_Pervasives_Native.option * RDF_Triple.triple)
      Prims.list)
  :
  (RDF_Term.wf_iri FStar_Pervasives_Native.option * RDF_Triple.triple)
    Prims.list=
  match qs with
  | [] -> []
  | q::rest -> (redirect_default_quad with_iri q) ::
      (redirect_default_quads with_iri rest)
let rec per_mapping_quads
  (outer : RDF_Term.wf_iri FStar_Pervasives_Native.option)
  (ggp : group_graph_pattern) (mus : solution_sequence) :
  (RDF_Term.wf_iri FStar_Pervasives_Native.option * RDF_Triple.triple)
    Prims.list Prims.list=
  match mus with
  | [] -> []
  | mu::rest -> (instantiate_ggp_quads outer ggp mu) ::
      (per_mapping_quads outer ggp rest)
let rec per_mapping_insert_quads (op_salt : Prims.string)
  (outer : RDF_Term.wf_iri FStar_Pervasives_Native.option)
  (ggp : group_graph_pattern) (mus : solution_sequence) (sol_ix : Prims.nat)
  :
  (RDF_Term.wf_iri FStar_Pervasives_Native.option * RDF_Triple.triple)
    Prims.list Prims.list=
  match mus with
  | [] -> []
  | mu::rest -> (instantiate_ggp_quads_freshen op_salt sol_ix outer ggp mu)
      ::
      (per_mapping_insert_quads op_salt outer ggp rest
         (sol_ix + Prims.int_one))
let rec insert_per_mapping_quads (ds : RDF_Graph.rdf_dataset)
  (per_mu_quads :
    (RDF_Term.wf_iri FStar_Pervasives_Native.option * RDF_Triple.triple)
      Prims.list Prims.list)
  : RDF_Graph.rdf_dataset=
  match per_mu_quads with
  | [] -> ds
  | qs::rest ->
      let ds' = insert_quads ds qs in insert_per_mapping_quads ds' rest
let apply_modify (op_salt : Prims.string) (ds : RDF_Graph.rdf_dataset)
  (with_iri : RDF_Term.wf_iri FStar_Pervasives_Native.option)
  (delete_tmpl : group_graph_pattern FStar_Pervasives_Native.option)
  (insert_tmpl : group_graph_pattern FStar_Pervasives_Native.option)
  (using : dataset_clause Prims.list) (where_ggp : group_graph_pattern) :
  RDF_Graph.rdf_dataset=
  let where_rewritten = rewrite_query_bnodes_pattern where_ggp in
  let where_ds = build_where_dataset ds with_iri using in
  let mus =
    eval_pattern FStar_Pervasives_Native.None where_rewritten
      where_ds.RDF_Graph.ds_default where_ds in
  let del_quads_per_mu =
    match delete_tmpl with
    | FStar_Pervasives_Native.None -> []
    | FStar_Pervasives_Native.Some dt ->
        per_mapping_quads FStar_Pervasives_Native.None dt mus in
  let del_quads_flat =
    FStar_List_Tot_Base.fold_left
      (fun acc qs -> RDF_List_Helpers.append_tr acc qs) [] del_quads_per_mu in
  let del_quads_redirected = redirect_default_quads with_iri del_quads_flat in
  let ds_after_delete = delete_quads ds del_quads_redirected in
  match insert_tmpl with
  | FStar_Pervasives_Native.None -> ds_after_delete
  | FStar_Pervasives_Native.Some it ->
      let ins_quads_per_mu =
        per_mapping_insert_quads op_salt FStar_Pervasives_Native.None it mus
          Prims.int_zero in
      let redirected_per_mu =
        FStar_List_Tot_Base.map
          (fun qs -> redirect_default_quads with_iri qs) ins_quads_per_mu in
      insert_per_mapping_quads ds_after_delete redirected_per_mu
let rec find_named_graph_triples (iri : RDF_Term.wf_iri)
  (named : RDF_Graph.named_graph Prims.list) : RDF_Triple.triple Prims.list=
  match named with
  | [] -> []
  | ng::rest ->
      if ng.RDF_Graph.ng_name = iri
      then ng.RDF_Graph.ng_graph
      else find_named_graph_triples iri rest
let rec has_named_graph (iri : RDF_Term.wf_iri)
  (named : RDF_Graph.named_graph Prims.list) : Prims.bool=
  match named with
  | [] -> false
  | ng::rest -> (ng.RDF_Graph.ng_name = iri) || (has_named_graph iri rest)
let rec replace_named_graph_triples (iri : RDF_Term.wf_iri)
  (ts : RDF_Triple.triple Prims.list)
  (named : RDF_Graph.named_graph Prims.list) :
  RDF_Graph.named_graph Prims.list=
  match named with
  | [] -> [{ RDF_Graph.ng_name = iri; RDF_Graph.ng_graph = ts }]
  | ng::rest ->
      if ng.RDF_Graph.ng_name = iri
      then
        { RDF_Graph.ng_name = (ng.RDF_Graph.ng_name); RDF_Graph.ng_graph = ts
        } :: rest
      else ng :: (replace_named_graph_triples iri ts rest)
let rec empty_graph_named (iri : RDF_Term.wf_iri)
  (named : RDF_Graph.named_graph Prims.list) :
  RDF_Graph.named_graph Prims.list=
  match named with
  | [] -> []
  | ng::rest ->
      if ng.RDF_Graph.ng_name = iri
      then
        { RDF_Graph.ng_name = (ng.RDF_Graph.ng_name); RDF_Graph.ng_graph = []
        } :: rest
      else ng :: (empty_graph_named iri rest)
let rec drop_named_by_iri (iri : RDF_Term.wf_iri)
  (named : RDF_Graph.named_graph Prims.list) :
  RDF_Graph.named_graph Prims.list=
  match named with
  | [] -> []
  | ng::rest ->
      if ng.RDF_Graph.ng_name = iri
      then rest
      else ng :: (drop_named_by_iri iri rest)
let rec empty_all_named (named : RDF_Graph.named_graph Prims.list) :
  RDF_Graph.named_graph Prims.list=
  match named with
  | [] -> []
  | ng::rest ->
      { RDF_Graph.ng_name = (ng.RDF_Graph.ng_name); RDF_Graph.ng_graph = [] }
      :: (empty_all_named rest)
let ensure_named_graph (iri : RDF_Term.wf_iri)
  (named : RDF_Graph.named_graph Prims.list) :
  RDF_Graph.named_graph Prims.list=
  if has_named_graph iri named
  then named
  else
    RDF_List_Helpers.append_tr named
      [{ RDF_Graph.ng_name = iri; RDF_Graph.ng_graph = [] }]
let read_graph_ref (gr : graph_ref) (ds : RDF_Graph.rdf_dataset) :
  RDF_Triple.triple Prims.list=
  match gr with
  | GR_Default -> ds.RDF_Graph.ds_default
  | GR_Graph iri -> find_named_graph_triples iri ds.RDF_Graph.ds_named
  | GR_Named -> []
  | GR_All -> []
let graph_ref_exists (gr : graph_ref) (ds : RDF_Graph.rdf_dataset) :
  Prims.bool=
  match gr with
  | GR_Default -> true
  | GR_Graph iri -> has_named_graph iri ds.RDF_Graph.ds_named
  | GR_Named -> false
  | GR_All -> false
let write_graph_ref (gr : graph_ref) (ts : RDF_Triple.triple Prims.list)
  (ds : RDF_Graph.rdf_dataset) : RDF_Graph.rdf_dataset=
  match gr with
  | GR_Default ->
      {
        RDF_Graph.ds_default = ts;
        RDF_Graph.ds_named = (ds.RDF_Graph.ds_named)
      }
  | GR_Graph iri ->
      {
        RDF_Graph.ds_default = (ds.RDF_Graph.ds_default);
        RDF_Graph.ds_named =
          (replace_named_graph_triples iri ts ds.RDF_Graph.ds_named)
      }
  | GR_Named -> ds
  | GR_All -> ds
let graph_ref_eq (a : graph_ref) (b : graph_ref) : Prims.bool=
  match (a, b) with
  | (GR_Default, GR_Default) -> true
  | (GR_Named, GR_Named) -> true
  | (GR_All, GR_All) -> true
  | (GR_Graph i1, GR_Graph i2) -> i1 = i2
  | (uu___, uu___1) -> false
let apply_create (ds : RDF_Graph.rdf_dataset) (silent : Prims.bool)
  (iri : RDF_Term.wf_iri) : RDF_Graph.rdf_dataset=
  let uu___ = silent in
  {
    RDF_Graph.ds_default = (ds.RDF_Graph.ds_default);
    RDF_Graph.ds_named = (ensure_named_graph iri ds.RDF_Graph.ds_named)
  }
let apply_clear (ds : RDF_Graph.rdf_dataset) (silent : Prims.bool)
  (gr : graph_ref) : RDF_Graph.rdf_dataset=
  let uu___ = silent in
  match gr with
  | GR_Default ->
      {
        RDF_Graph.ds_default = [];
        RDF_Graph.ds_named = (ds.RDF_Graph.ds_named)
      }
  | GR_Named ->
      {
        RDF_Graph.ds_default = (ds.RDF_Graph.ds_default);
        RDF_Graph.ds_named = (empty_all_named ds.RDF_Graph.ds_named)
      }
  | GR_All ->
      {
        RDF_Graph.ds_default = [];
        RDF_Graph.ds_named = (empty_all_named ds.RDF_Graph.ds_named)
      }
  | GR_Graph iri ->
      {
        RDF_Graph.ds_default = (ds.RDF_Graph.ds_default);
        RDF_Graph.ds_named = (empty_graph_named iri ds.RDF_Graph.ds_named)
      }
let apply_drop (ds : RDF_Graph.rdf_dataset) (silent : Prims.bool)
  (gr : graph_ref) : RDF_Graph.rdf_dataset=
  let uu___ = silent in
  match gr with
  | GR_Default ->
      {
        RDF_Graph.ds_default = [];
        RDF_Graph.ds_named = (ds.RDF_Graph.ds_named)
      }
  | GR_Named ->
      {
        RDF_Graph.ds_default = (ds.RDF_Graph.ds_default);
        RDF_Graph.ds_named = []
      }
  | GR_All -> { RDF_Graph.ds_default = []; RDF_Graph.ds_named = [] }
  | GR_Graph iri ->
      {
        RDF_Graph.ds_default = (ds.RDF_Graph.ds_default);
        RDF_Graph.ds_named = (drop_named_by_iri iri ds.RDF_Graph.ds_named)
      }
let apply_copy (ds : RDF_Graph.rdf_dataset) (silent : Prims.bool)
  (src : graph_ref) (dst : graph_ref) : RDF_Graph.rdf_dataset=
  let uu___ = silent in
  if graph_ref_eq src dst
  then ds
  else
    if Prims.op_Negation (graph_ref_exists src ds)
    then ds
    else
      (let src_triples = read_graph_ref src ds in
       write_graph_ref dst src_triples ds)
let apply_move (ds : RDF_Graph.rdf_dataset) (silent : Prims.bool)
  (src : graph_ref) (dst : graph_ref) : RDF_Graph.rdf_dataset=
  let uu___ = silent in
  if graph_ref_eq src dst
  then ds
  else
    if Prims.op_Negation (graph_ref_exists src ds)
    then ds
    else
      (let src_triples = read_graph_ref src ds in
       let ds_copied = write_graph_ref dst src_triples ds in
       match src with
       | GR_Default ->
           {
             RDF_Graph.ds_default = [];
             RDF_Graph.ds_named = (ds_copied.RDF_Graph.ds_named)
           }
       | GR_Graph iri ->
           {
             RDF_Graph.ds_default = (ds_copied.RDF_Graph.ds_default);
             RDF_Graph.ds_named =
               (drop_named_by_iri iri ds_copied.RDF_Graph.ds_named)
           }
       | GR_Named -> ds_copied
       | GR_All -> ds_copied)
let rec graph_append (src : RDF_Triple.triple Prims.list)
  (dst : RDF_Graph.rdf_graph) : RDF_Graph.rdf_graph=
  match src with
  | [] -> dst
  | t::rest -> graph_append rest (RDF_Graph.graph_add t dst)
let apply_add (ds : RDF_Graph.rdf_dataset) (silent : Prims.bool)
  (src : graph_ref) (dst : graph_ref) : RDF_Graph.rdf_dataset=
  let uu___ = silent in
  if graph_ref_eq src dst
  then ds
  else
    if Prims.op_Negation (graph_ref_exists src ds)
    then ds
    else
      (let src_triples = read_graph_ref src ds in
       let cur_dst = read_graph_ref dst ds in
       let merged = graph_append src_triples cur_dst in
       write_graph_ref dst merged ds)
let apply_update_op (request_salt : Prims.string) (op_idx : Prims.nat)
  (ds : RDF_Graph.rdf_dataset) (op : update_op) : RDF_Graph.rdf_dataset=
  let op_salt = FStar_String.concat "" ["op"; Prims.string_of_int op_idx] in
  match op with
  | U_InsertData g -> apply_insert_data request_salt ds g
  | U_DeleteData g -> apply_delete_data ds g
  | U_DeleteWhere g -> apply_delete_where ds g
  | U_Modify (w, d, i, u, p) -> apply_modify op_salt ds w d i u p
  | U_Create (silent, iri) -> apply_create ds silent iri
  | U_Clear (silent, gr) -> apply_clear ds silent gr
  | U_Drop (silent, gr) -> apply_drop ds silent gr
  | U_Copy (silent, src, dst) -> apply_copy ds silent src dst
  | U_Move (silent, src, dst) -> apply_move ds silent src dst
  | U_Add (silent, src, dst) -> apply_add ds silent src dst
  | U_Load (uu___, uu___1, uu___2) -> ds
let rec apply_update_ops_aux (request_salt : Prims.string)
  (op_idx : Prims.nat) (ds : RDF_Graph.rdf_dataset)
  (ops : update_op Prims.list) : RDF_Graph.rdf_dataset=
  match ops with
  | [] -> ds
  | op::rest ->
      let ds' = apply_update_op request_salt op_idx ds op in
      apply_update_ops_aux request_salt (op_idx + Prims.int_one) ds' rest
let apply_update_ops (ds : RDF_Graph.rdf_dataset)
  (ops : update_op Prims.list) : RDF_Graph.rdf_dataset=
  let request_salt = Prims.string_of_int (dataset_triple_count ds) in
  apply_update_ops_aux request_salt Prims.int_zero ds ops
let apply_update (ds : RDF_Graph.rdf_dataset) (u : sparql_update) :
  RDF_Graph.rdf_dataset= apply_update_ops ds u.u_ops
let is_implemented_op (op : update_op) : Prims.bool=
  match op with
  | U_InsertData uu___ -> true
  | U_DeleteData uu___ -> true
  | U_DeleteWhere uu___ -> true
  | U_Modify (uu___, uu___1, uu___2, uu___3, uu___4) -> true
  | U_Create (uu___, uu___1) -> true
  | U_Clear (uu___, uu___1) -> true
  | U_Drop (uu___, uu___1) -> true
  | U_Copy (uu___, uu___1, uu___2) -> true
  | U_Move (uu___, uu___1, uu___2) -> true
  | U_Add (uu___, uu___1, uu___2) -> true
  | U_Load (silent, uu___, uu___1) -> silent
let rec update_is_implemented_only_ops (ops : update_op Prims.list) :
  Prims.bool=
  match ops with
  | [] -> true
  | op::rest ->
      (is_implemented_op op) && (update_is_implemented_only_ops rest)
let update_is_implemented_only (u : sparql_update) : Prims.bool=
  update_is_implemented_only_ops u.u_ops
