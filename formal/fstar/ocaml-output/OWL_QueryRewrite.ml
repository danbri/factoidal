open Prims
let owl_intersectionOf_iri : RDF_Graph_Executable.wf_iri=
  "http://www.w3.org/2002/07/owl#intersectionOf"
let owl_unionOf_iri : RDF_Graph_Executable.wf_iri=
  "http://www.w3.org/2002/07/owl#unionOf"
let owl_Class_iri : RDF_Graph_Executable.wf_iri=
  "http://www.w3.org/2002/07/owl#Class"
let rdf_first_iri : RDF_Graph_Executable.wf_iri=
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#first"
let rdf_rest_iri : RDF_Graph_Executable.wf_iri=
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#rest"
let rdf_nil_iri : RDF_Graph_Executable.wf_iri=
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#nil"
let rdf_type_iri : RDF_Graph_Executable.wf_iri=
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#type"
let owl_Restriction_iri : RDF_Graph_Executable.wf_iri=
  "http://www.w3.org/2002/07/owl#Restriction"
let owl_onProperty_iri : RDF_Graph_Executable.wf_iri=
  "http://www.w3.org/2002/07/owl#onProperty"
let owl_someValuesFrom_iri : RDF_Graph_Executable.wf_iri=
  "http://www.w3.org/2002/07/owl#someValuesFrom"
let bnode_var_prefix : Prims.string= "_bnode_"
let strip_bnode_prefix (v : Prims.string) :
  Prims.string FStar_Pervasives_Native.option=
  if SPARQL11_Algebra.string_starts_with v bnode_var_prefix
  then
    FStar_Pervasives_Native.Some
      (SPARQL11_Algebra.string_substring v
         (SPARQL11_Algebra.string_length bnode_var_prefix)
         FStar_Pervasives_Native.None)
  else FStar_Pervasives_Native.None
let ps_marker_key (ps : SPARQL11_Algebra.pattern_subject) :
  Prims.string FStar_Pervasives_Native.option=
  match ps with
  | SPARQL11_Algebra.PS_BNode b -> FStar_Pervasives_Native.Some b
  | SPARQL11_Algebra.PS_Var v -> strip_bnode_prefix v
  | uu___ -> FStar_Pervasives_Native.None
let pt_marker_key (pt : SPARQL11_Algebra.pattern_term) :
  Prims.string FStar_Pervasives_Native.option=
  match pt with
  | SPARQL11_Algebra.PT_BNode b -> FStar_Pervasives_Native.Some b
  | SPARQL11_Algebra.PT_Var v -> strip_bnode_prefix v
  | uu___ -> FStar_Pervasives_Native.None
let ps_pt_same_anon (ps : SPARQL11_Algebra.pattern_subject)
  (pt : SPARQL11_Algebra.pattern_term) : Prims.bool=
  match ((ps_marker_key ps), (pt_marker_key pt)) with
  | (FStar_Pervasives_Native.Some k1, FStar_Pervasives_Native.Some k2) ->
      k1 = k2
  | (uu___, uu___1) -> false
let rec bgp_find_first_obj (b : SPARQL11_Algebra.bgp)
  (subj_key : Prims.string) (pred : RDF_Graph_Executable.wf_iri) :
  SPARQL11_Algebra.pattern_term FStar_Pervasives_Native.option=
  match b with
  | [] -> FStar_Pervasives_Native.None
  | tp::rest ->
      (match ((ps_marker_key tp.SPARQL11_Algebra.tp_s),
               (tp.SPARQL11_Algebra.tp_p))
       with
       | (FStar_Pervasives_Native.Some k, SPARQL11_Algebra.PT_IRI p) ->
           if (k = subj_key) && (p = pred)
           then FStar_Pervasives_Native.Some (tp.SPARQL11_Algebra.tp_o)
           else bgp_find_first_obj rest subj_key pred
       | (uu___, uu___1) -> bgp_find_first_obj rest subj_key pred)
let rec walk_rdf_collection_acc (b : SPARQL11_Algebra.bgp)
  (head : SPARQL11_Algebra.pattern_term)
  (acc : SPARQL11_Algebra.pattern_term Prims.list) (fuel : Prims.nat) :
  SPARQL11_Algebra.pattern_term Prims.list=
  match fuel with
  | uu___ when uu___ = Prims.int_zero -> FStar_List_Tot_Base.rev acc
  | n ->
      (match head with
       | SPARQL11_Algebra.PT_IRI uu___ -> FStar_List_Tot_Base.rev acc
       | uu___ ->
           (match pt_marker_key head with
            | FStar_Pervasives_Native.None -> FStar_List_Tot_Base.rev acc
            | FStar_Pervasives_Native.Some k ->
                let first = bgp_find_first_obj b k rdf_first_iri in
                let rest = bgp_find_first_obj b k rdf_rest_iri in
                (match (first, rest) with
                 | (FStar_Pervasives_Native.Some hd,
                    FStar_Pervasives_Native.Some tl) ->
                     walk_rdf_collection_acc b tl (hd :: acc)
                       (n - Prims.int_one)
                 | (uu___1, uu___2) -> FStar_List_Tot_Base.rev acc)))
let walk_rdf_collection (b : SPARQL11_Algebra.bgp)
  (head : SPARQL11_Algebra.pattern_term) :
  SPARQL11_Algebra.pattern_term Prims.list=
  walk_rdf_collection_acc b head []
    ((FStar_List_Tot_Base.length b) + Prims.int_one)
let extract_flat_intersection (b : SPARQL11_Algebra.bgp)
  (marker_key : Prims.string) :
  SPARQL11_Algebra.pattern_term Prims.list FStar_Pervasives_Native.option=
  match bgp_find_first_obj b marker_key owl_intersectionOf_iri with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some list_head ->
      (match walk_rdf_collection b list_head with
       | [] -> FStar_Pervasives_Native.None
       | operands -> FStar_Pervasives_Native.Some operands)
let extract_flat_union (b : SPARQL11_Algebra.bgp) (marker_key : Prims.string)
  : SPARQL11_Algebra.pattern_term Prims.list FStar_Pervasives_Native.option=
  match bgp_find_first_obj b marker_key owl_unionOf_iri with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some list_head ->
      (match walk_rdf_collection b list_head with
       | [] -> FStar_Pervasives_Native.None
       | operands -> FStar_Pervasives_Native.Some operands)
let rec collection_chain_keys_acc (b : SPARQL11_Algebra.bgp)
  (head : SPARQL11_Algebra.pattern_term) (acc : Prims.string Prims.list)
  (fuel : Prims.nat) : Prims.string Prims.list=
  match fuel with
  | uu___ when uu___ = Prims.int_zero -> acc
  | n ->
      (match pt_marker_key head with
       | FStar_Pervasives_Native.None -> acc
       | FStar_Pervasives_Native.Some k ->
           let acc' = if FStar_List_Tot_Base.mem k acc then acc else k :: acc in
           (match bgp_find_first_obj b k rdf_rest_iri with
            | FStar_Pervasives_Native.Some tl ->
                collection_chain_keys_acc b tl acc' (n - Prims.int_one)
            | FStar_Pervasives_Native.None -> acc'))
let collection_chain_keys (b : SPARQL11_Algebra.bgp)
  (head : SPARQL11_Algebra.pattern_term) : Prims.string Prims.list=
  collection_chain_keys_acc b head []
    ((FStar_List_Tot_Base.length b) + Prims.int_one)
let is_marker_bookkeeping (marker_key : Prims.string)
  (chain_keys : Prims.string Prims.list)
  (tp : SPARQL11_Algebra.triple_pattern) : Prims.bool=
  match ((ps_marker_key tp.SPARQL11_Algebra.tp_s),
          (tp.SPARQL11_Algebra.tp_p))
  with
  | (FStar_Pervasives_Native.Some sk, SPARQL11_Algebra.PT_IRI p) ->
      if sk = marker_key
      then
        ((p = owl_intersectionOf_iri) || (p = owl_unionOf_iri)) ||
          ((p = rdf_type_iri) &&
             ((match tp.SPARQL11_Algebra.tp_o with
               | SPARQL11_Algebra.PT_IRI oi -> oi = owl_Class_iri
               | uu___ -> false)))
      else
        if FStar_List_Tot_Base.mem sk chain_keys
        then (p = rdf_first_iri) || (p = rdf_rest_iri)
        else false
  | (uu___, uu___1) -> false
let is_consumer_triple (marker_key : Prims.string)
  (tp : SPARQL11_Algebra.triple_pattern) : Prims.bool=
  match ((tp.SPARQL11_Algebra.tp_p), (tp.SPARQL11_Algebra.tp_o)) with
  | (SPARQL11_Algebra.PT_IRI p, o) ->
      (p = rdf_type_iri) &&
        ((match pt_marker_key o with
          | FStar_Pervasives_Native.Some k -> k = marker_key
          | FStar_Pervasives_Native.None -> false))
  | (uu___, uu___1) -> false
let expand_consumer_for_intersection (tp : SPARQL11_Algebra.triple_pattern)
  (operands : SPARQL11_Algebra.pattern_term Prims.list) :
  SPARQL11_Algebra.triple_pattern Prims.list=
  let mk o =
    {
      SPARQL11_Algebra.tp_s = (tp.SPARQL11_Algebra.tp_s);
      SPARQL11_Algebra.tp_p = (SPARQL11_Algebra.PT_IRI rdf_type_iri);
      SPARQL11_Algebra.tp_o = o
    } in
  let step acc o = (mk o) :: acc in
  FStar_List_Tot_Base.rev (FStar_List_Tot_Base.fold_left step [] operands)
let rewrite_triple_intersection (marker_key : Prims.string)
  (chain_keys : Prims.string Prims.list)
  (operands : SPARQL11_Algebra.pattern_term Prims.list)
  (tp : SPARQL11_Algebra.triple_pattern) :
  SPARQL11_Algebra.triple_pattern Prims.list=
  if is_marker_bookkeeping marker_key chain_keys tp
  then []
  else
    if is_consumer_triple marker_key tp
    then expand_consumer_for_intersection tp operands
    else [tp]
let rewrite_bgp_intersection (marker_key : Prims.string)
  (chain_keys : Prims.string Prims.list)
  (operands : SPARQL11_Algebra.pattern_term Prims.list)
  (b : SPARQL11_Algebra.bgp) : SPARQL11_Algebra.bgp=
  let step acc tp =
    FStar_List_Tot_Base.append acc
      (rewrite_triple_intersection marker_key chain_keys operands tp) in
  FStar_List_Tot_Base.fold_left step [] b
let rewrite_bgp_strip_marker (marker_key : Prims.string)
  (chain_keys : Prims.string Prims.list) (b : SPARQL11_Algebra.bgp) :
  SPARQL11_Algebra.bgp=
  let step acc tp =
    if is_marker_bookkeeping marker_key chain_keys tp
    then acc
    else
      if is_consumer_triple marker_key tp
      then acc
      else FStar_List_Tot_Base.append acc [tp] in
  FStar_List_Tot_Base.fold_left step [] b
let rewrite_bgp_collect_consumers (marker_key : Prims.string)
  (b : SPARQL11_Algebra.bgp) : SPARQL11_Algebra.triple_pattern Prims.list=
  let step acc tp =
    if is_consumer_triple marker_key tp
    then FStar_List_Tot_Base.append acc [tp]
    else acc in
  FStar_List_Tot_Base.fold_left step [] b
let build_union_branch (residue : SPARQL11_Algebra.bgp)
  (consumers : SPARQL11_Algebra.triple_pattern Prims.list)
  (op : SPARQL11_Algebra.pattern_term) : SPARQL11_Algebra.bgp=
  let step acc tp =
    let new_tp =
      {
        SPARQL11_Algebra.tp_s = (tp.SPARQL11_Algebra.tp_s);
        SPARQL11_Algebra.tp_p = (SPARQL11_Algebra.PT_IRI rdf_type_iri);
        SPARQL11_Algebra.tp_o = op
      } in
    FStar_List_Tot_Base.append acc [new_tp] in
  FStar_List_Tot_Base.append residue
    (FStar_List_Tot_Base.fold_left step [] consumers)
let rec union_ladder (acc : SPARQL11_Algebra.group_graph_pattern)
  (branches : SPARQL11_Algebra.group_graph_pattern Prims.list) :
  SPARQL11_Algebra.group_graph_pattern=
  match branches with
  | [] -> acc
  | br::rest -> union_ladder (SPARQL11_Algebra.GP_Union (acc, br)) rest
let build_union_ggp (branch_bgps : SPARQL11_Algebra.bgp Prims.list) :
  SPARQL11_Algebra.group_graph_pattern=
  match branch_bgps with
  | [] -> SPARQL11_Algebra.GP_Empty
  | b::[] -> SPARQL11_Algebra.GP_BGP b
  | b1::rest ->
      let head = SPARQL11_Algebra.GP_BGP b1 in
      let rec_branches =
        FStar_List_Tot_Base.fold_left
          (fun acc b ->
             FStar_List_Tot_Base.append acc [SPARQL11_Algebra.GP_BGP b]) []
          rest in
      union_ladder head rec_branches
type ce_combinator =
  | CE_Intersect 
  | CE_Union 
  | CE_SomeValuesFrom 
let uu___is_CE_Intersect (projectee : ce_combinator) : Prims.bool=
  match projectee with | CE_Intersect -> true | uu___ -> false
let uu___is_CE_Union (projectee : ce_combinator) : Prims.bool=
  match projectee with | CE_Union -> true | uu___ -> false
let uu___is_CE_SomeValuesFrom (projectee : ce_combinator) : Prims.bool=
  match projectee with | CE_SomeValuesFrom -> true | uu___ -> false
let combinator_of_pred_flat (p : RDF_Graph_Executable.wf_iri) :
  ce_combinator FStar_Pervasives_Native.option=
  if p = owl_intersectionOf_iri
  then FStar_Pervasives_Native.Some CE_Intersect
  else
    if p = owl_unionOf_iri
    then FStar_Pervasives_Native.Some CE_Union
    else FStar_Pervasives_Native.None
let combinator_of_pred (p : RDF_Graph_Executable.wf_iri) :
  ce_combinator FStar_Pervasives_Native.option=
  if p = owl_intersectionOf_iri
  then FStar_Pervasives_Native.Some CE_Intersect
  else
    if p = owl_unionOf_iri
    then FStar_Pervasives_Native.Some CE_Union
    else
      if p = owl_someValuesFrom_iri
      then FStar_Pervasives_Native.Some CE_SomeValuesFrom
      else FStar_Pervasives_Native.None
let rec find_flat_markers_acc (b : SPARQL11_Algebra.bgp)
  (acc : (Prims.string * ce_combinator) Prims.list) :
  (Prims.string * ce_combinator) Prims.list=
  match b with
  | [] -> FStar_List_Tot_Base.rev acc
  | tp::rest ->
      (match ((ps_marker_key tp.SPARQL11_Algebra.tp_s),
               (tp.SPARQL11_Algebra.tp_p))
       with
       | (FStar_Pervasives_Native.Some k, SPARQL11_Algebra.PT_IRI p) ->
           (match combinator_of_pred_flat p with
            | FStar_Pervasives_Native.Some c ->
                let dup =
                  FStar_List_Tot_Base.existsb
                    (fun uu___ -> match uu___ with | (k', uu___1) -> k' = k)
                    acc in
                if dup
                then find_flat_markers_acc rest acc
                else find_flat_markers_acc rest ((k, c) :: acc)
            | FStar_Pervasives_Native.None -> find_flat_markers_acc rest acc)
       | (uu___, uu___1) -> find_flat_markers_acc rest acc)
let is_svf_subject (b : SPARQL11_Algebra.bgp) (k : Prims.string) :
  Prims.bool=
  FStar_Pervasives_Native.uu___is_Some
    (bgp_find_first_obj b k owl_someValuesFrom_iri)
let restriction_has_nested_filler (b : SPARQL11_Algebra.bgp)
  (k : Prims.string) : Prims.bool=
  match bgp_find_first_obj b k owl_someValuesFrom_iri with
  | FStar_Pervasives_Native.None -> false
  | FStar_Pervasives_Native.Some filler ->
      (match pt_marker_key filler with
       | FStar_Pervasives_Native.None -> false
       | FStar_Pervasives_Native.Some kf ->
           let flat = find_flat_markers_acc b [] in
           (FStar_List_Tot_Base.existsb
              (fun uu___ -> match uu___ with | (k', uu___1) -> k' = kf) flat)
             || (is_svf_subject b kf))
let rec add_restriction_markers_acc (b : SPARQL11_Algebra.bgp)
  (rem : SPARQL11_Algebra.bgp)
  (acc : (Prims.string * ce_combinator) Prims.list) :
  (Prims.string * ce_combinator) Prims.list=
  match rem with
  | [] -> acc
  | tp::rest ->
      (match ((ps_marker_key tp.SPARQL11_Algebra.tp_s),
               (tp.SPARQL11_Algebra.tp_p))
       with
       | (FStar_Pervasives_Native.Some k, SPARQL11_Algebra.PT_IRI p) ->
           if p = owl_someValuesFrom_iri
           then
             let dup =
               FStar_List_Tot_Base.existsb
                 (fun uu___ -> match uu___ with | (k', uu___1) -> k' = k) acc in
             (if dup
              then add_restriction_markers_acc b rest acc
              else
                if restriction_has_nested_filler b k
                then
                  add_restriction_markers_acc b rest
                    (FStar_List_Tot_Base.append acc [(k, CE_SomeValuesFrom)])
                else add_restriction_markers_acc b rest acc)
           else add_restriction_markers_acc b rest acc
       | (uu___, uu___1) -> add_restriction_markers_acc b rest acc)
let rec add_inner_restrictions_acc (b : SPARQL11_Algebra.bgp)
  (work : Prims.string Prims.list)
  (acc : (Prims.string * ce_combinator) Prims.list) (fuel : Prims.nat) :
  (Prims.string * ce_combinator) Prims.list=
  match (fuel, work) with
  | (uu___, uu___1) when uu___ = Prims.int_zero -> acc
  | (uu___, []) -> acc
  | (n, k::rest) ->
      (match bgp_find_first_obj b k owl_someValuesFrom_iri with
       | FStar_Pervasives_Native.None ->
           add_inner_restrictions_acc b rest acc (n - Prims.int_one)
       | FStar_Pervasives_Native.Some filler ->
           (match pt_marker_key filler with
            | FStar_Pervasives_Native.None ->
                add_inner_restrictions_acc b rest acc (n - Prims.int_one)
            | FStar_Pervasives_Native.Some kf ->
                let already =
                  FStar_List_Tot_Base.existsb
                    (fun uu___ -> match uu___ with | (k', uu___1) -> k' = kf)
                    acc in
                if already
                then
                  add_inner_restrictions_acc b rest acc (n - Prims.int_one)
                else
                  if is_svf_subject b kf
                  then
                    add_inner_restrictions_acc b
                      (FStar_List_Tot_Base.append rest [kf])
                      (FStar_List_Tot_Base.append acc
                         [(kf, CE_SomeValuesFrom)]) (n - Prims.int_one)
                  else
                    add_inner_restrictions_acc b rest acc (n - Prims.int_one)))
let find_markers (b : SPARQL11_Algebra.bgp) :
  (Prims.string * ce_combinator) Prims.list=
  let flat = find_flat_markers_acc b [] in
  let withr = add_restriction_markers_acc b b flat in
  let restr_keys =
    FStar_List_Tot_Base.fold_left
      (fun acc uu___ ->
         match uu___ with
         | (k, c) ->
             (match c with
              | CE_SomeValuesFrom -> FStar_List_Tot_Base.append acc [k]
              | uu___1 -> acc)) [] withr in
  add_inner_restrictions_acc b restr_keys withr
    ((FStar_List_Tot_Base.length b) + Prims.int_one)
let rewrite_bgp_one_intersection (marker_key : Prims.string)
  (b : SPARQL11_Algebra.bgp) : SPARQL11_Algebra.bgp=
  match extract_flat_intersection b marker_key with
  | FStar_Pervasives_Native.None -> b
  | FStar_Pervasives_Native.Some operands ->
      let head_opt = bgp_find_first_obj b marker_key owl_intersectionOf_iri in
      let chain_keys =
        match head_opt with
        | FStar_Pervasives_Native.Some hd -> collection_chain_keys b hd
        | FStar_Pervasives_Native.None -> [] in
      rewrite_bgp_intersection marker_key chain_keys operands b
let rewrite_bgp_one_union (marker_key : Prims.string)
  (b : SPARQL11_Algebra.bgp) : SPARQL11_Algebra.group_graph_pattern=
  match extract_flat_union b marker_key with
  | FStar_Pervasives_Native.None -> SPARQL11_Algebra.GP_BGP b
  | FStar_Pervasives_Native.Some operands ->
      let head_opt = bgp_find_first_obj b marker_key owl_unionOf_iri in
      let chain_keys =
        match head_opt with
        | FStar_Pervasives_Native.Some hd -> collection_chain_keys b hd
        | FStar_Pervasives_Native.None -> [] in
      let residue = rewrite_bgp_strip_marker marker_key chain_keys b in
      let consumers = rewrite_bgp_collect_consumers marker_key b in
      let branch_bgps =
        FStar_List_Tot_Base.fold_left
          (fun acc op ->
             FStar_List_Tot_Base.append acc
               [build_union_branch residue consumers op]) [] operands in
      build_union_ggp branch_bgps
let rewrite_bgp_flat (b : SPARQL11_Algebra.bgp) :
  SPARQL11_Algebra.group_graph_pattern=
  let markers = find_markers b in
  let inter_keys =
    FStar_List_Tot_Base.fold_left
      (fun acc uu___ ->
         match uu___ with
         | (k, c) ->
             (match c with
              | CE_Intersect -> FStar_List_Tot_Base.append acc [k]
              | uu___1 -> acc)) [] markers in
  let union_keys =
    FStar_List_Tot_Base.fold_left
      (fun acc uu___ ->
         match uu___ with
         | (k, c) ->
             (match c with
              | CE_Union -> FStar_List_Tot_Base.append acc [k]
              | uu___1 -> acc)) [] markers in
  let b_after_inter =
    FStar_List_Tot_Base.fold_left
      (fun cur k -> rewrite_bgp_one_intersection k cur) b inter_keys in
  match union_keys with
  | [] -> SPARQL11_Algebra.GP_BGP b_after_inter
  | k::uu___ -> rewrite_bgp_one_union k b_after_inter
let ce_combinator_for_term (b : SPARQL11_Algebra.bgp)
  (pt : SPARQL11_Algebra.pattern_term) :
  (Prims.string * ce_combinator) FStar_Pervasives_Native.option=
  match pt_marker_key pt with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some k ->
      let flat = find_flat_markers_acc b [] in
      let rec lookup ms =
        match ms with
        | [] -> FStar_Pervasives_Native.None
        | (k', c)::rest ->
            if k' = k then FStar_Pervasives_Native.Some c else lookup rest in
      (match lookup flat with
       | FStar_Pervasives_Native.Some c ->
           FStar_Pervasives_Native.Some (k, c)
       | FStar_Pervasives_Native.None ->
           if is_svf_subject b k
           then FStar_Pervasives_Native.Some (k, CE_SomeValuesFrom)
           else FStar_Pervasives_Native.None)
let single_type_bgp (subj : SPARQL11_Algebra.pattern_subject)
  (leaf : SPARQL11_Algebra.pattern_term) : SPARQL11_Algebra.bgp=
  [{
     SPARQL11_Algebra.tp_s = subj;
     SPARQL11_Algebra.tp_p = (SPARQL11_Algebra.PT_IRI rdf_type_iri);
     SPARQL11_Algebra.tp_o = leaf
   }]
let concat_bgps (bs : SPARQL11_Algebra.bgp Prims.list) :
  SPARQL11_Algebra.bgp=
  FStar_List_Tot_Base.fold_left
    (fun acc b -> FStar_List_Tot_Base.append acc b) [] bs
let rec join_ggps_acc (acc : SPARQL11_Algebra.group_graph_pattern)
  (rest : SPARQL11_Algebra.group_graph_pattern Prims.list) :
  SPARQL11_Algebra.group_graph_pattern=
  match rest with
  | [] -> acc
  | g::tl ->
      (match (acc, g) with
       | (SPARQL11_Algebra.GP_BGP ba, SPARQL11_Algebra.GP_BGP bg) ->
           join_ggps_acc
             (SPARQL11_Algebra.GP_BGP (FStar_List_Tot_Base.append ba bg)) tl
       | (uu___, uu___1) ->
           join_ggps_acc (SPARQL11_Algebra.GP_Join (acc, g)) tl)
let join_ggps (gs : SPARQL11_Algebra.group_graph_pattern Prims.list) :
  SPARQL11_Algebra.group_graph_pattern=
  match gs with
  | [] -> SPARQL11_Algebra.GP_Empty
  | g::[] -> g
  | g::tl -> join_ggps_acc g tl
let rec expand_ce_subject (b : SPARQL11_Algebra.bgp)
  (subj : SPARQL11_Algebra.pattern_subject)
  (op : SPARQL11_Algebra.pattern_term) (fuel : Prims.nat) :
  SPARQL11_Algebra.group_graph_pattern=
  match fuel with
  | uu___ when uu___ = Prims.int_zero ->
      SPARQL11_Algebra.GP_BGP (single_type_bgp subj op)
  | n ->
      (match ce_combinator_for_term b op with
       | FStar_Pervasives_Native.None ->
           SPARQL11_Algebra.GP_BGP (single_type_bgp subj op)
       | FStar_Pervasives_Native.Some (k, CE_Intersect) ->
           (match extract_flat_intersection b k with
            | FStar_Pervasives_Native.None ->
                SPARQL11_Algebra.GP_BGP (single_type_bgp subj op)
            | FStar_Pervasives_Native.Some operands ->
                let step acc o =
                  FStar_List_Tot_Base.append acc
                    [expand_ce_subject b subj o (n - Prims.int_one)] in
                let ggps = FStar_List_Tot_Base.fold_left step [] operands in
                join_ggps ggps)
       | FStar_Pervasives_Native.Some (k, CE_Union) ->
           (match extract_flat_union b k with
            | FStar_Pervasives_Native.None ->
                SPARQL11_Algebra.GP_BGP (single_type_bgp subj op)
            | FStar_Pervasives_Native.Some operands ->
                let step acc o =
                  FStar_List_Tot_Base.append acc
                    [expand_ce_subject b subj o (n - Prims.int_one)] in
                let branches = FStar_List_Tot_Base.fold_left step [] operands in
                (match branches with
                 | [] -> SPARQL11_Algebra.GP_BGP (single_type_bgp subj op)
                 | g::[] -> g
                 | g::tl ->
                     FStar_List_Tot_Base.fold_left
                       (fun acc br -> SPARQL11_Algebra.GP_Union (acc, br)) g
                       tl))
       | FStar_Pervasives_Native.Some (k, CE_SomeValuesFrom) ->
           let on_prop_opt = bgp_find_first_obj b k owl_onProperty_iri in
           let filler_opt = bgp_find_first_obj b k owl_someValuesFrom_iri in
           (match (on_prop_opt, filler_opt) with
            | (FStar_Pervasives_Native.Some (SPARQL11_Algebra.PT_IRI p_iri),
               FStar_Pervasives_Native.Some filler) ->
                let fresh_name = Prims.strcat "_sv_" k in
                let fresh_subj = SPARQL11_Algebra.PS_Var fresh_name in
                let fresh_term = SPARQL11_Algebra.PT_Var fresh_name in
                let prop_triple =
                  {
                    SPARQL11_Algebra.tp_s = subj;
                    SPARQL11_Algebra.tp_p = (SPARQL11_Algebra.PT_IRI p_iri);
                    SPARQL11_Algebra.tp_o = fresh_term
                  } in
                let prop_ggp = SPARQL11_Algebra.GP_BGP [prop_triple] in
                let filler_ggp =
                  expand_ce_subject b fresh_subj filler (n - Prims.int_one) in
                join_ggps [prop_ggp; filler_ggp]
            | (uu___, uu___1) ->
                SPARQL11_Algebra.GP_BGP (single_type_bgp subj op)))
let rec collect_top_markers_acc (b : SPARQL11_Algebra.bgp)
  (markers : (Prims.string * ce_combinator) Prims.list)
  (acc : Prims.string Prims.list) : Prims.string Prims.list=
  match b with
  | [] -> FStar_List_Tot_Base.rev acc
  | tp::rest ->
      (match tp.SPARQL11_Algebra.tp_p with
       | SPARQL11_Algebra.PT_IRI p ->
           if p = rdf_type_iri
           then
             (match pt_marker_key tp.SPARQL11_Algebra.tp_o with
              | FStar_Pervasives_Native.Some k ->
                  let is_marker =
                    FStar_List_Tot_Base.existsb
                      (fun uu___ -> match uu___ with | (k', uu___1) -> k' = k)
                      markers in
                  if
                    is_marker &&
                      (Prims.op_Negation (FStar_List_Tot_Base.mem k acc))
                  then collect_top_markers_acc rest markers (k :: acc)
                  else collect_top_markers_acc rest markers acc
              | FStar_Pervasives_Native.None ->
                  collect_top_markers_acc rest markers acc)
           else collect_top_markers_acc rest markers acc
       | uu___ -> collect_top_markers_acc rest markers acc)
let collect_top_markers (b : SPARQL11_Algebra.bgp)
  (markers : (Prims.string * ce_combinator) Prims.list) :
  Prims.string Prims.list= collect_top_markers_acc b markers []
let is_any_top_consumer (top_markers : Prims.string Prims.list)
  (tp : SPARQL11_Algebra.triple_pattern) : Prims.bool=
  match ((tp.SPARQL11_Algebra.tp_p),
          (pt_marker_key tp.SPARQL11_Algebra.tp_o))
  with
  | (SPARQL11_Algebra.PT_IRI p, FStar_Pervasives_Native.Some k) ->
      (p = rdf_type_iri) && (FStar_List_Tot_Base.mem k top_markers)
  | (uu___, uu___1) -> false
let is_nested_bookkeeping
  (markers : (Prims.string * ce_combinator) Prims.list)
  (all_chain_keys : Prims.string Prims.list)
  (tp : SPARQL11_Algebra.triple_pattern) : Prims.bool=
  match ((ps_marker_key tp.SPARQL11_Algebra.tp_s),
          (tp.SPARQL11_Algebra.tp_p))
  with
  | (FStar_Pervasives_Native.Some sk, SPARQL11_Algebra.PT_IRI p) ->
      let is_marker =
        FStar_List_Tot_Base.existsb
          (fun uu___ -> match uu___ with | (k', uu___1) -> k' = sk) markers in
      let is_on_chain = FStar_List_Tot_Base.mem sk all_chain_keys in
      let marker_meta =
        is_marker &&
          (((((p = owl_intersectionOf_iri) || (p = owl_unionOf_iri)) ||
               (p = owl_onProperty_iri))
              || (p = owl_someValuesFrom_iri))
             ||
             ((p = rdf_type_iri) &&
                (match tp.SPARQL11_Algebra.tp_o with
                 | SPARQL11_Algebra.PT_IRI oi ->
                     (oi = owl_Class_iri) || (oi = owl_Restriction_iri)
                 | uu___ -> false))) in
      let chain_meta =
        is_on_chain && ((p = rdf_first_iri) || (p = rdf_rest_iri)) in
      marker_meta || chain_meta
  | (uu___, uu___1) -> false
let all_chain_keys_for_markers (b : SPARQL11_Algebra.bgp)
  (markers : (Prims.string * ce_combinator) Prims.list) :
  Prims.string Prims.list=
  let step acc km =
    let uu___ = km in
    match uu___ with
    | (k, uu___1) ->
        let head_int = bgp_find_first_obj b k owl_intersectionOf_iri in
        let head_uni = bgp_find_first_obj b k owl_unionOf_iri in
        let head_opt =
          match head_int with
          | FStar_Pervasives_Native.Some h -> FStar_Pervasives_Native.Some h
          | FStar_Pervasives_Native.None -> head_uni in
        (match head_opt with
         | FStar_Pervasives_Native.None -> acc
         | FStar_Pervasives_Native.Some hd ->
             let chain = collection_chain_keys b hd in
             FStar_List_Tot_Base.fold_left
               (fun a c ->
                  if FStar_List_Tot_Base.mem c a
                  then a
                  else FStar_List_Tot_Base.append a [c]) acc chain) in
  FStar_List_Tot_Base.fold_left step [] markers
let rewrite_bgp_nested (b : SPARQL11_Algebra.bgp) :
  SPARQL11_Algebra.group_graph_pattern=
  let markers = find_markers b in
  match markers with
  | [] -> SPARQL11_Algebra.GP_BGP b
  | uu___ ->
      let top_markers = collect_top_markers b markers in
      (match top_markers with
       | [] -> rewrite_bgp_flat b
       | uu___1 ->
           let chain_keys = all_chain_keys_for_markers b markers in
           let residue =
             FStar_List_Tot_Base.fold_left
               (fun acc tp ->
                  if is_nested_bookkeeping markers chain_keys tp
                  then acc
                  else
                    if is_any_top_consumer top_markers tp
                    then acc
                    else FStar_List_Tot_Base.append acc [tp]) [] b in
           let fuel = (FStar_List_Tot_Base.length markers) + Prims.int_one in
           let consumer_ggps =
             FStar_List_Tot_Base.fold_left
               (fun acc tp ->
                  if is_any_top_consumer top_markers tp
                  then
                    FStar_List_Tot_Base.append acc
                      [expand_ce_subject b tp.SPARQL11_Algebra.tp_s
                         tp.SPARQL11_Algebra.tp_o fuel]
                  else acc) [] b in
           (match consumer_ggps with
            | [] ->
                if (FStar_List_Tot_Base.length residue) = Prims.int_zero
                then SPARQL11_Algebra.GP_Empty
                else SPARQL11_Algebra.GP_BGP residue
            | uu___2 ->
                let base =
                  if (FStar_List_Tot_Base.length residue) = Prims.int_zero
                  then SPARQL11_Algebra.GP_Empty
                  else SPARQL11_Algebra.GP_BGP residue in
                FStar_List_Tot_Base.fold_left
                  (fun acc g ->
                     match (acc, g) with
                     | (SPARQL11_Algebra.GP_Empty, uu___3) -> g
                     | (SPARQL11_Algebra.GP_BGP ba, SPARQL11_Algebra.GP_BGP
                        bg) ->
                         SPARQL11_Algebra.GP_BGP
                           (FStar_List_Tot_Base.append ba bg)
                     | (uu___3, uu___4) -> SPARQL11_Algebra.GP_Join (acc, g))
                  base consumer_ggps))
let coalesce_join (na : SPARQL11_Algebra.group_graph_pattern)
  (nb : SPARQL11_Algebra.group_graph_pattern) :
  SPARQL11_Algebra.group_graph_pattern=
  match (na, nb) with
  | (SPARQL11_Algebra.GP_BGP ba, SPARQL11_Algebra.GP_BGP bb) ->
      SPARQL11_Algebra.GP_BGP (FStar_List_Tot_Base.append ba bb)
  | (SPARQL11_Algebra.GP_BGP ba, SPARQL11_Algebra.GP_Join
     (SPARQL11_Algebra.GP_BGP bb, rest)) ->
      SPARQL11_Algebra.GP_Join
        ((SPARQL11_Algebra.GP_BGP (FStar_List_Tot_Base.append ba bb)), rest)
  | (SPARQL11_Algebra.GP_Join (left_spine, SPARQL11_Algebra.GP_BGP ba),
     SPARQL11_Algebra.GP_BGP bb) ->
      SPARQL11_Algebra.GP_Join
        (left_spine,
          (SPARQL11_Algebra.GP_BGP (FStar_List_Tot_Base.append ba bb)))
  | (uu___, uu___1) -> SPARQL11_Algebra.GP_Join (na, nb)
let rec normalise_joins (g : SPARQL11_Algebra.group_graph_pattern) :
  SPARQL11_Algebra.group_graph_pattern=
  match g with
  | SPARQL11_Algebra.GP_BGP b -> SPARQL11_Algebra.GP_BGP b
  | SPARQL11_Algebra.GP_Join (a, b) ->
      coalesce_join (normalise_joins a) (normalise_joins b)
  | SPARQL11_Algebra.GP_LeftJoin (a, b, e) ->
      SPARQL11_Algebra.GP_LeftJoin
        ((normalise_joins a), (normalise_joins b), e)
  | SPARQL11_Algebra.GP_Filter (e, a) ->
      SPARQL11_Algebra.GP_Filter (e, (normalise_joins a))
  | SPARQL11_Algebra.GP_Union (a, b) ->
      SPARQL11_Algebra.GP_Union ((normalise_joins a), (normalise_joins b))
  | SPARQL11_Algebra.GP_Graph (gt, a) ->
      SPARQL11_Algebra.GP_Graph (gt, (normalise_joins a))
  | SPARQL11_Algebra.GP_Minus (a, b) ->
      SPARQL11_Algebra.GP_Minus ((normalise_joins a), (normalise_joins b))
  | SPARQL11_Algebra.GP_Bind (e, v, a) ->
      SPARQL11_Algebra.GP_Bind (e, v, (normalise_joins a))
  | SPARQL11_Algebra.GP_Values (vs, rs) ->
      SPARQL11_Algebra.GP_Values (vs, rs)
  | SPARQL11_Algebra.GP_Service (i, a, s) ->
      SPARQL11_Algebra.GP_Service (i, (normalise_joins a), s)
  | SPARQL11_Algebra.GP_SubSelect q -> SPARQL11_Algebra.GP_SubSelect q
  | SPARQL11_Algebra.GP_PropertyPath (s, pp, o) ->
      SPARQL11_Algebra.GP_PropertyPath (s, pp, o)
  | SPARQL11_Algebra.GP_Empty -> SPARQL11_Algebra.GP_Empty
let rec rewrite_ggp (g : SPARQL11_Algebra.group_graph_pattern) :
  SPARQL11_Algebra.group_graph_pattern=
  match g with
  | SPARQL11_Algebra.GP_BGP b -> rewrite_bgp_nested b
  | SPARQL11_Algebra.GP_Join (a, b) ->
      SPARQL11_Algebra.GP_Join ((rewrite_ggp a), (rewrite_ggp b))
  | SPARQL11_Algebra.GP_LeftJoin (a, b, e) ->
      SPARQL11_Algebra.GP_LeftJoin ((rewrite_ggp a), (rewrite_ggp b), e)
  | SPARQL11_Algebra.GP_Filter (e, a) ->
      SPARQL11_Algebra.GP_Filter (e, (rewrite_ggp a))
  | SPARQL11_Algebra.GP_Union (a, b) ->
      SPARQL11_Algebra.GP_Union ((rewrite_ggp a), (rewrite_ggp b))
  | SPARQL11_Algebra.GP_Graph (gt, a) ->
      SPARQL11_Algebra.GP_Graph (gt, (rewrite_ggp a))
  | SPARQL11_Algebra.GP_Minus (a, b) ->
      SPARQL11_Algebra.GP_Minus ((rewrite_ggp a), (rewrite_ggp b))
  | SPARQL11_Algebra.GP_Bind (e, v, a) ->
      SPARQL11_Algebra.GP_Bind (e, v, (rewrite_ggp a))
  | SPARQL11_Algebra.GP_Values (vs, rs) ->
      SPARQL11_Algebra.GP_Values (vs, rs)
  | SPARQL11_Algebra.GP_Service (i, a, s) ->
      SPARQL11_Algebra.GP_Service (i, (rewrite_ggp a), s)
  | SPARQL11_Algebra.GP_SubSelect q -> SPARQL11_Algebra.GP_SubSelect q
  | SPARQL11_Algebra.GP_PropertyPath (s, pp, o) ->
      SPARQL11_Algebra.GP_PropertyPath (s, pp, o)
  | SPARQL11_Algebra.GP_Empty -> SPARQL11_Algebra.GP_Empty
let rewrite_query (q : SPARQL11_Algebra.query) : SPARQL11_Algebra.query=
  {
    SPARQL11_Algebra.q_base = (q.SPARQL11_Algebra.q_base);
    SPARQL11_Algebra.q_prefixes = (q.SPARQL11_Algebra.q_prefixes);
    SPARQL11_Algebra.q_form = (q.SPARQL11_Algebra.q_form);
    SPARQL11_Algebra.q_dataset = (q.SPARQL11_Algebra.q_dataset);
    SPARQL11_Algebra.q_pattern =
      (rewrite_ggp (normalise_joins q.SPARQL11_Algebra.q_pattern));
    SPARQL11_Algebra.q_group_by = (q.SPARQL11_Algebra.q_group_by);
    SPARQL11_Algebra.q_having = (q.SPARQL11_Algebra.q_having);
    SPARQL11_Algebra.q_modifier = (q.SPARQL11_Algebra.q_modifier);
    SPARQL11_Algebra.q_values = (q.SPARQL11_Algebra.q_values)
  }
let rewrite_query_for_owl_direct (q : SPARQL11_Algebra.query) :
  SPARQL11_Algebra.query= rewrite_query q
