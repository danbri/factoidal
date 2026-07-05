open Prims
type 'a bucket_map = (Prims.string * 'a Prims.list) Prims.list
let rec bucket_lookup : 'a . 'a bucket_map -> Prims.string -> 'a Prims.list =
  fun m k ->
    match m with
    | [] -> []
    | (k', v)::rest -> if k = k' then v else bucket_lookup rest k
let rec bucket_replace_acc :
  'a .
    'a bucket_map ->
      'a bucket_map -> Prims.string -> 'a Prims.list -> 'a bucket_map
  =
  fun acc m k v ->
    match m with
    | [] -> FStar_List_Tot_Base.rev_acc acc [(k, v)]
    | (k', v')::rest ->
        if k = k'
        then FStar_List_Tot_Base.rev_acc acc ((k, v) :: rest)
        else bucket_replace_acc ((k', v') :: acc) rest k v
let bucket_replace (m : 'a bucket_map) (k : Prims.string) (v : 'a Prims.list)
  : 'a bucket_map= bucket_replace_acc [] m k v
let bucket_push (m : 'a bucket_map) (k : Prims.string) (t : 'a) :
  'a bucket_map= bucket_replace m k (t :: (bucket_lookup m k))
let cmp_by_key (key_of : 'a -> Prims.string FStar_Pervasives_Native.option)
  (t1 : 'a) (t2 : 'a) : Prims.int=
  match ((key_of t1), (key_of t2)) with
  | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) ->
      Prims.int_zero
  | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.Some uu___) ->
      (Prims.of_int (-1))
  | (FStar_Pervasives_Native.Some uu___, FStar_Pervasives_Native.None) ->
      Prims.int_one
  | (FStar_Pervasives_Native.Some k1, FStar_Pervasives_Native.Some k2) ->
      FStar_String.compare k1 k2
let rec group_sorted_aux :
  'a .
    ('a -> Prims.string FStar_Pervasives_Native.option) ->
      'a Prims.list ->
        Prims.string FStar_Pervasives_Native.option ->
          'a Prims.list -> 'a bucket_map -> 'a bucket_map
  =
  fun key_of ts cur_key cur_bucket acc ->
    match ts with
    | [] ->
        (match cur_key with
         | FStar_Pervasives_Native.Some k -> (k, cur_bucket) :: acc
         | FStar_Pervasives_Native.None -> acc)
    | t::rest ->
        (match key_of t with
         | FStar_Pervasives_Native.None ->
             group_sorted_aux key_of rest cur_key cur_bucket acc
         | FStar_Pervasives_Native.Some k ->
             (match cur_key with
              | FStar_Pervasives_Native.Some k0 ->
                  if k = k0
                  then
                    group_sorted_aux key_of rest cur_key (t :: cur_bucket)
                      acc
                  else
                    group_sorted_aux key_of rest
                      (FStar_Pervasives_Native.Some k) [t] ((k0, cur_bucket)
                      :: acc)
              | FStar_Pervasives_Native.None ->
                  group_sorted_aux key_of rest
                    (FStar_Pervasives_Native.Some k) [t] acc))
let build_bucket (key_of : 'a -> Prims.string FStar_Pervasives_Native.option)
  (ts : 'a Prims.list) : 'a bucket_map=
  let sorted = FStar_List_Tot_Base.sortWith (cmp_by_key key_of) ts in
  group_sorted_aux key_of sorted FStar_Pervasives_Native.None [] []
type indexed_graph =
  {
  ig_triples: RDF_Triple.triple Prims.list ;
  ig_pred: RDF_Triple.triple bucket_map ;
  ig_subj: RDF_Triple.triple bucket_map ;
  ig_obj: RDF_Triple.triple bucket_map ;
  ig_sp: RDF_Triple.triple bucket_map ;
  ig_po: RDF_Triple.triple bucket_map ;
  ig_so: RDF_Triple.triple bucket_map }
let __proj__Mkindexed_graph__item__ig_triples (projectee : indexed_graph) :
  RDF_Triple.triple Prims.list=
  match projectee with
  | { ig_triples; ig_pred; ig_subj; ig_obj; ig_sp; ig_po; ig_so;_} ->
      ig_triples
let __proj__Mkindexed_graph__item__ig_pred (projectee : indexed_graph) :
  RDF_Triple.triple bucket_map=
  match projectee with
  | { ig_triples; ig_pred; ig_subj; ig_obj; ig_sp; ig_po; ig_so;_} -> ig_pred
let __proj__Mkindexed_graph__item__ig_subj (projectee : indexed_graph) :
  RDF_Triple.triple bucket_map=
  match projectee with
  | { ig_triples; ig_pred; ig_subj; ig_obj; ig_sp; ig_po; ig_so;_} -> ig_subj
let __proj__Mkindexed_graph__item__ig_obj (projectee : indexed_graph) :
  RDF_Triple.triple bucket_map=
  match projectee with
  | { ig_triples; ig_pred; ig_subj; ig_obj; ig_sp; ig_po; ig_so;_} -> ig_obj
let __proj__Mkindexed_graph__item__ig_sp (projectee : indexed_graph) :
  RDF_Triple.triple bucket_map=
  match projectee with
  | { ig_triples; ig_pred; ig_subj; ig_obj; ig_sp; ig_po; ig_so;_} -> ig_sp
let __proj__Mkindexed_graph__item__ig_po (projectee : indexed_graph) :
  RDF_Triple.triple bucket_map=
  match projectee with
  | { ig_triples; ig_pred; ig_subj; ig_obj; ig_sp; ig_po; ig_so;_} -> ig_po
let __proj__Mkindexed_graph__item__ig_so (projectee : indexed_graph) :
  RDF_Triple.triple bucket_map=
  match projectee with
  | { ig_triples; ig_pred; ig_subj; ig_obj; ig_sp; ig_po; ig_so;_} -> ig_so
let subject_to_key (s : RDF_Term.subject) : Prims.string=
  match s with
  | RDF_Term.S_IRI i -> FStar_String.concat "" ["I_"; i]
  | RDF_Term.S_BNode b -> FStar_String.concat "" ["B_"; b]
let term_to_key_opt (o : RDF_Term.rdf_term) :
  Prims.string FStar_Pervasives_Native.option=
  match o with
  | RDF_Term.T_IRI i ->
      FStar_Pervasives_Native.Some (FStar_String.concat "" ["I_"; i])
  | RDF_Term.T_BNode b ->
      FStar_Pervasives_Native.Some (FStar_String.concat "" ["B_"; b])
  | RDF_Term.T_Literal uu___ -> FStar_Pervasives_Native.None
let unit_sep : Prims.string= "\031"
let sp_key (s : RDF_Term.subject) (p : RDF_Term.wf_iri) : Prims.string=
  FStar_String.concat "" [subject_to_key s; unit_sep; p]
let po_key_opt (p : RDF_Term.wf_iri) (o : RDF_Term.rdf_term) :
  Prims.string FStar_Pervasives_Native.option=
  match term_to_key_opt o with
  | FStar_Pervasives_Native.Some k ->
      FStar_Pervasives_Native.Some (FStar_String.concat "" [p; unit_sep; k])
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
let so_key_opt (s : RDF_Term.subject) (o : RDF_Term.rdf_term) :
  Prims.string FStar_Pervasives_Native.option=
  match term_to_key_opt o with
  | FStar_Pervasives_Native.Some k ->
      FStar_Pervasives_Native.Some
        (FStar_String.concat "" [subject_to_key s; unit_sep; k])
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
let find_objects_indexed (ig : indexed_graph) (subj : RDF_Term.subject)
  (pred : RDF_Term.wf_iri) : RDF_Term.rdf_term Prims.list=
  let bucket = bucket_lookup ig.ig_sp (sp_key subj pred) in
  FStar_List_Tot_Base.map (fun t -> t.RDF_Triple.o) bucket
let find_subjects_indexed (ig : indexed_graph) (pred : RDF_Term.wf_iri)
  (obj : RDF_Term.rdf_term) : RDF_Term.subject Prims.list=
  let bucket =
    match po_key_opt pred obj with
    | FStar_Pervasives_Native.Some k -> bucket_lookup ig.ig_po k
    | FStar_Pervasives_Native.None ->
        FStar_List_Tot_Base.filter
          (fun t -> RDF_Term.rdf_term_eq t.RDF_Triple.o obj)
          (bucket_lookup ig.ig_pred pred) in
  FStar_List_Tot_Base.map (fun t -> t.RDF_Triple.s) bucket
let add_triple_to_indexes (ig : indexed_graph) (t : RDF_Triple.triple) :
  indexed_graph=
  let new_pred = bucket_push ig.ig_pred t.RDF_Triple.p t in
  let new_subj = bucket_push ig.ig_subj (subject_to_key t.RDF_Triple.s) t in
  let new_obj =
    match term_to_key_opt t.RDF_Triple.o with
    | FStar_Pervasives_Native.Some k -> bucket_push ig.ig_obj k t
    | FStar_Pervasives_Native.None -> ig.ig_obj in
  let new_sp = bucket_push ig.ig_sp (sp_key t.RDF_Triple.s t.RDF_Triple.p) t in
  let new_po =
    match po_key_opt t.RDF_Triple.p t.RDF_Triple.o with
    | FStar_Pervasives_Native.Some k -> bucket_push ig.ig_po k t
    | FStar_Pervasives_Native.None -> ig.ig_po in
  let new_so =
    match so_key_opt t.RDF_Triple.s t.RDF_Triple.o with
    | FStar_Pervasives_Native.Some k -> bucket_push ig.ig_so k t
    | FStar_Pervasives_Native.None -> ig.ig_so in
  {
    ig_triples = (t :: (ig.ig_triples));
    ig_pred = new_pred;
    ig_subj = new_subj;
    ig_obj = new_obj;
    ig_sp = new_sp;
    ig_po = new_po;
    ig_so = new_so
  }
let rec build_indexed_aux (g : RDF_Triple.triple Prims.list)
  (acc : indexed_graph) : indexed_graph=
  match g with
  | [] -> acc
  | t::rest -> build_indexed_aux rest (add_triple_to_indexes acc t)
let bucket_key_pred (t : RDF_Triple.triple) :
  Prims.string FStar_Pervasives_Native.option=
  FStar_Pervasives_Native.Some (t.RDF_Triple.p)
let bucket_key_subj (t : RDF_Triple.triple) :
  Prims.string FStar_Pervasives_Native.option=
  FStar_Pervasives_Native.Some (subject_to_key t.RDF_Triple.s)
let bucket_key_obj (t : RDF_Triple.triple) :
  Prims.string FStar_Pervasives_Native.option= term_to_key_opt t.RDF_Triple.o
let bucket_key_sp (t : RDF_Triple.triple) :
  Prims.string FStar_Pervasives_Native.option=
  FStar_Pervasives_Native.Some (sp_key t.RDF_Triple.s t.RDF_Triple.p)
let bucket_key_po (t : RDF_Triple.triple) :
  Prims.string FStar_Pervasives_Native.option=
  po_key_opt t.RDF_Triple.p t.RDF_Triple.o
let bucket_key_so (t : RDF_Triple.triple) :
  Prims.string FStar_Pervasives_Native.option=
  so_key_opt t.RDF_Triple.s t.RDF_Triple.o
let empty_indexed : indexed_graph=
  {
    ig_triples = [];
    ig_pred = [];
    ig_subj = [];
    ig_obj = [];
    ig_sp = [];
    ig_po = [];
    ig_so = []
  }
let build_indexed (g : RDF_Triple.triple Prims.list) : indexed_graph=
  {
    ig_triples = g;
    ig_pred = (build_bucket bucket_key_pred g);
    ig_subj = (build_bucket bucket_key_subj g);
    ig_obj = (build_bucket bucket_key_obj g);
    ig_sp = (build_bucket bucket_key_sp g);
    ig_po = (build_bucket bucket_key_po g);
    ig_so = (build_bucket bucket_key_so g)
  }
