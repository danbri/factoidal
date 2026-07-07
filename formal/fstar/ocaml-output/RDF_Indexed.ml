open Prims
type 'a bucket_tree =
  | BLeaf 
  | BNode of Prims.string * 'a Prims.list * 'a bucket_tree * 'a bucket_tree 
let uu___is_BLeaf (projectee : 'a bucket_tree) : Prims.bool=
  match projectee with | BLeaf -> true | uu___ -> false
let uu___is_BNode (projectee : 'a bucket_tree) : Prims.bool=
  match projectee with
  | BNode (key, value, left, right) -> true
  | uu___ -> false
let __proj__BNode__item__key (projectee : 'a bucket_tree) : Prims.string=
  match projectee with | BNode (key, value, left, right) -> key
let __proj__BNode__item__value (projectee : 'a bucket_tree) : 'a Prims.list=
  match projectee with | BNode (key, value, left, right) -> value
let __proj__BNode__item__left (projectee : 'a bucket_tree) : 'a bucket_tree=
  match projectee with | BNode (key, value, left, right) -> left
let __proj__BNode__item__right (projectee : 'a bucket_tree) : 'a bucket_tree=
  match projectee with | BNode (key, value, left, right) -> right
type 'a bucket_map = 'a bucket_tree
let rec bucket_lookup : 'a . 'a bucket_map -> Prims.string -> 'a Prims.list =
  fun m k ->
    match m with
    | BLeaf -> []
    | BNode (k', v, l, r) ->
        if k = k'
        then v
        else
          if (FStar_String.compare k k') < Prims.int_zero
          then bucket_lookup l k
          else bucket_lookup r k
let rec bucket_replace :
  'a . 'a bucket_map -> Prims.string -> 'a Prims.list -> 'a bucket_map =
  fun m k v ->
    match m with
    | BLeaf -> BNode (k, v, BLeaf, BLeaf)
    | BNode (k', v', l, r) ->
        if k = k'
        then BNode (k', v, l, r)
        else
          if (FStar_String.compare k k') < Prims.int_zero
          then BNode (k', v', (bucket_replace l k v), r)
          else BNode (k', v', l, (bucket_replace r k v))
let bucket_push (m : 'a bucket_map) (k : Prims.string) (t : 'a) :
  'a bucket_map= bucket_replace m k (t :: (bucket_lookup m k))
let rec bucket_tree_values : 'a . 'a bucket_tree -> 'a Prims.list =
  fun t ->
    match t with
    | BLeaf -> []
    | BNode (uu___, v, l, r) ->
        FStar_List_Tot_Base.append (bucket_tree_values l)
          (FStar_List_Tot_Base.append v (bucket_tree_values r))
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
let cmp_by_decorated_key
  (p1 : (Prims.string FStar_Pervasives_Native.option * 'a))
  (p2 : (Prims.string FStar_Pervasives_Native.option * 'a)) : Prims.int=
  match ((FStar_Pervasives_Native.fst p1), (FStar_Pervasives_Native.fst p2))
  with
  | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) ->
      Prims.int_zero
  | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.Some uu___) ->
      (Prims.of_int (-1))
  | (FStar_Pervasives_Native.Some uu___, FStar_Pervasives_Native.None) ->
      Prims.int_one
  | (FStar_Pervasives_Native.Some k1, FStar_Pervasives_Native.Some k2) ->
      FStar_String.compare k1 k2
let rec group_sorted_decorated_aux :
  'a .
    (Prims.string FStar_Pervasives_Native.option * 'a) Prims.list ->
      Prims.string FStar_Pervasives_Native.option ->
        'a Prims.list ->
          (Prims.string * 'a Prims.list) Prims.list ->
            (Prims.string * 'a Prims.list) Prims.list
  =
  fun ts cur_key cur_bucket acc ->
    match ts with
    | [] ->
        (match cur_key with
         | FStar_Pervasives_Native.Some k -> (k, cur_bucket) :: acc
         | FStar_Pervasives_Native.None -> acc)
    | (k, t)::rest ->
        (match k with
         | FStar_Pervasives_Native.None ->
             group_sorted_decorated_aux rest cur_key cur_bucket acc
         | FStar_Pervasives_Native.Some kk ->
             (match cur_key with
              | FStar_Pervasives_Native.Some k0 ->
                  if kk = k0
                  then
                    group_sorted_decorated_aux rest cur_key (t :: cur_bucket)
                      acc
                  else
                    group_sorted_decorated_aux rest
                      (FStar_Pervasives_Native.Some kk) [t] ((k0, cur_bucket)
                      :: acc)
              | FStar_Pervasives_Native.None ->
                  group_sorted_decorated_aux rest
                    (FStar_Pervasives_Native.Some kk) [t] acc))
let rec group_sorted_aux :
  'a .
    ('a -> Prims.string FStar_Pervasives_Native.option) ->
      'a Prims.list ->
        Prims.string FStar_Pervasives_Native.option ->
          'a Prims.list ->
            (Prims.string * 'a Prims.list) Prims.list ->
              (Prims.string * 'a Prims.list) Prims.list
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
let rec take_prefix_acc :
  'a .
    Prims.nat ->
      'a Prims.list -> 'a Prims.list -> ('a Prims.list * 'a Prims.list)
  =
  fun n acc xs ->
    if n = Prims.int_zero
    then ((FStar_List_Tot_Base.rev acc), xs)
    else
      (match xs with
       | [] -> ((FStar_List_Tot_Base.rev acc), [])
       | hd::tl -> take_prefix_acc (n - Prims.int_one) (hd :: acc) tl)
let take_prefix (n : Prims.nat) (xs : 'a Prims.list) :
  ('a Prims.list * 'a Prims.list)= take_prefix_acc n [] xs
let rec sorted_list_to_tree_fuel :
  'a .
    (Prims.string * 'a Prims.list) Prims.list -> Prims.nat -> 'a bucket_tree
  =
  fun xs fuel ->
    match xs with
    | [] -> BLeaf
    | uu___ ->
        if fuel = Prims.int_zero
        then BLeaf
        else
          (let n = FStar_List_Tot_Base.length xs in
           let mid = n / (Prims.of_int (2)) in
           let uu___2 = take_prefix mid xs in
           match uu___2 with
           | (left_xs, rest) ->
               (match rest with
                | (k, v)::right_xs ->
                    BNode
                      (k, v,
                        (sorted_list_to_tree_fuel left_xs
                           (fuel - Prims.int_one)),
                        (sorted_list_to_tree_fuel right_xs
                           (fuel - Prims.int_one)))
                | [] -> BLeaf))
let sorted_list_to_tree (xs : (Prims.string * 'a Prims.list) Prims.list) :
  'a bucket_tree= sorted_list_to_tree_fuel xs (FStar_List_Tot_Base.length xs)
let build_bucket (key_of : 'a -> Prims.string FStar_Pervasives_Native.option)
  (ts : 'a Prims.list) : 'a bucket_map=
  let decorated = FStar_List_Tot_Base.map (fun t -> ((key_of t), t)) ts in
  let sorted = FStar_List_Tot_Base.sortWith cmp_by_decorated_key decorated in
  let grouped =
    group_sorted_decorated_aux sorted FStar_Pervasives_Native.None [] [] in
  let ascending = FStar_List_Tot_Base.rev grouped in
  sorted_list_to_tree ascending
type bucket_needs =
  {
  bn_pred: Prims.bool ;
  bn_subj: Prims.bool ;
  bn_obj: Prims.bool ;
  bn_sp: Prims.bool ;
  bn_po: Prims.bool ;
  bn_so: Prims.bool }
let __proj__Mkbucket_needs__item__bn_pred (projectee : bucket_needs) :
  Prims.bool=
  match projectee with
  | { bn_pred; bn_subj; bn_obj; bn_sp; bn_po; bn_so;_} -> bn_pred
let __proj__Mkbucket_needs__item__bn_subj (projectee : bucket_needs) :
  Prims.bool=
  match projectee with
  | { bn_pred; bn_subj; bn_obj; bn_sp; bn_po; bn_so;_} -> bn_subj
let __proj__Mkbucket_needs__item__bn_obj (projectee : bucket_needs) :
  Prims.bool=
  match projectee with
  | { bn_pred; bn_subj; bn_obj; bn_sp; bn_po; bn_so;_} -> bn_obj
let __proj__Mkbucket_needs__item__bn_sp (projectee : bucket_needs) :
  Prims.bool=
  match projectee with
  | { bn_pred; bn_subj; bn_obj; bn_sp; bn_po; bn_so;_} -> bn_sp
let __proj__Mkbucket_needs__item__bn_po (projectee : bucket_needs) :
  Prims.bool=
  match projectee with
  | { bn_pred; bn_subj; bn_obj; bn_sp; bn_po; bn_so;_} -> bn_po
let __proj__Mkbucket_needs__item__bn_so (projectee : bucket_needs) :
  Prims.bool=
  match projectee with
  | { bn_pred; bn_subj; bn_obj; bn_sp; bn_po; bn_so;_} -> bn_so
let all_bucket_needs : bucket_needs=
  {
    bn_pred = true;
    bn_subj = true;
    bn_obj = true;
    bn_sp = true;
    bn_po = true;
    bn_so = true
  }
let no_bucket_needs : bucket_needs=
  {
    bn_pred = false;
    bn_subj = false;
    bn_obj = false;
    bn_sp = false;
    bn_po = false;
    bn_so = false
  }
let bucket_needs_or (a : bucket_needs) (b : bucket_needs) : bucket_needs=
  {
    bn_pred = (a.bn_pred || b.bn_pred);
    bn_subj = (a.bn_subj || b.bn_subj);
    bn_obj = (a.bn_obj || b.bn_obj);
    bn_sp = (a.bn_sp || b.bn_sp);
    bn_po = (a.bn_po || b.bn_po);
    bn_so = (a.bn_so || b.bn_so)
  }
type indexed_graph =
  {
  ig_triples: RDF_Triple.triple Prims.list ;
  ig_pred: RDF_Triple.triple bucket_map ;
  ig_subj: RDF_Triple.triple bucket_map ;
  ig_obj: RDF_Triple.triple bucket_map ;
  ig_sp: RDF_Triple.triple bucket_map ;
  ig_po: RDF_Triple.triple bucket_map ;
  ig_so: RDF_Triple.triple bucket_map ;
  ig_built: bucket_needs }
let __proj__Mkindexed_graph__item__ig_triples (projectee : indexed_graph) :
  RDF_Triple.triple Prims.list=
  match projectee with
  | { ig_triples; ig_pred; ig_subj; ig_obj; ig_sp; ig_po; ig_so; ig_built;_}
      -> ig_triples
let __proj__Mkindexed_graph__item__ig_pred (projectee : indexed_graph) :
  RDF_Triple.triple bucket_map=
  match projectee with
  | { ig_triples; ig_pred; ig_subj; ig_obj; ig_sp; ig_po; ig_so; ig_built;_}
      -> ig_pred
let __proj__Mkindexed_graph__item__ig_subj (projectee : indexed_graph) :
  RDF_Triple.triple bucket_map=
  match projectee with
  | { ig_triples; ig_pred; ig_subj; ig_obj; ig_sp; ig_po; ig_so; ig_built;_}
      -> ig_subj
let __proj__Mkindexed_graph__item__ig_obj (projectee : indexed_graph) :
  RDF_Triple.triple bucket_map=
  match projectee with
  | { ig_triples; ig_pred; ig_subj; ig_obj; ig_sp; ig_po; ig_so; ig_built;_}
      -> ig_obj
let __proj__Mkindexed_graph__item__ig_sp (projectee : indexed_graph) :
  RDF_Triple.triple bucket_map=
  match projectee with
  | { ig_triples; ig_pred; ig_subj; ig_obj; ig_sp; ig_po; ig_so; ig_built;_}
      -> ig_sp
let __proj__Mkindexed_graph__item__ig_po (projectee : indexed_graph) :
  RDF_Triple.triple bucket_map=
  match projectee with
  | { ig_triples; ig_pred; ig_subj; ig_obj; ig_sp; ig_po; ig_so; ig_built;_}
      -> ig_po
let __proj__Mkindexed_graph__item__ig_so (projectee : indexed_graph) :
  RDF_Triple.triple bucket_map=
  match projectee with
  | { ig_triples; ig_pred; ig_subj; ig_obj; ig_sp; ig_po; ig_so; ig_built;_}
      -> ig_so
let __proj__Mkindexed_graph__item__ig_built (projectee : indexed_graph) :
  bucket_needs=
  match projectee with
  | { ig_triples; ig_pred; ig_subj; ig_obj; ig_sp; ig_po; ig_so; ig_built;_}
      -> ig_built
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
    ig_so = new_so;
    ig_built = (ig.ig_built)
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
    ig_pred = BLeaf;
    ig_subj = BLeaf;
    ig_obj = BLeaf;
    ig_sp = BLeaf;
    ig_po = BLeaf;
    ig_so = BLeaf;
    ig_built = all_bucket_needs
  }
let build_indexed_selective (needs : bucket_needs)
  (g : RDF_Triple.triple Prims.list) : indexed_graph=
  {
    ig_triples = g;
    ig_pred =
      (if needs.bn_pred then build_bucket bucket_key_pred g else BLeaf);
    ig_subj =
      (if needs.bn_subj then build_bucket bucket_key_subj g else BLeaf);
    ig_obj = (if needs.bn_obj then build_bucket bucket_key_obj g else BLeaf);
    ig_sp = (if needs.bn_sp then build_bucket bucket_key_sp g else BLeaf);
    ig_po = (if needs.bn_po then build_bucket bucket_key_po g else BLeaf);
    ig_so = (if needs.bn_so then build_bucket bucket_key_so g else BLeaf);
    ig_built = needs
  }
let build_indexed (g : RDF_Triple.triple Prims.list) : indexed_graph=
  build_indexed_selective all_bucket_needs g
