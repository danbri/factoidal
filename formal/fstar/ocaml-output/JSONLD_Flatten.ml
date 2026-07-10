open Prims
type nm_node = (Prims.string * Parser_JSON.json_val) Prims.list
type nm_graph = (Prims.string * nm_node) Prims.list
type nm_state =
  {
  nm_graphs: (Prims.string * nm_graph) Prims.list ;
  nm_idmap: (Prims.string * Prims.string) Prims.list ;
  nm_ctr: Prims.nat }
let __proj__Mknm_state__item__nm_graphs (projectee : nm_state) :
  (Prims.string * nm_graph) Prims.list=
  match projectee with | { nm_graphs; nm_idmap; nm_ctr;_} -> nm_graphs
let __proj__Mknm_state__item__nm_idmap (projectee : nm_state) :
  (Prims.string * Prims.string) Prims.list=
  match projectee with | { nm_graphs; nm_idmap; nm_ctr;_} -> nm_idmap
let __proj__Mknm_state__item__nm_ctr (projectee : nm_state) : Prims.nat=
  match projectee with | { nm_graphs; nm_idmap; nm_ctr;_} -> nm_ctr
let rec fl_lookup :
  'a .
    (Prims.string * 'a) Prims.list ->
      Prims.string -> 'a FStar_Pervasives_Native.option
  =
  fun xs k ->
    match xs with
    | [] -> FStar_Pervasives_Native.None
    | (k2, v)::rest ->
        if k2 = k then FStar_Pervasives_Native.Some v else fl_lookup rest k
let rec fl_upd :
  'a .
    (Prims.string * 'a) Prims.list ->
      Prims.string -> 'a -> (Prims.string * 'a) Prims.list
  =
  fun xs k v ->
    match xs with
    | [] -> [(k, v)]
    | (k2, v2)::rest ->
        if k2 = k then (k2, v) :: rest else (k2, v2) :: (fl_upd rest k v)
let rec fl_remove :
  'a .
    (Prims.string * 'a) Prims.list ->
      Prims.string -> (Prims.string * 'a) Prims.list
  =
  fun xs k ->
    match xs with
    | [] -> []
    | (k2, v2)::rest ->
        if k2 = k then rest else (k2, v2) :: (fl_remove rest k)
let rec fl_insert_by_key :
  'a .
    (Prims.string * 'a) ->
      (Prims.string * 'a) Prims.list -> (Prims.string * 'a) Prims.list
  =
  fun kv xs ->
    match xs with
    | [] -> [kv]
    | y::rest ->
        if
          RDF_Graph_Executable.string_lt (FStar_Pervasives_Native.fst kv)
            (FStar_Pervasives_Native.fst y)
        then kv :: xs
        else y :: (fl_insert_by_key kv rest)
let rec fl_sort_by_key :
  'a . (Prims.string * 'a) Prims.list -> (Prims.string * 'a) Prims.list =
  fun xs ->
    match xs with
    | [] -> []
    | kv::rest -> fl_insert_by_key kv (fl_sort_by_key rest)
let rec fl_arr_contains (items : Parser_JSON.json_val Prims.list)
  (v : Parser_JSON.json_val) : Prims.bool=
  match items with
  | [] -> false
  | hd::tl ->
      (Parser_JSONLD.jsonld_expanded_equal hd v) || (fl_arr_contains tl v)
let node_append_prop (n : nm_node) (prop : Prims.string)
  (v : Parser_JSON.json_val) (dedup : Prims.bool) : nm_node=
  match fl_lookup n prop with
  | FStar_Pervasives_Native.Some (Parser_JSON.JArray items) ->
      if dedup && (fl_arr_contains items v)
      then n
      else
        fl_upd n prop
          (Parser_JSON.JArray (FStar_List_Tot_Base.op_At items [v]))
  | FStar_Pervasives_Native.Some other ->
      fl_upd n prop (Parser_JSON.JArray [other; v])
  | FStar_Pervasives_Native.None ->
      FStar_List_Tot_Base.op_At n [(prop, (Parser_JSON.JArray [v]))]
let node_ensure_prop (n : nm_node) (prop : Prims.string) : nm_node=
  match fl_lookup n prop with
  | FStar_Pervasives_Native.Some uu___ -> n
  | FStar_Pervasives_Native.None ->
      FStar_List_Tot_Base.op_At n [(prop, (Parser_JSON.JArray []))]
let rec fl_merge_type_items (existing : Parser_JSON.json_val Prims.list)
  (items : Parser_JSON.json_val Prims.list) :
  Parser_JSON.json_val Prims.list=
  match items with
  | [] -> existing
  | hd::tl ->
      if fl_arr_contains existing hd
      then fl_merge_type_items existing tl
      else fl_merge_type_items (FStar_List_Tot_Base.op_At existing [hd]) tl
let node_merge_types (n : nm_node) (items : Parser_JSON.json_val Prims.list)
  : nm_node=
  match fl_lookup n "@type" with
  | FStar_Pervasives_Native.Some (Parser_JSON.JArray existing) ->
      fl_upd n "@type"
        (Parser_JSON.JArray (fl_merge_type_items existing items))
  | FStar_Pervasives_Native.Some other ->
      fl_upd n "@type"
        (Parser_JSON.JArray (fl_merge_type_items [other] items))
  | FStar_Pervasives_Native.None ->
      FStar_List_Tot_Base.op_At n
        [("@type", (Parser_JSON.JArray (fl_merge_type_items [] items)))]
let node_set_index (n : nm_node) (idx : Parser_JSON.json_val) :
  nm_node FStar_Pervasives_Native.option=
  match fl_lookup n "@index" with
  | FStar_Pervasives_Native.Some old ->
      if Parser_JSONLD.jsonld_expanded_equal old idx
      then FStar_Pervasives_Native.Some n
      else FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.None ->
      FStar_Pervasives_Native.Some
        (FStar_List_Tot_Base.op_At n [("@index", idx)])
let node_has_only_id (n : nm_node) : Prims.bool=
  match n with | (k, uu___)::[] -> k = "@id" | uu___ -> false
let st_graph (st : nm_state) (g : Prims.string) : nm_graph=
  match fl_lookup st.nm_graphs g with
  | FStar_Pervasives_Native.Some gr -> gr
  | FStar_Pervasives_Native.None -> []
let st_put_graph (st : nm_state) (g : Prims.string) (gr : nm_graph) :
  nm_state=
  {
    nm_graphs = (fl_upd st.nm_graphs g gr);
    nm_idmap = (st.nm_idmap);
    nm_ctr = (st.nm_ctr)
  }
let st_ensure_node (st : nm_state) (g : Prims.string) (id : Prims.string) :
  nm_state=
  let gr = st_graph st g in
  match fl_lookup gr id with
  | FStar_Pervasives_Native.Some uu___ -> st_put_graph st g gr
  | FStar_Pervasives_Native.None ->
      st_put_graph st g
        (FStar_List_Tot_Base.op_At gr
           [(id, [("@id", (Parser_JSON.JString id))])])
let st_node_update (st : nm_state) (g : Prims.string) (id : Prims.string)
  (f : nm_node -> nm_node) : nm_state=
  let gr = st_graph st g in
  match fl_lookup gr id with
  | FStar_Pervasives_Native.Some n -> st_put_graph st g (fl_upd gr id (f n))
  | FStar_Pervasives_Native.None ->
      st_put_graph st g
        (FStar_List_Tot_Base.op_At gr
           [(id, (f [("@id", (Parser_JSON.JString id))]))])
let st_add_value (st : nm_state) (agraph : Prims.string)
  (asubj : Parser_JSON.json_val FStar_Pervasives_Native.option)
  (aprop : Prims.string FStar_Pervasives_Native.option)
  (v : Parser_JSON.json_val) (dedup : Prims.bool) : nm_state=
  match (asubj, aprop) with
  | (FStar_Pervasives_Native.Some (Parser_JSON.JString sid),
     FStar_Pervasives_Native.Some p) ->
      st_node_update st agraph sid (fun n -> node_append_prop n p v dedup)
  | (uu___, uu___1) -> st
let fl_issue_keyed (st : nm_state) (old : Prims.string) :
  (Prims.string * nm_state)=
  match fl_lookup st.nm_idmap old with
  | FStar_Pervasives_Native.Some nid -> (nid, st)
  | FStar_Pervasives_Native.None ->
      let nid = FStar_String.concat "" ["_:b"; Prims.string_of_int st.nm_ctr] in
      (nid,
        {
          nm_graphs = (st.nm_graphs);
          nm_idmap = (FStar_List_Tot_Base.op_At st.nm_idmap [(old, nid)]);
          nm_ctr = (st.nm_ctr + Prims.int_one)
        })
let fl_issue_fresh (st : nm_state) : (Prims.string * nm_state)=
  ((FStar_String.concat "" ["_:b"; Prims.string_of_int st.nm_ctr]),
    {
      nm_graphs = (st.nm_graphs);
      nm_idmap = (st.nm_idmap);
      nm_ctr = (st.nm_ctr + Prims.int_one)
    })
let rec fl_relabel_type_items (st : nm_state)
  (items : Parser_JSON.json_val Prims.list) :
  (nm_state * Parser_JSON.json_val Prims.list)=
  match items with
  | [] -> (st, [])
  | (Parser_JSON.JString s)::tl ->
      if Parser_JSONLD.jld_is_bnode_label s
      then
        let uu___ = fl_issue_keyed st s in
        (match uu___ with
         | (nid, st1) ->
             let uu___1 = fl_relabel_type_items st1 tl in
             (match uu___1 with
              | (st2, tl') -> (st2, ((Parser_JSON.JString nid) :: tl'))))
      else
        (let uu___1 = fl_relabel_type_items st tl in
         match uu___1 with
         | (st1, tl') -> (st1, ((Parser_JSON.JString s) :: tl')))
  | hd::tl ->
      let uu___ = fl_relabel_type_items st tl in
      (match uu___ with | (st1, tl') -> (st1, (hd :: tl')))
let fl_relabel_types (st : nm_state)
  (fields : (Prims.string * Parser_JSON.json_val) Prims.list) :
  (nm_state * (Prims.string * Parser_JSON.json_val) Prims.list)=
  match fl_lookup fields "@type" with
  | FStar_Pervasives_Native.Some (Parser_JSON.JArray items) ->
      let uu___ = fl_relabel_type_items st items in
      (match uu___ with
       | (st1, items') ->
           (st1, (fl_upd fields "@type" (Parser_JSON.JArray items'))))
  | FStar_Pervasives_Native.Some (Parser_JSON.JString s) ->
      if Parser_JSONLD.jld_is_bnode_label s
      then
        let uu___ = fl_issue_keyed st s in
        (match uu___ with
         | (nid, st1) ->
             (st1, (fl_upd fields "@type" (Parser_JSON.JString nid))))
      else (st, fields)
  | uu___ -> (st, fields)
let rec nmg (st : nm_state) (element : Parser_JSON.json_val)
  (agraph : Prims.string)
  (asubj : Parser_JSON.json_val FStar_Pervasives_Native.option)
  (aprop : Prims.string FStar_Pervasives_Native.option)
  (acc : Parser_JSON.json_val Prims.list FStar_Pervasives_Native.option)
  (fuel : Prims.nat) :
  (nm_state * Parser_JSON.json_val Prims.list FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (match element with
     | Parser_JSON.JArray items ->
         nmg_items st items agraph asubj aprop acc (fuel - Prims.int_one)
     | Parser_JSON.JObject fields0 ->
         let uu___1 = fl_relabel_types st fields0 in
         (match uu___1 with
          | (st1, fields) ->
              if JSONLD_Expand.jexp_has_field "@value" fields
              then
                (match acc with
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.Some
                       ((st_add_value st1 agraph asubj aprop
                           (Parser_JSON.JObject fields) true),
                         FStar_Pervasives_Native.None)
                 | FStar_Pervasives_Native.Some xs ->
                     FStar_Pervasives_Native.Some
                       (st1,
                         (FStar_Pervasives_Native.Some
                            (FStar_List_Tot_Base.op_At xs
                               [Parser_JSON.JObject fields]))))
              else
                if JSONLD_Expand.jexp_has_field "@list" fields
                then
                  (match fl_lookup fields "@list" with
                   | FStar_Pervasives_Native.None ->
                       FStar_Pervasives_Native.None
                   | FStar_Pervasives_Native.Some lval ->
                       (match nmg st1 lval agraph asubj aprop
                                (FStar_Pervasives_Native.Some [])
                                (fuel - Prims.int_one)
                        with
                        | FStar_Pervasives_Native.Some
                            (st11, FStar_Pervasives_Native.Some litems) ->
                            let result =
                              Parser_JSON.JObject
                                [("@list", (Parser_JSON.JArray litems))] in
                            (match acc with
                             | FStar_Pervasives_Native.None ->
                                 FStar_Pervasives_Native.Some
                                   ((st_add_value st11 agraph asubj aprop
                                       result false),
                                     FStar_Pervasives_Native.None)
                             | FStar_Pervasives_Native.Some xs ->
                                 FStar_Pervasives_Native.Some
                                   (st11,
                                     (FStar_Pervasives_Native.Some
                                        (FStar_List_Tot_Base.op_At xs
                                           [result]))))
                        | uu___3 -> FStar_Pervasives_Native.None))
                else
                  nmg_node st1 fields agraph asubj aprop acc
                    (fuel - Prims.int_one))
     | uu___1 -> FStar_Pervasives_Native.Some (st, acc))
and nmg_items (st : nm_state) (items : Parser_JSON.json_val Prims.list)
  (agraph : Prims.string)
  (asubj : Parser_JSON.json_val FStar_Pervasives_Native.option)
  (aprop : Prims.string FStar_Pervasives_Native.option)
  (acc : Parser_JSON.json_val Prims.list FStar_Pervasives_Native.option)
  (fuel : Prims.nat) :
  (nm_state * Parser_JSON.json_val Prims.list FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (match items with
     | [] -> FStar_Pervasives_Native.Some (st, acc)
     | hd::tl ->
         (match nmg st hd agraph asubj aprop acc (fuel - Prims.int_one) with
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (st1, acc1) ->
              nmg_items st1 tl agraph asubj aprop acc1 (fuel - Prims.int_one)))
and nmg_node (st : nm_state)
  (fields : (Prims.string * Parser_JSON.json_val) Prims.list)
  (agraph : Prims.string)
  (asubj : Parser_JSON.json_val FStar_Pervasives_Native.option)
  (aprop : Prims.string FStar_Pervasives_Native.option)
  (acc : Parser_JSON.json_val Prims.list FStar_Pervasives_Native.option)
  (fuel : Prims.nat) :
  (nm_state * Parser_JSON.json_val Prims.list FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (let id_res =
       match fl_lookup fields "@id" with
       | FStar_Pervasives_Native.Some (Parser_JSON.JString s) ->
           if Parser_JSONLD.jld_is_bnode_label s
           then
             let uu___1 = fl_issue_keyed st s in
             (match uu___1 with
              | (nid, st1) ->
                  FStar_Pervasives_Native.Some
                    (st1, nid, (fl_remove fields "@id")))
           else
             FStar_Pervasives_Native.Some (st, s, (fl_remove fields "@id"))
       | FStar_Pervasives_Native.Some uu___1 -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.None ->
           let uu___1 = fl_issue_fresh st in
           (match uu___1 with
            | (nid, st1) -> FStar_Pervasives_Native.Some (st1, nid, fields)) in
     match id_res with
     | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
     | FStar_Pervasives_Native.Some (st1, id, fields1) ->
         let st2 = st_ensure_node st1 agraph id in
         let uu___1 =
           match asubj with
           | FStar_Pervasives_Native.Some (Parser_JSON.JObject reffields) ->
               (match aprop with
                | FStar_Pervasives_Native.Some p ->
                    ((st_node_update st2 agraph id
                        (fun n ->
                           node_append_prop n p
                             (Parser_JSON.JObject reffields) true)), acc)
                | FStar_Pervasives_Native.None -> (st2, acc))
           | uu___2 ->
               (match aprop with
                | FStar_Pervasives_Native.None -> (st2, acc)
                | FStar_Pervasives_Native.Some p ->
                    let reference =
                      Parser_JSON.JObject [("@id", (Parser_JSON.JString id))] in
                    (match acc with
                     | FStar_Pervasives_Native.Some xs ->
                         (st2,
                           (FStar_Pervasives_Native.Some
                              (FStar_List_Tot_Base.op_At xs [reference])))
                     | FStar_Pervasives_Native.None ->
                         ((st_add_value st2 agraph asubj
                             (FStar_Pervasives_Native.Some p) reference true),
                           FStar_Pervasives_Native.None))) in
         (match uu___1 with
          | (st3, acc1) ->
              let st4 =
                match fl_lookup fields1 "@type" with
                | FStar_Pervasives_Native.Some (Parser_JSON.JArray items) ->
                    st_node_update st3 agraph id
                      (fun n -> node_merge_types n items)
                | FStar_Pervasives_Native.Some (Parser_JSON.JString s) ->
                    st_node_update st3 agraph id
                      (fun n -> node_merge_types n [Parser_JSON.JString s])
                | uu___2 -> st3 in
              let fields2 = fl_remove fields1 "@type" in
              let idx_res =
                match fl_lookup fields2 "@index" with
                | FStar_Pervasives_Native.Some idx ->
                    let gr = st_graph st4 agraph in
                    (match fl_lookup gr id with
                     | FStar_Pervasives_Native.Some n ->
                         (match node_set_index n idx with
                          | FStar_Pervasives_Native.None ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some n1 ->
                              FStar_Pervasives_Native.Some
                                ((st_put_graph st4 agraph (fl_upd gr id n1)),
                                  (fl_remove fields2 "@index")))
                     | FStar_Pervasives_Native.None ->
                         FStar_Pervasives_Native.Some
                           (st4, (fl_remove fields2 "@index")))
                | FStar_Pervasives_Native.None ->
                    FStar_Pervasives_Native.Some (st4, fields2) in
              (match idx_res with
               | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some (st5, fields3) ->
                   let rev_res =
                     match fl_lookup fields3 "@reverse" with
                     | FStar_Pervasives_Native.Some (Parser_JSON.JObject
                         rentries) ->
                         nmg_reverse_entries st5
                           (JSONLD_Expand.jexp_sort_map_entries rentries)
                           agraph id (fuel - Prims.int_one)
                     | FStar_Pervasives_Native.Some uu___2 ->
                         FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.None ->
                         FStar_Pervasives_Native.Some st5 in
                   (match rev_res with
                    | FStar_Pervasives_Native.None ->
                        FStar_Pervasives_Native.None
                    | FStar_Pervasives_Native.Some st6 ->
                        let fields4 = fl_remove fields3 "@reverse" in
                        let graph_res =
                          match fl_lookup fields4 "@graph" with
                          | FStar_Pervasives_Native.Some gval ->
                              (match nmg st6 gval id
                                       FStar_Pervasives_Native.None
                                       FStar_Pervasives_Native.None
                                       FStar_Pervasives_Native.None
                                       (fuel - Prims.int_one)
                               with
                               | FStar_Pervasives_Native.Some (st11, uu___2)
                                   -> FStar_Pervasives_Native.Some st11
                               | FStar_Pervasives_Native.None ->
                                   FStar_Pervasives_Native.None)
                          | FStar_Pervasives_Native.None ->
                              FStar_Pervasives_Native.Some st6 in
                        (match graph_res with
                         | FStar_Pervasives_Native.None ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some st7 ->
                             let fields5 = fl_remove fields4 "@graph" in
                             let incl_res =
                               match fl_lookup fields5 "@included" with
                               | FStar_Pervasives_Native.Some ival ->
                                   (match nmg st7 ival agraph
                                            FStar_Pervasives_Native.None
                                            FStar_Pervasives_Native.None
                                            FStar_Pervasives_Native.None
                                            (fuel - Prims.int_one)
                                    with
                                    | FStar_Pervasives_Native.Some
                                        (st11, uu___2) ->
                                        FStar_Pervasives_Native.Some st11
                                    | FStar_Pervasives_Native.None ->
                                        FStar_Pervasives_Native.None)
                               | FStar_Pervasives_Native.None ->
                                   FStar_Pervasives_Native.Some st7 in
                             (match incl_res with
                              | FStar_Pervasives_Native.None ->
                                  FStar_Pervasives_Native.None
                              | FStar_Pervasives_Native.Some st8 ->
                                  let fields6 = fl_remove fields5 "@included" in
                                  (match nmg_props st8
                                           (JSONLD_Expand.jexp_sort_map_entries
                                              fields6) agraph id
                                           (fuel - Prims.int_one)
                                   with
                                   | FStar_Pervasives_Native.None ->
                                       FStar_Pervasives_Native.None
                                   | FStar_Pervasives_Native.Some st9 ->
                                       FStar_Pervasives_Native.Some
                                         (st9, acc1))))))))
and nmg_props (st : nm_state)
  (props : (Prims.string * Parser_JSON.json_val) Prims.list)
  (agraph : Prims.string) (id : Prims.string) (fuel : Prims.nat) :
  nm_state FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (match props with
     | [] -> FStar_Pervasives_Native.Some st
     | (p, v)::tl ->
         let uu___1 =
           if Parser_JSONLD.jld_is_bnode_label p
           then fl_issue_keyed st p
           else (p, st) in
         (match uu___1 with
          | (p', st1) ->
              let st2 =
                st_node_update st1 agraph id (fun n -> node_ensure_prop n p') in
              (match nmg st2 v agraph
                       (FStar_Pervasives_Native.Some (Parser_JSON.JString id))
                       (FStar_Pervasives_Native.Some p')
                       FStar_Pervasives_Native.None (fuel - Prims.int_one)
               with
               | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some (st11, uu___2) ->
                   nmg_props st11 tl agraph id (fuel - Prims.int_one))))
and nmg_reverse_entries (st : nm_state)
  (entries : (Prims.string * Parser_JSON.json_val) Prims.list)
  (agraph : Prims.string) (id : Prims.string) (fuel : Prims.nat) :
  nm_state FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (match entries with
     | [] -> FStar_Pervasives_Native.Some st
     | (p, vals)::tl ->
         (match nmg_reverse_values st (Parser_JSONLD.jld_as_array vals) p
                  agraph id (fuel - Prims.int_one)
          with
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some st1 ->
              nmg_reverse_entries st1 tl agraph id (fuel - Prims.int_one)))
and nmg_reverse_values (st : nm_state)
  (vals : Parser_JSON.json_val Prims.list) (p : Prims.string)
  (agraph : Prims.string) (id : Prims.string) (fuel : Prims.nat) :
  nm_state FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (match vals with
     | [] -> FStar_Pervasives_Native.Some st
     | v::tl ->
         (match nmg st v agraph
                  (FStar_Pervasives_Native.Some
                     (Parser_JSON.JObject [("@id", (Parser_JSON.JString id))]))
                  (FStar_Pervasives_Native.Some p)
                  FStar_Pervasives_Native.None (fuel - Prims.int_one)
          with
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (st1, uu___1) ->
              nmg_reverse_values st1 tl p agraph id (fuel - Prims.int_one)))
let rec fl_emit_nodes (nodes : (Prims.string * nm_node) Prims.list) :
  Parser_JSON.json_val Prims.list=
  match nodes with
  | [] -> []
  | (uu___, n)::tl ->
      if node_has_only_id n
      then fl_emit_nodes tl
      else (Parser_JSON.JObject n) :: (fl_emit_nodes tl)
let rec fl_filter_named (graphs : (Prims.string * nm_graph) Prims.list) :
  (Prims.string * nm_graph) Prims.list=
  match graphs with
  | [] -> []
  | (g, gr)::tl ->
      if g = "@default"
      then fl_filter_named tl
      else (g, gr) :: (fl_filter_named tl)
let rec fl_fold_named (dflt : nm_graph)
  (named : (Prims.string * nm_graph) Prims.list) : nm_graph=
  match named with
  | [] -> dflt
  | (gname, gr)::tl ->
      let gnodes = fl_emit_nodes (fl_sort_by_key gr) in
      let dflt1 =
        match fl_lookup dflt gname with
        | FStar_Pervasives_Native.Some n ->
            fl_upd dflt gname
              (FStar_List_Tot_Base.op_At n
                 [("@graph", (Parser_JSON.JArray gnodes))])
        | FStar_Pervasives_Native.None ->
            FStar_List_Tot_Base.op_At dflt
              [(gname,
                 [("@id", (Parser_JSON.JString gname));
                 ("@graph", (Parser_JSON.JArray gnodes))])] in
      fl_fold_named dflt1 tl
let jld_flatten_expanded (expanded : Parser_JSON.json_val) :
  Parser_JSON.json_val Prims.list FStar_Pervasives_Native.option=
  let fuel =
    ((Prims.of_int (16)) * (Parser_JSON.json_size expanded)) +
      (Prims.of_int (128)) in
  let st0 =
    { nm_graphs = [("@default", [])]; nm_idmap = []; nm_ctr = Prims.int_zero
    } in
  match nmg st0 expanded "@default" FStar_Pervasives_Native.None
          FStar_Pervasives_Native.None FStar_Pervasives_Native.None fuel
  with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some (st, uu___) ->
      let dflt = st_graph st "@default" in
      let named = fl_sort_by_key (fl_filter_named st.nm_graphs) in
      let dflt1 = fl_fold_named dflt named in
      FStar_Pervasives_Native.Some (fl_emit_nodes (fl_sort_by_key dflt1))
let flatten_document (input : Prims.string)
  (ctx_doc : Prims.string FStar_Pervasives_Native.option)
  (base : Prims.string FStar_Pervasives_Native.option)
  (ctx_url : Prims.string FStar_Pervasives_Native.option)
  (compact_arrays : Prims.bool)
  (processing_mode : Prims.string FStar_Pervasives_Native.option) :
  Parser_JSON.json_val FStar_Pervasives_Native.option=
  match Parser_JSONLD.expand_document input base FStar_Pervasives_Native.None
          processing_mode
  with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some expanded ->
      (match jld_flatten_expanded expanded with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some flattened ->
           (match ctx_doc with
            | FStar_Pervasives_Native.None ->
                FStar_Pervasives_Native.Some (Parser_JSON.JArray flattened)
            | FStar_Pervasives_Native.Some ctx_text ->
                (match Parser_JSON.parse_json ctx_text with
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.None
                 | FStar_Pervasives_Native.Some ctx_root ->
                     let ctx_val =
                       match ctx_root with
                       | Parser_JSON.JObject cf ->
                           (match JSONLD_Compact.cmp_field cf "@context" with
                            | FStar_Pervasives_Native.Some c -> c
                            | FStar_Pervasives_Native.None -> ctx_root)
                       | uu___ -> ctx_root in
                     let mode10 =
                       processing_mode =
                         (FStar_Pervasives_Native.Some "json-ld-1.0") in
                     let ac_seed =
                       {
                         JSONLD_Context.ac_terms =
                           (JSONLD_Context.empty_active_context.JSONLD_Context.ac_terms);
                         JSONLD_Context.ac_vocab =
                           (JSONLD_Context.empty_active_context.JSONLD_Context.ac_vocab);
                         JSONLD_Context.ac_base = base;
                         JSONLD_Context.ac_language =
                           (JSONLD_Context.empty_active_context.JSONLD_Context.ac_language);
                         JSONLD_Context.ac_direction =
                           (JSONLD_Context.empty_active_context.JSONLD_Context.ac_direction);
                         JSONLD_Context.ac_previous =
                           (JSONLD_Context.empty_active_context.JSONLD_Context.ac_previous);
                         JSONLD_Context.ac_mode10 = mode10;
                         JSONLD_Context.ac_doc_url =
                           (match ctx_url with
                            | FStar_Pervasives_Native.Some u ->
                                FStar_Pervasives_Native.Some u
                            | FStar_Pervasives_Native.None -> base);
                         JSONLD_Context.ac_original_base = base;
                         JSONLD_Context.ac_suppress_pop =
                           (JSONLD_Context.empty_active_context.JSONLD_Context.ac_suppress_pop)
                       } in
                     (match JSONLD_Context.context_process ac_seed ctx_val
                              false JSONLD_Context.jld_remote_context_fuel []
                      with
                      | FStar_Pervasives_Native.None ->
                          FStar_Pervasives_Native.None
                      | FStar_Pervasives_Native.Some ac ->
                          let co =
                            {
                              JSONLD_Compact.co_arrays = compact_arrays;
                              JSONLD_Compact.co_rel = true
                            } in
                          let farr = Parser_JSON.JArray flattened in
                          let fuel =
                            ((Prims.of_int (16)) *
                               (Parser_JSON.json_size farr))
                              + (Prims.of_int (128)) in
                          (match JSONLD_Compact.compact_elem ac
                                   FStar_Pervasives_Native.None farr co fuel
                           with
                           | FStar_Pervasives_Native.None ->
                               FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some compacted0 ->
                               let garr =
                                 match compacted0 with
                                 | Parser_JSON.JArray xs ->
                                     Parser_JSON.JArray xs
                                 | other -> Parser_JSON.JArray [other] in
                               let gkey =
                                 JSONLD_Compact.cmp_alias_kw ac co "@graph" in
                               if JSONLD_Compact.cmp_ctx_is_empty ctx_val
                               then
                                 FStar_Pervasives_Native.Some
                                   (Parser_JSON.JObject [(gkey, garr)])
                               else
                                 FStar_Pervasives_Native.Some
                                   (Parser_JSON.JObject
                                      [("@context", ctx_val); (gkey, garr)]))))))
