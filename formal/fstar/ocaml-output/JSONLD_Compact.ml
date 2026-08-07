open Prims
type cmp_opts = {
  co_arrays: Prims.bool ;
  co_rel: Prims.bool }
let __proj__Mkcmp_opts__item__co_arrays (projectee : cmp_opts) : Prims.bool=
  match projectee with | { co_arrays; co_rel;_} -> co_arrays
let __proj__Mkcmp_opts__item__co_rel (projectee : cmp_opts) : Prims.bool=
  match projectee with | { co_arrays; co_rel;_} -> co_rel
let rec cmp_lookup :
  'a .
    (Prims.string * 'a) Prims.list ->
      Prims.string -> 'a FStar_Pervasives_Native.option
  =
  fun xs k ->
    match xs with
    | [] -> FStar_Pervasives_Native.None
    | (k2, v)::rest ->
        if k2 = k then FStar_Pervasives_Native.Some v else cmp_lookup rest k
let cmp_field (fields : (Prims.string * Parser_JSON.json_val) Prims.list)
  (k : Prims.string) : Parser_JSON.json_val FStar_Pervasives_Native.option=
  cmp_lookup fields k
let cmp_obj_field (v : Parser_JSON.json_val) (k : Prims.string) :
  Parser_JSON.json_val FStar_Pervasives_Native.option=
  match v with
  | Parser_JSON.JObject fields -> cmp_field fields k
  | uu___ -> FStar_Pervasives_Native.None
let cmp_is_scalar (v : Parser_JSON.json_val) : Prims.bool=
  match v with
  | Parser_JSON.JNull -> true
  | Parser_JSON.JBool uu___ -> true
  | Parser_JSON.JString uu___ -> true
  | Parser_JSON.JNumber uu___ -> true
  | uu___ -> false
let cmp_is_value_object (v : Parser_JSON.json_val) : Prims.bool=
  match v with
  | Parser_JSON.JObject fields ->
      JSONLD_Expand.jexp_has_field "@value" fields
  | uu___ -> false
let cmp_is_list_object (v : Parser_JSON.json_val) : Prims.bool=
  match v with
  | Parser_JSON.JObject fields -> JSONLD_Expand.jexp_has_field "@list" fields
  | uu___ -> false
let rec cmp_only_graph_keys
  (fields : (Prims.string * Parser_JSON.json_val) Prims.list) : Prims.bool=
  match fields with
  | [] -> true
  | (k, uu___)::rest ->
      (((k = "@graph") || (k = "@id")) || (k = "@index")) &&
        (cmp_only_graph_keys rest)
let cmp_is_graph_object (v : Parser_JSON.json_val) : Prims.bool=
  match v with
  | Parser_JSON.JObject fields ->
      (JSONLD_Expand.jexp_has_field "@graph" fields) &&
        (cmp_only_graph_keys fields)
  | uu___ -> false
let cmp_is_simple_graph (v : Parser_JSON.json_val) : Prims.bool=
  (cmp_is_graph_object v) &&
    (match v with
     | Parser_JSON.JObject fields ->
         Prims.op_Negation (JSONLD_Expand.jexp_has_field "@id" fields)
     | uu___ -> false)
let cmp_lower (s : Prims.string) : Prims.string= FStar_String.lowercase s
let cmp_concat (xs : Prims.string Prims.list) : Prims.string=
  FStar_String.concat "" xs
let cmp_term_less (a : Prims.string) (b : Prims.string) : Prims.bool=
  let la = Parser_FastString.fs_byte_length a in
  let lb = Parser_FastString.fs_byte_length b in
  if la < lb
  then true
  else if la > lb then false else RDF_Graph_Executable.string_lt a b
let cmp_starts_with (s : Prims.string) (p : Prims.string) : Prims.bool=
  let lp = Parser_FastString.fs_byte_length p in
  ((Parser_FastString.fs_byte_length s) >= lp) &&
    ((Parser_FastString.fs_byte_sub s Prims.int_zero lp) = p)
let rec cmp_keys_only
  (fields : (Prims.string * Parser_JSON.json_val) Prims.list)
  (allowed : Prims.string Prims.list) : Prims.bool=
  match fields with
  | [] -> true
  | (k, uu___)::rest ->
      (FStar_List_Tot_Base.mem k allowed) && (cmp_keys_only rest allowed)
let rec cmp_remove_key
  (xs : (Prims.string * Parser_JSON.json_val) Prims.list) (k : Prims.string)
  : (Prims.string * Parser_JSON.json_val) Prims.list=
  match xs with
  | [] -> []
  | (k2, v)::rest ->
      if k2 = k
      then cmp_remove_key rest k
      else (k2, v) :: (cmp_remove_key rest k)
let rec cmp_replace_or_add
  (xs : (Prims.string * Parser_JSON.json_val) Prims.list) (k : Prims.string)
  (v : Parser_JSON.json_val) :
  (Prims.string * Parser_JSON.json_val) Prims.list=
  match xs with
  | [] -> [(k, v)]
  | (k2, v2)::rest ->
      if k2 = k
      then (k2, v) :: rest
      else (k2, v2) :: (cmp_replace_or_add rest k v)
let cmp_merge_into (existing : Parser_JSON.json_val)
  (v : Parser_JSON.json_val) : Parser_JSON.json_val=
  match existing with
  | Parser_JSON.JArray xs ->
      Parser_JSON.JArray (FStar_List_Tot_Base.append xs [v])
  | x -> Parser_JSON.JArray [x; v]
let rec cmp_add_value
  (res : (Prims.string * Parser_JSON.json_val) Prims.list) (k : Prims.string)
  (v : Parser_JSON.json_val) (as_array : Prims.bool) :
  (Prims.string * Parser_JSON.json_val) Prims.list=
  match res with
  | [] -> [(k, (if as_array then Parser_JSON.JArray [v] else v))]
  | (k2, v2)::rest ->
      if k2 = k
      then (k2, (cmp_merge_into v2 v)) :: rest
      else (k2, v2) :: (cmp_add_value rest k v as_array)
let rec cmp_add_values
  (res : (Prims.string * Parser_JSON.json_val) Prims.list) (k : Prims.string)
  (vs : Parser_JSON.json_val Prims.list) (as_array : Prims.bool) :
  (Prims.string * Parser_JSON.json_val) Prims.list=
  match vs with
  | [] -> res
  | v::rest ->
      cmp_add_values (cmp_add_value res k v as_array) k rest as_array
let cmp_generic_add (res : (Prims.string * Parser_JSON.json_val) Prims.list)
  (k : Prims.string) (v : Parser_JSON.json_val) (as_array : Prims.bool) :
  (Prims.string * Parser_JSON.json_val) Prims.list=
  match v with
  | Parser_JSON.JArray [] ->
      (match cmp_lookup res k with
       | FStar_Pervasives_Native.Some uu___ -> res
       | FStar_Pervasives_Native.None ->
           FStar_List_Tot_Base.append res [(k, (Parser_JSON.JArray []))])
  | Parser_JSON.JArray xs -> cmp_add_values res k xs as_array
  | x -> cmp_add_value res k x as_array
let cmp_nested_get (res : (Prims.string * Parser_JSON.json_val) Prims.list)
  (nest : Prims.string FStar_Pervasives_Native.option) :
  (Prims.string * Parser_JSON.json_val) Prims.list=
  match nest with
  | FStar_Pervasives_Native.None -> res
  | FStar_Pervasives_Native.Some nk ->
      (match cmp_lookup res nk with
       | FStar_Pervasives_Native.Some (Parser_JSON.JObject nf) -> nf
       | uu___ -> [])
let cmp_nested_put (res : (Prims.string * Parser_JSON.json_val) Prims.list)
  (nest : Prims.string FStar_Pervasives_Native.option)
  (nres : (Prims.string * Parser_JSON.json_val) Prims.list) :
  (Prims.string * Parser_JSON.json_val) Prims.list=
  match nest with
  | FStar_Pervasives_Native.None -> nres
  | FStar_Pervasives_Native.Some nk ->
      cmp_replace_or_add res nk (Parser_JSON.JObject nres)
let cmp_container_list (td : JSONLD_Context.term_def) :
  Prims.string Prims.list=
  let base =
    match td.JSONLD_Context.td_container with
    | JSONLD_Context.CK_None -> []
    | JSONLD_Context.CK_List -> ["@list"]
    | JSONLD_Context.CK_Index -> ["@index"]
    | JSONLD_Context.CK_Language -> ["@language"]
    | JSONLD_Context.CK_Id -> ["@id"]
    | JSONLD_Context.CK_Type -> ["@type"]
    | JSONLD_Context.CK_Graph -> ["@graph"]
    | JSONLD_Context.CK_GraphId -> ["@graph"; "@id"]
    | JSONLD_Context.CK_GraphIndex -> ["@graph"; "@index"] in
  if td.JSONLD_Context.td_set
  then FStar_List_Tot_Base.append base ["@set"]
  else base
let cmp_container_key (td : JSONLD_Context.term_def) : Prims.string=
  match JSONLD_Context.jldctx_sort_strings (cmp_container_list td) with
  | [] -> "@none"
  | xs -> cmp_concat xs
let cmp_aprop_td (ac : JSONLD_Context.active_context)
  (aprop : Prims.string FStar_Pervasives_Native.option) :
  JSONLD_Context.term_def FStar_Pervasives_Native.option=
  match aprop with
  | FStar_Pervasives_Native.Some p ->
      (match JSONLD_Context.jldctx_find_term ac.JSONLD_Context.ac_terms p
       with
       | FStar_Pervasives_Native.Some td ->
           if td.JSONLD_Context.td_iri = "@null"
           then FStar_Pervasives_Native.None
           else FStar_Pervasives_Native.Some td
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
let cmp_container_of (ac : JSONLD_Context.active_context)
  (aprop : Prims.string FStar_Pervasives_Native.option) :
  Prims.string Prims.list=
  match cmp_aprop_td ac aprop with
  | FStar_Pervasives_Native.Some td -> cmp_container_list td
  | FStar_Pervasives_Native.None -> []
let cmp_has_container (ac : JSONLD_Context.active_context)
  (aprop : Prims.string FStar_Pervasives_Native.option) (c : Prims.string) :
  Prims.bool= FStar_List_Tot_Base.mem c (cmp_container_of ac aprop)
let rec cmp_dedupe_terms
  (terms : (Prims.string * JSONLD_Context.term_def) Prims.list)
  (seen : Prims.string Prims.list) :
  (Prims.string * JSONLD_Context.term_def) Prims.list=
  match terms with
  | [] -> []
  | (k, td)::rest ->
      if FStar_List_Tot_Base.mem k seen
      then cmp_dedupe_terms rest seen
      else (k, td) :: (cmp_dedupe_terms rest (k :: seen))
let rec cmp_insert_term (kv : (Prims.string * JSONLD_Context.term_def))
  (xs : (Prims.string * JSONLD_Context.term_def) Prims.list) :
  (Prims.string * JSONLD_Context.term_def) Prims.list=
  match xs with
  | [] -> [kv]
  | y::rest ->
      if
        cmp_term_less (FStar_Pervasives_Native.fst kv)
          (FStar_Pervasives_Native.fst y)
      then kv :: xs
      else y :: (cmp_insert_term kv rest)
let rec cmp_sort_terms
  (xs : (Prims.string * JSONLD_Context.term_def) Prims.list) :
  (Prims.string * JSONLD_Context.term_def) Prims.list=
  match xs with
  | [] -> []
  | x::rest -> cmp_insert_term x (cmp_sort_terms rest)
let cmp_live_terms (ac : JSONLD_Context.active_context) :
  (Prims.string * JSONLD_Context.term_def) Prims.list=
  cmp_dedupe_terms ac.JSONLD_Context.ac_terms []
let cmp_ordered_terms (ac : JSONLD_Context.active_context) :
  (Prims.string * JSONLD_Context.term_def) Prims.list=
  cmp_sort_terms (cmp_live_terms ac)
type inv_slot =
  | IS_Lang 
  | IS_Type 
  | IS_Any 
let uu___is_IS_Lang (projectee : inv_slot) : Prims.bool=
  match projectee with | IS_Lang -> true | uu___ -> false
let uu___is_IS_Type (projectee : inv_slot) : Prims.bool=
  match projectee with | IS_Type -> true | uu___ -> false
let uu___is_IS_Any (projectee : inv_slot) : Prims.bool=
  match projectee with | IS_Any -> true | uu___ -> false
type inv_maps =
  {
  im_language: (Prims.string * Prims.string) Prims.list ;
  im_type: (Prims.string * Prims.string) Prims.list ;
  im_any: (Prims.string * Prims.string) Prims.list }
let __proj__Mkinv_maps__item__im_language (projectee : inv_maps) :
  (Prims.string * Prims.string) Prims.list=
  match projectee with | { im_language; im_type; im_any;_} -> im_language
let __proj__Mkinv_maps__item__im_type (projectee : inv_maps) :
  (Prims.string * Prims.string) Prims.list=
  match projectee with | { im_language; im_type; im_any;_} -> im_type
let __proj__Mkinv_maps__item__im_any (projectee : inv_maps) :
  (Prims.string * Prims.string) Prims.list=
  match projectee with | { im_language; im_type; im_any;_} -> im_any
let inv_empty_maps : inv_maps=
  { im_language = []; im_type = []; im_any = [] }
type inverse_ctx =
  (Prims.string * (Prims.string * inv_maps) Prims.list) Prims.list
let inv_add_if_absent (m : (Prims.string * Prims.string) Prims.list)
  (k : Prims.string) (v : Prims.string) :
  (Prims.string * Prims.string) Prims.list=
  match cmp_lookup m k with
  | FStar_Pervasives_Native.Some uu___ -> m
  | FStar_Pervasives_Native.None -> FStar_List_Tot_Base.append m [(k, v)]
let inv_maps_add (maps : inv_maps) (slot : inv_slot) (k : Prims.string)
  (term : Prims.string) : inv_maps=
  match slot with
  | IS_Lang ->
      {
        im_language = (inv_add_if_absent maps.im_language k term);
        im_type = (maps.im_type);
        im_any = (maps.im_any)
      }
  | IS_Type ->
      {
        im_language = (maps.im_language);
        im_type = (inv_add_if_absent maps.im_type k term);
        im_any = (maps.im_any)
      }
  | IS_Any ->
      {
        im_language = (maps.im_language);
        im_type = (maps.im_type);
        im_any = (inv_add_if_absent maps.im_any k term)
      }
let rec inv_update_cont (conts : (Prims.string * inv_maps) Prims.list)
  (ckey : Prims.string) (slot : inv_slot) (k : Prims.string)
  (term : Prims.string) : (Prims.string * inv_maps) Prims.list=
  match conts with
  | [] -> [(ckey, (inv_maps_add inv_empty_maps slot k term))]
  | (c, maps)::rest ->
      if c = ckey
      then (c, (inv_maps_add maps slot k term)) :: rest
      else (c, maps) :: (inv_update_cont rest ckey slot k term)
let rec inv_update (inv : inverse_ctx) (iri : Prims.string)
  (ckey : Prims.string) (slot : inv_slot) (k : Prims.string)
  (term : Prims.string) : inverse_ctx=
  match inv with
  | [] -> [(iri, (inv_update_cont [] ckey slot k term))]
  | (i, conts)::rest ->
      if i = iri
      then (i, (inv_update_cont conts ckey slot k term)) :: rest
      else (i, conts) :: (inv_update rest iri ckey slot k term)
let inv_lang_dir_key (lo : Prims.string FStar_Pervasives_Native.option)
  (dopt : Prims.string FStar_Pervasives_Native.option) : Prims.string=
  match (lo, dopt) with
  | (FStar_Pervasives_Native.Some l, FStar_Pervasives_Native.Some d) ->
      cmp_lower (cmp_concat [l; "_"; d])
  | (FStar_Pervasives_Native.Some l, FStar_Pervasives_Native.None) ->
      cmp_lower l
  | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.Some d) ->
      cmp_concat ["_"; cmp_lower d]
  | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) -> "@null"
let inv_term_insertions (ac : JSONLD_Context.active_context)
  (td : JSONLD_Context.term_def) (default_lang_key : Prims.string) :
  (inv_slot * Prims.string) Prims.list=
  if td.JSONLD_Context.td_reverse
  then [(IS_Type, "@reverse")]
  else
    (match td.JSONLD_Context.td_type_mapping with
     | FStar_Pervasives_Native.Some "@none" ->
         [(IS_Lang, "@any"); (IS_Type, "@any")]
     | FStar_Pervasives_Native.Some t -> [(IS_Type, t)]
     | FStar_Pervasives_Native.None ->
         (match ((td.JSONLD_Context.td_language),
                  (td.JSONLD_Context.td_direction))
          with
          | (FStar_Pervasives_Native.Some lo, FStar_Pervasives_Native.Some
             dopt) -> [(IS_Lang, (inv_lang_dir_key lo dopt))]
          | (FStar_Pervasives_Native.Some lo, FStar_Pervasives_Native.None)
              ->
              [(IS_Lang,
                 ((match lo with
                   | FStar_Pervasives_Native.Some l -> cmp_lower l
                   | FStar_Pervasives_Native.None -> "@null")))]
          | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.Some dopt)
              ->
              [(IS_Lang,
                 ((match dopt with
                   | FStar_Pervasives_Native.Some d ->
                       cmp_concat ["_"; cmp_lower d]
                   | FStar_Pervasives_Native.None -> "@none")))]
          | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) ->
              (match ac.JSONLD_Context.ac_direction with
               | FStar_Pervasives_Native.Some d ->
                   let lang_dir =
                     cmp_lower
                       (cmp_concat
                          [(match ac.JSONLD_Context.ac_language with
                            | FStar_Pervasives_Native.Some l -> l
                            | FStar_Pervasives_Native.None -> "@none");
                          "_";
                          d]) in
                   [(IS_Lang, lang_dir);
                   (IS_Lang, "@none");
                   (IS_Type, "@none")]
               | FStar_Pervasives_Native.None ->
                   [(IS_Lang, default_lang_key);
                   (IS_Lang, "@none");
                   (IS_Type, "@none")])))
let rec inv_apply_insertions (inv : inverse_ctx) (iri : Prims.string)
  (ckey : Prims.string) (name : Prims.string)
  (ins : (inv_slot * Prims.string) Prims.list) : inverse_ctx=
  match ins with
  | [] -> inv
  | (slot, k)::rest ->
      inv_apply_insertions (inv_update inv iri ckey slot k name) iri ckey
        name rest
let rec inv_fold_terms (inv : inverse_ctx)
  (terms : (Prims.string * JSONLD_Context.term_def) Prims.list)
  (ac : JSONLD_Context.active_context) (default_lang_key : Prims.string) :
  inverse_ctx=
  match terms with
  | [] -> inv
  | (name, td)::rest ->
      if td.JSONLD_Context.td_iri = "@null"
      then inv_fold_terms inv rest ac default_lang_key
      else
        (let ckey = cmp_container_key td in
         let ins =
           FStar_List_Tot_Base.append
             (inv_term_insertions ac td default_lang_key) [(IS_Any, "@none")] in
         inv_fold_terms
           (inv_apply_insertions inv td.JSONLD_Context.td_iri ckey name ins)
           rest ac default_lang_key)
let cmp_inverse (ac : JSONLD_Context.active_context) : inverse_ctx=
  let default_lang_key =
    match ac.JSONLD_Context.ac_language with
    | FStar_Pervasives_Native.Some l -> cmp_lower l
    | FStar_Pervasives_Native.None -> "@none" in
  inv_fold_terms [] (cmp_ordered_terms ac) ac default_lang_key
let inv_slot_map (maps : inv_maps) (tl : Prims.string) :
  (Prims.string * Prims.string) Prims.list=
  if tl = "@type"
  then maps.im_type
  else if tl = "@any" then maps.im_any else maps.im_language
let rec cmp_select_prefs (m : (Prims.string * Prims.string) Prims.list)
  (prefs : Prims.string Prims.list) :
  Prims.string FStar_Pervasives_Native.option=
  match prefs with
  | [] -> FStar_Pervasives_Native.None
  | p::rest ->
      (match cmp_lookup m p with
       | FStar_Pervasives_Native.Some term ->
           FStar_Pervasives_Native.Some term
       | FStar_Pervasives_Native.None -> cmp_select_prefs m rest)
let rec cmp_select_term (conts : (Prims.string * inv_maps) Prims.list)
  (containers : Prims.string Prims.list) (tl : Prims.string)
  (prefs : Prims.string Prims.list) :
  Prims.string FStar_Pervasives_Native.option=
  match containers with
  | [] -> FStar_Pervasives_Native.None
  | c::rest ->
      (match cmp_lookup conts c with
       | FStar_Pervasives_Native.Some maps ->
           (match cmp_select_prefs (inv_slot_map maps tl) prefs with
            | FStar_Pervasives_Native.Some t ->
                FStar_Pervasives_Native.Some t
            | FStar_Pervasives_Native.None ->
                cmp_select_term conts rest tl prefs)
       | FStar_Pervasives_Native.None -> cmp_select_term conts rest tl prefs)
let cmp_item_lang_type (it : Parser_JSON.json_val) :
  (Prims.string * Prims.string)=
  match it with
  | Parser_JSON.JObject f ->
      if JSONLD_Expand.jexp_has_field "@value" f
      then
        (match cmp_field f "@direction" with
         | FStar_Pervasives_Native.Some (Parser_JSON.JString d) ->
             (((match cmp_field f "@language" with
                | FStar_Pervasives_Native.Some (Parser_JSON.JString l) ->
                    cmp_lower (cmp_concat [l; "_"; d])
                | uu___ -> cmp_concat ["_"; cmp_lower d])), "@none")
         | uu___ ->
             (match cmp_field f "@language" with
              | FStar_Pervasives_Native.Some (Parser_JSON.JString l) ->
                  ((cmp_lower l), "@none")
              | uu___1 ->
                  (match cmp_field f "@type" with
                   | FStar_Pervasives_Native.Some (Parser_JSON.JString t) ->
                       ("@none", t)
                   | uu___2 -> ("@null", "@none"))))
      else ("@none", "@id")
  | uu___ -> ("@none", "@id")
let rec cmp_list_common_walk (items : Parser_JSON.json_val Prims.list)
  (clang : Prims.string FStar_Pervasives_Native.option)
  (ctype : Prims.string FStar_Pervasives_Native.option) :
  (Prims.string * Prims.string)=
  match items with
  | [] ->
      (((match clang with
         | FStar_Pervasives_Native.Some c -> c
         | FStar_Pervasives_Native.None -> "@none")),
        ((match ctype with
          | FStar_Pervasives_Native.Some c -> c
          | FStar_Pervasives_Native.None -> "@none")))
  | it::rest ->
      let uu___ = cmp_item_lang_type it in
      (match uu___ with
       | (il, ity) ->
           let is_val = cmp_is_value_object it in
           let clang' =
             match clang with
             | FStar_Pervasives_Native.None ->
                 FStar_Pervasives_Native.Some il
             | FStar_Pervasives_Native.Some c ->
                 if c = il
                 then FStar_Pervasives_Native.Some c
                 else
                   if is_val
                   then FStar_Pervasives_Native.Some "@none"
                   else FStar_Pervasives_Native.Some c in
           let ctype' =
             match ctype with
             | FStar_Pervasives_Native.None ->
                 FStar_Pervasives_Native.Some ity
             | FStar_Pervasives_Native.Some c ->
                 if c = ity
                 then FStar_Pervasives_Native.Some c
                 else FStar_Pervasives_Native.Some "@none" in
           cmp_list_common_walk rest clang' ctype')
let cmp_iri_selectors (ac : JSONLD_Context.active_context)
  (value : Parser_JSON.json_val FStar_Pervasives_Native.option)
  (rev : Prims.bool) :
  (Prims.string Prims.list * Prims.string * Prims.string)=
  let has_index =
    match value with
    | FStar_Pervasives_Native.Some (Parser_JSON.JObject f) ->
        JSONLD_Expand.jexp_has_field "@index" f
    | uu___ -> false in
  let is_map =
    match value with
    | FStar_Pervasives_Native.Some (Parser_JSON.JObject uu___) -> true
    | uu___ -> false in
  let idx_pre =
    match value with
    | FStar_Pervasives_Native.Some (Parser_JSON.JObject f) ->
        if
          (JSONLD_Expand.jexp_has_field "@index" f) &&
            (Prims.op_Negation (cmp_is_graph_object (Parser_JSON.JObject f)))
        then ["@index"; "@index@set"]
        else []
    | uu___ -> [] in
  let uu___ =
    if rev
    then (["@set"], "@type", "@reverse")
    else
      (match value with
       | FStar_Pervasives_Native.Some (Parser_JSON.JObject f) ->
           if JSONLD_Expand.jexp_has_field "@list" f
           then
             let lst =
               match cmp_field f "@list" with
               | FStar_Pervasives_Native.Some v ->
                   JSONLD_Expand.jexp_as_array v
               | FStar_Pervasives_Native.None -> [] in
             let cont_list =
               if JSONLD_Expand.jexp_has_field "@index" f
               then []
               else ["@list"] in
             (match lst with
              | [] -> (cont_list, "@any", "@none")
              | uu___2 ->
                  let uu___3 =
                    cmp_list_common_walk lst FStar_Pervasives_Native.None
                      FStar_Pervasives_Native.None in
                  (match uu___3 with
                   | (cl, ct) ->
                       if ct <> "@none"
                       then (cont_list, "@type", ct)
                       else (cont_list, "@language", cl)))
           else
             if cmp_is_graph_object (Parser_JSON.JObject f)
             then
               (let gi = JSONLD_Expand.jexp_has_field "@index" f in
                let gid = JSONLD_Expand.jexp_has_field "@id" f in
                ((FStar_List_Tot_Base.append
                    (FStar_List_Tot_Base.append
                       (FStar_List_Tot_Base.append
                          (if gi
                           then ["@graph@index"; "@graph@index@set"]
                           else [])
                          (if gid then ["@graph@id"; "@graph@id@set"] else []))
                       (FStar_List_Tot_Base.append
                          ["@graph"; "@graph@set"; "@set"]
                          (if gi
                           then []
                           else ["@graph@index"; "@graph@index@set"])))
                    (FStar_List_Tot_Base.append
                       (if gid then [] else ["@graph@id"; "@graph@id@set"])
                       ["@index"; "@index@set"])), "@type", "@id"))
             else
               if JSONLD_Expand.jexp_has_field "@value" f
               then
                 (let no_idx =
                    Prims.op_Negation
                      (JSONLD_Expand.jexp_has_field "@index" f) in
                  let uu___4 =
                    match cmp_field f "@direction" with
                    | FStar_Pervasives_Native.Some (Parser_JSON.JString d) ->
                        if no_idx
                        then
                          (["@language"; "@language@set"], "@language",
                            ((match cmp_field f "@language" with
                              | FStar_Pervasives_Native.Some
                                  (Parser_JSON.JString l) ->
                                  cmp_lower (cmp_concat [l; "_"; d])
                              | uu___5 -> cmp_concat ["_"; cmp_lower d])))
                        else
                          (match cmp_field f "@type" with
                           | FStar_Pervasives_Native.Some
                               (Parser_JSON.JString t) -> ([], "@type", t)
                           | uu___6 -> ([], "@language", "@null"))
                    | uu___5 ->
                        (match cmp_field f "@language" with
                         | FStar_Pervasives_Native.Some (Parser_JSON.JString
                             l) ->
                             if no_idx
                             then
                               (["@language"; "@language@set"], "@language",
                                 (cmp_lower l))
                             else
                               (match cmp_field f "@type" with
                                | FStar_Pervasives_Native.Some
                                    (Parser_JSON.JString t) ->
                                    ([], "@type", t)
                                | uu___7 -> ([], "@language", "@null"))
                         | uu___6 ->
                             (match cmp_field f "@type" with
                              | FStar_Pervasives_Native.Some
                                  (Parser_JSON.JString t) -> ([], "@type", t)
                              | uu___7 -> ([], "@language", "@null"))) in
                  match uu___4 with
                  | (langconts, tl0, tlv0) ->
                      ((FStar_List_Tot_Base.append langconts ["@set"]), tl0,
                        tlv0))
               else
                 (["@id"; "@id@set"; "@type"; "@set@type"; "@set"], "@type",
                   "@id")
       | uu___2 ->
           (["@id"; "@id@set"; "@type"; "@set@type"; "@set"], "@type", "@id")) in
  match uu___ with
  | (mid, tl, tlv) ->
      let tail2 =
        if
          (Prims.op_Negation ac.JSONLD_Context.ac_mode10) &&
            ((Prims.op_Negation is_map) || (Prims.op_Negation has_index))
        then ["@index"; "@index@set"]
        else [] in
      let tail3 =
        if
          (Prims.op_Negation ac.JSONLD_Context.ac_mode10) &&
            (match value with
             | FStar_Pervasives_Native.Some (Parser_JSON.JObject f) ->
                 (match f with
                  | kv::[] -> (FStar_Pervasives_Native.fst kv) = "@value"
                  | uu___1 -> false)
             | uu___1 -> false)
        then ["@language"; "@language@set"]
        else [] in
      ((FStar_List_Tot_Base.append idx_pre
          (FStar_List_Tot_Base.append mid
             (FStar_List_Tot_Base.append ["@none"]
                (FStar_List_Tot_Base.append tail2 tail3)))), tl, tlv)
let cmp_underscore_suffix (s : Prims.string) :
  Prims.string FStar_Pervasives_Native.option=
  let n = Parser_FastString.fs_byte_length s in
  let pos =
    Parser_FastString.fs_find_byte s (Prims.of_int (0x5F)) Prims.int_zero in
  if pos < n
  then
    FStar_Pervasives_Native.Some
      (Parser_FastString.fs_byte_sub s pos (n - pos))
  else FStar_Pervasives_Native.None
let cmp_confused_with_prefix (ac : JSONLD_Context.active_context)
  (iri : Prims.string) : Prims.bool=
  match JSONLD_Context.jldctx_find_colon iri Prims.int_zero
          ((Parser_FastString.fs_byte_length iri) + Prims.int_one)
  with
  | FStar_Pervasives_Native.None -> false
  | FStar_Pervasives_Native.Some cpos ->
      if cpos > (Parser_FastString.fs_byte_length iri)
      then false
      else
        (let pfx = Parser_FastString.fs_byte_sub iri Prims.int_zero cpos in
         match JSONLD_Context.jldctx_find_term ac.JSONLD_Context.ac_terms pfx
         with
         | FStar_Pervasives_Native.Some td ->
             (td.JSONLD_Context.td_prefix &&
                (td.JSONLD_Context.td_iri <> "@null"))
               &&
               (Prims.op_Negation
                  (cmp_starts_with iri td.JSONLD_Context.td_iri))
         | FStar_Pervasives_Native.None -> false)
let rec cmp_curie_loop (ac : JSONLD_Context.active_context)
  (terms : (Prims.string * JSONLD_Context.term_def) Prims.list)
  (iri : Prims.string) (has_value : Prims.bool)
  (best : Prims.string FStar_Pervasives_Native.option) :
  Prims.string FStar_Pervasives_Native.option=
  match terms with
  | [] -> best
  | (name, td)::rest ->
      let li = Parser_FastString.fs_byte_length iri in
      let lt = Parser_FastString.fs_byte_length td.JSONLD_Context.td_iri in
      let skip =
        (((((FStar_Pervasives_Native.uu___is_Some
               (JSONLD_Context.jldctx_find_colon name Prims.int_zero
                  ((Parser_FastString.fs_byte_length name) + Prims.int_one)))
              || (td.JSONLD_Context.td_iri = "@null"))
             || (Prims.op_Negation td.JSONLD_Context.td_prefix))
            || (lt = Prims.int_zero))
           || (li <= lt))
          ||
          (Prims.op_Negation (cmp_starts_with iri td.JSONLD_Context.td_iri)) in
      if skip
      then cmp_curie_loop ac rest iri has_value best
      else
        (let suffix = Parser_FastString.fs_byte_sub iri lt (li - lt) in
         let candidate = cmp_concat [name; ":"; suffix] in
         let usable =
           match JSONLD_Context.jldctx_find_term ac.JSONLD_Context.ac_terms
                   candidate
           with
           | FStar_Pervasives_Native.None -> true
           | FStar_Pervasives_Native.Some ctd ->
               (Prims.op_Negation has_value) &&
                 (ctd.JSONLD_Context.td_iri = iri) in
         let better =
           usable &&
             (match best with
              | FStar_Pervasives_Native.None -> true
              | FStar_Pervasives_Native.Some b -> cmp_term_less candidate b) in
         cmp_curie_loop ac rest iri has_value
           (if better then FStar_Pervasives_Native.Some candidate else best))
let rec cmp_split_slash_from (s : Prims.string) (pos : Prims.nat)
  (fuel : Prims.nat) : Prims.string Prims.list=
  if fuel = Prims.int_zero
  then []
  else
    (let n = Parser_FastString.fs_byte_length s in
     let sl = Parser_FastString.fs_find_byte s (Prims.of_int (0x2F)) pos in
     if sl >= n
     then
       [Parser_FastString.fs_byte_sub s pos
          (if n >= pos then n - pos else Prims.int_zero)]
     else
       (Parser_FastString.fs_byte_sub s pos
          (if sl >= pos then sl - pos else Prims.int_zero))
       ::
       (cmp_split_slash_from s (sl + Prims.int_one) (fuel - Prims.int_one)))
let cmp_split_slash (s : Prims.string) : Prims.string Prims.list=
  cmp_split_slash_from s Prims.int_zero
    ((Parser_FastString.fs_byte_length s) + Prims.int_one)
let rec cmp_strip_common (bs : Prims.string Prims.list)
  (isegs : Prims.string Prims.list) (last : Prims.nat) :
  (Prims.string Prims.list * Prims.string Prims.list)=
  match (bs, isegs) with
  | (b::brest, i::irest) ->
      if (b = i) && ((FStar_List_Tot_Base.length isegs) > last)
      then cmp_strip_common brest irest last
      else (bs, isegs)
  | (uu___, uu___1) -> (bs, isegs)
let rec cmp_repeat_dotdot (n : Prims.nat) : Prims.string=
  if n = Prims.int_zero
  then ""
  else cmp_concat ["../"; cmp_repeat_dotdot (n - Prims.int_one)]
let rec cmp_join_slash (xs : Prims.string Prims.list) : Prims.string=
  match xs with
  | [] -> ""
  | x::[] -> x
  | x::rest -> cmp_concat [x; "/"; cmp_join_slash rest]
let cmp_iri_split (s : Prims.string) :
  (Prims.string * Prims.string * Prims.string FStar_Pervasives_Native.option
    * Prims.string FStar_Pervasives_Native.option)=
  let n = Parser_FastString.fs_byte_length s in
  let h =
    Parser_FastString.fs_find_byte s (Prims.of_int (0x23)) Prims.int_zero in
  let q0 =
    Parser_FastString.fs_find_byte s (Prims.of_int (0x3F)) Prims.int_zero in
  let has_frag = h < n in
  let has_query = (q0 < h) && (q0 < n) in
  let frag =
    if has_frag && ((h + Prims.int_one) <= n)
    then
      FStar_Pervasives_Native.Some
        (Parser_FastString.fs_byte_sub s (h + Prims.int_one)
           ((n - h) - Prims.int_one))
    else FStar_Pervasives_Native.None in
  let query =
    if has_query
    then
      let qend = if h < n then h else n in
      (if (q0 + Prims.int_one) <= qend
       then
         FStar_Pervasives_Native.Some
           (Parser_FastString.fs_byte_sub s (q0 + Prims.int_one)
              ((qend - q0) - Prims.int_one))
       else FStar_Pervasives_Native.Some "")
    else FStar_Pervasives_Native.None in
  let pe0 = if has_query then q0 else if h < n then h else n in
  let pe = if pe0 > n then n else pe0 in
  let c =
    Parser_FastString.fs_find_byte s (Prims.of_int (0x3A)) Prims.int_zero in
  let sl =
    Parser_FastString.fs_find_byte s (Prims.of_int (0x2F)) Prims.int_zero in
  let root_len =
    if ((c >= n) || (c >= pe)) || (sl < c)
    then Prims.int_zero
    else
      (let after = c + Prims.int_one in
       if
         (((after + Prims.int_one) < n) &&
            ((Parser_FastString.fs_byte_at s after) = (Prims.of_int (0x2F))))
           &&
           ((Parser_FastString.fs_byte_at s (after + Prims.int_one)) =
              (Prims.of_int (0x2F)))
       then
         let a0 = after + (Prims.of_int (2)) in
         let asl = Parser_FastString.fs_find_byte s (Prims.of_int (0x2F)) a0 in
         (if asl < pe then asl else pe)
       else after) in
  let root_len1 = if root_len > pe then pe else root_len in
  ((Parser_FastString.fs_byte_sub s Prims.int_zero root_len1),
    (Parser_FastString.fs_byte_sub s root_len1 (pe - root_len1)), query,
    frag)
let cmp_relativize (base : Prims.string) (iri : Prims.string) : Prims.string=
  let uu___ = cmp_iri_split base in
  match uu___ with
  | (broot, bpath, uu___1, uu___2) ->
      let uu___3 = cmp_iri_split iri in
      (match uu___3 with
       | (iroot, ipath, iq, ifr) ->
           if (broot = "") || (broot <> iroot)
           then iri
           else
             (let bsegs = cmp_split_slash bpath in
              let isegs = cmp_split_slash ipath in
              let last =
                if
                  (FStar_Pervasives_Native.uu___is_Some iq) ||
                    (FStar_Pervasives_Native.uu___is_Some ifr)
                then Prims.int_zero
                else Prims.int_one in
              let uu___5 = cmp_strip_common bsegs isegs last in
              match uu___5 with
              | (brem, irem) ->
                  let ups =
                    let l = FStar_List_Tot_Base.length brem in
                    if l > Prims.int_zero
                    then l - Prims.int_one
                    else Prims.int_zero in
                  let rel =
                    cmp_concat [cmp_repeat_dotdot ups; cmp_join_slash irem] in
                  let rel1 =
                    match iq with
                    | FStar_Pervasives_Native.Some q ->
                        cmp_concat [rel; "?"; q]
                    | FStar_Pervasives_Native.None -> rel in
                  let rel2 =
                    match ifr with
                    | FStar_Pervasives_Native.Some fg ->
                        cmp_concat [rel1; "#"; fg]
                    | FStar_Pervasives_Native.None -> rel1 in
                  if rel2 = ""
                  then "./"
                  else
                    if
                      (Parser_FastString.fs_byte_at rel2 Prims.int_zero) =
                        (Prims.of_int (0x40))
                    then cmp_concat ["./"; rel2]
                    else rel2))
let rec compact_iri (ac : JSONLD_Context.active_context) (co : cmp_opts)
  (iri : Prims.string)
  (value : Parser_JSON.json_val FStar_Pervasives_Native.option)
  (vocab : Prims.bool) (rev : Prims.bool) (depth : Prims.nat) :
  Prims.string FStar_Pervasives_Native.option=
  let inv = cmp_inverse ac in
  let term_sel =
    if Prims.op_Negation vocab
    then FStar_Pervasives_Native.None
    else
      (match cmp_lookup inv iri with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some conts ->
           let uu___1 = cmp_iri_selectors ac value rev in
           (match uu___1 with
            | (containers, tl0, tlv) ->
                let tl =
                  if (tlv = "@none") && (tl0 = "@any") then "@any" else tl0 in
                let id_pref =
                  if (tlv = "@id") || (tlv = "@reverse")
                  then
                    match value with
                    | FStar_Pervasives_Native.Some (Parser_JSON.JObject f) ->
                        (match cmp_field f "@id" with
                         | FStar_Pervasives_Native.Some (Parser_JSON.JString
                             idv) ->
                             let cand =
                               if depth > Prims.int_zero
                               then
                                 compact_iri ac co idv
                                   FStar_Pervasives_Native.None true false
                                   (depth - Prims.int_one)
                               else FStar_Pervasives_Native.None in
                             (match cand with
                              | FStar_Pervasives_Native.Some ct ->
                                  (match JSONLD_Context.jldctx_find_term
                                           ac.JSONLD_Context.ac_terms ct
                                   with
                                   | FStar_Pervasives_Native.Some ctd ->
                                       if ctd.JSONLD_Context.td_iri = idv
                                       then
                                         FStar_Pervasives_Native.Some
                                           ["@vocab"; "@id"; "@none"]
                                       else
                                         FStar_Pervasives_Native.Some
                                           ["@id"; "@vocab"; "@none"]
                                   | FStar_Pervasives_Native.None ->
                                       FStar_Pervasives_Native.Some
                                         ["@id"; "@vocab"; "@none"])
                              | FStar_Pervasives_Native.None ->
                                  FStar_Pervasives_Native.Some
                                    ["@id"; "@vocab"; "@none"])
                         | uu___2 -> FStar_Pervasives_Native.None)
                    | uu___2 -> FStar_Pervasives_Native.None
                  else FStar_Pervasives_Native.None in
                let prefs_base =
                  match id_pref with
                  | FStar_Pervasives_Native.Some ps ->
                      if tlv = "@reverse" then "@reverse" :: ps else ps
                  | FStar_Pervasives_Native.None ->
                      if tlv = "@reverse"
                      then ["@reverse"; tlv; "@none"]
                      else [tlv; "@none"] in
                let prefs1 = FStar_List_Tot_Base.append prefs_base ["@any"] in
                let prefs =
                  match cmp_underscore_suffix tlv with
                  | FStar_Pervasives_Native.Some u ->
                      FStar_List_Tot_Base.append prefs1 [u]
                  | FStar_Pervasives_Native.None -> prefs1 in
                cmp_select_term conts containers tl prefs)) in
  match term_sel with
  | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
  | FStar_Pervasives_Native.None ->
      let sfx =
        if vocab
        then
          match ac.JSONLD_Context.ac_vocab with
          | FStar_Pervasives_Native.Some vm ->
              let li = Parser_FastString.fs_byte_length iri in
              let lv = Parser_FastString.fs_byte_length vm in
              (if
                 ((lv > Prims.int_zero) && (li > lv)) &&
                   (cmp_starts_with iri vm)
               then
                 let suffix = Parser_FastString.fs_byte_sub iri lv (li - lv) in
                 match JSONLD_Context.jldctx_find_term
                         ac.JSONLD_Context.ac_terms suffix
                 with
                 | FStar_Pervasives_Native.Some uu___ ->
                     FStar_Pervasives_Native.None
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.Some suffix
               else FStar_Pervasives_Native.None)
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        else FStar_Pervasives_Native.None in
      (match sfx with
       | FStar_Pervasives_Native.Some s -> FStar_Pervasives_Native.Some s
       | FStar_Pervasives_Native.None ->
           (match cmp_curie_loop ac (cmp_live_terms ac) iri
                    (FStar_Pervasives_Native.uu___is_Some value)
                    FStar_Pervasives_Native.None
            with
            | FStar_Pervasives_Native.Some c ->
                FStar_Pervasives_Native.Some c
            | FStar_Pervasives_Native.None ->
                if cmp_confused_with_prefix ac iri
                then FStar_Pervasives_Native.None
                else
                  if (Prims.op_Negation vocab) && co.co_rel
                  then
                    (match ac.JSONLD_Context.ac_base with
                     | FStar_Pervasives_Native.Some b ->
                         FStar_Pervasives_Native.Some (cmp_relativize b iri)
                     | FStar_Pervasives_Native.None ->
                         FStar_Pervasives_Native.Some iri)
                  else FStar_Pervasives_Native.Some iri))
let cmp_alias_kw (ac : JSONLD_Context.active_context) (co : cmp_opts)
  (kw : Prims.string) : Prims.string=
  match compact_iri ac co kw FStar_Pervasives_Native.None true false
          (Prims.of_int (2))
  with
  | FStar_Pervasives_Native.Some s -> s
  | FStar_Pervasives_Native.None -> kw
let compact_value (ac : JSONLD_Context.active_context) (co : cmp_opts)
  (aprop : Prims.string FStar_Pervasives_Native.option)
  (vfields : (Prims.string * Parser_JSON.json_val) Prims.list) :
  Parser_JSON.json_val FStar_Pervasives_Native.option=
  let td = cmp_aprop_td ac aprop in
  let tmap =
    match td with
    | FStar_Pervasives_Native.Some t -> t.JSONLD_Context.td_type_mapping
    | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None in
  let lang =
    match td with
    | FStar_Pervasives_Native.Some t ->
        (match t.JSONLD_Context.td_language with
         | FStar_Pervasives_Native.Some lo -> lo
         | FStar_Pervasives_Native.None -> ac.JSONLD_Context.ac_language)
    | FStar_Pervasives_Native.None -> ac.JSONLD_Context.ac_language in
  let dir =
    match td with
    | FStar_Pervasives_Native.Some t ->
        (match t.JSONLD_Context.td_direction with
         | FStar_Pervasives_Native.Some dd -> dd
         | FStar_Pervasives_Native.None -> ac.JSONLD_Context.ac_direction)
    | FStar_Pervasives_Native.None -> ac.JSONLD_Context.ac_direction in
  let has_index = JSONLD_Expand.jexp_has_field "@index" vfields in
  let preserve_index =
    has_index && (Prims.op_Negation (cmp_has_container ac aprop "@index")) in
  if
    (JSONLD_Expand.jexp_has_field "@id" vfields) &&
      (cmp_keys_only vfields ["@id"; "@index"])
  then
    match cmp_field vfields "@id" with
    | FStar_Pervasives_Native.Some (Parser_JSON.JString idv) ->
        (if tmap = (FStar_Pervasives_Native.Some "@id")
         then
           match compact_iri ac co idv FStar_Pervasives_Native.None false
                   false (Prims.of_int (2))
           with
           | FStar_Pervasives_Native.Some s ->
               FStar_Pervasives_Native.Some (Parser_JSON.JString s)
           | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
         else
           if tmap = (FStar_Pervasives_Native.Some "@vocab")
           then
             (match compact_iri ac co idv FStar_Pervasives_Native.None true
                      false (Prims.of_int (2))
              with
              | FStar_Pervasives_Native.Some s ->
                  FStar_Pervasives_Native.Some (Parser_JSON.JString s)
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
           else FStar_Pervasives_Native.Some (Parser_JSON.JObject vfields))
    | uu___ -> FStar_Pervasives_Native.Some (Parser_JSON.JObject vfields)
  else
    if Prims.op_Negation (JSONLD_Expand.jexp_has_field "@value" vfields)
    then FStar_Pervasives_Native.Some (Parser_JSON.JObject vfields)
    else
      (let vval =
         match cmp_field vfields "@value" with
         | FStar_Pervasives_Native.Some v -> v
         | FStar_Pervasives_Native.None -> Parser_JSON.JNull in
       let vtype_s =
         match cmp_field vfields "@type" with
         | FStar_Pervasives_Native.Some (Parser_JSON.JString t) ->
             FStar_Pervasives_Native.Some t
         | uu___2 -> FStar_Pervasives_Native.None in
       let vlang_s =
         match cmp_field vfields "@language" with
         | FStar_Pervasives_Native.Some (Parser_JSON.JString l) ->
             FStar_Pervasives_Native.Some l
         | uu___2 -> FStar_Pervasives_Native.None in
       let vdir_s =
         match cmp_field vfields "@direction" with
         | FStar_Pervasives_Native.Some (Parser_JSON.JString d) ->
             FStar_Pervasives_Native.Some d
         | uu___2 -> FStar_Pervasives_Native.None in
       let tmap_none = tmap = (FStar_Pervasives_Native.Some "@none") in
       let lang_matches =
         match (vlang_s, lang) with
         | (FStar_Pervasives_Native.Some a, FStar_Pervasives_Native.Some b)
             -> (cmp_lower a) = (cmp_lower b)
         | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) ->
             true
         | (uu___2, uu___3) -> false in
       let dir_matches =
         match (vdir_s, dir) with
         | (FStar_Pervasives_Native.Some a, FStar_Pervasives_Native.Some b)
             -> (cmp_lower a) = (cmp_lower b)
         | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) ->
             true
         | (uu___2, uu___3) -> false in
       let type_collapse =
         ((FStar_Pervasives_Native.uu___is_Some vtype_s) &&
            (FStar_Pervasives_Native.uu___is_Some tmap))
           && (vtype_s = tmap) in
       let value_is_string = Parser_JSON.uu___is_JString vval in
       if
         ((Prims.op_Negation preserve_index) && (Prims.op_Negation tmap_none))
           && type_collapse
       then FStar_Pervasives_Native.Some vval
       else
         if
           (((((Prims.op_Negation preserve_index) &&
                 (Prims.op_Negation tmap_none))
                && (FStar_Pervasives_Native.uu___is_None vtype_s))
               && (Prims.op_Negation value_is_string))
              && (FStar_Pervasives_Native.uu___is_None vlang_s))
             && (FStar_Pervasives_Native.uu___is_None vdir_s)
         then FStar_Pervasives_Native.Some vval
         else
           if
             ((((Prims.op_Negation preserve_index) &&
                  (Prims.op_Negation tmap_none))
                 && (FStar_Pervasives_Native.uu___is_None vtype_s))
                && lang_matches)
               && dir_matches
           then FStar_Pervasives_Native.Some vval
           else
             (let idx_fields =
                if preserve_index
                then
                  match cmp_field vfields "@index" with
                  | FStar_Pervasives_Native.Some ix ->
                      [((cmp_alias_kw ac co "@index"), ix)]
                  | FStar_Pervasives_Native.None -> []
                else [] in
              let lang_fields =
                match vlang_s with
                | FStar_Pervasives_Native.Some l ->
                    [((cmp_alias_kw ac co "@language"),
                       (Parser_JSON.JString l))]
                | FStar_Pervasives_Native.None -> [] in
              let dir_fields =
                match vdir_s with
                | FStar_Pervasives_Native.Some d ->
                    [((cmp_alias_kw ac co "@direction"),
                       (Parser_JSON.JString d))]
                | FStar_Pervasives_Native.None -> [] in
              match vtype_s with
              | FStar_Pervasives_Native.Some t ->
                  (match compact_iri ac co t FStar_Pervasives_Native.None
                           true false (Prims.of_int (2))
                   with
                   | FStar_Pervasives_Native.None ->
                       FStar_Pervasives_Native.None
                   | FStar_Pervasives_Native.Some ct ->
                       FStar_Pervasives_Native.Some
                         (Parser_JSON.JObject
                            (FStar_List_Tot_Base.append idx_fields
                               (FStar_List_Tot_Base.append
                                  [((cmp_alias_kw ac co "@type"),
                                     (Parser_JSON.JString ct))]
                                  [((cmp_alias_kw ac co "@value"), vval)]))))
              | FStar_Pervasives_Native.None ->
                  FStar_Pervasives_Native.Some
                    (Parser_JSON.JObject
                       (FStar_List_Tot_Base.append idx_fields
                          (FStar_List_Tot_Base.append lang_fields
                             (FStar_List_Tot_Base.append dir_fields
                                [((cmp_alias_kw ac co "@value"), vval)]))))))
let cmp_nest_of (ac : JSONLD_Context.active_context) (iap : Prims.string) :
  Prims.string FStar_Pervasives_Native.option FStar_Pervasives_Native.option=
  match JSONLD_Context.jldctx_find_term ac.JSONLD_Context.ac_terms iap with
  | FStar_Pervasives_Native.Some td ->
      (match td.JSONLD_Context.td_nest with
       | FStar_Pervasives_Native.None ->
           FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some nt ->
           if nt = "@nest"
           then
             FStar_Pervasives_Native.Some (FStar_Pervasives_Native.Some nt)
           else
             (match JSONLD_Context.expand_iri ac nt true with
              | FStar_Pervasives_Native.Some e ->
                  if e = "@nest"
                  then
                    FStar_Pervasives_Native.Some
                      (FStar_Pervasives_Native.Some nt)
                  else FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None))
  | FStar_Pervasives_Native.None ->
      FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
let rec cmp_move_reverse (ac : JSONLD_Context.active_context) (co : cmp_opts)
  (rf : (Prims.string * Parser_JSON.json_val) Prims.list)
  (leftover : (Prims.string * Parser_JSON.json_val) Prims.list)
  (res : (Prims.string * Parser_JSON.json_val) Prims.list) :
  ((Prims.string * Parser_JSON.json_val) Prims.list * (Prims.string *
    Parser_JSON.json_val) Prims.list)=
  match rf with
  | [] -> (leftover, res)
  | (p, pv)::rest ->
      (match JSONLD_Context.jldctx_find_term ac.JSONLD_Context.ac_terms p
       with
       | FStar_Pervasives_Native.Some td ->
           if td.JSONLD_Context.td_reverse
           then
             let as_arr =
               td.JSONLD_Context.td_set || (Prims.op_Negation co.co_arrays) in
             let res1 =
               match pv with
               | Parser_JSON.JArray xs -> cmp_add_values res p xs as_arr
               | x -> cmp_add_value res p x as_arr in
             cmp_move_reverse ac co rest leftover res1
           else
             cmp_move_reverse ac co rest
               (FStar_List_Tot_Base.append leftover [(p, pv)]) res
       | FStar_Pervasives_Native.None ->
           cmp_move_reverse ac co rest
             (FStar_List_Tot_Base.append leftover [(p, pv)]) res)
let rec cmp_compact_types (tsc : JSONLD_Context.active_context)
  (co : cmp_opts) (items : Parser_JSON.json_val Prims.list) :
  Prims.string Prims.list FStar_Pervasives_Native.option=
  match items with
  | [] -> FStar_Pervasives_Native.Some []
  | (Parser_JSON.JString t)::rest ->
      (match compact_iri tsc co t FStar_Pervasives_Native.None true false
               (Prims.of_int (2))
       with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some ct ->
           (match cmp_compact_types tsc co rest with
            | FStar_Pervasives_Native.Some cs ->
                FStar_Pervasives_Native.Some (ct :: cs)
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None))
  | uu___::rest -> cmp_compact_types tsc co rest
let rec cmp_raw_type_names (items : Parser_JSON.json_val Prims.list) :
  Prims.string Prims.list=
  match items with
  | [] -> []
  | (Parser_JSON.JString t)::rest -> t :: (cmp_raw_type_names rest)
  | uu___::rest -> cmp_raw_type_names rest
let rec compact_elem (ac : JSONLD_Context.active_context)
  (aprop : Prims.string FStar_Pervasives_Native.option)
  (elem : Parser_JSON.json_val) (co : cmp_opts) (fuel : Prims.nat) :
  Parser_JSON.json_val FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (match elem with
     | Parser_JSON.JNull -> FStar_Pervasives_Native.Some elem
     | Parser_JSON.JBool uu___1 -> FStar_Pervasives_Native.Some elem
     | Parser_JSON.JString uu___1 -> FStar_Pervasives_Native.Some elem
     | Parser_JSON.JNumber uu___1 -> FStar_Pervasives_Native.Some elem
     | Parser_JSON.JArray items ->
         (match compact_items ac aprop items co (fuel - Prims.int_one) with
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some outs ->
              let collapse =
                (((co.co_arrays &&
                     (match outs with | uu___1::[] -> true | uu___1 -> false))
                    && (aprop <> (FStar_Pervasives_Native.Some "@graph")))
                   && (aprop <> (FStar_Pervasives_Native.Some "@set")))
                  && (Prims.uu___is_Nil (cmp_container_of ac aprop)) in
              if collapse
              then
                (match outs with
                 | x::[] -> FStar_Pervasives_Native.Some x
                 | uu___1 ->
                     FStar_Pervasives_Native.Some (Parser_JSON.JArray outs))
              else FStar_Pervasives_Native.Some (Parser_JSON.JArray outs))
     | Parser_JSON.JObject fields ->
         compact_map ac aprop fields co (fuel - Prims.int_one))
and compact_items (ac : JSONLD_Context.active_context)
  (aprop : Prims.string FStar_Pervasives_Native.option)
  (items : Parser_JSON.json_val Prims.list) (co : cmp_opts)
  (fuel : Prims.nat) :
  Parser_JSON.json_val Prims.list FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (match items with
     | [] -> FStar_Pervasives_Native.Some []
     | it::rest ->
         (match compact_elem ac aprop it co (fuel - Prims.int_one) with
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some c ->
              (match compact_items ac aprop rest co (fuel - Prims.int_one)
               with
               | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some cs ->
                   FStar_Pervasives_Native.Some (c :: cs))))
and compact_map (ac0 : JSONLD_Context.active_context)
  (aprop : Prims.string FStar_Pervasives_Native.option)
  (fields : (Prims.string * Parser_JSON.json_val) Prims.list) (co : cmp_opts)
  (fuel : Prims.nat) : Parser_JSON.json_val FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (let tsc = ac0 in
     let is_value = JSONLD_Expand.jexp_has_field "@value" fields in
     let id_only =
       match fields with
       | kv::[] -> (FStar_Pervasives_Native.fst kv) = "@id"
       | uu___1 -> false in
     let ac1 =
       match ac0.JSONLD_Context.ac_previous with
       | FStar_Pervasives_Native.Some prev ->
           if is_value || id_only then ac0 else prev
       | FStar_Pervasives_Native.None -> ac0 in
     let ac2_opt =
       match cmp_aprop_td tsc aprop with
       | FStar_Pervasives_Native.Some td ->
           (match td.JSONLD_Context.td_scoped_context with
            | FStar_Pervasives_Native.Some (scoped, def_url) ->
                JSONLD_Context.apply_context_with_propagate
                  {
                    JSONLD_Context.ac_terms = (ac1.JSONLD_Context.ac_terms);
                    JSONLD_Context.ac_vocab = (ac1.JSONLD_Context.ac_vocab);
                    JSONLD_Context.ac_base = (ac1.JSONLD_Context.ac_base);
                    JSONLD_Context.ac_language =
                      (ac1.JSONLD_Context.ac_language);
                    JSONLD_Context.ac_direction =
                      (ac1.JSONLD_Context.ac_direction);
                    JSONLD_Context.ac_previous =
                      (ac1.JSONLD_Context.ac_previous);
                    JSONLD_Context.ac_mode10 = (ac1.JSONLD_Context.ac_mode10);
                    JSONLD_Context.ac_doc_url = def_url;
                    JSONLD_Context.ac_original_base =
                      (ac1.JSONLD_Context.ac_original_base);
                    JSONLD_Context.ac_suppress_pop =
                      (ac1.JSONLD_Context.ac_suppress_pop);
                    JSONLD_Context.ac_frame_expansion =
                      (ac1.JSONLD_Context.ac_frame_expansion)
                  } scoped true true
            | FStar_Pervasives_Native.None ->
                FStar_Pervasives_Native.Some ac1)
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.Some ac1 in
     match ac2_opt with
     | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
     | FStar_Pervasives_Native.Some ac2 ->
         let has_id = JSONLD_Expand.jexp_has_field "@id" fields in
         let tmap2 =
           match cmp_aprop_td ac2 aprop with
           | FStar_Pervasives_Native.Some t ->
               t.JSONLD_Context.td_type_mapping
           | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None in
         if is_value || has_id
         then
           (match compact_value ac2 co aprop fields with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some r ->
                if
                  (cmp_is_scalar r) ||
                    (tmap2 = (FStar_Pervasives_Native.Some "@json"))
                then FStar_Pervasives_Native.Some r
                else
                  compact_map_body ac2 tsc aprop fields co
                    (fuel - Prims.int_one))
         else compact_map_body ac2 tsc aprop fields co (fuel - Prims.int_one))
and compact_map_body (ac2 : JSONLD_Context.active_context)
  (tsc : JSONLD_Context.active_context)
  (aprop : Prims.string FStar_Pervasives_Native.option)
  (fields : (Prims.string * Parser_JSON.json_val) Prims.list) (co : cmp_opts)
  (fuel : Prims.nat) : Parser_JSON.json_val FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    if
      (cmp_is_list_object (Parser_JSON.JObject fields)) &&
        (cmp_has_container ac2 aprop "@list")
    then
      (match cmp_field fields "@list" with
       | FStar_Pervasives_Native.Some lv ->
           compact_elem ac2 aprop lv co (fuel - Prims.int_one)
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
    else
      (let inside_rev = aprop = (FStar_Pervasives_Native.Some "@reverse") in
       let raw_types =
         match cmp_field fields "@type" with
         | FStar_Pervasives_Native.Some v -> JSONLD_Expand.jexp_as_array v
         | FStar_Pervasives_Native.None -> [] in
       match cmp_compact_types tsc co raw_types with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some ctype_names ->
           (match JSONLD_Context.jldctx_apply_type_scoped tsc ac2
                    (JSONLD_Context.jldctx_sort_strings ctype_names) false
            with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (ac3a, any_non_prop) ->
                let ac3 =
                  if any_non_prop
                  then
                    {
                      JSONLD_Context.ac_terms =
                        (ac3a.JSONLD_Context.ac_terms);
                      JSONLD_Context.ac_vocab =
                        (ac3a.JSONLD_Context.ac_vocab);
                      JSONLD_Context.ac_base = (ac3a.JSONLD_Context.ac_base);
                      JSONLD_Context.ac_language =
                        (ac3a.JSONLD_Context.ac_language);
                      JSONLD_Context.ac_direction =
                        (ac3a.JSONLD_Context.ac_direction);
                      JSONLD_Context.ac_previous =
                        (FStar_Pervasives_Native.Some ac2);
                      JSONLD_Context.ac_mode10 =
                        (ac3a.JSONLD_Context.ac_mode10);
                      JSONLD_Context.ac_doc_url =
                        (ac3a.JSONLD_Context.ac_doc_url);
                      JSONLD_Context.ac_original_base =
                        (ac3a.JSONLD_Context.ac_original_base);
                      JSONLD_Context.ac_suppress_pop =
                        (ac3a.JSONLD_Context.ac_suppress_pop);
                      JSONLD_Context.ac_frame_expansion =
                        (ac3a.JSONLD_Context.ac_frame_expansion)
                    }
                  else ac3a in
                (match compact_fields ac3 tsc aprop inside_rev fields [] co
                         (fuel - Prims.int_one)
                 with
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.None
                 | FStar_Pervasives_Native.Some res ->
                     FStar_Pervasives_Native.Some (Parser_JSON.JObject res))))
and compact_fields (ac : JSONLD_Context.active_context)
  (tsc : JSONLD_Context.active_context)
  (aprop : Prims.string FStar_Pervasives_Native.option)
  (inside_rev : Prims.bool)
  (pending : (Prims.string * Parser_JSON.json_val) Prims.list)
  (res : (Prims.string * Parser_JSON.json_val) Prims.list) (co : cmp_opts)
  (fuel : Prims.nat) :
  (Prims.string * Parser_JSON.json_val) Prims.list
    FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (match pending with
     | [] -> FStar_Pervasives_Native.Some res
     | (k, v)::rest ->
         if k = "@id"
         then
           (match v with
            | Parser_JSON.JString s ->
                (match compact_iri ac co s FStar_Pervasives_Native.None false
                         false (Prims.of_int (2))
                 with
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.None
                 | FStar_Pervasives_Native.Some cs ->
                     compact_fields ac tsc aprop inside_rev rest
                       (FStar_List_Tot_Base.append res
                          [((cmp_alias_kw ac co "@id"),
                             (Parser_JSON.JString cs))]) co
                       (fuel - Prims.int_one))
            | uu___1 ->
                compact_fields ac tsc aprop inside_rev rest
                  (FStar_List_Tot_Base.append res
                     [((cmp_alias_kw ac co "@id"), v)]) co
                  (fuel - Prims.int_one))
         else
           if k = "@type"
           then
             (match cmp_compact_types tsc co (JSONLD_Expand.jexp_as_array v)
              with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some cts ->
                  let alias = cmp_alias_kw ac co "@type" in
                  let as_set =
                    (Prims.op_Negation ac.JSONLD_Context.ac_mode10) &&
                      (match JSONLD_Context.jldctx_find_term
                               ac.JSONLD_Context.ac_terms alias
                       with
                       | FStar_Pervasives_Native.Some td ->
                           td.JSONLD_Context.td_set
                       | FStar_Pervasives_Native.None -> false) in
                  let cv =
                    match cts with
                    | single::[] ->
                        if co.co_arrays && (Prims.op_Negation as_set)
                        then Parser_JSON.JString single
                        else Parser_JSON.JArray [Parser_JSON.JString single]
                    | xs ->
                        Parser_JSON.JArray
                          (FStar_List_Tot_Base.map
                             (fun uu___2 -> Parser_JSON.JString uu___2) xs) in
                  compact_fields ac tsc aprop inside_rev rest
                    (FStar_List_Tot_Base.append res [(alias, cv)]) co
                    (fuel - Prims.int_one))
           else
             if k = "@reverse"
             then
               (match compact_elem ac
                        (FStar_Pervasives_Native.Some "@reverse") v co
                        (fuel - Prims.int_one)
                with
                | FStar_Pervasives_Native.None ->
                    FStar_Pervasives_Native.None
                | FStar_Pervasives_Native.Some cv ->
                    (match cv with
                     | Parser_JSON.JObject rf ->
                         let uu___3 = cmp_move_reverse ac co rf [] res in
                         (match uu___3 with
                          | (leftover, res1) ->
                              let res2 =
                                match leftover with
                                | [] -> res1
                                | uu___4 ->
                                    FStar_List_Tot_Base.append res1
                                      [((cmp_alias_kw ac co "@reverse"),
                                         (Parser_JSON.JObject leftover))] in
                              compact_fields ac tsc aprop inside_rev rest
                                res2 co (fuel - Prims.int_one))
                     | uu___3 ->
                         compact_fields ac tsc aprop inside_rev rest
                           (FStar_List_Tot_Base.append res
                              [((cmp_alias_kw ac co "@reverse"), cv)]) co
                           (fuel - Prims.int_one)))
             else
               if (k = "@index") && (cmp_has_container ac aprop "@index")
               then
                 compact_fields ac tsc aprop inside_rev rest res co
                   (fuel - Prims.int_one)
               else
                 if
                   (((k = "@index") || (k = "@value")) || (k = "@language"))
                     || (k = "@direction")
                 then
                   compact_fields ac tsc aprop inside_rev rest
                     (FStar_List_Tot_Base.append res
                        [((cmp_alias_kw ac co k), v)]) co
                     (fuel - Prims.int_one)
                 else
                   if k = "@preserve"
                   then
                     compact_fields ac tsc aprop inside_rev rest res co
                       (fuel - Prims.int_one)
                   else
                     (match v with
                      | Parser_JSON.JArray [] ->
                          (match compact_iri ac co k
                                   (FStar_Pervasives_Native.Some
                                      (Parser_JSON.JArray [])) true
                                   inside_rev (Prims.of_int (2))
                           with
                           | FStar_Pervasives_Native.None ->
                               FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some iap ->
                               (match cmp_nest_of ac iap with
                                | FStar_Pervasives_Native.None ->
                                    FStar_Pervasives_Native.None
                                | FStar_Pervasives_Native.Some nest ->
                                    let nres = cmp_nested_get res nest in
                                    let nres1 =
                                      match cmp_lookup nres iap with
                                      | FStar_Pervasives_Native.Some uu___7
                                          -> nres
                                      | FStar_Pervasives_Native.None ->
                                          FStar_List_Tot_Base.append nres
                                            [(iap, (Parser_JSON.JArray []))] in
                                    compact_fields ac tsc aprop inside_rev
                                      rest (cmp_nested_put res nest nres1) co
                                      (fuel - Prims.int_one)))
                      | uu___7 ->
                          (match compact_prop_items ac k
                                   (JSONLD_Expand.jexp_as_array v) inside_rev
                                   res co (fuel - Prims.int_one)
                           with
                           | FStar_Pervasives_Native.None ->
                               FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some res1 ->
                               compact_fields ac tsc aprop inside_rev rest
                                 res1 co (fuel - Prims.int_one))))
and compact_prop_items (ac : JSONLD_Context.active_context)
  (k : Prims.string) (items : Parser_JSON.json_val Prims.list)
  (inside_rev : Prims.bool)
  (res : (Prims.string * Parser_JSON.json_val) Prims.list) (co : cmp_opts)
  (fuel : Prims.nat) :
  (Prims.string * Parser_JSON.json_val) Prims.list
    FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (match items with
     | [] -> FStar_Pervasives_Native.Some res
     | it::rest ->
         (match compact_one_item ac k it inside_rev res co
                  (fuel - Prims.int_one)
          with
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some res1 ->
              compact_prop_items ac k rest inside_rev res1 co
                (fuel - Prims.int_one)))
and compact_one_item (ac : JSONLD_Context.active_context) (k : Prims.string)
  (item : Parser_JSON.json_val) (inside_rev : Prims.bool)
  (res : (Prims.string * Parser_JSON.json_val) Prims.list) (co : cmp_opts)
  (fuel : Prims.nat) :
  (Prims.string * Parser_JSON.json_val) Prims.list
    FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (match compact_iri ac co k (FStar_Pervasives_Native.Some item) true
             inside_rev (Prims.of_int (2))
     with
     | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
     | FStar_Pervasives_Native.Some iap ->
         (match cmp_nest_of ac iap with
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some nest ->
              let td_iap =
                JSONLD_Context.jldctx_find_term ac.JSONLD_Context.ac_terms
                  iap in
              let container =
                match td_iap with
                | FStar_Pervasives_Native.Some td ->
                    if td.JSONLD_Context.td_iri = "@null"
                    then []
                    else cmp_container_list td
                | FStar_Pervasives_Native.None -> [] in
              let is_list = cmp_is_list_object item in
              let is_graph = cmp_is_graph_object item in
              let inner =
                if is_list
                then
                  match cmp_obj_field item "@list" with
                  | FStar_Pervasives_Native.Some x -> x
                  | FStar_Pervasives_Native.None -> item
                else
                  if is_graph
                  then
                    (match cmp_obj_field item "@graph" with
                     | FStar_Pervasives_Native.Some x -> x
                     | FStar_Pervasives_Native.None -> item)
                  else item in
              (match compact_elem ac (FStar_Pervasives_Native.Some iap) inner
                       co (fuel - Prims.int_one)
               with
               | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some ci0 ->
                   let nres = cmp_nested_get res nest in
                   if is_list
                   then
                     let ci_arr =
                       match ci0 with
                       | Parser_JSON.JArray uu___1 -> ci0
                       | x -> Parser_JSON.JArray [x] in
                     (if
                        Prims.op_Negation
                          (FStar_List_Tot_Base.mem "@list" container)
                      then
                        let listobj =
                          FStar_List_Tot_Base.append
                            [((cmp_alias_kw ac co "@list"), ci_arr)]
                            (match cmp_obj_field item "@index" with
                             | FStar_Pervasives_Native.Some ix ->
                                 [((cmp_alias_kw ac co "@index"), ix)]
                             | FStar_Pervasives_Native.None -> []) in
                        cmp_item_add ac k iap container item
                          (Parser_JSON.JObject listobj) nest res nres co
                          (fuel - Prims.int_one)
                      else
                        (match cmp_lookup nres iap with
                         | FStar_Pervasives_Native.Some uu___2 ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.None ->
                             FStar_Pervasives_Native.Some
                               (cmp_nested_put res nest
                                  (FStar_List_Tot_Base.append nres
                                     [(iap, ci_arr)]))))
                   else
                     if is_graph
                     then
                       compact_graph_item ac k iap container item ci0 nest
                         res nres co (fuel - Prims.int_one)
                     else
                       cmp_item_add ac k iap container item ci0 nest res nres
                         co (fuel - Prims.int_one))))
and compact_graph_item (ac : JSONLD_Context.active_context)
  (k : Prims.string) (iap : Prims.string)
  (container : Prims.string Prims.list) (item : Parser_JSON.json_val)
  (ci0 : Parser_JSON.json_val)
  (nest : Prims.string FStar_Pervasives_Native.option)
  (res : (Prims.string * Parser_JSON.json_val) Prims.list)
  (nres : (Prims.string * Parser_JSON.json_val) Prims.list) (co : cmp_opts)
  (fuel : Prims.nat) :
  (Prims.string * Parser_JSON.json_val) Prims.list
    FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (let as_set = FStar_List_Tot_Base.mem "@set" container in
     let has_graph = FStar_List_Tot_Base.mem "@graph" container in
     if has_graph && (FStar_List_Tot_Base.mem "@id" container)
     then
       let key_res =
         match cmp_obj_field item "@id" with
         | FStar_Pervasives_Native.Some (Parser_JSON.JString gid) ->
             compact_iri ac co gid FStar_Pervasives_Native.None false false
               (Prims.of_int (2))
         | uu___1 ->
             compact_iri ac co "@none" FStar_Pervasives_Native.None true
               false (Prims.of_int (2)) in
       match key_res with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some keyk ->
           let mapObj =
             match cmp_lookup nres iap with
             | FStar_Pervasives_Native.Some (Parser_JSON.JObject mf) -> mf
             | uu___1 -> [] in
           let mapObj1 = cmp_generic_add mapObj keyk ci0 as_set in
           FStar_Pervasives_Native.Some
             (cmp_nested_put res nest
                (cmp_replace_or_add nres iap (Parser_JSON.JObject mapObj1)))
     else
       if
         (has_graph && (FStar_List_Tot_Base.mem "@index" container)) &&
           (cmp_is_simple_graph item)
       then
         (let keyk =
            match cmp_obj_field item "@index" with
            | FStar_Pervasives_Native.Some (Parser_JSON.JString ix) -> ix
            | uu___2 -> cmp_alias_kw ac co "@none" in
          let mapObj =
            match cmp_lookup nres iap with
            | FStar_Pervasives_Native.Some (Parser_JSON.JObject mf) -> mf
            | uu___2 -> [] in
          let mapObj1 = cmp_generic_add mapObj keyk ci0 as_set in
          FStar_Pervasives_Native.Some
            (cmp_nested_put res nest
               (cmp_replace_or_add nres iap (Parser_JSON.JObject mapObj1))))
       else
         if has_graph && (cmp_is_simple_graph item)
         then
           (let ci1 =
              match ci0 with
              | Parser_JSON.JArray xs ->
                  if (FStar_List_Tot_Base.length xs) > Prims.int_one
                  then
                    Parser_JSON.JObject
                      [((cmp_alias_kw ac co "@included"), ci0)]
                  else ci0
              | uu___3 -> ci0 in
            let as_arr = (Prims.op_Negation co.co_arrays) || as_set in
            FStar_Pervasives_Native.Some
              (cmp_nested_put res nest (cmp_generic_add nres iap ci1 as_arr)))
         else
           (let ci1 =
              match ci0 with
              | Parser_JSON.JArray (x::[]) -> if co.co_arrays then x else ci0
              | uu___4 -> ci0 in
            let id_fields_opt =
              match cmp_obj_field item "@id" with
              | FStar_Pervasives_Native.Some (Parser_JSON.JString gid) ->
                  (match compact_iri ac co gid FStar_Pervasives_Native.None
                           false false (Prims.of_int (2))
                   with
                   | FStar_Pervasives_Native.Some cg ->
                       FStar_Pervasives_Native.Some
                         [((cmp_alias_kw ac co "@id"),
                            (Parser_JSON.JString cg))]
                   | FStar_Pervasives_Native.None ->
                       FStar_Pervasives_Native.None)
              | uu___4 -> FStar_Pervasives_Native.Some [] in
            match id_fields_opt with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some id_fields ->
                let gwrap =
                  FStar_List_Tot_Base.append
                    [((cmp_alias_kw ac co "@graph"), ci1)]
                    (FStar_List_Tot_Base.append id_fields
                       (match cmp_obj_field item "@index" with
                        | FStar_Pervasives_Native.Some ix ->
                            [((cmp_alias_kw ac co "@index"), ix)]
                        | FStar_Pervasives_Native.None -> [])) in
                let as_arr = (Prims.op_Negation co.co_arrays) || as_set in
                FStar_Pervasives_Native.Some
                  (cmp_nested_put res nest
                     (cmp_generic_add nres iap (Parser_JSON.JObject gwrap)
                        as_arr))))
and cmp_item_add (ac : JSONLD_Context.active_context) (k : Prims.string)
  (iap : Prims.string) (container : Prims.string Prims.list)
  (item : Parser_JSON.json_val) (ci : Parser_JSON.json_val)
  (nest : Prims.string FStar_Pervasives_Native.option)
  (res : (Prims.string * Parser_JSON.json_val) Prims.list)
  (nres : (Prims.string * Parser_JSON.json_val) Prims.list) (co : cmp_opts)
  (fuel : Prims.nat) :
  (Prims.string * Parser_JSON.json_val) Prims.list
    FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (let as_set = FStar_List_Tot_Base.mem "@set" container in
     if
       (((FStar_List_Tot_Base.mem "@language" container) ||
           (FStar_List_Tot_Base.mem "@index" container))
          || (FStar_List_Tot_Base.mem "@id" container))
         || (FStar_List_Tot_Base.mem "@type" container)
     then
       let mapObj =
         match cmp_lookup nres iap with
         | FStar_Pervasives_Native.Some (Parser_JSON.JObject mf) -> mf
         | uu___1 -> [] in
       let step_res =
         if FStar_List_Tot_Base.mem "@language" container
         then
           let ci' =
             match item with
             | Parser_JSON.JObject f ->
                 if JSONLD_Expand.jexp_has_field "@value" f
                 then
                   (match cmp_field f "@value" with
                    | FStar_Pervasives_Native.Some vv -> vv
                    | FStar_Pervasives_Native.None -> ci)
                 else ci
             | uu___1 -> ci in
           FStar_Pervasives_Native.Some
             ((match cmp_obj_field item "@language" with
               | FStar_Pervasives_Native.Some (Parser_JSON.JString l) ->
                   FStar_Pervasives_Native.Some l
               | uu___1 -> FStar_Pervasives_Native.None), ci', false)
         else
           if FStar_List_Tot_Base.mem "@index" container
           then
             (match JSONLD_Context.jldctx_find_term
                      ac.JSONLD_Context.ac_terms iap
              with
              | FStar_Pervasives_Native.Some td ->
                  (match td.JSONLD_Context.td_index with
                   | FStar_Pervasives_Native.Some ik ->
                       (match ci with
                        | Parser_JSON.JObject cf ->
                            let ck_opt =
                              match cmp_lookup cf ik with
                              | FStar_Pervasives_Native.Some uu___2 ->
                                  FStar_Pervasives_Native.Some ik
                              | FStar_Pervasives_Native.None ->
                                  (match JSONLD_Context.expand_iri ac ik true
                                   with
                                   | FStar_Pervasives_Native.Some ikiri ->
                                       (match compact_iri ac co ikiri
                                                FStar_Pervasives_Native.None
                                                true false (Prims.of_int (2))
                                        with
                                        | FStar_Pervasives_Native.Some ck ->
                                            FStar_Pervasives_Native.Some ck
                                        | FStar_Pervasives_Native.None ->
                                            FStar_Pervasives_Native.None)
                                   | FStar_Pervasives_Native.None ->
                                       FStar_Pervasives_Native.None) in
                            (match ck_opt with
                             | FStar_Pervasives_Native.None ->
                                 FStar_Pervasives_Native.Some
                                   (FStar_Pervasives_Native.None, ci, false)
                             | FStar_Pervasives_Native.Some ck ->
                                 (match cmp_lookup cf ck with
                                  | FStar_Pervasives_Native.Some kv ->
                                      (match JSONLD_Expand.jexp_as_array kv
                                       with
                                       | (Parser_JSON.JString k0)::others ->
                                           let cf1 =
                                             match others with
                                             | [] -> cmp_remove_key cf ck
                                             | o::[] ->
                                                 cmp_replace_or_add cf ck o
                                             | os ->
                                                 cmp_replace_or_add cf ck
                                                   (Parser_JSON.JArray os) in
                                           FStar_Pervasives_Native.Some
                                             ((FStar_Pervasives_Native.Some
                                                 k0),
                                               (Parser_JSON.JObject cf1),
                                               false)
                                       | uu___2 ->
                                           FStar_Pervasives_Native.Some
                                             (FStar_Pervasives_Native.None,
                                               ci, false))
                                  | FStar_Pervasives_Native.None ->
                                      FStar_Pervasives_Native.Some
                                        (FStar_Pervasives_Native.None, ci,
                                          false)))
                        | uu___2 ->
                            FStar_Pervasives_Native.Some
                              (FStar_Pervasives_Native.None, ci, false))
                   | FStar_Pervasives_Native.None ->
                       let ci' =
                         match ci with
                         | Parser_JSON.JObject cf ->
                             Parser_JSON.JObject
                               (cmp_remove_key cf
                                  (cmp_alias_kw ac co "@index"))
                         | uu___2 -> ci in
                       FStar_Pervasives_Native.Some
                         (((match cmp_obj_field item "@index" with
                            | FStar_Pervasives_Native.Some
                                (Parser_JSON.JString ix) ->
                                FStar_Pervasives_Native.Some ix
                            | uu___2 -> FStar_Pervasives_Native.None)), ci',
                           false))
              | FStar_Pervasives_Native.None ->
                  let ci' =
                    match ci with
                    | Parser_JSON.JObject cf ->
                        Parser_JSON.JObject
                          (cmp_remove_key cf (cmp_alias_kw ac co "@index"))
                    | uu___2 -> ci in
                  FStar_Pervasives_Native.Some
                    (((match cmp_obj_field item "@index" with
                       | FStar_Pervasives_Native.Some (Parser_JSON.JString
                           ix) -> FStar_Pervasives_Native.Some ix
                       | uu___2 -> FStar_Pervasives_Native.None)), ci',
                      false))
           else
             if FStar_List_Tot_Base.mem "@id" container
             then
               (let idk = cmp_alias_kw ac co "@id" in
                match ci with
                | Parser_JSON.JObject cf ->
                    FStar_Pervasives_Native.Some
                      (((match cmp_lookup cf idk with
                         | FStar_Pervasives_Native.Some (Parser_JSON.JString
                             s) -> FStar_Pervasives_Native.Some s
                         | uu___3 -> FStar_Pervasives_Native.None)),
                        (Parser_JSON.JObject (cmp_remove_key cf idk)), false)
                | uu___3 ->
                    FStar_Pervasives_Native.Some
                      (FStar_Pervasives_Native.None, ci, false))
             else
               (let tk = cmp_alias_kw ac co "@type" in
                match ci with
                | Parser_JSON.JObject cf ->
                    (match cmp_lookup cf tk with
                     | FStar_Pervasives_Native.Some tv ->
                         (match JSONLD_Expand.jexp_as_array tv with
                          | (Parser_JSON.JString k0)::others ->
                              let cf1 =
                                match others with
                                | [] -> cmp_remove_key cf tk
                                | o::[] -> cmp_replace_or_add cf tk o
                                | os ->
                                    cmp_replace_or_add cf tk
                                      (Parser_JSON.JArray os) in
                              FStar_Pervasives_Native.Some
                                ((FStar_Pervasives_Native.Some k0),
                                  (Parser_JSON.JObject cf1), true)
                          | uu___4 ->
                              FStar_Pervasives_Native.Some
                                (FStar_Pervasives_Native.None,
                                  (Parser_JSON.JObject (cmp_remove_key cf tk)),
                                  true))
                     | FStar_Pervasives_Native.None ->
                         FStar_Pervasives_Native.Some
                           (FStar_Pervasives_Native.None, ci, true))
                | uu___4 ->
                    FStar_Pervasives_Native.Some
                      (FStar_Pervasives_Native.None, ci, false)) in
       match step_res with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some (key_opt, ci1, type_recheck) ->
           let ci2_opt =
             if type_recheck
             then
               match ci1 with
               | Parser_JSON.JObject (kv::[]) ->
                   (if
                      ((FStar_Pervasives_Native.fst kv) =
                         (cmp_alias_kw ac co "@id"))
                        &&
                        (FStar_Pervasives_Native.uu___is_Some
                           (cmp_obj_field item "@id"))
                    then
                      match cmp_obj_field item "@id" with
                      | FStar_Pervasives_Native.Some idv ->
                          (match compact_elem ac
                                   (FStar_Pervasives_Native.Some iap)
                                   (Parser_JSON.JObject [("@id", idv)]) co
                                   (fuel - Prims.int_one)
                           with
                           | FStar_Pervasives_Native.None ->
                               FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some rec_ci ->
                               (match rec_ci with
                                | Parser_JSON.JObject (kv2::[]) ->
                                    if
                                      (FStar_Pervasives_Native.fst kv2) =
                                        (cmp_alias_kw ac co "@id")
                                    then
                                      FStar_Pervasives_Native.Some
                                        (FStar_Pervasives_Native.snd kv2)
                                    else FStar_Pervasives_Native.Some rec_ci
                                | uu___1 ->
                                    FStar_Pervasives_Native.Some rec_ci))
                      | FStar_Pervasives_Native.None ->
                          FStar_Pervasives_Native.Some ci1
                    else FStar_Pervasives_Native.Some ci1)
               | uu___1 -> FStar_Pervasives_Native.Some ci1
             else FStar_Pervasives_Native.Some ci1 in
           (match ci2_opt with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some ci2 ->
                let keyk =
                  match key_opt with
                  | FStar_Pervasives_Native.Some s -> s
                  | FStar_Pervasives_Native.None ->
                      cmp_alias_kw ac co "@none" in
                let mapObj1 = cmp_add_value mapObj keyk ci2 as_set in
                FStar_Pervasives_Native.Some
                  (cmp_nested_put res nest
                     (cmp_replace_or_add nres iap
                        (Parser_JSON.JObject mapObj1))))
     else
       (let as_arr =
          (((((Prims.op_Negation co.co_arrays) || as_set) ||
               (FStar_List_Tot_Base.mem "@list" container))
              ||
              (match ci with
               | Parser_JSON.JArray [] -> true
               | uu___2 -> false))
             || (k = "@list"))
            || (k = "@graph") in
        FStar_Pervasives_Native.Some
          (cmp_nested_put res nest (cmp_generic_add nres iap ci as_arr))))
let cmp_ctx_is_empty (ctx : Parser_JSON.json_val) : Prims.bool=
  match ctx with
  | Parser_JSON.JNull -> true
  | Parser_JSON.JObject [] -> true
  | Parser_JSON.JArray [] -> true
  | uu___ -> false
let compact_document (input : Prims.string) (ctx_doc : Prims.string)
  (base : Prims.string FStar_Pervasives_Native.option)
  (ctx_url : Prims.string FStar_Pervasives_Native.option)
  (compact_arrays : Prims.bool) (compact_to_rel : Prims.bool)
  (processing_mode : Prims.string FStar_Pervasives_Native.option) :
  Parser_JSON.json_val FStar_Pervasives_Native.option=
  match Parser_JSONLD.expand_document input base FStar_Pervasives_Native.None
          processing_mode false
  with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some expanded ->
      (match Parser_JSON.parse_json ctx_doc with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some ctx_root ->
           let ctx_val =
             match ctx_root with
             | Parser_JSON.JObject cf ->
                 (match cmp_field cf "@context" with
                  | FStar_Pervasives_Native.Some c -> c
                  | FStar_Pervasives_Native.None -> ctx_root)
             | uu___ -> ctx_root in
           let mode10 =
             processing_mode = (FStar_Pervasives_Native.Some "json-ld-1.0") in
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
                 (JSONLD_Context.empty_active_context.JSONLD_Context.ac_suppress_pop);
               JSONLD_Context.ac_frame_expansion =
                 (JSONLD_Context.empty_active_context.JSONLD_Context.ac_frame_expansion)
             } in
           (match JSONLD_Context.context_process ac_seed ctx_val false
                    JSONLD_Context.jld_remote_context_fuel []
            with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some ac ->
                let co =
                  { co_arrays = compact_arrays; co_rel = compact_to_rel } in
                let fuel =
                  ((Prims.of_int (16)) * (Parser_JSON.json_size expanded)) +
                    (Prims.of_int (128)) in
                (match compact_elem ac FStar_Pervasives_Native.None expanded
                         co fuel
                 with
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.None
                 | FStar_Pervasives_Native.Some compacted0 ->
                     let compacted1 =
                       if compact_arrays
                       then
                         match compacted0 with
                         | Parser_JSON.JArray [] -> Parser_JSON.JObject []
                         | Parser_JSON.JArray (x::[]) -> x
                         | other -> other
                       else compacted0 in
                     let wrapped_opt =
                       match compacted1 with
                       | Parser_JSON.JArray uu___ ->
                           FStar_Pervasives_Native.Some
                             (Parser_JSON.JObject
                                [((cmp_alias_kw ac co "@graph"), compacted1)])
                       | Parser_JSON.JObject fs ->
                           FStar_Pervasives_Native.Some
                             (Parser_JSON.JObject fs)
                       | other -> FStar_Pervasives_Native.Some other in
                     (match wrapped_opt with
                      | FStar_Pervasives_Native.None ->
                          FStar_Pervasives_Native.None
                      | FStar_Pervasives_Native.Some wrapped ->
                          if cmp_ctx_is_empty ctx_val
                          then FStar_Pervasives_Native.Some wrapped
                          else
                            (match wrapped with
                             | Parser_JSON.JObject fs ->
                                 FStar_Pervasives_Native.Some
                                   (Parser_JSON.JObject
                                      (("@context", ctx_val) :: fs))
                             | other -> FStar_Pervasives_Native.Some other)))))
