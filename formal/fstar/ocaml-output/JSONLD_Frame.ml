open Prims
let is_keyword (k : Prims.string) : Prims.bool=
  (Parser_JSON.jbyte_at k Prims.int_zero) = (Prims.of_int (0x40))
let obj_fields (v : Parser_JSON.json_val) :
  (Prims.string * Parser_JSON.json_val) Prims.list=
  match v with | Parser_JSON.JObject fs -> fs | uu___ -> []
let obj_get (v : Parser_JSON.json_val) (k : Prims.string) :
  Parser_JSON.json_val FStar_Pervasives_Native.option=
  FStar_List_Tot_Base.assoc k (obj_fields v)
let obj_has (v : Parser_JSON.json_val) (k : Prims.string) : Prims.bool=
  FStar_Pervasives_Native.uu___is_Some (obj_get v k)
let rec jstrings (v : Parser_JSON.json_val) : Prims.string Prims.list=
  match v with
  | Parser_JSON.JString s -> [s]
  | Parser_JSON.JArray items -> jstrings_list items
  | uu___ -> []
and jstrings_list (items : Parser_JSON.json_val Prims.list) :
  Prims.string Prims.list=
  match items with
  | [] -> []
  | hd::tl -> FStar_List_Tot_Base.op_At (jstrings hd) (jstrings_list tl)
let node_types (node : Parser_JSON.json_val) : Prims.string Prims.list=
  match obj_get node "@type" with
  | FStar_Pervasives_Native.Some tv -> jstrings tv
  | FStar_Pervasives_Native.None -> []
let node_id (node : Parser_JSON.json_val) :
  Prims.string FStar_Pervasives_Native.option=
  match obj_get node "@id" with
  | FStar_Pervasives_Native.Some (Parser_JSON.JString s) ->
      FStar_Pervasives_Native.Some s
  | uu___ -> FStar_Pervasives_Native.None
let is_wildcard (v : Parser_JSON.json_val) : Prims.bool=
  match v with | Parser_JSON.JObject [] -> true | uu___ -> false
let is_empty_array (v : Parser_JSON.json_val) : Prims.bool=
  match v with | Parser_JSON.JArray [] -> true | uu___ -> false
let prop_values (node : Parser_JSON.json_val) (k : Prims.string) :
  Parser_JSON.json_val Prims.list=
  match obj_get node k with
  | FStar_Pervasives_Native.Some (Parser_JSON.JArray xs) -> xs
  | FStar_Pervasives_Native.Some other -> [other]
  | FStar_Pervasives_Native.None -> []
let ref_id (v : Parser_JSON.json_val) :
  Prims.string FStar_Pervasives_Native.option=
  match v with
  | Parser_JSON.JObject fs ->
      (match FStar_List_Tot_Base.assoc "@id" fs with
       | FStar_Pervasives_Native.Some (Parser_JSON.JString x) ->
           FStar_Pervasives_Native.Some x
       | uu___ -> FStar_Pervasives_Native.None)
  | uu___ -> FStar_Pervasives_Native.None
let prop_subframe (fv : Parser_JSON.json_val) : Parser_JSON.json_val=
  match fv with
  | Parser_JSON.JArray ((Parser_JSON.JObject o)::uu___) ->
      Parser_JSON.JObject o
  | Parser_JSON.JObject o -> Parser_JSON.JObject o
  | uu___ -> Parser_JSON.JObject []
let frame_explicit (frame : Parser_JSON.json_val) : Prims.bool=
  match obj_get frame "@explicit" with
  | FStar_Pervasives_Native.Some (Parser_JSON.JBool b) -> b
  | uu___ -> false
let match_one (k : Prims.string) (fv : Parser_JSON.json_val)
  (node : Parser_JSON.json_val) : Prims.bool=
  if k = "@type"
  then
    let ft = jstrings fv in
    let nt = node_types node in
    (if (Prims.uu___is_Nil ft) || (is_wildcard fv)
     then Prims.uu___is_Cons nt
     else
       FStar_List_Tot_Base.existsb (fun t -> FStar_List_Tot_Base.mem t ft) nt)
  else
    if k = "@id"
    then
      (let fid = jstrings fv in
       if (is_wildcard fv) || (Prims.uu___is_Nil fid)
       then true
       else
         (match node_id node with
          | FStar_Pervasives_Native.Some nid ->
              FStar_List_Tot_Base.mem nid fid
          | FStar_Pervasives_Native.None -> false))
    else
      if is_keyword k
      then true
      else
        if is_empty_array fv
        then Prims.op_Negation (obj_has node k)
        else obj_has node k
let rec matches_fields
  (frame_fields : (Prims.string * Parser_JSON.json_val) Prims.list)
  (node : Parser_JSON.json_val) : Prims.bool=
  match frame_fields with
  | [] -> true
  | (k, fv)::tl -> (match_one k fv node) && (matches_fields tl node)
let node_matches (frame : Parser_JSON.json_val) (node : Parser_JSON.json_val)
  : Prims.bool= matches_fields (obj_fields frame) node
let rec frame_node (map : (Prims.string * Parser_JSON.json_val) Prims.list)
  (frame : Parser_JSON.json_val) (node : Parser_JSON.json_val)
  (visited : Prims.string Prims.list) (fuel : Prims.nat) :
  Parser_JSON.json_val=
  if fuel = Prims.int_zero
  then node
  else
    (let id_entry =
       match obj_get node "@id" with
       | FStar_Pervasives_Native.Some v -> [("@id", v)]
       | FStar_Pervasives_Native.None -> [] in
     let type_entry =
       match obj_get node "@type" with
       | FStar_Pervasives_Native.Some v -> [("@type", v)]
       | FStar_Pervasives_Native.None -> [] in
     let prop_entries =
       frame_props map frame (obj_fields node) node visited fuel in
     Parser_JSON.JObject
       (FStar_List_Tot_Base.op_At id_entry
          (FStar_List_Tot_Base.op_At type_entry prop_entries)))
and frame_props (map : (Prims.string * Parser_JSON.json_val) Prims.list)
  (frame : Parser_JSON.json_val)
  (node_fields : (Prims.string * Parser_JSON.json_val) Prims.list)
  (node : Parser_JSON.json_val) (visited : Prims.string Prims.list)
  (fuel : Prims.nat) : (Prims.string * Parser_JSON.json_val) Prims.list=
  match node_fields with
  | [] -> []
  | (k, uu___)::tl ->
      let rest = frame_props map frame tl node visited fuel in
      if is_keyword k
      then rest
      else
        (match obj_get frame k with
         | FStar_Pervasives_Native.Some fv ->
             let vals = prop_values node k in
             let subframe = prop_subframe fv in
             let framed = frame_values map subframe vals visited fuel in
             (k, (Parser_JSON.JArray framed)) :: rest
         | FStar_Pervasives_Native.None ->
             if frame_explicit frame
             then rest
             else
               (let vals = prop_values node k in
                let framed =
                  frame_values map (Parser_JSON.JObject []) vals visited fuel in
                (k, (Parser_JSON.JArray framed)) :: rest))
and frame_values (map : (Prims.string * Parser_JSON.json_val) Prims.list)
  (subframe : Parser_JSON.json_val) (vals : Parser_JSON.json_val Prims.list)
  (visited : Prims.string Prims.list) (fuel : Prims.nat) :
  Parser_JSON.json_val Prims.list=
  match vals with
  | [] -> []
  | v::tl ->
      let rest = frame_values map subframe tl visited fuel in
      let this =
        if fuel = Prims.int_zero
        then v
        else
          (match ref_id v with
           | FStar_Pervasives_Native.Some x ->
               (match FStar_List_Tot_Base.assoc x map with
                | FStar_Pervasives_Native.Some target ->
                    if FStar_List_Tot_Base.mem x visited
                    then v
                    else
                      frame_node map subframe target (x :: visited)
                        (fuel - Prims.int_one)
                | FStar_Pervasives_Native.None -> v)
           | FStar_Pervasives_Native.None -> v) in
      this :: rest
let rec build_node_map (nodes : Parser_JSON.json_val Prims.list) :
  (Prims.string * Parser_JSON.json_val) Prims.list=
  match nodes with
  | [] -> []
  | n::tl ->
      (match node_id n with
       | FStar_Pervasives_Native.Some id -> (id, n) :: (build_node_map tl)
       | FStar_Pervasives_Native.None -> build_node_map tl)
let first_frame (frame_exp : Parser_JSON.json_val) : Parser_JSON.json_val=
  match frame_exp with
  | Parser_JSON.JArray ((Parser_JSON.JObject o)::uu___) ->
      Parser_JSON.JObject o
  | Parser_JSON.JObject o -> Parser_JSON.JObject o
  | uu___ -> Parser_JSON.JObject []
let rec top_frame (map : (Prims.string * Parser_JSON.json_val) Prims.list)
  (frame : Parser_JSON.json_val) (nodes : Parser_JSON.json_val Prims.list)
  (fuel : Prims.nat) : Parser_JSON.json_val Prims.list=
  match nodes with
  | [] -> []
  | n::tl ->
      let rest = top_frame map frame tl fuel in
      if node_matches frame n
      then
        let seed =
          match node_id n with
          | FStar_Pervasives_Native.Some id -> [id]
          | FStar_Pervasives_Native.None -> [] in
        (frame_node map frame n seed fuel) :: rest
      else rest
let frame_document (input_str : Prims.string) (frame_str : Prims.string)
  (base : Prims.string FStar_Pervasives_Native.option)
  (processing_mode : Prims.string FStar_Pervasives_Native.option) :
  Parser_JSON.json_val FStar_Pervasives_Native.option=
  match Parser_JSONLD.expand_document input_str base
          FStar_Pervasives_Native.None processing_mode false
  with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some expanded ->
      (match JSONLD_Flatten.jld_flatten_expanded expanded with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some nodes ->
           let map = build_node_map nodes in
           (match Parser_JSONLD.expand_document frame_str base
                    FStar_Pervasives_Native.None processing_mode true
            with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some frame_exp ->
                let frame = first_frame frame_exp in
                let fuel =
                  ((Prims.of_int (16)) * (Parser_JSON.json_size expanded)) +
                    (Prims.of_int (128)) in
                let trees = top_frame map frame nodes fuel in
                let framed =
                  Parser_JSON.JObject
                    [("@graph", (Parser_JSON.JArray trees))] in
                let framed_str = Parser_JSONLD.jcanon_document framed in
                JSONLD_Compact.compact_document framed_str frame_str base
                  FStar_Pervasives_Native.None true true processing_mode))
