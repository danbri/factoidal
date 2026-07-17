open Prims
type from_rdf_options =
  {
  use_native_types: Prims.bool ;
  use_rdf_type: Prims.bool ;
  rdf_direction: Prims.string FStar_Pervasives_Native.option }
let __proj__Mkfrom_rdf_options__item__use_native_types
  (projectee : from_rdf_options) : Prims.bool=
  match projectee with
  | { use_native_types; use_rdf_type; rdf_direction;_} -> use_native_types
let __proj__Mkfrom_rdf_options__item__use_rdf_type
  (projectee : from_rdf_options) : Prims.bool=
  match projectee with
  | { use_native_types; use_rdf_type; rdf_direction;_} -> use_rdf_type
let __proj__Mkfrom_rdf_options__item__rdf_direction
  (projectee : from_rdf_options) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | { use_native_types; use_rdf_type; rdf_direction;_} -> rdf_direction
let default_options : from_rdf_options=
  {
    use_native_types = false;
    use_rdf_type = false;
    rdf_direction = FStar_Pervasives_Native.None
  }
let rdf_type_iri : Prims.string=
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#type"
let rdf_first_iri : Prims.string=
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#first"
let rdf_rest_iri : Prims.string=
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#rest"
let rdf_nil_iri : Prims.string=
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#nil"
let rdf_json_iri : Prims.string=
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#JSON"
let rdf_list_iri : Prims.string=
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#List"
let rdf_value_iri : Prims.string=
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#value"
let rdf_direction_iri : Prims.string=
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#direction"
let rdf_language_iri : Prims.string=
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#language"
let i18n_prefix : Prims.string= "https://www.w3.org/ns/i18n#"
let sxsd_string : Prims.string= RDF_Term.xsd_string
let sxsd_integer : Prims.string= RDF_Term.xsd_integer
let sxsd_double : Prims.string= RDF_Term.xsd_double
let sxsd_boolean : Prims.string= RDF_Term.xsd_boolean
let strcat (a : Prims.string) (b : Prims.string) : Prims.string=
  FStar_String.concat "" [a; b]
type ov =
  | OV_Ref of Prims.string 
  | OV_Val of Parser_JSON.json_val 
  | OV_List of ov Prims.list 
let uu___is_OV_Ref (projectee : ov) : Prims.bool=
  match projectee with | OV_Ref _0 -> true | uu___ -> false
let __proj__OV_Ref__item___0 (projectee : ov) : Prims.string=
  match projectee with | OV_Ref _0 -> _0
let uu___is_OV_Val (projectee : ov) : Prims.bool=
  match projectee with | OV_Val _0 -> true | uu___ -> false
let __proj__OV_Val__item___0 (projectee : ov) : Parser_JSON.json_val=
  match projectee with | OV_Val _0 -> _0
let uu___is_OV_List (projectee : ov) : Prims.bool=
  match projectee with | OV_List _0 -> true | uu___ -> false
let __proj__OV_List__item___0 (projectee : ov) : ov Prims.list=
  match projectee with | OV_List _0 -> _0
type fr_node =
  {
  n_id: Prims.string ;
  n_blank: Prims.bool ;
  n_types: Prims.string Prims.list ;
  n_props: (Prims.string * ov Prims.list) Prims.list }
let __proj__Mkfr_node__item__n_id (projectee : fr_node) : Prims.string=
  match projectee with | { n_id; n_blank; n_types; n_props;_} -> n_id
let __proj__Mkfr_node__item__n_blank (projectee : fr_node) : Prims.bool=
  match projectee with | { n_id; n_blank; n_types; n_props;_} -> n_blank
let __proj__Mkfr_node__item__n_types (projectee : fr_node) :
  Prims.string Prims.list=
  match projectee with | { n_id; n_blank; n_types; n_props;_} -> n_types
let __proj__Mkfr_node__item__n_props (projectee : fr_node) :
  (Prims.string * ov Prims.list) Prims.list=
  match projectee with | { n_id; n_blank; n_types; n_props;_} -> n_props
type named_nm =
  {
  gn_name: Prims.string ;
  gn_blank: Prims.bool ;
  gn_map: fr_node Prims.list }
let __proj__Mknamed_nm__item__gn_name (projectee : named_nm) : Prims.string=
  match projectee with | { gn_name; gn_blank; gn_map;_} -> gn_name
let __proj__Mknamed_nm__item__gn_blank (projectee : named_nm) : Prims.bool=
  match projectee with | { gn_name; gn_blank; gn_map;_} -> gn_blank
let __proj__Mknamed_nm__item__gn_map (projectee : named_nm) :
  fr_node Prims.list=
  match projectee with | { gn_name; gn_blank; gn_map;_} -> gn_map
let subj_id (s : RDF_Term.subject) : Prims.string=
  match s with | RDF_Term.S_IRI i -> i | RDF_Term.S_BNode b -> strcat "_:" b
let subj_is_blank (s : RDF_Term.subject) : Prims.bool=
  RDF_Term.uu___is_S_BNode s
let term_node_id (o : RDF_Term.rdf_term) :
  (Prims.string * Prims.bool) FStar_Pervasives_Native.option=
  match o with
  | RDF_Term.T_IRI i -> FStar_Pervasives_Native.Some (i, false)
  | RDF_Term.T_BNode b ->
      FStar_Pervasives_Native.Some ((strcat "_:" b), true)
  | RDF_Term.T_Literal uu___ -> FStar_Pervasives_Native.None
  | RDF_Term.T_TripleTerm (uu___, uu___1, uu___2) ->
      FStar_Pervasives_Native.None
let starts_with_us (s : Prims.string) : Prims.bool=
  (((Parser_FastString.fs_byte_length s) >= (Prims.of_int (2))) &&
     ((Parser_FastString.fs_byte_at s Prims.int_zero) = (Prims.of_int (0x5F))))
    &&
    ((Parser_FastString.fs_byte_at s Prims.int_one) = (Prims.of_int (0x3A)))
let rec find_node (nm : fr_node Prims.list) (id : Prims.string) :
  fr_node FStar_Pervasives_Native.option=
  match nm with
  | [] -> FStar_Pervasives_Native.None
  | n::tl ->
      if n.n_id = id then FStar_Pervasives_Native.Some n else find_node tl id
let node_exists (nm : fr_node Prims.list) (id : Prims.string) : Prims.bool=
  FStar_Pervasives_Native.uu___is_Some (find_node nm id)
let ensure_node (nm : fr_node Prims.list) (id : Prims.string)
  (blank : Prims.bool) : fr_node Prims.list=
  if node_exists nm id
  then nm
  else
    FStar_List_Tot_Base.op_At nm
      [{ n_id = id; n_blank = blank; n_types = []; n_props = [] }]
let rec snoc_unique : 'a . 'a Prims.list -> 'a -> 'a Prims.list =
  fun xs x ->
    match xs with
    | [] -> [x]
    | h::tl -> if h = x then xs else h :: (snoc_unique tl x)
let rec find_prop (props : (Prims.string * ov Prims.list) Prims.list)
  (p : Prims.string) : ov Prims.list FStar_Pervasives_Native.option=
  match props with
  | [] -> FStar_Pervasives_Native.None
  | (k, vals)::tl ->
      if k = p then FStar_Pervasives_Native.Some vals else find_prop tl p
let node_prop_single (n : fr_node) (p : Prims.string) :
  ov FStar_Pervasives_Native.option=
  match find_prop n.n_props p with
  | FStar_Pervasives_Native.Some (v::[]) -> FStar_Pervasives_Native.Some v
  | uu___ -> FStar_Pervasives_Native.None
let rec prop_add (props : (Prims.string * ov Prims.list) Prims.list)
  (p : Prims.string) (v : ov) : (Prims.string * ov Prims.list) Prims.list=
  match props with
  | [] -> [(p, [v])]
  | (k, vals)::tl ->
      if k = p
      then (k, (snoc_unique vals v)) :: tl
      else (k, vals) :: (prop_add tl p v)
let node_update_prop (nm : fr_node Prims.list) (id : Prims.string)
  (p : Prims.string) (v : ov) : fr_node Prims.list=
  FStar_List_Tot_Base.map
    (fun n ->
       if n.n_id = id
       then
         {
           n_id = (n.n_id);
           n_blank = (n.n_blank);
           n_types = (n.n_types);
           n_props = (prop_add n.n_props p v)
         }
       else n) nm
let node_update_type (nm : fr_node Prims.list) (id : Prims.string)
  (t : Prims.string) : fr_node Prims.list=
  FStar_List_Tot_Base.map
    (fun n ->
       if n.n_id = id
       then
         {
           n_id = (n.n_id);
           n_blank = (n.n_blank);
           n_types = (snoc_unique n.n_types t);
           n_props = (n.n_props)
         }
       else n) nm
let is_dec_digit (c : Prims.nat) : Prims.bool=
  (c >= (Prims.of_int (0x30))) && (c <= (Prims.of_int (0x39)))
let rec all_dec_digits (s : Prims.string) (pos : Prims.nat)
  (fuel : Prims.nat) : Prims.bool=
  if fuel = Prims.int_zero
  then true
  else
    if pos >= (Parser_FastString.fs_byte_length s)
    then true
    else
      if is_dec_digit (Parser_FastString.fs_byte_at s pos)
      then all_dec_digits s (pos + Prims.int_one) (fuel - Prims.int_one)
      else false
let is_int_lexeme (s : Prims.string) : Prims.bool=
  let n = Parser_FastString.fs_byte_length s in
  if n = Prims.int_zero
  then false
  else
    (let first = Parser_FastString.fs_byte_at s Prims.int_zero in
     let start =
       if (first = (Prims.of_int (0x2B))) || (first = (Prims.of_int (0x2D)))
       then Prims.int_one
       else Prims.int_zero in
     (start < n) && (all_dec_digits s start ((n - start) + Prims.int_one)))
let rec find_exp_char (s : Prims.string) (pos : Prims.nat) (fuel : Prims.nat)
  : Prims.int=
  if (fuel = Prims.int_zero) || (pos >= (Parser_FastString.fs_byte_length s))
  then (Prims.of_int (-1))
  else
    (let c = Parser_FastString.fs_byte_at s pos in
     if (c = (Prims.of_int (0x65))) || (c = (Prims.of_int (0x45)))
     then pos
     else find_exp_char s (pos + Prims.int_one) (fuel - Prims.int_one))
let rec count_digits_from (s : Prims.string) (pos : Prims.nat)
  (fuel : Prims.nat) : Prims.nat=
  if (fuel = Prims.int_zero) || (pos >= (Parser_FastString.fs_byte_length s))
  then Prims.int_zero
  else
    (let c = Parser_FastString.fs_byte_at s pos in
     if is_dec_digit c
     then
       Prims.int_one +
         (count_digits_from s (pos + Prims.int_one) (fuel - Prims.int_one))
     else count_digits_from s (pos + Prims.int_one) (fuel - Prims.int_one))
let is_finite_double (s : Prims.string) : Prims.bool=
  match Parser_JSON.parse_json s with
  | FStar_Pervasives_Native.Some (Parser_JSON.JNumber uu___) ->
      let n = Parser_FastString.fs_byte_length s in
      let ei = find_exp_char s Prims.int_zero (n + Prims.int_one) in
      if ei < Prims.int_zero
      then true
      else
        (count_digits_from s (ei + Prims.int_one) (n + Prims.int_one)) <=
          (Prims.of_int (3))
  | uu___ -> false
let native_value (lex : Prims.string) (dt : Prims.string) : ov=
  if dt = sxsd_boolean
  then
    (if (lex = "true") || (lex = "1")
     then OV_Val (Parser_JSON.JObject [("@value", (Parser_JSON.JBool true))])
     else
       if (lex = "false") || (lex = "0")
       then
         OV_Val (Parser_JSON.JObject [("@value", (Parser_JSON.JBool false))])
       else
         OV_Val
           (Parser_JSON.JObject
              [("@value", (Parser_JSON.JString lex));
              ("@type", (Parser_JSON.JString dt))]))
  else
    if dt = sxsd_integer
    then
      (if is_int_lexeme lex
       then
         OV_Val (Parser_JSON.JObject [("@value", (Parser_JSON.JNumber lex))])
       else
         OV_Val
           (Parser_JSON.JObject
              [("@value", (Parser_JSON.JString lex));
              ("@type", (Parser_JSON.JString dt))]))
    else
      if dt = sxsd_double
      then
        (if is_finite_double lex
         then
           OV_Val
             (Parser_JSON.JObject [("@value", (Parser_JSON.JNumber lex))])
         else
           OV_Val
             (Parser_JSON.JObject
                [("@value", (Parser_JSON.JString lex));
                ("@type", (Parser_JSON.JString dt))]))
      else
        OV_Val
          (Parser_JSON.JObject
             [("@value", (Parser_JSON.JString lex));
             ("@type", (Parser_JSON.JString dt))])
let str_has_prefix (s : Prims.string) (pfx : Prims.string) : Prims.bool=
  let ls = Parser_FastString.fs_byte_length s in
  let lp = Parser_FastString.fs_byte_length pfx in
  (ls >= lp) && ((Parser_FastString.fs_byte_sub s Prims.int_zero lp) = pfx)
let rec last_us_pos (s : Prims.string) (pos : Prims.nat) (best : Prims.nat)
  (fuel : Prims.nat) : Prims.nat=
  if fuel = Prims.int_zero
  then best
  else
    if pos >= (Parser_FastString.fs_byte_length s)
    then best
    else
      last_us_pos s (pos + Prims.int_one)
        (if (Parser_FastString.fs_byte_at s pos) = (Prims.of_int (0x5F))
         then pos
         else best) (fuel - Prims.int_one)
let i18n_value_object (lex : Prims.string) (dt : Prims.string) : ov=
  let lp = Parser_FastString.fs_byte_length i18n_prefix in
  let dl = Parser_FastString.fs_byte_length dt in
  let frag =
    Parser_FastString.fs_byte_sub dt lp
      (if dl >= lp then dl - lp else Prims.int_zero) in
  let flen = Parser_FastString.fs_byte_length frag in
  let up = last_us_pos frag Prims.int_zero flen (flen + Prims.int_one) in
  let lang =
    if up >= flen
    then ""
    else Parser_FastString.fs_byte_sub frag Prims.int_zero up in
  let dir =
    if up >= flen
    then frag
    else
      Parser_FastString.fs_byte_sub frag (up + Prims.int_one)
        (if flen > (up + Prims.int_one)
         then (flen - up) - Prims.int_one
         else Prims.int_zero) in
  let base = [("@value", (Parser_JSON.JString lex))] in
  let with_lang =
    if (Parser_FastString.fs_byte_length lang) > Prims.int_zero
    then
      FStar_List_Tot_Base.op_At base
        [("@language", (Parser_JSON.JString lang))]
    else base in
  OV_Val
    (Parser_JSON.JObject
       (FStar_List_Tot_Base.op_At with_lang
          [("@direction", (Parser_JSON.JString dir))]))
let rdf_to_object (opts : from_rdf_options) (o : RDF_Term.rdf_term) :
  ov FStar_Pervasives_Native.option=
  match o with
  | RDF_Term.T_IRI i -> FStar_Pervasives_Native.Some (OV_Ref i)
  | RDF_Term.T_BNode b ->
      FStar_Pervasives_Native.Some (OV_Ref (strcat "_:" b))
  | RDF_Term.T_TripleTerm (uu___, uu___1, uu___2) ->
      FStar_Pervasives_Native.None
  | RDF_Term.T_Literal l ->
      let lex = l.RDF_Term.lexical_form in
      let dt = l.RDF_Term.datatype in
      (match l.RDF_Term.lang_tag with
       | FStar_Pervasives_Native.Some tag ->
           FStar_Pervasives_Native.Some
             (OV_Val
                (Parser_JSON.JObject
                   [("@value", (Parser_JSON.JString lex));
                   ("@language", (Parser_JSON.JString tag))]))
       | FStar_Pervasives_Native.None ->
           if
             (opts.rdf_direction =
                (FStar_Pervasives_Native.Some "i18n-datatype"))
               && (str_has_prefix dt i18n_prefix)
           then FStar_Pervasives_Native.Some (i18n_value_object lex dt)
           else
             if dt = rdf_json_iri
             then
               (match Parser_JSON.parse_json lex with
                | FStar_Pervasives_Native.Some j ->
                    FStar_Pervasives_Native.Some
                      (OV_Val
                         (Parser_JSON.JObject
                            [("@value", j);
                            ("@type", (Parser_JSON.JString "@json"))]))
                | FStar_Pervasives_Native.None ->
                    FStar_Pervasives_Native.None)
             else
               if dt = sxsd_string
               then
                 FStar_Pervasives_Native.Some
                   (OV_Val
                      (Parser_JSON.JObject
                         [("@value", (Parser_JSON.JString lex))]))
               else
                 if opts.use_native_types
                 then FStar_Pervasives_Native.Some (native_value lex dt)
                 else
                   FStar_Pervasives_Native.Some
                     (OV_Val
                        (Parser_JSON.JObject
                           [("@value", (Parser_JSON.JString lex));
                           ("@type", (Parser_JSON.JString dt))])))
let process_triple (opts : from_rdf_options) (nm : fr_node Prims.list)
  (t : RDF_Triple.triple) :
  fr_node Prims.list FStar_Pervasives_Native.option=
  let s_id = subj_id t.RDF_Triple.s in
  let s_blank = subj_is_blank t.RDF_Triple.s in
  let nm1 = ensure_node nm s_id s_blank in
  let nm2 =
    match term_node_id t.RDF_Triple.o with
    | FStar_Pervasives_Native.Some (oid, ob) -> ensure_node nm1 oid ob
    | FStar_Pervasives_Native.None -> nm1 in
  let p = t.RDF_Triple.p in
  let obj_is_node =
    (RDF_Term.uu___is_T_IRI t.RDF_Triple.o) ||
      (RDF_Term.uu___is_T_BNode t.RDF_Triple.o) in
  if
    ((p = rdf_type_iri) && (Prims.op_Negation opts.use_rdf_type)) &&
      obj_is_node
  then
    match term_node_id t.RDF_Triple.o with
    | FStar_Pervasives_Native.Some (oid, uu___) ->
        FStar_Pervasives_Native.Some (node_update_type nm2 s_id oid)
    | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.Some nm2
  else
    (match rdf_to_object opts t.RDF_Triple.o with
     | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
     | FStar_Pervasives_Native.Some v ->
         FStar_Pervasives_Native.Some (node_update_prop nm2 s_id p v))
let rec build_nodemap (opts : from_rdf_options) (nm : fr_node Prims.list)
  (ts : RDF_Triple.triple Prims.list) :
  fr_node Prims.list FStar_Pervasives_Native.option=
  match ts with
  | [] -> FStar_Pervasives_Native.Some nm
  | t::tl ->
      (match process_triple opts nm t with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some nm' -> build_nodemap opts nm' tl)
let rec build_named (opts : from_rdf_options)
  (ngs : RDF_Graph.named_graph Prims.list) :
  named_nm Prims.list FStar_Pervasives_Native.option=
  match ngs with
  | [] -> FStar_Pervasives_Native.Some []
  | ng::tl ->
      (match build_nodemap opts [] ng.RDF_Graph.ng_graph with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some m ->
           (match build_named opts tl with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some others ->
                FStar_Pervasives_Native.Some
                  ({
                     gn_name = (ng.RDF_Graph.ng_name);
                     gn_blank = (starts_with_us ng.RDF_Graph.ng_name);
                     gn_map = m
                   }
                  :: others)))
let rec add_graph_names (nm : fr_node Prims.list)
  (named : named_nm Prims.list) : fr_node Prims.list=
  match named with
  | [] -> nm
  | g::tl -> add_graph_names (ensure_node nm g.gn_name g.gn_blank) tl
let rec is_graph_name (named : named_nm Prims.list) (id : Prims.string) :
  Prims.bool=
  match named with
  | [] -> false
  | g::tl -> if g.gn_name = id then true else is_graph_name tl id
let rec lookup_graph_map (named : named_nm Prims.list) (id : Prims.string) :
  fr_node Prims.list FStar_Pervasives_Native.option=
  match named with
  | [] -> FStar_Pervasives_Native.None
  | g::tl ->
      if g.gn_name = id
      then FStar_Pervasives_Native.Some (g.gn_map)
      else lookup_graph_map tl id
let rec ovs_refids (vs : ov Prims.list) : Prims.string Prims.list=
  match vs with
  | [] -> []
  | (OV_Ref x)::tl -> x :: (ovs_refids tl)
  | uu___::tl -> ovs_refids tl
let rec props_refids (props : (Prims.string * ov Prims.list) Prims.list) :
  Prims.string Prims.list=
  match props with
  | [] -> []
  | (uu___, vals)::tl ->
      FStar_List_Tot_Base.op_At (ovs_refids vals) (props_refids tl)
let rec nodes_refids (nm : fr_node Prims.list) : Prims.string Prims.list=
  match nm with
  | [] -> []
  | n::tl ->
      FStar_List_Tot_Base.op_At (props_refids n.n_props) (nodes_refids tl)
let rec maps_refids (maps : fr_node Prims.list Prims.list) :
  Prims.string Prims.list=
  match maps with
  | [] -> []
  | m::tl -> FStar_List_Tot_Base.op_At (nodes_refids m) (maps_refids tl)
let count_occ (xs : Prims.string Prims.list) (x : Prims.string) : Prims.nat=
  FStar_List_Tot_Base.length (FStar_List_Tot_Base.filter (fun y -> y = x) xs)
let referenced_once (refids : Prims.string Prims.list) (id : Prims.string) :
  Prims.bool= (count_occ refids id) = Prims.int_one
let rec obj_lookup
  (fields : (Prims.string * Parser_JSON.json_val) Prims.list)
  (k : Prims.string) : Parser_JSON.json_val FStar_Pervasives_Native.option=
  match fields with
  | [] -> FStar_Pervasives_Native.None
  | (k2, v)::tl ->
      if k2 = k then FStar_Pervasives_Native.Some v else obj_lookup tl k
let cl_field (n : fr_node) (p : Prims.string) :
  Parser_JSON.json_val FStar_Pervasives_Native.option=
  match node_prop_single n p with
  | FStar_Pervasives_Native.Some (OV_Val (Parser_JSON.JObject fields)) ->
      obj_lookup fields "@value"
  | uu___ -> FStar_Pervasives_Native.None
let is_cl_shape (n : fr_node) : Prims.bool=
  (n.n_blank &&
     (FStar_Pervasives_Native.uu___is_Some (node_prop_single n rdf_value_iri)))
    &&
    (FStar_Pervasives_Native.uu___is_Some
       (node_prop_single n rdf_direction_iri))
let cl_value_object (n : fr_node) :
  Parser_JSON.json_val FStar_Pervasives_Native.option=
  match ((cl_field n rdf_value_iri), (cl_field n rdf_direction_iri)) with
  | (FStar_Pervasives_Native.Some v, FStar_Pervasives_Native.Some d) ->
      let lang = cl_field n rdf_language_iri in
      FStar_Pervasives_Native.Some
        (Parser_JSON.JObject
           (FStar_List_Tot_Base.op_At [("@value", v)]
              (FStar_List_Tot_Base.op_At
                 (match lang with
                  | FStar_Pervasives_Native.Some l -> [("@language", l)]
                  | FStar_Pervasives_Native.None -> []) [("@direction", d)])))
  | (uu___, uu___1) -> FStar_Pervasives_Native.None
let is_cl_collapsible (g : fr_node Prims.list)
  (refids : Prims.string Prims.list) (id : Prims.string) : Prims.bool=
  match find_node g id with
  | FStar_Pervasives_Native.None -> false
  | FStar_Pervasives_Native.Some n ->
      (is_cl_shape n) && (referenced_once refids id)
let is_list_shape (n : fr_node) : Prims.bool=
  (((n.n_blank && ((n.n_types = []) || (n.n_types = [rdf_list_iri]))) &&
      ((FStar_List_Tot_Base.length n.n_props) = (Prims.of_int (2))))
     &&
     (FStar_Pervasives_Native.uu___is_Some (node_prop_single n rdf_first_iri)))
    &&
    (FStar_Pervasives_Native.uu___is_Some (node_prop_single n rdf_rest_iri))
let rec is_collapsible (g : fr_node Prims.list)
  (refids : Prims.string Prims.list) (id : Prims.string) (fuel : Prims.nat) :
  Prims.bool=
  if fuel = Prims.int_zero
  then false
  else
    (match find_node g id with
     | FStar_Pervasives_Native.None -> false
     | FStar_Pervasives_Native.Some n ->
         if Prims.op_Negation (is_list_shape n)
         then false
         else
           if Prims.op_Negation (referenced_once refids id)
           then false
           else
             (match node_prop_single n rdf_rest_iri with
              | FStar_Pervasives_Native.Some (OV_Ref rt) ->
                  if rt = rdf_nil_iri
                  then true
                  else is_collapsible g refids rt (fuel - Prims.int_one)
              | uu___3 -> false))
let rec list_from (g : fr_node Prims.list) (refids : Prims.string Prims.list)
  (cl_mode : Prims.bool) (id : Prims.string) (fuel : Prims.nat) :
  ov Prims.list=
  if fuel = Prims.int_zero
  then []
  else
    (match find_node g id with
     | FStar_Pervasives_Native.None -> []
     | FStar_Pervasives_Native.Some n ->
         (match ((node_prop_single n rdf_first_iri),
                  (node_prop_single n rdf_rest_iri))
          with
          | (FStar_Pervasives_Native.Some fv, FStar_Pervasives_Native.Some
             (OV_Ref rt)) ->
              let elem = resolve g refids cl_mode fv (fuel - Prims.int_one) in
              if rt = rdf_nil_iri
              then [elem]
              else elem ::
                (list_from g refids cl_mode rt (fuel - Prims.int_one))
          | (uu___1, uu___2) -> []))
and resolve (g : fr_node Prims.list) (refids : Prims.string Prims.list)
  (cl_mode : Prims.bool) (v : ov) (fuel : Prims.nat) : ov=
  if fuel = Prims.int_zero
  then v
  else
    (match v with
     | OV_Ref x ->
         if x = rdf_nil_iri
         then OV_List []
         else
           if is_collapsible g refids x fuel
           then OV_List (list_from g refids cl_mode x (fuel - Prims.int_one))
           else
             if cl_mode && (is_cl_collapsible g refids x)
             then
               (match find_node g x with
                | FStar_Pervasives_Native.Some n ->
                    (match cl_value_object n with
                     | FStar_Pervasives_Native.Some j -> OV_Val j
                     | FStar_Pervasives_Native.None -> OV_Ref x)
                | FStar_Pervasives_Native.None -> OV_Ref x)
             else OV_Ref x
     | OV_Val j -> OV_Val j
     | OV_List l -> OV_List l)
let rewrite_node (g : fr_node Prims.list) (refids : Prims.string Prims.list)
  (cl_mode : Prims.bool) (fuel : Prims.nat) (n : fr_node) : fr_node=
  {
    n_id = (n.n_id);
    n_blank = (n.n_blank);
    n_types = (n.n_types);
    n_props =
      (FStar_List_Tot_Base.map
         (fun pv ->
            let uu___ = pv in
            match uu___ with
            | (p, vals) ->
                (p,
                  (FStar_List_Tot_Base.map
                     (fun v -> resolve g refids cl_mode v fuel) vals)))
         n.n_props)
  }
let rec ov_to_json (v : ov) : Parser_JSON.json_val=
  match v with
  | OV_Ref id -> Parser_JSON.JObject [("@id", (Parser_JSON.JString id))]
  | OV_Val j -> j
  | OV_List l ->
      Parser_JSON.JObject
        [("@list", (Parser_JSON.JArray (ov_list_to_json l)))]
and ov_list_to_json (l : ov Prims.list) : Parser_JSON.json_val Prims.list=
  match l with | [] -> [] | v::tl -> (ov_to_json v) :: (ov_list_to_json tl)
let types_field (types : Prims.string Prims.list) :
  (Prims.string * Parser_JSON.json_val) Prims.list=
  if Prims.uu___is_Cons types
  then
    [("@type",
       (Parser_JSON.JArray
          (FStar_List_Tot_Base.map (fun t -> Parser_JSON.JString t) types)))]
  else []
let graph_field
  (gj : Parser_JSON.json_val Prims.list FStar_Pervasives_Native.option) :
  (Prims.string * Parser_JSON.json_val) Prims.list=
  match gj with
  | FStar_Pervasives_Native.Some gs -> [("@graph", (Parser_JSON.JArray gs))]
  | FStar_Pervasives_Native.None -> []
let props_fields (props : (Prims.string * ov Prims.list) Prims.list) :
  (Prims.string * Parser_JSON.json_val) Prims.list=
  FStar_List_Tot_Base.map
    (fun pv ->
       let uu___ = pv in
       match uu___ with
       | (p, vals) ->
           (p,
             (Parser_JSON.JArray (FStar_List_Tot_Base.map ov_to_json vals))))
    props
let node_to_json (n : fr_node)
  (gj : Parser_JSON.json_val Prims.list FStar_Pervasives_Native.option) :
  Parser_JSON.json_val=
  Parser_JSON.JObject
    (FStar_List_Tot_Base.op_At [("@id", (Parser_JSON.JString (n.n_id)))]
       (FStar_List_Tot_Base.op_At (types_field n.n_types)
          (FStar_List_Tot_Base.op_At (graph_field gj)
             (props_fields n.n_props))))
let rec insert_sorted_node (n : fr_node) (xs : fr_node Prims.list) :
  fr_node Prims.list=
  match xs with
  | [] -> [n]
  | h::tl ->
      if RDF_Graph_Executable.string_lt n.n_id h.n_id
      then n :: xs
      else h :: (insert_sorted_node n tl)
let rec sort_nodes (xs : fr_node Prims.list) : fr_node Prims.list=
  match xs with | [] -> [] | h::tl -> insert_sorted_node h (sort_nodes tl)
let graph_fuel (g : fr_node Prims.list) : Prims.nat=
  ((Prims.of_int (4)) * (FStar_List_Tot_Base.length g)) + (Prims.of_int (16))
let emit_named_nodes (g : fr_node Prims.list)
  (refids : Prims.string Prims.list) (cl_mode : Prims.bool) :
  Parser_JSON.json_val Prims.list=
  let fuel = graph_fuel g in
  let survivors =
    FStar_List_Tot_Base.filter
      (fun n ->
         ((Prims.op_Negation (is_collapsible g refids n.n_id fuel)) &&
            (Prims.op_Negation
               (cl_mode && (is_cl_collapsible g refids n.n_id))))
           &&
           ((Prims.uu___is_Cons n.n_types) || (Prims.uu___is_Cons n.n_props)))
      g in
  let rewritten =
    FStar_List_Tot_Base.map (rewrite_node g refids cl_mode fuel) survivors in
  let ordered = sort_nodes rewritten in
  FStar_List_Tot_Base.map
    (fun n -> node_to_json n FStar_Pervasives_Native.None) ordered
let emit_default_nodes (dm : fr_node Prims.list)
  (named : named_nm Prims.list) (refids : Prims.string Prims.list)
  (cl_mode : Prims.bool) : Parser_JSON.json_val Prims.list=
  let fuel = graph_fuel dm in
  let survivors =
    FStar_List_Tot_Base.filter
      (fun n ->
         ((Prims.op_Negation (is_collapsible dm refids n.n_id fuel)) &&
            (Prims.op_Negation
               (cl_mode && (is_cl_collapsible dm refids n.n_id))))
           &&
           (((Prims.uu___is_Cons n.n_types) || (Prims.uu___is_Cons n.n_props))
              || (is_graph_name named n.n_id))) dm in
  let rewritten =
    FStar_List_Tot_Base.map (rewrite_node dm refids cl_mode fuel) survivors in
  let ordered = sort_nodes rewritten in
  FStar_List_Tot_Base.map
    (fun n ->
       let gj =
         if is_graph_name named n.n_id
         then
           match lookup_graph_map named n.n_id with
           | FStar_Pervasives_Native.Some gm ->
               FStar_Pervasives_Native.Some
                 (emit_named_nodes gm refids cl_mode)
           | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.Some []
         else FStar_Pervasives_Native.None in
       node_to_json n gj) ordered
let from_rdf (ds : RDF_Graph.rdf_dataset) (opts : from_rdf_options) :
  Parser_JSON.json_val FStar_Pervasives_Native.option=
  match build_nodemap opts [] ds.RDF_Graph.ds_default with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some dm0 ->
      (match build_named opts ds.RDF_Graph.ds_named with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some named ->
           let dm = add_graph_names dm0 named in
           let all_maps = dm ::
             (FStar_List_Tot_Base.map (fun g -> g.gn_map) named) in
           let refids = maps_refids all_maps in
           let cl_mode =
             opts.rdf_direction =
               (FStar_Pervasives_Native.Some "compound-literal") in
           FStar_Pervasives_Native.Some
             (Parser_JSON.JArray (emit_default_nodes dm named refids cl_mode)))
