open Prims
let cj_starts_with (s : Prims.string) (pfx : Prims.string) : Prims.bool=
  ((FStar_String.strlen s) >= (FStar_String.strlen pfx)) &&
    ((FStar_String.sub s Prims.int_zero (FStar_String.strlen pfx)) = pfx)
let cj_is_hex (c : FStar_Char.char) : Prims.bool=
  let n = FStar_Char.int_of_char c in
  (((n >= (Prims.of_int (48))) && (n <= (Prims.of_int (57)))) ||
     ((n >= (Prims.of_int (65))) && (n <= (Prims.of_int (70)))))
    || ((n >= (Prims.of_int (97))) && (n <= (Prims.of_int (102))))
let cj_hexv (c : FStar_Char.char) : Prims.nat=
  let n = FStar_Char.int_of_char c in
  if (n >= (Prims.of_int (48))) && (n <= (Prims.of_int (57)))
  then n - (Prims.of_int (48))
  else
    if (n >= (Prims.of_int (65))) && (n <= (Prims.of_int (70)))
    then n - (Prims.of_int (55))
    else
      if (n >= (Prims.of_int (97))) && (n <= (Prims.of_int (102)))
      then n - (Prims.of_int (87))
      else Prims.int_zero
let rec cj_url_decode_chars (cs : FStar_Char.char Prims.list) :
  FStar_Char.char Prims.list=
  match cs with
  | [] -> []
  | c::rest ->
      if (FStar_Char.int_of_char c) = (Prims.of_int (37))
      then
        (match rest with
         | h1::h2::rest' ->
             if (cj_is_hex h1) && (cj_is_hex h2)
             then
               let v = ((cj_hexv h1) * (Prims.of_int (16))) + (cj_hexv h2) in
               (FStar_Char.char_of_int v) :: (cj_url_decode_chars rest')
             else c :: (cj_url_decode_chars rest)
         | uu___ -> c :: (cj_url_decode_chars rest))
      else c :: (cj_url_decode_chars rest)
let cj_url_decode (s : Prims.string) : Prims.string=
  FStar_String.string_of_list
    (cj_url_decode_chars (FStar_String.list_of_string s))
let cj_prefixes : (Prims.string * Prims.string) Prims.list=
  [("csvw", "http://www.w3.org/ns/csvw#");
  ("rdf", "http://www.w3.org/1999/02/22-rdf-syntax-ns#");
  ("rdfs", "http://www.w3.org/2000/01/rdf-schema#");
  ("xsd", "http://www.w3.org/2001/XMLSchema#");
  ("dcat", "http://www.w3.org/ns/dcat#");
  ("dc", "http://purl.org/dc/terms/");
  ("dc11", "http://purl.org/dc/elements/1.1/");
  ("schema", "http://schema.org/");
  ("foaf", "http://xmlns.com/foaf/0.1/");
  ("skos", "http://www.w3.org/2004/02/skos/core#");
  ("owl", "http://www.w3.org/2002/07/owl#");
  ("org", "http://www.w3.org/ns/org#");
  ("oa", "http://www.w3.org/ns/oa#");
  ("prov", "http://www.w3.org/ns/prov#");
  ("as", "https://www.w3.org/ns/activitystreams#")]
let rec cj_compact_try (u : Prims.string)
  (ps : (Prims.string * Prims.string) Prims.list) : Prims.string=
  match ps with
  | [] -> u
  | (pfx, ns)::tl ->
      if
        (cj_starts_with u ns) &&
          ((FStar_String.strlen u) > (FStar_String.strlen ns))
      then
        Prims.strcat pfx
          (Prims.strcat ":"
             (FStar_String.sub u (FStar_String.strlen ns)
                ((FStar_String.strlen u) - (FStar_String.strlen ns))))
      else cj_compact_try u tl
let cj_compact_url (u : Prims.string) : Prims.string=
  cj_compact_try u cj_prefixes
let cj_xsd_ns : Prims.string= "http://www.w3.org/2001/XMLSchema#"
let cj_dt_local (dt : Prims.string) : Prims.string=
  if cj_starts_with dt cj_xsd_ns
  then
    FStar_String.sub dt (FStar_String.strlen cj_xsd_ns)
      ((FStar_String.strlen dt) - (FStar_String.strlen cj_xsd_ns))
  else dt
let cj_is_numeric_dt (dt : Prims.string) : Prims.bool=
  let n = cj_dt_local dt in
  (((((((((((((((n = "decimal") || (n = "integer")) || (n = "long")) ||
                (n = "int"))
               || (n = "short"))
              || (n = "byte"))
             || (n = "nonNegativeInteger"))
            || (n = "positiveInteger"))
           || (n = "unsignedLong"))
          || (n = "unsignedInt"))
         || (n = "unsignedShort"))
        || (n = "unsignedByte"))
       || (n = "nonPositiveInteger"))
      || (n = "negativeInteger"))
     || (n = "double"))
    || (n = "float")
let cj_is_boolean_dt (dt : Prims.string) : Prims.bool=
  (cj_dt_local dt) = "boolean"
let cj_strip_plus (s : Prims.string) : Prims.string=
  if
    ((FStar_String.strlen s) >= Prims.int_one) &&
      ((FStar_String.sub s Prims.int_zero Prims.int_one) = "+")
  then
    FStar_String.sub s Prims.int_one
      ((FStar_String.strlen s) - Prims.int_one)
  else s
let cj_is_special_num (s : Prims.string) : Prims.bool=
  ((s = "NaN") || (s = "INF")) || (s = "-INF")
let cj_json_of_term (t : RDF_Term.rdf_term) : Parser_JSON.json_val=
  match t with
  | RDF_Term.T_IRI i -> Parser_JSON.JString i
  | RDF_Term.T_BNode b -> Parser_JSON.JString b
  | RDF_Term.T_Literal l ->
      if cj_is_numeric_dt l.RDF_Term.datatype
      then
        (if cj_is_special_num l.RDF_Term.lexical_form
         then Parser_JSON.JString (l.RDF_Term.lexical_form)
         else Parser_JSON.JNumber (cj_strip_plus l.RDF_Term.lexical_form))
      else
        if cj_is_boolean_dt l.RDF_Term.datatype
        then Parser_JSON.JBool (l.RDF_Term.lexical_form = "true")
        else Parser_JSON.JString (l.RDF_Term.lexical_form)
  | RDF_Term.T_TripleTerm (uu___, uu___1, uu___2) -> Parser_JSON.JNull
type cj_pair =
  {
  cjp_key: Prims.string ;
  cjp_url: Prims.bool ;
  cjp_list: Prims.bool ;
  cjp_vals: Parser_JSON.json_val Prims.list }
let __proj__Mkcj_pair__item__cjp_key (projectee : cj_pair) : Prims.string=
  match projectee with | { cjp_key; cjp_url; cjp_list; cjp_vals;_} -> cjp_key
let __proj__Mkcj_pair__item__cjp_url (projectee : cj_pair) : Prims.bool=
  match projectee with | { cjp_key; cjp_url; cjp_list; cjp_vals;_} -> cjp_url
let __proj__Mkcj_pair__item__cjp_list (projectee : cj_pair) : Prims.bool=
  match projectee with
  | { cjp_key; cjp_url; cjp_list; cjp_vals;_} -> cjp_list
let __proj__Mkcj_pair__item__cjp_vals (projectee : cj_pair) :
  Parser_JSON.json_val Prims.list=
  match projectee with
  | { cjp_key; cjp_url; cjp_list; cjp_vals;_} -> cjp_vals
let cj_type_value (o : RDF_Term.rdf_term) : Parser_JSON.json_val=
  match o with
  | RDF_Term.T_IRI i -> Parser_JSON.JString (cj_compact_url i)
  | uu___ -> cj_json_of_term o
let cj_cell_key (table_url_resolved : Prims.string)
  (cur_lookup : Prims.string -> Prims.string FStar_Pervasives_Native.option)
  (spec : CSVW_Conversion.csvw_col_spec) : Prims.string=
  match spec.CSVW_Conversion.cs_property_url with
  | FStar_Pervasives_Native.Some tmpl ->
      let raw =
        RDF_IRI.resolve_iri_v2 table_url_resolved
          (CSVW_Conversion.csvw_expand_curie
             (CSVW_URITemplate.csvw_expand_template cur_lookup tmpl)) in
      let k = cj_compact_url raw in if k = "rdf:type" then "@type" else k
  | FStar_Pervasives_Native.None -> spec.CSVW_Conversion.cs_name
let cj_process_cell (table_url_resolved : Prims.string)
  (cur_lookup : Prims.string -> Prims.string FStar_Pervasives_Native.option)
  (default_subject : RDF_Term.subject) (spec : CSVW_Conversion.csvw_col_spec)
  (cell_text : Prims.string FStar_Pervasives_Native.option) :
  (RDF_Term.subject * cj_pair FStar_Pervasives_Native.option)=
  if spec.CSVW_Conversion.cs_suppress
  then (default_subject, FStar_Pervasives_Native.None)
  else
    (let subj =
       match spec.CSVW_Conversion.cs_about_url with
       | FStar_Pervasives_Native.Some tmpl ->
           let raw = CSVW_URITemplate.csvw_expand_template cur_lookup tmpl in
           let resolved = RDF_IRI.resolve_iri_v2 table_url_resolved raw in
           if RDF_Term.is_iri resolved
           then RDF_Term.S_IRI resolved
           else default_subject
       | FStar_Pervasives_Native.None -> default_subject in
     let key0 = cj_cell_key table_url_resolved cur_lookup spec in
     let is_type = key0 = "@type" in
     let has_value_url =
       FStar_Pervasives_Native.uu___is_Some spec.CSVW_Conversion.cs_value_url in
     match ((spec.CSVW_Conversion.cs_separator), cell_text) with
     | (FStar_Pervasives_Native.Some sep, FStar_Pervasives_Native.Some txt)
         ->
         let parts = CSVW_Conversion.csvw_split_list_cell sep txt in
         let objs =
           FStar_List_Tot_Base.choose
             (fun part ->
                CSVW_Conversion.csvw_cell_object table_url_resolved spec
                  (FStar_Pervasives_Native.Some part) cur_lookup) parts in
         (match objs with
          | [] -> (subj, FStar_Pervasives_Native.None)
          | uu___1 ->
              let vals =
                FStar_List_Tot_Base.map
                  (fun o ->
                     if is_type then cj_type_value o else cj_json_of_term o)
                  objs in
              (subj,
                (FStar_Pervasives_Native.Some
                   {
                     cjp_key = key0;
                     cjp_url = has_value_url;
                     cjp_list = true;
                     cjp_vals = vals
                   })))
     | uu___1 ->
         (match CSVW_Conversion.csvw_cell_object table_url_resolved spec
                  cell_text cur_lookup
          with
          | FStar_Pervasives_Native.None ->
              (subj, FStar_Pervasives_Native.None)
          | FStar_Pervasives_Native.Some obj ->
              let v =
                if is_type then cj_type_value obj else cj_json_of_term obj in
              (subj,
                (FStar_Pervasives_Native.Some
                   {
                     cjp_key = key0;
                     cjp_url = has_value_url;
                     cjp_list = false;
                     cjp_vals = [v]
                   }))))
let rec cj_subject_present (s : RDF_Term.subject)
  (rest :
    (RDF_Term.subject * cj_pair FStar_Pervasives_Native.option) Prims.list)
  : Prims.bool=
  match rest with
  | [] -> false
  | (s2, p)::tl ->
      ((RDF_Term.subject_eq s s2) && (FStar_Pervasives_Native.uu___is_Some p))
        || (cj_subject_present s tl)
let rec cj_distinct_subjects (seen : RDF_Term.subject Prims.list)
  (cells :
    (RDF_Term.subject * cj_pair FStar_Pervasives_Native.option) Prims.list)
  : RDF_Term.subject Prims.list=
  match cells with
  | [] -> []
  | (s, p)::tl ->
      if
        (FStar_Pervasives_Native.uu___is_Some p) &&
          (Prims.op_Negation
             (FStar_List_Tot_Base.existsb (fun x -> RDF_Term.subject_eq x s)
                seen))
      then s :: (cj_distinct_subjects (s :: seen) tl)
      else cj_distinct_subjects seen tl
type cj_acc =
  {
  ca_key: Prims.string ;
  ca_url: Prims.bool ;
  ca_forcearr: Prims.bool ;
  ca_vals: Parser_JSON.json_val Prims.list }
let __proj__Mkcj_acc__item__ca_key (projectee : cj_acc) : Prims.string=
  match projectee with | { ca_key; ca_url; ca_forcearr; ca_vals;_} -> ca_key
let __proj__Mkcj_acc__item__ca_url (projectee : cj_acc) : Prims.bool=
  match projectee with | { ca_key; ca_url; ca_forcearr; ca_vals;_} -> ca_url
let __proj__Mkcj_acc__item__ca_forcearr (projectee : cj_acc) : Prims.bool=
  match projectee with
  | { ca_key; ca_url; ca_forcearr; ca_vals;_} -> ca_forcearr
let __proj__Mkcj_acc__item__ca_vals (projectee : cj_acc) :
  Parser_JSON.json_val Prims.list=
  match projectee with | { ca_key; ca_url; ca_forcearr; ca_vals;_} -> ca_vals
let rec cj_acc_find (k : Prims.string) (acc : cj_acc Prims.list) :
  cj_acc FStar_Pervasives_Native.option=
  match acc with
  | [] -> FStar_Pervasives_Native.None
  | a::tl ->
      if a.ca_key = k
      then FStar_Pervasives_Native.Some a
      else cj_acc_find k tl
let rec cj_acc_update (k : Prims.string) (p : cj_pair)
  (acc : cj_acc Prims.list) : cj_acc Prims.list=
  match acc with
  | [] ->
      [{
         ca_key = k;
         ca_url = (p.cjp_url);
         ca_forcearr = (p.cjp_list);
         ca_vals = (p.cjp_vals)
       }]
  | a::tl ->
      if a.ca_key = k
      then
        {
          ca_key = (a.ca_key);
          ca_url = (a.ca_url);
          ca_forcearr = true;
          ca_vals = (FStar_List_Tot_Base.op_At a.ca_vals p.cjp_vals)
        } :: tl
      else a :: (cj_acc_update k p tl)
let rec cj_collect_pairs (subj : RDF_Term.subject)
  (cells :
    (RDF_Term.subject * cj_pair FStar_Pervasives_Native.option) Prims.list)
  (acc : cj_acc Prims.list) : cj_acc Prims.list=
  match cells with
  | [] -> acc
  | (s, p)::tl ->
      (match p with
       | FStar_Pervasives_Native.Some pr ->
           if RDF_Term.subject_eq s subj
           then cj_collect_pairs subj tl (cj_acc_update pr.cjp_key pr acc)
           else cj_collect_pairs subj tl acc
       | FStar_Pervasives_Native.None -> cj_collect_pairs subj tl acc)
let cj_acc_to_pair (a : cj_acc) : (Prims.string * Parser_JSON.json_val)=
  match a.ca_vals with
  | v::[] ->
      if a.ca_forcearr
      then ((a.ca_key), (Parser_JSON.JArray [v]))
      else ((a.ca_key), v)
  | vs -> ((a.ca_key), (Parser_JSON.JArray vs))
type cj_obj =
  {
  co_id: Prims.string FStar_Pervasives_Native.option ;
  co_pairs: (Prims.string * Parser_JSON.json_val) Prims.list ;
  co_urlkeys: Prims.string Prims.list }
let __proj__Mkcj_obj__item__co_id (projectee : cj_obj) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with | { co_id; co_pairs; co_urlkeys;_} -> co_id
let __proj__Mkcj_obj__item__co_pairs (projectee : cj_obj) :
  (Prims.string * Parser_JSON.json_val) Prims.list=
  match projectee with | { co_id; co_pairs; co_urlkeys;_} -> co_pairs
let __proj__Mkcj_obj__item__co_urlkeys (projectee : cj_obj) :
  Prims.string Prims.list=
  match projectee with | { co_id; co_pairs; co_urlkeys;_} -> co_urlkeys
let cj_build_obj (subj : RDF_Term.subject)
  (cells :
    (RDF_Term.subject * cj_pair FStar_Pervasives_Native.option) Prims.list)
  : cj_obj=
  let accs = cj_collect_pairs subj cells [] in
  let id =
    match subj with
    | RDF_Term.S_IRI i -> FStar_Pervasives_Native.Some i
    | RDF_Term.S_BNode uu___ -> FStar_Pervasives_Native.None in
  let pairs = FStar_List_Tot_Base.map cj_acc_to_pair accs in
  let urlkeys =
    FStar_List_Tot_Base.map (fun a -> a.ca_key)
      (FStar_List_Tot_Base.filter (fun a -> a.ca_url) accs) in
  { co_id = id; co_pairs = pairs; co_urlkeys = urlkeys }
let cj_row_objects
  (cells :
    (RDF_Term.subject * cj_pair FStar_Pervasives_Native.option) Prims.list)
  : cj_obj Prims.list=
  let subs = cj_distinct_subjects [] cells in
  FStar_List_Tot_Base.map (fun s -> cj_build_obj s cells) subs
let rec cj_all_url_values (objs : cj_obj Prims.list) :
  Prims.string Prims.list=
  match objs with
  | [] -> []
  | o::tl ->
      FStar_List_Tot_Base.op_At
        (FStar_List_Tot_Base.choose
           (fun kv ->
              let uu___ = kv in
              match uu___ with
              | (k, v) ->
                  if FStar_List_Tot_Base.mem k o.co_urlkeys
                  then
                    (match v with
                     | Parser_JSON.JString s ->
                         FStar_Pervasives_Native.Some s
                     | uu___1 -> FStar_Pervasives_Native.None)
                  else FStar_Pervasives_Native.None) o.co_pairs)
        (cj_all_url_values tl)
let cj_count (x : Prims.string) (xs : Prims.string Prims.list) : Prims.nat=
  FStar_List_Tot_Base.length (FStar_List_Tot_Base.filter (fun y -> y = x) xs)
let rec cj_find_obj_by_id (i : Prims.string) (objs : cj_obj Prims.list) :
  cj_obj FStar_Pervasives_Native.option=
  match objs with
  | [] -> FStar_Pervasives_Native.None
  | o::tl ->
      (match o.co_id with
       | FStar_Pervasives_Native.Some j ->
           if j = i
           then FStar_Pervasives_Native.Some o
           else cj_find_obj_by_id i tl
       | FStar_Pervasives_Native.None -> cj_find_obj_by_id i tl)
let cj_obj_to_json (o : cj_obj) : Parser_JSON.json_val=
  match o.co_id with
  | FStar_Pervasives_Native.Some i ->
      Parser_JSON.JObject (("@id", (Parser_JSON.JString i)) :: (o.co_pairs))
  | FStar_Pervasives_Native.None -> Parser_JSON.JObject (o.co_pairs)
let rec cj_nest_obj (depth : Prims.nat) (urllist : Prims.string Prims.list)
  (all : cj_obj Prims.list) (o : cj_obj) : Parser_JSON.json_val=
  if depth = Prims.int_zero
  then cj_obj_to_json o
  else
    (let pairs' =
       FStar_List_Tot_Base.map
         (fun kv ->
            let uu___1 = kv in
            match uu___1 with
            | (k, v) ->
                if FStar_List_Tot_Base.mem k o.co_urlkeys
                then
                  (match v with
                   | Parser_JSON.JString s ->
                       if FStar_List_Tot_Base.mem s urllist
                       then
                         (match cj_find_obj_by_id s all with
                          | FStar_Pervasives_Native.Some target ->
                              if
                                (match ((target.co_id), (o.co_id)) with
                                 | (FStar_Pervasives_Native.Some a,
                                    FStar_Pervasives_Native.Some b) -> 
                                     a = b
                                 | uu___2 -> false)
                              then (k, v)
                              else
                                (k,
                                  (cj_nest_obj (depth - Prims.int_one)
                                     urllist all target))
                          | FStar_Pervasives_Native.None -> (k, v))
                       else (k, v)
                   | uu___2 -> (k, v))
                else (k, v)) o.co_pairs in
     match o.co_id with
     | FStar_Pervasives_Native.Some i ->
         Parser_JSON.JObject (("@id", (Parser_JSON.JString i)) :: pairs')
     | FStar_Pervasives_Native.None -> Parser_JSON.JObject pairs')
let rec cj_nested_ids (urllist : Prims.string Prims.list)
  (all : cj_obj Prims.list) (objs : cj_obj Prims.list) :
  Prims.string Prims.list=
  match objs with
  | [] -> []
  | o::tl ->
      FStar_List_Tot_Base.op_At
        (FStar_List_Tot_Base.choose
           (fun kv ->
              let uu___ = kv in
              match uu___ with
              | (k, v) ->
                  if FStar_List_Tot_Base.mem k o.co_urlkeys
                  then
                    (match v with
                     | Parser_JSON.JString s ->
                         if
                           ((FStar_List_Tot_Base.mem s urllist) &&
                              (FStar_Pervasives_Native.uu___is_Some
                                 (cj_find_obj_by_id s all)))
                             &&
                             (Prims.op_Negation
                                (match o.co_id with
                                 | FStar_Pervasives_Native.Some b -> b = s
                                 | FStar_Pervasives_Native.None -> false))
                         then FStar_Pervasives_Native.Some s
                         else FStar_Pervasives_Native.None
                     | uu___1 -> FStar_Pervasives_Native.None)
                  else FStar_Pervasives_Native.None) o.co_pairs)
        (cj_nested_ids urllist all tl)
let cj_row_roots
  (cells :
    (RDF_Term.subject * cj_pair FStar_Pervasives_Native.option) Prims.list)
  : Parser_JSON.json_val Prims.list=
  let objs = cj_row_objects cells in
  let allvals = cj_all_url_values objs in
  let urllist =
    FStar_List_Tot_Base.filter
      (fun s -> (cj_count s allvals) = Prims.int_one) allvals in
  let nested = cj_nested_ids urllist objs objs in
  let roots =
    FStar_List_Tot_Base.filter
      (fun o ->
         match o.co_id with
         | FStar_Pervasives_Native.Some i ->
             Prims.op_Negation (FStar_List_Tot_Base.mem i nested)
         | FStar_Pervasives_Native.None -> true) objs in
  FStar_List_Tot_Base.map
    (fun o -> cj_nest_obj (FStar_List_Tot_Base.length objs) urllist objs o)
    roots
let rec cj_assoc (k : Prims.string)
  (fs : (Prims.string * Parser_JSON.json_val) Prims.list) :
  Parser_JSON.json_val FStar_Pervasives_Native.option=
  match fs with
  | [] -> FStar_Pervasives_Native.None
  | (k2, v)::tl ->
      if k2 = k then FStar_Pervasives_Native.Some v else cj_assoc k tl
let rec cj_compact_json (fuel : Prims.nat) (v : Parser_JSON.json_val) :
  Parser_JSON.json_val=
  if fuel = Prims.int_zero
  then v
  else
    (match v with
     | Parser_JSON.JString s -> Parser_JSON.JString (cj_compact_url s)
     | Parser_JSON.JArray xs ->
         Parser_JSON.JArray (cj_map_compact (fuel - Prims.int_one) xs)
     | uu___1 -> v)
and cj_map_compact (fuel : Prims.nat) (xs : Parser_JSON.json_val Prims.list)
  : Parser_JSON.json_val Prims.list=
  if fuel = Prims.int_zero
  then xs
  else
    (match xs with
     | [] -> []
     | x::tl -> (cj_compact_json (fuel - Prims.int_one) x) ::
         (cj_map_compact (fuel - Prims.int_one) tl))
let rec cj_ld_to_json (fuel : Prims.nat) (v : Parser_JSON.json_val) :
  Parser_JSON.json_val=
  if fuel = Prims.int_zero
  then v
  else
    (match v with
     | Parser_JSON.JObject fields ->
         (match cj_assoc "@value" fields with
          | FStar_Pervasives_Native.Some vv -> vv
          | FStar_Pervasives_Native.None ->
              (match cj_assoc "@id" fields with
               | FStar_Pervasives_Native.Some (Parser_JSON.JString s) ->
                   Parser_JSON.JString s
               | FStar_Pervasives_Native.Some other -> other
               | FStar_Pervasives_Native.None ->
                   Parser_JSON.JObject
                     (cj_ld_fields (fuel - Prims.int_one) fields)))
     | Parser_JSON.JArray xs ->
         Parser_JSON.JArray (cj_ld_items (fuel - Prims.int_one) xs)
     | uu___1 -> v)
and cj_ld_fields (fuel : Prims.nat)
  (fs : (Prims.string * Parser_JSON.json_val) Prims.list) :
  (Prims.string * Parser_JSON.json_val) Prims.list=
  if fuel = Prims.int_zero
  then fs
  else
    (match fs with
     | [] -> []
     | (k, x)::tl ->
         let x' =
           if k = "@type"
           then cj_compact_json (Parser_JSON.json_size x) x
           else cj_ld_to_json (fuel - Prims.int_one) x in
         (k, x') :: (cj_ld_fields (fuel - Prims.int_one) tl))
and cj_ld_items (fuel : Prims.nat) (xs : Parser_JSON.json_val Prims.list) :
  Parser_JSON.json_val Prims.list=
  if fuel = Prims.int_zero
  then xs
  else
    (match xs with
     | [] -> []
     | x::tl -> (cj_ld_to_json (fuel - Prims.int_one) x) ::
         (cj_ld_items (fuel - Prims.int_one) tl))
let cj_common_pairs
  (common : (Prims.string * Parser_JSON.json_val) Prims.list) :
  (Prims.string * Parser_JSON.json_val) Prims.list=
  FStar_List_Tot_Base.map
    (fun kv ->
       let uu___ = kv in
       match uu___ with
       | (k, v) ->
           ((cj_compact_url (CSVW_Conversion.csvw_expand_curie k)),
             (cj_ld_to_json ((Parser_JSON.json_size v) + Prims.int_one) v)))
    common
let cj_table_id_pairs (base_iri : Prims.string)
  (doc_url : Prims.string FStar_Pervasives_Native.option)
  (tbl : CSVW_Metadata.csvw_table) :
  (Prims.string * Parser_JSON.json_val) Prims.list=
  match tbl.CSVW_Metadata.tbl_id with
  | CSVW_Metadata.CsvwIdString s ->
      let r = RDF_IRI.resolve_iri_v2 base_iri s in
      if RDF_Term.is_iri r then [("@id", (Parser_JSON.JString r))] else []
  | CSVW_Metadata.CsvwIdInvalid ->
      (match doc_url with
       | FStar_Pervasives_Native.Some u ->
           if RDF_Term.is_iri u
           then [("@id", (Parser_JSON.JString u))]
           else []
       | FStar_Pervasives_Native.None -> [])
  | CSVW_Metadata.CsvwIdNone -> []
let cj_notes_pairs (notes : Parser_JSON.json_val Prims.list) :
  (Prims.string * Parser_JSON.json_val) Prims.list=
  match notes with
  | [] -> []
  | uu___ ->
      [("notes",
         (Parser_JSON.JArray
            (FStar_List_Tot_Base.map
               (fun n ->
                  cj_ld_to_json ((Parser_JSON.json_size n) + Prims.int_one) n)
               notes)))]
let cj_row_cells (table_url_resolved : Prims.string)
  (col_specs : CSVW_Conversion.csvw_col_spec Prims.list)
  (row_num : Prims.nat) (source_row_num : Prims.nat)
  (cells : Prims.string Prims.list) :
  (RDF_Term.subject * cj_pair FStar_Pervasives_Native.option) Prims.list=
  let phys_specs =
    FStar_List_Tot_Base.filter
      (fun s -> Prims.op_Negation s.CSVW_Conversion.cs_virtual) col_specs in
  let virt_specs =
    FStar_List_Tot_Base.filter (fun s -> s.CSVW_Conversion.cs_virtual)
      col_specs in
  let phys_pairs = CSVW_Conversion.csvw_zip_specs_cells phys_specs cells in
  let phys_bindings =
    FStar_List_Tot_Base.map
      (fun p ->
         (((FStar_Pervasives_Native.fst p).CSVW_Conversion.cs_name),
           (FStar_Pervasives_Native.snd p))) phys_pairs in
  let base_lookup =
    CSVW_Conversion.csvw_row_lookup phys_bindings row_num source_row_num in
  let default_subject =
    RDF_Term.S_BNode
      (Prims.strcat "cjrow_" (Prims.string_of_int source_row_num)) in
  let cur spec v =
    if v = "_name"
    then FStar_Pervasives_Native.Some (spec.CSVW_Conversion.cs_name)
    else base_lookup v in
  FStar_List_Tot_Base.op_At
    (FStar_List_Tot_Base.map
       (fun p ->
          cj_process_cell table_url_resolved
            (cur (FStar_Pervasives_Native.fst p)) default_subject
            (FStar_Pervasives_Native.fst p)
            (FStar_Pervasives_Native.Some (FStar_Pervasives_Native.snd p)))
       phys_pairs)
    (FStar_List_Tot_Base.map
       (fun s ->
          cj_process_cell table_url_resolved (cur s) default_subject s
            FStar_Pervasives_Native.None) virt_specs)
let cj_row_titles (col_specs : CSVW_Conversion.csvw_col_spec Prims.list)
  (cells : Prims.string Prims.list) (row_titles : Prims.string Prims.list) :
  (Prims.string * Parser_JSON.json_val) Prims.list=
  let phys_specs =
    FStar_List_Tot_Base.filter
      (fun s -> Prims.op_Negation s.CSVW_Conversion.cs_virtual) col_specs in
  let phys_pairs = CSVW_Conversion.csvw_zip_specs_cells phys_specs cells in
  let bindings =
    FStar_List_Tot_Base.map
      (fun p ->
         (((FStar_Pervasives_Native.fst p).CSVW_Conversion.cs_name),
           (FStar_Pervasives_Native.snd p))) phys_pairs in
  let vals =
    FStar_List_Tot_Base.choose
      (fun name ->
         match FStar_List_Tot_Base.assoc name bindings with
         | FStar_Pervasives_Native.Some txt ->
             FStar_Pervasives_Native.Some (Parser_JSON.JString txt)
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
      row_titles in
  match vals with
  | [] -> []
  | v::[] -> [("titles", v)]
  | uu___ -> [("titles", (Parser_JSON.JArray vals))]
let cj_row_json_standard (table_url_resolved : Prims.string)
  (col_specs : CSVW_Conversion.csvw_col_spec Prims.list)
  (row_titles : Prims.string Prims.list) (row_num : Prims.nat)
  (source_row_num : Prims.nat) (cells : Prims.string Prims.list) :
  Parser_JSON.json_val=
  let row_cells =
    cj_row_cells table_url_resolved col_specs row_num source_row_num cells in
  let roots = cj_row_roots row_cells in
  let row_url =
    CSVW_Conversion.csvw_row_url table_url_resolved source_row_num in
  Parser_JSON.JObject
    (FStar_List_Tot_Base.op_At
       [("url", (Parser_JSON.JString row_url));
       ("rownum", (Parser_JSON.JNumber (Prims.string_of_int row_num)))]
       (FStar_List_Tot_Base.op_At (cj_row_titles col_specs cells row_titles)
          [("describes", (Parser_JSON.JArray roots))]))
let cj_comment_pairs (comments : Prims.string Prims.list) :
  (Prims.string * Parser_JSON.json_val) Prims.list=
  match comments with
  | [] -> []
  | uu___ ->
      [("rdfs:comment",
         (Parser_JSON.JArray
            (FStar_List_Tot_Base.map (fun c -> Parser_JSON.JString c)
               comments)))]
let cj_table_rows (grp_inherited : CSVW_Metadata.csvw_inherited_props)
  (base_iri : Prims.string) (fallback_url : Prims.string)
  (tbl : CSVW_Metadata.csvw_table)
  (all_rows : Prims.string Prims.list Prims.list) :
  (Prims.string * Parser_JSON.json_val Prims.list * Parser_JSON.json_val
    Prims.list * Prims.string Prims.list)=
  let table_url_resolved =
    CSVW_Conversion.csvw_effective_table_url base_iri fallback_url tbl in
  let dia = tbl.CSVW_Metadata.tbl_dialect in
  let skip_cols_n = CSVW_Conversion.csvw_skip_columns_count dia in
  let uu___ = CSVW_Conversion.csvw_classify_table_rows dia all_rows in
  match uu___ with
  | (comments, header_row_opt, data_entries) ->
      let header_cells_raw =
        match header_row_opt with
        | FStar_Pervasives_Native.Some h -> h
        | FStar_Pervasives_Native.None ->
            (match tbl.CSVW_Metadata.tbl_table_schema with
             | FStar_Pervasives_Native.Some uu___1 -> []
             | FStar_Pervasives_Native.None ->
                 (match data_entries with
                  | (uu___1, uu___2, r)::uu___3 ->
                      FStar_List_Tot_Base.map (fun uu___4 -> "") r
                  | [] -> [])) in
      let header_cells =
        CSVW_Conversion.csvw_drop skip_cols_n header_cells_raw in
      let col_specs =
        CSVW_Conversion.csvw_build_col_specs grp_inherited
          tbl.CSVW_Metadata.tbl_inherited tbl.CSVW_Metadata.tbl_table_schema
          header_cells in
      let row_titles =
        match tbl.CSVW_Metadata.tbl_table_schema with
        | FStar_Pervasives_Native.Some ts -> ts.CSVW_Metadata.ts_row_titles
        | FStar_Pervasives_Native.None -> [] in
      let std_rows =
        FStar_List_Tot_Base.map
          (fun p ->
             let uu___1 = p in
             match uu___1 with
             | (row_num, source_row_num, raw_cells) ->
                 cj_row_json_standard table_url_resolved col_specs row_titles
                   row_num source_row_num
                   (CSVW_Conversion.csvw_drop skip_cols_n raw_cells))
          data_entries in
      let min_roots =
        FStar_List_Tot_Base.collect
          (fun p ->
             let uu___1 = p in
             match uu___1 with
             | (row_num, source_row_num, raw_cells) ->
                 let row_cells =
                   cj_row_cells table_url_resolved col_specs row_num
                     source_row_num
                     (CSVW_Conversion.csvw_drop skip_cols_n raw_cells) in
                 cj_row_roots row_cells) data_entries in
      (table_url_resolved, std_rows, min_roots, comments)
let cj_document_json_minimal
  (grp_inherited : CSVW_Metadata.csvw_inherited_props)
  (base_iri : Prims.string)
  (tables_with_rows :
    (CSVW_Metadata.csvw_table * Prims.string * Prims.string Prims.list
      Prims.list) Prims.list)
  : Parser_JSON.json_val=
  Parser_JSON.JArray
    (FStar_List_Tot_Base.collect
       (fun t ->
          let uu___ = t in
          match uu___ with
          | (tbl, fallback_url, rows) ->
              if CSVW_Conversion.csvw_table_suppressed tbl
              then []
              else
                (let uu___2 =
                   cj_table_rows grp_inherited base_iri fallback_url tbl rows in
                 match uu___2 with | (uu___3, uu___4, mins, uu___5) -> mins))
       tables_with_rows)
let cj_document_json_standard (grp : CSVW_Metadata.csvw_group_meta)
  (doc_url : Prims.string FStar_Pervasives_Native.option)
  (base_iri : Prims.string)
  (tables_with_rows :
    (CSVW_Metadata.csvw_table * Prims.string * Prims.string Prims.list
      Prims.list) Prims.list)
  : Parser_JSON.json_val=
  let tables =
    FStar_List_Tot_Base.map
      (fun t ->
         let uu___ = t in
         match uu___ with
         | (tbl, fallback_url, rows) ->
             let uu___1 =
               cj_table_rows grp.CSVW_Metadata.grp_inherited base_iri
                 fallback_url tbl rows in
             (match uu___1 with
              | (turl, std_rows, uu___2, comments) ->
                  Parser_JSON.JObject
                    (FStar_List_Tot_Base.op_At
                       (cj_table_id_pairs base_iri doc_url tbl)
                       (FStar_List_Tot_Base.op_At
                          [("url", (Parser_JSON.JString turl))]
                          (FStar_List_Tot_Base.op_At
                             (cj_common_pairs tbl.CSVW_Metadata.tbl_common)
                             (FStar_List_Tot_Base.op_At
                                (cj_notes_pairs tbl.CSVW_Metadata.tbl_notes)
                                (FStar_List_Tot_Base.op_At
                                   [("row", (Parser_JSON.JArray std_rows))]
                                   (cj_comment_pairs comments))))))))
      (FStar_List_Tot_Base.filter
         (fun t ->
            let uu___ = t in
            match uu___ with
            | (tbl, uu___1, uu___2) ->
                Prims.op_Negation (CSVW_Conversion.csvw_table_suppressed tbl))
         tables_with_rows) in
  Parser_JSON.JObject
    (FStar_List_Tot_Base.op_At (cj_common_pairs grp.CSVW_Metadata.grp_common)
       [("tables", (Parser_JSON.JArray tables))])
