open Prims
let is_iunreserved (c : FStar_Char.char) : Prims.bool=
  let code = FStar_Char.int_of_char c in
  (((((((((((((((((SPARQL11_Algebra.is_uri_unreserved c) ||
                    ((code >= (Prims.of_int (0xA0))) &&
                       (code <= (Prims.of_int (0xD7FF)))))
                   ||
                   ((code >= (Prims.of_int (0xF900))) &&
                      (code <= (Prims.of_int (0xFDCF)))))
                  ||
                  ((code >= (Prims.of_int (0xFDF0))) &&
                     (code <= (Prims.of_int (0xFFEF)))))
                 ||
                 ((code >= (Prims.parse_int "0x10000")) &&
                    (code <= (Prims.parse_int "0x1FFFD"))))
                ||
                ((code >= (Prims.parse_int "0x20000")) &&
                   (code <= (Prims.parse_int "0x2FFFD"))))
               ||
               ((code >= (Prims.parse_int "0x30000")) &&
                  (code <= (Prims.parse_int "0x3FFFD"))))
              ||
              ((code >= (Prims.parse_int "0x40000")) &&
                 (code <= (Prims.parse_int "0x4FFFD"))))
             ||
             ((code >= (Prims.parse_int "0x50000")) &&
                (code <= (Prims.parse_int "0x5FFFD"))))
            ||
            ((code >= (Prims.parse_int "0x60000")) &&
               (code <= (Prims.parse_int "0x6FFFD"))))
           ||
           ((code >= (Prims.parse_int "0x70000")) &&
              (code <= (Prims.parse_int "0x7FFFD"))))
          ||
          ((code >= (Prims.parse_int "0x80000")) &&
             (code <= (Prims.parse_int "0x8FFFD"))))
         ||
         ((code >= (Prims.parse_int "0x90000")) &&
            (code <= (Prims.parse_int "0x9FFFD"))))
        ||
        ((code >= (Prims.parse_int "0xA0000")) &&
           (code <= (Prims.parse_int "0xAFFFD"))))
       ||
       ((code >= (Prims.parse_int "0xB0000")) &&
          (code <= (Prims.parse_int "0xBFFFD"))))
      ||
      ((code >= (Prims.parse_int "0xC0000")) &&
         (code <= (Prims.parse_int "0xCFFFD"))))
     ||
     ((code >= (Prims.parse_int "0xD0000")) &&
        (code <= (Prims.parse_int "0xDFFFD"))))
    ||
    ((code >= (Prims.parse_int "0xE1000")) &&
       (code <= (Prims.parse_int "0xEFFFD")))
let rec encode_iri_chars (cs : FStar_Char.char Prims.list) :
  FStar_Char.char Prims.list=
  match cs with
  | [] -> []
  | c::rest ->
      if is_iunreserved c
      then c :: (encode_iri_chars rest)
      else
        FStar_List_Tot_Base.append (SPARQL11_Algebra.percent_encode_char c)
          (encode_iri_chars rest)
let string_encode_iri (s : Prims.string) : Prims.string=
  FStar_String.string_of_list
    (encode_iri_chars (FStar_String.list_of_string s))
let is_frac_or_exp_marker (c : FStar_Char.char) : Prims.bool=
  let i = FStar_Char.int_of_char c in
  ((i = (Prims.of_int (0x2E))) || (i = (Prims.of_int (0x65)))) ||
    (i = (Prims.of_int (0x45)))
let json_number_natural_datatype (lex : Prims.string) :
  RDF_Graph_Executable.wf_iri=
  if
    FStar_List_Tot_Base.existsb is_frac_or_exp_marker
      (FStar_String.list_of_string lex)
  then RDF_Graph_Executable.xsd_double
  else RDF_Graph_Executable.xsd_integer
let json_natural_value (v : Parser_JSON.json_val) :
  (Prims.string * RDF_Graph_Executable.wf_iri) FStar_Pervasives_Native.option=
  match v with
  | Parser_JSON.JString s ->
      FStar_Pervasives_Native.Some (s, RDF_Graph_Executable.xsd_string)
  | Parser_JSON.JNumber s ->
      FStar_Pervasives_Native.Some (s, (json_number_natural_datatype s))
  | Parser_JSON.JBool b ->
      FStar_Pervasives_Native.Some
        ((if b then "true" else "false"), RDF_Graph_Executable.xsd_boolean)
  | Parser_JSON.JNull -> FStar_Pervasives_Native.None
  | Parser_JSON.JArray uu___ -> FStar_Pervasives_Native.None
  | Parser_JSON.JObject uu___ -> FStar_Pervasives_Native.None
let json_natural_cast_string (v : Parser_JSON.json_val) :
  Prims.string FStar_Pervasives_Native.option=
  match json_natural_value v with
  | FStar_Pervasives_Native.Some (s, uu___) -> FStar_Pervasives_Native.Some s
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
let reference_natural_values (row : RML_Sources.source_row)
  (path : Prims.string) :
  (Prims.string * RDF_Graph_Executable.wf_iri) Prims.list=
  match row with
  | RML_Sources.Row_JSON uu___ ->
      FStar_List_Tot_Base.concatMap
        (fun v ->
           match json_natural_value v with
           | FStar_Pervasives_Native.Some p -> [p]
           | FStar_Pervasives_Native.None -> [])
        (RML_Sources.json_reference_values row path)
  | RML_Sources.Row_CSV uu___ ->
      FStar_List_Tot_Base.map (fun v -> (v, RDF_Graph_Executable.xsd_string))
        (RML_Sources.csv_reference_values row path)
let reference_cast_strings (row : RML_Sources.source_row)
  (path : Prims.string) : Prims.string Prims.list=
  FStar_List_Tot_Base.map FStar_Pervasives_Native.fst
    (reference_natural_values row path)
let rec build_template_product
  (segs : RML_Mapping.template_segment Prims.list)
  (encode : (Prims.string -> Prims.string) FStar_Pervasives_Native.option)
  (row : RML_Sources.source_row) : Prims.string Prims.list=
  match segs with
  | [] -> [""]
  | (RML_Mapping.TSeg_Literal l)::rest ->
      let tails = build_template_product rest encode row in
      FStar_List_Tot_Base.map (fun t -> Prims.strcat l t) tails
  | (RML_Mapping.TSeg_Reference r)::rest ->
      let vals = reference_cast_strings row r in
      let vals_enc =
        match encode with
        | FStar_Pervasives_Native.Some f -> FStar_List_Tot_Base.map f vals
        | FStar_Pervasives_Native.None -> vals in
      let tails = build_template_product rest encode row in
      FStar_List_Tot_Base.concatMap
        (fun v -> FStar_List_Tot_Base.map (fun t -> Prims.strcat v t) tails)
        vals_enc
let eval_template_strings
  (encode : (Prims.string -> Prims.string) FStar_Pervasives_Native.option)
  (raw : Prims.string) (row : RML_Sources.source_row) :
  Prims.string Prims.list=
  build_template_product (RML_Mapping.parse_template raw) encode row
type map_role =
  | MR_Subject 
  | MR_Predicate 
  | MR_Graph 
  | MR_Object 
let uu___is_MR_Subject (projectee : map_role) : Prims.bool=
  match projectee with | MR_Subject -> true | uu___ -> false
let uu___is_MR_Predicate (projectee : map_role) : Prims.bool=
  match projectee with | MR_Predicate -> true | uu___ -> false
let uu___is_MR_Graph (projectee : map_role) : Prims.bool=
  match projectee with | MR_Graph -> true | uu___ -> false
let uu___is_MR_Object (projectee : map_role) : Prims.bool=
  match projectee with | MR_Object -> true | uu___ -> false
let is_reference_form (form : RML_Mapping.term_map_form) : Prims.bool=
  match form with | RML_Mapping.TMF_Reference uu___ -> true | uu___ -> false
let effective_term_type (role : map_role) (tm : RML_Mapping.term_map) :
  RML_Mapping.term_type=
  match tm.RML_Mapping.tmap_termtype with
  | FStar_Pervasives_Native.Some tt -> tt
  | FStar_Pervasives_Native.None ->
      (match role with
       | MR_Subject -> RML_Mapping.TT_IRI
       | MR_Predicate -> RML_Mapping.TT_IRI
       | MR_Graph -> RML_Mapping.TT_IRI
       | MR_Object ->
           if
             ((is_reference_form tm.RML_Mapping.tmap_form) ||
                (FStar_Pervasives_Native.uu___is_Some
                   tm.RML_Mapping.tmap_datatype))
               ||
               (FStar_Pervasives_Native.uu___is_Some
                  tm.RML_Mapping.tmap_language)
           then RML_Mapping.TT_Literal
           else RML_Mapping.TT_IRI)
let rml_forbidden_iri_byte (b : Prims.int) : Prims.bool=
  ((((((((((b >= Prims.int_zero) && (b <= (Prims.of_int (0x20)))) ||
            (b = (Prims.of_int (0x3C))))
           || (b = (Prims.of_int (0x3E))))
          || (b = (Prims.of_int (0x22))))
         || (b = (Prims.of_int (0x7B))))
        || (b = (Prims.of_int (0x7D))))
       || (b = (Prims.of_int (0x7C))))
      || (b = (Prims.of_int (0x5C))))
     || (b = (Prims.of_int (0x5E))))
    || (b = (Prims.of_int (0x60)))
let rec rml_iri_scan_wf (s : Prims.string) (pos : Prims.nat)
  (fuel : Prims.nat) : Prims.bool=
  if fuel = Prims.int_zero
  then true
  else
    (let len = FStar_String.strlen s in
     if pos >= len
     then true
     else
       if
         rml_forbidden_iri_byte
           (FStar_Char.int_of_char (FStar_String.index s pos))
       then false
       else rml_iri_scan_wf s (pos + Prims.int_one) (fuel - Prims.int_one))
let rml_is_valid_absolute_iri (s : Prims.string) : Prims.bool=
  (RDF_Graph_Executable.is_iri s) &&
    (rml_iri_scan_wf s Prims.int_zero
       ((FStar_String.strlen s) + Prims.int_one))
let iri_like_term_gated (strict : Prims.bool) (value : Prims.string)
  (base_iri : Prims.string FStar_Pervasives_Native.option) :
  RDF_Graph_Executable.rdf_term FStar_Pervasives_Native.option=
  let ok s =
    if strict
    then rml_is_valid_absolute_iri s
    else RDF_Graph_Executable.is_iri s in
  if ok value
  then FStar_Pervasives_Native.Some (RDF_Graph_Executable.T_IRI value)
  else
    (match base_iri with
     | FStar_Pervasives_Native.Some b ->
         let combined = Prims.strcat b value in
         if ok combined
         then
           FStar_Pervasives_Native.Some (RDF_Graph_Executable.T_IRI combined)
         else FStar_Pervasives_Native.None
     | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
let iri_like_term (value : Prims.string)
  (base_iri : Prims.string FStar_Pervasives_Native.option) :
  RDF_Graph_Executable.rdf_term FStar_Pervasives_Native.option=
  iri_like_term_gated true value base_iri
let eval_plain_strings (tm : RML_Mapping.term_map)
  (row : RML_Sources.source_row) : Prims.string Prims.list=
  match tm.RML_Mapping.tmap_form with
  | RML_Mapping.TMF_Constant t ->
      (match t with
       | RDF_Graph_Executable.T_IRI i -> [i]
       | RDF_Graph_Executable.T_Literal l ->
           [l.RDF_Graph_Executable.lexical_form]
       | RDF_Graph_Executable.T_BNode uu___ -> [])
  | RML_Mapping.TMF_Reference r -> reference_cast_strings row r
  | RML_Mapping.TMF_Template t ->
      eval_template_strings FStar_Pervasives_Native.None t row
  | RML_Mapping.TMF_Unknown -> []
let build_literal_opt (lex : Prims.string) (dt : Prims.string)
  (lang : Prims.string FStar_Pervasives_Native.option) :
  RDF_Graph_Executable.rdf_term FStar_Pervasives_Native.option=
  if RDF_Graph_Executable.is_iri dt
  then
    let l =
      {
        RDF_Graph_Executable.lexical_form = lex;
        RDF_Graph_Executable.datatype = dt;
        RDF_Graph_Executable.lang_tag = lang
      } in
    (if RDF_Graph_Executable.literal_wf l
     then FStar_Pervasives_Native.Some (RDF_Graph_Executable.T_Literal l)
     else FStar_Pervasives_Native.None)
  else FStar_Pervasives_Native.None
let eval_iri_valued_strings (tm : RML_Mapping.term_map)
  (row : RML_Sources.source_row)
  (base_iri : Prims.string FStar_Pervasives_Native.option) :
  Prims.string Prims.list=
  let resolve s =
    match iri_like_term s base_iri with
    | FStar_Pervasives_Native.Some (RDF_Graph_Executable.T_IRI i) -> [i]
    | uu___ -> [] in
  match tm.RML_Mapping.tmap_form with
  | RML_Mapping.TMF_Constant t ->
      (match t with | RDF_Graph_Executable.T_IRI i -> [i] | uu___ -> [])
  | RML_Mapping.TMF_Reference r ->
      FStar_List_Tot_Base.concatMap resolve (reference_cast_strings row r)
  | RML_Mapping.TMF_Template t ->
      FStar_List_Tot_Base.concatMap resolve
        (eval_template_strings
           (FStar_Pervasives_Native.Some string_encode_iri) t row)
  | RML_Mapping.TMF_Unknown -> []
let is_ascii_alpha (c : FStar_Char.char) : Prims.bool=
  let i = FStar_Char.int_of_char c in
  ((i >= (Prims.of_int (0x41))) && (i <= (Prims.of_int (0x5A)))) ||
    ((i >= (Prims.of_int (0x61))) && (i <= (Prims.of_int (0x7A))))
let rec all_ascii_alpha (cs : FStar_Char.char Prims.list) : Prims.bool=
  match cs with
  | [] -> true
  | c::rest -> (is_ascii_alpha c) && (all_ascii_alpha rest)
let rec find_hyphen (s : Prims.string) (pos : Prims.nat) (fuel : Prims.nat) :
  Prims.nat FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (let len = FStar_String.strlen s in
     if pos >= len
     then FStar_Pervasives_Native.None
     else
       if
         (FStar_Char.int_of_char (FStar_String.index s pos)) =
           (Prims.of_int (0x2D))
       then FStar_Pervasives_Native.Some pos
       else find_hyphen s (pos + Prims.int_one) (fuel - Prims.int_one))
let rml_lang_tag_wf (s : Prims.string) : Prims.bool=
  let len = FStar_String.strlen s in
  if len = Prims.int_zero
  then false
  else
    (let first =
       match find_hyphen s Prims.int_zero (len + Prims.int_one) with
       | FStar_Pervasives_Native.Some i ->
           FStar_String.sub s Prims.int_zero i
       | FStar_Pervasives_Native.None -> s in
     let flen = FStar_String.strlen first in
     (all_ascii_alpha (FStar_String.list_of_string first)) &&
       (((flen = Prims.int_one) &&
           ((((first = "i") || (first = "I")) || (first = "x")) ||
              (first = "X")))
          || ((flen >= (Prims.of_int (2))) && (flen <= (Prims.of_int (8))))))
let literal_terms_for_base (tm : RML_Mapping.term_map)
  (row : RML_Sources.source_row)
  (base_iri : Prims.string FStar_Pervasives_Native.option)
  (natural_dt : RDF_Graph_Executable.wf_iri) (lex : Prims.string) :
  RDF_Graph_Executable.rdf_term Prims.list=
  match tm.RML_Mapping.tmap_language with
  | FStar_Pervasives_Native.Some lang_tm ->
      FStar_List_Tot_Base.concatMap
        (fun lang ->
           if rml_lang_tag_wf lang
           then
             match build_literal_opt lex RDF_Graph_Executable.rdf_lang_string
                     (FStar_Pervasives_Native.Some lang)
             with
             | FStar_Pervasives_Native.Some t -> [t]
             | FStar_Pervasives_Native.None -> []
           else []) (eval_plain_strings lang_tm row)
  | FStar_Pervasives_Native.None ->
      (match tm.RML_Mapping.tmap_datatype with
       | FStar_Pervasives_Native.Some dt_tm ->
           FStar_List_Tot_Base.concatMap
             (fun dt ->
                match build_literal_opt lex dt FStar_Pervasives_Native.None
                with
                | FStar_Pervasives_Native.Some t -> [t]
                | FStar_Pervasives_Native.None -> [])
             (eval_iri_valued_strings dt_tm row base_iri)
       | FStar_Pervasives_Native.None ->
           (match build_literal_opt lex natural_dt
                    FStar_Pervasives_Native.None
            with
            | FStar_Pervasives_Native.Some t -> [t]
            | FStar_Pervasives_Native.None -> []))
type resolved_value =
  | RV_Value of Prims.string * RDF_Graph_Executable.wf_iri 
  | RV_String of Prims.string 
let uu___is_RV_Value (projectee : resolved_value) : Prims.bool=
  match projectee with | RV_Value (_0, _1) -> true | uu___ -> false
let __proj__RV_Value__item___0 (projectee : resolved_value) : Prims.string=
  match projectee with | RV_Value (_0, _1) -> _0
let __proj__RV_Value__item___1 (projectee : resolved_value) :
  RDF_Graph_Executable.wf_iri= match projectee with | RV_Value (_0, _1) -> _1
let uu___is_RV_String (projectee : resolved_value) : Prims.bool=
  match projectee with | RV_String _0 -> true | uu___ -> false
let __proj__RV_String__item___0 (projectee : resolved_value) : Prims.string=
  match projectee with | RV_String _0 -> _0
let resolved_value_natural (rv : resolved_value) :
  (Prims.string * RDF_Graph_Executable.wf_iri) FStar_Pervasives_Native.option=
  match rv with
  | RV_Value (s, dt) -> FStar_Pervasives_Native.Some (s, dt)
  | RV_String s ->
      FStar_Pervasives_Native.Some (s, RDF_Graph_Executable.xsd_string)
let finalize_value (tt : RML_Mapping.term_type) (tm : RML_Mapping.term_map)
  (row : RML_Sources.source_row)
  (base_iri : Prims.string FStar_Pervasives_Native.option)
  (rv : resolved_value) : RDF_Graph_Executable.rdf_term Prims.list=
  match resolved_value_natural rv with
  | FStar_Pervasives_Native.None -> []
  | FStar_Pervasives_Native.Some (s, dt) ->
      (match tt with
       | RML_Mapping.TT_IRI ->
           (match iri_like_term s base_iri with
            | FStar_Pervasives_Native.Some t -> [t]
            | FStar_Pervasives_Native.None -> [])
       | RML_Mapping.TT_URI ->
           (match iri_like_term s base_iri with
            | FStar_Pervasives_Native.Some t -> [t]
            | FStar_Pervasives_Native.None -> [])
       | RML_Mapping.TT_UnsafeIRI ->
           (match iri_like_term_gated false s base_iri with
            | FStar_Pervasives_Native.Some t -> [t]
            | FStar_Pervasives_Native.None -> [])
       | RML_Mapping.TT_BlankNode -> [RDF_Graph_Executable.T_BNode s]
       | RML_Mapping.TT_Literal ->
           literal_terms_for_base tm row base_iri dt s)
let eval_term_map (role : map_role) (tm : RML_Mapping.term_map)
  (row : RML_Sources.source_row) (row_seed : Prims.string)
  (base_iri : Prims.string FStar_Pervasives_Native.option) :
  RDF_Graph_Executable.rdf_term Prims.list=
  match tm.RML_Mapping.tmap_form with
  | RML_Mapping.TMF_Constant t ->
      (match t with
       | RDF_Graph_Executable.T_IRI uu___ -> [t]
       | RDF_Graph_Executable.T_Literal uu___ -> [t]
       | RDF_Graph_Executable.T_BNode uu___ -> [])
  | RML_Mapping.TMF_Unknown ->
      (match tm.RML_Mapping.tmap_termtype with
       | FStar_Pervasives_Native.Some (RML_Mapping.TT_BlankNode) ->
           [RDF_Graph_Executable.T_BNode row_seed]
       | uu___ -> [])
  | RML_Mapping.TMF_Reference r ->
      let tt = effective_term_type role tm in
      let leaves = reference_natural_values row r in
      FStar_List_Tot_Base.concatMap
        (fun uu___ ->
           match uu___ with
           | (s, dt) -> finalize_value tt tm row base_iri (RV_Value (s, dt)))
        leaves
  | RML_Mapping.TMF_Template t ->
      let tt = effective_term_type role tm in
      let encode =
        match tt with
        | RML_Mapping.TT_IRI ->
            FStar_Pervasives_Native.Some string_encode_iri
        | RML_Mapping.TT_URI ->
            FStar_Pervasives_Native.Some SPARQL11_Algebra.string_encode_uri
        | uu___ -> FStar_Pervasives_Native.None in
      let strs = eval_template_strings encode t row in
      FStar_List_Tot_Base.concatMap
        (fun s -> finalize_value tt tm row base_iri (RV_String s)) strs
let list_nonempty (l : 'a Prims.list) : Prims.bool=
  match l with | [] -> false | uu___ -> true
let subject_of_rdf_term (t : RDF_Graph_Executable.rdf_term) :
  RDF_Graph_Executable.subject FStar_Pervasives_Native.option=
  match t with
  | RDF_Graph_Executable.T_IRI i ->
      FStar_Pervasives_Native.Some (RDF_Graph_Executable.S_IRI i)
  | RDF_Graph_Executable.T_BNode b ->
      FStar_Pervasives_Native.Some (RDF_Graph_Executable.S_BNode b)
  | RDF_Graph_Executable.T_Literal uu___ -> FStar_Pervasives_Native.None
let term_to_graph_name (t : RDF_Graph_Executable.rdf_term) :
  Prims.string FStar_Pervasives_Native.option=
  match t with
  | RDF_Graph_Executable.T_IRI i -> FStar_Pervasives_Native.Some i
  | RDF_Graph_Executable.T_BNode b ->
      FStar_Pervasives_Native.Some (Prims.strcat "_:" b)
  | RDF_Graph_Executable.T_Literal uu___ -> FStar_Pervasives_Native.None
let eval_graphs (gms : RML_Mapping.term_map Prims.list)
  (row : RML_Sources.source_row) (row_seed : Prims.string)
  (base_iri : Prims.string FStar_Pervasives_Native.option) :
  Prims.string Prims.list=
  FStar_List_Tot_Base.concatMap
    (fun g ->
       FStar_List_Tot_Base.concatMap
         (fun t ->
            match term_to_graph_name t with
            | FStar_Pervasives_Native.Some n -> [n]
            | FStar_Pervasives_Native.None -> [])
         (eval_term_map MR_Graph g row row_seed base_iri)) gms
type placed_triple =
  {
  pt_triple: RDF_Graph_Executable.triple ;
  pt_graphs: Prims.string Prims.list ;
  pt_drop: Prims.bool }
let __proj__Mkplaced_triple__item__pt_triple (projectee : placed_triple) :
  RDF_Graph_Executable.triple=
  match projectee with | { pt_triple; pt_graphs; pt_drop;_} -> pt_triple
let __proj__Mkplaced_triple__item__pt_graphs (projectee : placed_triple) :
  Prims.string Prims.list=
  match projectee with | { pt_triple; pt_graphs; pt_drop;_} -> pt_graphs
let __proj__Mkplaced_triple__item__pt_drop (projectee : placed_triple) :
  Prims.bool=
  match projectee with | { pt_triple; pt_graphs; pt_drop;_} -> pt_drop
let eval_pom (row : RML_Sources.source_row) (row_seed : Prims.string)
  (base_iri : Prims.string FStar_Pervasives_Native.option)
  (pom : RML_Mapping.predicate_object_map) :
  (RDF_Graph_Executable.rdf_term Prims.list * RDF_Graph_Executable.rdf_term
    Prims.list * Prims.string Prims.list)=
  let predicates =
    FStar_List_Tot_Base.concatMap
      (fun p -> eval_term_map MR_Predicate p row row_seed base_iri)
      pom.RML_Mapping.pom_predicates in
  let objects =
    FStar_List_Tot_Base.concatMap
      (fun ob ->
         match ob with
         | RML_Mapping.OB_TermMap tm ->
             eval_term_map MR_Object tm row row_seed base_iri
         | RML_Mapping.OB_Join uu___ -> []) pom.RML_Mapping.pom_objects in
  let graphs = eval_graphs pom.RML_Mapping.pom_graphs row row_seed base_iri in
  (predicates, objects, graphs)
let placed_triples_for_pom (subj : RDF_Graph_Executable.subject)
  (subject_graphs : Prims.string Prims.list) (has_sgm : Prims.bool)
  (row : RML_Sources.source_row) (row_seed : Prims.string)
  (base_iri : Prims.string FStar_Pervasives_Native.option)
  (pom : RML_Mapping.predicate_object_map) : placed_triple Prims.list=
  let uu___ = eval_pom row row_seed base_iri pom in
  match uu___ with
  | (predicates, objects, pog) ->
      let has_pogm = list_nonempty pom.RML_Mapping.pom_graphs in
      let target =
        if (Prims.op_Negation has_sgm) && (Prims.op_Negation has_pogm)
        then []
        else FStar_List_Tot_Base.op_At subject_graphs pog in
      let drop = (has_sgm || has_pogm) && (target = []) in
      FStar_List_Tot_Base.concatMap
        (fun p ->
           match p with
           | RDF_Graph_Executable.T_IRI pi ->
               FStar_List_Tot_Base.concatMap
                 (fun o ->
                    [{
                       pt_triple =
                         {
                           RDF_Graph_Executable.s = subj;
                           RDF_Graph_Executable.p = pi;
                           RDF_Graph_Executable.o = o
                         };
                       pt_graphs = target;
                       pt_drop = drop
                     }]) objects
           | uu___1 -> []) predicates
let class_placed_triples (subj : RDF_Graph_Executable.subject)
  (subject_graphs : Prims.string Prims.list) (has_sgm : Prims.bool)
  (classes : RDF_Graph_Executable.wf_iri Prims.list) :
  placed_triple Prims.list=
  let target = if has_sgm then subject_graphs else [] in
  let drop = has_sgm && (target = []) in
  FStar_List_Tot_Base.map
    (fun cls ->
       {
         pt_triple =
           {
             RDF_Graph_Executable.s = subj;
             RDF_Graph_Executable.p = RDF_Graph_Executable.rdf_type;
             RDF_Graph_Executable.o = (RDF_Graph_Executable.T_IRI cls)
           };
         pt_graphs = target;
         pt_drop = drop
       }) classes
let gen_row_triples (tmap : RML_Mapping.triples_map)
  (sm : RML_Mapping.subject_map_t) (row : RML_Sources.source_row)
  (row_seed : Prims.string)
  (base_iri : Prims.string FStar_Pervasives_Native.option) :
  placed_triple Prims.list=
  let subj_terms =
    eval_term_map MR_Subject sm.RML_Mapping.sm_term row row_seed base_iri in
  let has_sgm = list_nonempty sm.RML_Mapping.sm_graphs in
  let subject_graphs =
    eval_graphs sm.RML_Mapping.sm_graphs row row_seed base_iri in
  FStar_List_Tot_Base.concatMap
    (fun subj_term ->
       match subject_of_rdf_term subj_term with
       | FStar_Pervasives_Native.None -> []
       | FStar_Pervasives_Native.Some subj ->
           let class_triples =
             class_placed_triples subj subject_graphs has_sgm
               sm.RML_Mapping.sm_classes in
           let pom_triples =
             FStar_List_Tot_Base.concatMap
               (placed_triples_for_pom subj subject_graphs has_sgm row
                  row_seed base_iri)
               tmap.RML_Mapping.tm_predicate_object_maps in
           FStar_List_Tot_Base.op_At class_triples pom_triples) subj_terms
let eval_triples_map (tmap : RML_Mapping.triples_map)
  (rows : RML_Sources.source_row Prims.list)
  (default_base_iri : Prims.string FStar_Pervasives_Native.option) :
  placed_triple Prims.list=
  let base_iri =
    match tmap.RML_Mapping.tm_base_iri with
    | FStar_Pervasives_Native.Some b -> FStar_Pervasives_Native.Some b
    | FStar_Pervasives_Native.None -> default_base_iri in
  match tmap.RML_Mapping.tm_subject_map with
  | FStar_Pervasives_Native.Some sm ->
      FStar_List_Tot_Base.concatMap
        (fun uu___ ->
           match uu___ with
           | (idx, row) ->
               let row_seed =
                 Prims.strcat tmap.RML_Mapping.tm_id
                   (Prims.strcat "#r" (Prims.string_of_int idx)) in
               gen_row_triples tmap sm row row_seed base_iri)
        (FStar_List_Tot_Base.mapi (fun i r -> (i, r)) rows)
  | FStar_Pervasives_Native.None -> []
let eval_triples_map_json (tmap : RML_Mapping.triples_map)
  (json_root : Parser_JSON.json_val)
  (default_base_iri : Prims.string FStar_Pervasives_Native.option) :
  placed_triple Prims.list=
  match tmap.RML_Mapping.tm_logical_source with
  | FStar_Pervasives_Native.Some ls ->
      (match ls.RML_Mapping.ls_reference_formulation with
       | FStar_Pervasives_Native.Some (RML_Mapping.RF_JSONPath) ->
           let iterator =
             match ls.RML_Mapping.ls_iterator with
             | FStar_Pervasives_Native.Some it -> it
             | FStar_Pervasives_Native.None -> "$" in
           eval_triples_map tmap
             (RML_Sources.json_iterate json_root iterator) default_base_iri
       | uu___ -> [])
  | FStar_Pervasives_Native.None -> []
let eval_triples_map_csv (tmap : RML_Mapping.triples_map)
  (csv_text : Prims.string)
  (default_base_iri : Prims.string FStar_Pervasives_Native.option) :
  placed_triple Prims.list=
  match tmap.RML_Mapping.tm_logical_source with
  | FStar_Pervasives_Native.Some ls ->
      (match ls.RML_Mapping.ls_reference_formulation with
       | FStar_Pervasives_Native.Some (RML_Mapping.RF_CSV) ->
           eval_triples_map tmap
             (RML_Sources.csv_iterate csv_text ls.RML_Mapping.ls_null_values)
             default_base_iri
       | uu___ -> [])
  | FStar_Pervasives_Native.None -> []
let join_condition_holds (jc : RML_Mapping.join_condition)
  (child_row : RML_Sources.source_row) (parent_row : RML_Sources.source_row)
  : Prims.bool=
  let child_vals = eval_plain_strings jc.RML_Mapping.jc_child child_row in
  let parent_vals = eval_plain_strings jc.RML_Mapping.jc_parent parent_row in
  FStar_List_Tot_Base.existsb
    (fun v -> FStar_List_Tot_Base.mem v parent_vals) child_vals
let join_conditions_hold (jcs : RML_Mapping.join_condition Prims.list)
  (child_row : RML_Sources.source_row) (parent_row : RML_Sources.source_row)
  : Prims.bool=
  FStar_List_Tot_Base.for_all
    (fun jc -> join_condition_holds jc child_row parent_row) jcs
let matching_parent_rows (jcs : RML_Mapping.join_condition Prims.list)
  (cidx : Prims.int) (crow : RML_Sources.source_row)
  (parent_rows_idx : (Prims.int * RML_Sources.source_row) Prims.list) :
  (Prims.int * RML_Sources.source_row) Prims.list=
  match jcs with
  | [] ->
      FStar_List_Tot_Base.filter
        (fun uu___ -> match uu___ with | (pidx, uu___1) -> pidx = cidx)
        parent_rows_idx
  | uu___ ->
      FStar_List_Tot_Base.filter
        (fun uu___1 ->
           match uu___1 with
           | (uu___2, prow) -> join_conditions_hold jcs crow prow)
        parent_rows_idx
let eval_join_pom (subj : RDF_Graph_Executable.subject)
  (subject_graphs : Prims.string Prims.list) (has_sgm : Prims.bool)
  (crow : RML_Sources.source_row) (cidx : Prims.int)
  (row_seed : Prims.string)
  (base_iri : Prims.string FStar_Pervasives_Native.option)
  (lookup_parent :
    RML_Mapping.node_ref ->
      (RML_Mapping.triples_map * RML_Sources.source_row Prims.list)
        FStar_Pervasives_Native.option)
  (pom : RML_Mapping.predicate_object_map) : placed_triple Prims.list=
  let predicates =
    FStar_List_Tot_Base.concatMap
      (fun p -> eval_term_map MR_Predicate p crow row_seed base_iri)
      pom.RML_Mapping.pom_predicates in
  let pog = eval_graphs pom.RML_Mapping.pom_graphs crow row_seed base_iri in
  let has_pogm = list_nonempty pom.RML_Mapping.pom_graphs in
  let target =
    if (Prims.op_Negation has_sgm) && (Prims.op_Negation has_pogm)
    then []
    else FStar_List_Tot_Base.op_At subject_graphs pog in
  let drop = (has_sgm || has_pogm) && (target = []) in
  FStar_List_Tot_Base.concatMap
    (fun ob ->
       match ob with
       | RML_Mapping.OB_TermMap uu___ -> []
       | RML_Mapping.OB_Join rom ->
           (match lookup_parent rom.RML_Mapping.rom_parent_triples_map with
            | FStar_Pervasives_Native.None -> []
            | FStar_Pervasives_Native.Some (ptmap, prows) ->
                (match ptmap.RML_Mapping.tm_subject_map with
                 | FStar_Pervasives_Native.None -> []
                 | FStar_Pervasives_Native.Some psm ->
                     let parent_base = ptmap.RML_Mapping.tm_base_iri in
                     let parent_rows_idx =
                       FStar_List_Tot_Base.mapi (fun i r -> (i, r)) prows in
                     let matches =
                       matching_parent_rows rom.RML_Mapping.rom_joins cidx
                         crow parent_rows_idx in
                     FStar_List_Tot_Base.concatMap
                       (fun uu___ ->
                          match uu___ with
                          | (pidx, prow) ->
                              let prow_seed =
                                Prims.strcat ptmap.RML_Mapping.tm_id
                                  (Prims.strcat "#r"
                                     (Prims.string_of_int pidx)) in
                              let obj_terms =
                                eval_term_map MR_Subject
                                  psm.RML_Mapping.sm_term prow prow_seed
                                  parent_base in
                              FStar_List_Tot_Base.concatMap
                                (fun obj_term ->
                                   FStar_List_Tot_Base.concatMap
                                     (fun p ->
                                        match p with
                                        | RDF_Graph_Executable.T_IRI pi ->
                                            [{
                                               pt_triple =
                                                 {
                                                   RDF_Graph_Executable.s =
                                                     subj;
                                                   RDF_Graph_Executable.p =
                                                     pi;
                                                   RDF_Graph_Executable.o =
                                                     obj_term
                                                 };
                                               pt_graphs = target;
                                               pt_drop = drop
                                             }]
                                        | uu___1 -> []) predicates) obj_terms)
                       matches))) pom.RML_Mapping.pom_objects
let eval_join_triples_map (tmap : RML_Mapping.triples_map)
  (rows : RML_Sources.source_row Prims.list)
  (default_base_iri : Prims.string FStar_Pervasives_Native.option)
  (lookup_parent :
    RML_Mapping.node_ref ->
      (RML_Mapping.triples_map * RML_Sources.source_row Prims.list)
        FStar_Pervasives_Native.option)
  : placed_triple Prims.list=
  let base_iri =
    match tmap.RML_Mapping.tm_base_iri with
    | FStar_Pervasives_Native.Some b -> FStar_Pervasives_Native.Some b
    | FStar_Pervasives_Native.None -> default_base_iri in
  match tmap.RML_Mapping.tm_subject_map with
  | FStar_Pervasives_Native.None -> []
  | FStar_Pervasives_Native.Some sm ->
      let has_sgm = list_nonempty sm.RML_Mapping.sm_graphs in
      FStar_List_Tot_Base.concatMap
        (fun uu___ ->
           match uu___ with
           | (cidx, crow) ->
               let row_seed =
                 Prims.strcat tmap.RML_Mapping.tm_id
                   (Prims.strcat "#r" (Prims.string_of_int cidx)) in
               let subj_terms =
                 eval_term_map MR_Subject sm.RML_Mapping.sm_term crow
                   row_seed base_iri in
               let subject_graphs =
                 eval_graphs sm.RML_Mapping.sm_graphs crow row_seed base_iri in
               FStar_List_Tot_Base.concatMap
                 (fun subj_term ->
                    match subject_of_rdf_term subj_term with
                    | FStar_Pervasives_Native.None -> []
                    | FStar_Pervasives_Native.Some subj ->
                        FStar_List_Tot_Base.concatMap
                          (eval_join_pom subj subject_graphs has_sgm crow
                             cidx row_seed base_iri lookup_parent)
                          tmap.RML_Mapping.tm_predicate_object_maps)
                 subj_terms)
        (FStar_List_Tot_Base.mapi (fun i r -> (i, r)) rows)
let add_to_named_graph (ds : RDF_Graph_Executable.rdf_dataset)
  (name : Prims.string) (t : RDF_Graph_Executable.triple) :
  RDF_Graph_Executable.rdf_dataset=
  match FStar_List_Tot_Base.tryFind
          (fun ng -> ng.RDF_Graph_Executable.ng_name = name)
          ds.RDF_Graph_Executable.ds_named
  with
  | FStar_Pervasives_Native.Some uu___ ->
      {
        RDF_Graph_Executable.ds_default =
          (ds.RDF_Graph_Executable.ds_default);
        RDF_Graph_Executable.ds_named =
          (FStar_List_Tot_Base.map
             (fun ng ->
                if ng.RDF_Graph_Executable.ng_name = name
                then
                  {
                    RDF_Graph_Executable.ng_name =
                      (ng.RDF_Graph_Executable.ng_name);
                    RDF_Graph_Executable.ng_graph = (t ::
                      (ng.RDF_Graph_Executable.ng_graph))
                  }
                else ng) ds.RDF_Graph_Executable.ds_named)
      }
  | FStar_Pervasives_Native.None ->
      {
        RDF_Graph_Executable.ds_default =
          (ds.RDF_Graph_Executable.ds_default);
        RDF_Graph_Executable.ds_named =
          ({
             RDF_Graph_Executable.ng_name = name;
             RDF_Graph_Executable.ng_graph = [t]
           } :: (ds.RDF_Graph_Executable.ds_named))
      }
let add_to_graph (ds : RDF_Graph_Executable.rdf_dataset)
  (name : Prims.string) (t : RDF_Graph_Executable.triple) :
  RDF_Graph_Executable.rdf_dataset=
  if name = RML_Mapping.rml_defaultGraph
  then
    {
      RDF_Graph_Executable.ds_default = (t ::
        (ds.RDF_Graph_Executable.ds_default));
      RDF_Graph_Executable.ds_named = (ds.RDF_Graph_Executable.ds_named)
    }
  else add_to_named_graph ds name t
let rec place_into_dataset (ds : RDF_Graph_Executable.rdf_dataset)
  (pts : placed_triple Prims.list) : RDF_Graph_Executable.rdf_dataset=
  match pts with
  | [] -> ds
  | pt::rest ->
      let ds1 =
        if pt.pt_drop
        then ds
        else
          if pt.pt_graphs = []
          then
            {
              RDF_Graph_Executable.ds_default = ((pt.pt_triple) ::
                (ds.RDF_Graph_Executable.ds_default));
              RDF_Graph_Executable.ds_named =
                (ds.RDF_Graph_Executable.ds_named)
            }
          else
            FStar_List_Tot_Base.fold_left
              (fun d g -> add_to_graph d g pt.pt_triple) ds pt.pt_graphs in
      place_into_dataset ds1 rest
let eval_join_triples_map_dataset (tmap : RML_Mapping.triples_map)
  (rows : RML_Sources.source_row Prims.list)
  (default_base_iri : Prims.string FStar_Pervasives_Native.option)
  (lookup_parent :
    RML_Mapping.node_ref ->
      (RML_Mapping.triples_map * RML_Sources.source_row Prims.list)
        FStar_Pervasives_Native.option)
  (ds : RDF_Graph_Executable.rdf_dataset) : RDF_Graph_Executable.rdf_dataset=
  place_into_dataset ds
    (eval_join_triples_map tmap rows default_base_iri lookup_parent)
let eval_triples_map_dataset (tmap : RML_Mapping.triples_map)
  (rows : RML_Sources.source_row Prims.list)
  (default_base_iri : Prims.string FStar_Pervasives_Native.option) :
  RDF_Graph_Executable.rdf_dataset=
  place_into_dataset RDF_Graph_Executable.empty_dataset
    (eval_triples_map tmap rows default_base_iri)
let eval_triples_map_json_dataset (tmap : RML_Mapping.triples_map)
  (json_root : Parser_JSON.json_val)
  (default_base_iri : Prims.string FStar_Pervasives_Native.option) :
  RDF_Graph_Executable.rdf_dataset=
  place_into_dataset RDF_Graph_Executable.empty_dataset
    (eval_triples_map_json tmap json_root default_base_iri)
let eval_triples_map_csv_dataset (tmap : RML_Mapping.triples_map)
  (csv_text : Prims.string)
  (default_base_iri : Prims.string FStar_Pervasives_Native.option) :
  RDF_Graph_Executable.rdf_dataset=
  place_into_dataset RDF_Graph_Executable.empty_dataset
    (eval_triples_map_csv tmap csv_text default_base_iri)
