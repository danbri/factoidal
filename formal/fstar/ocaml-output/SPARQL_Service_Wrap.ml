open Prims
let str_starts_with (s : Prims.string) (prefix : Prims.string) : Prims.bool=
  let lp = FStar_String.strlen prefix in
  ((FStar_String.strlen s) >= lp) &&
    ((FStar_String.sub s Prims.int_zero lp) = prefix)
let str_drop_prefix (s : Prims.string) (prefix : Prims.string) :
  Prims.string=
  let lp = FStar_String.strlen prefix in
  if (FStar_String.strlen s) >= lp
  then FStar_String.sub s lp ((FStar_String.strlen s) - lp)
  else s
let rec split_once_chars_acc (sep : Prims.nat)
  (cs : FStar_Char.char Prims.list) (acc : FStar_Char.char Prims.list) :
  (FStar_Char.char Prims.list * FStar_Char.char Prims.list
    FStar_Pervasives_Native.option)=
  match cs with
  | [] -> ((FStar_List_Tot_Base.rev acc), FStar_Pervasives_Native.None)
  | c::rest ->
      if (SPARQL_HTTP_Client.char_code c) = sep
      then
        ((FStar_List_Tot_Base.rev acc), (FStar_Pervasives_Native.Some rest))
      else split_once_chars_acc sep rest (c :: acc)
let split_once_on (s : Prims.string) (sep : FStar_Char.char) :
  (Prims.string * Prims.string FStar_Pervasives_Native.option)=
  let uu___ =
    split_once_chars_acc (SPARQL_HTTP_Client.char_code sep)
      (FStar_String.list_of_string s) [] in
  match uu___ with
  | (before, after) ->
      ((FStar_String.string_of_list before),
        ((match after with
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some cs ->
              FStar_Pervasives_Native.Some (FStar_String.string_of_list cs))))
let rec split_all_chars_acc (sep : Prims.nat)
  (cs : FStar_Char.char Prims.list) (cur : FStar_Char.char Prims.list) :
  FStar_Char.char Prims.list Prims.list=
  match cs with
  | [] -> [FStar_List_Tot_Base.rev cur]
  | c::rest ->
      if (SPARQL_HTTP_Client.char_code c) = sep
      then (FStar_List_Tot_Base.rev cur) :: (split_all_chars_acc sep rest [])
      else split_all_chars_acc sep rest (c :: cur)
let split_all_on (s : Prims.string) (sep : FStar_Char.char) :
  Prims.string Prims.list=
  FStar_List_Tot_Base.map FStar_String.string_of_list
    (split_all_chars_acc (SPARQL_HTTP_Client.char_code sep)
       (FStar_String.list_of_string s) [])
let is_hex_digit_wrap (c : FStar_Char.char) : Prims.bool=
  let cd = SPARQL_HTTP_Client.char_code c in
  (((cd >= (Prims.of_int (0x30))) && (cd <= (Prims.of_int (0x39)))) ||
     ((cd >= (Prims.of_int (0x41))) && (cd <= (Prims.of_int (0x46)))))
    || ((cd >= (Prims.of_int (0x61))) && (cd <= (Prims.of_int (0x66))))
let hex_value_wrap (c : FStar_Char.char) : Prims.nat=
  let cd = SPARQL_HTTP_Client.char_code c in
  if (cd >= (Prims.of_int (0x30))) && (cd <= (Prims.of_int (0x39)))
  then cd - (Prims.of_int (0x30))
  else
    if (cd >= (Prims.of_int (0x41))) && (cd <= (Prims.of_int (0x46)))
    then (cd - (Prims.of_int (0x41))) + (Prims.of_int (10))
    else
      if (cd >= (Prims.of_int (0x61))) && (cd <= (Prims.of_int (0x66)))
      then (cd - (Prims.of_int (0x61))) + (Prims.of_int (10))
      else Prims.int_zero
let rec form_decode_chars (cs : FStar_Char.char Prims.list) :
  FStar_Char.char Prims.list=
  match cs with
  | [] -> []
  | c::rest ->
      let code = SPARQL_HTTP_Client.char_code c in
      if code = (Prims.of_int (0x25))
      then
        (match rest with
         | h1::h2::rest' ->
             if (is_hex_digit_wrap h1) && (is_hex_digit_wrap h2)
             then
               (FStar_Char.char_of_int
                  (((hex_value_wrap h1) * (Prims.of_int (16))) +
                     (hex_value_wrap h2)))
               :: (form_decode_chars rest')
             else c :: (form_decode_chars rest)
         | uu___ -> c :: (form_decode_chars rest))
      else
        if code = (Prims.of_int (0x2B))
        then (FStar_Char.char_of_int (Prims.of_int (0x20))) ::
          (form_decode_chars rest)
        else c :: (form_decode_chars rest)
let form_decode (s : Prims.string) : Prims.string=
  FStar_String.string_of_list
    (form_decode_chars (FStar_String.list_of_string s))
let parse_kv_pair (pair : Prims.string) :
  (Prims.string * Prims.string) FStar_Pervasives_Native.option=
  match split_once_on pair (FStar_Char.char_of_int (Prims.of_int (0x3D)))
  with
  | (k, FStar_Pervasives_Native.Some v) ->
      FStar_Pervasives_Native.Some ((form_decode k), (form_decode v))
  | (k, FStar_Pervasives_Native.None) ->
      if (FStar_String.strlen k) = Prims.int_zero
      then FStar_Pervasives_Native.None
      else FStar_Pervasives_Native.Some ((form_decode k), "")
let parse_control_fragment (frag : Prims.string) :
  (Prims.string * Prims.string) Prims.list=
  FStar_List_Tot_Base.concatMap
    (fun p ->
       match parse_kv_pair p with
       | FStar_Pervasives_Native.Some kv -> [kv]
       | FStar_Pervasives_Native.None -> [])
    (split_all_on frag (FStar_Char.char_of_int (Prims.of_int (0x26))))
let ascii_lower_char_wrap (c : FStar_Char.char) : FStar_Char.char=
  let cd = SPARQL_HTTP_Client.char_code c in
  if (cd >= (Prims.of_int (0x41))) && (cd <= (Prims.of_int (0x5A)))
  then FStar_Char.char_of_int (cd + (Prims.of_int (32)))
  else c
let ascii_lower_string_wrap (s : Prims.string) : Prims.string=
  FStar_String.string_of_list
    (FStar_List_Tot_Base.map ascii_lower_char_wrap
       (FStar_String.list_of_string s))
let rec trim_ws_left (cs : FStar_Char.char Prims.list) :
  FStar_Char.char Prims.list=
  match cs with
  | c::rest ->
      if
        ((SPARQL_HTTP_Client.char_code c) = (Prims.of_int (0x20))) ||
          ((SPARQL_HTTP_Client.char_code c) = (Prims.of_int (0x09)))
      then trim_ws_left rest
      else cs
  | [] -> cs
let trim_ws_wrap (s : Prims.string) : Prims.string=
  FStar_String.string_of_list
    (FStar_List_Tot_Base.rev
       (trim_ws_left
          (FStar_List_Tot_Base.rev
             (trim_ws_left (FStar_String.list_of_string s)))))
let content_type_base (ct : Prims.string) : Prims.string=
  match split_once_on ct (FStar_Char.char_of_int (Prims.of_int (0x3B))) with
  | (base, uu___) -> ascii_lower_string_wrap (trim_ws_wrap base)
let rec header_lookup_ci_wrap (hs : (Prims.string * Prims.string) Prims.list)
  (needle : Prims.string) : Prims.string FStar_Pervasives_Native.option=
  match hs with
  | [] -> FStar_Pervasives_Native.None
  | (k, v)::rest ->
      if k = needle
      then FStar_Pervasives_Native.Some v
      else header_lookup_ci_wrap rest needle
let header_lookup_ci_local
  (headers : (Prims.string * Prims.string) Prims.list) (name : Prims.string)
  : Prims.string FStar_Pervasives_Native.option=
  header_lookup_ci_wrap headers (ascii_lower_string_wrap name)
type wrap_transport =
  | WT_Https 
  | WT_Http 
let uu___is_WT_Https (projectee : wrap_transport) : Prims.bool=
  match projectee with | WT_Https -> true | uu___ -> false
let uu___is_WT_Http (projectee : wrap_transport) : Prims.bool=
  match projectee with | WT_Http -> true | uu___ -> false
let wrap_https_prefix : Prims.string= "wrap+https://"
let wrap_http_prefix : Prims.string= "wrap+http://"
type wrap_target =
  {
  wt_transport: wrap_transport ;
  wt_target: Prims.string ;
  wt_control: (Prims.string * Prims.string) Prims.list }
let __proj__Mkwrap_target__item__wt_transport (projectee : wrap_target) :
  wrap_transport=
  match projectee with
  | { wt_transport; wt_target; wt_control;_} -> wt_transport
let __proj__Mkwrap_target__item__wt_target (projectee : wrap_target) :
  Prims.string=
  match projectee with
  | { wt_transport; wt_target; wt_control;_} -> wt_target
let __proj__Mkwrap_target__item__wt_control (projectee : wrap_target) :
  (Prims.string * Prims.string) Prims.list=
  match projectee with
  | { wt_transport; wt_target; wt_control;_} -> wt_control
let wrap_target_url (wt : wrap_target) : Prims.string=
  Prims.strcat
    (match wt.wt_transport with
     | WT_Https -> "https://"
     | WT_Http -> "http://") wt.wt_target
let wrap_target_rml_name (wt : wrap_target) :
  Prims.string FStar_Pervasives_Native.option=
  FStar_List_Tot_Base.assoc "rml" wt.wt_control
let wrap_target_mime_override (wt : wrap_target) :
  Prims.string FStar_Pervasives_Native.option=
  FStar_List_Tot_Base.assoc "mime" wt.wt_control
let wrap_target_ttl (wt : wrap_target) :
  Prims.string FStar_Pervasives_Native.option=
  FStar_List_Tot_Base.assoc "ttl" wt.wt_control
let parse_wrap_iri (s : Prims.string) :
  wrap_target FStar_Pervasives_Native.option=
  let uu___ = split_once_on s (FStar_Char.char_of_int (Prims.of_int (0x23))) in
  match uu___ with
  | (before_frag, frag) ->
      let control =
        match frag with
        | FStar_Pervasives_Native.None -> []
        | FStar_Pervasives_Native.Some f -> parse_control_fragment f in
      if str_starts_with before_frag wrap_https_prefix
      then
        FStar_Pervasives_Native.Some
          {
            wt_transport = WT_Https;
            wt_target = (str_drop_prefix before_frag wrap_https_prefix);
            wt_control = control
          }
      else
        if str_starts_with before_frag wrap_http_prefix
        then
          FStar_Pervasives_Native.Some
            {
              wt_transport = WT_Http;
              wt_target = (str_drop_prefix before_frag wrap_http_prefix);
              wt_control = control
            }
        else FStar_Pervasives_Native.None
type wrap_format =
  | WF_Json 
  | WF_Csv 
  | WF_Turtle 
  | WF_NTriples 
  | WF_NQuads 
  | WF_PlainString 
let uu___is_WF_Json (projectee : wrap_format) : Prims.bool=
  match projectee with | WF_Json -> true | uu___ -> false
let uu___is_WF_Csv (projectee : wrap_format) : Prims.bool=
  match projectee with | WF_Csv -> true | uu___ -> false
let uu___is_WF_Turtle (projectee : wrap_format) : Prims.bool=
  match projectee with | WF_Turtle -> true | uu___ -> false
let uu___is_WF_NTriples (projectee : wrap_format) : Prims.bool=
  match projectee with | WF_NTriples -> true | uu___ -> false
let uu___is_WF_NQuads (projectee : wrap_format) : Prims.bool=
  match projectee with | WF_NQuads -> true | uu___ -> false
let uu___is_WF_PlainString (projectee : wrap_format) : Prims.bool=
  match projectee with | WF_PlainString -> true | uu___ -> false
let detect_wrap_format
  (content_type : Prims.string FStar_Pervasives_Native.option)
  (mime_override : Prims.string FStar_Pervasives_Native.option) :
  wrap_format=
  let base =
    match mime_override with
    | FStar_Pervasives_Native.Some m -> content_type_base m
    | FStar_Pervasives_Native.None ->
        (match content_type with
         | FStar_Pervasives_Native.Some ct -> content_type_base ct
         | FStar_Pervasives_Native.None -> "") in
  if base = "application/json"
  then WF_Json
  else
    if base = "text/csv"
    then WF_Csv
    else
      if (base = "text/turtle") || (base = "application/x-turtle")
      then WF_Turtle
      else
        if base = "application/n-triples"
        then WF_NTriples
        else
          if base = "application/n-quads" then WF_NQuads else WF_PlainString
let default_port_for (t : wrap_transport) : Prims.nat=
  match t with
  | WT_Https -> (Prims.of_int (443))
  | WT_Http -> (Prims.of_int (80))
let split_authority_path (s : Prims.string) : (Prims.string * Prims.string)=
  match split_once_on s (FStar_Char.char_of_int (Prims.of_int (0x2F))) with
  | (auth, FStar_Pervasives_Native.None) -> (auth, "/")
  | (auth, FStar_Pervasives_Native.Some rest) ->
      (auth, (Prims.strcat "/" rest))
let split_host_port (authority : Prims.string) (default_port : Prims.nat) :
  (Prims.string * Prims.nat)=
  match split_once_on authority
          (FStar_Char.char_of_int (Prims.of_int (0x3A)))
  with
  | (host, FStar_Pervasives_Native.None) -> (host, default_port)
  | (host, FStar_Pervasives_Native.Some port_s) ->
      (match SPARQL_HTTP_Client.parse_nat port_s with
       | FStar_Pervasives_Native.Some p -> (host, p)
       | FStar_Pervasives_Native.None -> (host, default_port))
let split_path_query (path_and_query : Prims.string) :
  (Prims.string * Prims.string)=
  match split_once_on path_and_query
          (FStar_Char.char_of_int (Prims.of_int (0x3F)))
  with
  | (p, FStar_Pervasives_Native.None) -> (p, "")
  | (p, FStar_Pervasives_Native.Some q) -> (p, q)
type wrap_request =
  {
  wr_host: Prims.string ;
  wr_port: Prims.nat ;
  wr_msg: SPARQL_HTTP_Client.http_request_msg }
let __proj__Mkwrap_request__item__wr_host (projectee : wrap_request) :
  Prims.string=
  match projectee with | { wr_host; wr_port; wr_msg;_} -> wr_host
let __proj__Mkwrap_request__item__wr_port (projectee : wrap_request) :
  Prims.nat= match projectee with | { wr_host; wr_port; wr_msg;_} -> wr_port
let __proj__Mkwrap_request__item__wr_msg (projectee : wrap_request) :
  SPARQL_HTTP_Client.http_request_msg=
  match projectee with | { wr_host; wr_port; wr_msg;_} -> wr_msg
let build_wrap_get_request (wt : wrap_target) : wrap_request=
  let uu___ = split_authority_path wt.wt_target in
  match uu___ with
  | (authority, path_and_query) ->
      let uu___1 =
        split_host_port authority (default_port_for wt.wt_transport) in
      (match uu___1 with
       | (host, port) ->
           let uu___2 = split_path_query path_and_query in
           (match uu___2 with
            | (path, query) ->
                {
                  wr_host = host;
                  wr_port = port;
                  wr_msg =
                    {
                      SPARQL_HTTP_Client.rm_method = "GET";
                      SPARQL_HTTP_Client.rm_path = path;
                      SPARQL_HTTP_Client.rm_query_str = query;
                      SPARQL_HTTP_Client.rm_version = "HTTP/1.1";
                      SPARQL_HTTP_Client.rm_host = host;
                      SPARQL_HTTP_Client.rm_headers =
                        [("Accept", "*/*"); ("Connection", "close")];
                      SPARQL_HTTP_Client.rm_body = ""
                    }
                }))
let default_wrap_ns : Prims.string= "http://factoidal.example/ns/wrap#"
let wrap_predicate_iri (ns : Prims.string) (key_encoded : Prims.string) :
  RDF_Term.wf_iri FStar_Pervasives_Native.option=
  let candidate = Prims.strcat ns key_encoded in
  if RDF_Term.is_iri candidate
  then FStar_Pervasives_Native.Some candidate
  else FStar_Pervasives_Native.None
let json_scalar_to_object (v : Parser_JSON.json_val) :
  RDF_Term.rdf_term FStar_Pervasives_Native.option=
  match RML_Eval.json_natural_value v with
  | FStar_Pervasives_Native.Some (lex, dt) ->
      RML_Eval.build_literal_opt lex dt FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
let subject_to_term (s : RDF_Term.subject) : RDF_Term.rdf_term=
  match s with
  | RDF_Term.S_IRI i -> RDF_Term.T_IRI i
  | RDF_Term.S_BNode b -> RDF_Term.T_BNode b
let rec json_field_value_triples (ns : Prims.string)
  (subj : RDF_Term.subject) (pred : RDF_Term.wf_iri) (seed : Prims.string)
  (v : Parser_JSON.json_val) : RDF_Triple.triple Prims.list=
  match v with
  | Parser_JSON.JArray items ->
      json_array_items_triples ns subj pred seed items
  | Parser_JSON.JObject fields ->
      let nested = RDF_Term.S_BNode seed in
      {
        RDF_Triple.s = subj;
        RDF_Triple.p = pred;
        RDF_Triple.o = (subject_to_term nested)
      } :: (json_object_fields_triples ns nested seed fields)
  | uu___ ->
      (match json_scalar_to_object v with
       | FStar_Pervasives_Native.None -> []
       | FStar_Pervasives_Native.Some obj ->
           [{ RDF_Triple.s = subj; RDF_Triple.p = pred; RDF_Triple.o = obj }])
and json_array_items_triples (ns : Prims.string) (subj : RDF_Term.subject)
  (pred : RDF_Term.wf_iri) (seed : Prims.string)
  (items : Parser_JSON.json_val Prims.list) : RDF_Triple.triple Prims.list=
  match items with
  | [] -> []
  | item::rest ->
      let item_seed =
        Prims.strcat seed
          (Prims.strcat "i"
             (Prims.string_of_int (FStar_List_Tot_Base.length rest))) in
      FStar_List_Tot_Base.op_At
        (json_field_value_triples ns subj pred item_seed item)
        (json_array_items_triples ns subj pred seed rest)
and json_object_fields_triples (ns : Prims.string) (subj : RDF_Term.subject)
  (seed : Prims.string)
  (fields : (Prims.string * Parser_JSON.json_val) Prims.list) :
  RDF_Triple.triple Prims.list=
  match fields with
  | [] -> []
  | (key, value)::rest ->
      (match wrap_predicate_iri ns (RML_Eval.string_encode_iri key) with
       | FStar_Pervasives_Native.None ->
           json_object_fields_triples ns subj seed rest
       | FStar_Pervasives_Native.Some pred ->
           FStar_List_Tot_Base.op_At
             (json_field_value_triples ns subj pred
                (Prims.strcat seed (Prims.strcat "_" key)) value)
             (json_object_fields_triples ns subj seed rest))
let default_json_document_triples (root : Parser_JSON.json_val) :
  RDF_Triple.triple Prims.list=
  let subj = RDF_Term.S_BNode "wrapdoc" in
  match root with
  | Parser_JSON.JObject fields ->
      json_object_fields_triples default_wrap_ns subj "wrapdoc" fields
  | Parser_JSON.JArray items ->
      (match wrap_predicate_iri default_wrap_ns "member" with
       | FStar_Pervasives_Native.None -> []
       | FStar_Pervasives_Native.Some pred ->
           json_array_items_triples default_wrap_ns subj pred "wrapdoc" items)
  | uu___ ->
      (match ((wrap_predicate_iri default_wrap_ns "value"),
               (json_scalar_to_object root))
       with
       | (FStar_Pervasives_Native.Some pred, FStar_Pervasives_Native.Some
          obj) ->
           [{ RDF_Triple.s = subj; RDF_Triple.p = pred; RDF_Triple.o = obj }]
       | uu___1 -> [])
let csv_row_triples (ns : Prims.string) (idx : Prims.int)
  (bindings : (Prims.string * Prims.string) Prims.list) :
  RDF_Triple.triple Prims.list=
  let subj =
    RDF_Term.S_BNode (Prims.strcat "wrapcsv_r" (Prims.string_of_int idx)) in
  FStar_List_Tot_Base.concatMap
    (fun cell ->
       let uu___ = cell in
       match uu___ with
       | (header, value) ->
           (match wrap_predicate_iri ns (RML_Eval.string_encode_iri header)
            with
            | FStar_Pervasives_Native.None -> []
            | FStar_Pervasives_Native.Some pred ->
                (match RML_Eval.build_literal_opt value RDF_Term.xsd_string
                         FStar_Pervasives_Native.None
                 with
                 | FStar_Pervasives_Native.None -> []
                 | FStar_Pervasives_Native.Some obj ->
                     [{
                        RDF_Triple.s = subj;
                        RDF_Triple.p = pred;
                        RDF_Triple.o = obj
                      }]))) bindings
let default_csv_document_triples (rows : RML_Sources.source_row Prims.list) :
  RDF_Triple.triple Prims.list=
  FStar_List_Tot_Base.concatMap
    (fun pair ->
       let uu___ = pair in
       match uu___ with
       | (i, row) ->
           (match row with
            | RML_Sources.Row_CSV bindings ->
                csv_row_triples default_wrap_ns i bindings
            | RML_Sources.Row_JSON uu___1 -> []))
    (FStar_List_Tot_Base.mapi (fun i r -> (i, r)) rows)
let plain_string_fallback_triples (body : Prims.string) :
  RDF_Triple.triple Prims.list=
  match wrap_predicate_iri default_wrap_ns "value" with
  | FStar_Pervasives_Native.None -> []
  | FStar_Pervasives_Native.Some pred ->
      (match RML_Eval.build_literal_opt body RDF_Term.xsd_string
               FStar_Pervasives_Native.None
       with
       | FStar_Pervasives_Native.None -> []
       | FStar_Pervasives_Native.Some obj ->
           [{
              RDF_Triple.s = (RDF_Term.S_BNode "wrapdoc");
              RDF_Triple.p = pred;
              RDF_Triple.o = obj
            }])
let nquads_dataset_triples (ds : RDF_Graph.rdf_dataset) :
  RDF_Triple.triple Prims.list=
  FStar_List_Tot_Base.op_At ds.RDF_Graph.ds_default
    (FStar_List_Tot_Base.concatMap (fun ng -> ng.RDF_Graph.ng_graph)
       ds.RDF_Graph.ds_named)
let select_triples_maps (doc : RML_Mapping.mapping_document)
  (name : Prims.string FStar_Pervasives_Native.option) :
  RML_Mapping.triples_map Prims.list=
  match name with
  | FStar_Pervasives_Native.None -> doc.RML_Mapping.md_triples_maps
  | FStar_Pervasives_Native.Some n ->
      let matches =
        FStar_List_Tot_Base.filter (fun tm -> tm.RML_Mapping.tm_id = n)
          doc.RML_Mapping.md_triples_maps in
      if Prims.uu___is_Nil matches
      then doc.RML_Mapping.md_triples_maps
      else matches
let triplify_with_rml (fmt : wrap_format) (body : Prims.string)
  (tmaps : RML_Mapping.triples_map Prims.list) :
  RDF_Triple.triple Prims.list=
  match fmt with
  | WF_Json ->
      (match Parser_JSON.parse_json body with
       | FStar_Pervasives_Native.Some root ->
           (RML_Eval.place_into_dataset RDF_Graph.empty_dataset
              (FStar_List_Tot_Base.concatMap
                 (fun tm ->
                    RML_Eval.eval_triples_map_json tm root
                      FStar_Pervasives_Native.None) tmaps)).RDF_Graph.ds_default
       | FStar_Pervasives_Native.None -> [])
  | WF_Csv ->
      (RML_Eval.place_into_dataset RDF_Graph.empty_dataset
         (FStar_List_Tot_Base.concatMap
            (fun tm ->
               RML_Eval.eval_triples_map_csv tm body
                 FStar_Pervasives_Native.None) tmaps)).RDF_Graph.ds_default
  | uu___ -> []
let resolve_wrap_response (wrap_iri : Prims.string) (status : Prims.nat)
  (headers : (Prims.string * Prims.string) Prims.list) (body : Prims.string)
  (rml_ttl_text : Prims.string FStar_Pervasives_Native.option) :
  RDF_Triple.triple Prims.list=
  match parse_wrap_iri wrap_iri with
  | FStar_Pervasives_Native.None -> []
  | FStar_Pervasives_Native.Some wt ->
      if (status < (Prims.of_int (200))) || (status >= (Prims.of_int (300)))
      then []
      else
        (let content_type = header_lookup_ci_local headers "Content-Type" in
         let fmt =
           detect_wrap_format content_type (wrap_target_mime_override wt) in
         match rml_ttl_text with
         | FStar_Pervasives_Native.Some ttl ->
             let doc =
               RML_Mapping.decode_mapping_document
                 (Parser_Turtle.parse_turtle ttl) in
             let tmaps = select_triples_maps doc (wrap_target_rml_name wt) in
             triplify_with_rml fmt body tmaps
         | FStar_Pervasives_Native.None ->
             (match fmt with
              | WF_Turtle ->
                  (match Parser_Turtle.parse_turtle_strict body with
                   | FStar_Pervasives_Native.Some ts -> ts
                   | FStar_Pervasives_Native.None -> [])
              | WF_NTriples ->
                  (match Parser_NTriples.parse_ntriples_strict body with
                   | FStar_Pervasives_Native.Some ts -> ts
                   | FStar_Pervasives_Native.None -> [])
              | WF_NQuads ->
                  (match Parser_NQuads.parse_nquads_strict body with
                   | FStar_Pervasives_Native.Some ds ->
                       nquads_dataset_triples ds
                   | FStar_Pervasives_Native.None -> [])
              | WF_Json ->
                  (match Parser_JSON.parse_json body with
                   | FStar_Pervasives_Native.Some root ->
                       default_json_document_triples root
                   | FStar_Pervasives_Native.None -> [])
              | WF_Csv ->
                  default_csv_document_triples
                    (RML_Sources.csv_iterate body [""])
              | WF_PlainString -> plain_string_fallback_triples body))
let _test_parse_wrap_https : Prims.bool=
  match parse_wrap_iri
          "wrap+https://api.example.org/v1/users?id=42#rml=urn:mapping:users-api"
  with
  | FStar_Pervasives_Native.Some wt ->
      ((wt.wt_transport = WT_Https) &&
         (wt.wt_target = "api.example.org/v1/users?id=42"))
        &&
        ((wrap_target_rml_name wt) =
           (FStar_Pervasives_Native.Some "urn:mapping:users-api"))
  | FStar_Pervasives_Native.None -> false
let _test_parse_wrap_http_no_fragment : Prims.bool=
  match parse_wrap_iri "wrap+http://internal.example.org/status" with
  | FStar_Pervasives_Native.Some wt ->
      ((wt.wt_transport = WT_Http) &&
         (wt.wt_target = "internal.example.org/status"))
        && ((wrap_target_rml_name wt) = FStar_Pervasives_Native.None)
  | FStar_Pervasives_Native.None -> false
let _test_parse_wrap_rejects_unknown_scheme : Prims.bool=
  (FStar_Pervasives_Native.uu___is_None
     (parse_wrap_iri "wrap+mcp:geocoder/geocode?x=1"))
    &&
    (FStar_Pervasives_Native.uu___is_None
       (parse_wrap_iri "http://example.org/plain"))
let _test_wrap_target_url : Prims.bool=
  match parse_wrap_iri "wrap+https://127.0.0.1:8099/data.json" with
  | FStar_Pervasives_Native.Some wt ->
      (wrap_target_url wt) = "https://127.0.0.1:8099/data.json"
  | FStar_Pervasives_Native.None -> false
let _test_build_wrap_get_request : Prims.bool=
  match parse_wrap_iri "wrap+http://127.0.0.1:8099/data.json?x=1" with
  | FStar_Pervasives_Native.Some wt ->
      let req = build_wrap_get_request wt in
      ((((req.wr_host = "127.0.0.1") && (req.wr_port = (Prims.of_int (8099))))
          && ((req.wr_msg).SPARQL_HTTP_Client.rm_path = "/data.json"))
         && ((req.wr_msg).SPARQL_HTTP_Client.rm_query_str = "x=1"))
        && ((req.wr_msg).SPARQL_HTTP_Client.rm_method = "GET")
  | FStar_Pervasives_Native.None -> false
let _test_default_port : Prims.bool=
  match parse_wrap_iri "wrap+https://example.org/x" with
  | FStar_Pervasives_Native.Some wt ->
      (build_wrap_get_request wt).wr_port = (Prims.of_int (443))
  | FStar_Pervasives_Native.None -> false
let _test_detect_format_mime_override_wins : Prims.bool=
  (detect_wrap_format (FStar_Pervasives_Native.Some "text/plain")
     (FStar_Pervasives_Native.Some "application/json"))
    = WF_Json
let _test_detect_format_content_type : Prims.bool=
  (detect_wrap_format
     (FStar_Pervasives_Native.Some "text/csv; charset=utf-8")
     FStar_Pervasives_Native.None)
    = WF_Csv
let _test_detect_format_unknown : Prims.bool=
  (detect_wrap_format FStar_Pervasives_Native.None
     FStar_Pervasives_Native.None)
    = WF_PlainString
let _test_default_json_object_mapping : Prims.bool=
  match Parser_JSON.parse_json "{\"name\": \"Ada\", \"age\": 36}" with
  | FStar_Pervasives_Native.Some root ->
      let ts = default_json_document_triples root in
      (FStar_List_Tot_Base.length ts) = (Prims.of_int (2))
  | FStar_Pervasives_Native.None -> false
let _test_default_json_nested_object : Prims.bool=
  match Parser_JSON.parse_json
          "{\"name\": \"Ada\", \"address\": {\"city\": \"London\"}}"
  with
  | FStar_Pervasives_Native.Some root ->
      (FStar_List_Tot_Base.length (default_json_document_triples root)) =
        (Prims.of_int (3))
  | FStar_Pervasives_Native.None -> false
let _test_default_json_array_fanout : Prims.bool=
  match Parser_JSON.parse_json "{\"tag\": [\"a\", \"b\", \"c\"]}" with
  | FStar_Pervasives_Native.Some root ->
      (FStar_List_Tot_Base.length (default_json_document_triples root)) =
        (Prims.of_int (3))
  | FStar_Pervasives_Native.None -> false
let _test_default_csv_mapping : Prims.bool=
  let rows = RML_Sources.csv_iterate "name,age\nAda,36\nGrace,85\n" [""] in
  (FStar_List_Tot_Base.length (default_csv_document_triples rows)) =
    (Prims.of_int (4))
let _test_plain_string_fallback : Prims.bool=
  (FStar_List_Tot_Base.length (plain_string_fallback_triples "hello")) =
    Prims.int_one
let _test_resolve_default_json : Prims.bool=
  (FStar_List_Tot_Base.length
     (resolve_wrap_response "wrap+http://127.0.0.1:8099/x"
        (Prims.of_int (200)) [("content-type", "application/json")]
        "{\"a\": \"b\"}" FStar_Pervasives_Native.None))
    = Prims.int_one
let _test_resolve_non_2xx_status : Prims.bool=
  Prims.uu___is_Nil
    (resolve_wrap_response "wrap+http://127.0.0.1:8099/x"
       (Prims.of_int (404)) [("content-type", "application/json")] "{}"
       FStar_Pervasives_Native.None)
let _test_resolve_turtle_passthrough : Prims.bool=
  (FStar_List_Tot_Base.length
     (resolve_wrap_response "wrap+http://127.0.0.1:8099/x"
        (Prims.of_int (200)) [("content-type", "text/turtle")]
        "<http://example.org/s> <http://example.org/p> \"o\" ."
        FStar_Pervasives_Native.None))
    = Prims.int_one
let _test_resolve_unrecognized_iri : Prims.bool=
  Prims.uu___is_Nil
    (resolve_wrap_response "http://example.org/plain-service"
       (Prims.of_int (200)) [] "irrelevant" FStar_Pervasives_Native.None)
