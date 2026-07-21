open Prims
let mk_literal (lexical : Prims.string) (dt : Prims.string)
  (lang : Prims.string FStar_Pervasives_Native.option) :
  RDF_Term.rdf_term FStar_Pervasives_Native.option=
  if RDF_Term.is_iri dt
  then
    let lit =
      {
        RDF_Term.lexical_form = lexical;
        RDF_Term.datatype = dt;
        RDF_Term.lang_tag = lang;
        RDF_Term.direction = FStar_Pervasives_Native.None
      } in
    (if RDF_Term.literal_wf lit
     then FStar_Pervasives_Native.Some (RDF_Term.T_Literal lit)
     else FStar_Pervasives_Native.None)
  else FStar_Pervasives_Native.None
let json_parse_text_direction (s : Prims.string) :
  RDF_Term.text_direction FStar_Pervasives_Native.option=
  if s = "ltr"
  then FStar_Pervasives_Native.Some RDF_Term.Dir_LTR
  else
    if s = "rtl"
    then FStar_Pervasives_Native.Some RDF_Term.Dir_RTL
    else FStar_Pervasives_Native.None
let mk_dir_literal (lexical : Prims.string) (lang : Prims.string)
  (dir : RDF_Term.text_direction) :
  RDF_Term.rdf_term FStar_Pervasives_Native.option=
  let lit =
    {
      RDF_Term.lexical_form = lexical;
      RDF_Term.datatype = RDF_Term.rdf_dir_lang_string;
      RDF_Term.lang_tag = (FStar_Pervasives_Native.Some lang);
      RDF_Term.direction = (FStar_Pervasives_Native.Some dir)
    } in
  if RDF_Term.literal_wf lit
  then FStar_Pervasives_Native.Some (RDF_Term.T_Literal lit)
  else FStar_Pervasives_Native.None
let rec parse_binding_value_fuel (fuel : Prims.nat)
  (obj : Parser_JSON.json_val) :
  RDF_Term.rdf_term FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (match Parser_JSON.json_get_string "type" obj with
     | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
     | FStar_Pervasives_Native.Some typ ->
         let val_str =
           match Parser_JSON.json_get_string "value" obj with
           | FStar_Pervasives_Native.Some s -> s
           | FStar_Pervasives_Native.None -> "" in
         if typ = "uri"
         then
           (if RDF_Term.is_iri val_str
            then FStar_Pervasives_Native.Some (RDF_Term.T_IRI val_str)
            else FStar_Pervasives_Native.None)
         else
           if typ = "bnode"
           then FStar_Pervasives_Native.Some (RDF_Term.T_BNode val_str)
           else
             if (typ = "literal") || (typ = "typed-literal")
             then
               (let lang = Parser_JSON.json_get_string "xml:lang" obj in
                let dt = Parser_JSON.json_get_string "datatype" obj in
                let its_dir = Parser_JSON.json_get_string "its:dir" obj in
                match (lang, its_dir) with
                | (FStar_Pervasives_Native.Some lang_val,
                   FStar_Pervasives_Native.Some dir_str) ->
                    (match json_parse_text_direction dir_str with
                     | FStar_Pervasives_Native.Some dir_val ->
                         mk_dir_literal val_str lang_val dir_val
                     | FStar_Pervasives_Native.None ->
                         mk_literal val_str RDF_Term.rdf_lang_string
                           (FStar_Pervasives_Native.Some lang_val))
                | (FStar_Pervasives_Native.Some lang_val,
                   FStar_Pervasives_Native.None) ->
                    mk_literal val_str RDF_Term.rdf_lang_string
                      (FStar_Pervasives_Native.Some lang_val)
                | (FStar_Pervasives_Native.None, uu___3) ->
                    (match dt with
                     | FStar_Pervasives_Native.Some dt_val ->
                         mk_literal val_str dt_val
                           FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.None ->
                         mk_literal val_str RDF_Term.xsd_string
                           FStar_Pervasives_Native.None))
             else
               if typ = "triple"
               then
                 (match Parser_JSON.json_get_field "value" obj with
                  | FStar_Pervasives_Native.None ->
                      FStar_Pervasives_Native.None
                  | FStar_Pervasives_Native.Some tval ->
                      (match ((Parser_JSON.json_get_field "subject" tval),
                               (Parser_JSON.json_get_field "predicate" tval),
                               (Parser_JSON.json_get_field "object" tval))
                       with
                       | (FStar_Pervasives_Native.Some sj,
                          FStar_Pervasives_Native.Some pj,
                          FStar_Pervasives_Native.Some oj) ->
                           (match ((parse_binding_value_fuel
                                      (fuel - Prims.int_one) sj),
                                    (parse_binding_value_fuel
                                       (fuel - Prims.int_one) pj),
                                    (parse_binding_value_fuel
                                       (fuel - Prims.int_one) oj))
                            with
                            | (FStar_Pervasives_Native.Some (RDF_Term.T_IRI
                               si), FStar_Pervasives_Native.Some
                               (RDF_Term.T_IRI p),
                               FStar_Pervasives_Native.Some ot) ->
                                FStar_Pervasives_Native.Some
                                  (RDF_Term.T_TripleTerm
                                     ((RDF_Term.S_IRI si), p, ot))
                            | (FStar_Pervasives_Native.Some (RDF_Term.T_BNode
                               sb), FStar_Pervasives_Native.Some
                               (RDF_Term.T_IRI p),
                               FStar_Pervasives_Native.Some ot) ->
                                FStar_Pervasives_Native.Some
                                  (RDF_Term.T_TripleTerm
                                     ((RDF_Term.S_BNode sb), p, ot))
                            | (uu___4, uu___5, uu___6) ->
                                FStar_Pervasives_Native.None)
                       | (uu___4, uu___5, uu___6) ->
                           FStar_Pervasives_Native.None))
               else FStar_Pervasives_Native.None)
let parse_binding_value (obj : Parser_JSON.json_val) :
  RDF_Term.rdf_term FStar_Pervasives_Native.option=
  parse_binding_value_fuel (Prims.of_int (64)) obj
let parse_binding_row (obj : Parser_JSON.json_val) :
  (Prims.string * RDF_Term.rdf_term) Prims.list=
  match obj with
  | Parser_JSON.JObject fields ->
      FStar_List_Tot_Base.concatMap
        (fun pair ->
           let uu___ = pair in
           match uu___ with
           | (var_name, val_obj) ->
               (match parse_binding_value val_obj with
                | FStar_Pervasives_Native.Some term -> [(var_name, term)]
                | FStar_Pervasives_Native.None -> [])) fields
  | uu___ -> []
let parse_srj_results (input : Prims.string) :
  (Prims.string Prims.list * (Prims.string * RDF_Term.rdf_term) Prims.list
    Prims.list) FStar_Pervasives_Native.option=
  match Parser_JSON.parse_json input with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some root ->
      let vars =
        match Parser_JSON.json_get_field "head" root with
        | FStar_Pervasives_Native.None -> []
        | FStar_Pervasives_Native.Some head ->
            (match Parser_JSON.json_get_string_array "vars" head with
             | FStar_Pervasives_Native.Some vs -> vs
             | FStar_Pervasives_Native.None -> []) in
      (match Parser_JSON.json_get_field "results" root with
       | FStar_Pervasives_Native.Some results_obj ->
           (match Parser_JSON.json_get_array "bindings" results_obj with
            | FStar_Pervasives_Native.Some bindings ->
                let rows = FStar_List_Tot_Base.map parse_binding_row bindings in
                FStar_Pervasives_Native.Some (vars, rows)
            | FStar_Pervasives_Native.None ->
                FStar_Pervasives_Native.Some (vars, []))
       | FStar_Pervasives_Native.None ->
           FStar_Pervasives_Native.Some (vars, []))
let parse_srj_boolean (input : Prims.string) :
  Prims.bool FStar_Pervasives_Native.option=
  match Parser_JSON.parse_json input with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some root ->
      Parser_JSON.json_get_bool "boolean" root
