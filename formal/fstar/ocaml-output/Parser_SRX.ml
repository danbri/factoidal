open Prims
let rec find_colon_in_list (cs : FStar_Char.char Prims.list) :
  FStar_Char.char Prims.list=
  match cs with
  | [] -> []
  | c::rest ->
      if (FStar_Char.int_of_char c) = (Prims.of_int (0x3A))
      then rest
      else find_colon_in_list rest
let strip_ns_prefix (tag : Prims.string) : Prims.string=
  let cs = FStar_String.list_of_string tag in
  let after = find_colon_in_list cs in
  match after with | [] -> tag | uu___ -> FStar_String.string_of_list after
let tag_matches (expected : Prims.string) (actual : Prims.string) :
  Prims.bool= (actual = expected) || ((strip_ns_prefix actual) = expected)
let find_child (tag : Prims.string)
  (children : Parser_XML.xml_node Prims.list) :
  Parser_XML.xml_node FStar_Pervasives_Native.option=
  match FStar_List_Tot_Base.find
          (fun node ->
             match node with
             | Parser_XML.XElement (t, uu___, uu___1) -> tag_matches tag t
             | uu___ -> false) children
  with
  | FStar_Pervasives_Native.Some n -> FStar_Pervasives_Native.Some n
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
let find_children (tag : Prims.string)
  (children : Parser_XML.xml_node Prims.list) :
  Parser_XML.xml_node Prims.list=
  FStar_List_Tot_Base.filter
    (fun node ->
       match node with
       | Parser_XML.XElement (t, uu___, uu___1) -> tag_matches tag t
       | uu___ -> false) children
let get_attr (name : Prims.string)
  (attrs : Parser_XML.xml_attribute Prims.list) :
  Prims.string FStar_Pervasives_Native.option=
  match FStar_List_Tot_Base.find (fun a -> a.Parser_XML.attr_name = name)
          attrs
  with
  | FStar_Pervasives_Native.Some a ->
      FStar_Pervasives_Native.Some (a.Parser_XML.attr_value)
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
let collect_text (node : Parser_XML.xml_node) : Prims.string=
  Parser_XML.text_content node
let parse_uri_value (node : Parser_XML.xml_node) :
  RDF_Graph_Executable.rdf_term FStar_Pervasives_Native.option=
  let uri_str = collect_text node in
  if RDF_Graph_Executable.is_iri uri_str
  then FStar_Pervasives_Native.Some (RDF_Graph_Executable.T_IRI uri_str)
  else FStar_Pervasives_Native.None
let parse_bnode_value (node : Parser_XML.xml_node) :
  RDF_Graph_Executable.rdf_term FStar_Pervasives_Native.option=
  let bnode_str = collect_text node in
  FStar_Pervasives_Native.Some (RDF_Graph_Executable.T_BNode bnode_str)
let parse_literal_value (node : Parser_XML.xml_node) :
  RDF_Graph_Executable.rdf_term FStar_Pervasives_Native.option=
  match node with
  | Parser_XML.XElement (uu___, attrs, children) ->
      let lex =
        FStar_String.concat ""
          (FStar_List_Tot_Base.map collect_text children) in
      let lang = get_attr "xml:lang" attrs in
      let dt = get_attr "datatype" attrs in
      (match (lang, dt) with
       | (FStar_Pervasives_Native.Some lang_val, uu___1) ->
           let lit =
             {
               RDF_Graph_Executable.lexical_form = lex;
               RDF_Graph_Executable.datatype =
                 RDF_Graph_Executable.rdf_lang_string;
               RDF_Graph_Executable.lang_tag =
                 (FStar_Pervasives_Native.Some lang_val)
             } in
           if RDF_Graph_Executable.literal_wf lit
           then
             FStar_Pervasives_Native.Some
               (RDF_Graph_Executable.T_Literal lit)
           else FStar_Pervasives_Native.None
       | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.Some dt_val)
           ->
           if RDF_Graph_Executable.is_iri dt_val
           then
             let lit =
               {
                 RDF_Graph_Executable.lexical_form = lex;
                 RDF_Graph_Executable.datatype = dt_val;
                 RDF_Graph_Executable.lang_tag = FStar_Pervasives_Native.None
               } in
             (if RDF_Graph_Executable.literal_wf lit
              then
                FStar_Pervasives_Native.Some
                  (RDF_Graph_Executable.T_Literal lit)
              else FStar_Pervasives_Native.None)
           else FStar_Pervasives_Native.None
       | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) ->
           let lit =
             {
               RDF_Graph_Executable.lexical_form = lex;
               RDF_Graph_Executable.datatype =
                 RDF_Graph_Executable.xsd_string;
               RDF_Graph_Executable.lang_tag = FStar_Pervasives_Native.None
             } in
           if RDF_Graph_Executable.literal_wf lit
           then
             FStar_Pervasives_Native.Some
               (RDF_Graph_Executable.T_Literal lit)
           else FStar_Pervasives_Native.None)
  | uu___ -> FStar_Pervasives_Native.None
let parse_binding_value (node : Parser_XML.xml_node) :
  RDF_Graph_Executable.rdf_term FStar_Pervasives_Native.option=
  match node with
  | Parser_XML.XElement (uu___, uu___1, children) ->
      let elems =
        FStar_List_Tot_Base.filter
          (fun child ->
             match child with
             | Parser_XML.XElement (uu___2, uu___3, uu___4) -> true
             | uu___2 -> false) children in
      (match elems with
       | [] -> FStar_Pervasives_Native.None
       | value_node::uu___2 ->
           (match value_node with
            | Parser_XML.XElement (t, uu___3, uu___4) ->
                let local = strip_ns_prefix t in
                if local = "uri"
                then parse_uri_value value_node
                else
                  if local = "bnode"
                  then parse_bnode_value value_node
                  else
                    if local = "literal"
                    then parse_literal_value value_node
                    else FStar_Pervasives_Native.None
            | uu___3 -> FStar_Pervasives_Native.None))
  | uu___ -> FStar_Pervasives_Native.None
let parse_binding (node : Parser_XML.xml_node) :
  (Prims.string * RDF_Graph_Executable.rdf_term)
    FStar_Pervasives_Native.option=
  match node with
  | Parser_XML.XElement (uu___, attrs, uu___1) ->
      (match get_attr "name" attrs with
       | FStar_Pervasives_Native.Some var_name ->
           (match parse_binding_value node with
            | FStar_Pervasives_Native.Some term ->
                FStar_Pervasives_Native.Some (var_name, term)
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
  | uu___ -> FStar_Pervasives_Native.None
let parse_result_row (node : Parser_XML.xml_node) :
  (Prims.string * RDF_Graph_Executable.rdf_term) Prims.list=
  match node with
  | Parser_XML.XElement (uu___, uu___1, children) ->
      let bindings = find_children "binding" children in
      FStar_List_Tot_Base.concatMap
        (fun b ->
           match parse_binding b with
           | FStar_Pervasives_Native.Some pair -> [pair]
           | FStar_Pervasives_Native.None -> []) bindings
  | uu___ -> []
let parse_head_vars (head_node : Parser_XML.xml_node) :
  Prims.string Prims.list=
  match head_node with
  | Parser_XML.XElement (uu___, uu___1, children) ->
      let var_elems = find_children "variable" children in
      FStar_List_Tot_Base.concatMap
        (fun v ->
           match v with
           | Parser_XML.XElement (uu___2, attrs, uu___3) ->
               (match get_attr "name" attrs with
                | FStar_Pervasives_Native.Some n -> [n]
                | FStar_Pervasives_Native.None -> [])
           | uu___2 -> []) var_elems
  | uu___ -> []
let parse_srx_results (input : Prims.string) :
  (Prims.string Prims.list * (Prims.string * RDF_Graph_Executable.rdf_term)
    Prims.list Prims.list) FStar_Pervasives_Native.option=
  match Parser_XML.parse_xml_document input with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some root ->
      (match root with
       | Parser_XML.XElement (uu___, uu___1, children) ->
           let vars =
             match find_child "head" children with
             | FStar_Pervasives_Native.Some head_node ->
                 parse_head_vars head_node
             | FStar_Pervasives_Native.None -> [] in
           (match find_child "results" children with
            | FStar_Pervasives_Native.Some results_node ->
                (match results_node with
                 | Parser_XML.XElement (uu___2, uu___3, result_children) ->
                     let result_elems =
                       find_children "result" result_children in
                     let rows =
                       FStar_List_Tot_Base.map parse_result_row result_elems in
                     FStar_Pervasives_Native.Some (vars, rows)
                 | uu___2 -> FStar_Pervasives_Native.None)
            | FStar_Pervasives_Native.None ->
                FStar_Pervasives_Native.Some (vars, []))
       | uu___ -> FStar_Pervasives_Native.None)
let parse_srx_boolean (input : Prims.string) :
  Prims.bool FStar_Pervasives_Native.option=
  match Parser_XML.parse_xml_document input with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some root ->
      (match root with
       | Parser_XML.XElement (uu___, uu___1, children) ->
           (match find_child "boolean" children with
            | FStar_Pervasives_Native.Some bool_node ->
                let txt = collect_text bool_node in
                if txt = "true"
                then FStar_Pervasives_Native.Some true
                else
                  if txt = "false"
                  then FStar_Pervasives_Native.Some false
                  else FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
       | uu___ -> FStar_Pervasives_Native.None)
