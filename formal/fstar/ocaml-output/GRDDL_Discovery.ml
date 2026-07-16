open Prims
let grddl_ns : Prims.string= "http://www.w3.org/2003/g/data-view#"
let grddl_profile : Prims.string= "http://www.w3.org/2003/g/data-view"
let rdf_ns : Prims.string= "http://www.w3.org/1999/02/22-rdf-syntax-ns#"
let grddl_testvocab_ns : Prims.string=
  "http://www.w3.org/2001/sw/grddl-wg/td/grddl-test-vocabulary#"
let networked_test_iri : Prims.string=
  "http://www.w3.org/2001/sw/grddl-wg/td/grddl-test-vocabulary#NetworkedTest"
let rule_nstx : Prims.string= "http://www.w3.org/TR/grddl/#rule_nstx"
let rule_profiletrans : Prims.string=
  "http://www.w3.org/TR/grddl/#rule_profiletrans"
let is_networked_type (iri : Prims.string) : Prims.bool=
  iri = networked_test_iri
let is_stage2_rule (iri : Prims.string) : Prims.bool=
  (iri = rule_nstx) || (iri = rule_profiletrans)
let is_ws_char (c : FStar_Char.char) : Prims.bool=
  let n = FStar_Char.int_of_char c in
  (((n = (Prims.of_int (0x20))) || (n = (Prims.of_int (0x09)))) ||
     (n = (Prims.of_int (0x0A))))
    || (n = (Prims.of_int (0x0D)))
let rec split_ws_acc (cs : FStar_Char.char Prims.list)
  (cur : FStar_Char.char Prims.list) (acc : Prims.string Prims.list) :
  Prims.string Prims.list=
  match cs with
  | [] ->
      (match cur with
       | [] -> FStar_List_Tot_Base.rev acc
       | uu___ ->
           FStar_List_Tot_Base.rev
             ((FStar_String.string_of_list (FStar_List_Tot_Base.rev cur)) ::
             acc))
  | c::rest ->
      if is_ws_char c
      then
        (match cur with
         | [] -> split_ws_acc rest [] acc
         | uu___ ->
             split_ws_acc rest []
               ((FStar_String.string_of_list (FStar_List_Tot_Base.rev cur))
               :: acc))
      else split_ws_acc rest (c :: cur) acc
let split_ws (s : Prims.string) : Prims.string Prims.list=
  split_ws_acc (FStar_String.list_of_string s) [] []
let rec ns_map_of_attrs (attrs : Parser_XML.xml_attribute Prims.list) :
  (Prims.string * Prims.string) Prims.list=
  match attrs with
  | [] -> []
  | a::rest ->
      let uu___ = Parser_RDFXML.split_qname a.Parser_XML.attr_name in
      (match uu___ with
       | (pfx, loc) ->
           if (pfx = "xmlns") && (loc <> "")
           then (loc, (a.Parser_XML.attr_value)) :: (ns_map_of_attrs rest)
           else ns_map_of_attrs rest)
let rec find_grddl_attr_val (nsm : (Prims.string * Prims.string) Prims.list)
  (attrs : Parser_XML.xml_attribute Prims.list) :
  Prims.string FStar_Pervasives_Native.option=
  match attrs with
  | [] -> FStar_Pervasives_Native.None
  | a::rest ->
      let uu___ = Parser_RDFXML.split_qname a.Parser_XML.attr_name in
      (match uu___ with
       | (pfx, loc) ->
           if (loc = "transformation") && (pfx <> "")
           then
             (match Parser_RDFXML.lookup_ns pfx nsm with
              | FStar_Pervasives_Native.Some uri ->
                  if (uri = grddl_ns) || (uri = grddl_profile)
                  then FStar_Pervasives_Native.Some (a.Parser_XML.attr_value)
                  else find_grddl_attr_val nsm rest
              | FStar_Pervasives_Native.None -> find_grddl_attr_val nsm rest)
           else find_grddl_attr_val nsm rest)
let find_transformation_attr (root : Parser_XML.xml_node) :
  Prims.string Prims.list=
  let attrs = Parser_XML.element_attrs root in
  let nsm = ns_map_of_attrs attrs in
  match find_grddl_attr_val nsm attrs with
  | FStar_Pervasives_Native.Some v -> split_ws v
  | FStar_Pervasives_Native.None -> []
let local_of (name : Prims.string) : Prims.string=
  let uu___ = Parser_RDFXML.split_qname name in
  match uu___ with | (uu___1, loc) -> if loc = "" then name else loc
let rec find_head_in_node (node : Parser_XML.xml_node) :
  Parser_XML.xml_node FStar_Pervasives_Native.option=
  match node with
  | Parser_XML.XElement (tag, uu___, children) ->
      if (local_of tag) = "head"
      then FStar_Pervasives_Native.Some node
      else find_head_in_list children
  | uu___ -> FStar_Pervasives_Native.None
and find_head_in_list (nodes : Parser_XML.xml_node Prims.list) :
  Parser_XML.xml_node FStar_Pervasives_Native.option=
  match nodes with
  | [] -> FStar_Pervasives_Native.None
  | n::rest ->
      (match find_head_in_node n with
       | FStar_Pervasives_Native.Some h -> FStar_Pervasives_Native.Some h
       | FStar_Pervasives_Native.None -> find_head_in_list rest)
let head_has_grddl_profile (root : Parser_XML.xml_node) : Prims.bool=
  match find_head_in_node root with
  | FStar_Pervasives_Native.Some (Parser_XML.XElement (uu___, attrs, uu___1))
      ->
      (match Parser_XML.find_attr "profile" attrs with
       | FStar_Pervasives_Native.Some pv ->
           FStar_List_Tot_Base.mem grddl_profile (split_ws pv)
       | FStar_Pervasives_Native.None -> false)
  | uu___ -> false
let elt_is_transform_link (node : Parser_XML.xml_node) : Prims.bool=
  match node with
  | Parser_XML.XElement (tag, attrs, uu___) ->
      let ln = local_of tag in
      ((ln = "link") || (ln = "a")) &&
        ((match Parser_XML.find_attr "rel" attrs with
          | FStar_Pervasives_Native.Some rv ->
              FStar_List_Tot_Base.mem "transformation" (split_ws rv)
          | FStar_Pervasives_Native.None -> false))
  | uu___ -> false
let elt_href (node : Parser_XML.xml_node) : Prims.string Prims.list=
  match node with
  | Parser_XML.XElement (uu___, attrs, uu___1) ->
      (match Parser_XML.find_attr "href" attrs with
       | FStar_Pervasives_Native.Some h -> [h]
       | FStar_Pervasives_Native.None -> [])
  | uu___ -> []
let rec collect_links_node (node : Parser_XML.xml_node) :
  Prims.string Prims.list=
  let here = if elt_is_transform_link node then elt_href node else [] in
  match node with
  | Parser_XML.XElement (uu___, uu___1, children) ->
      FStar_List_Tot_Base.op_At here (collect_links_list children)
  | uu___ -> here
and collect_links_list (nodes : Parser_XML.xml_node Prims.list) :
  Prims.string Prims.list=
  match nodes with
  | [] -> []
  | n::rest ->
      FStar_List_Tot_Base.op_At (collect_links_node n)
        (collect_links_list rest)
let find_xhtml_transformation_links (root : Parser_XML.xml_node) :
  Prims.string Prims.list=
  if head_has_grddl_profile root then collect_links_node root else []
let effective_base (fallback : Prims.string) (root : Parser_XML.xml_node) :
  Prims.string=
  match Parser_XML.find_attr "xml:base" (Parser_XML.element_attrs root) with
  | FStar_Pervasives_Native.Some b -> Parser_RDFXML.resolve_iri fallback b
  | FStar_Pervasives_Native.None -> fallback
let rec resolve_all (base : Prims.string) (refs : Prims.string Prims.list) :
  Prims.string Prims.list=
  match refs with
  | [] -> []
  | r::rest -> (Parser_RDFXML.resolve_iri base r) :: (resolve_all base rest)
let discover_transformations (fallback_base : Prims.string)
  (root : Parser_XML.xml_node) : Prims.string Prims.list=
  let base = effective_base fallback_base root in
  let raw =
    FStar_List_Tot_Base.op_At (find_transformation_attr root)
      (find_xhtml_transformation_links root) in
  resolve_all base raw
let rec find_base_href_in_list (nodes : Parser_XML.xml_node Prims.list) :
  Prims.string FStar_Pervasives_Native.option=
  match nodes with
  | [] -> FStar_Pervasives_Native.None
  | n::rest ->
      (match n with
       | Parser_XML.XElement (tag, attrs, uu___) ->
           if (local_of tag) = "base"
           then
             (match Parser_XML.find_attr "href" attrs with
              | FStar_Pervasives_Native.Some h ->
                  FStar_Pervasives_Native.Some h
              | FStar_Pervasives_Native.None -> find_base_href_in_list rest)
           else find_base_href_in_list rest
       | uu___ -> find_base_href_in_list rest)
let html_base_href (root : Parser_XML.xml_node) :
  Prims.string FStar_Pervasives_Native.option=
  match find_head_in_node root with
  | FStar_Pervasives_Native.Some (Parser_XML.XElement
      (uu___, uu___1, children)) -> find_base_href_in_list children
  | uu___ -> FStar_Pervasives_Native.None
let doc_base (fallback : Prims.string) (root : Parser_XML.xml_node) :
  Prims.string=
  match html_base_href root with
  | FStar_Pervasives_Native.Some b -> Parser_RDFXML.resolve_iri fallback b
  | FStar_Pervasives_Native.None -> effective_base fallback root
let head_custom_profile_uris (fallback : Prims.string)
  (root : Parser_XML.xml_node) : Prims.string Prims.list=
  let base = doc_base fallback root in
  match find_head_in_node root with
  | FStar_Pervasives_Native.Some (Parser_XML.XElement (uu___, attrs, uu___1))
      ->
      (match Parser_XML.find_attr "profile" attrs with
       | FStar_Pervasives_Native.Some pv ->
           resolve_all base
             (FStar_List_Tot_Base.filter (fun u -> u <> grddl_profile)
                (split_ws pv))
       | FStar_Pervasives_Native.None -> [])
  | uu___ -> []
let elt_is_profiletx_link (node : Parser_XML.xml_node) : Prims.bool=
  match node with
  | Parser_XML.XElement (tag, attrs, uu___) ->
      let ln = local_of tag in
      ((ln = "link") || (ln = "a")) &&
        ((match Parser_XML.find_attr "rel" attrs with
          | FStar_Pervasives_Native.Some rv ->
              FStar_List_Tot_Base.mem "profileTransformation" (split_ws rv)
          | FStar_Pervasives_Native.None -> false))
  | uu___ -> false
let rec collect_profiletx_node (node : Parser_XML.xml_node) :
  Prims.string Prims.list=
  let here = if elt_is_profiletx_link node then elt_href node else [] in
  match node with
  | Parser_XML.XElement (uu___, uu___1, children) ->
      FStar_List_Tot_Base.op_At here (collect_profiletx_list children)
  | uu___ -> here
and collect_profiletx_list (nodes : Parser_XML.xml_node Prims.list) :
  Prims.string Prims.list=
  match nodes with
  | [] -> []
  | n::rest ->
      FStar_List_Tot_Base.op_At (collect_profiletx_node n)
        (collect_profiletx_list rest)
let profile_doc_transformations (profile_iri : Prims.string)
  (profile_doc : Parser_XML.xml_node) : Prims.string Prims.list=
  if head_has_grddl_profile profile_doc
  then
    resolve_all (doc_base profile_iri profile_doc)
      (collect_profiletx_node profile_doc)
  else []
let root_namespace_uri (root : Parser_XML.xml_node) :
  Prims.string FStar_Pervasives_Native.option=
  match root with
  | Parser_XML.XElement (tag, attrs, uu___) ->
      let uu___1 = Parser_RDFXML.split_qname tag in
      (match uu___1 with
       | (pfx, uu___2) ->
           if pfx = ""
           then Parser_XML.find_attr "xmlns" attrs
           else Parser_RDFXML.lookup_ns pfx (ns_map_of_attrs attrs))
  | uu___ -> FStar_Pervasives_Native.None
let elt_ns_transform (node : Parser_XML.xml_node) : Prims.string Prims.list=
  match node with
  | Parser_XML.XElement (tag, attrs, uu___) ->
      if (local_of tag) = "namespaceTransformation"
      then
        (match Parser_XML.find_attr "rdf:resource" attrs with
         | FStar_Pervasives_Native.Some r -> [r]
         | FStar_Pervasives_Native.None -> [])
      else []
  | uu___ -> []
let rec collect_nstx_node (node : Parser_XML.xml_node) :
  Prims.string Prims.list=
  let here = elt_ns_transform node in
  match node with
  | Parser_XML.XElement (uu___, uu___1, children) ->
      FStar_List_Tot_Base.op_At here (collect_nstx_list children)
  | uu___ -> here
and collect_nstx_list (nodes : Parser_XML.xml_node Prims.list) :
  Prims.string Prims.list=
  match nodes with
  | [] -> []
  | n::rest ->
      FStar_List_Tot_Base.op_At (collect_nstx_node n)
        (collect_nstx_list rest)
let namespace_doc_transformations (ns_iri : Prims.string)
  (ns_doc : Parser_XML.xml_node) : Prims.string Prims.list=
  resolve_all (doc_base ns_iri ns_doc) (collect_nstx_node ns_doc)
let is_rdfxml_root (root : Parser_XML.xml_node) : Prims.bool=
  match root with
  | Parser_XML.XElement (tag, attrs, uu___) ->
      let uu___1 = Parser_RDFXML.split_qname tag in
      (match uu___1 with
       | (pfx, loc) ->
           (loc = "RDF") &&
             ((match Parser_RDFXML.lookup_ns pfx (ns_map_of_attrs attrs) with
               | FStar_Pervasives_Native.Some uri -> uri = rdf_ns
               | FStar_Pervasives_Native.None -> false)))
  | uu___ -> false
let rdfxml_base_triples (base : Prims.string) (root : Parser_XML.xml_node)
  (input : Prims.string) : RDF_Triple.triple Prims.list=
  if is_rdfxml_root root
  then Parser_RDFXML.parse_rdfxml_with_base base input
  else []
let grddl_apply (base : Prims.string) (stylesheet : Parser_XML.xml_node)
  (source : Parser_XML.xml_node) :
  RDF_Triple.triple Prims.list FStar_Pervasives_Native.option=
  let out = XSLT_Transform.transform stylesheet source in
  Parser_RDFXML.parse_rdfxml_with_base_strict base out
let rec grddl_apply_all (base : Prims.string)
  (styles : Parser_XML.xml_node Prims.list) (source : Parser_XML.xml_node) :
  RDF_Triple.triple Prims.list=
  match styles with
  | [] -> []
  | s::rest ->
      let ts =
        match grddl_apply base s source with
        | FStar_Pervasives_Native.Some t -> t
        | FStar_Pervasives_Native.None ->
            Parser_RDFXML.parse_rdfxml_with_base base
              (XSLT_Transform.transform s source) in
      FStar_List_Tot_Base.op_At ts (grddl_apply_all base rest source)
let grddl_result (base : Prims.string) (root : Parser_XML.xml_node)
  (input : Prims.string) (styles : Parser_XML.xml_node Prims.list) :
  RDF_Triple.triple Prims.list=
  FStar_List_Tot_Base.op_At (rdfxml_base_triples base root input)
    (grddl_apply_all base styles root)
let rec triple_mem (t : RDF_Triple.triple)
  (ts : RDF_Triple.triple Prims.list) : Prims.bool=
  match ts with
  | [] -> false
  | h::r -> if RDF_Triple.triple_eq t h then true else triple_mem t r
let rec dedup_triples (ts : RDF_Triple.triple Prims.list) :
  RDF_Triple.triple Prims.list=
  match ts with
  | [] -> []
  | h::r -> let d = dedup_triples r in if triple_mem h d then d else h :: d
let graph_to_canonical_nquads (ts : RDF_Triple.triple Prims.list) :
  Prims.string=
  RDF_Canonical.canonicalize_to_nquads
    { RDF_Graph.ds_default = (dedup_triples ts); RDF_Graph.ds_named = [] }
let graphs_isomorphic (g1 : RDF_Triple.triple Prims.list)
  (g2 : RDF_Triple.triple Prims.list) : Prims.bool=
  (graph_to_canonical_nquads g1) = (graph_to_canonical_nquads g2)
