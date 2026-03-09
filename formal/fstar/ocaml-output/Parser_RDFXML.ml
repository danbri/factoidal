open Prims
let rdf_ns : Prims.string= "http://www.w3.org/1999/02/22-rdf-syntax-ns#"
let rdfs_ns : Prims.string= "http://www.w3.org/2000/01/rdf-schema#"
let xml_ns : Prims.string= "http://www.w3.org/XML/1998/namespace"
let xmlns_ns : Prims.string= "http://www.w3.org/2000/xmlns/"
let xsd_ns : Prims.string= "http://www.w3.org/2001/XMLSchema#"
let rdf_type_iri : Prims.string=
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#type"
let rdf_first_iri : Prims.string=
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#first"
let rdf_rest_iri : Prims.string=
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#rest"
let rdf_nil_iri : Prims.string=
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#nil"
let rdf_xmlliteral_iri : Prims.string=
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#XMLLiteral"
type rdfxml_state =
  {
  base_iri: Prims.string ;
  namespaces: (Prims.string * Prims.string) Prims.list ;
  lang: Prims.string FStar_Pervasives_Native.option ;
  bnode_counter: Prims.nat ;
  li_counter: Prims.nat ;
  errors: Prims.string Prims.list ;
  seen_ids: Prims.string Prims.list }
let __proj__Mkrdfxml_state__item__base_iri (projectee : rdfxml_state) :
  Prims.string=
  match projectee with
  | { base_iri; namespaces; lang; bnode_counter; li_counter; errors;
      seen_ids;_} -> base_iri
let __proj__Mkrdfxml_state__item__namespaces (projectee : rdfxml_state) :
  (Prims.string * Prims.string) Prims.list=
  match projectee with
  | { base_iri; namespaces; lang; bnode_counter; li_counter; errors;
      seen_ids;_} -> namespaces
let __proj__Mkrdfxml_state__item__lang (projectee : rdfxml_state) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | { base_iri; namespaces; lang; bnode_counter; li_counter; errors;
      seen_ids;_} -> lang
let __proj__Mkrdfxml_state__item__bnode_counter (projectee : rdfxml_state) :
  Prims.nat=
  match projectee with
  | { base_iri; namespaces; lang; bnode_counter; li_counter; errors;
      seen_ids;_} -> bnode_counter
let __proj__Mkrdfxml_state__item__li_counter (projectee : rdfxml_state) :
  Prims.nat=
  match projectee with
  | { base_iri; namespaces; lang; bnode_counter; li_counter; errors;
      seen_ids;_} -> li_counter
let __proj__Mkrdfxml_state__item__errors (projectee : rdfxml_state) :
  Prims.string Prims.list=
  match projectee with
  | { base_iri; namespaces; lang; bnode_counter; li_counter; errors;
      seen_ids;_} -> errors
let __proj__Mkrdfxml_state__item__seen_ids (projectee : rdfxml_state) :
  Prims.string Prims.list=
  match projectee with
  | { base_iri; namespaces; lang; bnode_counter; li_counter; errors;
      seen_ids;_} -> seen_ids
let initial_state (base : Prims.string) : rdfxml_state=
  {
    base_iri = base;
    namespaces =
      [("rdf", rdf_ns);
      ("rdfs", rdfs_ns);
      ("xml", xml_ns);
      ("xmlns", xmlns_ns);
      ("xsd", xsd_ns)];
    lang = FStar_Pervasives_Native.None;
    bnode_counter = Prims.int_zero;
    li_counter = Prims.int_one;
    errors = [];
    seen_ids = []
  }
let add_error (st : rdfxml_state) (msg : Prims.string) : rdfxml_state=
  {
    base_iri = (st.base_iri);
    namespaces = (st.namespaces);
    lang = (st.lang);
    bnode_counter = (st.bnode_counter);
    li_counter = (st.li_counter);
    errors = (msg :: (st.errors));
    seen_ids = (st.seen_ids)
  }
let has_errors (st : rdfxml_state) : Prims.bool=
  match st.errors with | [] -> false | uu___ -> true
let fresh_bnode (st : rdfxml_state) : (Prims.string * rdfxml_state)=
  let id =
    FStar_String.concat ""
      ["_:rdfxml_b"; Prims.string_of_int st.bnode_counter] in
  (id,
    {
      base_iri = (st.base_iri);
      namespaces = (st.namespaces);
      lang = (st.lang);
      bnode_counter = (st.bnode_counter + Prims.int_one);
      li_counter = (st.li_counter);
      errors = (st.errors);
      seen_ids = (st.seen_ids)
    })
let reset_li_counter (st : rdfxml_state) : rdfxml_state=
  {
    base_iri = (st.base_iri);
    namespaces = (st.namespaces);
    lang = (st.lang);
    bnode_counter = (st.bnode_counter);
    li_counter = Prims.int_one;
    errors = (st.errors);
    seen_ids = (st.seen_ids)
  }
let next_li (st : rdfxml_state) : (Prims.string * rdfxml_state)=
  let prop =
    FStar_String.concat "" [rdf_ns; "_"; Prims.string_of_int st.li_counter] in
  (prop,
    {
      base_iri = (st.base_iri);
      namespaces = (st.namespaces);
      lang = (st.lang);
      bnode_counter = (st.bnode_counter);
      li_counter = (st.li_counter + Prims.int_one);
      errors = (st.errors);
      seen_ids = (st.seen_ids)
    })
let rec find_colon_pos_in_list (cs : FStar_Char.char Prims.list)
  (idx : Prims.nat) : Prims.nat FStar_Pervasives_Native.option=
  match cs with
  | [] -> FStar_Pervasives_Native.None
  | c::rest ->
      if (FStar_Char.int_of_char c) = (Prims.of_int (0x3A))
      then FStar_Pervasives_Native.Some idx
      else find_colon_pos_in_list rest (idx + Prims.int_one)
let find_colon_pos (s : Prims.string) :
  Prims.nat FStar_Pervasives_Native.option=
  find_colon_pos_in_list (FStar_String.list_of_string s) Prims.int_zero
let split_qname (name : Prims.string) : (Prims.string * Prims.string)=
  match find_colon_pos name with
  | FStar_Pervasives_Native.Some pos ->
      let len = FStar_String.strlen name in
      if pos = Prims.int_zero
      then ("", name)
      else
        if (pos + Prims.int_one) >= len
        then ((FStar_String.sub name Prims.int_zero pos), "")
        else
          ((FStar_String.sub name Prims.int_zero pos),
            (FStar_String.sub name (pos + Prims.int_one)
               ((len - pos) - Prims.int_one)))
  | FStar_Pervasives_Native.None -> ("", name)
let rec lookup_ns (prefix : Prims.string)
  (nss : (Prims.string * Prims.string) Prims.list) :
  Prims.string FStar_Pervasives_Native.option=
  match nss with
  | [] -> FStar_Pervasives_Native.None
  | (p, uri)::rest ->
      if p = prefix
      then FStar_Pervasives_Native.Some uri
      else lookup_ns prefix rest
let resolve_qname (st : rdfxml_state) (name : Prims.string) :
  Prims.string FStar_Pervasives_Native.option=
  let uu___ = split_qname name in
  match uu___ with
  | (prefix, local) ->
      (match lookup_ns prefix st.namespaces with
       | FStar_Pervasives_Native.Some ns_iri ->
           FStar_Pervasives_Native.Some
             (FStar_String.concat "" [ns_iri; local])
       | FStar_Pervasives_Native.None ->
           (match find_colon_pos name with
            | FStar_Pervasives_Native.Some uu___1 ->
                FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None))
let is_ncname_start_char (code : Prims.nat) : Prims.bool=
  ((((code >= (Prims.of_int (0x41))) && (code <= (Prims.of_int (0x5A)))) ||
      (code = (Prims.of_int (0x5F))))
     || ((code >= (Prims.of_int (0x61))) && (code <= (Prims.of_int (0x7A)))))
    || (code >= (Prims.of_int (0x80)))
let is_ncname_char (code : Prims.nat) : Prims.bool=
  ((((((is_ncname_start_char code) || (code = (Prims.of_int (0x2D)))) ||
        (code = (Prims.of_int (0x2E))))
       ||
       ((code >= (Prims.of_int (0x30))) && (code <= (Prims.of_int (0x39)))))
      || (code = (Prims.of_int (0xB7))))
     ||
     ((code >= (Prims.of_int (0x300))) && (code <= (Prims.of_int (0x36F)))))
    ||
    ((code >= (Prims.of_int (0x203F))) && (code <= (Prims.of_int (0x2040))))
let is_valid_ncname (s : Prims.string) : Prims.bool=
  let chars = FStar_String.list_of_string s in
  match chars with
  | [] -> false
  | first::rest ->
      let first_code = FStar_Char.int_of_char first in
      if Prims.op_Negation (is_ncname_start_char first_code)
      then false
      else
        (let rec check_rest cs =
           match cs with
           | [] -> true
           | c::tl ->
               let code = FStar_Char.int_of_char c in
               if code = (Prims.of_int (0x3A))
               then false
               else if is_ncname_char code then check_rest tl else false in
         check_rest rest)
let is_forbidden_node_element_name (full_iri : Prims.string) : Prims.bool=
  ((((((((((full_iri = (FStar_String.concat "" [rdf_ns; "RDF"])) ||
             (full_iri = (FStar_String.concat "" [rdf_ns; "ID"])))
            || (full_iri = (FStar_String.concat "" [rdf_ns; "about"])))
           || (full_iri = (FStar_String.concat "" [rdf_ns; "bagID"])))
          || (full_iri = (FStar_String.concat "" [rdf_ns; "parseType"])))
         || (full_iri = (FStar_String.concat "" [rdf_ns; "resource"])))
        || (full_iri = (FStar_String.concat "" [rdf_ns; "nodeID"])))
       || (full_iri = (FStar_String.concat "" [rdf_ns; "datatype"])))
      || (full_iri = (FStar_String.concat "" [rdf_ns; "li"])))
     || (full_iri = (FStar_String.concat "" [rdf_ns; "aboutEach"])))
    || (full_iri = (FStar_String.concat "" [rdf_ns; "aboutEachPrefix"]))
let is_forbidden_property_element_name (full_iri : Prims.string) :
  Prims.bool=
  ((((((((((full_iri = (FStar_String.concat "" [rdf_ns; "Description"])) ||
             (full_iri = (FStar_String.concat "" [rdf_ns; "RDF"])))
            || (full_iri = (FStar_String.concat "" [rdf_ns; "ID"])))
           || (full_iri = (FStar_String.concat "" [rdf_ns; "about"])))
          || (full_iri = (FStar_String.concat "" [rdf_ns; "bagID"])))
         || (full_iri = (FStar_String.concat "" [rdf_ns; "parseType"])))
        || (full_iri = (FStar_String.concat "" [rdf_ns; "resource"])))
       || (full_iri = (FStar_String.concat "" [rdf_ns; "nodeID"])))
      || (full_iri = (FStar_String.concat "" [rdf_ns; "datatype"])))
     || (full_iri = (FStar_String.concat "" [rdf_ns; "aboutEach"])))
    || (full_iri = (FStar_String.concat "" [rdf_ns; "aboutEachPrefix"]))
let is_forbidden_property_attribute_name (full_iri : Prims.string) :
  Prims.bool= full_iri = (FStar_String.concat "" [rdf_ns; "li"])
let rec has_scheme_chars (cs : FStar_Char.char Prims.list)
  (depth : Prims.nat) : Prims.bool=
  if depth > (Prims.of_int (20))
  then false
  else
    (match cs with
     | [] -> false
     | c::rest ->
         let code = FStar_Char.int_of_char c in
         if code = (Prims.of_int (0x3A))
         then
           (match rest with
            | c2::c3::uu___1 ->
                ((FStar_Char.int_of_char c2) = (Prims.of_int (0x2F))) &&
                  ((FStar_Char.int_of_char c3) = (Prims.of_int (0x2F)))
            | uu___1 -> false)
         else
           if
             ((((((code >= (Prims.of_int (0x61))) &&
                    (code <= (Prims.of_int (0x7A))))
                   ||
                   ((code >= (Prims.of_int (0x41))) &&
                      (code <= (Prims.of_int (0x5A)))))
                  ||
                  ((code >= (Prims.of_int (0x30))) &&
                     (code <= (Prims.of_int (0x39)))))
                 || (code = (Prims.of_int (0x2B))))
                || (code = (Prims.of_int (0x2D))))
               || (code = (Prims.of_int (0x2E)))
           then has_scheme_chars rest (depth + Prims.int_one)
           else false)
let is_absolute_iri (s : Prims.string) : Prims.bool=
  has_scheme_chars (FStar_String.list_of_string s) Prims.int_zero
let strip_fragment (s : Prims.string) : Prims.string=
  let chars = FStar_String.list_of_string s in
  let rec take_before_hash cs acc =
    match cs with
    | [] -> FStar_List_Tot_Base.rev acc
    | c::rest ->
        if (FStar_Char.int_of_char c) = (Prims.of_int (0x23))
        then FStar_List_Tot_Base.rev acc
        else take_before_hash rest (c :: acc) in
  FStar_String.string_of_list (take_before_hash chars [])
let get_scheme_authority (s : Prims.string) : Prims.string=
  let chars = FStar_String.list_of_string s in
  let rec find_scheme_end cs idx =
    match cs with
    | [] -> FStar_Pervasives_Native.None
    | c::rest ->
        if (FStar_Char.int_of_char c) = (Prims.of_int (0x3A))
        then
          (match rest with
           | c2::c3::uu___ ->
               if
                 ((FStar_Char.int_of_char c2) = (Prims.of_int (0x2F))) &&
                   ((FStar_Char.int_of_char c3) = (Prims.of_int (0x2F)))
               then FStar_Pervasives_Native.Some (idx + (Prims.of_int (3)))
               else find_scheme_end rest (idx + Prims.int_one)
           | uu___ -> FStar_Pervasives_Native.None)
        else find_scheme_end rest (idx + Prims.int_one) in
  match find_scheme_end chars Prims.int_zero with
  | FStar_Pervasives_Native.None -> s
  | FStar_Pervasives_Native.Some auth_start ->
      let len = FStar_String.strlen s in
      let rec find_path_start idx =
        if idx >= len
        then len
        else
          (let c = FStar_String.index s idx in
           if (FStar_Char.int_of_char c) = (Prims.of_int (0x2F))
           then idx
           else find_path_start (idx + Prims.int_one)) in
      let path_start = find_path_start auth_start in
      if path_start <= len
      then FStar_String.sub s Prims.int_zero path_start
      else s
let get_path (s : Prims.string) : Prims.string=
  let chars = FStar_String.list_of_string s in
  let rec find_auth_end cs idx =
    match cs with
    | [] -> Prims.int_zero
    | c::rest ->
        if (FStar_Char.int_of_char c) = (Prims.of_int (0x3A))
        then
          (match rest with
           | c2::c3::uu___ ->
               if
                 ((FStar_Char.int_of_char c2) = (Prims.of_int (0x2F))) &&
                   ((FStar_Char.int_of_char c3) = (Prims.of_int (0x2F)))
               then idx + (Prims.of_int (3))
               else find_auth_end rest (idx + Prims.int_one)
           | uu___ -> idx + Prims.int_one)
        else find_auth_end rest (idx + Prims.int_one) in
  let auth_end = find_auth_end chars Prims.int_zero in
  let len = FStar_String.strlen s in
  let rec find_path_start idx =
    if idx >= len
    then len
    else
      (let c = FStar_String.index s idx in
       if (FStar_Char.int_of_char c) = (Prims.of_int (0x2F))
       then idx
       else find_path_start (idx + Prims.int_one)) in
  let path_start = find_path_start auth_end in
  if path_start < len
  then FStar_String.sub s path_start (len - path_start)
  else "/"
let merge_paths (base : Prims.string) (rel : Prims.string) : Prims.string=
  let base_no_frag = strip_fragment base in
  let sa = get_scheme_authority base_no_frag in
  let base_path = get_path base_no_frag in
  let base_path_chars = FStar_String.list_of_string base_path in
  let rec take_up_to_last_slash cs best current =
    match cs with
    | [] -> best
    | c::rest ->
        let new_current = FStar_List_Tot_Base.op_At current [c] in
        if (FStar_Char.int_of_char c) = (Prims.of_int (0x2F))
        then take_up_to_last_slash rest new_current new_current
        else take_up_to_last_slash rest best new_current in
  let prefix = take_up_to_last_slash base_path_chars [] [] in
  FStar_String.concat "" [sa; FStar_String.string_of_list prefix; rel]
let remove_dot_segments (path : Prims.string) : Prims.string=
  let segments =
    let chars = FStar_String.list_of_string path in
    let rec split_on_slash cs current acc =
      match cs with
      | [] ->
          FStar_List_Tot_Base.rev
            ((FStar_String.string_of_list (FStar_List_Tot_Base.rev current))
            :: acc)
      | c::rest ->
          if (FStar_Char.int_of_char c) = (Prims.of_int (0x2F))
          then
            split_on_slash rest []
              ((FStar_String.string_of_list (FStar_List_Tot_Base.rev current))
              :: acc)
          else split_on_slash rest (c :: current) acc in
    split_on_slash chars [] [] in
  let rec process segs out =
    match segs with
    | [] -> FStar_List_Tot_Base.rev out
    | seg::rest ->
        if seg = "."
        then process rest out
        else
          if seg = ".."
          then
            (let new_out = match out with | [] -> [] | uu___1::tl -> tl in
             process rest new_out)
          else process rest (seg :: out) in
  let result_segs = process segments [] in
  let joined = FStar_String.concat "/" result_segs in
  let chars0 = FStar_String.list_of_string path in
  match chars0 with
  | c::uu___ ->
      if (FStar_Char.int_of_char c) = (Prims.of_int (0x2F))
      then
        (if (FStar_String.strlen joined) > Prims.int_zero
         then
           let jc0 = FStar_String.list_of_string joined in
           match jc0 with
           | c2::uu___1 ->
               (if (FStar_Char.int_of_char c2) = (Prims.of_int (0x2F))
                then joined
                else FStar_String.concat "" ["/"; joined])
           | [] -> "/"
         else "/")
      else joined
  | [] -> joined
let resolve_iri (base : Prims.string) (rel : Prims.string) : Prims.string=
  if (FStar_String.strlen rel) = Prims.int_zero
  then strip_fragment base
  else
    if is_absolute_iri rel
    then rel
    else
      (let base_no_frag = strip_fragment base in
       let chars = FStar_String.list_of_string rel in
       match chars with
       | c::uu___2 ->
           if (FStar_Char.int_of_char c) = (Prims.of_int (0x23))
           then FStar_String.concat "" [base_no_frag; rel]
           else
             if (FStar_Char.int_of_char c) = (Prims.of_int (0x2F))
             then
               (match chars with
                | uu___4::c2::uu___5 ->
                    if (FStar_Char.int_of_char c2) = (Prims.of_int (0x2F))
                    then
                      let base_chars =
                        FStar_String.list_of_string base_no_frag in
                      let rec take_scheme bcs acc =
                        match bcs with
                        | [] -> ""
                        | bc::brest ->
                            if
                              (FStar_Char.int_of_char bc) =
                                (Prims.of_int (0x3A))
                            then
                              FStar_String.string_of_list
                                (FStar_List_Tot_Base.rev (bc :: acc))
                            else take_scheme brest (bc :: acc) in
                      let scheme = take_scheme base_chars [] in
                      FStar_String.concat "" [scheme; rel]
                    else
                      (let sa = get_scheme_authority base_no_frag in
                       let resolved_path = remove_dot_segments rel in
                       FStar_String.concat "" [sa; resolved_path])
                | uu___4 ->
                    let sa = get_scheme_authority base_no_frag in
                    FStar_String.concat "" [sa; rel])
             else
               (let merged = merge_paths base_no_frag rel in
                let sa = get_scheme_authority merged in
                let merged_path = get_path merged in
                let clean_path = remove_dot_segments merged_path in
                FStar_String.concat "" [sa; clean_path])
       | [] -> base_no_frag)
let rec extract_namespaces (attrs : Parser_XML.xml_attribute Prims.list)
  (nss : (Prims.string * Prims.string) Prims.list) :
  (Prims.string * Prims.string) Prims.list=
  match attrs with
  | [] -> nss
  | attr::rest ->
      let uu___ = split_qname attr.Parser_XML.attr_name in
      (match uu___ with
       | (prefix, local) ->
           if
             (prefix = "xmlns") &&
               ((FStar_String.strlen local) > Prims.int_zero)
           then
             extract_namespaces rest ((local, (attr.Parser_XML.attr_value))
               :: nss)
           else
             if attr.Parser_XML.attr_name = "xmlns"
             then
               extract_namespaces rest (("", (attr.Parser_XML.attr_value)) ::
                 nss)
             else extract_namespaces rest nss)
let extract_lang (attrs : Parser_XML.xml_attribute Prims.list)
  (current_lang : Prims.string FStar_Pervasives_Native.option) :
  Prims.string FStar_Pervasives_Native.option=
  match Parser_XML.find_attr "xml:lang" attrs with
  | FStar_Pervasives_Native.Some lang_val ->
      if (FStar_String.strlen lang_val) = Prims.int_zero
      then FStar_Pervasives_Native.None
      else FStar_Pervasives_Native.Some lang_val
  | FStar_Pervasives_Native.None -> current_lang
let extract_base (attrs : Parser_XML.xml_attribute Prims.list)
  (current_base : Prims.string) : Prims.string=
  match Parser_XML.find_attr "xml:base" attrs with
  | FStar_Pervasives_Native.Some base_val ->
      resolve_iri current_base base_val
  | FStar_Pervasives_Native.None -> current_base
let update_state_from_attrs (st : rdfxml_state)
  (attrs : Parser_XML.xml_attribute Prims.list) : rdfxml_state=
  let new_nss = extract_namespaces attrs st.namespaces in
  let new_lang = extract_lang attrs st.lang in
  let new_base = extract_base attrs st.base_iri in
  {
    base_iri = new_base;
    namespaces = new_nss;
    lang = new_lang;
    bnode_counter = (st.bnode_counter);
    li_counter = (st.li_counter);
    errors = (st.errors);
    seen_ids = (st.seen_ids)
  }
let resolve_name (st : rdfxml_state) (name : Prims.string) :
  Prims.string FStar_Pervasives_Native.option=
  let uu___ = split_qname name in
  match uu___ with
  | (prefix, local) ->
      if (FStar_String.strlen prefix) > Prims.int_zero
      then
        (match lookup_ns prefix st.namespaces with
         | FStar_Pervasives_Native.Some ns_iri ->
             FStar_Pervasives_Native.Some
               (FStar_String.concat "" [ns_iri; local])
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
      else
        (match lookup_ns "" st.namespaces with
         | FStar_Pervasives_Native.Some ns_iri ->
             FStar_Pervasives_Native.Some
               (FStar_String.concat "" [ns_iri; name])
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
let is_rdf_syntax_attr (full_iri : Prims.string) : Prims.bool=
  (((((((((full_iri = (FStar_String.concat "" [rdf_ns; "about"])) ||
            (full_iri = (FStar_String.concat "" [rdf_ns; "ID"])))
           || (full_iri = (FStar_String.concat "" [rdf_ns; "resource"])))
          || (full_iri = (FStar_String.concat "" [rdf_ns; "datatype"])))
         || (full_iri = (FStar_String.concat "" [rdf_ns; "nodeID"])))
        || (full_iri = (FStar_String.concat "" [rdf_ns; "parseType"])))
       || (full_iri = (FStar_String.concat "" [rdf_ns; "about"])))
      || (full_iri = (FStar_String.concat "" [rdf_ns; "RDF"])))
     || (full_iri = (FStar_String.concat "" [rdf_ns; "Description"])))
    || (full_iri = (FStar_String.concat "" [rdf_ns; "li"]))
let is_xml_or_xmlns_attr (name : Prims.string) : Prims.bool=
  let uu___ = split_qname name in
  match uu___ with
  | (prefix, _local) ->
      ((prefix = "xml") || (prefix = "xmlns")) || (name = "xmlns")
let make_wf_iri (s : Prims.string) :
  RDF_Graph_Executable.wf_iri FStar_Pervasives_Native.option=
  if RDF_Graph_Executable.is_iri s
  then FStar_Pervasives_Native.Some s
  else FStar_Pervasives_Native.None
let make_iri_subject (iri_str : Prims.string) :
  RDF_Graph_Executable.subject FStar_Pervasives_Native.option=
  if RDF_Graph_Executable.is_iri iri_str
  then FStar_Pervasives_Native.Some (RDF_Graph_Executable.S_IRI iri_str)
  else FStar_Pervasives_Native.None
let make_bnode_subject (id : Prims.string) : RDF_Graph_Executable.subject=
  RDF_Graph_Executable.S_BNode id
let make_iri_object (iri_str : Prims.string) :
  RDF_Graph_Executable.rdf_term FStar_Pervasives_Native.option=
  if RDF_Graph_Executable.is_iri iri_str
  then FStar_Pervasives_Native.Some (RDF_Graph_Executable.T_IRI iri_str)
  else FStar_Pervasives_Native.None
let make_plain_literal (lex : Prims.string)
  (lang : Prims.string FStar_Pervasives_Native.option) :
  RDF_Graph_Executable.rdf_term FStar_Pervasives_Native.option=
  match lang with
  | FStar_Pervasives_Native.Some l ->
      FStar_Pervasives_Native.Some
        (RDF_Graph_Executable.T_Literal
           {
             RDF_Graph_Executable.lexical_form = lex;
             RDF_Graph_Executable.datatype =
               RDF_Graph_Executable.rdf_lang_string;
             RDF_Graph_Executable.lang_tag = (FStar_Pervasives_Native.Some l)
           })
  | FStar_Pervasives_Native.None ->
      FStar_Pervasives_Native.Some
        (RDF_Graph_Executable.T_Literal
           {
             RDF_Graph_Executable.lexical_form = lex;
             RDF_Graph_Executable.datatype = RDF_Graph_Executable.xsd_string;
             RDF_Graph_Executable.lang_tag = FStar_Pervasives_Native.None
           })
let make_typed_literal (lex : Prims.string) (dt : Prims.string) :
  RDF_Graph_Executable.rdf_term FStar_Pervasives_Native.option=
  if RDF_Graph_Executable.is_iri dt
  then
    (if dt = "http://www.w3.org/1999/02/22-rdf-syntax-ns#langString"
     then FStar_Pervasives_Native.None
     else
       FStar_Pervasives_Native.Some
         (RDF_Graph_Executable.T_Literal
            {
              RDF_Graph_Executable.lexical_form = lex;
              RDF_Graph_Executable.datatype = dt;
              RDF_Graph_Executable.lang_tag = FStar_Pervasives_Native.None
            }))
  else FStar_Pervasives_Native.None
let make_triple (subj : RDF_Graph_Executable.subject)
  (pred_iri : Prims.string) (obj : RDF_Graph_Executable.rdf_term) :
  RDF_Graph_Executable.triple FStar_Pervasives_Native.option=
  if RDF_Graph_Executable.is_iri pred_iri
  then
    FStar_Pervasives_Native.Some
      {
        RDF_Graph_Executable.s = subj;
        RDF_Graph_Executable.p = pred_iri;
        RDF_Graph_Executable.o = obj
      }
  else FStar_Pervasives_Native.None
let rdf_statement_iri : Prims.string=
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#Statement"
let rdf_subject_iri : Prims.string=
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#subject"
let rdf_predicate_iri : Prims.string=
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#predicate"
let rdf_object_iri : Prims.string=
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#object"
let make_reification_triples (reif_iri : Prims.string)
  (subj : RDF_Graph_Executable.subject) (pred_iri : Prims.string)
  (obj : RDF_Graph_Executable.rdf_term) :
  RDF_Graph_Executable.triple Prims.list=
  if Prims.op_Negation (RDF_Graph_Executable.is_iri reif_iri)
  then []
  else
    if
      Prims.op_Negation
        ((((((RDF_Graph_Executable.is_iri rdf_type_iri) &&
               (RDF_Graph_Executable.is_iri rdf_statement_iri))
              && (RDF_Graph_Executable.is_iri rdf_subject_iri))
             && (RDF_Graph_Executable.is_iri rdf_predicate_iri))
            && (RDF_Graph_Executable.is_iri rdf_object_iri))
           && (RDF_Graph_Executable.is_iri pred_iri))
    then []
    else
      (let reif_subj = RDF_Graph_Executable.S_IRI reif_iri in
       let subj_term =
         match subj with
         | RDF_Graph_Executable.S_IRI i -> RDF_Graph_Executable.T_IRI i
         | RDF_Graph_Executable.S_BNode b -> RDF_Graph_Executable.T_BNode b in
       [{
          RDF_Graph_Executable.s = reif_subj;
          RDF_Graph_Executable.p = rdf_type_iri;
          RDF_Graph_Executable.o =
            (RDF_Graph_Executable.T_IRI rdf_statement_iri)
        };
       {
         RDF_Graph_Executable.s = reif_subj;
         RDF_Graph_Executable.p = rdf_subject_iri;
         RDF_Graph_Executable.o = subj_term
       };
       {
         RDF_Graph_Executable.s = reif_subj;
         RDF_Graph_Executable.p = rdf_predicate_iri;
         RDF_Graph_Executable.o = (RDF_Graph_Executable.T_IRI pred_iri)
       };
       {
         RDF_Graph_Executable.s = reif_subj;
         RDF_Graph_Executable.p = rdf_object_iri;
         RDF_Graph_Executable.o = obj
       }])
let validate_rdf_id (st : rdfxml_state) (id_val : Prims.string) :
  rdfxml_state=
  let st1 =
    if Prims.op_Negation (is_valid_ncname id_val)
    then
      add_error st
        (FStar_String.concat ""
           ["Invalid rdf:ID value (not an NCName): "; id_val])
    else st in
  let full_id =
    resolve_iri st1.base_iri (FStar_String.concat "" ["#"; id_val]) in
  let rec mem_str s l =
    match l with
    | [] -> false
    | x::rest -> if x = s then true else mem_str s rest in
  if mem_str full_id st1.seen_ids
  then
    add_error
      {
        base_iri = (st1.base_iri);
        namespaces = (st1.namespaces);
        lang = (st1.lang);
        bnode_counter = (st1.bnode_counter);
        li_counter = (st1.li_counter);
        errors = (st1.errors);
        seen_ids = (full_id :: (st1.seen_ids))
      } (FStar_String.concat "" ["Duplicate rdf:ID: "; id_val])
  else
    {
      base_iri = (st1.base_iri);
      namespaces = (st1.namespaces);
      lang = (st1.lang);
      bnode_counter = (st1.bnode_counter);
      li_counter = (st1.li_counter);
      errors = (st1.errors);
      seen_ids = (full_id :: (st1.seen_ids))
    }
let validate_rdf_nodeID (st : rdfxml_state) (nid : Prims.string) :
  rdfxml_state=
  if Prims.op_Negation (is_valid_ncname nid)
  then
    add_error st
      (FStar_String.concat ""
         ["Invalid rdf:nodeID value (not an NCName): "; nid])
  else st
let maybe_reify (st : rdfxml_state)
  (attrs : Parser_XML.xml_attribute Prims.list)
  (subj : RDF_Graph_Executable.subject) (pred_iri : Prims.string)
  (obj : RDF_Graph_Executable.rdf_term) :
  (RDF_Graph_Executable.triple Prims.list * rdfxml_state)=
  match Parser_XML.find_attr "rdf:ID" attrs with
  | FStar_Pervasives_Native.Some id_val ->
      let st1 = validate_rdf_id st id_val in
      let reif_iri =
        resolve_iri st1.base_iri (FStar_String.concat "" ["#"; id_val]) in
      ((make_reification_triples reif_iri subj pred_iri obj), st1)
  | FStar_Pervasives_Native.None -> ([], st)
let rec has_property_attributes (st : rdfxml_state)
  (attrs : Parser_XML.xml_attribute Prims.list) : Prims.bool=
  match attrs with
  | [] -> false
  | attr::rest ->
      if is_xml_or_xmlns_attr attr.Parser_XML.attr_name
      then has_property_attributes st rest
      else
        (match resolve_name st attr.Parser_XML.attr_name with
         | FStar_Pervasives_Native.Some full_iri ->
             if is_rdf_syntax_attr full_iri
             then has_property_attributes st rest
             else if full_iri = rdf_type_iri then true else true
         | FStar_Pervasives_Native.None -> has_property_attributes st rest)
let rec collect_text (children : Parser_XML.xml_node Prims.list) :
  Prims.string=
  match children with
  | [] -> ""
  | child::rest ->
      let this_text =
        match child with
        | Parser_XML.XText t -> t
        | Parser_XML.XCDATA t -> t
        | Parser_XML.XComment uu___ -> ""
        | Parser_XML.XElement (uu___, uu___1, uu___2) -> "" in
      FStar_String.concat "" [this_text; collect_text rest]
let rec is_all_text (children : Parser_XML.xml_node Prims.list) : Prims.bool=
  match children with
  | [] -> true
  | child::rest ->
      (match child with
       | Parser_XML.XText uu___ -> is_all_text rest
       | Parser_XML.XCDATA uu___ -> is_all_text rest
       | Parser_XML.XComment uu___ -> is_all_text rest
       | Parser_XML.XElement (uu___, uu___1, uu___2) -> false)
let rec serialize_xml_node (node : Parser_XML.xml_node) (fuel : Prims.nat) :
  Prims.string=
  if fuel = Prims.int_zero
  then ""
  else
    (match node with
     | Parser_XML.XText t -> t
     | Parser_XML.XCDATA t -> FStar_String.concat "" ["<![CDATA["; t; "]]>"]
     | Parser_XML.XComment t -> FStar_String.concat "" ["<!--"; t; "-->"]
     | Parser_XML.XElement (tag, attrs, children) ->
         let attr_strs =
           FStar_List_Tot_Base.map
             (fun a ->
                FStar_String.concat ""
                  [" ";
                  a.Parser_XML.attr_name;
                  "=\"";
                  a.Parser_XML.attr_value;
                  "\""]) attrs in
         let attr_str = FStar_String.concat "" attr_strs in
         if (FStar_List_Tot_Base.length children) = Prims.int_zero
         then FStar_String.concat "" ["<"; tag; attr_str; "/>"]
         else
           (let child_strs =
              FStar_List_Tot_Base.map
                (fun c -> serialize_xml_node c (fuel - Prims.int_one))
                children in
            let children_str = FStar_String.concat "" child_strs in
            FStar_String.concat ""
              ["<"; tag; attr_str; ">"; children_str; "</"; tag; ">"]))
let serialize_children_xml (children : Parser_XML.xml_node Prims.list) :
  Prims.string=
  let strs =
    FStar_List_Tot_Base.map
      (fun c -> serialize_xml_node c (Prims.of_int (100))) children in
  FStar_String.concat "" strs
let rec collect_ns_attrs (nss : (Prims.string * Prims.string) Prims.list) :
  (Prims.string * Prims.string) Prims.list=
  match nss with
  | [] -> []
  | (prefix, uri)::rest ->
      if
        (((prefix = "xml") || (prefix = "xmlns")) || (prefix = "xsd")) ||
          (prefix = "rdfs")
      then collect_ns_attrs rest
      else (prefix, uri) :: (collect_ns_attrs rest)
let rec string_le_chars (cs1 : FStar_Char.char Prims.list)
  (cs2 : FStar_Char.char Prims.list) : Prims.bool=
  match (cs1, cs2) with
  | ([], uu___) -> true
  | (uu___, []) -> false
  | (c1::r1, c2::r2) ->
      let v1 = FStar_Char.int_of_char c1 in
      let v2 = FStar_Char.int_of_char c2 in
      if v1 < v2
      then true
      else if v1 > v2 then false else string_le_chars r1 r2
let string_le (s1 : Prims.string) (s2 : Prims.string) : Prims.bool=
  string_le_chars (FStar_String.list_of_string s1)
    (FStar_String.list_of_string s2)
let rec insert_sorted (item : (Prims.string * Prims.string))
  (lst : (Prims.string * Prims.string) Prims.list) :
  (Prims.string * Prims.string) Prims.list=
  match lst with
  | [] -> [item]
  | (p2, u2)::rest ->
      let uu___ = item in
      (match uu___ with
       | (p1, _u1) ->
           let key1 =
             if (FStar_String.strlen p1) = Prims.int_zero
             then "xmlns"
             else FStar_String.concat "" ["xmlns:"; p1] in
           let key2 =
             if (FStar_String.strlen p2) = Prims.int_zero
             then "xmlns"
             else FStar_String.concat "" ["xmlns:"; p2] in
           if string_le key1 key2
           then item :: lst
           else (p2, u2) :: (insert_sorted item rest))
let rec sort_ns_list (nss : (Prims.string * Prims.string) Prims.list) :
  (Prims.string * Prims.string) Prims.list=
  match nss with
  | [] -> []
  | item::rest -> insert_sorted item (sort_ns_list rest)
let is_ns_decl_attr (name : Prims.string) : Prims.bool=
  (name = "xmlns") ||
    (let chars = FStar_String.list_of_string name in
     match chars with
     | c1::c2::c3::c4::c5::c6::uu___ ->
         ((((((FStar_Char.int_of_char c1) = (Prims.of_int (0x78))) &&
               ((FStar_Char.int_of_char c2) = (Prims.of_int (0x6D))))
              && ((FStar_Char.int_of_char c3) = (Prims.of_int (0x6C))))
             && ((FStar_Char.int_of_char c4) = (Prims.of_int (0x6E))))
            && ((FStar_Char.int_of_char c5) = (Prims.of_int (0x73))))
           && ((FStar_Char.int_of_char c6) = (Prims.of_int (0x3A)))
     | uu___ -> false)
let rec filter_non_ns_attrs (attrs : Parser_XML.xml_attribute Prims.list) :
  Parser_XML.xml_attribute Prims.list=
  match attrs with
  | [] -> []
  | a::rest ->
      if is_ns_decl_attr a.Parser_XML.attr_name
      then filter_non_ns_attrs rest
      else a :: (filter_non_ns_attrs rest)
let rec serialize_xml_node_canonical (node : Parser_XML.xml_node)
  (in_scope_ns : (Prims.string * Prims.string) Prims.list) (fuel : Prims.nat)
  : Prims.string=
  if fuel = Prims.int_zero
  then ""
  else
    (match node with
     | Parser_XML.XText t -> t
     | Parser_XML.XCDATA t -> t
     | Parser_XML.XComment uu___1 -> ""
     | Parser_XML.XElement (tag, attrs, children) ->
         let sorted_ns = sort_ns_list in_scope_ns in
         let ns_attr_strs =
           FStar_List_Tot_Base.map
             (fun ns_pair ->
                let uu___1 = ns_pair in
                match uu___1 with
                | (prefix, uri) ->
                    if (FStar_String.strlen prefix) = Prims.int_zero
                    then FStar_String.concat "" [" xmlns=\""; uri; "\""]
                    else
                      FStar_String.concat ""
                        [" xmlns:"; prefix; "=\""; uri; "\""]) sorted_ns in
         let ns_str = FStar_String.concat "" ns_attr_strs in
         let regular_attrs = filter_non_ns_attrs attrs in
         let attr_strs =
           FStar_List_Tot_Base.map
             (fun a ->
                FStar_String.concat ""
                  [" ";
                  a.Parser_XML.attr_name;
                  "=\"";
                  a.Parser_XML.attr_value;
                  "\""]) regular_attrs in
         let attr_str = FStar_String.concat "" attr_strs in
         let child_strs =
           FStar_List_Tot_Base.map
             (fun c ->
                serialize_xml_node_canonical c in_scope_ns
                  (fuel - Prims.int_one)) children in
         let children_str = FStar_String.concat "" child_strs in
         FStar_String.concat ""
           ["<"; tag; ns_str; attr_str; ">"; children_str; "</"; tag; ">"])
let serialize_children_xml_canonical (st : rdfxml_state)
  (children : Parser_XML.xml_node Prims.list) : Prims.string=
  let in_scope_ns = collect_ns_attrs st.namespaces in
  let strs =
    FStar_List_Tot_Base.map
      (fun c ->
         serialize_xml_node_canonical c in_scope_ns (Prims.of_int (100)))
      children in
  FStar_String.concat "" strs
type process_result =
  {
  pr_triples: RDF_Graph_Executable.triple Prims.list ;
  pr_state: rdfxml_state }
let __proj__Mkprocess_result__item__pr_triples (projectee : process_result) :
  RDF_Graph_Executable.triple Prims.list=
  match projectee with | { pr_triples; pr_state;_} -> pr_triples
let __proj__Mkprocess_result__item__pr_state (projectee : process_result) :
  rdfxml_state= match projectee with | { pr_triples; pr_state;_} -> pr_state
let empty_result (st : rdfxml_state) : process_result=
  { pr_triples = []; pr_state = st }
let add_triples (pr : process_result)
  (ts : RDF_Graph_Executable.triple Prims.list) : process_result=
  {
    pr_triples = (FStar_List_Tot_Base.op_At pr.pr_triples ts);
    pr_state = (pr.pr_state)
  }
let validate_node_attrs (st : rdfxml_state)
  (attrs : Parser_XML.xml_attribute Prims.list) : rdfxml_state=
  let has_about =
    match Parser_XML.find_attr "rdf:about" attrs with
    | FStar_Pervasives_Native.Some uu___ -> true
    | FStar_Pervasives_Native.None -> false in
  let has_id =
    match Parser_XML.find_attr "rdf:ID" attrs with
    | FStar_Pervasives_Native.Some uu___ -> true
    | FStar_Pervasives_Native.None -> false in
  let has_nodeID =
    match Parser_XML.find_attr "rdf:nodeID" attrs with
    | FStar_Pervasives_Native.Some uu___ -> true
    | FStar_Pervasives_Native.None -> false in
  let has_aboutEach =
    match Parser_XML.find_attr "rdf:aboutEach" attrs with
    | FStar_Pervasives_Native.Some uu___ -> true
    | FStar_Pervasives_Native.None -> false in
  let has_aboutEachPrefix =
    match Parser_XML.find_attr "rdf:aboutEachPrefix" attrs with
    | FStar_Pervasives_Native.Some uu___ -> true
    | FStar_Pervasives_Native.None -> false in
  let st1 =
    if has_nodeID && has_id
    then
      add_error st
        "Cannot have both rdf:nodeID and rdf:ID on the same element"
    else st in
  let st2 =
    if has_nodeID && has_about
    then
      add_error st1
        "Cannot have both rdf:nodeID and rdf:about on the same element"
    else st1 in
  let st3 =
    if has_aboutEach
    then add_error st2 "rdf:aboutEach is no longer permitted in RDF/XML"
    else st2 in
  if has_aboutEachPrefix
  then add_error st3 "rdf:aboutEachPrefix is no longer permitted in RDF/XML"
  else st3
let validate_property_attrs (st : rdfxml_state)
  (attrs : Parser_XML.xml_attribute Prims.list) : rdfxml_state=
  let has_resource =
    match Parser_XML.find_attr "rdf:resource" attrs with
    | FStar_Pervasives_Native.Some uu___ -> true
    | FStar_Pervasives_Native.None -> false in
  let has_nodeID =
    match Parser_XML.find_attr "rdf:nodeID" attrs with
    | FStar_Pervasives_Native.Some uu___ -> true
    | FStar_Pervasives_Native.None -> false in
  let has_parseType =
    match Parser_XML.find_attr "rdf:parseType" attrs with
    | FStar_Pervasives_Native.Some uu___ -> true
    | FStar_Pervasives_Native.None -> false in
  let st1 =
    if has_nodeID && has_resource
    then
      add_error st
        "Cannot have both rdf:nodeID and rdf:resource on the same element"
    else st in
  if has_parseType && has_resource
  then
    add_error st1
      "Cannot have both rdf:parseType and rdf:resource on the same element"
  else st1
let determine_subject (st : rdfxml_state)
  (attrs : Parser_XML.xml_attribute Prims.list) :
  (RDF_Graph_Executable.subject * rdfxml_state)=
  let st0 = validate_node_attrs st attrs in
  match Parser_XML.find_attr "rdf:about" attrs with
  | FStar_Pervasives_Native.Some about_val ->
      let iri = resolve_iri st0.base_iri about_val in
      if RDF_Graph_Executable.is_iri iri
      then ((RDF_Graph_Executable.S_IRI iri), st0)
      else
        (let uu___1 = fresh_bnode st0 in
         match uu___1 with
         | (bid, st') -> ((RDF_Graph_Executable.S_BNode bid), st'))
  | FStar_Pervasives_Native.None ->
      (match Parser_XML.find_attr "rdf:ID" attrs with
       | FStar_Pervasives_Native.Some id_val ->
           let st1 = validate_rdf_id st0 id_val in
           let iri =
             resolve_iri st1.base_iri (FStar_String.concat "" ["#"; id_val]) in
           if RDF_Graph_Executable.is_iri iri
           then ((RDF_Graph_Executable.S_IRI iri), st1)
           else
             (let uu___1 = fresh_bnode st1 in
              match uu___1 with
              | (bid, st') -> ((RDF_Graph_Executable.S_BNode bid), st'))
       | FStar_Pervasives_Native.None ->
           (match Parser_XML.find_attr "rdf:nodeID" attrs with
            | FStar_Pervasives_Native.Some nid ->
                let st1 = validate_rdf_nodeID st0 nid in
                let bid = FStar_String.concat "" ["_:"; nid] in
                ((RDF_Graph_Executable.S_BNode bid), st1)
            | FStar_Pervasives_Native.None ->
                let uu___ = fresh_bnode st0 in
                (match uu___ with
                 | (bid, st') -> ((RDF_Graph_Executable.S_BNode bid), st'))))
let determine_property_object_from_attrs (st : rdfxml_state)
  (attrs : Parser_XML.xml_attribute Prims.list) :
  (RDF_Graph_Executable.rdf_term * rdfxml_state)
    FStar_Pervasives_Native.option=
  match Parser_XML.find_attr "rdf:resource" attrs with
  | FStar_Pervasives_Native.Some res_val ->
      let iri = resolve_iri st.base_iri res_val in
      if RDF_Graph_Executable.is_iri iri
      then
        FStar_Pervasives_Native.Some ((RDF_Graph_Executable.T_IRI iri), st)
      else FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.None ->
      (match Parser_XML.find_attr "rdf:nodeID" attrs with
       | FStar_Pervasives_Native.Some nid ->
           let st1 = validate_rdf_nodeID st nid in
           let bid = FStar_String.concat "" ["_:"; nid] in
           FStar_Pervasives_Native.Some
             ((RDF_Graph_Executable.T_BNode bid), st1)
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
let rec collect_property_attributes (st : rdfxml_state)
  (subj : RDF_Graph_Executable.subject)
  (attrs : Parser_XML.xml_attribute Prims.list) :
  RDF_Graph_Executable.triple Prims.list=
  match attrs with
  | [] -> []
  | attr::rest ->
      let rest_triples = collect_property_attributes st subj rest in
      if is_xml_or_xmlns_attr attr.Parser_XML.attr_name
      then rest_triples
      else
        (match resolve_name st attr.Parser_XML.attr_name with
         | FStar_Pervasives_Native.Some full_iri ->
             if is_rdf_syntax_attr full_iri
             then rest_triples
             else
               if full_iri = rdf_type_iri
               then
                 (let type_iri =
                    resolve_iri st.base_iri attr.Parser_XML.attr_value in
                  if
                    (RDF_Graph_Executable.is_iri full_iri) &&
                      (RDF_Graph_Executable.is_iri type_iri)
                  then
                    {
                      RDF_Graph_Executable.s = subj;
                      RDF_Graph_Executable.p = full_iri;
                      RDF_Graph_Executable.o =
                        (RDF_Graph_Executable.T_IRI type_iri)
                    } :: rest_triples
                  else rest_triples)
               else
                 if RDF_Graph_Executable.is_iri full_iri
                 then
                   (match make_plain_literal attr.Parser_XML.attr_value
                            st.lang
                    with
                    | FStar_Pervasives_Native.Some lit_term ->
                        {
                          RDF_Graph_Executable.s = subj;
                          RDF_Graph_Executable.p = full_iri;
                          RDF_Graph_Executable.o = lit_term
                        } :: rest_triples
                    | FStar_Pervasives_Native.None -> rest_triples)
                 else rest_triples
         | FStar_Pervasives_Native.None -> rest_triples)
let rec process_node_element (st : rdfxml_state) (node : Parser_XML.xml_node)
  (fuel : Prims.nat) : process_result=
  if fuel = Prims.int_zero
  then empty_result st
  else
    (match node with
     | Parser_XML.XElement (tag, attrs, children) ->
         let st1 = update_state_from_attrs st attrs in
         let st11 =
           match resolve_name st1 tag with
           | FStar_Pervasives_Native.Some full_tag_iri ->
               if is_forbidden_node_element_name full_tag_iri
               then
                 add_error st1
                   (FStar_String.concat ""
                      ["Forbidden node element name: "; full_tag_iri])
               else st1
           | FStar_Pervasives_Native.None -> st1 in
         let st12 =
           let rec check_li_attr ats s =
             match ats with
             | [] -> s
             | a::rest ->
                 let s1 =
                   match resolve_name s a.Parser_XML.attr_name with
                   | FStar_Pervasives_Native.Some iri ->
                       if is_forbidden_property_attribute_name iri
                       then
                         add_error s
                           "rdf:li is not allowed as a property attribute"
                       else s
                   | FStar_Pervasives_Native.None -> s in
                 check_li_attr rest s1 in
           check_li_attr attrs st11 in
         let uu___1 = determine_subject st12 attrs in
         (match uu___1 with
          | (subj, st2) ->
              let type_triples =
                match resolve_name st12 tag with
                | FStar_Pervasives_Native.Some full_tag_iri ->
                    if
                      full_tag_iri =
                        (FStar_String.concat "" [rdf_ns; "Description"])
                    then []
                    else
                      if
                        full_tag_iri =
                          (FStar_String.concat "" [rdf_ns; "RDF"])
                      then []
                      else
                        if
                          full_tag_iri =
                            (FStar_String.concat "" [rdf_ns; "Bag"])
                        then
                          (if
                             (RDF_Graph_Executable.is_iri rdf_type_iri) &&
                               (RDF_Graph_Executable.is_iri full_tag_iri)
                           then
                             [{
                                RDF_Graph_Executable.s = subj;
                                RDF_Graph_Executable.p = rdf_type_iri;
                                RDF_Graph_Executable.o =
                                  (RDF_Graph_Executable.T_IRI full_tag_iri)
                              }]
                           else [])
                        else
                          if
                            full_tag_iri =
                              (FStar_String.concat "" [rdf_ns; "Seq"])
                          then
                            (if
                               (RDF_Graph_Executable.is_iri rdf_type_iri) &&
                                 (RDF_Graph_Executable.is_iri full_tag_iri)
                             then
                               [{
                                  RDF_Graph_Executable.s = subj;
                                  RDF_Graph_Executable.p = rdf_type_iri;
                                  RDF_Graph_Executable.o =
                                    (RDF_Graph_Executable.T_IRI full_tag_iri)
                                }]
                             else [])
                          else
                            if
                              full_tag_iri =
                                (FStar_String.concat "" [rdf_ns; "Alt"])
                            then
                              (if
                                 (RDF_Graph_Executable.is_iri rdf_type_iri)
                                   &&
                                   (RDF_Graph_Executable.is_iri full_tag_iri)
                               then
                                 [{
                                    RDF_Graph_Executable.s = subj;
                                    RDF_Graph_Executable.p = rdf_type_iri;
                                    RDF_Graph_Executable.o =
                                      (RDF_Graph_Executable.T_IRI
                                         full_tag_iri)
                                  }]
                               else [])
                            else
                              if
                                (RDF_Graph_Executable.is_iri rdf_type_iri) &&
                                  (RDF_Graph_Executable.is_iri full_tag_iri)
                              then
                                [{
                                   RDF_Graph_Executable.s = subj;
                                   RDF_Graph_Executable.p = rdf_type_iri;
                                   RDF_Graph_Executable.o =
                                     (RDF_Graph_Executable.T_IRI full_tag_iri)
                                 }]
                              else []
                | FStar_Pervasives_Native.None -> [] in
              let prop_attr_triples =
                collect_property_attributes st12 subj attrs in
              let st3 = reset_li_counter st2 in
              let child_result =
                process_property_children st3 subj children
                  (fuel - Prims.int_one) in
              {
                pr_triples =
                  (FStar_List_Tot_Base.op_At type_triples
                     (FStar_List_Tot_Base.op_At prop_attr_triples
                        child_result.pr_triples));
                pr_state = (child_result.pr_state)
              })
     | uu___1 -> empty_result st)
and process_property_children (st : rdfxml_state)
  (subj : RDF_Graph_Executable.subject)
  (children : Parser_XML.xml_node Prims.list) (fuel : Prims.nat) :
  process_result=
  if fuel = Prims.int_zero
  then empty_result st
  else
    (match children with
     | [] -> empty_result st
     | child::rest ->
         (match child with
          | Parser_XML.XElement (tag, uu___1, uu___2) ->
              let result1 =
                process_property_element st subj child (fuel - Prims.int_one) in
              let st1_for_tag =
                update_state_from_attrs st
                  (match child with
                   | Parser_XML.XElement (uu___3, a, uu___4) -> a
                   | uu___3 -> []) in
              let next_li_counter =
                match resolve_name st1_for_tag tag with
                | FStar_Pervasives_Native.Some full_iri ->
                    if full_iri = (FStar_String.concat "" [rdf_ns; "li"])
                    then st.li_counter + Prims.int_one
                    else st.li_counter
                | FStar_Pervasives_Native.None -> st.li_counter in
              let sibling_st =
                let uu___3 = result1.pr_state in
                {
                  base_iri = (st.base_iri);
                  namespaces = (st.namespaces);
                  lang = (st.lang);
                  bnode_counter = (uu___3.bnode_counter);
                  li_counter = next_li_counter;
                  errors = (uu___3.errors);
                  seen_ids = (uu___3.seen_ids)
                } in
              let result2 =
                process_property_children sibling_st subj rest
                  (fuel - Prims.int_one) in
              {
                pr_triples =
                  (FStar_List_Tot_Base.op_At result1.pr_triples
                     result2.pr_triples);
                pr_state = (result2.pr_state)
              }
          | uu___1 ->
              process_property_children st subj rest (fuel - Prims.int_one)))
and process_property_element (st : rdfxml_state)
  (subj : RDF_Graph_Executable.subject) (node : Parser_XML.xml_node)
  (fuel : Prims.nat) : process_result=
  if fuel = Prims.int_zero
  then empty_result st
  else
    (match node with
     | Parser_XML.XElement (tag, attrs, children) ->
         let st1 = update_state_from_attrs st attrs in
         let st11 =
           match resolve_name st1 tag with
           | FStar_Pervasives_Native.Some full_iri ->
               if is_forbidden_property_element_name full_iri
               then
                 add_error st1
                   (FStar_String.concat ""
                      ["Forbidden property element name: "; full_iri])
               else st1
           | FStar_Pervasives_Native.None -> st1 in
         let st12 = validate_property_attrs st11 attrs in
         let uu___1 =
           match resolve_name st12 tag with
           | FStar_Pervasives_Native.Some full_iri ->
               if full_iri = (FStar_String.concat "" [rdf_ns; "li"])
               then
                 let uu___2 = next_li st12 in
                 (match uu___2 with
                  | (li_iri, st') ->
                      ((FStar_Pervasives_Native.Some li_iri), st'))
               else ((FStar_Pervasives_Native.Some full_iri), st12)
           | FStar_Pervasives_Native.None ->
               (FStar_Pervasives_Native.None, st12) in
         (match uu___1 with
          | (pred_iri_opt, st2) ->
              (match pred_iri_opt with
               | FStar_Pervasives_Native.None -> empty_result st2
               | FStar_Pervasives_Native.Some pred_iri ->
                   if
                     Prims.op_Negation (RDF_Graph_Executable.is_iri pred_iri)
                   then empty_result st2
                   else
                     (let parse_type =
                        Parser_XML.find_attr "rdf:parseType" attrs in
                      match parse_type with
                      | FStar_Pervasives_Native.Some "Literal" ->
                          let xml_content =
                            serialize_children_xml_canonical st2 children in
                          if RDF_Graph_Executable.is_iri rdf_xmlliteral_iri
                          then
                            (match make_typed_literal xml_content
                                     rdf_xmlliteral_iri
                             with
                             | FStar_Pervasives_Native.Some obj ->
                                 let t =
                                   {
                                     RDF_Graph_Executable.s = subj;
                                     RDF_Graph_Executable.p = pred_iri;
                                     RDF_Graph_Executable.o = obj
                                   } in
                                 let uu___3 =
                                   maybe_reify st2 attrs subj pred_iri obj in
                                 (match uu___3 with
                                  | (reif_triples, _st_reif) ->
                                      {
                                        pr_triples = (t :: reif_triples);
                                        pr_state = st2
                                      })
                             | FStar_Pervasives_Native.None ->
                                 empty_result st2)
                          else empty_result st2
                      | FStar_Pervasives_Native.Some "Resource" ->
                          let uu___3 = fresh_bnode st2 in
                          (match uu___3 with
                           | (bid, st3) ->
                               let bnode_subj =
                                 RDF_Graph_Executable.S_BNode bid in
                               let link_triple =
                                 {
                                   RDF_Graph_Executable.s = subj;
                                   RDF_Graph_Executable.p = pred_iri;
                                   RDF_Graph_Executable.o =
                                     (RDF_Graph_Executable.T_BNode bid)
                                 } in
                               let uu___4 =
                                 maybe_reify st2 attrs subj pred_iri
                                   (RDF_Graph_Executable.T_BNode bid) in
                               (match uu___4 with
                                | (reif_triples, _st_reif) ->
                                    let st4 = reset_li_counter st3 in
                                    let child_result =
                                      process_property_children st4
                                        bnode_subj children
                                        (fuel - Prims.int_one) in
                                    {
                                      pr_triples =
                                        (FStar_List_Tot_Base.op_At
                                           (link_triple :: reif_triples)
                                           child_result.pr_triples);
                                      pr_state = (child_result.pr_state)
                                    }))
                      | FStar_Pervasives_Native.Some "Collection" ->
                          let collection_result =
                            process_collection st2 subj pred_iri children
                              (fuel - Prims.int_one) in
                          let reif_triples =
                            match Parser_XML.find_attr "rdf:ID" attrs with
                            | FStar_Pervasives_Native.Some uu___3 ->
                                (match collection_result.pr_triples with
                                 | first_t::uu___4 ->
                                     let uu___5 =
                                       maybe_reify st2 attrs subj pred_iri
                                         first_t.RDF_Graph_Executable.o in
                                     (match uu___5 with | (rt, _st_r) -> rt)
                                 | [] -> [])
                            | FStar_Pervasives_Native.None -> [] in
                          {
                            pr_triples =
                              (FStar_List_Tot_Base.op_At
                                 collection_result.pr_triples reif_triples);
                            pr_state = (collection_result.pr_state)
                          }
                      | uu___3 ->
                          (match determine_property_object_from_attrs st2
                                   attrs
                           with
                           | FStar_Pervasives_Native.Some (obj, st3) ->
                               let link_triple =
                                 {
                                   RDF_Graph_Executable.s = subj;
                                   RDF_Graph_Executable.p = pred_iri;
                                   RDF_Graph_Executable.o = obj
                                 } in
                               let obj_subj_opt =
                                 match obj with
                                 | RDF_Graph_Executable.T_IRI i ->
                                     if RDF_Graph_Executable.is_iri i
                                     then
                                       FStar_Pervasives_Native.Some
                                         (RDF_Graph_Executable.S_IRI i)
                                     else FStar_Pervasives_Native.None
                                 | RDF_Graph_Executable.T_BNode b ->
                                     FStar_Pervasives_Native.Some
                                       (RDF_Graph_Executable.S_BNode b)
                                 | uu___4 -> FStar_Pervasives_Native.None in
                               let prop_attr_triples =
                                 match obj_subj_opt with
                                 | FStar_Pervasives_Native.Some obj_s ->
                                     collect_property_attributes st3 obj_s
                                       attrs
                                 | FStar_Pervasives_Native.None -> [] in
                               let uu___4 =
                                 maybe_reify st2 attrs subj pred_iri obj in
                               (match uu___4 with
                                | (reif_triples, _st_reif) ->
                                    {
                                      pr_triples =
                                        (FStar_List_Tot_Base.op_At
                                           (link_triple :: prop_attr_triples)
                                           reif_triples);
                                      pr_state = st3
                                    })
                           | FStar_Pervasives_Native.None ->
                               let datatype_opt =
                                 Parser_XML.find_attr "rdf:datatype" attrs in
                               let child_elements_list =
                                 FStar_List_Tot_Base.filter
                                   (fun c ->
                                      match c with
                                      | Parser_XML.XElement
                                          (uu___4, uu___5, uu___6) -> true
                                      | uu___4 -> false) children in
                               if
                                 (FStar_List_Tot_Base.length
                                    child_elements_list)
                                   > Prims.int_zero
                               then
                                 (match child_elements_list with
                                  | child_elem::uu___4 ->
                                      let node_result =
                                        process_node_element st2 child_elem
                                          (fuel - Prims.int_one) in
                                      let child_subj =
                                        determine_subject
                                          (update_state_from_attrs st2
                                             (Parser_XML.element_attrs
                                                child_elem))
                                          (Parser_XML.element_attrs
                                             child_elem) in
                                      let uu___5 = child_subj in
                                      (match uu___5 with
                                       | (child_s, st3) ->
                                           let obj_term =
                                             match child_s with
                                             | RDF_Graph_Executable.S_IRI i
                                                 ->
                                                 RDF_Graph_Executable.T_IRI i
                                             | RDF_Graph_Executable.S_BNode b
                                                 ->
                                                 RDF_Graph_Executable.T_BNode
                                                   b in
                                           let link_triple =
                                             {
                                               RDF_Graph_Executable.s = subj;
                                               RDF_Graph_Executable.p =
                                                 pred_iri;
                                               RDF_Graph_Executable.o =
                                                 obj_term
                                             } in
                                           let uu___6 =
                                             maybe_reify st2 attrs subj
                                               pred_iri obj_term in
                                           (match uu___6 with
                                            | (reif_triples, _st_reif) ->
                                                {
                                                  pr_triples =
                                                    (FStar_List_Tot_Base.op_At
                                                       (link_triple ::
                                                       reif_triples)
                                                       node_result.pr_triples);
                                                  pr_state =
                                                    (node_result.pr_state)
                                                }))
                                  | [] -> empty_result st2)
                               else
                                 if has_property_attributes st2 attrs
                                 then
                                   (let uu___5 = fresh_bnode st2 in
                                    match uu___5 with
                                    | (bid, st3) ->
                                        let bnode_subj =
                                          RDF_Graph_Executable.S_BNode bid in
                                        let link_triple =
                                          {
                                            RDF_Graph_Executable.s = subj;
                                            RDF_Graph_Executable.p = pred_iri;
                                            RDF_Graph_Executable.o =
                                              (RDF_Graph_Executable.T_BNode
                                                 bid)
                                          } in
                                        let prop_attr_triples =
                                          collect_property_attributes st3
                                            bnode_subj attrs in
                                        let uu___6 =
                                          maybe_reify st2 attrs subj pred_iri
                                            (RDF_Graph_Executable.T_BNode bid) in
                                        (match uu___6 with
                                         | (reif_triples, _st_reif) ->
                                             {
                                               pr_triples =
                                                 (FStar_List_Tot_Base.op_At
                                                    (link_triple ::
                                                    prop_attr_triples)
                                                    reif_triples);
                                               pr_state = st3
                                             }))
                                 else
                                   (let text_val = collect_text children in
                                    let obj_opt =
                                      match datatype_opt with
                                      | FStar_Pervasives_Native.Some dt ->
                                          let full_dt =
                                            resolve_iri st2.base_iri dt in
                                          make_typed_literal text_val full_dt
                                      | FStar_Pervasives_Native.None ->
                                          make_plain_literal text_val
                                            st2.lang in
                                    match obj_opt with
                                    | FStar_Pervasives_Native.Some obj ->
                                        let t =
                                          {
                                            RDF_Graph_Executable.s = subj;
                                            RDF_Graph_Executable.p = pred_iri;
                                            RDF_Graph_Executable.o = obj
                                          } in
                                        let uu___6 =
                                          maybe_reify st2 attrs subj pred_iri
                                            obj in
                                        (match uu___6 with
                                         | (reif_triples, _st_reif) ->
                                             {
                                               pr_triples = (t ::
                                                 reif_triples);
                                               pr_state = st2
                                             })
                                    | FStar_Pervasives_Native.None ->
                                        empty_result st2
                                    | uu___6 -> empty_result st))))))
and process_collection (st : rdfxml_state)
  (subj : RDF_Graph_Executable.subject) (pred_iri : Prims.string)
  (items : Parser_XML.xml_node Prims.list) (fuel : Prims.nat) :
  process_result=
  if fuel = Prims.int_zero
  then empty_result st
  else
    (let elem_items =
       FStar_List_Tot_Base.filter
         (fun c ->
            match c with
            | Parser_XML.XElement (uu___1, uu___2, uu___3) -> true
            | uu___1 -> false) items in
     if (FStar_List_Tot_Base.length elem_items) = Prims.int_zero
     then
       (if
          (RDF_Graph_Executable.is_iri rdf_nil_iri) &&
            (RDF_Graph_Executable.is_iri pred_iri)
        then
          let t =
            {
              RDF_Graph_Executable.s = subj;
              RDF_Graph_Executable.p = pred_iri;
              RDF_Graph_Executable.o =
                (RDF_Graph_Executable.T_IRI rdf_nil_iri)
            } in
          { pr_triples = [t]; pr_state = st }
        else empty_result st)
     else
       build_collection_list st subj pred_iri elem_items
         (fuel - Prims.int_one))
and build_collection_list (st : rdfxml_state)
  (subj : RDF_Graph_Executable.subject) (pred_iri : Prims.string)
  (items : Parser_XML.xml_node Prims.list) (fuel : Prims.nat) :
  process_result=
  if fuel = Prims.int_zero
  then empty_result st
  else
    (match items with
     | [] ->
         if
           (RDF_Graph_Executable.is_iri rdf_nil_iri) &&
             (RDF_Graph_Executable.is_iri pred_iri)
         then
           let t =
             {
               RDF_Graph_Executable.s = subj;
               RDF_Graph_Executable.p = pred_iri;
               RDF_Graph_Executable.o =
                 (RDF_Graph_Executable.T_IRI rdf_nil_iri)
             } in
           { pr_triples = [t]; pr_state = st }
         else empty_result st
     | item::rest ->
         let uu___1 = fresh_bnode st in
         (match uu___1 with
          | (list_bid, st2) ->
              let list_node = RDF_Graph_Executable.S_BNode list_bid in
              let link_triple =
                {
                  RDF_Graph_Executable.s = subj;
                  RDF_Graph_Executable.p = pred_iri;
                  RDF_Graph_Executable.o =
                    (RDF_Graph_Executable.T_BNode list_bid)
                } in
              let item_result =
                process_node_element st2 item (fuel - Prims.int_one) in
              let item_st =
                update_state_from_attrs item_result.pr_state
                  (Parser_XML.element_attrs item) in
              let uu___2 =
                determine_subject item_st (Parser_XML.element_attrs item) in
              (match uu___2 with
               | (item_subj, st3) ->
                   let item_term =
                     match item_subj with
                     | RDF_Graph_Executable.S_IRI i ->
                         RDF_Graph_Executable.T_IRI i
                     | RDF_Graph_Executable.S_BNode b ->
                         RDF_Graph_Executable.T_BNode b in
                   let first_triple =
                     {
                       RDF_Graph_Executable.s = list_node;
                       RDF_Graph_Executable.p = rdf_first_iri;
                       RDF_Graph_Executable.o = item_term
                     } in
                   let first_triple_opt =
                     if RDF_Graph_Executable.is_iri rdf_first_iri
                     then FStar_Pervasives_Native.Some first_triple
                     else FStar_Pervasives_Native.None in
                   let rest_result =
                     if RDF_Graph_Executable.is_iri rdf_rest_iri
                     then
                       build_collection_list st3 list_node rdf_rest_iri rest
                         (fuel - Prims.int_one)
                     else empty_result st3 in
                   let all_triples =
                     match first_triple_opt with
                     | FStar_Pervasives_Native.Some ft ->
                         FStar_List_Tot_Base.op_At (link_triple :: ft ::
                           (item_result.pr_triples)) rest_result.pr_triples
                     | FStar_Pervasives_Native.None ->
                         FStar_List_Tot_Base.op_At (link_triple ::
                           (item_result.pr_triples)) rest_result.pr_triples in
                   {
                     pr_triples = all_triples;
                     pr_state = (rest_result.pr_state)
                   })))
let rec process_node_elements (st : rdfxml_state)
  (nodes : Parser_XML.xml_node Prims.list) (fuel : Prims.nat) :
  process_result=
  if fuel = Prims.int_zero
  then empty_result st
  else
    (match nodes with
     | [] -> empty_result st
     | node::rest ->
         (match node with
          | Parser_XML.XElement (uu___1, uu___2, uu___3) ->
              let result1 =
                process_node_element st node (fuel - Prims.int_one) in
              let sibling_st =
                let uu___4 = result1.pr_state in
                {
                  base_iri = (st.base_iri);
                  namespaces = (st.namespaces);
                  lang = (st.lang);
                  bnode_counter = (uu___4.bnode_counter);
                  li_counter = (uu___4.li_counter);
                  errors = (uu___4.errors);
                  seen_ids = (uu___4.seen_ids)
                } in
              let result2 =
                process_node_elements sibling_st rest (fuel - Prims.int_one) in
              {
                pr_triples =
                  (FStar_List_Tot_Base.op_At result1.pr_triples
                     result2.pr_triples);
                pr_state = (result2.pr_state)
              }
          | uu___1 -> process_node_elements st rest (fuel - Prims.int_one)))
let process_xml_tree (st : rdfxml_state) (root : Parser_XML.xml_node) :
  RDF_Graph_Executable.triple Prims.list FStar_Pervasives_Native.option=
  let fuel = (Prims.of_int (10000)) in
  match root with
  | Parser_XML.XElement (tag, attrs, children) ->
      let st1 = update_state_from_attrs st attrs in
      let is_rdf_root =
        match resolve_name st1 tag with
        | FStar_Pervasives_Native.Some full_iri ->
            full_iri = (FStar_String.concat "" [rdf_ns; "RDF"])
        | FStar_Pervasives_Native.None -> tag = "rdf:RDF" in
      let result =
        if is_rdf_root
        then process_node_elements st1 children fuel
        else process_node_element st1 root fuel in
      if has_errors result.pr_state
      then FStar_Pervasives_Native.None
      else FStar_Pervasives_Native.Some (result.pr_triples)
  | uu___ -> FStar_Pervasives_Native.Some []
let parse_rdfxml_with_base_opt (base_iri : Prims.string)
  (input : Prims.string) :
  RDF_Graph_Executable.triple Prims.list FStar_Pervasives_Native.option=
  match Parser_XML.parse_xml_document input with
  | FStar_Pervasives_Native.Some root ->
      let st = initial_state base_iri in process_xml_tree st root
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
let parse_rdfxml_with_base (base_iri : Prims.string) (input : Prims.string) :
  RDF_Graph_Executable.triple Prims.list=
  match parse_rdfxml_with_base_opt base_iri input with
  | FStar_Pervasives_Native.Some triples -> triples
  | FStar_Pervasives_Native.None -> failwith "Invalid RDF/XML document"
let parse_rdfxml (input : Prims.string) :
  RDF_Graph_Executable.triple Prims.list= parse_rdfxml_with_base "" input
