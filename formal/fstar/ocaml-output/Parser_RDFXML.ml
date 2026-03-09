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
  li_counter: Prims.nat }
let __proj__Mkrdfxml_state__item__base_iri (projectee : rdfxml_state) :
  Prims.string=
  match projectee with
  | { base_iri; namespaces; lang; bnode_counter; li_counter;_} -> base_iri
let __proj__Mkrdfxml_state__item__namespaces (projectee : rdfxml_state) :
  (Prims.string * Prims.string) Prims.list=
  match projectee with
  | { base_iri; namespaces; lang; bnode_counter; li_counter;_} -> namespaces
let __proj__Mkrdfxml_state__item__lang (projectee : rdfxml_state) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | { base_iri; namespaces; lang; bnode_counter; li_counter;_} -> lang
let __proj__Mkrdfxml_state__item__bnode_counter (projectee : rdfxml_state) :
  Prims.nat=
  match projectee with
  | { base_iri; namespaces; lang; bnode_counter; li_counter;_} ->
      bnode_counter
let __proj__Mkrdfxml_state__item__li_counter (projectee : rdfxml_state) :
  Prims.nat=
  match projectee with
  | { base_iri; namespaces; lang; bnode_counter; li_counter;_} -> li_counter
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
    li_counter = Prims.int_one
  }
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
      li_counter = (st.li_counter)
    })
let reset_li_counter (st : rdfxml_state) : rdfxml_state=
  {
    base_iri = (st.base_iri);
    namespaces = (st.namespaces);
    lang = (st.lang);
    bnode_counter = (st.bnode_counter);
    li_counter = Prims.int_one
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
      li_counter = (st.li_counter + Prims.int_one)
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
    li_counter = (st.li_counter)
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
(* ================================================================ *)
(* RDF/XML Validation — NCName, reserved names, attribute conflicts *)
(* ================================================================ *)

(* NCName validation per XML Namespaces spec:
   NCName ::= Name - (Char* ':' Char*)
   NameStartChar ::= ":" | [A-Z] | "_" | [a-z] | [#xC0-#xD6] | ...
   NameChar ::= NameStartChar | "-" | "." | [0-9] | #xB7 | ...
   NCName starts with NameStartChar minus ':', so letter or underscore *)
let is_ncname_start_char (code : Prims.int) : Prims.bool =
  ((code >= Prims.of_int 0x41) && (code <= Prims.of_int 0x5A)) ||  (* A-Z *)
  (code = Prims.of_int 0x5F) ||                                     (* _ *)
  ((code >= Prims.of_int 0x61) && (code <= Prims.of_int 0x7A)) ||  (* a-z *)
  ((code >= Prims.of_int 0xC0) && (code <= Prims.of_int 0xD6)) ||
  ((code >= Prims.of_int 0xD8) && (code <= Prims.of_int 0xF6)) ||
  ((code >= Prims.of_int 0xF8) && (code <= Prims.of_int 0x2FF)) ||
  ((code >= Prims.of_int 0x370) && (code <= Prims.of_int 0x37D)) ||
  ((code >= Prims.of_int 0x37F) && (code <= Prims.of_int 0x1FFF)) ||
  ((code >= Prims.of_int 0x200C) && (code <= Prims.of_int 0x200D)) ||
  ((code >= Prims.of_int 0x2070) && (code <= Prims.of_int 0x218F)) ||
  ((code >= Prims.of_int 0x2C00) && (code <= Prims.of_int 0x2FEF)) ||
  ((code >= Prims.of_int 0x3001) && (code <= Prims.of_int 0xD7FF)) ||
  ((code >= Prims.of_int 0xF900) && (code <= Prims.of_int 0xFDCF)) ||
  ((code >= Prims.of_int 0xFDF0) && (code <= Prims.of_int 0xFFFD)) ||
  ((code >= Prims.of_int 0x10000) && (code <= Prims.of_int 0xEFFFF))

let is_ncname_char (code : Prims.int) : Prims.bool =
  is_ncname_start_char code ||
  (code = Prims.of_int 0x2D) ||  (* - *)
  (code = Prims.of_int 0x2E) ||  (* . *)
  ((code >= Prims.of_int 0x30) && (code <= Prims.of_int 0x39)) ||  (* 0-9 *)
  (code = Prims.of_int 0xB7) ||
  ((code >= Prims.of_int 0x300) && (code <= Prims.of_int 0x36F)) ||
  ((code >= Prims.of_int 0x203F) && (code <= Prims.of_int 0x2040))

let is_valid_ncname (s : Prims.string) : Prims.bool =
  let len = FStar_String.strlen s in
  if len = Prims.int_zero then false
  else
    let chars = FStar_String.list_of_string s in
    match chars with
    | [] -> false
    | first :: rest ->
      let first_code = FStar_Char.int_of_char first in
      if Prims.op_Negation (is_ncname_start_char first_code) then false
      else
        let rec check_rest cs =
          match cs with
          | [] -> true
          | c :: tl ->
            let code = FStar_Char.int_of_char c in
            if is_ncname_char code then check_rest tl else false
        in
        (* Also reject if it contains a colon *)
        let rec has_colon cs =
          match cs with
          | [] -> false
          | c :: tl ->
            if (FStar_Char.int_of_char c) = Prims.of_int 0x3A then true
            else has_colon tl
        in
        if has_colon chars then false
        else check_rest rest

let validate_ncname (context : Prims.string) (value : Prims.string) : unit =
  if Prims.op_Negation (is_valid_ncname value) then
    failwith (FStar_String.concat "" ["Invalid NCName for "; context; ": "; value])

(* Forbidden node element names in rdf: namespace per RDF/XML spec section 7.2.11 *)
let forbidden_node_element_local_names : Prims.string Prims.list =
  ["RDF"; "ID"; "about"; "bagID"; "parseType"; "resource"; "nodeID";
   "li"; "aboutEach"; "aboutEachPrefix"]

(* Forbidden property element names in rdf: namespace per RDF/XML spec section 7.2.12 *)
let forbidden_property_element_local_names : Prims.string Prims.list =
  ["Description"; "RDF"; "ID"; "about"; "bagID"; "parseType"; "resource";
   "nodeID"; "aboutEach"; "aboutEachPrefix"]

let is_forbidden_node_element_name (full_iri : Prims.string) : Prims.bool =
  let rdf_prefix = rdf_ns in
  let rdf_prefix_len = FStar_String.strlen rdf_prefix in
  let iri_len = FStar_String.strlen full_iri in
  if iri_len > rdf_prefix_len then
    let prefix = FStar_String.sub full_iri Prims.int_zero rdf_prefix_len in
    if prefix = rdf_prefix then
      let local = FStar_String.sub full_iri rdf_prefix_len (iri_len - rdf_prefix_len) in
      FStar_List_Tot_Base.mem local forbidden_node_element_local_names
    else false
  else false

let is_forbidden_property_element_name (full_iri : Prims.string) : Prims.bool =
  let rdf_prefix = rdf_ns in
  let rdf_prefix_len = FStar_String.strlen rdf_prefix in
  let iri_len = FStar_String.strlen full_iri in
  if iri_len > rdf_prefix_len then
    let prefix = FStar_String.sub full_iri Prims.int_zero rdf_prefix_len in
    if prefix = rdf_prefix then
      let local = FStar_String.sub full_iri rdf_prefix_len (iri_len - rdf_prefix_len) in
      FStar_List_Tot_Base.mem local forbidden_property_element_local_names
    else false
  else false

(* Check for rdf:aboutEach or rdf:aboutEachPrefix attributes *)
let check_no_about_each (attrs : Parser_XML.xml_attribute Prims.list) : unit =
  let rec check attrs =
    match attrs with
    | [] -> ()
    | attr :: rest ->
      if attr.Parser_XML.attr_name = "rdf:aboutEach" then
        failwith "rdf:aboutEach is not allowed (removed from RDF)"
      else if attr.Parser_XML.attr_name = "rdf:aboutEachPrefix" then
        failwith "rdf:aboutEachPrefix is not allowed (removed from RDF)"
      else check rest
  in check attrs

(* Check for rdf:li used as an attribute *)
let check_no_li_attribute (attrs : Parser_XML.xml_attribute Prims.list) : unit =
  let rec check attrs =
    match attrs with
    | [] -> ()
    | attr :: rest ->
      if attr.Parser_XML.attr_name = "rdf:li" then
        failwith "rdf:li is not allowed as an attribute"
      else check rest
  in check attrs

(* Check for conflicting subject attributes: rdf:nodeID + rdf:ID, rdf:nodeID + rdf:about *)
let check_no_subject_conflicts (attrs : Parser_XML.xml_attribute Prims.list) : unit =
  let has_about = match Parser_XML.find_attr "rdf:about" attrs with
    | FStar_Pervasives_Native.Some _ -> true | _ -> false in
  let has_id = match Parser_XML.find_attr "rdf:ID" attrs with
    | FStar_Pervasives_Native.Some _ -> true | _ -> false in
  let has_nodeid = match Parser_XML.find_attr "rdf:nodeID" attrs with
    | FStar_Pervasives_Native.Some _ -> true | _ -> false in
  if has_nodeid && has_id then
    failwith "Cannot have both rdf:nodeID and rdf:ID on same element"
  else if has_nodeid && has_about then
    failwith "Cannot have both rdf:nodeID and rdf:about on same element"
  else ()

(* Check for conflicting property object attributes: rdf:nodeID + rdf:resource *)
let check_no_property_object_conflicts (attrs : Parser_XML.xml_attribute Prims.list) : unit =
  let has_resource = match Parser_XML.find_attr "rdf:resource" attrs with
    | FStar_Pervasives_Native.Some _ -> true | _ -> false in
  let has_nodeid = match Parser_XML.find_attr "rdf:nodeID" attrs with
    | FStar_Pervasives_Native.Some _ -> true | _ -> false in
  if has_nodeid && has_resource then
    failwith "Cannot have both rdf:nodeID and rdf:resource on same element"
  else ()

(* Check rdf:parseType + rdf:resource conflict *)
let check_no_parsetype_resource_conflict (attrs : Parser_XML.xml_attribute Prims.list) : unit =
  let has_parsetype = match Parser_XML.find_attr "rdf:parseType" attrs with
    | FStar_Pervasives_Native.Some _ -> true | _ -> false in
  let has_resource = match Parser_XML.find_attr "rdf:resource" attrs with
    | FStar_Pervasives_Native.Some _ -> true | _ -> false in
  if has_parsetype && has_resource then
    failwith "Cannot have both rdf:parseType and rdf:resource on same element"
  else ()

(* Validate rdf:ID values are valid NCNames *)
let validate_rdf_id_attr (attrs : Parser_XML.xml_attribute Prims.list) : unit =
  match Parser_XML.find_attr "rdf:ID" attrs with
  | FStar_Pervasives_Native.Some id_val -> validate_ncname "rdf:ID" id_val
  | FStar_Pervasives_Native.None -> ()

(* Validate rdf:nodeID values are valid NCNames *)
let validate_rdf_nodeid_attr (attrs : Parser_XML.xml_attribute Prims.list) : unit =
  match Parser_XML.find_attr "rdf:nodeID" attrs with
  | FStar_Pervasives_Native.Some nid_val -> validate_ncname "rdf:nodeID" nid_val
  | FStar_Pervasives_Native.None -> ()

(* Validate rdf:bagID values are valid NCNames *)
let validate_rdf_bagid_attr (attrs : Parser_XML.xml_attribute Prims.list) : unit =
  match Parser_XML.find_attr "rdf:bagID" attrs with
  | FStar_Pervasives_Native.Some bid_val -> validate_ncname "rdf:bagID" bid_val
  | FStar_Pervasives_Native.None -> ()

(* Track duplicate rdf:ID values - using a ref for document-wide tracking *)
let seen_ids : (string, unit) Hashtbl.t = Hashtbl.create 64

let reset_seen_ids () = Hashtbl.clear seen_ids

let check_duplicate_rdf_id (attrs : Parser_XML.xml_attribute Prims.list) : unit =
  match Parser_XML.find_attr "rdf:ID" attrs with
  | FStar_Pervasives_Native.Some id_val ->
    if Hashtbl.mem seen_ids id_val then
      failwith (FStar_String.concat "" ["Duplicate rdf:ID: "; id_val])
    else
      Hashtbl.add seen_ids id_val ()
  | FStar_Pervasives_Native.None -> ()

(* Run all node element validations *)
let validate_node_element (st : rdfxml_state) (tag : Prims.string) (attrs : Parser_XML.xml_attribute Prims.list) : unit =
  check_no_about_each attrs;
  check_no_li_attribute attrs;
  check_no_subject_conflicts attrs;
  validate_rdf_id_attr attrs;
  validate_rdf_nodeid_attr attrs;
  validate_rdf_bagid_attr attrs;
  check_duplicate_rdf_id attrs;
  (* Check forbidden node element names *)
  (match resolve_name st tag with
   | FStar_Pervasives_Native.Some full_iri ->
     if is_forbidden_node_element_name full_iri then
       failwith (FStar_String.concat "" ["Forbidden node element name: "; full_iri])
   | FStar_Pervasives_Native.None -> ())

(* Run all property element validations *)
let validate_property_element (st : rdfxml_state) (tag : Prims.string) (attrs : Parser_XML.xml_attribute Prims.list) : unit =
  check_no_parsetype_resource_conflict attrs;
  check_no_property_object_conflicts attrs;
  validate_rdf_id_attr attrs;
  validate_rdf_nodeid_attr attrs;
  validate_rdf_bagid_attr attrs;
  check_duplicate_rdf_id attrs;
  (* Check forbidden property element names *)
  (match resolve_name st tag with
   | FStar_Pervasives_Native.Some full_iri ->
     if is_forbidden_property_element_name full_iri then
       failwith (FStar_String.concat "" ["Forbidden property element name: "; full_iri])
   | FStar_Pervasives_Native.None -> ())

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
let maybe_reify (st : rdfxml_state)
  (attrs : Parser_XML.xml_attribute Prims.list)
  (subj : RDF_Graph_Executable.subject) (pred_iri : Prims.string)
  (obj : RDF_Graph_Executable.rdf_term) :
  RDF_Graph_Executable.triple Prims.list=
  match Parser_XML.find_attr "rdf:ID" attrs with
  | FStar_Pervasives_Native.Some id_val ->
      let reif_iri =
        resolve_iri st.base_iri (FStar_String.concat "" ["#"; id_val]) in
      make_reification_triples reif_iri subj pred_iri obj
  | FStar_Pervasives_Native.None -> []
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
let determine_subject (st : rdfxml_state)
  (attrs : Parser_XML.xml_attribute Prims.list) :
  (RDF_Graph_Executable.subject * rdfxml_state)=
  match Parser_XML.find_attr "rdf:about" attrs with
  | FStar_Pervasives_Native.Some about_val ->
      let iri = resolve_iri st.base_iri about_val in
      if RDF_Graph_Executable.is_iri iri
      then ((RDF_Graph_Executable.S_IRI iri), st)
      else
        (let uu___1 = fresh_bnode st in
         match uu___1 with
         | (bid, st') -> ((RDF_Graph_Executable.S_BNode bid), st'))
  | FStar_Pervasives_Native.None ->
      (match Parser_XML.find_attr "rdf:ID" attrs with
       | FStar_Pervasives_Native.Some id_val ->
           let iri =
             resolve_iri st.base_iri (FStar_String.concat "" ["#"; id_val]) in
           if RDF_Graph_Executable.is_iri iri
           then ((RDF_Graph_Executable.S_IRI iri), st)
           else
             (let uu___1 = fresh_bnode st in
              match uu___1 with
              | (bid, st') -> ((RDF_Graph_Executable.S_BNode bid), st'))
       | FStar_Pervasives_Native.None ->
           (match Parser_XML.find_attr "rdf:nodeID" attrs with
            | FStar_Pervasives_Native.Some nid ->
                let bid = FStar_String.concat "" ["_:"; nid] in
                ((RDF_Graph_Executable.S_BNode bid), st)
            | FStar_Pervasives_Native.None ->
                let uu___ = fresh_bnode st in
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
           let bid = FStar_String.concat "" ["_:"; nid] in
           FStar_Pervasives_Native.Some
             ((RDF_Graph_Executable.T_BNode bid), st)
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
         validate_node_element st1 tag attrs;
         let uu___1 = determine_subject st1 attrs in
         (match uu___1 with
          | (subj, st2) ->
              let type_triples =
                match resolve_name st1 tag with
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
                collect_property_attributes st1 subj attrs in
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
                  li_counter = next_li_counter
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
         validate_property_element st1 tag attrs;
         let uu___1 =
           match resolve_name st1 tag with
           | FStar_Pervasives_Native.Some full_iri ->
               if full_iri = (FStar_String.concat "" [rdf_ns; "li"])
               then
                 let uu___2 = next_li st1 in
                 (match uu___2 with
                  | (li_iri, st') ->
                      ((FStar_Pervasives_Native.Some li_iri), st'))
               else ((FStar_Pervasives_Native.Some full_iri), st1)
           | FStar_Pervasives_Native.None ->
               (FStar_Pervasives_Native.None, st1) in
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
                          let xml_content = serialize_children_xml children in
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
                                 let reif_triples =
                                   maybe_reify st2 attrs subj pred_iri obj in
                                 {
                                   pr_triples = (t :: reif_triples);
                                   pr_state = st2
                                 }
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
                               let reif_triples =
                                 maybe_reify st2 attrs subj pred_iri
                                   (RDF_Graph_Executable.T_BNode bid) in
                               let st4 = reset_li_counter st3 in
                               let child_result =
                                 process_property_children st4 bnode_subj
                                   children (fuel - Prims.int_one) in
                               {
                                 pr_triples =
                                   (FStar_List_Tot_Base.op_At (link_triple ::
                                      reif_triples) child_result.pr_triples);
                                 pr_state = (child_result.pr_state)
                               })
                      | FStar_Pervasives_Native.Some "Collection" ->
                          let collection_result =
                            process_collection st2 subj pred_iri children
                              (fuel - Prims.int_one) in
                          let reif_triples =
                            match Parser_XML.find_attr "rdf:ID" attrs with
                            | FStar_Pervasives_Native.Some uu___3 ->
                                (match collection_result.pr_triples with
                                 | first_t::uu___4 ->
                                     maybe_reify st2 attrs subj pred_iri
                                       first_t.RDF_Graph_Executable.o
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
                               let reif_triples =
                                 maybe_reify st2 attrs subj pred_iri obj in
                               {
                                 pr_triples =
                                   (FStar_List_Tot_Base.op_At (link_triple ::
                                      prop_attr_triples) reif_triples);
                                 pr_state = st3
                               }
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
                                           let reif_triples =
                                             maybe_reify st2 attrs subj
                                               pred_iri obj_term in
                                           {
                                             pr_triples =
                                               (FStar_List_Tot_Base.op_At
                                                  (link_triple ::
                                                  reif_triples)
                                                  node_result.pr_triples);
                                             pr_state =
                                               (node_result.pr_state)
                                           })
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
                                        let reif_triples =
                                          maybe_reify st2 attrs subj pred_iri
                                            (RDF_Graph_Executable.T_BNode bid) in
                                        {
                                          pr_triples =
                                            (FStar_List_Tot_Base.op_At
                                               (link_triple ::
                                               prop_attr_triples)
                                               reif_triples);
                                          pr_state = st3
                                        })
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
                                        let reif_triples =
                                          maybe_reify st2 attrs subj pred_iri
                                            obj in
                                        {
                                          pr_triples = (t :: reif_triples);
                                          pr_state = st2
                                        }
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
                  li_counter = (uu___4.li_counter)
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
  RDF_Graph_Executable.triple Prims.list=
  let fuel = (Prims.of_int (10000)) in
  match root with
  | Parser_XML.XElement (tag, attrs, children) ->
      let st1 = update_state_from_attrs st attrs in
      let is_rdf_root =
        match resolve_name st1 tag with
        | FStar_Pervasives_Native.Some full_iri ->
            full_iri = (FStar_String.concat "" [rdf_ns; "RDF"])
        | FStar_Pervasives_Native.None -> tag = "rdf:RDF" in
      if is_rdf_root
      then
        let result = process_node_elements st1 children fuel in
        result.pr_triples
      else
        (let result = process_node_element st1 root fuel in result.pr_triples)
  | uu___ -> []
let parse_rdfxml_with_base (base_iri : Prims.string) (input : Prims.string) :
  RDF_Graph_Executable.triple Prims.list=
  reset_seen_ids ();
  match Parser_XML.parse_xml_document input with
  | FStar_Pervasives_Native.Some root ->
      let st = initial_state base_iri in process_xml_tree st root
  | FStar_Pervasives_Native.None -> []
let parse_rdfxml (input : Prims.string) :
  RDF_Graph_Executable.triple Prims.list= parse_rdfxml_with_base "" input
