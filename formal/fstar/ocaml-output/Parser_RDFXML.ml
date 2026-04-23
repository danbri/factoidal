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

(* RDF/XML validation: forbidden rdf: names *)
exception Rdfxml_error of string

(* Names forbidden as node element names (sec 7.2.11) *)
let forbidden_node_element_names = [
  rdf_ns ^ "RDF"; rdf_ns ^ "ID"; rdf_ns ^ "about"; rdf_ns ^ "bagID";
  rdf_ns ^ "parseType"; rdf_ns ^ "resource"; rdf_ns ^ "nodeID";
  rdf_ns ^ "li"; rdf_ns ^ "aboutEach"; rdf_ns ^ "aboutEachPrefix"
]

(* Names forbidden as property element names (sec 7.2.12) *)
let forbidden_property_element_names = [
  rdf_ns ^ "Description"; rdf_ns ^ "RDF"; rdf_ns ^ "ID"; rdf_ns ^ "about";
  rdf_ns ^ "bagID"; rdf_ns ^ "parseType"; rdf_ns ^ "resource";
  rdf_ns ^ "nodeID"; rdf_ns ^ "aboutEach"; rdf_ns ^ "aboutEachPrefix"
]

(* Validate rdf:ID / rdf:nodeID values: must be valid XML NCName.
   Now codepoint-aware: decodes UTF-8 and checks against XML 1.1
   NameStartChar / NameChar productions. Previously we approximated
   by treating every byte >= 0x80 as a valid start, which incorrectly
   accepted e.g. a leading U+0301 (combining acute — `&#x301;`).
   Reference: https://www.w3.org/TR/xml-names/#NT-NCName

   Uses Stdlib operators explicitly because open Prims shadows them with Z.t. *)
let is_valid_ncname s =
  let module S = Stdlib in
  let len = S.String.length s in
  if S.(=) len 0 then false
  else
    let byte_at i = S.Char.code (S.String.get s i) in
    (* Decode one UTF-8 codepoint starting at byte i.
       Returns (cp, bytes_consumed). Returns (-1, 1) on malformed bytes. *)
    let decode_cp i =
      let band a b = Stdlib.(land) a b in
      let bor a b = Stdlib.(lor) a b in
      let bshl a n = Stdlib.(lsl) a n in
      let b0 = byte_at i in
      if S.(<) b0 0x80 then (b0, 1)
      else if S.(<) b0 0xC0 then (-1, 1)
      else if S.(<) b0 0xE0 && S.(<) (S.(+) i 1) len then
        let b1 = byte_at (S.(+) i 1) in
        (bor (bshl (band b0 0x1F) 6) (band b1 0x3F), 2)
      else if S.(<) b0 0xF0 && S.(<) (S.(+) i 2) len then
        let b1 = byte_at (S.(+) i 1) in
        let b2 = byte_at (S.(+) i 2) in
        (bor (bor (bshl (band b0 0x0F) 12)
                  (bshl (band b1 0x3F) 6))
             (band b2 0x3F), 3)
      else if S.(<) b0 0xF8 && S.(<) (S.(+) i 3) len then
        let b1 = byte_at (S.(+) i 1) in
        let b2 = byte_at (S.(+) i 2) in
        let b3 = byte_at (S.(+) i 3) in
        (bor (bor (bor (bshl (band b0 0x07) 18)
                       (bshl (band b1 0x3F) 12))
                  (bshl (band b2 0x3F) 6))
             (band b3 0x3F), 4)
      else (-1, 1)
    in
    (* XML 1.1 NameStartChar minus ':' (= NCName start char). *)
    let is_name_start_char cp =
      (S.(>=) cp 0x41 && S.(<=) cp 0x5A) ||                (* A-Z *)
      S.(=) cp 0x5F ||                                      (* _   *)
      (S.(>=) cp 0x61 && S.(<=) cp 0x7A) ||                (* a-z *)
      (S.(>=) cp 0xC0 && S.(<=) cp 0xD6) ||
      (S.(>=) cp 0xD8 && S.(<=) cp 0xF6) ||
      (S.(>=) cp 0xF8 && S.(<=) cp 0x2FF) ||
      (S.(>=) cp 0x370 && S.(<=) cp 0x37D) ||
      (S.(>=) cp 0x37F && S.(<=) cp 0x1FFF) ||
      (S.(>=) cp 0x200C && S.(<=) cp 0x200D) ||
      (S.(>=) cp 0x2070 && S.(<=) cp 0x218F) ||
      (S.(>=) cp 0x2C00 && S.(<=) cp 0x2FEF) ||
      (S.(>=) cp 0x3001 && S.(<=) cp 0xD7FF) ||
      (S.(>=) cp 0xF900 && S.(<=) cp 0xFDCF) ||
      (S.(>=) cp 0xFDF0 && S.(<=) cp 0xFFFD) ||
      (S.(>=) cp 0x10000 && S.(<=) cp 0xEFFFF)
    in
    let is_name_char cp =
      is_name_start_char cp ||
      (S.(>=) cp 0x30 && S.(<=) cp 0x39) ||                (* 0-9 *)
      S.(=) cp 0x2D || S.(=) cp 0x2E ||                    (* - . *)
      S.(=) cp 0xB7 ||                                      (* middle dot *)
      (S.(>=) cp 0x0300 && S.(<=) cp 0x036F) ||            (* combining marks *)
      (S.(>=) cp 0x203F && S.(<=) cp 0x2040)
    in
    let (cp0, n0) = decode_cp 0 in
    if not (is_name_start_char cp0) then false
    else
      let ok = S.ref true in
      let i = S.ref n0 in
      while S.(&&) (S.(!) ok) (S.(<) (S.(!) i) len) do
        let (cp, n) = decode_cp (S.(!) i) in
        if not (is_name_char cp) then ok := false;
        i := S.(+) (S.(!) i) n
      done;
      S.(!) ok

let validate_rdf_id_attr (attrs : Parser_XML.xml_attribute list) =
  List.iter (fun (a : Parser_XML.xml_attribute) ->
    if a.attr_name = "rdf:ID" || a.attr_name = "rdf:nodeID" then
      if not (is_valid_ncname a.attr_value) then
        raise (Rdfxml_error (Printf.sprintf "Invalid %s value: %s" a.attr_name a.attr_value))
  ) attrs

(* Checks that apply on both node and property elements. *)
let check_conflicting_attrs_common (attrs : Parser_XML.xml_attribute list) =
  let has a = List.exists (fun (x : Parser_XML.xml_attribute) -> x.attr_name = a) attrs in
  if has "rdf:parseType" && has "rdf:resource" then
    raise (Rdfxml_error "conflicting rdf:parseType and rdf:resource");
  if has "rdf:aboutEach" then
    raise (Rdfxml_error "rdf:aboutEach is deprecated and forbidden");
  if has "rdf:aboutEachPrefix" then
    raise (Rdfxml_error "rdf:aboutEachPrefix is deprecated and forbidden");
  (* rdf:bagID was removed in RDF 1.1 (§18 of the Concepts spec).
     Accept as an explicit error; error006/error007 exercise this. *)
  if has "rdf:bagID" then
    raise (Rdfxml_error "rdf:bagID is not supported in RDF 1.1");
  (* rdf:li is an element name, never an attribute. Covers
     rdf-containers-syntax-vs-schema-error001. *)
  if has "rdf:li" then
    raise (Rdfxml_error "rdf:li may not be used as an attribute")

(* Retained name for the node-element path: adds the node-scoped
   mutual-exclusion rules on top of the common checks.
   On a node element, rdf:ID / rdf:about / rdf:nodeID all identify
   the node itself, so any two together are contradictory. *)
let check_conflicting_attrs (attrs : Parser_XML.xml_attribute list) =
  check_conflicting_attrs_common attrs;
  let has a = List.exists (fun (x : Parser_XML.xml_attribute) -> x.attr_name = a) attrs in
  if has "rdf:nodeID" && has "rdf:ID" then
    raise (Rdfxml_error "conflicting rdf:nodeID and rdf:ID on a node element");
  if has "rdf:nodeID" && has "rdf:about" then
    raise (Rdfxml_error "conflicting rdf:nodeID and rdf:about on a node element");
  if has "rdf:ID" && has "rdf:about" then
    raise (Rdfxml_error "conflicting rdf:ID and rdf:about on a node element")

(* For property elements, rdf:ID identifies the *statement* (for
   reification), not the object. It can legitimately co-occur with
   rdf:nodeID (which picks the object) — see rdfms-syntax-incomplete-
   test004. The only mutual-exclusion at the object-identifying
   level is rdf:nodeID + rdf:resource (both pick the object). *)
let check_conflicting_attrs_property (attrs : Parser_XML.xml_attribute list) =
  check_conflicting_attrs_common attrs;
  let has a = List.exists (fun (x : Parser_XML.xml_attribute) -> x.attr_name = a) attrs in
  if has "rdf:nodeID" && has "rdf:resource" then
    raise (Rdfxml_error "conflicting rdf:nodeID and rdf:resource on a property element")

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
        if pos >= len
        then (name, "")
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
let resolve_iri (base : Prims.string) (rel : Prims.string) : Prims.string=
  if (FStar_String.strlen rel) = Prims.int_zero
  then base
  else
    if is_absolute_iri rel
    then rel
    else
      if (FStar_String.strlen base) = Prims.int_zero
      then rel
      else Parser_IRI.resolve_iri_v2 base rel
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
let rec strip_fragment_from (s : Prims.string) (pos : Prims.nat)
  (fuel : Prims.nat) : Prims.string=
  let len = FStar_String.strlen s in
  if (fuel = Prims.int_zero) || (pos >= len)
  then s
  else
    (let c = FStar_Char.int_of_char (FStar_String.index s pos) in
     if c = (Prims.of_int (0x23))
     then FStar_String.sub s Prims.int_zero pos
     else strip_fragment_from s (pos + Prims.int_one) (fuel - Prims.int_one))
let strip_fragment (s : Prims.string) : Prims.string=
  strip_fragment_from s Prims.int_zero
    ((FStar_String.strlen s) + Prims.int_one)
let extract_base (attrs : Parser_XML.xml_attribute Prims.list)
  (current_base : Prims.string) : Prims.string=
  match Parser_XML.find_attr "xml:base" attrs with
  | FStar_Pervasives_Native.Some base_val ->
      strip_fragment (resolve_iri current_base base_val)
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
let rdf_statement_iri : Prims.string=
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#Statement"
let rdf_subject_iri : Prims.string=
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#subject"
let rdf_predicate_iri : Prims.string=
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#predicate"
let rdf_object_iri : Prims.string=
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#object"
let subject_to_term (s : RDF_Graph_Executable.subject) :
  RDF_Graph_Executable.rdf_term=
  match s with
  | RDF_Graph_Executable.S_IRI i -> RDF_Graph_Executable.T_IRI i
  | RDF_Graph_Executable.S_BNode b -> RDF_Graph_Executable.T_BNode b
let make_reification_triples (reif_iri : Prims.string)
  (subj : RDF_Graph_Executable.subject) (pred_iri : Prims.string)
  (obj : RDF_Graph_Executable.rdf_term) :
  RDF_Graph_Executable.triple Prims.list=
  if
    (Prims.op_Negation (RDF_Graph_Executable.is_iri reif_iri)) ||
      (Prims.op_Negation (RDF_Graph_Executable.is_iri pred_iri))
  then []
  else
    if
      ((((Prims.op_Negation (RDF_Graph_Executable.is_iri rdf_type_iri)) ||
           (Prims.op_Negation (RDF_Graph_Executable.is_iri rdf_statement_iri)))
          ||
          (Prims.op_Negation (RDF_Graph_Executable.is_iri rdf_subject_iri)))
         ||
         (Prims.op_Negation (RDF_Graph_Executable.is_iri rdf_predicate_iri)))
        || (Prims.op_Negation (RDF_Graph_Executable.is_iri rdf_object_iri))
    then []
    else
      (let reif_s = RDF_Graph_Executable.S_IRI reif_iri in
       [{
          RDF_Graph_Executable.s = reif_s;
          RDF_Graph_Executable.p = rdf_type_iri;
          RDF_Graph_Executable.o =
            (RDF_Graph_Executable.T_IRI rdf_statement_iri)
        };
       {
         RDF_Graph_Executable.s = reif_s;
         RDF_Graph_Executable.p = rdf_subject_iri;
         RDF_Graph_Executable.o = (subject_to_term subj)
       };
       {
         RDF_Graph_Executable.s = reif_s;
         RDF_Graph_Executable.p = rdf_predicate_iri;
         RDF_Graph_Executable.o = (RDF_Graph_Executable.T_IRI pred_iri)
       };
       {
         RDF_Graph_Executable.s = reif_s;
         RDF_Graph_Executable.p = rdf_object_iri;
         RDF_Graph_Executable.o = obj
       }])
let compute_reif_iri (st : rdfxml_state)
  (attrs : Parser_XML.xml_attribute Prims.list) :
  Prims.string FStar_Pervasives_Native.option=
  match Parser_XML.find_attr "rdf:ID" attrs with
  | FStar_Pervasives_Native.Some id_val ->
      let frag = FStar_String.concat "" ["#"; id_val] in
      let r = resolve_iri st.base_iri frag in
      if RDF_Graph_Executable.is_iri r
      then FStar_Pervasives_Native.Some r
      else FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
let rec process_node_element (st : rdfxml_state) (node : Parser_XML.xml_node)
  (fuel : Prims.nat) : process_result=
  if fuel = Prims.int_zero
  then empty_result st
  else
    (match node with
     | Parser_XML.XElement (tag, attrs, children) ->
         (* Validate: reject forbidden rdf: names as node elements *)
         (match resolve_name st tag with
          | Some full_iri ->
            if List.mem full_iri forbidden_node_element_names then
              raise (Rdfxml_error (Printf.sprintf "Forbidden node element name: %s" full_iri))
          | None -> ());
         validate_rdf_id_attr attrs;
         check_conflicting_attrs attrs;
         let st1 = update_state_from_attrs st attrs in
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
          | Parser_XML.XElement (uu___1, uu___2, uu___3) ->
              let result1 =
                process_property_element st subj child (fuel - Prims.int_one) in
              let result2 =
                process_property_children result1.pr_state subj rest
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
         (* Validate: reject forbidden rdf: names as property elements *)
         (match resolve_name st tag with
          | Some full_iri ->
            if List.mem full_iri forbidden_property_element_names then
              raise (Rdfxml_error (Printf.sprintf "Forbidden property element name: %s" full_iri));
            (* rdf:Bag/Seq/Alt ARE legal as property element names per
               RDF/XML §7.2.2.1 — they are just IRIs in the rdf: namespace
               when used as predicates. The guard that used to reject them
               here failed tests rdfms-rdf-names-use-test-017/018/019. *)
            ()
          | None -> ());
         validate_rdf_id_attr attrs;
         check_conflicting_attrs_property attrs;
         let st1 = update_state_from_attrs st attrs in
         let reif_iri_opt = compute_reif_iri st1 attrs in
         let reif_of pred_iri obj =
           match reif_iri_opt with
           | FStar_Pervasives_Native.Some r ->
               make_reification_triples r subj pred_iri obj
           | FStar_Pervasives_Native.None -> [] in
         let uu___1 =
           match resolve_name st1 tag with
           | FStar_Pervasives_Native.Some full_iri ->
               if full_iri = (FStar_String.concat "" [rdf_ns; "li"])
               then
                 let uu___2 = next_li st1 in
                 (match uu___2 with
                  | (li_iri, st') ->
                      if RDF_Graph_Executable.is_iri li_iri
                      then ((FStar_Pervasives_Native.Some li_iri), st')
                      else (FStar_Pervasives_Native.None, st'))
               else
                 if RDF_Graph_Executable.is_iri full_iri
                 then ((FStar_Pervasives_Native.Some full_iri), st1)
                 else (FStar_Pervasives_Native.None, st1)
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
                                 {
                                   pr_triples = (t :: (reif_of pred_iri obj));
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
                               let obj_term =
                                 RDF_Graph_Executable.T_BNode bid in
                               let link_triple =
                                 {
                                   RDF_Graph_Executable.s = subj;
                                   RDF_Graph_Executable.p = pred_iri;
                                   RDF_Graph_Executable.o = obj_term
                                 } in
                               let st4 = reset_li_counter st3 in
                               let child_result =
                                 process_property_children st4 bnode_subj
                                   children (fuel - Prims.int_one) in
                               {
                                 pr_triples =
                                   (FStar_List_Tot_Base.op_At (link_triple ::
                                      (reif_of pred_iri obj_term))
                                      child_result.pr_triples);
                                 pr_state = (child_result.pr_state)
                               })
                      | FStar_Pervasives_Native.Some "Collection" ->
                          let collection_result =
                            process_collection st2 subj pred_iri reif_iri_opt
                              children (fuel - Prims.int_one) in
                          collection_result
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
                               {
                                 pr_triples =
                                   (FStar_List_Tot_Base.op_At (link_triple ::
                                      (reif_of pred_iri obj))
                                      prop_attr_triples);
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
                                           {
                                             pr_triples =
                                               (FStar_List_Tot_Base.op_At
                                                  (link_triple ::
                                                  (reif_of pred_iri obj_term))
                                                  node_result.pr_triples);
                                             pr_state =
                                               (node_result.pr_state)
                                           })
                                  | [] -> empty_result st2)
                               else
                                 (let text_val = collect_text children in
                                  let has_text =
                                    (FStar_String.strlen text_val) >
                                      Prims.int_zero in
                                  let has_datatype =
                                    match datatype_opt with
                                    | FStar_Pervasives_Native.Some uu___5 ->
                                        true
                                    | FStar_Pervasives_Native.None -> false in
                                  let probe_triples =
                                    let uu___5 = fresh_bnode st2 in
                                    match uu___5 with
                                    | (probe_bid, uu___6) ->
                                        collect_property_attributes st2
                                          (RDF_Graph_Executable.S_BNode
                                             probe_bid) attrs in
                                  if
                                    ((Prims.op_Negation has_text) &&
                                       (Prims.op_Negation has_datatype))
                                      &&
                                      ((FStar_List_Tot_Base.length
                                          probe_triples)
                                         > Prims.int_zero)
                                  then
                                    let uu___5 = fresh_bnode st2 in
                                    match uu___5 with
                                    | (bid, st3) ->
                                        let bnode_subj =
                                          RDF_Graph_Executable.S_BNode bid in
                                        let obj_term =
                                          RDF_Graph_Executable.T_BNode bid in
                                        let link_triple =
                                          {
                                            RDF_Graph_Executable.s = subj;
                                            RDF_Graph_Executable.p = pred_iri;
                                            RDF_Graph_Executable.o = obj_term
                                          } in
                                        let prop_attr_triples =
                                          collect_property_attributes st3
                                            bnode_subj attrs in
                                        {
                                          pr_triples =
                                            (FStar_List_Tot_Base.op_At
                                               (link_triple ::
                                               (reif_of pred_iri obj_term))
                                               prop_attr_triples);
                                          pr_state = st3
                                        }
                                  else
                                    (let obj_opt =
                                       match datatype_opt with
                                       | FStar_Pervasives_Native.Some dt ->
                                           let full_dt =
                                             resolve_iri st2.base_iri dt in
                                           make_typed_literal text_val
                                             full_dt
                                       | FStar_Pervasives_Native.None ->
                                           make_plain_literal text_val
                                             st2.lang in
                                     match obj_opt with
                                     | FStar_Pervasives_Native.Some obj ->
                                         let t =
                                           {
                                             RDF_Graph_Executable.s = subj;
                                             RDF_Graph_Executable.p =
                                               pred_iri;
                                             RDF_Graph_Executable.o = obj
                                           } in
                                         {
                                           pr_triples = (t ::
                                             (reif_of pred_iri obj));
                                           pr_state = st2
                                         }
                                     | FStar_Pervasives_Native.None ->
                                         empty_result st2))))))
     | uu___1 -> empty_result st)
and process_collection (st : rdfxml_state)
  (subj : RDF_Graph_Executable.subject) (pred_iri : Prims.string)
  (reif_iri_opt : Prims.string FStar_Pervasives_Native.option)
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
     let reif_for obj =
       match reif_iri_opt with
       | FStar_Pervasives_Native.Some r ->
           make_reification_triples r subj pred_iri obj
       | FStar_Pervasives_Native.None -> [] in
     if (FStar_List_Tot_Base.length elem_items) = Prims.int_zero
     then
       (if
          (RDF_Graph_Executable.is_iri rdf_nil_iri) &&
            (RDF_Graph_Executable.is_iri pred_iri)
        then
          let obj = RDF_Graph_Executable.T_IRI rdf_nil_iri in
          let t =
            {
              RDF_Graph_Executable.s = subj;
              RDF_Graph_Executable.p = pred_iri;
              RDF_Graph_Executable.o = obj
            } in
          { pr_triples = (t :: (reif_for obj)); pr_state = st }
        else empty_result st)
     else
       build_collection_list st subj pred_iri reif_iri_opt elem_items
         (fuel - Prims.int_one))
and build_collection_list (st : rdfxml_state)
  (subj : RDF_Graph_Executable.subject) (pred_iri : Prims.string)
  (reif_iri_opt : Prims.string FStar_Pervasives_Native.option)
  (items : Parser_XML.xml_node Prims.list) (fuel : Prims.nat) :
  process_result=
  if fuel = Prims.int_zero
  then empty_result st
  else
    (let reif_for obj =
       match reif_iri_opt with
       | FStar_Pervasives_Native.Some r ->
           make_reification_triples r subj pred_iri obj
       | FStar_Pervasives_Native.None -> [] in
     match items with
     | [] ->
         if
           (RDF_Graph_Executable.is_iri rdf_nil_iri) &&
             (RDF_Graph_Executable.is_iri pred_iri)
         then
           let obj = RDF_Graph_Executable.T_IRI rdf_nil_iri in
           let t =
             {
               RDF_Graph_Executable.s = subj;
               RDF_Graph_Executable.p = pred_iri;
               RDF_Graph_Executable.o = obj
             } in
           { pr_triples = (t :: (reif_for obj)); pr_state = st }
         else empty_result st
     | item::rest ->
         if Prims.op_Negation (RDF_Graph_Executable.is_iri pred_iri)
         then empty_result st
         else
           (let uu___2 = fresh_bnode st in
            match uu___2 with
            | (list_bid, st2) ->
                let list_node = RDF_Graph_Executable.S_BNode list_bid in
                let link_obj = RDF_Graph_Executable.T_BNode list_bid in
                let link_triple =
                  {
                    RDF_Graph_Executable.s = subj;
                    RDF_Graph_Executable.p = pred_iri;
                    RDF_Graph_Executable.o = link_obj
                  } in
                let link_reif = reif_for link_obj in
                let item_result =
                  process_node_element st2 item (fuel - Prims.int_one) in
                let item_st =
                  update_state_from_attrs item_result.pr_state
                    (Parser_XML.element_attrs item) in
                let uu___3 =
                  determine_subject item_st (Parser_XML.element_attrs item) in
                (match uu___3 with
                 | (item_subj, st3) ->
                     let item_term =
                       match item_subj with
                       | RDF_Graph_Executable.S_IRI i ->
                           RDF_Graph_Executable.T_IRI i
                       | RDF_Graph_Executable.S_BNode b ->
                           RDF_Graph_Executable.T_BNode b in
                     if RDF_Graph_Executable.is_iri rdf_first_iri
                     then
                       let first_triple =
                         {
                           RDF_Graph_Executable.s = list_node;
                           RDF_Graph_Executable.p = rdf_first_iri;
                           RDF_Graph_Executable.o = item_term
                         } in
                       let rest_result =
                         if RDF_Graph_Executable.is_iri rdf_rest_iri
                         then
                           build_collection_list st3 list_node rdf_rest_iri
                             FStar_Pervasives_Native.None rest
                             (fuel - Prims.int_one)
                         else empty_result st3 in
                       let all_triples =
                         FStar_List_Tot_Base.op_At (link_triple :: link_reif)
                           (FStar_List_Tot_Base.op_At (first_triple ::
                              (item_result.pr_triples))
                              rest_result.pr_triples) in
                       {
                         pr_triples = all_triples;
                         pr_state = (rest_result.pr_state)
                       }
                     else
                       (let rest_result =
                          if RDF_Graph_Executable.is_iri rdf_rest_iri
                          then
                            build_collection_list st3 list_node rdf_rest_iri
                              FStar_Pervasives_Native.None rest
                              (fuel - Prims.int_one)
                          else empty_result st3 in
                        let all_triples =
                          FStar_List_Tot_Base.op_At (link_triple ::
                            link_reif)
                            (FStar_List_Tot_Base.op_At item_result.pr_triples
                               rest_result.pr_triples) in
                        {
                          pr_triples = all_triples;
                          pr_state = (rest_result.pr_state)
                        }))))
let restore_scope (parent : rdfxml_state) (child : rdfxml_state) :
  rdfxml_state=
  {
    base_iri = (parent.base_iri);
    namespaces = (parent.namespaces);
    lang = (parent.lang);
    bnode_counter = (child.bnode_counter);
    li_counter = (parent.li_counter)
  }
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
              let st' = restore_scope st result1.pr_state in
              let result2 =
                process_node_elements st' rest (fuel - Prims.int_one) in
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
  match Parser_XML.parse_xml_document input with
  | FStar_Pervasives_Native.Some root ->
      let st = initial_state base_iri in process_xml_tree st root
  | FStar_Pervasives_Native.None -> []
let parse_rdfxml (input : Prims.string) :
  RDF_Graph_Executable.triple Prims.list= parse_rdfxml_with_base "" input
