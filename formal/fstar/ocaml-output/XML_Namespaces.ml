open Prims
let xml_ns_uri : Prims.string= "http://www.w3.org/XML/1998/namespace"
let xmlns_ns_uri : Prims.string= "http://www.w3.org/2000/xmlns/"
type qname_split =
  | QSimple of Prims.string 
  | QPrefixed of Prims.string * Prims.string 
  | QMalformed 
let uu___is_QSimple (projectee : qname_split) : Prims.bool=
  match projectee with | QSimple local -> true | uu___ -> false
let __proj__QSimple__item__local (projectee : qname_split) : Prims.string=
  match projectee with | QSimple local -> local
let uu___is_QPrefixed (projectee : qname_split) : Prims.bool=
  match projectee with | QPrefixed (prefix, local) -> true | uu___ -> false
let __proj__QPrefixed__item__prefix (projectee : qname_split) : Prims.string=
  match projectee with | QPrefixed (prefix, local) -> prefix
let __proj__QPrefixed__item__local (projectee : qname_split) : Prims.string=
  match projectee with | QPrefixed (prefix, local) -> local
let uu___is_QMalformed (projectee : qname_split) : Prims.bool=
  match projectee with | QMalformed -> true | uu___ -> false
let rec find_colon_positions (s : Prims.string) (pos : Prims.nat)
  (limit : Prims.nat) (fuel : Prims.nat) (acc : Prims.nat Prims.list) :
  Prims.nat Prims.list=
  if fuel = Prims.int_zero
  then FStar_List_Tot_Base.rev acc
  else
    if pos >= limit
    then FStar_List_Tot_Base.rev acc
    else
      (let c = Parser_FastString.fs_byte_index s pos in
       if c = 58
       then
         find_colon_positions s (pos + Prims.int_one) limit
           (fuel - Prims.int_one) (pos :: acc)
       else
         find_colon_positions s (pos + Prims.int_one) limit
           (fuel - Prims.int_one) acc)
let split_qname (s : Prims.string) : qname_split=
  let len = Parser_FastString.fs_byte_length s in
  match find_colon_positions s Prims.int_zero len len [] with
  | [] -> QSimple s
  | i::[] ->
      if (i = Prims.int_zero) || ((i + Prims.int_one) >= len)
      then QMalformed
      else
        QPrefixed
          ((Parser_FastString.fs_byte_sub s Prims.int_zero i),
            (Parser_FastString.fs_byte_sub s (i + Prims.int_one)
               (len - (i + Prims.int_one))))
  | uu___ -> QMalformed
type ns_scope =
  (Prims.string * Prims.string FStar_Pervasives_Native.option) Prims.list
let initial_scope : ns_scope=
  [("xml", (FStar_Pervasives_Native.Some xml_ns_uri))]
let rec lookup_prefix (scope : ns_scope) (prefix : Prims.string) :
  Prims.string FStar_Pervasives_Native.option=
  match scope with
  | [] -> FStar_Pervasives_Native.None
  | (p, u)::rest -> if p = prefix then u else lookup_prefix rest prefix
let rec apply_declarations (version : Prims.string) (scope : ns_scope)
  (attrs : Parser_XML.xml_attribute Prims.list) :
  ns_scope FStar_Pervasives_Native.option=
  match attrs with
  | [] -> FStar_Pervasives_Native.Some scope
  | a::rest ->
      (match split_qname a.Parser_XML.attr_name with
       | QSimple "xmlns" ->
           let v = a.Parser_XML.attr_value in
           if (v = xml_ns_uri) || (v = xmlns_ns_uri)
           then FStar_Pervasives_Native.None
           else
             (let entry =
                if v = ""
                then ("", FStar_Pervasives_Native.None)
                else ("", (FStar_Pervasives_Native.Some v)) in
              match apply_declarations version scope rest with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some sc ->
                  FStar_Pervasives_Native.Some (entry :: sc))
       | QPrefixed ("xmlns", local) ->
           let v = a.Parser_XML.attr_value in
           if local = "xmlns"
           then FStar_Pervasives_Native.None
           else
             if (local = "xml") && (v <> xml_ns_uri)
             then FStar_Pervasives_Native.None
             else
               if (local <> "xml") && (v = xml_ns_uri)
               then FStar_Pervasives_Native.None
               else
                 if v = xmlns_ns_uri
                 then FStar_Pervasives_Native.None
                 else
                   if (v = "") && (version <> "1.1")
                   then FStar_Pervasives_Native.None
                   else
                     (let entry =
                        if v = ""
                        then (local, FStar_Pervasives_Native.None)
                        else (local, (FStar_Pervasives_Native.Some v)) in
                      match apply_declarations version scope rest with
                      | FStar_Pervasives_Native.None ->
                          FStar_Pervasives_Native.None
                      | FStar_Pervasives_Native.Some sc ->
                          FStar_Pervasives_Native.Some (entry :: sc))
       | uu___ -> apply_declarations version scope rest)
let rec all_attr_names_wellformed
  (attrs : Parser_XML.xml_attribute Prims.list) : Prims.bool=
  match attrs with
  | [] -> true
  | a::rest ->
      (match split_qname a.Parser_XML.attr_name with
       | QMalformed -> false
       | uu___ -> all_attr_names_wellformed rest)
let tag_prefix_bound (scope : ns_scope) (qs : qname_split) : Prims.bool=
  match qs with
  | QSimple uu___ -> true
  | QPrefixed (pfx, uu___) ->
      (match lookup_prefix scope pfx with
       | FStar_Pervasives_Native.Some uu___1 -> true
       | FStar_Pervasives_Native.None -> false)
  | QMalformed -> false
let rec attrs_prefixes_bound (scope : ns_scope)
  (attrs : Parser_XML.xml_attribute Prims.list) : Prims.bool=
  match attrs with
  | [] -> true
  | a::rest ->
      (match split_qname a.Parser_XML.attr_name with
       | QSimple "xmlns" -> attrs_prefixes_bound scope rest
       | QPrefixed ("xmlns", uu___) -> attrs_prefixes_bound scope rest
       | QSimple uu___ -> attrs_prefixes_bound scope rest
       | QPrefixed (pfx, uu___) ->
           (match lookup_prefix scope pfx with
            | FStar_Pervasives_Native.Some uu___1 ->
                attrs_prefixes_bound scope rest
            | FStar_Pervasives_Native.None -> false)
       | QMalformed -> false)
let expand_attr_key (scope : ns_scope) (a : Parser_XML.xml_attribute) :
  (Prims.string FStar_Pervasives_Native.option * Prims.string)
    FStar_Pervasives_Native.option=
  match split_qname a.Parser_XML.attr_name with
  | QSimple "xmlns" -> FStar_Pervasives_Native.None
  | QPrefixed ("xmlns", uu___) -> FStar_Pervasives_Native.None
  | QSimple name ->
      FStar_Pervasives_Native.Some (FStar_Pervasives_Native.None, name)
  | QPrefixed (pfx, local) ->
      FStar_Pervasives_Native.Some ((lookup_prefix scope pfx), local)
  | QMalformed -> FStar_Pervasives_Native.None
let rec expand_attr_keys (scope : ns_scope)
  (attrs : Parser_XML.xml_attribute Prims.list) :
  (Prims.string FStar_Pervasives_Native.option * Prims.string) Prims.list=
  match attrs with
  | [] -> []
  | a::rest ->
      (match expand_attr_key scope a with
       | FStar_Pervasives_Native.Some k -> k :: (expand_attr_keys scope rest)
       | FStar_Pervasives_Native.None -> expand_attr_keys scope rest)
let rec mem_key
  (k : (Prims.string FStar_Pervasives_Native.option * Prims.string))
  (ks :
    (Prims.string FStar_Pervasives_Native.option * Prims.string) Prims.list)
  : Prims.bool=
  match ks with
  | [] -> false
  | k2::rest -> if k = k2 then true else mem_key k rest
let rec keys_unique
  (ks :
    (Prims.string FStar_Pervasives_Native.option * Prims.string) Prims.list)
  : Prims.bool=
  match ks with
  | [] -> true
  | k::rest -> if mem_key k rest then false else keys_unique rest
let attrs_unique_expanded (scope : ns_scope)
  (attrs : Parser_XML.xml_attribute Prims.list) : Prims.bool=
  keys_unique (expand_attr_keys scope attrs)
let rec check_element (version : Prims.string) (scope : ns_scope)
  (node : Parser_XML.xml_node) : Prims.bool=
  match node with
  | Parser_XML.XElement (tag, attrs, children) ->
      (match split_qname tag with
       | QMalformed -> false
       | tag_split ->
           if Prims.op_Negation (all_attr_names_wellformed attrs)
           then false
           else
             (match apply_declarations version scope attrs with
              | FStar_Pervasives_Native.None -> false
              | FStar_Pervasives_Native.Some new_scope ->
                  if Prims.op_Negation (tag_prefix_bound new_scope tag_split)
                  then false
                  else
                    if
                      Prims.op_Negation
                        (attrs_prefixes_bound new_scope attrs)
                    then false
                    else
                      if
                        Prims.op_Negation
                          (attrs_unique_expanded new_scope attrs)
                      then false
                      else check_children version new_scope children))
  | uu___ -> true
and check_children (version : Prims.string) (scope : ns_scope)
  (nodes : Parser_XML.xml_node Prims.list) : Prims.bool=
  match nodes with
  | [] -> true
  | hd::tl ->
      if check_element version scope hd
      then check_children version scope tl
      else false
let is_namespace_wellformed (version : Prims.string)
  (root : Parser_XML.xml_node) : Prims.bool=
  check_element version initial_scope root
