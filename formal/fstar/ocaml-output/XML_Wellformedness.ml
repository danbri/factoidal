open Prims
let rdf_ns : Prims.string= "http://www.w3.org/1999/02/22-rdf-syntax-ns#"
let is_name_start_char (cp : Prims.int) : Prims.bool=
  (((((((((((((((cp >= (Prims.of_int (0x41))) &&
                  (cp <= (Prims.of_int (0x5A))))
                 || (cp = (Prims.of_int (0x5F))))
                ||
                ((cp >= (Prims.of_int (0x61))) &&
                   (cp <= (Prims.of_int (0x7A)))))
               ||
               ((cp >= (Prims.of_int (0xC0))) &&
                  (cp <= (Prims.of_int (0xD6)))))
              ||
              ((cp >= (Prims.of_int (0xD8))) && (cp <= (Prims.of_int (0xF6)))))
             ||
             ((cp >= (Prims.of_int (0xF8))) && (cp <= (Prims.of_int (0x2FF)))))
            ||
            ((cp >= (Prims.of_int (0x370))) && (cp <= (Prims.of_int (0x37D)))))
           ||
           ((cp >= (Prims.of_int (0x37F))) && (cp <= (Prims.of_int (0x1FFF)))))
          ||
          ((cp >= (Prims.of_int (0x200C))) && (cp <= (Prims.of_int (0x200D)))))
         ||
         ((cp >= (Prims.of_int (0x2070))) && (cp <= (Prims.of_int (0x218F)))))
        ||
        ((cp >= (Prims.of_int (0x2C00))) && (cp <= (Prims.of_int (0x2FEF)))))
       ||
       ((cp >= (Prims.of_int (0x3001))) && (cp <= (Prims.of_int (0xD7FF)))))
      || ((cp >= (Prims.of_int (0xF900))) && (cp <= (Prims.of_int (0xFDCF)))))
     || ((cp >= (Prims.of_int (0xFDF0))) && (cp <= (Prims.of_int (0xFFFD)))))
    ||
    ((cp >= (Prims.parse_int "0x10000")) &&
       (cp <= (Prims.parse_int "0xEFFFF")))
let is_name_char (cp : Prims.int) : Prims.bool=
  ((((((is_name_start_char cp) ||
         ((cp >= (Prims.of_int (0x30))) && (cp <= (Prims.of_int (0x39)))))
        || (cp = (Prims.of_int (0x2D))))
       || (cp = (Prims.of_int (0x2E))))
      || (cp = (Prims.of_int (0xB7))))
     || ((cp >= (Prims.of_int (0x0300))) && (cp <= (Prims.of_int (0x036F)))))
    || ((cp >= (Prims.of_int (0x203F))) && (cp <= (Prims.of_int (0x2040))))
let rec all_name_char (cps : FStar_Char.char Prims.list) : Prims.bool=
  match cps with
  | [] -> true
  | c::rest ->
      if is_name_char (FStar_Char.int_of_char c)
      then all_name_char rest
      else false
let is_valid_ncname (s : Prims.string) : Prims.bool=
  match FStar_String.list_of_string s with
  | [] -> false
  | c::rest ->
      if is_name_start_char (FStar_Char.int_of_char c)
      then all_name_char rest
      else false
let forbidden_node_element_names : Prims.string Prims.list=
  [Prims.strcat rdf_ns "RDF";
  Prims.strcat rdf_ns "ID";
  Prims.strcat rdf_ns "about";
  Prims.strcat rdf_ns "bagID";
  Prims.strcat rdf_ns "parseType";
  Prims.strcat rdf_ns "resource";
  Prims.strcat rdf_ns "nodeID";
  Prims.strcat rdf_ns "li";
  Prims.strcat rdf_ns "aboutEach";
  Prims.strcat rdf_ns "aboutEachPrefix"]
let forbidden_property_element_names : Prims.string Prims.list=
  [Prims.strcat rdf_ns "Description";
  Prims.strcat rdf_ns "RDF";
  Prims.strcat rdf_ns "ID";
  Prims.strcat rdf_ns "about";
  Prims.strcat rdf_ns "bagID";
  Prims.strcat rdf_ns "parseType";
  Prims.strcat rdf_ns "resource";
  Prims.strcat rdf_ns "nodeID";
  Prims.strcat rdf_ns "aboutEach";
  Prims.strcat rdf_ns "aboutEachPrefix"]
let rec mem_string (x : Prims.string) (xs : Prims.string Prims.list) :
  Prims.bool=
  match xs with
  | [] -> false
  | y::rest -> if x = y then true else mem_string x rest
let is_forbidden_node_element_name (full_iri : Prims.string) : Prims.bool=
  mem_string full_iri forbidden_node_element_names
let is_forbidden_property_element_name (full_iri : Prims.string) :
  Prims.bool= mem_string full_iri forbidden_property_element_names
let rec validate_rdf_id_attr
  (attrs : (Prims.string * Prims.string) Prims.list) :
  Prims.string FStar_Pervasives_Native.option=
  match attrs with
  | [] -> FStar_Pervasives_Native.None
  | (name, value)::rest ->
      if
        ((name = "rdf:ID") || (name = "rdf:nodeID")) &&
          (Prims.op_Negation (is_valid_ncname value))
      then
        FStar_Pervasives_Native.Some
          (FStar_String.concat "" ["Invalid "; name; " value: "; value])
      else validate_rdf_id_attr rest
let rec has_attr (name : Prims.string)
  (attrs : (Prims.string * Prims.string) Prims.list) : Prims.bool=
  match attrs with
  | [] -> false
  | (n, uu___)::rest -> if n = name then true else has_attr name rest
let check_conflicting_attrs_common
  (attrs : (Prims.string * Prims.string) Prims.list) :
  Prims.string FStar_Pervasives_Native.option=
  if (has_attr "rdf:parseType" attrs) && (has_attr "rdf:resource" attrs)
  then
    FStar_Pervasives_Native.Some "conflicting rdf:parseType and rdf:resource"
  else
    if has_attr "rdf:aboutEach" attrs
    then
      FStar_Pervasives_Native.Some
        "rdf:aboutEach is deprecated and forbidden"
    else
      if has_attr "rdf:aboutEachPrefix" attrs
      then
        FStar_Pervasives_Native.Some
          "rdf:aboutEachPrefix is deprecated and forbidden"
      else
        if has_attr "rdf:bagID" attrs
        then
          FStar_Pervasives_Native.Some
            "rdf:bagID is not supported in RDF 1.1"
        else
          if has_attr "rdf:li" attrs
          then
            FStar_Pervasives_Native.Some
              "rdf:li may not be used as an attribute"
          else FStar_Pervasives_Native.None
let check_conflicting_attrs_node
  (attrs : (Prims.string * Prims.string) Prims.list) :
  Prims.string FStar_Pervasives_Native.option=
  match check_conflicting_attrs_common attrs with
  | FStar_Pervasives_Native.Some msg -> FStar_Pervasives_Native.Some msg
  | FStar_Pervasives_Native.None ->
      if (has_attr "rdf:nodeID" attrs) && (has_attr "rdf:ID" attrs)
      then
        FStar_Pervasives_Native.Some
          "conflicting rdf:nodeID and rdf:ID on a node element"
      else
        if (has_attr "rdf:nodeID" attrs) && (has_attr "rdf:about" attrs)
        then
          FStar_Pervasives_Native.Some
            "conflicting rdf:nodeID and rdf:about on a node element"
        else
          if (has_attr "rdf:ID" attrs) && (has_attr "rdf:about" attrs)
          then
            FStar_Pervasives_Native.Some
              "conflicting rdf:ID and rdf:about on a node element"
          else FStar_Pervasives_Native.None
let check_conflicting_attrs_property
  (attrs : (Prims.string * Prims.string) Prims.list) :
  Prims.string FStar_Pervasives_Native.option=
  match check_conflicting_attrs_common attrs with
  | FStar_Pervasives_Native.Some msg -> FStar_Pervasives_Native.Some msg
  | FStar_Pervasives_Native.None ->
      if (has_attr "rdf:nodeID" attrs) && (has_attr "rdf:resource" attrs)
      then
        FStar_Pervasives_Native.Some
          "conflicting rdf:nodeID and rdf:resource on a property element"
      else FStar_Pervasives_Native.None
