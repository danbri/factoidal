open Prims
type bnode_id = Prims.string
type iri = Prims.string
let rec string_has_colon_from (s : Prims.string) (pos : Prims.nat)
  (fuel : Prims.nat) : Prims.bool=
  if fuel = Prims.int_zero
  then false
  else
    (let len = FStar_String.strlen s in
     if pos >= len
     then false
     else
       if
         (FStar_Char.int_of_char (FStar_String.index s pos)) =
           (Prims.of_int (0x3A))
       then true
       else
         string_has_colon_from s (pos + Prims.int_one) (fuel - Prims.int_one))
let string_contains_colon (s : Prims.string) : Prims.bool=
  string_has_colon_from s Prims.int_zero
    ((FStar_String.strlen s) + Prims.int_one)
let is_iri (s : Prims.string) : Prims.bool=
  ((FStar_String.strlen s) > Prims.int_zero) && (string_contains_colon s)
type wf_iri = iri
let rdf_lang_string : wf_iri=
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#langString"
let xsd_string : wf_iri= "http://www.w3.org/2001/XMLSchema#string"
let xsd_integer : wf_iri= "http://www.w3.org/2001/XMLSchema#integer"
let xsd_decimal : wf_iri= "http://www.w3.org/2001/XMLSchema#decimal"
let xsd_double : wf_iri= "http://www.w3.org/2001/XMLSchema#double"
let xsd_boolean : wf_iri= "http://www.w3.org/2001/XMLSchema#boolean"
type literal =
  {
  lexical_form: Prims.string ;
  datatype: wf_iri ;
  lang_tag: Prims.string FStar_Pervasives_Native.option }
let __proj__Mkliteral__item__lexical_form (projectee : literal) :
  Prims.string=
  match projectee with
  | { lexical_form; datatype; lang_tag;_} -> lexical_form
let __proj__Mkliteral__item__datatype (projectee : literal) : wf_iri=
  match projectee with | { lexical_form; datatype; lang_tag;_} -> datatype
let __proj__Mkliteral__item__lang_tag (projectee : literal) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with | { lexical_form; datatype; lang_tag;_} -> lang_tag
let literal_wf (l : literal) : Prims.bool=
  match l.lang_tag with
  | FStar_Pervasives_Native.None -> l.datatype <> rdf_lang_string
  | FStar_Pervasives_Native.Some uu___ -> l.datatype = rdf_lang_string
type wf_literal = literal
type rdf_term =
  | T_IRI of wf_iri 
  | T_BNode of bnode_id 
  | T_Literal of wf_literal 
let uu___is_T_IRI (projectee : rdf_term) : Prims.bool=
  match projectee with | T_IRI _0 -> true | uu___ -> false
let __proj__T_IRI__item___0 (projectee : rdf_term) : wf_iri=
  match projectee with | T_IRI _0 -> _0
let uu___is_T_BNode (projectee : rdf_term) : Prims.bool=
  match projectee with | T_BNode _0 -> true | uu___ -> false
let __proj__T_BNode__item___0 (projectee : rdf_term) : bnode_id=
  match projectee with | T_BNode _0 -> _0
let uu___is_T_Literal (projectee : rdf_term) : Prims.bool=
  match projectee with | T_Literal _0 -> true | uu___ -> false
let __proj__T_Literal__item___0 (projectee : rdf_term) : wf_literal=
  match projectee with | T_Literal _0 -> _0
type subject =
  | S_IRI of wf_iri 
  | S_BNode of bnode_id 
let uu___is_S_IRI (projectee : subject) : Prims.bool=
  match projectee with | S_IRI _0 -> true | uu___ -> false
let __proj__S_IRI__item___0 (projectee : subject) : wf_iri=
  match projectee with | S_IRI _0 -> _0
let uu___is_S_BNode (projectee : subject) : Prims.bool=
  match projectee with | S_BNode _0 -> true | uu___ -> false
let __proj__S_BNode__item___0 (projectee : subject) : bnode_id=
  match projectee with | S_BNode _0 -> _0
let subject_eq (s1 : subject) (s2 : subject) : Prims.bool=
  match (s1, s2) with
  | (S_IRI i1, S_IRI i2) -> i1 = i2
  | (S_BNode b1, S_BNode b2) -> b1 = b2
  | (uu___, uu___1) -> false
let lang_tag_eq (t1 : Prims.string) (t2 : Prims.string) : Prims.bool=
  (FStar_String.lowercase t1) = (FStar_String.lowercase t2)
let lang_tag_option_eq (t1 : Prims.string FStar_Pervasives_Native.option)
  (t2 : Prims.string FStar_Pervasives_Native.option) : Prims.bool=
  match (t1, t2) with
  | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) -> true
  | (FStar_Pervasives_Native.Some s1, FStar_Pervasives_Native.Some s2) ->
      lang_tag_eq s1 s2
  | (uu___, uu___1) -> false
let literal_eq (l1 : literal) (l2 : literal) : Prims.bool=
  ((l1.lexical_form = l2.lexical_form) && (l1.datatype = l2.datatype)) &&
    (lang_tag_option_eq l1.lang_tag l2.lang_tag)
let rdf_term_eq (t1 : rdf_term) (t2 : rdf_term) : Prims.bool=
  match (t1, t2) with
  | (T_IRI i1, T_IRI i2) -> i1 = i2
  | (T_BNode b1, T_BNode b2) -> b1 = b2
  | (T_Literal l1, T_Literal l2) -> literal_eq l1 l2
  | (uu___, uu___1) -> false
let literal_value_eq (l1 : literal) (l2 : literal) : Prims.bool=
  ((l1.lexical_form = l2.lexical_form) &&
     (lang_tag_option_eq l1.lang_tag l2.lang_tag))
    && (l1.datatype = l2.datatype)
