open Prims
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
type bnode_id = Prims.string
type iri = Prims.string
type wf_iri = iri
let rdf_lang_string : wf_iri=
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#langString"
let rdf_dir_lang_string : wf_iri=
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#dirLangString"
type text_direction =
  | Dir_LTR 
  | Dir_RTL 
let uu___is_Dir_LTR (projectee : text_direction) : Prims.bool=
  match projectee with | Dir_LTR -> true | uu___ -> false
let uu___is_Dir_RTL (projectee : text_direction) : Prims.bool=
  match projectee with | Dir_RTL -> true | uu___ -> false
type literal =
  {
  lexical_form: Prims.string ;
  datatype: wf_iri ;
  lang_tag: Prims.string FStar_Pervasives_Native.option ;
  direction: text_direction FStar_Pervasives_Native.option }
let __proj__Mkliteral__item__lexical_form (projectee : literal) :
  Prims.string=
  match projectee with
  | { lexical_form; datatype; lang_tag; direction;_} -> lexical_form
let __proj__Mkliteral__item__datatype (projectee : literal) : wf_iri=
  match projectee with
  | { lexical_form; datatype; lang_tag; direction;_} -> datatype
let __proj__Mkliteral__item__lang_tag (projectee : literal) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | { lexical_form; datatype; lang_tag; direction;_} -> lang_tag
let __proj__Mkliteral__item__direction (projectee : literal) :
  text_direction FStar_Pervasives_Native.option=
  match projectee with
  | { lexical_form; datatype; lang_tag; direction;_} -> direction
let literal_wf (l : literal) : Prims.bool=
  match ((l.lang_tag), (l.direction)) with
  | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) ->
      (l.datatype <> rdf_lang_string) && (l.datatype <> rdf_dir_lang_string)
  | (FStar_Pervasives_Native.Some uu___, FStar_Pervasives_Native.None) ->
      l.datatype = rdf_lang_string
  | (FStar_Pervasives_Native.Some uu___, FStar_Pervasives_Native.Some uu___1)
      -> l.datatype = rdf_dir_lang_string
  | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.Some uu___) ->
      false
type wf_literal = literal
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
type rdf_term =
  | T_IRI of wf_iri 
  | T_BNode of bnode_id 
  | T_Literal of wf_literal 
  | T_TripleTerm of subject * wf_iri * rdf_term 
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
let uu___is_T_TripleTerm (projectee : rdf_term) : Prims.bool=
  match projectee with | T_TripleTerm (_0, _1, _2) -> true | uu___ -> false
let __proj__T_TripleTerm__item___0 (projectee : rdf_term) : subject=
  match projectee with | T_TripleTerm (_0, _1, _2) -> _0
let __proj__T_TripleTerm__item___1 (projectee : rdf_term) : wf_iri=
  match projectee with | T_TripleTerm (_0, _1, _2) -> _1
let __proj__T_TripleTerm__item___2 (projectee : rdf_term) : rdf_term=
  match projectee with | T_TripleTerm (_0, _1, _2) -> _2
let xsd_string : wf_iri= "http://www.w3.org/2001/XMLSchema#string"
let xsd_integer : wf_iri= "http://www.w3.org/2001/XMLSchema#integer"
let xsd_decimal : wf_iri= "http://www.w3.org/2001/XMLSchema#decimal"
let xsd_double : wf_iri= "http://www.w3.org/2001/XMLSchema#double"
let xsd_boolean : wf_iri= "http://www.w3.org/2001/XMLSchema#boolean"
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
let rdf_XMLLiteral : wf_iri=
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#XMLLiteral"
let xmlc_is_ws (c : FStar_Char.char) : Prims.bool=
  let n = FStar_Char.int_of_char c in
  (((n = (Prims.of_int (0x20))) || (n = (Prims.of_int (0x09)))) ||
     (n = (Prims.of_int (0x0A))))
    || (n = (Prims.of_int (0x0D)))
let rec xmlc_chars_lt (a : FStar_Char.char Prims.list)
  (b : FStar_Char.char Prims.list) : Prims.bool=
  match (a, b) with
  | ([], []) -> false
  | ([], uu___::uu___1) -> true
  | (uu___::uu___1, []) -> false
  | (x::xs, y::ys) ->
      let nx = FStar_Char.int_of_char x in
      let ny = FStar_Char.int_of_char y in
      if nx < ny
      then true
      else if nx > ny then false else xmlc_chars_lt xs ys
let rec xmlc_take_name (cs : FStar_Char.char Prims.list)
  (acc : FStar_Char.char Prims.list) :
  (FStar_Char.char Prims.list * FStar_Char.char Prims.list)=
  match cs with
  | [] -> ((FStar_List_Tot_Base.rev acc), [])
  | c::rest ->
      if ((xmlc_is_ws c) || (c = 47)) || (c = 61)
      then ((FStar_List_Tot_Base.rev acc), cs)
      else xmlc_take_name rest (c :: acc)
let rec xmlc_drop_ws (cs : FStar_Char.char Prims.list) :
  FStar_Char.char Prims.list=
  match cs with
  | c::rest -> if xmlc_is_ws c then xmlc_drop_ws rest else cs
  | [] -> []
let xmlc_drop_to_value (cs : FStar_Char.char Prims.list) :
  FStar_Char.char Prims.list=
  let cs1 = xmlc_drop_ws cs in
  match cs1 with
  | c::rest -> if c = 61 then xmlc_drop_ws rest else cs1
  | [] -> cs1
let rec xmlc_take_until (q : FStar_Char.char)
  (cs : FStar_Char.char Prims.list) (acc : FStar_Char.char Prims.list) :
  (FStar_Char.char Prims.list * FStar_Char.char Prims.list)=
  match cs with
  | [] -> ((FStar_List_Tot_Base.rev acc), [])
  | c::rest ->
      if c = q
      then ((FStar_List_Tot_Base.rev acc), rest)
      else xmlc_take_until q rest (c :: acc)
let xmlc_take_quoted (cs : FStar_Char.char Prims.list) :
  (FStar_Char.char Prims.list * FStar_Char.char Prims.list)=
  match cs with
  | c::rest ->
      if (c = 34) || (c = 39) then xmlc_take_until c rest [] else ([], cs)
  | [] -> ([], [])
let rec xmlc_parse_attrs (fuel : Prims.nat) (cs : FStar_Char.char Prims.list)
  (acc :
    (FStar_Char.char Prims.list * FStar_Char.char Prims.list) Prims.list)
  :
  ((FStar_Char.char Prims.list * FStar_Char.char Prims.list) Prims.list *
    Prims.bool)=
  if fuel = Prims.int_zero
  then ((FStar_List_Tot_Base.rev acc), false)
  else
    (match cs with
     | [] -> ((FStar_List_Tot_Base.rev acc), false)
     | c::rest ->
         if xmlc_is_ws c
         then xmlc_parse_attrs (fuel - Prims.int_one) rest acc
         else
           if c = 47
           then ((FStar_List_Tot_Base.rev acc), true)
           else
             (let uu___3 = xmlc_take_name cs [] in
              match uu___3 with
              | (nm, r1) ->
                  let r2 = xmlc_drop_to_value r1 in
                  let uu___4 = xmlc_take_quoted r2 in
                  (match uu___4 with
                   | (v, r3) ->
                       xmlc_parse_attrs (fuel - Prims.int_one) r3 ((nm, v) ::
                         acc))))
let rec xmlc_insert_attr
  (p : (FStar_Char.char Prims.list * FStar_Char.char Prims.list))
  (xs : (FStar_Char.char Prims.list * FStar_Char.char Prims.list) Prims.list)
  : (FStar_Char.char Prims.list * FStar_Char.char Prims.list) Prims.list=
  match xs with
  | [] -> [p]
  | q::rest ->
      if
        xmlc_chars_lt (FStar_Pervasives_Native.fst p)
          (FStar_Pervasives_Native.fst q)
      then p :: xs
      else q :: (xmlc_insert_attr p rest)
let rec xmlc_sort_attrs
  (xs : (FStar_Char.char Prims.list * FStar_Char.char Prims.list) Prims.list)
  : (FStar_Char.char Prims.list * FStar_Char.char Prims.list) Prims.list=
  match xs with
  | [] -> []
  | x::rest -> xmlc_insert_attr x (xmlc_sort_attrs rest)
let rec xmlc_render_attrs
  (xs : (FStar_Char.char Prims.list * FStar_Char.char Prims.list) Prims.list)
  : FStar_Char.char Prims.list=
  match xs with
  | [] -> []
  | (nm, v)::rest ->
      FStar_List_Tot_Base.append [32]
        (FStar_List_Tot_Base.append nm
           (FStar_List_Tot_Base.append [61; 34]
              (FStar_List_Tot_Base.append v
                 (FStar_List_Tot_Base.append [34] (xmlc_render_attrs rest)))))
let xmlc_canon_tag (body : FStar_Char.char Prims.list) :
  FStar_Char.char Prims.list=
  match body with
  | [] -> [60; 62]
  | 47::uu___ ->
      FStar_List_Tot_Base.append [60] (FStar_List_Tot_Base.append body [62])
  | 33::uu___ ->
      FStar_List_Tot_Base.append [60] (FStar_List_Tot_Base.append body [62])
  | 63::uu___ ->
      FStar_List_Tot_Base.append [60] (FStar_List_Tot_Base.append body [62])
  | uu___ ->
      let uu___1 = xmlc_take_name body [] in
      (match uu___1 with
       | (nm, r1) ->
           let uu___2 =
             xmlc_parse_attrs
               ((FStar_List_Tot_Base.length r1) + Prims.int_one) r1 [] in
           (match uu___2 with
            | (attrs, self_close) ->
                let sorted = xmlc_sort_attrs attrs in
                let open_tag =
                  FStar_List_Tot_Base.append [60]
                    (FStar_List_Tot_Base.append nm
                       (FStar_List_Tot_Base.append (xmlc_render_attrs sorted)
                          [62])) in
                if self_close
                then
                  FStar_List_Tot_Base.append open_tag
                    (FStar_List_Tot_Base.append [60; 47]
                       (FStar_List_Tot_Base.append nm [62]))
                else open_tag))
let rec xmlc_split_tag (cs : FStar_Char.char Prims.list)
  (acc : FStar_Char.char Prims.list) :
  (FStar_Char.char Prims.list * FStar_Char.char Prims.list)=
  match cs with
  | [] -> ((FStar_List_Tot_Base.rev acc), [])
  | c::rest ->
      if c = 62
      then ((FStar_List_Tot_Base.rev acc), rest)
      else xmlc_split_tag rest (c :: acc)
let rec xmlc_walk (fuel : Prims.nat) (cs : FStar_Char.char Prims.list) :
  FStar_Char.char Prims.list=
  if fuel = Prims.int_zero
  then []
  else
    (match cs with
     | [] -> []
     | c::rest ->
         if c = 60
         then
           let uu___1 = xmlc_split_tag rest [] in
           (match uu___1 with
            | (body, remainder) ->
                FStar_List_Tot_Base.append (xmlc_canon_tag body)
                  (xmlc_walk (fuel - Prims.int_one) remainder))
         else c :: (xmlc_walk (fuel - Prims.int_one) rest))
let xmlc_canonicalize (s : Prims.string) : FStar_Char.char Prims.list=
  let cs = FStar_String.list_of_string s in
  xmlc_walk ((FStar_List_Tot_Base.length cs) + Prims.int_one) cs
let xml_canon_eq (s1 : Prims.string) (s2 : Prims.string) : Prims.bool=
  (xmlc_canonicalize s1) = (xmlc_canonicalize s2)
let literal_eq (l1 : literal) (l2 : literal) : Prims.bool=
  (((if (l1.datatype = rdf_XMLLiteral) && (l2.datatype = rdf_XMLLiteral)
     then xml_canon_eq l1.lexical_form l2.lexical_form
     else l1.lexical_form = l2.lexical_form) && (l1.datatype = l2.datatype))
     && (lang_tag_option_eq l1.lang_tag l2.lang_tag))
    && (l1.direction = l2.direction)
let join_canon_literal (l : literal) : literal=
  {
    lexical_form =
      (if l.datatype = rdf_XMLLiteral
       then FStar_String.string_of_list (xmlc_canonicalize l.lexical_form)
       else l.lexical_form);
    datatype = (l.datatype);
    lang_tag =
      (match l.lang_tag with
       | FStar_Pervasives_Native.Some t ->
           FStar_Pervasives_Native.Some (FStar_String.lowercase t)
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None);
    direction = (l.direction)
  }
let rec join_canon_term (t : rdf_term) : rdf_term=
  match t with
  | T_IRI uu___ -> t
  | T_BNode uu___ -> t
  | T_Literal l -> T_Literal (join_canon_literal l)
  | T_TripleTerm (s, p, o) -> T_TripleTerm (s, p, (join_canon_term o))
let rec rdf_term_eq (t1 : rdf_term) (t2 : rdf_term) : Prims.bool=
  match (t1, t2) with
  | (T_IRI i1, T_IRI i2) -> i1 = i2
  | (T_BNode b1, T_BNode b2) -> b1 = b2
  | (T_Literal l1, T_Literal l2) -> literal_eq l1 l2
  | (T_TripleTerm (s1, p1, o1), T_TripleTerm (s2, p2, o2)) ->
      ((subject_eq s1 s2) && (p1 = p2)) && (rdf_term_eq o1 o2)
  | (uu___, uu___1) -> false
let literal_value_eq (l1 : literal) (l2 : literal) : Prims.bool=
  (((l1.lexical_form = l2.lexical_form) &&
      (lang_tag_option_eq l1.lang_tag l2.lang_tag))
     && (l1.datatype = l2.datatype))
    && (l1.direction = l2.direction)
