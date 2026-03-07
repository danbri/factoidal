open Prims
type bnode_id = Prims.string
type iri = Prims.string
let rec list_has_colon (cs : FStar_Char.char Prims.list) : Prims.bool=
  match cs with
  | [] -> false
  | c::rest ->
      ((FStar_Char.int_of_char c) = (Prims.of_int (0x3A))) ||
        (list_has_colon rest)
let string_contains_colon (s : Prims.string) : Prims.bool=
  list_has_colon (FStar_String.list_of_string s)
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
let literal_eq (l1 : literal) (l2 : literal) : Prims.bool=
  ((l1.lexical_form = l2.lexical_form) && (l1.datatype = l2.datatype)) &&
    (l1.lang_tag = l2.lang_tag)
let rdf_term_eq (t1 : rdf_term) (t2 : rdf_term) : Prims.bool=
  match (t1, t2) with
  | (T_IRI i1, T_IRI i2) -> i1 = i2
  | (T_BNode b1, T_BNode b2) -> b1 = b2
  | (T_Literal l1, T_Literal l2) -> literal_eq l1 l2
  | (uu___, uu___1) -> false
type triple = {
  s: subject ;
  p: wf_iri ;
  o: rdf_term }
let __proj__Mktriple__item__s (projectee : triple) : subject=
  match projectee with | { s; p; o;_} -> s
let __proj__Mktriple__item__p (projectee : triple) : wf_iri=
  match projectee with | { s; p; o;_} -> p
let __proj__Mktriple__item__o (projectee : triple) : rdf_term=
  match projectee with | { s; p; o;_} -> o
let triple_eq (a : triple) (b : triple) : Prims.bool=
  ((subject_eq a.s b.s) && (a.p = b.p)) && (rdf_term_eq a.o b.o)
type rdf_graph = triple Prims.list
let empty_graph : rdf_graph= []
let rec graph_bnodes (g : rdf_graph) : bnode_id Prims.list=
  match g with
  | [] -> []
  | hd::tl ->
      let nodes = match hd.s with | S_BNode id -> [id] | uu___ -> [] in
      let obj_nodes = match hd.o with | T_BNode id -> [id] | uu___ -> [] in
      FStar_List_Tot_Base.op_At nodes
        (FStar_List_Tot_Base.op_At obj_nodes (graph_bnodes tl))
let rec mem_triple (t : triple) (g : rdf_graph) : Prims.bool=
  match g with
  | [] -> false
  | hd::tl -> (triple_eq hd t) || (mem_triple t tl)
let graph_add (t : triple) (g : rdf_graph) : rdf_graph=
  if mem_triple t g then g else FStar_List_Tot_Base.op_At g [t]
let graph_remove (t : triple) (g : rdf_graph) : rdf_graph=
  FStar_List_Tot_Base.filter (fun hd -> Prims.op_Negation (triple_eq hd t)) g
let graph_len (g : rdf_graph) : Prims.nat= FStar_List_Tot_Base.length g
let rec graph_union (g1 : rdf_graph) (g2 : rdf_graph) : rdf_graph=
  match g1 with | [] -> g2 | hd::tl -> graph_union tl (graph_add hd g2)
let rec find_by_subject (subj : wf_iri) (g : rdf_graph) : rdf_graph=
  match g with
  | [] -> []
  | hd::tl ->
      let rest = find_by_subject subj tl in
      (match hd.s with
       | S_IRI i -> if i = subj then hd :: rest else rest
       | uu___ -> rest)
let rec find_by_predicate (pred : wf_iri) (g : rdf_graph) : rdf_graph=
  match g with
  | [] -> []
  | hd::tl ->
      let rest = find_by_predicate pred tl in
      if hd.p = pred then hd :: rest else rest
let must_escape (c : FStar_Char.char) : Prims.bool=
  let code = FStar_Char.int_of_char c in
  (((((((code = (Prims.of_int (0x5C))) || (code = (Prims.of_int (0x22)))) ||
         (code = (Prims.of_int (0x0A))))
        || (code = (Prims.of_int (0x0D))))
       || (code = (Prims.of_int (0x09))))
      || (code = (Prims.of_int (0x08))))
     || (code = (Prims.of_int (0x0C))))
    || (code < (Prims.of_int (0x20)))
let rec is_nt_escaped_list (cs : FStar_Char.char Prims.list) : Prims.bool=
  match cs with
  | [] -> true
  | c::rest ->
      let code = FStar_Char.int_of_char c in
      if
        ((code < (Prims.of_int (0x20))) || (code = (Prims.of_int (0x22)))) ||
          (code = (Prims.of_int (0x5C)))
      then false
      else is_nt_escaped_list rest
let is_nt_escaped (s : Prims.string) (n : Prims.nat) : Prims.bool=
  let cs = FStar_String.list_of_string s in
  let rec drop_n l k =
    match l with
    | [] -> []
    | uu___::tl ->
        if k = Prims.int_zero then l else drop_n tl (k - Prims.int_one) in
  is_nt_escaped_list (drop_n cs n)
type var_name = Prims.string
type pattern_term =
  | PT_Concrete of rdf_term 
  | PT_Var of var_name 
let uu___is_PT_Concrete (projectee : pattern_term) : Prims.bool=
  match projectee with | PT_Concrete _0 -> true | uu___ -> false
let __proj__PT_Concrete__item___0 (projectee : pattern_term) : rdf_term=
  match projectee with | PT_Concrete _0 -> _0
let uu___is_PT_Var (projectee : pattern_term) : Prims.bool=
  match projectee with | PT_Var _0 -> true | uu___ -> false
let __proj__PT_Var__item___0 (projectee : pattern_term) : var_name=
  match projectee with | PT_Var _0 -> _0
type pattern_subject =
  | PS_Concrete of subject 
  | PS_Var of var_name 
let uu___is_PS_Concrete (projectee : pattern_subject) : Prims.bool=
  match projectee with | PS_Concrete _0 -> true | uu___ -> false
let __proj__PS_Concrete__item___0 (projectee : pattern_subject) : subject=
  match projectee with | PS_Concrete _0 -> _0
let uu___is_PS_Var (projectee : pattern_subject) : Prims.bool=
  match projectee with | PS_Var _0 -> true | uu___ -> false
let __proj__PS_Var__item___0 (projectee : pattern_subject) : var_name=
  match projectee with | PS_Var _0 -> _0
type triple_pattern =
  {
  tp_s: pattern_subject ;
  tp_p: wf_iri ;
  tp_o: pattern_term }
let __proj__Mktriple_pattern__item__tp_s (projectee : triple_pattern) :
  pattern_subject= match projectee with | { tp_s; tp_p; tp_o;_} -> tp_s
let __proj__Mktriple_pattern__item__tp_p (projectee : triple_pattern) :
  wf_iri= match projectee with | { tp_s; tp_p; tp_o;_} -> tp_p
let __proj__Mktriple_pattern__item__tp_o (projectee : triple_pattern) :
  pattern_term= match projectee with | { tp_s; tp_p; tp_o;_} -> tp_o
type solution_mapping = (var_name * rdf_term) Prims.list
type bgp = triple_pattern Prims.list
let pattern_subject_matches (ps : pattern_subject) (s : subject)
  (mu : solution_mapping) : Prims.bool=
  match ps with
  | PS_Concrete cs -> subject_eq cs s
  | PS_Var v ->
      (match FStar_List_Tot_Base.assoc v mu with
       | FStar_Pervasives_Native.Some (T_IRI i) -> subject_eq s (S_IRI i)
       | FStar_Pervasives_Native.Some (T_BNode b) -> subject_eq s (S_BNode b)
       | uu___ -> true)
let pattern_term_matches (pt : pattern_term) (t : rdf_term)
  (mu : solution_mapping) : Prims.bool=
  match pt with
  | PT_Concrete ct -> rdf_term_eq ct t
  | PT_Var v ->
      (match FStar_List_Tot_Base.assoc v mu with
       | FStar_Pervasives_Native.Some bound -> rdf_term_eq bound t
       | FStar_Pervasives_Native.None -> true)
let triple_pattern_matches (tp : triple_pattern) (t : triple)
  (mu : solution_mapping) : Prims.bool=
  ((pattern_subject_matches tp.tp_s t.s mu) && (tp.tp_p = t.p)) &&
    (pattern_term_matches tp.tp_o t.o mu)
type algebra_op =
  | BGP_Op of bgp 
  | Filter_Op of algebra_op 
  | Optional_Op of algebra_op * algebra_op 
  | Union_Op of algebra_op * algebra_op 
let uu___is_BGP_Op (projectee : algebra_op) : Prims.bool=
  match projectee with | BGP_Op _0 -> true | uu___ -> false
let __proj__BGP_Op__item___0 (projectee : algebra_op) : bgp=
  match projectee with | BGP_Op _0 -> _0
let uu___is_Filter_Op (projectee : algebra_op) : Prims.bool=
  match projectee with | Filter_Op _0 -> true | uu___ -> false
let __proj__Filter_Op__item___0 (projectee : algebra_op) : algebra_op=
  match projectee with | Filter_Op _0 -> _0
let uu___is_Optional_Op (projectee : algebra_op) : Prims.bool=
  match projectee with | Optional_Op (_0, _1) -> true | uu___ -> false
let __proj__Optional_Op__item___0 (projectee : algebra_op) : algebra_op=
  match projectee with | Optional_Op (_0, _1) -> _0
let __proj__Optional_Op__item___1 (projectee : algebra_op) : algebra_op=
  match projectee with | Optional_Op (_0, _1) -> _1
let uu___is_Union_Op (projectee : algebra_op) : Prims.bool=
  match projectee with | Union_Op (_0, _1) -> true | uu___ -> false
let __proj__Union_Op__item___0 (projectee : algebra_op) : algebra_op=
  match projectee with | Union_Op (_0, _1) -> _0
let __proj__Union_Op__item___1 (projectee : algebra_op) : algebra_op=
  match projectee with | Union_Op (_0, _1) -> _1
type solution_multiset = solution_mapping Prims.list
type numeric_type =
  | NT_Integer 
  | NT_Decimal 
  | NT_Double 
  | NT_Float 
let uu___is_NT_Integer (projectee : numeric_type) : Prims.bool=
  match projectee with | NT_Integer -> true | uu___ -> false
let uu___is_NT_Decimal (projectee : numeric_type) : Prims.bool=
  match projectee with | NT_Decimal -> true | uu___ -> false
let uu___is_NT_Double (projectee : numeric_type) : Prims.bool=
  match projectee with | NT_Double -> true | uu___ -> false
let uu___is_NT_Float (projectee : numeric_type) : Prims.bool=
  match projectee with | NT_Float -> true | uu___ -> false
type comp_op =
  | Eq 
  | Ne 
  | Lt 
  | Gt 
  | Le 
  | Ge 
let uu___is_Eq (projectee : comp_op) : Prims.bool=
  match projectee with | Eq -> true | uu___ -> false
let uu___is_Ne (projectee : comp_op) : Prims.bool=
  match projectee with | Ne -> true | uu___ -> false
let uu___is_Lt (projectee : comp_op) : Prims.bool=
  match projectee with | Lt -> true | uu___ -> false
let uu___is_Gt (projectee : comp_op) : Prims.bool=
  match projectee with | Gt -> true | uu___ -> false
let uu___is_Le (projectee : comp_op) : Prims.bool=
  match projectee with | Le -> true | uu___ -> false
let uu___is_Ge (projectee : comp_op) : Prims.bool=
  match projectee with | Ge -> true | uu___ -> false
type sparql_value =
  | SV_Numeric of Prims.int * numeric_type 
  | SV_PlainLiteral of Prims.string 
  | SV_LangLiteral of Prims.string * Prims.string 
  | SV_Iri of Prims.string 
  | SV_BNode of bnode_id 
  | SV_TypedLiteral of Prims.string * wf_iri 
  | SV_Boolean of Prims.bool 
let uu___is_SV_Numeric (projectee : sparql_value) : Prims.bool=
  match projectee with | SV_Numeric (value, ntype) -> true | uu___ -> false
let __proj__SV_Numeric__item__value (projectee : sparql_value) : Prims.int=
  match projectee with | SV_Numeric (value, ntype) -> value
let __proj__SV_Numeric__item__ntype (projectee : sparql_value) :
  numeric_type= match projectee with | SV_Numeric (value, ntype) -> ntype
let uu___is_SV_PlainLiteral (projectee : sparql_value) : Prims.bool=
  match projectee with | SV_PlainLiteral lexical -> true | uu___ -> false
let __proj__SV_PlainLiteral__item__lexical (projectee : sparql_value) :
  Prims.string= match projectee with | SV_PlainLiteral lexical -> lexical
let uu___is_SV_LangLiteral (projectee : sparql_value) : Prims.bool=
  match projectee with
  | SV_LangLiteral (lexical, lang) -> true
  | uu___ -> false
let __proj__SV_LangLiteral__item__lexical (projectee : sparql_value) :
  Prims.string=
  match projectee with | SV_LangLiteral (lexical, lang) -> lexical
let __proj__SV_LangLiteral__item__lang (projectee : sparql_value) :
  Prims.string= match projectee with | SV_LangLiteral (lexical, lang) -> lang
let uu___is_SV_Iri (projectee : sparql_value) : Prims.bool=
  match projectee with | SV_Iri iri_str -> true | uu___ -> false
let __proj__SV_Iri__item__iri_str (projectee : sparql_value) : Prims.string=
  match projectee with | SV_Iri iri_str -> iri_str
let uu___is_SV_BNode (projectee : sparql_value) : Prims.bool=
  match projectee with | SV_BNode id -> true | uu___ -> false
let __proj__SV_BNode__item__id (projectee : sparql_value) : bnode_id=
  match projectee with | SV_BNode id -> id
let uu___is_SV_TypedLiteral (projectee : sparql_value) : Prims.bool=
  match projectee with
  | SV_TypedLiteral (lexical, datatype) -> true
  | uu___ -> false
let __proj__SV_TypedLiteral__item__lexical (projectee : sparql_value) :
  Prims.string=
  match projectee with | SV_TypedLiteral (lexical, datatype) -> lexical
let __proj__SV_TypedLiteral__item__datatype (projectee : sparql_value) :
  wf_iri=
  match projectee with | SV_TypedLiteral (lexical, datatype) -> datatype
let uu___is_SV_Boolean (projectee : sparql_value) : Prims.bool=
  match projectee with | SV_Boolean b -> true | uu___ -> false
let __proj__SV_Boolean__item__b (projectee : sparql_value) : Prims.bool=
  match projectee with | SV_Boolean b -> b
let string_lt (s1 : Prims.string) (s2 : Prims.string) : Prims.bool=
  (FStar_String.compare s1 s2) < Prims.int_zero
let value_compare (lv : sparql_value) (rv : sparql_value) (op : comp_op) :
  Prims.bool FStar_Pervasives_Native.option=
  match (lv, rv) with
  | (SV_Numeric (ln, uu___), SV_Numeric (rn, uu___1)) ->
      FStar_Pervasives_Native.Some
        ((match op with
          | Eq -> ln = rn
          | Ne -> ln <> rn
          | Lt -> ln < rn
          | Gt -> ln > rn
          | Le -> ln <= rn
          | Ge -> ln >= rn))
  | (SV_Boolean l, SV_Boolean r) ->
      (match op with
       | Eq -> FStar_Pervasives_Native.Some (l = r)
       | Ne -> FStar_Pervasives_Native.Some (l <> r)
       | uu___ -> FStar_Pervasives_Native.None)
  | (SV_PlainLiteral l, SV_PlainLiteral r) ->
      FStar_Pervasives_Native.Some
        ((match op with
          | Eq -> l = r
          | Ne -> l <> r
          | Lt -> string_lt l r
          | Gt -> string_lt r l
          | Le -> (l = r) || (string_lt l r)
          | Ge -> (l = r) || (string_lt r l)))
  | (SV_LangLiteral (llex, llang), SV_LangLiteral (rlex, rlang)) ->
      (match op with
       | Eq ->
           FStar_Pervasives_Native.Some ((llex = rlex) && (llang = rlang))
       | Ne ->
           FStar_Pervasives_Native.Some ((llex <> rlex) || (llang <> rlang))
       | uu___ -> FStar_Pervasives_Native.None)
  | (SV_Iri l, SV_Iri r) ->
      FStar_Pervasives_Native.Some
        ((match op with
          | Eq -> l = r
          | Ne -> l <> r
          | Lt -> string_lt l r
          | Gt -> string_lt r l
          | Le -> (l = r) || (string_lt l r)
          | Ge -> (l = r) || (string_lt r l)))
  | (SV_BNode l, SV_BNode r) ->
      (match op with
       | Eq -> FStar_Pervasives_Native.Some (l = r)
       | Ne -> FStar_Pervasives_Native.Some (l <> r)
       | uu___ -> FStar_Pervasives_Native.None)
  | (SV_TypedLiteral (llex, ldt), SV_TypedLiteral (rlex, rdt)) ->
      if ldt = rdt
      then
        FStar_Pervasives_Native.Some
          ((match op with
            | Eq -> llex = rlex
            | Ne -> llex <> rlex
            | Lt -> string_lt llex rlex
            | Gt -> string_lt rlex llex
            | Le -> (llex = rlex) || (string_lt llex rlex)
            | Ge -> (llex = rlex) || (string_lt rlex llex)))
      else FStar_Pervasives_Native.None
  | (uu___, uu___1) -> FStar_Pervasives_Native.None
let boolean_effective_value (v : sparql_value) : Prims.bool=
  match v with
  | SV_Boolean b -> b
  | SV_Numeric (n, uu___) -> n <> Prims.int_zero
  | SV_PlainLiteral s -> (FStar_String.strlen s) > Prims.int_zero
  | SV_LangLiteral (s, uu___) -> (FStar_String.strlen s) > Prims.int_zero
  | SV_Iri uu___ -> false
  | SV_BNode uu___ -> false
  | SV_TypedLiteral (uu___, uu___1) -> false
let bev_of_option (v : sparql_value FStar_Pervasives_Native.option) :
  Prims.bool=
  match v with
  | FStar_Pervasives_Native.None -> false
  | FStar_Pervasives_Native.Some x -> boolean_effective_value x
type filter_expr_eval =
  solution_mapping -> rdf_term FStar_Pervasives_Native.option
let bind_eval (eval : filter_expr_eval) (var : var_name)
  (mu : solution_mapping) :
  (var_name * rdf_term) FStar_Pervasives_Native.option=
  match FStar_List_Tot_Base.assoc var mu with
  | FStar_Pervasives_Native.Some uu___ -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.None ->
      (match eval mu with
       | FStar_Pervasives_Native.Some term ->
           FStar_Pervasives_Native.Some (var, term)
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
let apply_bind (eval : filter_expr_eval) (var : var_name)
  (mu : solution_mapping) : solution_mapping=
  match bind_eval eval var mu with
  | FStar_Pervasives_Native.Some pair -> pair :: mu
  | FStar_Pervasives_Native.None -> mu
let sparql_strlen (s : Prims.string) : Prims.nat= FStar_String.strlen s
let string_substring (s : Prims.string) (i : Prims.nat) (len : Prims.nat) :
  Prims.string=
  let slen = FStar_String.strlen s in
  if i >= slen
  then ""
  else
    (let max_len = slen - i in
     let actual_len = if len <= max_len then len else max_len in
     FStar_String.sub s i actual_len)
let sparql_substr (s : Prims.string) (start : Prims.nat)
  (len : Prims.nat FStar_Pervasives_Native.option) : Prims.string=
  let start_idx =
    if start > Prims.int_zero then start - Prims.int_one else Prims.int_zero in
  let remaining =
    if (FStar_String.strlen s) > start_idx
    then (FStar_String.strlen s) - start_idx
    else Prims.int_zero in
  match len with
  | FStar_Pervasives_Native.Some n -> string_substring s start_idx n
  | FStar_Pervasives_Native.None -> string_substring s start_idx remaining
let string_to_upper (s : Prims.string) : Prims.string=
  FStar_String.uppercase s
let sparql_ucase (s : Prims.string) : Prims.string= string_to_upper s
let string_to_lower (s : Prims.string) : Prims.string=
  FStar_String.lowercase s
let sparql_lcase (s : Prims.string) : Prims.string= string_to_lower s
let rec sparql_concat (args : Prims.string Prims.list) : Prims.string=
  match args with
  | [] -> ""
  | hd::tl -> FStar_String.concat "" [hd; sparql_concat tl]
type chars = FStar_Char.char Prims.list
let char_code (c : FStar_Char.char) : Prims.int= FStar_Char.int_of_char c
let is_valid_codepoint (n : Prims.int) : Prims.bool=
  ((n >= Prims.int_zero) && (n < (Prims.of_int (0xd7ff)))) ||
    ((n >= (Prims.of_int (0xe000))) && (n <= (Prims.parse_int "0x10ffff")))
let mk_char_safe (n : Prims.nat) : FStar_Char.char= FStar_Char.char_of_int n
let mk_char (n : Prims.int) : FStar_Char.char=
  if (n >= Prims.int_zero) && (n < (Prims.of_int (0xd7ff)))
  then mk_char_safe n
  else
    if (n >= (Prims.of_int (0xe000))) && (n <= (Prims.parse_int "0x10ffff"))
    then mk_char_safe n
    else mk_char_safe (Prims.of_int (0xFFFD))
type 'a parse_result = ('a * chars) FStar_Pervasives_Native.option
let rec skip_ws (cs : chars) : chars=
  match cs with
  | [] -> []
  | c::rest ->
      let code = char_code c in
      if (code = (Prims.of_int (0x20))) || (code = (Prims.of_int (0x09)))
      then skip_ws rest
      else cs
let rec skip_to_eol (cs : chars) : chars=
  match cs with
  | [] -> []
  | c::rest ->
      let code = char_code c in
      if (code = (Prims.of_int (0x0A))) || (code = (Prims.of_int (0x0D)))
      then cs
      else skip_to_eol rest
let skip_eol (cs : chars) : chars=
  match cs with
  | [] -> []
  | c1::rest ->
      if (char_code c1) = (Prims.of_int (0x0D))
      then
        (match rest with
         | c2::rest2 ->
             if (char_code c2) = (Prims.of_int (0x0A)) then rest2 else rest
         | [] -> [])
      else if (char_code c1) = (Prims.of_int (0x0A)) then rest else cs
let parse_escape (cs : chars) : FStar_Char.char parse_result=
  match cs with
  | [] -> FStar_Pervasives_Native.None
  | c::rest ->
      let code = char_code c in
      if code = (Prims.of_int (0x74))
      then
        FStar_Pervasives_Native.Some ((mk_char (Prims.of_int (0x09))), rest)
      else
        if code = (Prims.of_int (0x6E))
        then
          FStar_Pervasives_Native.Some
            ((mk_char (Prims.of_int (0x0A))), rest)
        else
          if code = (Prims.of_int (0x72))
          then
            FStar_Pervasives_Native.Some
              ((mk_char (Prims.of_int (0x0D))), rest)
          else
            if code = (Prims.of_int (0x62))
            then
              FStar_Pervasives_Native.Some
                ((mk_char (Prims.of_int (0x08))), rest)
            else
              if code = (Prims.of_int (0x66))
              then
                FStar_Pervasives_Native.Some
                  ((mk_char (Prims.of_int (0x0C))), rest)
              else
                if code = (Prims.of_int (0x22))
                then
                  FStar_Pervasives_Native.Some
                    ((mk_char (Prims.of_int (0x22))), rest)
                else
                  if code = (Prims.of_int (0x27))
                  then
                    FStar_Pervasives_Native.Some
                      ((mk_char (Prims.of_int (0x27))), rest)
                  else
                    if code = (Prims.of_int (0x5C))
                    then
                      FStar_Pervasives_Native.Some
                        ((mk_char (Prims.of_int (0x5C))), rest)
                    else FStar_Pervasives_Native.None
let hex_digit_val (c : FStar_Char.char) :
  Prims.int FStar_Pervasives_Native.option=
  let code = char_code c in
  if (code >= (Prims.of_int (0x30))) && (code <= (Prims.of_int (0x39)))
  then FStar_Pervasives_Native.Some (code - (Prims.of_int (0x30)))
  else
    if (code >= (Prims.of_int (0x41))) && (code <= (Prims.of_int (0x46)))
    then
      FStar_Pervasives_Native.Some
        ((code - (Prims.of_int (0x41))) + (Prims.of_int (10)))
    else
      if (code >= (Prims.of_int (0x61))) && (code <= (Prims.of_int (0x66)))
      then
        FStar_Pervasives_Native.Some
          ((code - (Prims.of_int (0x61))) + (Prims.of_int (10)))
      else FStar_Pervasives_Native.None
let rec parse_hex_chars (cs : chars) (n : Prims.nat) (acc : Prims.nat) :
  (Prims.nat * chars) FStar_Pervasives_Native.option=
  if n = Prims.int_zero
  then FStar_Pervasives_Native.Some (acc, cs)
  else
    (match cs with
     | [] -> FStar_Pervasives_Native.None
     | c::rest ->
         (match hex_digit_val c with
          | FStar_Pervasives_Native.Some v ->
              let acc' = (acc * (Prims.of_int (16))) + v in
              parse_hex_chars rest (n - Prims.int_one) acc'
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None))
let parse_unicode_escape (cs : chars) : FStar_Char.char parse_result=
  match cs with
  | [] -> FStar_Pervasives_Native.None
  | c::rest ->
      let code = char_code c in
      if code = (Prims.of_int (0x75))
      then
        (match parse_hex_chars rest (Prims.of_int (4)) Prims.int_zero with
         | FStar_Pervasives_Native.Some (cp, rest2) ->
             FStar_Pervasives_Native.Some ((mk_char cp), rest2)
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
      else
        if code = (Prims.of_int (0x55))
        then
          (match parse_hex_chars rest (Prims.of_int (8)) Prims.int_zero with
           | FStar_Pervasives_Native.Some (cp, rest2) ->
               FStar_Pervasives_Native.Some ((mk_char cp), rest2)
           | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
        else FStar_Pervasives_Native.None
let rec parse_string_chars (cs : chars) (acc : chars) (fuel : Prims.nat) :
  Prims.string parse_result=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (match cs with
     | [] -> FStar_Pervasives_Native.None
     | c::rest ->
         let code = char_code c in
         if code = (Prims.of_int (0x22))
         then
           FStar_Pervasives_Native.Some
             ((FStar_String.string_of_list (FStar_List_Tot_Base.rev acc)),
               rest)
         else
           if code = (Prims.of_int (0x5C))
           then
             (match rest with
              | [] -> FStar_Pervasives_Native.None
              | c2::uu___2 ->
                  let c2code = char_code c2 in
                  if
                    (c2code = (Prims.of_int (0x75))) ||
                      (c2code = (Prims.of_int (0x55)))
                  then
                    (match parse_unicode_escape rest with
                     | FStar_Pervasives_Native.Some (ch, rest2) ->
                         parse_string_chars rest2 (ch :: acc)
                           (fuel - Prims.int_one)
                     | FStar_Pervasives_Native.None ->
                         FStar_Pervasives_Native.None)
                  else
                    (match parse_escape rest with
                     | FStar_Pervasives_Native.Some (ch, rest2) ->
                         parse_string_chars rest2 (ch :: acc)
                           (fuel - Prims.int_one)
                     | FStar_Pervasives_Native.None ->
                         FStar_Pervasives_Native.None))
           else
             if
               (code = (Prims.of_int (0x0A))) ||
                 (code = (Prims.of_int (0x0D)))
             then FStar_Pervasives_Native.None
             else parse_string_chars rest (c :: acc) (fuel - Prims.int_one))
let rec parse_iri_chars (cs : chars) (acc : chars) (fuel : Prims.nat) :
  Prims.string parse_result=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (match cs with
     | [] -> FStar_Pervasives_Native.None
     | c::rest ->
         let code = char_code c in
         if code = (Prims.of_int (0x3E))
         then
           FStar_Pervasives_Native.Some
             ((FStar_String.string_of_list (FStar_List_Tot_Base.rev acc)),
               rest)
         else
           if code = (Prims.of_int (0x5C))
           then
             (match parse_unicode_escape rest with
              | FStar_Pervasives_Native.Some (ch, rest2) ->
                  parse_iri_chars rest2 (ch :: acc) (fuel - Prims.int_one)
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
           else
             if code <= (Prims.of_int (0x20))
             then FStar_Pervasives_Native.None
             else parse_iri_chars rest (c :: acc) (fuel - Prims.int_one))
let parse_iriref (cs : chars) : Prims.string parse_result=
  match cs with
  | [] -> FStar_Pervasives_Native.None
  | c::rest ->
      if (char_code c) = (Prims.of_int (0x3C))
      then parse_iri_chars rest [] (FStar_List_Tot_Base.length rest)
      else FStar_Pervasives_Native.None
let is_pn_chars_u (code : Prims.int) : Prims.bool=
  (((code >= (Prims.of_int (0x41))) && (code <= (Prims.of_int (0x5A)))) ||
     ((code >= (Prims.of_int (0x61))) && (code <= (Prims.of_int (0x7A)))))
    || (code = (Prims.of_int (0x5F)))
let is_pn_chars (code : Prims.int) : Prims.bool=
  (((is_pn_chars_u code) ||
      ((code >= (Prims.of_int (0x30))) && (code <= (Prims.of_int (0x39)))))
     || (code = (Prims.of_int (0x2D))))
    || (code = (Prims.of_int (0xB7)))
let rec strip_trailing_dots (acc : chars) (dots : chars) : (chars * chars)=
  match acc with
  | c::rest ->
      if (char_code c) = (Prims.of_int (0x2E))
      then strip_trailing_dots rest (c :: dots)
      else (acc, dots)
  | [] -> (acc, dots)
let rec parse_bnode_label_chars (cs : chars) (acc : chars) (fuel : Prims.nat)
  : Prims.string parse_result=
  if fuel = Prims.int_zero
  then
    let uu___ = strip_trailing_dots acc [] in
    match uu___ with
    | (trimmed, dots) ->
        FStar_Pervasives_Native.Some
          ((FStar_String.string_of_list (FStar_List_Tot_Base.rev trimmed)),
            (FStar_List_Tot_Base.append dots cs))
  else
    (match cs with
     | [] ->
         let uu___1 = strip_trailing_dots acc [] in
         (match uu___1 with
          | (trimmed, _dots) ->
              FStar_Pervasives_Native.Some
                ((FStar_String.string_of_list
                    (FStar_List_Tot_Base.rev trimmed)), []))
     | c::rest ->
         let code = char_code c in
         if (is_pn_chars code) || (code = (Prims.of_int (0x2E)))
         then parse_bnode_label_chars rest (c :: acc) (fuel - Prims.int_one)
         else
           (let uu___2 = strip_trailing_dots acc [] in
            match uu___2 with
            | (trimmed, dots) ->
                FStar_Pervasives_Native.Some
                  ((FStar_String.string_of_list
                      (FStar_List_Tot_Base.rev trimmed)),
                    (FStar_List_Tot_Base.append dots cs))))
let parse_blank_node (cs : chars) : Prims.string parse_result=
  match cs with
  | c1::c2::rest ->
      if
        ((char_code c1) = (Prims.of_int (0x5F))) &&
          ((char_code c2) = (Prims.of_int (0x3A)))
      then
        (match rest with
         | c3::uu___ ->
             let code3 = char_code c3 in
             if
               (is_pn_chars_u code3) ||
                 ((code3 >= (Prims.of_int (0x30))) &&
                    (code3 <= (Prims.of_int (0x39))))
             then
               parse_bnode_label_chars rest []
                 (FStar_List_Tot_Base.length rest)
             else FStar_Pervasives_Native.None
         | [] -> FStar_Pervasives_Native.None)
      else FStar_Pervasives_Native.None
  | uu___ -> FStar_Pervasives_Native.None
let is_alpha (code : Prims.int) : Prims.bool=
  ((code >= (Prims.of_int (0x41))) && (code <= (Prims.of_int (0x5A)))) ||
    ((code >= (Prims.of_int (0x61))) && (code <= (Prims.of_int (0x7A))))
let is_alnum (code : Prims.int) : Prims.bool=
  (is_alpha code) ||
    ((code >= (Prims.of_int (0x30))) && (code <= (Prims.of_int (0x39))))
let rec parse_lang_rest (cs : chars) (acc : chars) (fuel : Prims.nat) :
  Prims.string parse_result=
  if fuel = Prims.int_zero
  then
    FStar_Pervasives_Native.Some
      ((FStar_String.string_of_list (FStar_List_Tot_Base.rev acc)), cs)
  else
    (match cs with
     | [] ->
         FStar_Pervasives_Native.Some
           ((FStar_String.string_of_list (FStar_List_Tot_Base.rev acc)), [])
     | c::rest ->
         let code = char_code c in
         if (is_alnum code) || (code = (Prims.of_int (0x2D)))
         then parse_lang_rest rest (c :: acc) (fuel - Prims.int_one)
         else
           FStar_Pervasives_Native.Some
             ((FStar_String.string_of_list (FStar_List_Tot_Base.rev acc)),
               cs))
let parse_langtag (cs : chars) : Prims.string parse_result=
  match cs with
  | [] -> FStar_Pervasives_Native.None
  | c::rest ->
      if (char_code c) = (Prims.of_int (0x40))
      then
        (match rest with
         | c2::uu___ ->
             if is_alpha (char_code c2)
             then parse_lang_rest rest [] (FStar_List_Tot_Base.length rest)
             else FStar_Pervasives_Native.None
         | [] -> FStar_Pervasives_Native.None)
      else FStar_Pervasives_Native.None
let parse_nt_subject (cs : chars) : subject parse_result=
  match parse_iriref cs with
  | FStar_Pervasives_Native.Some (iri_str, rest) ->
      if is_iri iri_str
      then FStar_Pervasives_Native.Some ((S_IRI iri_str), rest)
      else FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.None ->
      (match parse_blank_node cs with
       | FStar_Pervasives_Native.Some (label, rest) ->
           FStar_Pervasives_Native.Some ((S_BNode label), rest)
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
let parse_nt_predicate (cs : chars) : wf_iri parse_result=
  match parse_iriref cs with
  | FStar_Pervasives_Native.Some (iri_str, rest) ->
      if is_iri iri_str
      then FStar_Pervasives_Native.Some (iri_str, rest)
      else FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
let mk_wf_literal (lex : Prims.string) (dt : wf_iri)
  (lang : Prims.string FStar_Pervasives_Native.option) :
  wf_literal FStar_Pervasives_Native.option=
  let l = { lexical_form = lex; datatype = dt; lang_tag = lang } in
  if literal_wf l
  then FStar_Pervasives_Native.Some l
  else FStar_Pervasives_Native.None
let parse_nt_literal (cs : chars) : wf_literal parse_result=
  match cs with
  | [] -> FStar_Pervasives_Native.None
  | c::rest ->
      if (char_code c) <> (Prims.of_int (0x22))
      then FStar_Pervasives_Native.None
      else
        (match parse_string_chars rest [] (FStar_List_Tot_Base.length rest)
         with
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some (lexical, after_str) ->
             let mk_result lit rest1 =
               match lit with
               | FStar_Pervasives_Native.Some l ->
                   FStar_Pervasives_Native.Some (l, rest1)
               | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None in
             (match after_str with
              | c1::c2::rest2 ->
                  if
                    ((char_code c1) = (Prims.of_int (0x5E))) &&
                      ((char_code c2) = (Prims.of_int (0x5E)))
                  then
                    (match parse_iriref rest2 with
                     | FStar_Pervasives_Native.Some (dt, rest3) ->
                         if is_iri dt
                         then
                           mk_result
                             (mk_wf_literal lexical dt
                                FStar_Pervasives_Native.None) rest3
                         else FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.None ->
                         FStar_Pervasives_Native.None)
                  else
                    if (char_code c1) = (Prims.of_int (0x40))
                    then
                      (match parse_langtag after_str with
                       | FStar_Pervasives_Native.Some (lang, rest3) ->
                           mk_result
                             (mk_wf_literal lexical rdf_lang_string
                                (FStar_Pervasives_Native.Some lang)) rest3
                       | FStar_Pervasives_Native.None ->
                           FStar_Pervasives_Native.None)
                    else
                      mk_result
                        (mk_wf_literal lexical xsd_string
                           FStar_Pervasives_Native.None) after_str
              | c1::[] ->
                  if (char_code c1) = (Prims.of_int (0x40))
                  then
                    (match parse_langtag after_str with
                     | FStar_Pervasives_Native.Some (lang, rest3) ->
                         mk_result
                           (mk_wf_literal lexical rdf_lang_string
                              (FStar_Pervasives_Native.Some lang)) rest3
                     | FStar_Pervasives_Native.None ->
                         FStar_Pervasives_Native.None)
                  else
                    mk_result
                      (mk_wf_literal lexical xsd_string
                         FStar_Pervasives_Native.None) after_str
              | [] ->
                  mk_result
                    (mk_wf_literal lexical xsd_string
                       FStar_Pervasives_Native.None) []))
let parse_nt_object (cs : chars) : rdf_term parse_result=
  match parse_iriref cs with
  | FStar_Pervasives_Native.Some (iri_str, rest) ->
      if is_iri iri_str
      then FStar_Pervasives_Native.Some ((T_IRI iri_str), rest)
      else FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.None ->
      (match parse_blank_node cs with
       | FStar_Pervasives_Native.Some (label, rest) ->
           FStar_Pervasives_Native.Some ((T_BNode label), rest)
       | FStar_Pervasives_Native.None ->
           (match parse_nt_literal cs with
            | FStar_Pervasives_Native.Some (lit, rest) ->
                FStar_Pervasives_Native.Some ((T_Literal lit), rest)
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None))
let require_ws (cs : chars) : chars FStar_Pervasives_Native.option=
  match cs with
  | [] -> FStar_Pervasives_Native.None
  | c::uu___ ->
      let code = char_code c in
      if (code = (Prims.of_int (0x20))) || (code = (Prims.of_int (0x09)))
      then FStar_Pervasives_Native.Some (skip_ws cs)
      else FStar_Pervasives_Native.None
let parse_nt_triple (cs : chars) : triple parse_result=
  match parse_nt_subject cs with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some (subj, after_s) ->
      let after_ws1 = skip_ws after_s in
      (match parse_nt_predicate after_ws1 with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some (pred, after_p) ->
           let after_ws2 = skip_ws after_p in
           (match parse_nt_object after_ws2 with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (obj, after_o) ->
                let after_ws3 = skip_ws after_o in
                (match after_ws3 with
                 | c::rest ->
                     if (char_code c) = (Prims.of_int (0x2E))
                     then
                       FStar_Pervasives_Native.Some
                         ({ s = subj; p = pred; o = obj }, (skip_ws rest))
                     else FStar_Pervasives_Native.None
                 | [] -> FStar_Pervasives_Native.None)))
let rec parse_nt_lines (cs : chars) (acc : triple Prims.list)
  (fuel : Prims.nat) : triple Prims.list FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.Some (FStar_List_Tot_Base.rev acc)
  else
    (let cs1 = skip_ws cs in
     match cs1 with
     | [] -> FStar_Pervasives_Native.Some (FStar_List_Tot_Base.rev acc)
     | c::rest ->
         let code = char_code c in
         if (code = (Prims.of_int (0x0A))) || (code = (Prims.of_int (0x0D)))
         then parse_nt_lines (skip_eol cs1) acc (fuel - Prims.int_one)
         else
           if code = (Prims.of_int (0x23))
           then
             parse_nt_lines (skip_eol (skip_to_eol rest)) acc
               (fuel - Prims.int_one)
           else
             (match parse_nt_triple cs1 with
              | FStar_Pervasives_Native.Some (t, rest2) ->
                  parse_nt_lines (skip_eol rest2) (t :: acc)
                    (fuel - Prims.int_one)
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None))
let parse_ntriples (s : Prims.string) :
  rdf_graph FStar_Pervasives_Native.option=
  let cs = FStar_String.list_of_string s in
  parse_nt_lines cs [] (FStar_List_Tot_Base.length cs)
let parse_ntriples_graph (s : Prims.string) :
  rdf_graph FStar_Pervasives_Native.option=
  match parse_ntriples s with
  | FStar_Pervasives_Native.Some triples ->
      FStar_Pervasives_Native.Some
        (FStar_List_Tot_Base.fold_left (fun g t -> graph_add t g) empty_graph
           triples)
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
