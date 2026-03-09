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
let rdf_term_value_eq (t1 : rdf_term) (t2 : rdf_term) : Prims.bool=
  match (t1, t2) with
  | (T_IRI i1, T_IRI i2) -> i1 = i2
  | (T_BNode b1, T_BNode b2) -> b1 = b2
  | (T_Literal l1, T_Literal l2) -> literal_value_eq l1 l2
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
type named_graph = {
  ng_name: iri ;
  ng_graph: rdf_graph }
let __proj__Mknamed_graph__item__ng_name (projectee : named_graph) : 
  iri= match projectee with | { ng_name; ng_graph;_} -> ng_name
let __proj__Mknamed_graph__item__ng_graph (projectee : named_graph) :
  rdf_graph= match projectee with | { ng_name; ng_graph;_} -> ng_graph
type rdf_dataset = {
  ds_default: rdf_graph ;
  ds_named: named_graph Prims.list }
let __proj__Mkrdf_dataset__item__ds_default (projectee : rdf_dataset) :
  rdf_graph= match projectee with | { ds_default; ds_named;_} -> ds_default
let __proj__Mkrdf_dataset__item__ds_named (projectee : rdf_dataset) :
  named_graph Prims.list=
  match projectee with | { ds_default; ds_named;_} -> ds_named
let empty_dataset : rdf_dataset= { ds_default = empty_graph; ds_named = [] }
let make_dataset (default_g : rdf_graph) (named : named_graph Prims.list) :
  rdf_dataset= { ds_default = default_g; ds_named = named }
let rec lookup_named_graph (name : iri) (named : named_graph Prims.list) :
  rdf_graph FStar_Pervasives_Native.option=
  match named with
  | [] -> FStar_Pervasives_Native.None
  | ng::rest ->
      if ng.ng_name = name
      then FStar_Pervasives_Native.Some (ng.ng_graph)
      else lookup_named_graph name rest
let named_graph_iris (ds : rdf_dataset) : iri Prims.list=
  FStar_List_Tot_Base.map (fun ng -> ng.ng_name) ds.ds_named
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
           FStar_Pervasives_Native.Some
             ((llex = rlex) && (lang_tag_eq llang rlang))
       | Ne ->
           FStar_Pervasives_Native.Some
             ((llex <> rlex) || (Prims.op_Negation (lang_tag_eq llang rlang)))
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
let rdfs_subClassOf : wf_iri=
  "http://www.w3.org/2000/01/rdf-schema#subClassOf"
let rdfs_subPropertyOf : wf_iri=
  "http://www.w3.org/2000/01/rdf-schema#subPropertyOf"
let rdfs_domain : wf_iri= "http://www.w3.org/2000/01/rdf-schema#domain"
let rdfs_range : wf_iri= "http://www.w3.org/2000/01/rdf-schema#range"
let rdf_type : wf_iri= "http://www.w3.org/1999/02/22-rdf-syntax-ns#type"
let rdfs_Class : wf_iri= "http://www.w3.org/2000/01/rdf-schema#Class"
let rdf_Property : wf_iri=
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#Property"
let rdfs_Resource : wf_iri= "http://www.w3.org/2000/01/rdf-schema#Resource"
let rdfs_Literal : wf_iri= "http://www.w3.org/2000/01/rdf-schema#Literal"
let rdfs_ContainerMembershipProperty : wf_iri=
  "http://www.w3.org/2000/01/rdf-schema#ContainerMembershipProperty"
let rdfs_member : wf_iri= "http://www.w3.org/2000/01/rdf-schema#member"
let rdfs_Datatype : wf_iri= "http://www.w3.org/2000/01/rdf-schema#Datatype"
let rdf_1 : wf_iri= "http://www.w3.org/1999/02/22-rdf-syntax-ns#_1"
let rdf_2 : wf_iri= "http://www.w3.org/1999/02/22-rdf-syntax-ns#_2"
let rdf_3 : wf_iri= "http://www.w3.org/1999/02/22-rdf-syntax-ns#_3"
let rdf_4 : wf_iri= "http://www.w3.org/1999/02/22-rdf-syntax-ns#_4"
let rdf_5 : wf_iri= "http://www.w3.org/1999/02/22-rdf-syntax-ns#_5"
let container_membership_properties : wf_iri Prims.list=
  [rdf_1; rdf_2; rdf_3; rdf_4; rdf_5]
let subject_to_term (s : subject) : rdf_term=
  match s with | S_IRI i -> T_IRI i | S_BNode b -> T_BNode b
let term_to_subject (t : rdf_term) : subject FStar_Pervasives_Native.option=
  match t with
  | T_IRI i -> FStar_Pervasives_Native.Some (S_IRI i)
  | T_BNode b -> FStar_Pervasives_Native.Some (S_BNode b)
  | T_Literal uu___ -> FStar_Pervasives_Native.None
let rec find_objects (g : rdf_graph) (subj : subject) (pred : wf_iri) :
  rdf_term Prims.list=
  match g with
  | [] -> []
  | hd::tl ->
      let rest = find_objects tl subj pred in
      if (subject_eq hd.s subj) && (hd.p = pred)
      then (hd.o) :: rest
      else rest
let rec find_subjects (g : rdf_graph) (pred : wf_iri) (obj : rdf_term) :
  subject Prims.list=
  match g with
  | [] -> []
  | hd::tl ->
      let rest = find_subjects tl pred obj in
      if (hd.p = pred) && (rdf_term_eq hd.o obj)
      then (hd.s) :: rest
      else rest
let has_triple (g : rdf_graph) (t : triple) : Prims.bool= mem_triple t g
let add_triple_if_new (g : rdf_graph) (t : triple) : rdf_graph= graph_add t g
let rec add_triples_if_new (g : rdf_graph) (ts : triple Prims.list) :
  rdf_graph=
  match ts with
  | [] -> g
  | hd::tl -> add_triples_if_new (add_triple_if_new g hd) tl
let rdfs_rule_subPropertyOf (g : rdf_graph) : rdf_graph=
  FStar_List_Tot_Base.fold_left
    (fun acc t ->
       let super_props = find_objects g (S_IRI (t.p)) rdfs_subPropertyOf in
       FStar_List_Tot_Base.fold_left
         (fun acc2 q_term ->
            match q_term with
            | T_IRI q ->
                let new_t = { s = (t.s); p = q; o = (t.o) } in
                add_triple_if_new acc2 new_t
            | uu___ -> acc2) acc super_props) g g
let rdfs_rule_domain (g : rdf_graph) : rdf_graph=
  FStar_List_Tot_Base.fold_left
    (fun acc t ->
       let domain_classes = find_objects g (S_IRI (t.p)) rdfs_domain in
       FStar_List_Tot_Base.fold_left
         (fun acc2 c_term ->
            let new_t = { s = (t.s); p = rdf_type; o = c_term } in
            add_triple_if_new acc2 new_t) acc domain_classes) g g
let rdfs_rule_range (g : rdf_graph) : rdf_graph=
  FStar_List_Tot_Base.fold_left
    (fun acc t ->
       let range_classes = find_objects g (S_IRI (t.p)) rdfs_range in
       match term_to_subject t.o with
       | FStar_Pervasives_Native.Some b_subj ->
           FStar_List_Tot_Base.fold_left
             (fun acc2 c_term ->
                let new_t = { s = b_subj; p = rdf_type; o = c_term } in
                add_triple_if_new acc2 new_t) acc range_classes
       | FStar_Pervasives_Native.None -> acc) g g
let rdfs_rule_subClassOf (g : rdf_graph) : rdf_graph=
  FStar_List_Tot_Base.fold_left
    (fun acc t ->
       if t.p = rdf_type
       then
         match t.o with
         | T_IRI class_iri ->
             let super_classes =
               find_objects g (S_IRI class_iri) rdfs_subClassOf in
             FStar_List_Tot_Base.fold_left
               (fun acc2 b_term ->
                  let new_t = { s = (t.s); p = rdf_type; o = b_term } in
                  add_triple_if_new acc2 new_t) acc super_classes
         | uu___ -> acc
       else acc) g g
let rdfs_rule_container_membership (g : rdf_graph) : rdf_graph=
  FStar_List_Tot_Base.fold_left
    (fun acc cmp ->
       let t1 =
         { s = (S_IRI cmp); p = rdfs_subPropertyOf; o = (T_IRI rdfs_member) } in
       let t2 =
         {
           s = (S_IRI cmp);
           p = rdf_type;
           o = (T_IRI rdfs_ContainerMembershipProperty)
         } in
       add_triple_if_new (add_triple_if_new acc t1) t2) g
    container_membership_properties
let rdfs_closure_step (g : rdf_graph) : rdf_graph=
  let g1 = rdfs_rule_subPropertyOf g in
  let g2 = rdfs_rule_domain g1 in
  let g3 = rdfs_rule_range g2 in
  let g4 = rdfs_rule_subClassOf g3 in
  let g5 = rdfs_rule_container_membership g4 in g5
let rec rdfs_closure (g : rdf_graph) (fuel : Prims.nat) : rdf_graph=
  match fuel with
  | uu___ when uu___ = Prims.int_zero -> g
  | uu___ ->
      let g' = rdfs_closure_step g in
      if (graph_len g') = (graph_len g)
      then g
      else rdfs_closure g' (fuel - Prims.int_one)
let is_digit (c : FStar_Char.char) : Prims.bool=
  let code = FStar_Char.int_of_char c in
  (code >= (Prims.of_int (0x30))) && (code <= (Prims.of_int (0x39)))
let rec strip_leading_zeros (cs : FStar_Char.char Prims.list) :
  FStar_Char.char Prims.list=
  match cs with
  | [] -> [FStar_Char.char_of_int (Prims.of_int (0x30))]
  | c::[] -> [c]
  | c::rest ->
      if (FStar_Char.int_of_char c) = (Prims.of_int (0x30))
      then strip_leading_zeros rest
      else cs
let normalize_integer_lexical (s : Prims.string) : Prims.string=
  let chars = FStar_String.list_of_string s in
  match chars with
  | [] -> "0"
  | c::rest ->
      let code = FStar_Char.int_of_char c in
      if code = (Prims.of_int (0x2D))
      then
        let normalized = strip_leading_zeros rest in
        (match normalized with
         | z::[] ->
             if (FStar_Char.int_of_char z) = (Prims.of_int (0x30))
             then "0"
             else
               FStar_String.concat ""
                 ["-"; FStar_String.string_of_list normalized]
         | uu___ ->
             FStar_String.concat ""
               ["-"; FStar_String.string_of_list normalized])
      else
        if code = (Prims.of_int (0x2B))
        then FStar_String.string_of_list (strip_leading_zeros rest)
        else FStar_String.string_of_list (strip_leading_zeros chars)
let strip_trailing_zeros (cs : FStar_Char.char Prims.list) :
  FStar_Char.char Prims.list=
  match cs with
  | [] -> [FStar_Char.char_of_int (Prims.of_int (0x30))]
  | uu___ ->
      let rev = FStar_List_Tot_Base.rev cs in
      let rec drop_zeros l =
        match l with
        | [] -> [FStar_Char.char_of_int (Prims.of_int (0x30))]
        | c::rest ->
            if (FStar_Char.int_of_char c) = (Prims.of_int (0x30))
            then drop_zeros rest
            else FStar_List_Tot_Base.rev l in
      drop_zeros rev
let rec split_at_dot (cs : FStar_Char.char Prims.list)
  (acc : FStar_Char.char Prims.list) :
  (FStar_Char.char Prims.list * FStar_Char.char Prims.list
    FStar_Pervasives_Native.option)=
  match cs with
  | [] -> ((FStar_List_Tot_Base.rev acc), FStar_Pervasives_Native.None)
  | c::rest ->
      if (FStar_Char.int_of_char c) = (Prims.of_int (0x2E))
      then
        ((FStar_List_Tot_Base.rev acc), (FStar_Pervasives_Native.Some rest))
      else split_at_dot rest (c :: acc)
let normalize_decimal_lexical (s : Prims.string) : Prims.string=
  let chars = FStar_String.list_of_string s in
  let uu___ =
    match chars with
    | [] -> ("", chars)
    | c::rest ->
        let code = FStar_Char.int_of_char c in
        if code = (Prims.of_int (0x2D))
        then ("-", rest)
        else if code = (Prims.of_int (0x2B)) then ("", rest) else ("", chars) in
  match uu___ with
  | (sign, digits) ->
      let uu___1 = split_at_dot digits [] in
      (match uu___1 with
       | (int_part, frac_opt) ->
           let norm_int = strip_leading_zeros int_part in
           (match frac_opt with
            | FStar_Pervasives_Native.None ->
                let result =
                  FStar_String.concat ""
                    [sign; FStar_String.string_of_list norm_int] in
                if (sign = "-") && (result = "-0") then "0" else result
            | FStar_Pervasives_Native.Some frac_digits ->
                let norm_frac = strip_trailing_zeros frac_digits in
                let int_str = FStar_String.string_of_list norm_int in
                let frac_str = FStar_String.string_of_list norm_frac in
                let result =
                  FStar_String.concat "" [sign; int_str; "."; frac_str] in
                if ((sign = "-") && (int_str = "0")) && (frac_str = "0")
                then "0.0"
                else result))
let datatype_value_eq (l1 : literal) (l2 : literal) : Prims.bool=
  if l1.datatype = l2.datatype
  then
    (if l1.datatype = xsd_integer
     then
       ((normalize_integer_lexical l1.lexical_form) =
          (normalize_integer_lexical l2.lexical_form))
         && (lang_tag_option_eq l1.lang_tag l2.lang_tag)
     else
       if l1.datatype = xsd_decimal
       then
         ((normalize_decimal_lexical l1.lexical_form) =
            (normalize_decimal_lexical l2.lexical_form))
           && (lang_tag_option_eq l1.lang_tag l2.lang_tag)
       else literal_eq l1 l2)
  else false
