include RDF_Term
include RDF_Triple
include RDF_Graph
include RDF_Indexed
include RDFS_Closure
include OWL_Closure
open Prims
let rename_bnode_id (prefix : Prims.string) (id : RDF_Term.bnode_id) :
  RDF_Term.bnode_id= FStar_String.concat "" [prefix; ":"; id]
let rename_subject_bnodes (prefix : Prims.string) (s : RDF_Term.subject) :
  RDF_Term.subject=
  match s with
  | RDF_Term.S_IRI i -> RDF_Term.S_IRI i
  | RDF_Term.S_BNode b -> RDF_Term.S_BNode (rename_bnode_id prefix b)
let rename_term_bnodes (prefix : Prims.string) (o : RDF_Term.rdf_term) :
  RDF_Term.rdf_term=
  match o with
  | RDF_Term.T_IRI i -> RDF_Term.T_IRI i
  | RDF_Term.T_Literal l -> RDF_Term.T_Literal l
  | RDF_Term.T_BNode b -> RDF_Term.T_BNode (rename_bnode_id prefix b)
let rename_triple_bnodes (prefix : Prims.string) (t : RDF_Triple.triple) :
  RDF_Triple.triple=
  {
    RDF_Triple.s = (rename_subject_bnodes prefix t.RDF_Triple.s);
    RDF_Triple.p = (t.RDF_Triple.p);
    RDF_Triple.o = (rename_term_bnodes prefix t.RDF_Triple.o)
  }
let rec graph_bnodes_acc (acc : RDF_Term.bnode_id Prims.list)
  (g : RDF_Graph.rdf_graph) : RDF_Term.bnode_id Prims.list=
  match g with
  | [] -> FStar_List_Tot_Base.rev acc
  | hd::tl ->
      let acc1 =
        match hd.RDF_Triple.s with
        | RDF_Term.S_BNode id -> id :: acc
        | uu___ -> acc in
      let acc2 =
        match hd.RDF_Triple.o with
        | RDF_Term.T_BNode id -> id :: acc1
        | uu___ -> acc1 in
      graph_bnodes_acc acc2 tl
let graph_bnodes (g : RDF_Graph.rdf_graph) : RDF_Term.bnode_id Prims.list=
  graph_bnodes_acc [] g
let graph_add_unchecked (t : RDF_Triple.triple) (g : RDF_Graph.rdf_graph) :
  RDF_Graph.rdf_graph= t :: g
let graph_finalise (g : RDF_Graph.rdf_graph) : RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.rev g
let dataset_finalise (ds : RDF_Graph.rdf_dataset) : RDF_Graph.rdf_dataset=
  {
    RDF_Graph.ds_default = (graph_finalise ds.RDF_Graph.ds_default);
    RDF_Graph.ds_named =
      (FStar_List_Tot_Base.map
         (fun ng ->
            {
              RDF_Graph.ng_name = (ng.RDF_Graph.ng_name);
              RDF_Graph.ng_graph = (graph_finalise ng.RDF_Graph.ng_graph)
            }) ds.RDF_Graph.ds_named)
  }
let graph_remove (t : RDF_Triple.triple) (g : RDF_Graph.rdf_graph) :
  RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.filter
    (fun hd -> Prims.op_Negation (RDF_Triple.triple_eq hd t)) g
let rec graph_union (g1 : RDF_Graph.rdf_graph) (g2 : RDF_Graph.rdf_graph) :
  RDF_Graph.rdf_graph=
  match g1 with
  | [] -> g2
  | hd::tl -> graph_union tl (RDF_Graph.graph_add hd g2)
let rec find_by_subject (subj : RDF_Term.wf_iri) (g : RDF_Graph.rdf_graph) :
  RDF_Graph.rdf_graph=
  match g with
  | [] -> []
  | hd::tl ->
      let rest = find_by_subject subj tl in
      (match hd.RDF_Triple.s with
       | RDF_Term.S_IRI i -> if i = subj then hd :: rest else rest
       | uu___ -> rest)
let rec find_by_predicate (pred : RDF_Term.wf_iri) (g : RDF_Graph.rdf_graph)
  : RDF_Graph.rdf_graph=
  match g with
  | [] -> []
  | hd::tl ->
      let rest = find_by_predicate pred tl in
      if hd.RDF_Triple.p = pred then hd :: rest else rest
type var_name = Prims.string
type pattern_term =
  | PT_Concrete of RDF_Term.rdf_term 
  | PT_Var of var_name 
let uu___is_PT_Concrete (projectee : pattern_term) : Prims.bool=
  match projectee with | PT_Concrete _0 -> true | uu___ -> false
let __proj__PT_Concrete__item___0 (projectee : pattern_term) :
  RDF_Term.rdf_term= match projectee with | PT_Concrete _0 -> _0
let uu___is_PT_Var (projectee : pattern_term) : Prims.bool=
  match projectee with | PT_Var _0 -> true | uu___ -> false
let __proj__PT_Var__item___0 (projectee : pattern_term) : var_name=
  match projectee with | PT_Var _0 -> _0
type pattern_subject =
  | PS_Concrete of RDF_Term.subject 
  | PS_Var of var_name 
let uu___is_PS_Concrete (projectee : pattern_subject) : Prims.bool=
  match projectee with | PS_Concrete _0 -> true | uu___ -> false
let __proj__PS_Concrete__item___0 (projectee : pattern_subject) :
  RDF_Term.subject= match projectee with | PS_Concrete _0 -> _0
let uu___is_PS_Var (projectee : pattern_subject) : Prims.bool=
  match projectee with | PS_Var _0 -> true | uu___ -> false
let __proj__PS_Var__item___0 (projectee : pattern_subject) : var_name=
  match projectee with | PS_Var _0 -> _0
type triple_pattern =
  {
  tp_s: pattern_subject ;
  tp_p: RDF_Term.wf_iri ;
  tp_o: pattern_term }
let __proj__Mktriple_pattern__item__tp_s (projectee : triple_pattern) :
  pattern_subject= match projectee with | { tp_s; tp_p; tp_o;_} -> tp_s
let __proj__Mktriple_pattern__item__tp_p (projectee : triple_pattern) :
  RDF_Term.wf_iri= match projectee with | { tp_s; tp_p; tp_o;_} -> tp_p
let __proj__Mktriple_pattern__item__tp_o (projectee : triple_pattern) :
  pattern_term= match projectee with | { tp_s; tp_p; tp_o;_} -> tp_o
type solution_mapping = (var_name * RDF_Term.rdf_term) Prims.list
type bgp = triple_pattern Prims.list
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
  | SV_BNode of RDF_Term.bnode_id 
  | SV_TypedLiteral of Prims.string * RDF_Term.wf_iri 
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
let __proj__SV_BNode__item__id (projectee : sparql_value) :
  RDF_Term.bnode_id= match projectee with | SV_BNode id -> id
let uu___is_SV_TypedLiteral (projectee : sparql_value) : Prims.bool=
  match projectee with
  | SV_TypedLiteral (lexical, datatype) -> true
  | uu___ -> false
let __proj__SV_TypedLiteral__item__lexical (projectee : sparql_value) :
  Prims.string=
  match projectee with | SV_TypedLiteral (lexical, datatype) -> lexical
let __proj__SV_TypedLiteral__item__datatype (projectee : sparql_value) :
  RDF_Term.wf_iri=
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
             ((llex = rlex) && (RDF_Term.lang_tag_eq llang rlang))
       | Ne ->
           FStar_Pervasives_Native.Some
             ((llex <> rlex) ||
                (Prims.op_Negation (RDF_Term.lang_tag_eq llang rlang)))
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
type filter_expr_eval =
  solution_mapping -> RDF_Term.rdf_term FStar_Pervasives_Native.option
let bind_eval (eval : filter_expr_eval) (var : var_name)
  (mu : solution_mapping) :
  (var_name * RDF_Term.rdf_term) FStar_Pervasives_Native.option=
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
let string_substring (s : Prims.string) (i : Prims.nat) (len : Prims.nat) :
  Prims.string=
  let slen = FStar_String.strlen s in
  if i >= slen
  then ""
  else
    (let max_len = slen - i in
     let actual_len = if len <= max_len then len else max_len in
     FStar_String.sub s i actual_len)
let rec sparql_concat (args : Prims.string Prims.list) : Prims.string=
  match args with
  | [] -> ""
  | hd::tl -> FStar_String.concat "" [hd; sparql_concat tl]
let rec find_objects_acc (acc : RDF_Term.rdf_term Prims.list)
  (g : RDF_Graph.rdf_graph) (subj : RDF_Term.subject)
  (pred : RDF_Term.wf_iri) : RDF_Term.rdf_term Prims.list=
  match g with
  | [] -> FStar_List_Tot_Base.rev acc
  | hd::tl ->
      if
        (RDF_Term.subject_eq hd.RDF_Triple.s subj) &&
          (hd.RDF_Triple.p = pred)
      then find_objects_acc ((hd.RDF_Triple.o) :: acc) tl subj pred
      else find_objects_acc acc tl subj pred
let find_objects (g : RDF_Graph.rdf_graph) (subj : RDF_Term.subject)
  (pred : RDF_Term.wf_iri) : RDF_Term.rdf_term Prims.list=
  find_objects_acc [] g subj pred
let rec find_subjects_acc (acc : RDF_Term.subject Prims.list)
  (g : RDF_Graph.rdf_graph) (pred : RDF_Term.wf_iri)
  (obj : RDF_Term.rdf_term) : RDF_Term.subject Prims.list=
  match g with
  | [] -> FStar_List_Tot_Base.rev acc
  | hd::tl ->
      if
        (hd.RDF_Triple.p = pred) &&
          (RDF_Term.rdf_term_eq hd.RDF_Triple.o obj)
      then find_subjects_acc ((hd.RDF_Triple.s) :: acc) tl pred obj
      else find_subjects_acc acc tl pred obj
let find_subjects (g : RDF_Graph.rdf_graph) (pred : RDF_Term.wf_iri)
  (obj : RDF_Term.rdf_term) : RDF_Term.subject Prims.list=
  find_subjects_acc [] g pred obj
