include RDF_Term
include RDF_Triple
include RDF_Graph
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
let rec mem_triple (t : RDF_Triple.triple) (g : RDF_Graph.rdf_graph) :
  Prims.bool=
  match g with
  | [] -> false
  | hd::tl -> (RDF_Triple.triple_eq hd t) || (mem_triple t tl)
let graph_add (t : RDF_Triple.triple) (g : RDF_Graph.rdf_graph) :
  RDF_Graph.rdf_graph=
  if mem_triple t g then g else FStar_List_Tot_Base.op_At g [t]
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
let graph_len (g : RDF_Graph.rdf_graph) : Prims.nat=
  FStar_List_Tot_Base.length g
let rec graph_union (g1 : RDF_Graph.rdf_graph) (g2 : RDF_Graph.rdf_graph) :
  RDF_Graph.rdf_graph=
  match g1 with | [] -> g2 | hd::tl -> graph_union tl (graph_add hd g2)
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
type 'a bucket_map = 'a RDF_Indexed.bucket_map
let bucket_lookup (m : 'a bucket_map) (k : Prims.string) : 'a Prims.list=
  RDF_Indexed.bucket_lookup m k
let bucket_replace (m : 'a bucket_map) (k : Prims.string) (v : 'a Prims.list)
  : 'a bucket_map= RDF_Indexed.bucket_replace m k v
let bucket_push (m : 'a bucket_map) (k : Prims.string) (t : 'a) :
  'a bucket_map= RDF_Indexed.bucket_push m k t
let build_bucket (key_of : 'a -> Prims.string FStar_Pervasives_Native.option)
  (ts : 'a Prims.list) : 'a bucket_map= RDF_Indexed.build_bucket key_of ts
type indexed_graph =
  {
  ig_triples: RDF_Triple.triple Prims.list ;
  ig_pred: RDF_Triple.triple bucket_map ;
  ig_subj: RDF_Triple.triple bucket_map ;
  ig_obj: RDF_Triple.triple bucket_map ;
  ig_sp: RDF_Triple.triple bucket_map ;
  ig_po: RDF_Triple.triple bucket_map ;
  ig_so: RDF_Triple.triple bucket_map }
let __proj__Mkindexed_graph__item__ig_triples (projectee : indexed_graph) :
  RDF_Triple.triple Prims.list=
  match projectee with
  | { ig_triples; ig_pred; ig_subj; ig_obj; ig_sp; ig_po; ig_so;_} ->
      ig_triples
let __proj__Mkindexed_graph__item__ig_pred (projectee : indexed_graph) :
  RDF_Triple.triple bucket_map=
  match projectee with
  | { ig_triples; ig_pred; ig_subj; ig_obj; ig_sp; ig_po; ig_so;_} -> ig_pred
let __proj__Mkindexed_graph__item__ig_subj (projectee : indexed_graph) :
  RDF_Triple.triple bucket_map=
  match projectee with
  | { ig_triples; ig_pred; ig_subj; ig_obj; ig_sp; ig_po; ig_so;_} -> ig_subj
let __proj__Mkindexed_graph__item__ig_obj (projectee : indexed_graph) :
  RDF_Triple.triple bucket_map=
  match projectee with
  | { ig_triples; ig_pred; ig_subj; ig_obj; ig_sp; ig_po; ig_so;_} -> ig_obj
let __proj__Mkindexed_graph__item__ig_sp (projectee : indexed_graph) :
  RDF_Triple.triple bucket_map=
  match projectee with
  | { ig_triples; ig_pred; ig_subj; ig_obj; ig_sp; ig_po; ig_so;_} -> ig_sp
let __proj__Mkindexed_graph__item__ig_po (projectee : indexed_graph) :
  RDF_Triple.triple bucket_map=
  match projectee with
  | { ig_triples; ig_pred; ig_subj; ig_obj; ig_sp; ig_po; ig_so;_} -> ig_po
let __proj__Mkindexed_graph__item__ig_so (projectee : indexed_graph) :
  RDF_Triple.triple bucket_map=
  match projectee with
  | { ig_triples; ig_pred; ig_subj; ig_obj; ig_sp; ig_po; ig_so;_} -> ig_so
let subject_to_key (s : RDF_Term.subject) : Prims.string=
  match s with
  | RDF_Term.S_IRI i -> FStar_String.concat "" ["I_"; i]
  | RDF_Term.S_BNode b -> FStar_String.concat "" ["B_"; b]
let term_to_key_opt (o : RDF_Term.rdf_term) :
  Prims.string FStar_Pervasives_Native.option=
  match o with
  | RDF_Term.T_IRI i ->
      FStar_Pervasives_Native.Some (FStar_String.concat "" ["I_"; i])
  | RDF_Term.T_BNode b ->
      FStar_Pervasives_Native.Some (FStar_String.concat "" ["B_"; b])
  | RDF_Term.T_Literal uu___ -> FStar_Pervasives_Native.None
let unit_sep : Prims.string= "\031"
let sp_key (s : RDF_Term.subject) (p : RDF_Term.wf_iri) : Prims.string=
  FStar_String.concat "" [subject_to_key s; unit_sep; p]
let po_key_opt (p : RDF_Term.wf_iri) (o : RDF_Term.rdf_term) :
  Prims.string FStar_Pervasives_Native.option=
  match term_to_key_opt o with
  | FStar_Pervasives_Native.Some k ->
      FStar_Pervasives_Native.Some (FStar_String.concat "" [p; unit_sep; k])
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
let so_key_opt (s : RDF_Term.subject) (o : RDF_Term.rdf_term) :
  Prims.string FStar_Pervasives_Native.option=
  match term_to_key_opt o with
  | FStar_Pervasives_Native.Some k ->
      FStar_Pervasives_Native.Some
        (FStar_String.concat "" [subject_to_key s; unit_sep; k])
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
let find_objects_indexed (ig : indexed_graph) (subj : RDF_Term.subject)
  (pred : RDF_Term.wf_iri) : RDF_Term.rdf_term Prims.list=
  let bucket = bucket_lookup ig.ig_sp (sp_key subj pred) in
  FStar_List_Tot_Base.map (fun t -> t.RDF_Triple.o) bucket
let find_subjects_indexed (ig : indexed_graph) (pred : RDF_Term.wf_iri)
  (obj : RDF_Term.rdf_term) : RDF_Term.subject Prims.list=
  let bucket =
    match po_key_opt pred obj with
    | FStar_Pervasives_Native.Some k -> bucket_lookup ig.ig_po k
    | FStar_Pervasives_Native.None ->
        FStar_List_Tot_Base.filter
          (fun t -> RDF_Term.rdf_term_eq t.RDF_Triple.o obj)
          (bucket_lookup ig.ig_pred pred) in
  FStar_List_Tot_Base.map (fun t -> t.RDF_Triple.s) bucket
let add_triple_to_indexes (ig : indexed_graph) (t : RDF_Triple.triple) :
  indexed_graph=
  let new_pred = bucket_push ig.ig_pred t.RDF_Triple.p t in
  let new_subj = bucket_push ig.ig_subj (subject_to_key t.RDF_Triple.s) t in
  let new_obj =
    match term_to_key_opt t.RDF_Triple.o with
    | FStar_Pervasives_Native.Some k -> bucket_push ig.ig_obj k t
    | FStar_Pervasives_Native.None -> ig.ig_obj in
  let new_sp = bucket_push ig.ig_sp (sp_key t.RDF_Triple.s t.RDF_Triple.p) t in
  let new_po =
    match po_key_opt t.RDF_Triple.p t.RDF_Triple.o with
    | FStar_Pervasives_Native.Some k -> bucket_push ig.ig_po k t
    | FStar_Pervasives_Native.None -> ig.ig_po in
  let new_so =
    match so_key_opt t.RDF_Triple.s t.RDF_Triple.o with
    | FStar_Pervasives_Native.Some k -> bucket_push ig.ig_so k t
    | FStar_Pervasives_Native.None -> ig.ig_so in
  {
    ig_triples = (t :: (ig.ig_triples));
    ig_pred = new_pred;
    ig_subj = new_subj;
    ig_obj = new_obj;
    ig_sp = new_sp;
    ig_po = new_po;
    ig_so = new_so
  }
let rec build_indexed_aux (g : RDF_Triple.triple Prims.list)
  (acc : indexed_graph) : indexed_graph=
  match g with
  | [] -> acc
  | t::rest -> build_indexed_aux rest (add_triple_to_indexes acc t)
let bucket_key_pred (t : RDF_Triple.triple) :
  Prims.string FStar_Pervasives_Native.option=
  FStar_Pervasives_Native.Some (t.RDF_Triple.p)
let bucket_key_subj (t : RDF_Triple.triple) :
  Prims.string FStar_Pervasives_Native.option=
  FStar_Pervasives_Native.Some (subject_to_key t.RDF_Triple.s)
let bucket_key_obj (t : RDF_Triple.triple) :
  Prims.string FStar_Pervasives_Native.option= term_to_key_opt t.RDF_Triple.o
let bucket_key_sp (t : RDF_Triple.triple) :
  Prims.string FStar_Pervasives_Native.option=
  FStar_Pervasives_Native.Some (sp_key t.RDF_Triple.s t.RDF_Triple.p)
let bucket_key_po (t : RDF_Triple.triple) :
  Prims.string FStar_Pervasives_Native.option=
  po_key_opt t.RDF_Triple.p t.RDF_Triple.o
let bucket_key_so (t : RDF_Triple.triple) :
  Prims.string FStar_Pervasives_Native.option=
  so_key_opt t.RDF_Triple.s t.RDF_Triple.o
let empty_indexed : indexed_graph=
  {
    ig_triples = [];
    ig_pred = [];
    ig_subj = [];
    ig_obj = [];
    ig_sp = [];
    ig_po = [];
    ig_so = []
  }
let build_indexed (g : RDF_Graph.rdf_graph) : indexed_graph=
  {
    ig_triples = g;
    ig_pred = (build_bucket bucket_key_pred g);
    ig_subj = (build_bucket bucket_key_subj g);
    ig_obj = (build_bucket bucket_key_obj g);
    ig_sp = (build_bucket bucket_key_sp g);
    ig_po = (build_bucket bucket_key_po g);
    ig_so = (build_bucket bucket_key_so g)
  }
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
let rdfs_subClassOf : RDF_Term.wf_iri= RDF_Vocabulary.rdfs_subClassOf
let rdfs_subPropertyOf : RDF_Term.wf_iri= RDF_Vocabulary.rdfs_subPropertyOf
let rdfs_domain : RDF_Term.wf_iri= RDF_Vocabulary.rdfs_domain
let rdfs_range : RDF_Term.wf_iri= RDF_Vocabulary.rdfs_range
let rdf_type : RDF_Term.wf_iri= RDF_Vocabulary.rdf_type
let rdfs_Class : RDF_Term.wf_iri= RDF_Vocabulary.rdfs_Class
let rdf_Property : RDF_Term.wf_iri= RDF_Vocabulary.rdf_Property
let rdfs_Resource : RDF_Term.wf_iri= RDF_Vocabulary.rdfs_Resource
let rdfs_Literal : RDF_Term.wf_iri= RDF_Vocabulary.rdfs_Literal
let rdfs_ContainerMembershipProperty : RDF_Term.wf_iri=
  RDF_Vocabulary.rdfs_ContainerMembershipProperty
let rdfs_member : RDF_Term.wf_iri= RDF_Vocabulary.rdfs_member
let rdfs_Datatype : RDF_Term.wf_iri= RDF_Vocabulary.rdfs_Datatype
let rdf_1 : RDF_Term.wf_iri= RDF_Vocabulary.rdf_1
let rdf_2 : RDF_Term.wf_iri= RDF_Vocabulary.rdf_2
let rdf_3 : RDF_Term.wf_iri= RDF_Vocabulary.rdf_3
let rdf_4 : RDF_Term.wf_iri= RDF_Vocabulary.rdf_4
let rdf_5 : RDF_Term.wf_iri= RDF_Vocabulary.rdf_5
let container_membership_properties : RDF_Term.wf_iri Prims.list=
  [rdf_1; rdf_2; rdf_3; rdf_4; rdf_5]
let subject_to_term (s : RDF_Term.subject) : RDF_Term.rdf_term=
  match s with
  | RDF_Term.S_IRI i -> RDF_Term.T_IRI i
  | RDF_Term.S_BNode b -> RDF_Term.T_BNode b
let term_to_subject (t : RDF_Term.rdf_term) :
  RDF_Term.subject FStar_Pervasives_Native.option=
  match t with
  | RDF_Term.T_IRI i -> FStar_Pervasives_Native.Some (RDF_Term.S_IRI i)
  | RDF_Term.T_BNode b -> FStar_Pervasives_Native.Some (RDF_Term.S_BNode b)
  | RDF_Term.T_Literal uu___ -> FStar_Pervasives_Native.None
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
let add_triple_if_new (g : RDF_Graph.rdf_graph) (t : RDF_Triple.triple) :
  RDF_Graph.rdf_graph= graph_add t g
let add_triple_unchecked (g : RDF_Graph.rdf_graph) (t : RDF_Triple.triple) :
  RDF_Graph.rdf_graph= t :: g
let term_to_key_total (o : RDF_Term.rdf_term) : Prims.string=
  match o with
  | RDF_Term.T_IRI i -> FStar_String.concat "" ["I_"; i]
  | RDF_Term.T_BNode b -> FStar_String.concat "" ["B_"; b]
  | RDF_Term.T_Literal l ->
      FStar_String.concat ""
        ["L_";
        l.RDF_Term.lexical_form;
        "^^";
        l.RDF_Term.datatype;
        (match l.RDF_Term.lang_tag with
         | FStar_Pervasives_Native.Some t -> FStar_String.concat "" ["@"; t]
         | FStar_Pervasives_Native.None -> "")]
let triple_to_key (t : RDF_Triple.triple) : Prims.string=
  FStar_String.concat ""
    [subject_to_key t.RDF_Triple.s;
    unit_sep;
    t.RDF_Triple.p;
    unit_sep;
    term_to_key_total t.RDF_Triple.o]
let triple_cmp (t1 : RDF_Triple.triple) (t2 : RDF_Triple.triple) : Prims.int=
  FStar_String.compare (triple_to_key t1) (triple_to_key t2)
let rec dedup_sorted_aux
  (prev_key : Prims.string FStar_Pervasives_Native.option)
  (ts : RDF_Triple.triple Prims.list) (acc : RDF_Triple.triple Prims.list) :
  RDF_Triple.triple Prims.list=
  match ts with
  | [] -> FStar_List_Tot_Base.rev acc
  | t::rest ->
      let k = triple_to_key t in
      let dup =
        match prev_key with
        | FStar_Pervasives_Native.Some p -> p = k
        | FStar_Pervasives_Native.None -> false in
      if dup
      then dedup_sorted_aux prev_key rest acc
      else dedup_sorted_aux (FStar_Pervasives_Native.Some k) rest (t :: acc)
let graph_dedup_sort (g : RDF_Graph.rdf_graph) : RDF_Graph.rdf_graph=
  let sorted = FStar_List_Tot_Base.sortWith triple_cmp g in
  dedup_sorted_aux FStar_Pervasives_Native.None sorted []
let rec add_triples_if_new (g : RDF_Graph.rdf_graph)
  (ts : RDF_Triple.triple Prims.list) : RDF_Graph.rdf_graph=
  match ts with
  | [] -> g
  | hd::tl -> add_triples_if_new (add_triple_if_new g hd) tl
let rdfs_rule_subPropertyOf (g : RDF_Graph.rdf_graph) (ig : indexed_graph) :
  RDF_Graph.rdf_graph=
  let decls = bucket_lookup ig.ig_pred rdfs_subPropertyOf in
  FStar_List_Tot_Base.fold_left
    (fun acc decl ->
       match ((decl.RDF_Triple.s), (decl.RDF_Triple.o)) with
       | (RDF_Term.S_IRI p, RDF_Term.T_IRI q) ->
           let matching = bucket_lookup ig.ig_pred p in
           FStar_List_Tot_Base.fold_left
             (fun acc2 t ->
                let new_t =
                  {
                    RDF_Triple.s = (t.RDF_Triple.s);
                    RDF_Triple.p = q;
                    RDF_Triple.o = (t.RDF_Triple.o)
                  } in
                add_triple_unchecked acc2 new_t) acc matching
       | (uu___, uu___1) -> acc) g decls
let rdfs_rule_domain (g : RDF_Graph.rdf_graph) (ig : indexed_graph) :
  RDF_Graph.rdf_graph=
  let decls = bucket_lookup ig.ig_pred rdfs_domain in
  FStar_List_Tot_Base.fold_left
    (fun acc decl ->
       match decl.RDF_Triple.s with
       | RDF_Term.S_IRI p ->
           let matching = bucket_lookup ig.ig_pred p in
           FStar_List_Tot_Base.fold_left
             (fun acc2 t ->
                let new_t =
                  {
                    RDF_Triple.s = (t.RDF_Triple.s);
                    RDF_Triple.p = rdf_type;
                    RDF_Triple.o = (decl.RDF_Triple.o)
                  } in
                add_triple_unchecked acc2 new_t) acc matching
       | uu___ -> acc) g decls
let rdfs_rule_range (g : RDF_Graph.rdf_graph) (ig : indexed_graph) :
  RDF_Graph.rdf_graph=
  let decls = bucket_lookup ig.ig_pred rdfs_range in
  FStar_List_Tot_Base.fold_left
    (fun acc decl ->
       match decl.RDF_Triple.s with
       | RDF_Term.S_IRI p ->
           let matching = bucket_lookup ig.ig_pred p in
           FStar_List_Tot_Base.fold_left
             (fun acc2 t ->
                match term_to_subject t.RDF_Triple.o with
                | FStar_Pervasives_Native.Some b_subj ->
                    let new_t =
                      {
                        RDF_Triple.s = b_subj;
                        RDF_Triple.p = rdf_type;
                        RDF_Triple.o = (decl.RDF_Triple.o)
                      } in
                    add_triple_unchecked acc2 new_t
                | FStar_Pervasives_Native.None -> acc2) acc matching
       | uu___ -> acc) g decls
let rdfs_rule_subClassOf (g : RDF_Graph.rdf_graph) (ig : indexed_graph) :
  RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.fold_left
    (fun acc t ->
       if t.RDF_Triple.p = rdf_type
       then
         match t.RDF_Triple.o with
         | RDF_Term.T_IRI class_iri ->
             let super_classes =
               find_objects_indexed ig (RDF_Term.S_IRI class_iri)
                 rdfs_subClassOf in
             FStar_List_Tot_Base.fold_left
               (fun acc2 b_term ->
                  let new_t =
                    {
                      RDF_Triple.s = (t.RDF_Triple.s);
                      RDF_Triple.p = rdf_type;
                      RDF_Triple.o = b_term
                    } in
                  add_triple_unchecked acc2 new_t) acc super_classes
         | uu___ -> acc
       else acc) g g
let rdfs_rule_subClassOf_trans (g : RDF_Graph.rdf_graph) (ig : indexed_graph)
  : RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.fold_left
    (fun acc t ->
       if t.RDF_Triple.p = rdfs_subClassOf
       then
         match term_to_subject t.RDF_Triple.o with
         | FStar_Pervasives_Native.Some b_subj ->
             let supers = find_objects_indexed ig b_subj rdfs_subClassOf in
             FStar_List_Tot_Base.fold_left
               (fun acc2 c_term ->
                  let new_t =
                    {
                      RDF_Triple.s = (t.RDF_Triple.s);
                      RDF_Triple.p = rdfs_subClassOf;
                      RDF_Triple.o = c_term
                    } in
                  add_triple_unchecked acc2 new_t) acc supers
         | FStar_Pervasives_Native.None -> acc
       else acc) g g
let rdfs_rule_subPropertyOf_trans (g : RDF_Graph.rdf_graph)
  (ig : indexed_graph) : RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.fold_left
    (fun acc t ->
       if t.RDF_Triple.p = rdfs_subPropertyOf
       then
         match term_to_subject t.RDF_Triple.o with
         | FStar_Pervasives_Native.Some q_subj ->
             let supers = find_objects_indexed ig q_subj rdfs_subPropertyOf in
             FStar_List_Tot_Base.fold_left
               (fun acc2 r_term ->
                  let new_t =
                    {
                      RDF_Triple.s = (t.RDF_Triple.s);
                      RDF_Triple.p = rdfs_subPropertyOf;
                      RDF_Triple.o = r_term
                    } in
                  add_triple_unchecked acc2 new_t) acc supers
         | FStar_Pervasives_Native.None -> acc
       else acc) g g
let rdfs_rule_container_membership (g : RDF_Graph.rdf_graph)
  (ig : indexed_graph) : RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.fold_left
    (fun acc cmp ->
       let t1 =
         {
           RDF_Triple.s = (RDF_Term.S_IRI cmp);
           RDF_Triple.p = rdfs_subPropertyOf;
           RDF_Triple.o = (RDF_Term.T_IRI rdfs_member)
         } in
       let t2 =
         {
           RDF_Triple.s = (RDF_Term.S_IRI cmp);
           RDF_Triple.p = rdf_type;
           RDF_Triple.o = (RDF_Term.T_IRI rdfs_ContainerMembershipProperty)
         } in
       add_triple_unchecked (add_triple_unchecked acc t1) t2) g
    container_membership_properties
let rdfs_closure_step (g : RDF_Graph.rdf_graph) : RDF_Graph.rdf_graph=
  let ig = build_indexed g in
  let g1 = rdfs_rule_subPropertyOf g ig in
  let g2 = rdfs_rule_domain g1 ig in
  let g3 = rdfs_rule_range g2 ig in
  let g4 = rdfs_rule_subClassOf g3 ig in
  let g5 = rdfs_rule_container_membership g4 ig in
  let g6 = rdfs_rule_subClassOf_trans g5 ig in
  let g7 = rdfs_rule_subPropertyOf_trans g6 ig in graph_dedup_sort g7
let rec rdfs_closure (g : RDF_Graph.rdf_graph) (fuel : Prims.nat) :
  RDF_Graph.rdf_graph=
  match fuel with
  | uu___ when uu___ = Prims.int_zero -> g
  | n ->
      let g' = rdfs_closure_step g in
      if (graph_len g') = (graph_len g)
      then g
      else rdfs_closure g' (n - Prims.int_one)
let owl_Class : RDF_Term.wf_iri= "http://www.w3.org/2002/07/owl#Class"
let owl_ObjectProperty : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#ObjectProperty"
let owl_DatatypeProperty : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#DatatypeProperty"
let owl_Thing : RDF_Term.wf_iri= "http://www.w3.org/2002/07/owl#Thing"
let owl_Nothing : RDF_Term.wf_iri= "http://www.w3.org/2002/07/owl#Nothing"
let owl_NamedIndividual : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#NamedIndividual"
let cons_if_new_iri (i : RDF_Term.wf_iri) (acc : RDF_Term.wf_iri Prims.list)
  : RDF_Term.wf_iri Prims.list=
  if FStar_List_Tot_Base.mem i acc then acc else i :: acc
let cons_subject_iri_if_new (s : RDF_Term.subject)
  (acc : RDF_Term.wf_iri Prims.list) : RDF_Term.wf_iri Prims.list=
  match s with
  | RDF_Term.S_IRI i -> cons_if_new_iri i acc
  | RDF_Term.S_BNode uu___ -> acc
let cons_term_iri_if_new (t : RDF_Term.rdf_term)
  (acc : RDF_Term.wf_iri Prims.list) : RDF_Term.wf_iri Prims.list=
  match t with | RDF_Term.T_IRI i -> cons_if_new_iri i acc | uu___ -> acc
let is_class_type_object (o : RDF_Term.rdf_term) : Prims.bool=
  match o with
  | RDF_Term.T_IRI c -> (c = rdfs_Class) || (c = owl_Class)
  | uu___ -> false
let is_property_type_object (o : RDF_Term.rdf_term) : Prims.bool=
  match o with
  | RDF_Term.T_IRI c ->
      ((c = rdf_Property) || (c = owl_ObjectProperty)) ||
        (c = owl_DatatypeProperty)
  | uu___ -> false
let collect_classes (g : RDF_Graph.rdf_graph) : RDF_Term.wf_iri Prims.list=
  FStar_List_Tot_Base.fold_left
    (fun acc t ->
       let acc1 =
         if t.RDF_Triple.p = rdfs_subClassOf
         then
           cons_term_iri_if_new t.RDF_Triple.o
             (cons_subject_iri_if_new t.RDF_Triple.s acc)
         else acc in
       if
         (t.RDF_Triple.p = rdf_type) && (is_class_type_object t.RDF_Triple.o)
       then cons_subject_iri_if_new t.RDF_Triple.s acc1
       else acc1) [] g
let collect_properties (g : RDF_Graph.rdf_graph) :
  RDF_Term.wf_iri Prims.list=
  FStar_List_Tot_Base.fold_left
    (fun acc t ->
       let acc1 =
         if t.RDF_Triple.p = rdfs_subPropertyOf
         then
           cons_term_iri_if_new t.RDF_Triple.o
             (cons_subject_iri_if_new t.RDF_Triple.s acc)
         else acc in
       if
         (t.RDF_Triple.p = rdf_type) &&
           (is_property_type_object t.RDF_Triple.o)
       then cons_subject_iri_if_new t.RDF_Triple.s acc1
       else acc1) [] g
let rdfs_reflexivity_axioms (g : RDF_Graph.rdf_graph) : RDF_Graph.rdf_graph=
  let classes = collect_classes g in
  let properties = collect_properties g in
  let class_triples =
    FStar_List_Tot_Base.map
      (fun c ->
         {
           RDF_Triple.s = (RDF_Term.S_IRI c);
           RDF_Triple.p = rdfs_subClassOf;
           RDF_Triple.o = (RDF_Term.T_IRI c)
         }) classes in
  let property_triples =
    FStar_List_Tot_Base.map
      (fun p ->
         {
           RDF_Triple.s = (RDF_Term.S_IRI p);
           RDF_Triple.p = rdfs_subPropertyOf;
           RDF_Triple.o = (RDF_Term.T_IRI p)
         }) properties in
  FStar_List_Tot_Base.op_At class_triples property_triples
let rdfs_closure_with_reflexivity (g : RDF_Graph.rdf_graph)
  (fuel : Prims.nat) : RDF_Graph.rdf_graph=
  let closed = rdfs_closure g fuel in
  let refl_axioms = rdfs_reflexivity_axioms closed in
  let with_refl = add_triples_if_new closed refl_axioms in
  rdfs_closure with_refl fuel
let owl_sameAs : RDF_Term.wf_iri= "http://www.w3.org/2002/07/owl#sameAs"
let owl_SymmetricProperty : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#SymmetricProperty"
let owl_TransitiveProperty : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#TransitiveProperty"
let owl_InverseFunctionalProperty : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#InverseFunctionalProperty"
let owl_FunctionalProperty : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#FunctionalProperty"
let owl_AsymmetricProperty : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#AsymmetricProperty"
let owl_IrreflexiveProperty : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#IrreflexiveProperty"
let owl_inverseOf : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#inverseOf"
let owl_equivalentClass : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#equivalentClass"
let owl_equivalentProperty : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#equivalentProperty"
let owl_differentFrom : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#differentFrom"
let owl_propertyDisjointWith : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#propertyDisjointWith"
let owl_sourceIndividual : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#sourceIndividual"
let owl_assertionProperty : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#assertionProperty"
let owl_targetIndividual : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#targetIndividual"
let owl_targetValue : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#targetValue"
let is_owl_metapredicate (p : RDF_Term.wf_iri) : Prims.bool=
  (((p = owl_sameAs) || (p = owl_inverseOf)) || (p = owl_equivalentClass)) ||
    (p = owl_equivalentProperty)
let owl_rule_equivalent_class (g : RDF_Graph.rdf_graph) (ig : indexed_graph)
  : RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.fold_left
    (fun acc t ->
       if t.RDF_Triple.p = owl_equivalentClass
       then
         match term_to_subject t.RDF_Triple.o with
         | FStar_Pervasives_Native.Some d_subj ->
             let t1 =
               {
                 RDF_Triple.s = (t.RDF_Triple.s);
                 RDF_Triple.p = rdfs_subClassOf;
                 RDF_Triple.o = (subject_to_term d_subj)
               } in
             let t2 =
               {
                 RDF_Triple.s = d_subj;
                 RDF_Triple.p = rdfs_subClassOf;
                 RDF_Triple.o = (subject_to_term t.RDF_Triple.s)
               } in
             (match ((t.RDF_Triple.s), d_subj) with
              | (RDF_Term.S_IRI uu___, RDF_Term.S_IRI uu___1) ->
                  add_triple_unchecked (add_triple_unchecked acc t1) t2
              | (RDF_Term.S_IRI uu___, RDF_Term.S_BNode uu___1) ->
                  add_triple_unchecked acc t1
              | (RDF_Term.S_BNode uu___, RDF_Term.S_IRI uu___1) ->
                  add_triple_unchecked acc t2
              | (RDF_Term.S_BNode uu___, RDF_Term.S_BNode uu___1) -> acc)
         | FStar_Pervasives_Native.None -> acc
       else acc) g g
let owl_rule_equivalent_property (g : RDF_Graph.rdf_graph)
  (ig : indexed_graph) : RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.fold_left
    (fun acc t ->
       if t.RDF_Triple.p = owl_equivalentProperty
       then
         match ((t.RDF_Triple.s), (t.RDF_Triple.o)) with
         | (RDF_Term.S_IRI p_iri, RDF_Term.T_IRI q_iri) ->
             let t1 =
               {
                 RDF_Triple.s = (RDF_Term.S_IRI p_iri);
                 RDF_Triple.p = rdfs_subPropertyOf;
                 RDF_Triple.o = (RDF_Term.T_IRI q_iri)
               } in
             let t2 =
               {
                 RDF_Triple.s = (RDF_Term.S_IRI q_iri);
                 RDF_Triple.p = rdfs_subPropertyOf;
                 RDF_Triple.o = (RDF_Term.T_IRI p_iri)
               } in
             add_triple_unchecked (add_triple_unchecked acc t1) t2
         | (uu___, uu___1) -> acc
       else acc) g g
let owl_rule_scm_eqc2 (g : RDF_Graph.rdf_graph) (ig : indexed_graph) :
  RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.fold_left
    (fun acc t ->
       if t.RDF_Triple.p = rdfs_subClassOf
       then
         match ((t.RDF_Triple.s), (t.RDF_Triple.o)) with
         | (RDF_Term.S_IRI c_iri, RDF_Term.T_IRI d_iri) ->
             (if c_iri = d_iri
              then acc
              else
                (let supers_of_d =
                   find_objects_indexed ig (RDF_Term.S_IRI d_iri)
                     rdfs_subClassOf in
                 if
                   FStar_List_Tot_Base.existsb
                     (fun x -> RDF_Term.rdf_term_eq x (RDF_Term.T_IRI c_iri))
                     supers_of_d
                 then
                   let new_t =
                     {
                       RDF_Triple.s = (RDF_Term.S_IRI c_iri);
                       RDF_Triple.p = owl_equivalentClass;
                       RDF_Triple.o = (RDF_Term.T_IRI d_iri)
                     } in
                   add_triple_unchecked acc new_t
                 else acc))
         | (uu___, uu___1) -> acc
       else acc) g g
let owl_rule_scm_eqp2 (g : RDF_Graph.rdf_graph) (ig : indexed_graph) :
  RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.fold_left
    (fun acc t ->
       if t.RDF_Triple.p = rdfs_subPropertyOf
       then
         match ((t.RDF_Triple.s), (t.RDF_Triple.o)) with
         | (RDF_Term.S_IRI p_iri, RDF_Term.T_IRI q_iri) ->
             (if p_iri = q_iri
              then acc
              else
                (let supers_of_q =
                   find_objects_indexed ig (RDF_Term.S_IRI q_iri)
                     rdfs_subPropertyOf in
                 if
                   FStar_List_Tot_Base.existsb
                     (fun x -> RDF_Term.rdf_term_eq x (RDF_Term.T_IRI p_iri))
                     supers_of_q
                 then
                   let new_t =
                     {
                       RDF_Triple.s = (RDF_Term.S_IRI p_iri);
                       RDF_Triple.p = owl_equivalentProperty;
                       RDF_Triple.o = (RDF_Term.T_IRI q_iri)
                     } in
                   add_triple_unchecked acc new_t
                 else acc))
         | (uu___, uu___1) -> acc
       else acc) g g
let owl_rule_symmetric_property (g : RDF_Graph.rdf_graph)
  (ig : indexed_graph) : RDF_Graph.rdf_graph=
  let sym_props =
    FStar_List_Tot_Base.fold_left
      (fun acc t ->
         if
           (t.RDF_Triple.p = rdf_type) &&
             (RDF_Term.rdf_term_eq t.RDF_Triple.o
                (RDF_Term.T_IRI owl_SymmetricProperty))
         then
           match t.RDF_Triple.s with
           | RDF_Term.S_IRI p_iri -> cons_if_new_iri p_iri acc
           | uu___ -> acc
         else acc) [] g in
  FStar_List_Tot_Base.fold_left
    (fun acc t ->
       if FStar_List_Tot_Base.mem t.RDF_Triple.p sym_props
       then
         match term_to_subject t.RDF_Triple.o with
         | FStar_Pervasives_Native.Some new_subj ->
             let new_t =
               {
                 RDF_Triple.s = new_subj;
                 RDF_Triple.p = (t.RDF_Triple.p);
                 RDF_Triple.o = (subject_to_term t.RDF_Triple.s)
               } in
             add_triple_unchecked acc new_t
         | FStar_Pervasives_Native.None -> acc
       else acc) g g
let owl_rule_transitive_property (g : RDF_Graph.rdf_graph)
  (ig : indexed_graph) : RDF_Graph.rdf_graph=
  let trans_props =
    FStar_List_Tot_Base.fold_left
      (fun acc t ->
         if
           (t.RDF_Triple.p = rdf_type) &&
             (RDF_Term.rdf_term_eq t.RDF_Triple.o
                (RDF_Term.T_IRI owl_TransitiveProperty))
         then
           match t.RDF_Triple.s with
           | RDF_Term.S_IRI p_iri -> cons_if_new_iri p_iri acc
           | uu___ -> acc
         else acc) [] g in
  FStar_List_Tot_Base.fold_left
    (fun acc t ->
       if FStar_List_Tot_Base.mem t.RDF_Triple.p trans_props
       then
         match term_to_subject t.RDF_Triple.o with
         | FStar_Pervasives_Native.Some y_subj ->
             let zs = find_objects_indexed ig y_subj t.RDF_Triple.p in
             FStar_List_Tot_Base.fold_left
               (fun acc2 z_term ->
                  let new_t =
                    {
                      RDF_Triple.s = (t.RDF_Triple.s);
                      RDF_Triple.p = (t.RDF_Triple.p);
                      RDF_Triple.o = z_term
                    } in
                  add_triple_unchecked acc2 new_t) acc zs
         | FStar_Pervasives_Native.None -> acc
       else acc) g g
let owl_rule_inverseOf_domain_range_flip (g : RDF_Graph.rdf_graph)
  (ig : indexed_graph) : RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.fold_left
    (fun acc inv_t ->
       if inv_t.RDF_Triple.p = owl_inverseOf
       then
         match ((inv_t.RDF_Triple.s), (inv_t.RDF_Triple.o)) with
         | (RDF_Term.S_IRI p1, RDF_Term.T_IRI p2) ->
             FStar_List_Tot_Base.fold_left
               (fun acc2 t ->
                  let add_flip target_p target_pred acc3 =
                    match t.RDF_Triple.o with
                    | RDF_Term.T_IRI c ->
                        add_triple_unchecked acc3
                          {
                            RDF_Triple.s = (RDF_Term.S_IRI target_p);
                            RDF_Triple.p = target_pred;
                            RDF_Triple.o = (RDF_Term.T_IRI c)
                          }
                    | uu___ -> acc3 in
                  match t.RDF_Triple.s with
                  | RDF_Term.S_IRI src_p ->
                      if (src_p = p1) && (t.RDF_Triple.p = rdfs_domain)
                      then add_flip p2 rdfs_range acc2
                      else
                        if (src_p = p1) && (t.RDF_Triple.p = rdfs_range)
                        then add_flip p2 rdfs_domain acc2
                        else
                          if (src_p = p2) && (t.RDF_Triple.p = rdfs_domain)
                          then add_flip p1 rdfs_range acc2
                          else
                            if (src_p = p2) && (t.RDF_Triple.p = rdfs_range)
                            then add_flip p1 rdfs_domain acc2
                            else acc2
                  | uu___ -> acc2) acc g
         | (uu___, uu___1) -> acc
       else acc) g g
let owl_rule_inverse_of (g : RDF_Graph.rdf_graph) (ig : indexed_graph) :
  RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.fold_left
    (fun acc inv_t ->
       if inv_t.RDF_Triple.p = owl_inverseOf
       then
         match ((inv_t.RDF_Triple.s), (inv_t.RDF_Triple.o)) with
         | (RDF_Term.S_IRI p1_iri, RDF_Term.T_IRI p2_iri) ->
             FStar_List_Tot_Base.fold_left
               (fun acc2 t ->
                  let add_inverse target_p acc3 =
                    match term_to_subject t.RDF_Triple.o with
                    | FStar_Pervasives_Native.Some new_subj ->
                        let new_t =
                          {
                            RDF_Triple.s = new_subj;
                            RDF_Triple.p = target_p;
                            RDF_Triple.o = (subject_to_term t.RDF_Triple.s)
                          } in
                        add_triple_unchecked acc3 new_t
                    | FStar_Pervasives_Native.None -> acc3 in
                  if t.RDF_Triple.p = p1_iri
                  then add_inverse p2_iri acc2
                  else
                    if t.RDF_Triple.p = p2_iri
                    then add_inverse p1_iri acc2
                    else acc2) acc g
         | (uu___, uu___1) -> acc
       else acc) g g
let collect_iri_or_bnode_terms (g : RDF_Graph.rdf_graph) :
  RDF_Term.subject Prims.list=
  FStar_List_Tot_Base.fold_left
    (fun acc t ->
       let acc1 =
         if
           FStar_List_Tot_Base.existsb
             (fun x -> RDF_Term.subject_eq x t.RDF_Triple.s) acc
         then acc
         else (t.RDF_Triple.s) :: acc in
       match t.RDF_Triple.o with
       | RDF_Term.T_IRI i ->
           let ox = RDF_Term.S_IRI i in
           if
             FStar_List_Tot_Base.existsb (fun x -> RDF_Term.subject_eq x ox)
               acc1
           then acc1
           else ox :: acc1
       | RDF_Term.T_BNode b ->
           let ox = RDF_Term.S_BNode b in
           if
             FStar_List_Tot_Base.existsb (fun x -> RDF_Term.subject_eq x ox)
               acc1
           then acc1
           else ox :: acc1
       | RDF_Term.T_Literal uu___ -> acc1) [] g
let owl_rule_sameAs_reflexivity (g : RDF_Graph.rdf_graph)
  (ig : indexed_graph) : RDF_Graph.rdf_graph=
  let nodes = collect_iri_or_bnode_terms g in
  FStar_List_Tot_Base.fold_left
    (fun acc n ->
       let new_t =
         {
           RDF_Triple.s = n;
           RDF_Triple.p = owl_sameAs;
           RDF_Triple.o = (subject_to_term n)
         } in
       add_triple_unchecked acc new_t) g nodes
let sameas_pair_key (xy : (RDF_Term.subject * RDF_Term.subject)) :
  Prims.string=
  let uu___ = xy in
  match uu___ with
  | (x, y) ->
      FStar_String.concat "" [subject_to_key x; unit_sep; subject_to_key y]
let sameas_pair_cmp (a : (RDF_Term.subject * RDF_Term.subject))
  (b : (RDF_Term.subject * RDF_Term.subject)) : Prims.int=
  FStar_String.compare (sameas_pair_key a) (sameas_pair_key b)
let rec dedup_pairs_sorted_aux
  (prev_key : Prims.string FStar_Pervasives_Native.option)
  (ps : (RDF_Term.subject * RDF_Term.subject) Prims.list)
  (acc : (RDF_Term.subject * RDF_Term.subject) Prims.list) :
  (RDF_Term.subject * RDF_Term.subject) Prims.list=
  match ps with
  | [] -> FStar_List_Tot_Base.rev acc
  | p::rest ->
      let k = sameas_pair_key p in
      let dup =
        match prev_key with
        | FStar_Pervasives_Native.Some q -> q = k
        | FStar_Pervasives_Native.None -> false in
      if dup
      then dedup_pairs_sorted_aux prev_key rest acc
      else
        dedup_pairs_sorted_aux (FStar_Pervasives_Native.Some k) rest (p ::
          acc)
let sameas_pairs (ig : indexed_graph) :
  (RDF_Term.subject * RDF_Term.subject) Prims.list=
  let raw =
    FStar_List_Tot_Base.fold_left
      (fun acc t ->
         if t.RDF_Triple.p = owl_sameAs
         then
           match term_to_subject t.RDF_Triple.o with
           | FStar_Pervasives_Native.Some y ->
               (if RDF_Term.subject_eq t.RDF_Triple.s y
                then acc
                else ((t.RDF_Triple.s), y) :: acc)
           | FStar_Pervasives_Native.None -> acc
         else acc) [] ig.ig_triples in
  let sorted = FStar_List_Tot_Base.sortWith sameas_pair_cmp raw in
  dedup_pairs_sorted_aux FStar_Pervasives_Native.None sorted []
let owl_rule_sameAs_symmetry (g : RDF_Graph.rdf_graph) (ig : indexed_graph) :
  RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.fold_left
    (fun acc xy ->
       let uu___ = xy in
       match uu___ with
       | (x, y) ->
           let new_t =
             {
               RDF_Triple.s = y;
               RDF_Triple.p = owl_sameAs;
               RDF_Triple.o = (subject_to_term x)
             } in
           add_triple_unchecked acc new_t) g (sameas_pairs ig)
let owl_rule_differentFrom_symmetry (g : RDF_Graph.rdf_graph)
  (ig : indexed_graph) : RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.fold_left
    (fun acc t ->
       if t.RDF_Triple.p = owl_differentFrom
       then
         match term_to_subject t.RDF_Triple.o with
         | FStar_Pervasives_Native.Some new_subj ->
             let new_t =
               {
                 RDF_Triple.s = new_subj;
                 RDF_Triple.p = owl_differentFrom;
                 RDF_Triple.o = (subject_to_term t.RDF_Triple.s)
               } in
             add_triple_unchecked acc new_t
         | FStar_Pervasives_Native.None -> acc
       else acc) g g
let owl_rule_sameAs_transitivity (g : RDF_Graph.rdf_graph)
  (ig : indexed_graph) : RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.fold_left
    (fun acc xy ->
       let uu___ = xy in
       match uu___ with
       | (x, y) ->
           let zs = find_objects_indexed ig y owl_sameAs in
           FStar_List_Tot_Base.fold_left
             (fun acc2 z_term ->
                let new_t =
                  {
                    RDF_Triple.s = x;
                    RDF_Triple.p = owl_sameAs;
                    RDF_Triple.o = z_term
                  } in
                add_triple_unchecked acc2 new_t) acc zs) g (sameas_pairs ig)
let owl_rule_sameAs_replace_subject (g : RDF_Graph.rdf_graph)
  (ig : indexed_graph) : RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.fold_left
    (fun acc xy ->
       let uu___ = xy in
       match uu___ with
       | (x, s_prime) ->
           let srcs = bucket_lookup ig.ig_subj (subject_to_key x) in
           FStar_List_Tot_Base.fold_left
             (fun acc2 src ->
                if src.RDF_Triple.p <> owl_sameAs
                then
                  let new_t =
                    {
                      RDF_Triple.s = s_prime;
                      RDF_Triple.p = (src.RDF_Triple.p);
                      RDF_Triple.o = (src.RDF_Triple.o)
                    } in
                  add_triple_unchecked acc2 new_t
                else acc2) acc srcs) g (sameas_pairs ig)
let owl_rule_sameAs_replace_object (g : RDF_Graph.rdf_graph)
  (ig : indexed_graph) : RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.fold_left
    (fun acc xy ->
       let uu___ = xy in
       match uu___ with
       | (x, y) ->
           let y_term = subject_to_term y in
           let srcs = bucket_lookup ig.ig_obj (subject_to_key x) in
           FStar_List_Tot_Base.fold_left
             (fun acc2 src ->
                if src.RDF_Triple.p <> owl_sameAs
                then
                  let new_t =
                    {
                      RDF_Triple.s = (src.RDF_Triple.s);
                      RDF_Triple.p = (src.RDF_Triple.p);
                      RDF_Triple.o = y_term
                    } in
                  add_triple_unchecked acc2 new_t
                else acc2) acc srcs) g (sameas_pairs ig)
let owl_rule_sameAs_replace_predicate (g : RDF_Graph.rdf_graph)
  (ig : indexed_graph) : RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.fold_left
    (fun acc xy ->
       match xy with
       | (RDF_Term.S_IRI p_iri, RDF_Term.S_IRI p_prime_iri) ->
           if is_owl_metapredicate p_iri
           then acc
           else
             (let srcs = bucket_lookup ig.ig_pred p_iri in
              FStar_List_Tot_Base.fold_left
                (fun acc2 src ->
                   let new_t =
                     {
                       RDF_Triple.s = (src.RDF_Triple.s);
                       RDF_Triple.p = p_prime_iri;
                       RDF_Triple.o = (src.RDF_Triple.o)
                     } in
                   add_triple_unchecked acc2 new_t) acc srcs)
       | uu___ -> acc) g (sameas_pairs ig)
let owl_rule_functional (g : RDF_Graph.rdf_graph) (ig : indexed_graph) :
  RDF_Graph.rdf_graph=
  let fp_props =
    FStar_List_Tot_Base.fold_left
      (fun acc t ->
         if
           (t.RDF_Triple.p = rdf_type) &&
             (RDF_Term.rdf_term_eq t.RDF_Triple.o
                (RDF_Term.T_IRI owl_FunctionalProperty))
         then
           match t.RDF_Triple.s with
           | RDF_Term.S_IRI p_iri -> cons_if_new_iri p_iri acc
           | uu___ -> acc
         else acc) [] g in
  FStar_List_Tot_Base.fold_left
    (fun acc t1 ->
       if FStar_List_Tot_Base.mem t1.RDF_Triple.p fp_props
       then
         match term_to_subject t1.RDF_Triple.o with
         | FStar_Pervasives_Native.None -> acc
         | FStar_Pervasives_Native.Some y_subj ->
             let zs = find_objects_indexed ig t1.RDF_Triple.s t1.RDF_Triple.p in
             FStar_List_Tot_Base.fold_left
               (fun acc2 z ->
                  if RDF_Term.rdf_term_eq z t1.RDF_Triple.o
                  then acc2
                  else
                    (let new_t =
                       {
                         RDF_Triple.s = y_subj;
                         RDF_Triple.p = owl_sameAs;
                         RDF_Triple.o = z
                       } in
                     add_triple_unchecked acc2 new_t)) acc zs
       else acc) g g
let owl_rule_inverse_functional (g : RDF_Graph.rdf_graph)
  (ig : indexed_graph) : RDF_Graph.rdf_graph=
  let ifp_props =
    FStar_List_Tot_Base.fold_left
      (fun acc t ->
         if
           (t.RDF_Triple.p = rdf_type) &&
             (RDF_Term.rdf_term_eq t.RDF_Triple.o
                (RDF_Term.T_IRI owl_InverseFunctionalProperty))
         then
           match t.RDF_Triple.s with
           | RDF_Term.S_IRI p_iri -> cons_if_new_iri p_iri acc
           | uu___ -> acc
         else acc) [] g in
  FStar_List_Tot_Base.fold_left
    (fun acc t1 ->
       if FStar_List_Tot_Base.mem t1.RDF_Triple.p ifp_props
       then
         let zs = find_subjects_indexed ig t1.RDF_Triple.p t1.RDF_Triple.o in
         FStar_List_Tot_Base.fold_left
           (fun acc2 z ->
              if RDF_Term.subject_eq z t1.RDF_Triple.s
              then acc2
              else
                (let new_t =
                   {
                     RDF_Triple.s = (t1.RDF_Triple.s);
                     RDF_Triple.p = owl_sameAs;
                     RDF_Triple.o = (subject_to_term z)
                   } in
                 add_triple_unchecked acc2 new_t)) acc zs
       else acc) g g
let differentFrom_in_graph (g : RDF_Graph.rdf_graph) (a : RDF_Term.rdf_term)
  (b : RDF_Term.rdf_term) : Prims.bool=
  FStar_List_Tot_Base.existsb
    (fun t ->
       (t.RDF_Triple.p = owl_differentFrom) &&
         (((RDF_Term.rdf_term_eq (subject_to_term t.RDF_Triple.s) a) &&
             (RDF_Term.rdf_term_eq t.RDF_Triple.o b))
            ||
            ((RDF_Term.rdf_term_eq (subject_to_term t.RDF_Triple.s) b) &&
               (RDF_Term.rdf_term_eq t.RDF_Triple.o a)))) g
let owl_rule_pdw_to_differentFrom (g : RDF_Graph.rdf_graph)
  (ig : indexed_graph) : RDF_Graph.rdf_graph=
  let pdw_pairs =
    FStar_List_Tot_Base.fold_left
      (fun acc t ->
         if t.RDF_Triple.p = owl_propertyDisjointWith
         then
           match ((t.RDF_Triple.s), (t.RDF_Triple.o)) with
           | (RDF_Term.S_IRI p1, RDF_Term.T_IRI p2) -> (p1, p2) :: acc
           | uu___ -> acc
         else acc) [] g in
  FStar_List_Tot_Base.fold_left
    (fun acc pair ->
       let uu___ = pair in
       match uu___ with
       | (p1, p2) ->
           FStar_List_Tot_Base.fold_left
             (fun acc1 t1 ->
                if t1.RDF_Triple.p = p1
                then
                  match term_to_subject t1.RDF_Triple.o with
                  | FStar_Pervasives_Native.None -> acc1
                  | FStar_Pervasives_Native.Some o1_subj ->
                      let o2_terms =
                        find_objects_indexed ig t1.RDF_Triple.s p2 in
                      FStar_List_Tot_Base.fold_left
                        (fun acc2 o2_term ->
                           if RDF_Term.rdf_term_eq t1.RDF_Triple.o o2_term
                           then acc2
                           else
                             (match term_to_subject o2_term with
                              | FStar_Pervasives_Native.None -> acc2
                              | FStar_Pervasives_Native.Some uu___2 ->
                                  let new_t =
                                    {
                                      RDF_Triple.s = o1_subj;
                                      RDF_Triple.p = owl_differentFrom;
                                      RDF_Triple.o = o2_term
                                    } in
                                  add_triple_unchecked acc2 new_t)) acc1
                        o2_terms
                else acc1) acc g) g pdw_pairs
let owl_rule_pdw_shared_value_to_differentFrom (g : RDF_Graph.rdf_graph)
  (ig : indexed_graph) : RDF_Graph.rdf_graph=
  let pdw_pairs =
    FStar_List_Tot_Base.fold_left
      (fun acc t ->
         if t.RDF_Triple.p = owl_propertyDisjointWith
         then
           match ((t.RDF_Triple.s), (t.RDF_Triple.o)) with
           | (RDF_Term.S_IRI p1, RDF_Term.T_IRI p2) -> (p1, p2) :: acc
           | uu___ -> acc
         else acc) [] g in
  FStar_List_Tot_Base.fold_left
    (fun acc pair ->
       let uu___ = pair in
       match uu___ with
       | (p1, p2) ->
           FStar_List_Tot_Base.fold_left
             (fun acc1 t1 ->
                if t1.RDF_Triple.p = p1
                then
                  let ys = find_subjects_indexed ig p2 t1.RDF_Triple.o in
                  FStar_List_Tot_Base.fold_left
                    (fun acc2 y ->
                       if RDF_Term.subject_eq y t1.RDF_Triple.s
                       then acc2
                       else
                         (let new_t =
                            {
                              RDF_Triple.s = (t1.RDF_Triple.s);
                              RDF_Triple.p = owl_differentFrom;
                              RDF_Triple.o = (subject_to_term y)
                            } in
                          add_triple_unchecked acc2 new_t)) acc1 ys
                else acc1) acc g) g pdw_pairs
let owl_rule_fp_diff_to_diff (g : RDF_Graph.rdf_graph) (ig : indexed_graph) :
  RDF_Graph.rdf_graph=
  let fp_props =
    FStar_List_Tot_Base.fold_left
      (fun acc t ->
         if
           (t.RDF_Triple.p = rdf_type) &&
             (RDF_Term.rdf_term_eq t.RDF_Triple.o
                (RDF_Term.T_IRI owl_FunctionalProperty))
         then
           match t.RDF_Triple.s with
           | RDF_Term.S_IRI p_iri -> cons_if_new_iri p_iri acc
           | uu___ -> acc
         else acc) [] g in
  FStar_List_Tot_Base.fold_left
    (fun acc t1 ->
       if FStar_List_Tot_Base.mem t1.RDF_Triple.p fp_props
       then
         FStar_List_Tot_Base.fold_left
           (fun acc2 t2 ->
              if
                ((t2.RDF_Triple.p = t1.RDF_Triple.p) &&
                   (Prims.op_Negation
                      (RDF_Term.subject_eq t2.RDF_Triple.s t1.RDF_Triple.s)))
                  &&
                  (differentFrom_in_graph g t1.RDF_Triple.o t2.RDF_Triple.o)
              then
                let new_t =
                  {
                    RDF_Triple.s = (t1.RDF_Triple.s);
                    RDF_Triple.p = owl_differentFrom;
                    RDF_Triple.o = (subject_to_term t2.RDF_Triple.s)
                  } in
                add_triple_unchecked acc2 new_t
              else acc2) acc g
       else acc) g g
let owl_rule_ifp_diff_to_diff (g : RDF_Graph.rdf_graph) (ig : indexed_graph)
  : RDF_Graph.rdf_graph=
  let ifp_props =
    FStar_List_Tot_Base.fold_left
      (fun acc t ->
         if
           (t.RDF_Triple.p = rdf_type) &&
             (RDF_Term.rdf_term_eq t.RDF_Triple.o
                (RDF_Term.T_IRI owl_InverseFunctionalProperty))
         then
           match t.RDF_Triple.s with
           | RDF_Term.S_IRI p_iri -> cons_if_new_iri p_iri acc
           | uu___ -> acc
         else acc) [] g in
  FStar_List_Tot_Base.fold_left
    (fun acc t1 ->
       if FStar_List_Tot_Base.mem t1.RDF_Triple.p ifp_props
       then
         FStar_List_Tot_Base.fold_left
           (fun acc2 t2 ->
              if
                ((t2.RDF_Triple.p = t1.RDF_Triple.p) &&
                   (Prims.op_Negation
                      (RDF_Term.subject_eq t2.RDF_Triple.s t1.RDF_Triple.s)))
                  &&
                  (differentFrom_in_graph g (subject_to_term t1.RDF_Triple.s)
                     (subject_to_term t2.RDF_Triple.s))
              then
                match term_to_subject t1.RDF_Triple.o with
                | FStar_Pervasives_Native.None -> acc2
                | FStar_Pervasives_Native.Some y1_subj ->
                    let new_t =
                      {
                        RDF_Triple.s = y1_subj;
                        RDF_Triple.p = owl_differentFrom;
                        RDF_Triple.o = (t2.RDF_Triple.o)
                      } in
                    add_triple_unchecked acc2 new_t
              else acc2) acc g
       else acc) g g
let owl_Restriction_iri : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#Restriction"
let owl_onProperty_iri : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#onProperty"
let owl_someValuesFrom_iri : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#someValuesFrom"
let owl_allValuesFrom_iri : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#allValuesFrom"
let owl_minCardinality_iri : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#minCardinality"
let owl_minQualifiedCardinality_iri : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#minQualifiedCardinality"
let owl_maxCardinality_iri : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#maxCardinality"
let owl_maxQualifiedCardinality_iri : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#maxQualifiedCardinality"
let owl_qualifiedCardinality_iri : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#qualifiedCardinality"
let owl_cardinality_iri : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#cardinality"
let owl_onClass_iri : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#onClass"
let owl_hasValue_iri : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#hasValue"
let owl_oneOf_iri : RDF_Term.wf_iri= "http://www.w3.org/2002/07/owl#oneOf"
let owl_intersectionOf_iri : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#intersectionOf"
let owl_unionOf_iri : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#unionOf"
let owl_complementOf_iri : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#complementOf"
let owl_disjointWith_iri : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#disjointWith"
let is_schema_metapredicate (p : RDF_Term.wf_iri) : Prims.bool=
  (((((((((((((((((((((((is_owl_metapredicate p) || (p = rdfs_subClassOf)) ||
                         (p = rdfs_subPropertyOf))
                        || (p = rdfs_domain))
                       || (p = rdfs_range))
                      || (p = owl_onProperty_iri))
                     || (p = owl_onClass_iri))
                    || (p = owl_someValuesFrom_iri))
                   || (p = owl_allValuesFrom_iri))
                  || (p = owl_hasValue_iri))
                 || (p = owl_minCardinality_iri))
                || (p = owl_maxCardinality_iri))
               || (p = owl_cardinality_iri))
              || (p = owl_minQualifiedCardinality_iri))
             || (p = owl_maxQualifiedCardinality_iri))
            || (p = owl_qualifiedCardinality_iri))
           || (p = owl_oneOf_iri))
          || (p = owl_intersectionOf_iri))
         || (p = owl_unionOf_iri))
        || (p = owl_complementOf_iri))
       || (p = owl_disjointWith_iri))
      || (p = "http://www.w3.org/2002/07/owl#propertyChainAxiom"))
     || (p = "http://www.w3.org/2002/07/owl#distinctMembers"))
    || (p = "http://www.w3.org/2002/07/owl#members")
let xsd_nonNegativeInteger : RDF_Term.wf_iri=
  "http://www.w3.org/2001/XMLSchema#nonNegativeInteger"
let one_nonNegInteger_literal : RDF_Term.wf_literal=
  let l =
    {
      RDF_Term.lexical_form = "1";
      RDF_Term.datatype = xsd_nonNegativeInteger;
      RDF_Term.lang_tag = FStar_Pervasives_Native.None
    } in
  l
let canonical_svf_restriction_bnode (p : RDF_Term.wf_iri)
  (c : RDF_Term.wf_iri) : RDF_Term.bnode_id=
  FStar_String.concat "" ["__rl_svf_"; p; "__on__"; c]
let canonical_minqc1_restriction_bnode (p : RDF_Term.wf_iri)
  (c : RDF_Term.wf_iri) : RDF_Term.bnode_id=
  FStar_String.concat "" ["__rl_minqc1_"; p; "__on__"; c]
let canonical_maxqc1_restriction_bnode (p : RDF_Term.wf_iri)
  (c : RDF_Term.wf_iri) : RDF_Term.bnode_id=
  FStar_String.concat "" ["__rl_maxqc1_"; p; "__on__"; c]
let canonical_exactqc1_restriction_bnode (p : RDF_Term.wf_iri)
  (c : RDF_Term.wf_iri) : RDF_Term.bnode_id=
  FStar_String.concat "" ["__rl_exactqc1_"; p; "__on__"; c]
let owl_rule_disjoint_with_propagation (g : RDF_Graph.rdf_graph)
  (ig : indexed_graph) : RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.fold_left
    (fun acc t ->
       if t.RDF_Triple.p = owl_disjointWith_iri
       then
         match ((t.RDF_Triple.s), (t.RDF_Triple.o)) with
         | (RDF_Term.S_IRI c_iri, RDF_Term.T_IRI d_iri) ->
             let new_t =
               {
                 RDF_Triple.s = (RDF_Term.S_IRI d_iri);
                 RDF_Triple.p = owl_disjointWith_iri;
                 RDF_Triple.o = (RDF_Term.T_IRI c_iri)
               } in
             add_triple_unchecked acc new_t
         | (uu___, uu___1) -> acc
       else
         if t.RDF_Triple.p = owl_complementOf_iri
         then
           (match ((t.RDF_Triple.s), (t.RDF_Triple.o)) with
            | (RDF_Term.S_IRI c_iri, RDF_Term.T_IRI d_iri) ->
                let t1 =
                  {
                    RDF_Triple.s = (RDF_Term.S_IRI c_iri);
                    RDF_Triple.p = owl_disjointWith_iri;
                    RDF_Triple.o = (RDF_Term.T_IRI d_iri)
                  } in
                let t2 =
                  {
                    RDF_Triple.s = (RDF_Term.S_IRI d_iri);
                    RDF_Triple.p = owl_disjointWith_iri;
                    RDF_Triple.o = (RDF_Term.T_IRI c_iri)
                  } in
                add_triple_unchecked (add_triple_unchecked acc t1) t2
            | (uu___1, uu___2) -> acc)
         else acc) g g
let canonical_complement_bnode (c : RDF_Term.wf_iri) : RDF_Term.bnode_id=
  FStar_String.concat "" ["__rl_comp__"; c]
let owl_rule_disjoint_to_complement (g : RDF_Graph.rdf_graph)
  (ig : indexed_graph) : RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.fold_left
    (fun acc t ->
       if t.RDF_Triple.p = owl_disjointWith_iri
       then
         match ((t.RDF_Triple.s), (t.RDF_Triple.o)) with
         | (RDF_Term.S_IRI c1, RDF_Term.T_IRI c2) ->
             (if (c2 = owl_Thing) || (c2 = owl_Nothing)
              then acc
              else
                (let cb = RDF_Term.S_BNode (canonical_complement_bnode c2) in
                 let shape1 =
                   {
                     RDF_Triple.s = cb;
                     RDF_Triple.p = owl_complementOf_iri;
                     RDF_Triple.o = (RDF_Term.T_IRI c2)
                   } in
                 let shape2 =
                   {
                     RDF_Triple.s = cb;
                     RDF_Triple.p = rdf_type;
                     RDF_Triple.o = (RDF_Term.T_IRI owl_Class)
                   } in
                 let acc1 =
                   add_triple_unchecked (add_triple_unchecked acc shape1)
                     shape2 in
                 let members =
                   find_subjects_indexed ig rdf_type (RDF_Term.T_IRI c1) in
                 FStar_List_Tot_Base.fold_left
                   (fun acc2 x ->
                      let memb =
                        {
                          RDF_Triple.s = x;
                          RDF_Triple.p = rdf_type;
                          RDF_Triple.o =
                            (RDF_Term.T_BNode (canonical_complement_bnode c2))
                        } in
                      add_triple_unchecked acc2 memb) acc1 members))
         | (uu___, uu___1) -> acc
       else acc) g g
let canonical_svf2_witness_bnode (p : RDF_Term.wf_iri) (c : RDF_Term.wf_iri)
  (x : RDF_Term.subject) : RDF_Term.bnode_id=
  FStar_String.concat ""
    ["__rl_svf2w__on__"; p; "__filler__"; c; "__from__"; subject_to_key x]
let owl_rule_svf2_existential_witness (g : RDF_Graph.rdf_graph)
  (ig : indexed_graph) : RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.fold_left
    (fun acc svf_t ->
       if svf_t.RDF_Triple.p = owl_someValuesFrom_iri
       then
         match svf_t.RDF_Triple.o with
         | RDF_Term.T_IRI c ->
             (if c = owl_Thing
              then acc
              else
                (let r_subj = svf_t.RDF_Triple.s in
                 let onprops =
                   find_objects_indexed ig r_subj owl_onProperty_iri in
                 FStar_List_Tot_Base.fold_left
                   (fun acc2 op_term ->
                      match op_term with
                      | RDF_Term.T_IRI p ->
                          let r_term = subject_to_term r_subj in
                          let ancestors =
                            find_subjects_indexed ig rdfs_subClassOf r_term in
                          FStar_List_Tot_Base.fold_left
                            (fun acc3 cls_subj ->
                               match cls_subj with
                               | RDF_Term.S_IRI cls_iri ->
                                   let members =
                                     find_subjects_indexed ig rdf_type
                                       (RDF_Term.T_IRI cls_iri) in
                                   FStar_List_Tot_Base.fold_left
                                     (fun acc4 x ->
                                        let w_id =
                                          canonical_svf2_witness_bnode p c x in
                                        let edge_t =
                                          {
                                            RDF_Triple.s = x;
                                            RDF_Triple.p = p;
                                            RDF_Triple.o =
                                              (RDF_Term.T_BNode w_id)
                                          } in
                                        let type_t =
                                          {
                                            RDF_Triple.s =
                                              (RDF_Term.S_BNode w_id);
                                            RDF_Triple.p = rdf_type;
                                            RDF_Triple.o = (RDF_Term.T_IRI c)
                                          } in
                                        add_triple_unchecked
                                          (add_triple_unchecked acc4 edge_t)
                                          type_t) acc3 members
                               | uu___1 -> acc3) acc2 ancestors
                      | uu___1 -> acc2) acc onprops))
         | uu___ -> acc
       else acc) g g
let owl_rule_minc1_bridge (g : RDF_Graph.rdf_graph) (ig : indexed_graph) :
  RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.fold_left
    (fun acc t ->
       if
         (t.RDF_Triple.p = owl_someValuesFrom_iri) &&
           (RDF_Term.rdf_term_eq t.RDF_Triple.o (RDF_Term.T_IRI owl_Thing))
       then
         let onprops =
           find_objects_indexed ig t.RDF_Triple.s owl_onProperty_iri in
         FStar_List_Tot_Base.fold_left
           (fun acc2 op_term ->
              match op_term with
              | RDF_Term.T_IRI uu___ ->
                  let new_t =
                    {
                      RDF_Triple.s = (t.RDF_Triple.s);
                      RDF_Triple.p = owl_minCardinality_iri;
                      RDF_Triple.o =
                        (RDF_Term.T_Literal one_nonNegInteger_literal)
                    } in
                  add_triple_unchecked acc2 new_t
              | uu___ -> acc2) acc onprops
       else acc) g g
let owl_rule_cls_hv1 (g : RDF_Graph.rdf_graph) (ig : indexed_graph) :
  RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.fold_left
    (fun acc hv_t ->
       if hv_t.RDF_Triple.p = owl_hasValue_iri
       then
         let r_subj = hv_t.RDF_Triple.s in
         let v = hv_t.RDF_Triple.o in
         let onprops = find_objects_indexed ig r_subj owl_onProperty_iri in
         FStar_List_Tot_Base.fold_left
           (fun acc2 op_term ->
              match op_term with
              | RDF_Term.T_IRI p ->
                  let members =
                    find_subjects_indexed ig rdf_type
                      (subject_to_term r_subj) in
                  FStar_List_Tot_Base.fold_left
                    (fun acc3 x ->
                       add_triple_unchecked acc3
                         {
                           RDF_Triple.s = x;
                           RDF_Triple.p = p;
                           RDF_Triple.o = v
                         }) acc2 members
              | uu___ -> acc2) acc onprops
       else acc) g g
let owl_rule_cls_hv2 (g : RDF_Graph.rdf_graph) (ig : indexed_graph) :
  RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.fold_left
    (fun acc hv_t ->
       if hv_t.RDF_Triple.p = owl_hasValue_iri
       then
         let r_subj = hv_t.RDF_Triple.s in
         let v = hv_t.RDF_Triple.o in
         let onprops = find_objects_indexed ig r_subj owl_onProperty_iri in
         FStar_List_Tot_Base.fold_left
           (fun acc2 op_term ->
              match op_term with
              | RDF_Term.T_IRI p ->
                  let holders = find_subjects_indexed ig p v in
                  FStar_List_Tot_Base.fold_left
                    (fun acc3 x ->
                       add_triple_unchecked acc3
                         {
                           RDF_Triple.s = x;
                           RDF_Triple.p = rdf_type;
                           RDF_Triple.o = (subject_to_term r_subj)
                         }) acc2 holders
              | uu___ -> acc2) acc onprops
       else acc) g g
let rl_canonical_bnode_prefix : Prims.string= "__rl_"
let bnode_is_rl_canonical (b : RDF_Term.bnode_id) : Prims.bool=
  let plen = FStar_String.strlen rl_canonical_bnode_prefix in
  let blen = FStar_String.strlen b in
  if blen < plen
  then false
  else (FStar_String.sub b Prims.int_zero plen) = rl_canonical_bnode_prefix
let is_owl_or_rdfs_metaclass (i : RDF_Term.wf_iri) : Prims.bool=
  ((((((((((((((((((((((((i = owl_Class) || (i = owl_Restriction_iri)) ||
                          (i = owl_NamedIndividual))
                         || (i = owl_Thing))
                        || (i = owl_Nothing))
                       || (i = owl_FunctionalProperty))
                      || (i = owl_InverseFunctionalProperty))
                     || (i = owl_TransitiveProperty))
                    || (i = owl_SymmetricProperty))
                   ||
                   (i = "http://www.w3.org/2002/07/owl#AsymmetricProperty"))
                  || (i = "http://www.w3.org/2002/07/owl#ReflexiveProperty"))
                 || (i = "http://www.w3.org/2002/07/owl#IrreflexiveProperty"))
                || (i = owl_ObjectProperty))
               || (i = owl_DatatypeProperty))
              || (i = "http://www.w3.org/2002/07/owl#AnnotationProperty"))
             || (i = "http://www.w3.org/2002/07/owl#OntologyProperty"))
            || (i = "http://www.w3.org/2002/07/owl#Ontology"))
           || (i = rdfs_Class))
          || (i = rdfs_Resource))
         || (i = rdfs_Datatype))
        || (i = rdfs_Literal))
       || (i = "http://www.w3.org/1999/02/22-rdf-syntax-ns#Property"))
      || (i = "http://www.w3.org/1999/02/22-rdf-syntax-ns#List"))
     || (i = "http://www.w3.org/1999/02/22-rdf-syntax-ns#Statement"))
    ||
    (let xsd_prefix = "http://www.w3.org/2001/XMLSchema#" in
     let plen = FStar_String.strlen xsd_prefix in
     let ilen = FStar_String.strlen i in
     if ilen < plen
     then false
     else (FStar_String.sub i Prims.int_zero plen) = xsd_prefix)
let edge_subject_is_safe (e : RDF_Triple.triple) : Prims.bool=
  match e.RDF_Triple.s with
  | RDF_Term.S_IRI i ->
      (Prims.op_Negation (is_schema_metapredicate i)) &&
        (Prims.op_Negation (is_owl_or_rdfs_metaclass i))
  | RDF_Term.S_BNode b -> Prims.op_Negation (bnode_is_rl_canonical b)
let owl_rule_cls_svf2_qualified (g : RDF_Graph.rdf_graph)
  (ig : indexed_graph) : RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.fold_left
    (fun acc edge ->
       if
         (edge.RDF_Triple.p = rdf_type) ||
           (is_schema_metapredicate edge.RDF_Triple.p)
       then acc
       else
         if Prims.op_Negation (edge_subject_is_safe edge)
         then acc
         else
           (match term_to_subject edge.RDF_Triple.o with
            | FStar_Pervasives_Native.None -> acc
            | FStar_Pervasives_Native.Some y_subj ->
                let p = edge.RDF_Triple.p in
                let x = edge.RDF_Triple.s in
                let ytypes = find_objects_indexed ig y_subj rdf_type in
                FStar_List_Tot_Base.fold_left
                  (fun acc2 ty ->
                     match ty with
                     | RDF_Term.T_IRI c ->
                         if c = owl_Thing
                         then acc2
                         else
                           (let rb = canonical_svf_restriction_bnode p c in
                            let rb_subj = RDF_Term.S_BNode rb in
                            let rb_term = RDF_Term.T_BNode rb in
                            let shape1 =
                              {
                                RDF_Triple.s = rb_subj;
                                RDF_Triple.p = rdf_type;
                                RDF_Triple.o =
                                  (RDF_Term.T_IRI owl_Restriction_iri)
                              } in
                            let shape2 =
                              {
                                RDF_Triple.s = rb_subj;
                                RDF_Triple.p = owl_onProperty_iri;
                                RDF_Triple.o = (RDF_Term.T_IRI p)
                              } in
                            let shape3 =
                              {
                                RDF_Triple.s = rb_subj;
                                RDF_Triple.p = owl_someValuesFrom_iri;
                                RDF_Triple.o = (RDF_Term.T_IRI c)
                              } in
                            let memb =
                              {
                                RDF_Triple.s = x;
                                RDF_Triple.p = rdf_type;
                                RDF_Triple.o = rb_term
                              } in
                            add_triple_unchecked
                              (add_triple_unchecked
                                 (add_triple_unchecked
                                    (add_triple_unchecked acc2 shape1) shape2)
                                 shape3) memb)
                     | uu___2 -> acc2) acc ytypes)) g g
let owl_rule_cls_minc_qual1 (g : RDF_Graph.rdf_graph) (ig : indexed_graph) :
  RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.fold_left
    (fun acc edge ->
       if
         (edge.RDF_Triple.p = rdf_type) ||
           (is_schema_metapredicate edge.RDF_Triple.p)
       then acc
       else
         if Prims.op_Negation (edge_subject_is_safe edge)
         then acc
         else
           (match term_to_subject edge.RDF_Triple.o with
            | FStar_Pervasives_Native.None -> acc
            | FStar_Pervasives_Native.Some y_subj ->
                let p = edge.RDF_Triple.p in
                let x = edge.RDF_Triple.s in
                let ytypes = find_objects_indexed ig y_subj rdf_type in
                FStar_List_Tot_Base.fold_left
                  (fun acc2 ty ->
                     match ty with
                     | RDF_Term.T_IRI c ->
                         if c = owl_Thing
                         then acc2
                         else
                           (let rb = canonical_minqc1_restriction_bnode p c in
                            let rb_subj = RDF_Term.S_BNode rb in
                            let rb_term = RDF_Term.T_BNode rb in
                            let shape1 =
                              {
                                RDF_Triple.s = rb_subj;
                                RDF_Triple.p = rdf_type;
                                RDF_Triple.o =
                                  (RDF_Term.T_IRI owl_Restriction_iri)
                              } in
                            let shape2 =
                              {
                                RDF_Triple.s = rb_subj;
                                RDF_Triple.p = owl_onProperty_iri;
                                RDF_Triple.o = (RDF_Term.T_IRI p)
                              } in
                            let shape3 =
                              {
                                RDF_Triple.s = rb_subj;
                                RDF_Triple.p =
                                  owl_minQualifiedCardinality_iri;
                                RDF_Triple.o =
                                  (RDF_Term.T_Literal
                                     one_nonNegInteger_literal)
                              } in
                            let shape4 =
                              {
                                RDF_Triple.s = rb_subj;
                                RDF_Triple.p = owl_onClass_iri;
                                RDF_Triple.o = (RDF_Term.T_IRI c)
                              } in
                            let memb =
                              {
                                RDF_Triple.s = x;
                                RDF_Triple.p = rdf_type;
                                RDF_Triple.o = rb_term
                              } in
                            add_triple_unchecked
                              (add_triple_unchecked
                                 (add_triple_unchecked
                                    (add_triple_unchecked
                                       (add_triple_unchecked acc2 shape1)
                                       shape2) shape3) shape4) memb)
                     | uu___2 -> acc2) acc ytypes)) g g
let count_p_successors_typed_c (g : RDF_Graph.rdf_graph) (ig : indexed_graph)
  (x : RDF_Term.subject) (p : RDF_Term.wf_iri) (c : RDF_Term.wf_iri) :
  Prims.nat=
  let succs = find_objects_indexed ig x p in
  let typed =
    FStar_List_Tot_Base.filter
      (fun y ->
         match term_to_subject y with
         | FStar_Pervasives_Native.None -> false
         | FStar_Pervasives_Native.Some y_subj ->
             let ts = find_objects_indexed ig y_subj rdf_type in
             FStar_List_Tot_Base.existsb
               (fun t -> RDF_Term.rdf_term_eq t (RDF_Term.T_IRI c)) ts) succs in
  FStar_List_Tot_Base.length typed
let owl_rule_cls_maxqc1 (g : RDF_Graph.rdf_graph) (ig : indexed_graph) :
  RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.fold_left
    (fun acc edge ->
       if
         (edge.RDF_Triple.p = rdf_type) ||
           (is_schema_metapredicate edge.RDF_Triple.p)
       then acc
       else
         if Prims.op_Negation (edge_subject_is_safe edge)
         then acc
         else
           (match term_to_subject edge.RDF_Triple.o with
            | FStar_Pervasives_Native.None -> acc
            | FStar_Pervasives_Native.Some y_subj ->
                let p = edge.RDF_Triple.p in
                let x = edge.RDF_Triple.s in
                let ytypes = find_objects_indexed ig y_subj rdf_type in
                FStar_List_Tot_Base.fold_left
                  (fun acc2 ty ->
                     match ty with
                     | RDF_Term.T_IRI c ->
                         if c = owl_Thing
                         then acc2
                         else
                           (let n = count_p_successors_typed_c g ig x p c in
                            if n > Prims.int_one
                            then acc2
                            else
                              (let rb =
                                 canonical_maxqc1_restriction_bnode p c in
                               let rb_subj = RDF_Term.S_BNode rb in
                               let rb_term = RDF_Term.T_BNode rb in
                               let shape1 =
                                 {
                                   RDF_Triple.s = rb_subj;
                                   RDF_Triple.p = rdf_type;
                                   RDF_Triple.o =
                                     (RDF_Term.T_IRI owl_Restriction_iri)
                                 } in
                               let shape2 =
                                 {
                                   RDF_Triple.s = rb_subj;
                                   RDF_Triple.p = owl_onProperty_iri;
                                   RDF_Triple.o = (RDF_Term.T_IRI p)
                                 } in
                               let shape3 =
                                 {
                                   RDF_Triple.s = rb_subj;
                                   RDF_Triple.p =
                                     owl_maxQualifiedCardinality_iri;
                                   RDF_Triple.o =
                                     (RDF_Term.T_Literal
                                        one_nonNegInteger_literal)
                                 } in
                               let shape4 =
                                 {
                                   RDF_Triple.s = rb_subj;
                                   RDF_Triple.p = owl_onClass_iri;
                                   RDF_Triple.o = (RDF_Term.T_IRI c)
                                 } in
                               let memb =
                                 {
                                   RDF_Triple.s = x;
                                   RDF_Triple.p = rdf_type;
                                   RDF_Triple.o = rb_term
                                 } in
                               add_triple_unchecked
                                 (add_triple_unchecked
                                    (add_triple_unchecked
                                       (add_triple_unchecked
                                          (add_triple_unchecked acc2 shape1)
                                          shape2) shape3) shape4) memb))
                     | uu___2 -> acc2) acc ytypes)) g g
let owl_rule_cls_exactqc1 (g : RDF_Graph.rdf_graph) (ig : indexed_graph) :
  RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.fold_left
    (fun acc edge ->
       if
         (edge.RDF_Triple.p = rdf_type) ||
           (is_schema_metapredicate edge.RDF_Triple.p)
       then acc
       else
         if Prims.op_Negation (edge_subject_is_safe edge)
         then acc
         else
           (match term_to_subject edge.RDF_Triple.o with
            | FStar_Pervasives_Native.None -> acc
            | FStar_Pervasives_Native.Some y_subj ->
                let p = edge.RDF_Triple.p in
                let x = edge.RDF_Triple.s in
                let ytypes = find_objects_indexed ig y_subj rdf_type in
                FStar_List_Tot_Base.fold_left
                  (fun acc2 ty ->
                     match ty with
                     | RDF_Term.T_IRI c ->
                         if c = owl_Thing
                         then acc2
                         else
                           (let rb = canonical_exactqc1_restriction_bnode p c in
                            let rb_subj = RDF_Term.S_BNode rb in
                            let rb_term = RDF_Term.T_BNode rb in
                            let shape1 =
                              {
                                RDF_Triple.s = rb_subj;
                                RDF_Triple.p = rdf_type;
                                RDF_Triple.o =
                                  (RDF_Term.T_IRI owl_Restriction_iri)
                              } in
                            let shape2 =
                              {
                                RDF_Triple.s = rb_subj;
                                RDF_Triple.p = owl_onProperty_iri;
                                RDF_Triple.o = (RDF_Term.T_IRI p)
                              } in
                            let shape3 =
                              {
                                RDF_Triple.s = rb_subj;
                                RDF_Triple.p = owl_qualifiedCardinality_iri;
                                RDF_Triple.o =
                                  (RDF_Term.T_Literal
                                     one_nonNegInteger_literal)
                              } in
                            let shape4 =
                              {
                                RDF_Triple.s = rb_subj;
                                RDF_Triple.p = owl_onClass_iri;
                                RDF_Triple.o = (RDF_Term.T_IRI c)
                              } in
                            let memb =
                              {
                                RDF_Triple.s = x;
                                RDF_Triple.p = rdf_type;
                                RDF_Triple.o = rb_term
                              } in
                            add_triple_unchecked
                              (add_triple_unchecked
                                 (add_triple_unchecked
                                    (add_triple_unchecked
                                       (add_triple_unchecked acc2 shape1)
                                       shape2) shape3) shape4) memb)
                     | uu___2 -> acc2) acc ytypes)) g g
let owl_rule_cls_maxc2 (g : RDF_Graph.rdf_graph) (ig : indexed_graph) :
  RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.fold_left
    (fun acc t ->
       if
         (t.RDF_Triple.p = owl_maxCardinality_iri) &&
           (RDF_Term.rdf_term_eq t.RDF_Triple.o
              (RDF_Term.T_Literal one_nonNegInteger_literal))
       then
         let r_subj = t.RDF_Triple.s in
         let props = find_objects_indexed ig r_subj owl_onProperty_iri in
         FStar_List_Tot_Base.fold_left
           (fun acc2 p_term ->
              match p_term with
              | RDF_Term.T_IRI p ->
                  let members =
                    find_subjects_indexed ig rdf_type
                      (subject_to_term r_subj) in
                  FStar_List_Tot_Base.fold_left
                    (fun acc3 x ->
                       let ys = find_objects_indexed ig x p in
                       FStar_List_Tot_Base.fold_left
                         (fun acc4 y1 ->
                            FStar_List_Tot_Base.fold_left
                              (fun acc5 y2 ->
                                 if RDF_Term.rdf_term_eq y1 y2
                                 then acc5
                                 else
                                   (match term_to_subject y1 with
                                    | FStar_Pervasives_Native.None -> acc5
                                    | FStar_Pervasives_Native.Some y1_subj ->
                                        let new_t =
                                          {
                                            RDF_Triple.s = y1_subj;
                                            RDF_Triple.p = owl_sameAs;
                                            RDF_Triple.o = y2
                                          } in
                                        add_triple_unchecked acc5 new_t))
                              acc4 ys) acc3 ys) acc2 members
              | uu___ -> acc2) acc props
       else acc) g g
let object_has_type (ig : indexed_graph) (y : RDF_Term.rdf_term)
  (c : RDF_Term.wf_iri) : Prims.bool=
  match term_to_subject y with
  | FStar_Pervasives_Native.None -> false
  | FStar_Pervasives_Native.Some y_subj ->
      let ts = find_objects_indexed ig y_subj rdf_type in
      FStar_List_Tot_Base.existsb
        (fun ty -> RDF_Term.rdf_term_eq ty (RDF_Term.T_IRI c)) ts
let owl_rule_cls_maxqc_comp (g : RDF_Graph.rdf_graph) (ig : indexed_graph) :
  RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.fold_left
    (fun acc t ->
       if
         (t.RDF_Triple.p = owl_maxQualifiedCardinality_iri) &&
           (RDF_Term.rdf_term_eq t.RDF_Triple.o
              (RDF_Term.T_Literal one_nonNegInteger_literal))
       then
         let r_subj = t.RDF_Triple.s in
         let props = find_objects_indexed ig r_subj owl_onProperty_iri in
         let classes = find_objects_indexed ig r_subj owl_onClass_iri in
         FStar_List_Tot_Base.fold_left
           (fun acc2 p_term ->
              match p_term with
              | RDF_Term.T_IRI p ->
                  FStar_List_Tot_Base.fold_left
                    (fun acc3 c_term ->
                       match c_term with
                       | RDF_Term.T_IRI c ->
                           if (c = owl_Thing) || (c = owl_Nothing)
                           then acc3
                           else
                             (let members =
                                find_subjects_indexed ig rdf_type
                                  (subject_to_term r_subj) in
                              FStar_List_Tot_Base.fold_left
                                (fun acc4 x ->
                                   let ys = find_objects_indexed ig x p in
                                   FStar_List_Tot_Base.fold_left
                                     (fun acc5 y1 ->
                                        if object_has_type ig y1 c
                                        then
                                          FStar_List_Tot_Base.fold_left
                                            (fun acc6 y2 ->
                                               if RDF_Term.rdf_term_eq y1 y2
                                               then acc6
                                               else
                                                 if
                                                   Prims.op_Negation
                                                     (differentFrom_in_graph
                                                        g y1 y2)
                                                 then acc6
                                                 else
                                                   (match term_to_subject y2
                                                    with
                                                    | FStar_Pervasives_Native.None
                                                        -> acc6
                                                    | FStar_Pervasives_Native.Some
                                                        y2_subj ->
                                                        let cb =
                                                          RDF_Term.S_BNode
                                                            (canonical_complement_bnode
                                                               c) in
                                                        let shape1 =
                                                          {
                                                            RDF_Triple.s = cb;
                                                            RDF_Triple.p =
                                                              owl_complementOf_iri;
                                                            RDF_Triple.o =
                                                              (RDF_Term.T_IRI
                                                                 c)
                                                          } in
                                                        let shape2 =
                                                          {
                                                            RDF_Triple.s = cb;
                                                            RDF_Triple.p =
                                                              rdf_type;
                                                            RDF_Triple.o =
                                                              (RDF_Term.T_IRI
                                                                 owl_Class)
                                                          } in
                                                        let memb =
                                                          {
                                                            RDF_Triple.s =
                                                              y2_subj;
                                                            RDF_Triple.p =
                                                              rdf_type;
                                                            RDF_Triple.o =
                                                              (RDF_Term.T_BNode
                                                                 (canonical_complement_bnode
                                                                    c))
                                                          } in
                                                        add_triple_unchecked
                                                          (add_triple_unchecked
                                                             (add_triple_unchecked
                                                                acc6 shape1)
                                                             shape2) memb))
                                            acc5 ys
                                        else acc5) acc4 ys) acc3 members)
                       | uu___ -> acc3) acc2 classes
              | uu___ -> acc2) acc props
       else acc) g g
let owl_rule_cls_avf1 (g : RDF_Graph.rdf_graph) (ig : indexed_graph) :
  RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.fold_left
    (fun acc t_avf ->
       if t_avf.RDF_Triple.p = owl_allValuesFrom_iri
       then
         match t_avf.RDF_Triple.o with
         | RDF_Term.T_IRI d ->
             let r_subj = t_avf.RDF_Triple.s in
             let props = find_objects_indexed ig r_subj owl_onProperty_iri in
             FStar_List_Tot_Base.fold_left
               (fun acc2 p_term ->
                  match p_term with
                  | RDF_Term.T_IRI p ->
                      let members =
                        find_subjects_indexed ig rdf_type
                          (subject_to_term r_subj) in
                      FStar_List_Tot_Base.fold_left
                        (fun acc3 x ->
                           let ys = find_objects_indexed ig x p in
                           FStar_List_Tot_Base.fold_left
                             (fun acc4 y ->
                                match term_to_subject y with
                                | FStar_Pervasives_Native.None -> acc4
                                | FStar_Pervasives_Native.Some y_subj ->
                                    let new_t =
                                      {
                                        RDF_Triple.s = y_subj;
                                        RDF_Triple.p = rdf_type;
                                        RDF_Triple.o = (RDF_Term.T_IRI d)
                                      } in
                                    add_triple_unchecked acc4 new_t) acc3 ys)
                        acc2 members
                  | uu___ -> acc2) acc props
         | uu___ -> acc
       else acc) g g
let owl_ReflexiveProperty : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#ReflexiveProperty"
let prp_rfl_individuals (g : RDF_Graph.rdf_graph) :
  RDF_Term.wf_iri Prims.list=
  FStar_List_Tot_Base.fold_left
    (fun acc t ->
       let acc1 = cons_subject_iri_if_new t.RDF_Triple.s acc in
       cons_term_iri_if_new t.RDF_Triple.o acc1) [] g
let owl_rule_reflexive_property (g : RDF_Graph.rdf_graph)
  (ig : indexed_graph) : RDF_Graph.rdf_graph=
  let refl_props =
    FStar_List_Tot_Base.fold_left
      (fun acc t ->
         if
           (t.RDF_Triple.p = rdf_type) &&
             (RDF_Term.rdf_term_eq t.RDF_Triple.o
                (RDF_Term.T_IRI owl_ReflexiveProperty))
         then
           match t.RDF_Triple.s with
           | RDF_Term.S_IRI p_iri -> cons_if_new_iri p_iri acc
           | uu___ -> acc
         else acc) [] g in
  match refl_props with
  | [] -> g
  | uu___ ->
      let indivs = prp_rfl_individuals g in
      FStar_List_Tot_Base.fold_left
        (fun acc p_iri ->
           FStar_List_Tot_Base.fold_left
             (fun acc2 x ->
                let new_t =
                  {
                    RDF_Triple.s = (RDF_Term.S_IRI x);
                    RDF_Triple.p = p_iri;
                    RDF_Triple.o = (RDF_Term.T_IRI x)
                  } in
                add_triple_unchecked acc2 new_t) acc indivs) g refl_props
let owl_rule_scm_cls_restriction (g : RDF_Graph.rdf_graph)
  (ig : indexed_graph) : RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.fold_left
    (fun acc t ->
       if
         (t.RDF_Triple.p = rdf_type) &&
           (RDF_Term.rdf_term_eq t.RDF_Triple.o
              (RDF_Term.T_IRI owl_Restriction_iri))
       then
         let new_t =
           {
             RDF_Triple.s = (t.RDF_Triple.s);
             RDF_Triple.p = rdf_type;
             RDF_Triple.o = (RDF_Term.T_IRI owl_Class)
           } in
         add_triple_unchecked acc new_t
       else acc) g g
let rdf_first : RDF_Term.wf_iri=
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#first"
let rdf_rest : RDF_Term.wf_iri=
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#rest"
let rdf_nil_iri : RDF_Term.wf_iri=
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#nil"
let owl_propertyChainAxiom : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#propertyChainAxiom"
let owl_hasKey : RDF_Term.wf_iri= "http://www.w3.org/2002/07/owl#hasKey"
let decode_chain_pair (g : RDF_Graph.rdf_graph) (ig : indexed_graph)
  (head_subj : RDF_Term.subject) :
  (RDF_Term.wf_iri * RDF_Term.wf_iri) FStar_Pervasives_Native.option=
  let firsts1 = find_objects_indexed ig head_subj rdf_first in
  let rests1 = find_objects_indexed ig head_subj rdf_rest in
  match (firsts1, rests1) with
  | ((RDF_Term.T_IRI p1)::uu___, tail_term::uu___1) ->
      (match term_to_subject tail_term with
       | FStar_Pervasives_Native.Some tail_subj ->
           let firsts2 = find_objects_indexed ig tail_subj rdf_first in
           let rests2 = find_objects_indexed ig tail_subj rdf_rest in
           (match (firsts2, rests2) with
            | ((RDF_Term.T_IRI p2)::uu___2, (RDF_Term.T_IRI nil_iri)::uu___3)
                ->
                if nil_iri = rdf_nil_iri
                then FStar_Pervasives_Native.Some (p1, p2)
                else FStar_Pervasives_Native.None
            | (uu___2, uu___3) -> FStar_Pervasives_Native.None)
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
  | (uu___, uu___1) -> FStar_Pervasives_Native.None
let owl_rule_property_chain_2 (g : RDF_Graph.rdf_graph) (ig : indexed_graph)
  : RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.fold_left
    (fun acc chain_t ->
       if chain_t.RDF_Triple.p = owl_propertyChainAxiom
       then
         match ((chain_t.RDF_Triple.s),
                 (term_to_subject chain_t.RDF_Triple.o))
         with
         | (RDF_Term.S_IRI p_iri, FStar_Pervasives_Native.Some list_subj) ->
             (match decode_chain_pair g ig list_subj with
              | FStar_Pervasives_Native.Some (p1, p2) ->
                  FStar_List_Tot_Base.fold_left
                    (fun acc2 t1 ->
                       if t1.RDF_Triple.p = p1
                       then
                         match term_to_subject t1.RDF_Triple.o with
                         | FStar_Pervasives_Native.Some y_subj ->
                             let zs = find_objects_indexed ig y_subj p2 in
                             FStar_List_Tot_Base.fold_left
                               (fun acc3 z_term ->
                                  let new_t =
                                    {
                                      RDF_Triple.s = (t1.RDF_Triple.s);
                                      RDF_Triple.p = p_iri;
                                      RDF_Triple.o = z_term
                                    } in
                                  add_triple_unchecked acc3 new_t) acc2 zs
                         | FStar_Pervasives_Native.None -> acc2
                       else acc2) acc g
              | FStar_Pervasives_Native.None -> acc)
         | (uu___, uu___1) -> acc
       else acc) g g
let rec decode_chain_list_fuel (g : RDF_Graph.rdf_graph) (ig : indexed_graph)
  (head_subj : RDF_Term.subject) (fuel : Prims.nat) :
  RDF_Term.wf_iri Prims.list FStar_Pervasives_Native.option=
  let is_nil =
    match head_subj with
    | RDF_Term.S_IRI i -> i = rdf_nil_iri
    | uu___ -> false in
  if is_nil
  then FStar_Pervasives_Native.Some []
  else
    if fuel = Prims.int_zero
    then FStar_Pervasives_Native.None
    else
      (let firsts = find_objects_indexed ig head_subj rdf_first in
       let rests = find_objects_indexed ig head_subj rdf_rest in
       match (firsts, rests) with
       | ((RDF_Term.T_IRI p1)::uu___2, tail_term::uu___3) ->
           (match term_to_subject tail_term with
            | FStar_Pervasives_Native.Some tail_subj ->
                (match decode_chain_list_fuel g ig tail_subj
                         (fuel - Prims.int_one)
                 with
                 | FStar_Pervasives_Native.Some tail_props ->
                     FStar_Pervasives_Native.Some (p1 :: tail_props)
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.None)
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
       | (uu___2, uu___3) -> FStar_Pervasives_Native.None)
let decode_chain_list (g : RDF_Graph.rdf_graph) (ig : indexed_graph)
  (head_subj : RDF_Term.subject) :
  RDF_Term.wf_iri Prims.list FStar_Pervasives_Native.option=
  let fuel = (graph_len g) + Prims.int_one in
  match decode_chain_list_fuel g ig head_subj fuel with
  | FStar_Pervasives_Native.Some [] -> FStar_Pervasives_Native.None
  | x -> x
let rec find_chain_endpoints (g : RDF_Graph.rdf_graph) (ig : indexed_graph)
  (chain : RDF_Term.wf_iri Prims.list) (x : RDF_Term.subject) :
  RDF_Term.rdf_term Prims.list=
  match chain with
  | [] -> [subject_to_term x]
  | p::rest ->
      let next_terms = find_objects_indexed ig x p in
      FStar_List_Tot_Base.fold_left
        (fun acc y_term ->
           match term_to_subject y_term with
           | FStar_Pervasives_Native.Some y_subj ->
               FStar_List_Tot_Base.append acc
                 (find_chain_endpoints g ig rest y_subj)
           | FStar_Pervasives_Native.None -> acc) [] next_terms
let owl_rule_property_chain_n (g : RDF_Graph.rdf_graph) (ig : indexed_graph)
  : RDF_Graph.rdf_graph=
  let chain_decls = bucket_lookup ig.ig_pred owl_propertyChainAxiom in
  match chain_decls with
  | [] -> g
  | uu___ ->
      let starting_subjects =
        FStar_List_Tot_Base.fold_left
          (fun acc t ->
             if
               FStar_List_Tot_Base.existsb
                 (fun s -> RDF_Term.subject_eq s t.RDF_Triple.s) acc
             then acc
             else (t.RDF_Triple.s) :: acc) [] g in
      FStar_List_Tot_Base.fold_left
        (fun acc chain_t ->
           if chain_t.RDF_Triple.p = owl_propertyChainAxiom
           then
             match ((chain_t.RDF_Triple.s),
                     (term_to_subject chain_t.RDF_Triple.o))
             with
             | (RDF_Term.S_IRI p_iri, FStar_Pervasives_Native.Some list_subj)
                 ->
                 (match decode_chain_list g ig list_subj with
                  | FStar_Pervasives_Native.Some chain ->
                      if
                        (FStar_List_Tot_Base.length chain) >=
                          (Prims.of_int (2))
                      then
                        FStar_List_Tot_Base.fold_left
                          (fun acc1 x ->
                             let zs = find_chain_endpoints g ig chain x in
                             FStar_List_Tot_Base.fold_left
                               (fun acc2 z_term ->
                                  let new_t =
                                    {
                                      RDF_Triple.s = x;
                                      RDF_Triple.p = p_iri;
                                      RDF_Triple.o = z_term
                                    } in
                                  add_triple_unchecked acc2 new_t) acc1 zs)
                          acc starting_subjects
                      else acc
                  | FStar_Pervasives_Native.None -> acc)
             | (uu___1, uu___2) -> acc
           else acc) g g
let owl_rule_chain_to_transitive (g : RDF_Graph.rdf_graph)
  (ig : indexed_graph) : RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.fold_left
    (fun acc chain_t ->
       if chain_t.RDF_Triple.p = owl_propertyChainAxiom
       then
         match ((chain_t.RDF_Triple.s),
                 (term_to_subject chain_t.RDF_Triple.o))
         with
         | (RDF_Term.S_IRI p_iri, FStar_Pervasives_Native.Some list_subj) ->
             (match decode_chain_pair g ig list_subj with
              | FStar_Pervasives_Native.Some (q1, q2) ->
                  if (q1 = p_iri) && (q2 = p_iri)
                  then
                    let new_t =
                      {
                        RDF_Triple.s = (RDF_Term.S_IRI p_iri);
                        RDF_Triple.p = rdf_type;
                        RDF_Triple.o =
                          (RDF_Term.T_IRI owl_TransitiveProperty)
                      } in
                    add_triple_unchecked acc new_t
                  else acc
              | FStar_Pervasives_Native.None -> acc)
         | (uu___, uu___1) -> acc
       else acc) g g
let canonical_chainl1_bnode (p : RDF_Term.wf_iri) : RDF_Term.bnode_id=
  FStar_String.concat "" ["__rl_chainl1__"; p]
let canonical_chainl2_bnode (p : RDF_Term.wf_iri) : RDF_Term.bnode_id=
  FStar_String.concat "" ["__rl_chainl2__"; p]
let owl_rule_transitive_to_chain (g : RDF_Graph.rdf_graph)
  (ig : indexed_graph) : RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.fold_left
    (fun acc t ->
       if
         (t.RDF_Triple.p = rdf_type) &&
           (RDF_Term.rdf_term_eq t.RDF_Triple.o
              (RDF_Term.T_IRI owl_TransitiveProperty))
       then
         match t.RDF_Triple.s with
         | RDF_Term.S_IRI p_iri ->
             let l1 = canonical_chainl1_bnode p_iri in
             let l2 = canonical_chainl2_bnode p_iri in
             add_triples_if_new acc
               [{
                  RDF_Triple.s = (RDF_Term.S_IRI p_iri);
                  RDF_Triple.p = owl_propertyChainAxiom;
                  RDF_Triple.o = (RDF_Term.T_BNode l1)
                };
               {
                 RDF_Triple.s = (RDF_Term.S_BNode l1);
                 RDF_Triple.p = rdf_first;
                 RDF_Triple.o = (RDF_Term.T_IRI p_iri)
               };
               {
                 RDF_Triple.s = (RDF_Term.S_BNode l1);
                 RDF_Triple.p = rdf_rest;
                 RDF_Triple.o = (RDF_Term.T_BNode l2)
               };
               {
                 RDF_Triple.s = (RDF_Term.S_BNode l2);
                 RDF_Triple.p = rdf_first;
                 RDF_Triple.o = (RDF_Term.T_IRI p_iri)
               };
               {
                 RDF_Triple.s = (RDF_Term.S_BNode l2);
                 RDF_Triple.p = rdf_rest;
                 RDF_Triple.o = (RDF_Term.T_IRI rdf_nil_iri)
               }]
         | uu___ -> acc
       else acc) g g
let owl_rule_named_sameAs_to_equivClass (g : RDF_Graph.rdf_graph)
  (ig : indexed_graph) : RDF_Graph.rdf_graph=
  let is_class i =
    let types = find_objects_indexed ig (RDF_Term.S_IRI i) rdf_type in
    FStar_List_Tot_Base.existsb
      (fun x -> RDF_Term.rdf_term_eq x (RDF_Term.T_IRI owl_Class)) types in
  FStar_List_Tot_Base.fold_left
    (fun acc t ->
       if t.RDF_Triple.p = owl_sameAs
       then
         match ((t.RDF_Triple.s), (t.RDF_Triple.o)) with
         | (RDF_Term.S_IRI c_iri, RDF_Term.T_IRI d_iri) ->
             (if ((c_iri <> d_iri) && (is_class c_iri)) && (is_class d_iri)
              then
                let t1 =
                  {
                    RDF_Triple.s = (RDF_Term.S_IRI c_iri);
                    RDF_Triple.p = owl_equivalentClass;
                    RDF_Triple.o = (RDF_Term.T_IRI d_iri)
                  } in
                let t2 =
                  {
                    RDF_Triple.s = (RDF_Term.S_IRI d_iri);
                    RDF_Triple.p = owl_equivalentClass;
                    RDF_Triple.o = (RDF_Term.T_IRI c_iri)
                  } in
                add_triple_unchecked (add_triple_unchecked acc t1) t2
              else acc)
         | (uu___, uu___1) -> acc
       else acc) g g
let owl_semantics_direct : Prims.string= "DIRECT"
let owl_semantics_rdf_based : Prims.string= "RDF-BASED"
let owl_rule_named_equivClass_to_sameAs_mode (g : RDF_Graph.rdf_graph)
  (ig : indexed_graph) (mode : Prims.string) : RDF_Graph.rdf_graph=
  if mode = owl_semantics_rdf_based
  then g
  else
    (let is_class i =
       let types = find_objects_indexed ig (RDF_Term.S_IRI i) rdf_type in
       FStar_List_Tot_Base.existsb
         (fun x -> RDF_Term.rdf_term_eq x (RDF_Term.T_IRI owl_Class)) types in
     let has_extra_property i =
       FStar_List_Tot_Base.existsb
         (fun t ->
            match t.RDF_Triple.s with
            | RDF_Term.S_IRI si ->
                ((((si = i) && (t.RDF_Triple.p <> rdf_type)) &&
                    (t.RDF_Triple.p <> owl_equivalentClass))
                   && (t.RDF_Triple.p <> rdfs_subClassOf))
                  && (t.RDF_Triple.p <> owl_sameAs)
            | RDF_Term.S_BNode uu___1 -> false) g in
     FStar_List_Tot_Base.fold_left
       (fun acc t ->
          if t.RDF_Triple.p = owl_equivalentClass
          then
            match ((t.RDF_Triple.s), (t.RDF_Triple.o)) with
            | (RDF_Term.S_IRI c_iri, RDF_Term.T_IRI d_iri) ->
                (if
                   (((c_iri <> d_iri) && (is_class c_iri)) &&
                      (is_class d_iri))
                     &&
                     ((has_extra_property c_iri) ||
                        (has_extra_property d_iri))
                 then
                   let t1 =
                     {
                       RDF_Triple.s = (RDF_Term.S_IRI c_iri);
                       RDF_Triple.p = owl_sameAs;
                       RDF_Triple.o = (RDF_Term.T_IRI d_iri)
                     } in
                   let t2 =
                     {
                       RDF_Triple.s = (RDF_Term.S_IRI d_iri);
                       RDF_Triple.p = owl_sameAs;
                       RDF_Triple.o = (RDF_Term.T_IRI c_iri)
                     } in
                   add_triple_unchecked (add_triple_unchecked acc t1) t2
                 else acc)
            | (uu___1, uu___2) -> acc
          else acc) g g)
let owl_rule_named_equivClass_to_sameAs (g : RDF_Graph.rdf_graph)
  (ig : indexed_graph) : RDF_Graph.rdf_graph=
  owl_rule_named_equivClass_to_sameAs_mode g ig owl_semantics_direct
let rec decode_iri_list (g : RDF_Graph.rdf_graph) (ig : indexed_graph)
  (head_subj : RDF_Term.subject) (fuel : Prims.nat) :
  RDF_Term.wf_iri Prims.list FStar_Pervasives_Native.option=
  let is_nil_head =
    match head_subj with
    | RDF_Term.S_IRI i -> i = rdf_nil_iri
    | uu___ -> false in
  if is_nil_head
  then FStar_Pervasives_Native.Some []
  else
    if fuel = Prims.int_zero
    then FStar_Pervasives_Native.None
    else
      (let firsts = find_objects_indexed ig head_subj rdf_first in
       let rests = find_objects_indexed ig head_subj rdf_rest in
       match (firsts, rests) with
       | ((RDF_Term.T_IRI p_iri)::uu___2, tail_term::uu___3) ->
           (match term_to_subject tail_term with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some tail_subj ->
                (match decode_iri_list g ig tail_subj (fuel - Prims.int_one)
                 with
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.None
                 | FStar_Pervasives_Native.Some rest_props ->
                     FStar_Pervasives_Native.Some (p_iri :: rest_props)))
       | (uu___2, uu___3) -> FStar_Pervasives_Native.None)
let collect_haskey_axioms (g : RDF_Graph.rdf_graph) (ig : indexed_graph) :
  (RDF_Term.wf_iri * RDF_Term.wf_iri Prims.list) Prims.list=
  let fuel = FStar_List_Tot_Base.length g in
  FStar_List_Tot_Base.fold_left
    (fun acc t ->
       if t.RDF_Triple.p = owl_hasKey
       then
         match ((t.RDF_Triple.s), (term_to_subject t.RDF_Triple.o)) with
         | (RDF_Term.S_IRI c_iri, FStar_Pervasives_Native.Some list_subj) ->
             (match decode_iri_list g ig list_subj fuel with
              | FStar_Pervasives_Native.Some props -> (c_iri, props) :: acc
              | FStar_Pervasives_Native.None -> acc)
         | (uu___, uu___1) -> acc
       else acc) [] g
let owl_rule_cls_int1 (g : RDF_Graph.rdf_graph) (ig : indexed_graph) :
  RDF_Graph.rdf_graph=
  let fuel = FStar_List_Tot_Base.length g in
  FStar_List_Tot_Base.fold_left
    (fun acc t ->
       if t.RDF_Triple.p = owl_intersectionOf_iri
       then
         match term_to_subject t.RDF_Triple.o with
         | FStar_Pervasives_Native.None -> acc
         | FStar_Pervasives_Native.Some list_subj ->
             (match decode_iri_list g ig list_subj fuel with
              | FStar_Pervasives_Native.None -> acc
              | FStar_Pervasives_Native.Some members ->
                  let xs =
                    find_subjects_indexed ig rdf_type
                      (subject_to_term t.RDF_Triple.s) in
                  FStar_List_Tot_Base.fold_left
                    (fun acc1 x ->
                       FStar_List_Tot_Base.fold_left
                         (fun acc2 ci ->
                            let new_t =
                              {
                                RDF_Triple.s = x;
                                RDF_Triple.p = rdf_type;
                                RDF_Triple.o = (RDF_Term.T_IRI ci)
                              } in
                            add_triple_unchecked acc2 new_t) acc1 members)
                    acc xs)
       else acc) g g
let members_of_class (g : RDF_Graph.rdf_graph) (cls : RDF_Term.wf_iri) :
  RDF_Term.wf_iri Prims.list=
  FStar_List_Tot_Base.fold_left
    (fun acc t ->
       if
         (t.RDF_Triple.p = rdf_type) &&
           (RDF_Term.rdf_term_eq t.RDF_Triple.o (RDF_Term.T_IRI cls))
       then
         match t.RDF_Triple.s with
         | RDF_Term.S_IRI x_iri ->
             (if FStar_List_Tot_Base.mem x_iri acc then acc else x_iri :: acc)
         | uu___ -> acc
       else acc) [] g
let agree_on_property (g : RDF_Graph.rdf_graph) (ig : indexed_graph)
  (x : RDF_Term.wf_iri) (y : RDF_Term.wf_iri) (p : RDF_Term.wf_iri) :
  Prims.bool=
  let xs_objs = find_objects_indexed ig (RDF_Term.S_IRI x) p in
  let ys_objs = find_objects_indexed ig (RDF_Term.S_IRI y) p in
  FStar_List_Tot_Base.existsb
    (fun xv ->
       FStar_List_Tot_Base.existsb (fun yv -> RDF_Term.rdf_term_eq xv yv)
         ys_objs) xs_objs
let rec all_keys_match (g : RDF_Graph.rdf_graph) (ig : indexed_graph)
  (x : RDF_Term.wf_iri) (y : RDF_Term.wf_iri)
  (props : RDF_Term.wf_iri Prims.list) : Prims.bool=
  match props with
  | [] -> true
  | p::rest ->
      if agree_on_property g ig x y p
      then all_keys_match g ig x y rest
      else false
let owl_rule_prp_key (g : RDF_Graph.rdf_graph) (ig : indexed_graph) :
  RDF_Graph.rdf_graph=
  let axioms = collect_haskey_axioms g ig in
  FStar_List_Tot_Base.fold_left
    (fun acc axiom ->
       let uu___ = axiom in
       match uu___ with
       | (c_iri, props) ->
           (match props with
            | [] -> acc
            | uu___1 ->
                let members = members_of_class g c_iri in
                FStar_List_Tot_Base.fold_left
                  (fun acc1 x ->
                     FStar_List_Tot_Base.fold_left
                       (fun acc2 y ->
                          if x = y
                          then acc2
                          else
                            if all_keys_match g ig x y props
                            then
                              (let new_t =
                                 {
                                   RDF_Triple.s = (RDF_Term.S_IRI x);
                                   RDF_Triple.p = owl_sameAs;
                                   RDF_Triple.o = (RDF_Term.T_IRI y)
                                 } in
                               add_triple_unchecked acc2 new_t)
                            else acc2) acc1 members) acc members)) g axioms
let xsd_long : RDF_Term.wf_iri= "http://www.w3.org/2001/XMLSchema#long"
let xsd_int : RDF_Term.wf_iri= "http://www.w3.org/2001/XMLSchema#int"
let xsd_short : RDF_Term.wf_iri= "http://www.w3.org/2001/XMLSchema#short"
let xsd_byte : RDF_Term.wf_iri= "http://www.w3.org/2001/XMLSchema#byte"
let xsd_positiveInteger : RDF_Term.wf_iri=
  "http://www.w3.org/2001/XMLSchema#positiveInteger"
let xsd_unsignedLong : RDF_Term.wf_iri=
  "http://www.w3.org/2001/XMLSchema#unsignedLong"
let xsd_unsignedInt : RDF_Term.wf_iri=
  "http://www.w3.org/2001/XMLSchema#unsignedInt"
let xsd_unsignedShort : RDF_Term.wf_iri=
  "http://www.w3.org/2001/XMLSchema#unsignedShort"
let xsd_unsignedByte : RDF_Term.wf_iri=
  "http://www.w3.org/2001/XMLSchema#unsignedByte"
let xsd_nonPositiveInteger : RDF_Term.wf_iri=
  "http://www.w3.org/2001/XMLSchema#nonPositiveInteger"
let xsd_negativeInteger : RDF_Term.wf_iri=
  "http://www.w3.org/2001/XMLSchema#negativeInteger"
let xsd_ns_prefix : Prims.string= "http://www.w3.org/2001/XMLSchema#"
let iri_in_xsd_ns (i : RDF_Term.wf_iri) : Prims.bool=
  let plen = FStar_String.strlen xsd_ns_prefix in
  let ilen = FStar_String.strlen i in
  if ilen < plen
  then false
  else (FStar_String.sub i Prims.int_zero plen) = xsd_ns_prefix
let term_in_xsd_ns (t : RDF_Term.rdf_term) : Prims.bool=
  match t with | RDF_Term.T_IRI i -> iri_in_xsd_ns i | uu___ -> false
let subject_in_xsd_ns (s : RDF_Term.subject) : Prims.bool=
  match s with | RDF_Term.S_IRI i -> iri_in_xsd_ns i | uu___ -> false
let triple_mentions_xsd (t : RDF_Triple.triple) : Prims.bool=
  ((subject_in_xsd_ns t.RDF_Triple.s) || (iri_in_xsd_ns t.RDF_Triple.p)) ||
    (term_in_xsd_ns t.RDF_Triple.o)
let graph_mentions_xsd_iri (g : RDF_Graph.rdf_graph) : Prims.bool=
  FStar_List_Tot_Base.existsb triple_mentions_xsd g
let xsd_hierarchy_edges : (RDF_Term.wf_iri * RDF_Term.wf_iri) Prims.list=
  [(xsd_byte, xsd_short);
  (xsd_short, xsd_int);
  (xsd_int, xsd_long);
  (xsd_long, RDF_Term.xsd_integer);
  (xsd_positiveInteger, xsd_nonNegativeInteger);
  (xsd_unsignedByte, xsd_unsignedShort);
  (xsd_unsignedShort, xsd_unsignedInt);
  (xsd_unsignedInt, xsd_unsignedLong);
  (xsd_unsignedLong, xsd_nonNegativeInteger);
  (xsd_nonNegativeInteger, RDF_Term.xsd_integer);
  (xsd_negativeInteger, xsd_nonPositiveInteger);
  (xsd_nonPositiveInteger, RDF_Term.xsd_integer);
  (RDF_Term.xsd_integer, RDF_Term.xsd_decimal);
  (RDF_Term.xsd_decimal, RDF_Term.xsd_double)]
let xsd_all_datatypes : RDF_Term.wf_iri Prims.list=
  [RDF_Term.xsd_string;
  RDF_Term.xsd_boolean;
  RDF_Term.xsd_double;
  RDF_Term.xsd_decimal;
  RDF_Term.xsd_integer;
  xsd_long;
  xsd_int;
  xsd_short;
  xsd_byte;
  xsd_nonNegativeInteger;
  xsd_positiveInteger;
  xsd_unsignedLong;
  xsd_unsignedInt;
  xsd_unsignedShort;
  xsd_unsignedByte;
  xsd_nonPositiveInteger;
  xsd_negativeInteger]
let owl_rule_xsd_datatype_axioms (g : RDF_Graph.rdf_graph)
  (ig : indexed_graph) : RDF_Graph.rdf_graph=
  if Prims.op_Negation (graph_mentions_xsd_iri g)
  then g
  else
    (let sub_triples =
       FStar_List_Tot_Base.map
         (fun pair ->
            let uu___1 = pair in
            match uu___1 with
            | (sub_i, sup_i) ->
                {
                  RDF_Triple.s = (RDF_Term.S_IRI sub_i);
                  RDF_Triple.p = rdfs_subClassOf;
                  RDF_Triple.o = (RDF_Term.T_IRI sup_i)
                }) xsd_hierarchy_edges in
     let dt_triples =
       FStar_List_Tot_Base.map
         (fun i ->
            {
              RDF_Triple.s = (RDF_Term.S_IRI i);
              RDF_Triple.p = rdf_type;
              RDF_Triple.o = (RDF_Term.T_IRI rdfs_Datatype)
            }) xsd_all_datatypes in
     add_triples_if_new (add_triples_if_new g sub_triples) dt_triples)
let xsd_range_intersections :
  (RDF_Term.wf_iri * RDF_Term.wf_iri * RDF_Term.wf_iri Prims.list) Prims.list=
  [(xsd_short, xsd_unsignedInt, [xsd_unsignedShort]);
  (xsd_short, xsd_unsignedLong, [xsd_unsignedShort]);
  (xsd_byte, xsd_unsignedInt, [xsd_unsignedByte]);
  (xsd_nonNegativeInteger, xsd_nonPositiveInteger,
    [xsd_byte; xsd_unsignedByte])]
let owl_rule_dt_range_intersect (g : RDF_Graph.rdf_graph)
  (ig : indexed_graph) : RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.fold_left
    (fun acc t ->
       if t.RDF_Triple.p = rdfs_range
       then
         match t.RDF_Triple.o with
         | RDF_Term.T_IRI d1 ->
             let others = find_objects_indexed ig t.RDF_Triple.s rdfs_range in
             FStar_List_Tot_Base.fold_left
               (fun acc1 d2_term ->
                  match d2_term with
                  | RDF_Term.T_IRI d2 ->
                      FStar_List_Tot_Base.fold_left
                        (fun acc2 entry ->
                           let uu___ = entry in
                           match uu___ with
                           | (e1, e2, outs) ->
                               if
                                 ((e1 = d1) && (e2 = d2)) ||
                                   ((e1 = d2) && (e2 = d1))
                               then
                                 FStar_List_Tot_Base.fold_left
                                   (fun acc3 d3 ->
                                      add_triple_unchecked acc3
                                        {
                                          RDF_Triple.s = (t.RDF_Triple.s);
                                          RDF_Triple.p = rdfs_range;
                                          RDF_Triple.o = (RDF_Term.T_IRI d3)
                                        }) acc2 outs
                               else acc2) acc1 xsd_range_intersections
                  | uu___ -> acc1) acc others
         | uu___ -> acc
       else acc) g g
let owl_rule_scm_dom2 (g : RDF_Graph.rdf_graph) (ig : indexed_graph) :
  RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.fold_left
    (fun acc t ->
       if t.RDF_Triple.p = rdfs_domain
       then
         match t.RDF_Triple.o with
         | RDF_Term.T_IRI c1_iri ->
             let supers =
               find_objects_indexed ig (RDF_Term.S_IRI c1_iri)
                 rdfs_subClassOf in
             FStar_List_Tot_Base.fold_left
               (fun acc2 c2_term ->
                  match c2_term with
                  | RDF_Term.T_IRI uu___ ->
                      let new_t =
                        {
                          RDF_Triple.s = (t.RDF_Triple.s);
                          RDF_Triple.p = rdfs_domain;
                          RDF_Triple.o = c2_term
                        } in
                      add_triple_unchecked acc2 new_t
                  | uu___ -> acc2) acc supers
         | uu___ -> acc
       else acc) g g
let owl_rule_scm_rng2 (g : RDF_Graph.rdf_graph) (ig : indexed_graph) :
  RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.fold_left
    (fun acc t ->
       if t.RDF_Triple.p = rdfs_range
       then
         match t.RDF_Triple.o with
         | RDF_Term.T_IRI c1_iri ->
             let supers =
               find_objects_indexed ig (RDF_Term.S_IRI c1_iri)
                 rdfs_subClassOf in
             FStar_List_Tot_Base.fold_left
               (fun acc2 c2_term ->
                  match c2_term with
                  | RDF_Term.T_IRI uu___ ->
                      let new_t =
                        {
                          RDF_Triple.s = (t.RDF_Triple.s);
                          RDF_Triple.p = rdfs_range;
                          RDF_Triple.o = c2_term
                        } in
                      add_triple_unchecked acc2 new_t
                  | uu___ -> acc2) acc supers
         | uu___ -> acc
       else acc) g g
let owl_xsd_core_datatype_axioms : RDF_Triple.triple Prims.list=
  [{
     RDF_Triple.s = (RDF_Term.S_IRI RDF_Term.xsd_integer);
     RDF_Triple.p = rdf_type;
     RDF_Triple.o = (RDF_Term.T_IRI rdfs_Datatype)
   };
  {
    RDF_Triple.s = (RDF_Term.S_IRI RDF_Term.xsd_string);
    RDF_Triple.p = rdf_type;
    RDF_Triple.o = (RDF_Term.T_IRI rdfs_Datatype)
  }]
let owl_rule_xsd_core_datatype_axioms (g : RDF_Graph.rdf_graph)
  (ig : indexed_graph) : RDF_Graph.rdf_graph=
  add_triples_if_new g owl_xsd_core_datatype_axioms
let owl_AllDisjointClasses_iri : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#AllDisjointClasses"
let owl_members_iri : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#members"
let owl_rule_all_disjoint_classes (g : RDF_Graph.rdf_graph)
  (ig : indexed_graph) : RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.fold_left
    (fun acc t ->
       if
         (t.RDF_Triple.p = rdf_type) &&
           (RDF_Term.rdf_term_eq t.RDF_Triple.o
              (RDF_Term.T_IRI owl_AllDisjointClasses_iri))
       then
         FStar_List_Tot_Base.fold_left
           (fun acc1 l_term ->
              match term_to_subject l_term with
              | FStar_Pervasives_Native.None -> acc1
              | FStar_Pervasives_Native.Some l_subj ->
                  (match decode_chain_list g ig l_subj with
                   | FStar_Pervasives_Native.Some cs ->
                       FStar_List_Tot_Base.fold_left
                         (fun acc2 c1 ->
                            FStar_List_Tot_Base.fold_left
                              (fun acc3 c2 ->
                                 if c1 = c2
                                 then acc3
                                 else
                                   add_triple_unchecked acc3
                                     {
                                       RDF_Triple.s = (RDF_Term.S_IRI c1);
                                       RDF_Triple.p = owl_disjointWith_iri;
                                       RDF_Triple.o = (RDF_Term.T_IRI c2)
                                     }) acc2 cs) acc1 cs
                   | FStar_Pervasives_Native.None -> acc1)) acc
           (find_objects_indexed ig t.RDF_Triple.s owl_members_iri)
       else acc) g g
let owl_AllDisjointProperties_iri : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#AllDisjointProperties"
let owl_AllDifferent_iri : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#AllDifferent"
let owl_rule_all_disjoint_properties (g : RDF_Graph.rdf_graph)
  (ig : indexed_graph) : RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.fold_left
    (fun acc t ->
       if
         (t.RDF_Triple.p = rdf_type) &&
           (RDF_Term.rdf_term_eq t.RDF_Triple.o
              (RDF_Term.T_IRI owl_AllDisjointProperties_iri))
       then
         FStar_List_Tot_Base.fold_left
           (fun acc1 l_term ->
              match term_to_subject l_term with
              | FStar_Pervasives_Native.None -> acc1
              | FStar_Pervasives_Native.Some l_subj ->
                  (match decode_chain_list g ig l_subj with
                   | FStar_Pervasives_Native.Some ps ->
                       FStar_List_Tot_Base.fold_left
                         (fun acc2 p1 ->
                            FStar_List_Tot_Base.fold_left
                              (fun acc3 p2 ->
                                 if p1 = p2
                                 then acc3
                                 else
                                   add_triple_unchecked acc3
                                     {
                                       RDF_Triple.s = (RDF_Term.S_IRI p1);
                                       RDF_Triple.p =
                                         owl_propertyDisjointWith;
                                       RDF_Triple.o = (RDF_Term.T_IRI p2)
                                     }) acc2 ps) acc1 ps
                   | FStar_Pervasives_Native.None -> acc1)) acc
           (find_objects_indexed ig t.RDF_Triple.s owl_members_iri)
       else acc) g g
let differentFrom_canonical_pairs (ig : indexed_graph) :
  (RDF_Term.subject * RDF_Term.subject) Prims.list=
  let raw =
    FStar_List_Tot_Base.fold_left
      (fun acc t ->
         if t.RDF_Triple.p = owl_differentFrom
         then
           match term_to_subject t.RDF_Triple.o with
           | FStar_Pervasives_Native.Some y ->
               (if RDF_Term.subject_eq t.RDF_Triple.s y
                then acc
                else
                  if
                    (FStar_String.compare (subject_to_key t.RDF_Triple.s)
                       (subject_to_key y))
                      < Prims.int_zero
                  then ((t.RDF_Triple.s), y) :: acc
                  else acc)
           | FStar_Pervasives_Native.None -> acc
         else acc) [] ig.ig_triples in
  let sorted = FStar_List_Tot_Base.sortWith sameas_pair_cmp raw in
  dedup_pairs_sorted_aux FStar_Pervasives_Native.None sorted []
let canonical_adf_bnode (k1 : Prims.string) (k2 : Prims.string) :
  RDF_Term.bnode_id= FStar_String.concat "" ["__rl_adf__"; k1; "__vs__"; k2]
let canonical_adfl1_bnode (k1 : Prims.string) (k2 : Prims.string) :
  RDF_Term.bnode_id=
  FStar_String.concat "" ["__rl_adfl1__"; k1; "__vs__"; k2]
let canonical_adfl2_bnode (k1 : Prims.string) (k2 : Prims.string) :
  RDF_Term.bnode_id=
  FStar_String.concat "" ["__rl_adfl2__"; k1; "__vs__"; k2]
let owl_rule_differentFrom_to_allDifferent (g : RDF_Graph.rdf_graph)
  (ig : indexed_graph) : RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.fold_left
    (fun acc xy ->
       let uu___ = xy in
       match uu___ with
       | (x, y) ->
           let k1 = subject_to_key x in
           let k2 = subject_to_key y in
           let adf = RDF_Term.S_BNode (canonical_adf_bnode k1 k2) in
           let l1 = canonical_adfl1_bnode k1 k2 in
           let l2 = canonical_adfl2_bnode k1 k2 in
           add_triples_if_new acc
             [{
                RDF_Triple.s = adf;
                RDF_Triple.p = rdf_type;
                RDF_Triple.o = (RDF_Term.T_IRI owl_AllDifferent_iri)
              };
             {
               RDF_Triple.s = adf;
               RDF_Triple.p = owl_members_iri;
               RDF_Triple.o = (RDF_Term.T_BNode l1)
             };
             {
               RDF_Triple.s = (RDF_Term.S_BNode l1);
               RDF_Triple.p = rdf_first;
               RDF_Triple.o = (subject_to_term x)
             };
             {
               RDF_Triple.s = (RDF_Term.S_BNode l1);
               RDF_Triple.p = rdf_rest;
               RDF_Triple.o = (RDF_Term.T_BNode l2)
             };
             {
               RDF_Triple.s = (RDF_Term.S_BNode l2);
               RDF_Triple.p = rdf_first;
               RDF_Triple.o = (subject_to_term y)
             };
             {
               RDF_Triple.s = (RDF_Term.S_BNode l2);
               RDF_Triple.p = rdf_rest;
               RDF_Triple.o = (RDF_Term.T_IRI rdf_nil_iri)
             }]) g (differentFrom_canonical_pairs ig)
let owl_rl_closure_step_mode (g : RDF_Graph.rdf_graph) (mode : Prims.string)
  : RDF_Graph.rdf_graph=
  let ig = build_indexed g in
  let g1 = owl_rule_equivalent_class g ig in
  let g2 = owl_rule_equivalent_property g1 ig in
  let g2a = owl_rule_scm_eqc2 g2 ig in
  let g2b = owl_rule_scm_eqp2 g2a ig in
  let g3 = owl_rule_inverse_of g2b ig in
  let g3_adc = owl_rule_all_disjoint_classes g3 ig in
  let g3_disj = owl_rule_disjoint_with_propagation g3_adc ig in
  let g3_comp = owl_rule_disjoint_to_complement g3_disj ig in
  let g3a = owl_rule_inverseOf_domain_range_flip g3_comp ig in
  let g4 = owl_rule_symmetric_property g3a ig in
  let g5 = owl_rule_transitive_property g4 ig in
  let g5a = owl_rule_named_equivClass_to_sameAs_mode g5 ig mode in
  let g6 = owl_rule_sameAs_reflexivity g5a ig in
  let g7 = owl_rule_sameAs_symmetry g6 ig in
  let g7a = owl_rule_differentFrom_symmetry g7 ig in
  let g8 = owl_rule_sameAs_transitivity g7a ig in
  let g9 = owl_rule_sameAs_replace_subject g8 ig in
  let g10 = owl_rule_sameAs_replace_object g9 ig in
  let g11 = owl_rule_sameAs_replace_predicate g10 ig in
  let g11a = owl_rule_functional g11 ig in
  let g12 = owl_rule_inverse_functional g11a ig in
  let g12_adp = owl_rule_all_disjoint_properties g12 ig in
  let g12a = owl_rule_pdw_to_differentFrom g12_adp ig in
  let g12a1 = owl_rule_pdw_shared_value_to_differentFrom g12a ig in
  let g12b = owl_rule_fp_diff_to_diff g12a1 ig in
  let g12c = owl_rule_ifp_diff_to_diff g12b ig in
  let g12d = owl_rule_differentFrom_to_allDifferent g12c ig in
  let g13 = owl_rule_minc1_bridge g12d ig in
  let g13a = owl_rule_svf2_existential_witness g13 ig in
  let g14 = owl_rule_cls_svf2_qualified g13a ig in
  let g15 = owl_rule_cls_minc_qual1 g14 ig in
  let g16 = owl_rule_cls_maxqc1 g15 ig in
  let g17 = owl_rule_cls_exactqc1 g16 ig in
  let g18 = owl_rule_cls_maxc2 g17 ig in
  let g18a = owl_rule_cls_maxqc_comp g18 ig in
  let g19 = owl_rule_cls_avf1 g18a ig in
  let g19a = owl_rule_cls_hv1 g19 ig in
  let g19b = owl_rule_cls_hv2 g19a ig in
  let g20 = owl_rule_reflexive_property g19b ig in
  let g21 = owl_rule_scm_cls_restriction g20 ig in
  let g21a = owl_rule_cls_int1 g21 ig in
  let g22 = owl_rule_property_chain_2 g21a ig in
  let g22a = owl_rule_property_chain_n g22 ig in
  let g23 = owl_rule_chain_to_transitive g22a ig in
  let g23a = owl_rule_transitive_to_chain g23 ig in
  let g24 = owl_rule_named_sameAs_to_equivClass g23a ig in
  let g24a = owl_rule_prp_key g24 ig in
  let g25 = owl_rule_xsd_datatype_axioms g24a ig in
  let g25a = owl_rule_dt_range_intersect g25 ig in
  let g26 = owl_rule_xsd_core_datatype_axioms g25a ig in
  let g27 = owl_rule_scm_dom2 g26 ig in
  let g28 = owl_rule_scm_rng2 g27 ig in graph_dedup_sort g28
let owl_rl_closure_step (g : RDF_Graph.rdf_graph) : RDF_Graph.rdf_graph=
  owl_rl_closure_step_mode g owl_semantics_direct
let rec owl_rl_closure_mode (g : RDF_Graph.rdf_graph) (fuel : Prims.nat)
  (mode : Prims.string) : RDF_Graph.rdf_graph=
  match fuel with
  | uu___ when uu___ = Prims.int_zero -> g
  | uu___ ->
      let next_fuel = fuel - Prims.int_one in
      let g_owl = owl_rl_closure_step_mode g mode in
      let g_rdfs = rdfs_closure_step g_owl in
      if (graph_len g_rdfs) = (graph_len g)
      then g
      else owl_rl_closure_mode g_rdfs next_fuel mode
let owl_rl_closure (g : RDF_Graph.rdf_graph) (fuel : Prims.nat) :
  RDF_Graph.rdf_graph= owl_rl_closure_mode g fuel owl_semantics_direct
let owl_thing_subject_iris (g : RDF_Graph.rdf_graph) :
  RDF_Term.wf_iri Prims.list=
  FStar_List_Tot_Base.fold_left
    (fun acc t ->
       let acc1 = cons_subject_iri_if_new t.RDF_Triple.s acc in
       cons_term_iri_if_new t.RDF_Triple.o acc1) [] g
let owl_thing_predicates (g : RDF_Graph.rdf_graph) :
  RDF_Term.wf_iri Prims.list=
  FStar_List_Tot_Base.fold_left
    (fun acc t -> cons_if_new_iri t.RDF_Triple.p acc) [] g
let owl_thing_axioms (g : RDF_Graph.rdf_graph) : RDF_Graph.rdf_graph=
  let classes = collect_classes g in
  let properties = collect_properties g in
  let indivs = owl_thing_subject_iris g in
  let predicates = owl_thing_predicates g in
  let top_class_triples =
    FStar_List_Tot_Base.map
      (fun c ->
         {
           RDF_Triple.s = (RDF_Term.S_IRI c);
           RDF_Triple.p = rdfs_subClassOf;
           RDF_Triple.o = (RDF_Term.T_IRI owl_Thing)
         }) classes in
  let bottom_class_triples =
    FStar_List_Tot_Base.map
      (fun c ->
         {
           RDF_Triple.s = (RDF_Term.S_IRI owl_Nothing);
           RDF_Triple.p = rdfs_subClassOf;
           RDF_Triple.o = (RDF_Term.T_IRI c)
         }) classes in
  let property_domain_triples =
    FStar_List_Tot_Base.map
      (fun p ->
         {
           RDF_Triple.s = (RDF_Term.S_IRI p);
           RDF_Triple.p = rdfs_domain;
           RDF_Triple.o = (RDF_Term.T_IRI owl_Thing)
         }) properties in
  let property_range_triples =
    FStar_List_Tot_Base.map
      (fun p ->
         {
           RDF_Triple.s = (RDF_Term.S_IRI p);
           RDF_Triple.p = rdfs_range;
           RDF_Triple.o = (RDF_Term.T_IRI owl_Thing)
         }) properties in
  let predicate_domain_triples =
    FStar_List_Tot_Base.map
      (fun p ->
         {
           RDF_Triple.s = (RDF_Term.S_IRI p);
           RDF_Triple.p = rdfs_domain;
           RDF_Triple.o = (RDF_Term.T_IRI owl_Thing)
         }) predicates in
  let predicate_range_triples =
    FStar_List_Tot_Base.map
      (fun p ->
         {
           RDF_Triple.s = (RDF_Term.S_IRI p);
           RDF_Triple.p = rdfs_range;
           RDF_Triple.o = (RDF_Term.T_IRI owl_Thing)
         }) predicates in
  let individual_triples =
    FStar_List_Tot_Base.map
      (fun i ->
         {
           RDF_Triple.s = (RDF_Term.S_IRI i);
           RDF_Triple.p = rdf_type;
           RDF_Triple.o = (RDF_Term.T_IRI owl_Thing)
         }) indivs in
  let self_axioms =
    [{
       RDF_Triple.s = (RDF_Term.S_IRI owl_Thing);
       RDF_Triple.p = rdf_type;
       RDF_Triple.o = (RDF_Term.T_IRI owl_Class)
     };
    {
      RDF_Triple.s = (RDF_Term.S_IRI owl_Nothing);
      RDF_Triple.p = rdf_type;
      RDF_Triple.o = (RDF_Term.T_IRI owl_Class)
    };
    {
      RDF_Triple.s = (RDF_Term.S_IRI owl_Nothing);
      RDF_Triple.p = rdfs_subClassOf;
      RDF_Triple.o = (RDF_Term.T_IRI owl_Thing)
    }] in
  FStar_List_Tot_Base.op_At top_class_triples
    (FStar_List_Tot_Base.op_At bottom_class_triples
       (FStar_List_Tot_Base.op_At property_domain_triples
          (FStar_List_Tot_Base.op_At property_range_triples
             (FStar_List_Tot_Base.op_At predicate_domain_triples
                (FStar_List_Tot_Base.op_At predicate_range_triples
                   (FStar_List_Tot_Base.op_At individual_triples self_axioms))))))
let owl_rl_closure_with_reflexivity_mode (g : RDF_Graph.rdf_graph)
  (fuel : Prims.nat) (mode : Prims.string) : RDF_Graph.rdf_graph=
  let rdfs_closed = rdfs_closure_with_reflexivity g fuel in
  let thing_axioms = owl_thing_axioms rdfs_closed in
  let with_thing = add_triples_if_new rdfs_closed thing_axioms in
  owl_rl_closure_mode with_thing fuel mode
let owl_rl_closure_with_reflexivity (g : RDF_Graph.rdf_graph)
  (fuel : Prims.nat) : RDF_Graph.rdf_graph=
  owl_rl_closure_with_reflexivity_mode g fuel owl_semantics_direct
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
let datatype_value_eq (l1 : RDF_Term.literal) (l2 : RDF_Term.literal) :
  Prims.bool=
  if l1.RDF_Term.datatype = l2.RDF_Term.datatype
  then
    (if l1.RDF_Term.datatype = RDF_Term.xsd_integer
     then
       ((normalize_integer_lexical l1.RDF_Term.lexical_form) =
          (normalize_integer_lexical l2.RDF_Term.lexical_form))
         &&
         (RDF_Term.lang_tag_option_eq l1.RDF_Term.lang_tag
            l2.RDF_Term.lang_tag)
     else
       if l1.RDF_Term.datatype = RDF_Term.xsd_decimal
       then
         ((normalize_decimal_lexical l1.RDF_Term.lexical_form) =
            (normalize_decimal_lexical l2.RDF_Term.lexical_form))
           &&
           (RDF_Term.lang_tag_option_eq l1.RDF_Term.lang_tag
              l2.RDF_Term.lang_tag)
       else RDF_Term.literal_eq l1 l2)
  else false
let has_disjoint_with (g : RDF_Graph.rdf_graph) (c1 : RDF_Term.rdf_term)
  (c2 : RDF_Term.rdf_term) : Prims.bool=
  FStar_List_Tot_Base.existsb
    (fun t ->
       (t.RDF_Triple.p = owl_disjointWith_iri) &&
         (((RDF_Term.rdf_term_eq (subject_to_term t.RDF_Triple.s) c1) &&
             (RDF_Term.rdf_term_eq t.RDF_Triple.o c2))
            ||
            ((RDF_Term.rdf_term_eq (subject_to_term t.RDF_Triple.s) c2) &&
               (RDF_Term.rdf_term_eq t.RDF_Triple.o c1)))) g
let rec xsd_is_subtype_fuel (d1 : RDF_Term.wf_iri) (d2 : RDF_Term.wf_iri)
  (fuel : Prims.nat) : Prims.bool=
  if d1 = d2
  then true
  else
    if fuel = Prims.int_zero
    then false
    else
      FStar_List_Tot_Base.existsb
        (fun edge ->
           let uu___2 = edge in
           match uu___2 with
           | (sub_i, sup_i) ->
               (sub_i = d1) &&
                 (xsd_is_subtype_fuel sup_i d2 (fuel - Prims.int_one)))
        xsd_hierarchy_edges
let xsd_is_subtype (d1 : RDF_Term.wf_iri) (d2 : RDF_Term.wf_iri) :
  Prims.bool=
  xsd_is_subtype_fuel d1 d2
    ((FStar_List_Tot_Base.length xsd_hierarchy_edges) + Prims.int_one)
let is_inconsistent (g : RDF_Graph.rdf_graph) : Prims.bool=
  let has_nothing =
    FStar_List_Tot_Base.existsb
      (fun t ->
         (t.RDF_Triple.p = rdf_type) &&
           (RDF_Term.rdf_term_eq t.RDF_Triple.o (RDF_Term.T_IRI owl_Nothing)))
      g in
  if has_nothing
  then true
  else
    (let has_sameAs_diff_clash =
       FStar_List_Tot_Base.existsb
         (fun t ->
            (t.RDF_Triple.p = owl_sameAs) &&
              (differentFrom_in_graph g (subject_to_term t.RDF_Triple.s)
                 t.RDF_Triple.o)) g in
     if has_sameAs_diff_clash
     then true
     else
       (let has_disjoint_class_clash =
          FStar_List_Tot_Base.existsb
            (fun t1 ->
               (t1.RDF_Triple.p = rdf_type) &&
                 (FStar_List_Tot_Base.existsb
                    (fun t2 ->
                       (((t2.RDF_Triple.p = rdf_type) &&
                           (RDF_Term.subject_eq t1.RDF_Triple.s
                              t2.RDF_Triple.s))
                          &&
                          (Prims.op_Negation
                             (RDF_Term.rdf_term_eq t1.RDF_Triple.o
                                t2.RDF_Triple.o)))
                         &&
                         (has_disjoint_with g t1.RDF_Triple.o t2.RDF_Triple.o))
                    g)) g in
        if has_disjoint_class_clash
        then true
        else
          (let has_irreflexive_violation =
             FStar_List_Tot_Base.existsb
               (fun decl ->
                  ((decl.RDF_Triple.p = rdf_type) &&
                     (RDF_Term.rdf_term_eq decl.RDF_Triple.o
                        (RDF_Term.T_IRI owl_IrreflexiveProperty)))
                    &&
                    (match decl.RDF_Triple.s with
                     | RDF_Term.S_IRI prop_iri ->
                         FStar_List_Tot_Base.existsb
                           (fun use ->
                              (use.RDF_Triple.p = prop_iri) &&
                                (RDF_Term.rdf_term_eq
                                   (subject_to_term use.RDF_Triple.s)
                                   use.RDF_Triple.o)) g
                     | uu___3 -> false)) g in
           if has_irreflexive_violation
           then true
           else
             (let has_asymmetric_violation =
                FStar_List_Tot_Base.existsb
                  (fun decl ->
                     ((decl.RDF_Triple.p = rdf_type) &&
                        (RDF_Term.rdf_term_eq decl.RDF_Triple.o
                           (RDF_Term.T_IRI owl_AsymmetricProperty)))
                       &&
                       (match decl.RDF_Triple.s with
                        | RDF_Term.S_IRI prop_iri ->
                            FStar_List_Tot_Base.existsb
                              (fun t1 ->
                                 (t1.RDF_Triple.p = prop_iri) &&
                                   (FStar_List_Tot_Base.existsb
                                      (fun t2 ->
                                         ((t2.RDF_Triple.p = prop_iri) &&
                                            (RDF_Term.rdf_term_eq
                                               (subject_to_term
                                                  t1.RDF_Triple.s)
                                               t2.RDF_Triple.o))
                                           &&
                                           (RDF_Term.rdf_term_eq
                                              t1.RDF_Triple.o
                                              (subject_to_term
                                                 t2.RDF_Triple.s))) g)) g
                        | uu___4 -> false)) g in
              if has_asymmetric_violation
              then true
              else
                (let is_pdw_pair p1 p2 =
                   FStar_List_Tot_Base.existsb
                     (fun pdw ->
                        (pdw.RDF_Triple.p = owl_propertyDisjointWith) &&
                          (match ((pdw.RDF_Triple.s), (pdw.RDF_Triple.o))
                           with
                           | (RDF_Term.S_IRI ps, RDF_Term.T_IRI po) ->
                               ((ps = p1) && (po = p2)) ||
                                 ((ps = p2) && (po = p1))
                           | uu___5 -> false)) g in
                 let has_pdw_direct_clash =
                   FStar_List_Tot_Base.existsb
                     (fun t1 ->
                        FStar_List_Tot_Base.existsb
                          (fun t2 ->
                             (((t1.RDF_Triple.p <> t2.RDF_Triple.p) &&
                                 (RDF_Term.subject_eq t1.RDF_Triple.s
                                    t2.RDF_Triple.s))
                                &&
                                (RDF_Term.rdf_term_eq t1.RDF_Triple.o
                                   t2.RDF_Triple.o))
                               &&
                               (is_pdw_pair t1.RDF_Triple.p t2.RDF_Triple.p))
                          g) g in
                 if has_pdw_direct_clash
                 then true
                 else
                   (let has_fp_literal_clash =
                      FStar_List_Tot_Base.existsb
                        (fun decl ->
                           ((decl.RDF_Triple.p = rdf_type) &&
                              (RDF_Term.rdf_term_eq decl.RDF_Triple.o
                                 (RDF_Term.T_IRI owl_FunctionalProperty)))
                             &&
                             (match decl.RDF_Triple.s with
                              | RDF_Term.S_IRI prop_iri ->
                                  FStar_List_Tot_Base.existsb
                                    (fun t1 ->
                                       (t1.RDF_Triple.p = prop_iri) &&
                                         (match t1.RDF_Triple.o with
                                          | RDF_Term.T_Literal l1 ->
                                              FStar_List_Tot_Base.existsb
                                                (fun t2 ->
                                                   ((t2.RDF_Triple.p =
                                                       prop_iri)
                                                      &&
                                                      (RDF_Term.subject_eq
                                                         t1.RDF_Triple.s
                                                         t2.RDF_Triple.s))
                                                     &&
                                                     (match t2.RDF_Triple.o
                                                      with
                                                      | RDF_Term.T_Literal l2
                                                          ->
                                                          Prims.op_Negation
                                                            (datatype_value_eq
                                                               l1 l2)
                                                      | uu___6 -> false)) g
                                          | uu___6 -> false)) g
                              | uu___6 -> false)) g in
                    if has_fp_literal_clash
                    then true
                    else
                      (let has_npa_clash =
                         FStar_List_Tot_Base.existsb
                           (fun npa ->
                              (npa.RDF_Triple.p = owl_sourceIndividual) &&
                                (match term_to_subject npa.RDF_Triple.o with
                                 | FStar_Pervasives_Native.None -> false
                                 | FStar_Pervasives_Native.Some i1 ->
                                     FStar_List_Tot_Base.existsb
                                       (fun ap ->
                                          ((RDF_Term.subject_eq
                                              ap.RDF_Triple.s
                                              npa.RDF_Triple.s)
                                             &&
                                             (ap.RDF_Triple.p =
                                                owl_assertionProperty))
                                            &&
                                            (match ap.RDF_Triple.o with
                                             | RDF_Term.T_IRI p ->
                                                 FStar_List_Tot_Base.existsb
                                                   (fun tgt ->
                                                      ((RDF_Term.subject_eq
                                                          tgt.RDF_Triple.s
                                                          npa.RDF_Triple.s)
                                                         &&
                                                         ((tgt.RDF_Triple.p =
                                                             owl_targetIndividual)
                                                            ||
                                                            (tgt.RDF_Triple.p
                                                               =
                                                               owl_targetValue)))
                                                        &&
                                                        (FStar_List_Tot_Base.existsb
                                                           (fun pos ->
                                                              ((pos.RDF_Triple.p
                                                                  = p)
                                                                 &&
                                                                 (RDF_Term.subject_eq
                                                                    pos.RDF_Triple.s
                                                                    i1))
                                                                &&
                                                                (RDF_Term.rdf_term_eq
                                                                   pos.RDF_Triple.o
                                                                   tgt.RDF_Triple.o))
                                                           g)) g
                                             | uu___7 -> false)) g)) g in
                       if has_npa_clash
                       then true
                       else
                         (let has_cls_com_clash =
                            FStar_List_Tot_Base.existsb
                              (fun comp ->
                                 (comp.RDF_Triple.p = owl_complementOf_iri)
                                   &&
                                   (FStar_List_Tot_Base.existsb
                                      (fun t1 ->
                                         ((t1.RDF_Triple.p = rdf_type) &&
                                            (RDF_Term.rdf_term_eq
                                               t1.RDF_Triple.o
                                               (subject_to_term
                                                  comp.RDF_Triple.s)))
                                           &&
                                           (FStar_List_Tot_Base.existsb
                                              (fun t2 ->
                                                 ((t2.RDF_Triple.p = rdf_type)
                                                    &&
                                                    (RDF_Term.subject_eq
                                                       t1.RDF_Triple.s
                                                       t2.RDF_Triple.s))
                                                   &&
                                                   (RDF_Term.rdf_term_eq
                                                      t2.RDF_Triple.o
                                                      comp.RDF_Triple.o)) g))
                                      g)) g in
                          if has_cls_com_clash
                          then true
                          else
                            FStar_List_Tot_Base.existsb
                              (fun rng ->
                                 (rng.RDF_Triple.p = rdfs_range) &&
                                   (match ((rng.RDF_Triple.s),
                                            (rng.RDF_Triple.o))
                                    with
                                    | (RDF_Term.S_IRI p, RDF_Term.T_IRI
                                       d_range) ->
                                        (FStar_List_Tot_Base.mem d_range
                                           xsd_all_datatypes)
                                          &&
                                          (FStar_List_Tot_Base.existsb
                                             (fun t ->
                                                (t.RDF_Triple.p = p) &&
                                                  (match t.RDF_Triple.o with
                                                   | RDF_Term.T_Literal lit
                                                       ->
                                                       ((FStar_List_Tot_Base.mem
                                                           lit.RDF_Term.datatype
                                                           xsd_all_datatypes)
                                                          &&
                                                          (Prims.op_Negation
                                                             (lit.RDF_Term.datatype
                                                                = d_range)))
                                                         &&
                                                         (Prims.op_Negation
                                                            (xsd_is_subtype
                                                               lit.RDF_Term.datatype
                                                               d_range))
                                                   | uu___9 -> false)) g)
                                    | (uu___9, uu___10) -> false)) g))))))))
let regime_rdf : Prims.string= "RDF"
let regime_rdfs : Prims.string= "RDFS"
let regime_owl_rl : Prims.string= "OWL-RL"
let regime_owl_direct : Prims.string= "OWL-Direct"
let entailment_closure (regime : Prims.string) (g : RDF_Graph.rdf_graph)
  (fuel : Prims.nat) : RDF_Graph.rdf_graph=
  if regime = regime_owl_rl
  then owl_rl_closure_with_reflexivity g fuel
  else
    if regime = regime_owl_direct
    then owl_rl_closure_with_reflexivity g fuel
    else
      if regime = regime_rdfs
      then rdfs_closure_with_reflexivity g fuel
      else if regime = regime_rdf then rdfs_closure g fuel else g
