open Prims
type rdf_graph = RDF_Triple.triple Prims.list
let empty_graph : rdf_graph= []
type named_graph = {
  ng_name: RDF_Term.iri ;
  ng_graph: rdf_graph }
let __proj__Mknamed_graph__item__ng_name (projectee : named_graph) :
  RDF_Term.iri= match projectee with | { ng_name; ng_graph;_} -> ng_name
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
let rec lookup_named_graph (name : RDF_Term.iri)
  (named : named_graph Prims.list) :
  rdf_graph FStar_Pervasives_Native.option=
  match named with
  | [] -> FStar_Pervasives_Native.None
  | ng::rest ->
      if ng.ng_name = name
      then FStar_Pervasives_Native.Some (ng.ng_graph)
      else lookup_named_graph name rest
let rec mem_triple (t : RDF_Triple.triple) (g : rdf_graph) : Prims.bool=
  match g with
  | [] -> false
  | hd::tl -> (RDF_Triple.triple_eq hd t) || (mem_triple t tl)
let graph_add (t : RDF_Triple.triple) (g : rdf_graph) : rdf_graph=
  if mem_triple t g then g else FStar_List_Tot_Base.op_At g [t]
let graph_len (g : rdf_graph) : Prims.nat= FStar_List_Tot_Base.length g
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
  | RDF_Term.T_TripleTerm (uu___, uu___1, uu___2) ->
      FStar_Pervasives_Native.None
let add_triple_if_new (g : rdf_graph) (t : RDF_Triple.triple) : rdf_graph=
  graph_add t g
let add_triple_unchecked (g : rdf_graph) (t : RDF_Triple.triple) : rdf_graph=
  t :: g
let lit_key_lang_part (l : RDF_Term.literal) : Prims.string=
  match l.RDF_Term.lang_tag with
  | FStar_Pervasives_Native.Some t -> Prims.strcat "@" t
  | FStar_Pervasives_Native.None -> ""
let lit_key_dir_part (l : RDF_Term.literal) : Prims.string=
  match l.RDF_Term.direction with
  | FStar_Pervasives_Native.Some (RDF_Term.Dir_LTR) -> "--ltr"
  | FStar_Pervasives_Native.Some (RDF_Term.Dir_RTL) -> "--rtl"
  | FStar_Pervasives_Native.None -> ""
let rec term_to_key_total (o : RDF_Term.rdf_term) : Prims.string=
  match o with
  | RDF_Term.T_IRI i -> Prims.strcat "I_" i
  | RDF_Term.T_BNode b -> Prims.strcat "B_" b
  | RDF_Term.T_Literal l ->
      Prims.strcat (Prims.strcat "L_" l.RDF_Term.lexical_form)
        (Prims.strcat RDF_Indexed.unit_sep
           (Prims.strcat l.RDF_Term.datatype
              (Prims.strcat RDF_Indexed.unit_sep
                 (Prims.strcat (lit_key_lang_part l)
                    (Prims.strcat RDF_Indexed.unit_sep (lit_key_dir_part l))))))
  | RDF_Term.T_TripleTerm (s, p, obj) ->
      Prims.strcat (Prims.strcat "T_" (RDF_Indexed.subject_to_key s))
        (Prims.strcat RDF_Indexed.unit_sep
           (Prims.strcat p
              (Prims.strcat RDF_Indexed.unit_sep (term_to_key_total obj))))
let triple_to_key (t : RDF_Triple.triple) : Prims.string=
  Prims.strcat (RDF_Indexed.subject_to_key t.RDF_Triple.s)
    (Prims.strcat RDF_Indexed.unit_sep
       (Prims.strcat t.RDF_Triple.p
          (Prims.strcat RDF_Indexed.unit_sep
             (term_to_key_total t.RDF_Triple.o))))
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
let cmp_decorated_triple (p1 : (Prims.string * RDF_Triple.triple))
  (p2 : (Prims.string * RDF_Triple.triple)) : Prims.int=
  FStar_String.compare (FStar_Pervasives_Native.fst p1)
    (FStar_Pervasives_Native.fst p2)
let rec dedup_sorted_decorated_aux
  (prev_key : Prims.string FStar_Pervasives_Native.option)
  (ts : (Prims.string * RDF_Triple.triple) Prims.list)
  (acc : RDF_Triple.triple Prims.list) : RDF_Triple.triple Prims.list=
  match ts with
  | [] -> FStar_List_Tot_Base.rev acc
  | (k, t)::rest ->
      let dup =
        match prev_key with
        | FStar_Pervasives_Native.Some p -> p = k
        | FStar_Pervasives_Native.None -> false in
      if dup
      then dedup_sorted_decorated_aux prev_key rest acc
      else
        dedup_sorted_decorated_aux (FStar_Pervasives_Native.Some k) rest (t
          :: acc)
let graph_dedup_sort (g : rdf_graph) : rdf_graph=
  let decorated = FStar_List_Tot_Base.map (fun t -> ((triple_to_key t), t)) g in
  let sorted = FStar_List_Tot_Base.sortWith cmp_decorated_triple decorated in
  dedup_sorted_decorated_aux FStar_Pervasives_Native.None sorted []
let rec add_triples_if_new (g : rdf_graph)
  (ts : RDF_Triple.triple Prims.list) : rdf_graph=
  match ts with
  | [] -> g
  | hd::tl -> add_triples_if_new (add_triple_if_new g hd) tl
let rec sorted_diff_aux (newer : RDF_Triple.triple Prims.list)
  (older : RDF_Triple.triple Prims.list) (acc : RDF_Triple.triple Prims.list)
  : RDF_Triple.triple Prims.list=
  match (newer, older) with
  | ([], uu___) -> FStar_List_Tot_Base.rev acc
  | (uu___, []) -> FStar_List_Tot_Base.rev_acc acc newer
  | (n::ns, o::os) ->
      let c = triple_cmp n o in
      if c < Prims.int_zero
      then sorted_diff_aux ns older (n :: acc)
      else
        if c = Prims.int_zero
        then sorted_diff_aux ns older acc
        else sorted_diff_aux newer os acc
let sorted_diff (newer : RDF_Triple.triple Prims.list)
  (older : RDF_Triple.triple Prims.list) : RDF_Triple.triple Prims.list=
  sorted_diff_aux newer older []
let add_triples_if_new_bulk (g : rdf_graph)
  (ts : RDF_Triple.triple Prims.list) : rdf_graph=
  match ts with
  | [] -> g
  | uu___ ->
      let fresh = sorted_diff (graph_dedup_sort ts) (graph_dedup_sort g) in
      FStar_List_Tot_Base.append g fresh
