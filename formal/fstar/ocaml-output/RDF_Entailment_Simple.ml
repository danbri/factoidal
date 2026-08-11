open Prims
type binding = (Prims.string * RDF_Term.rdf_term) Prims.list
let subj_as_term (s : RDF_Term.subject) : RDF_Term.rdf_term=
  match s with
  | RDF_Term.S_IRI i -> RDF_Term.T_IRI i
  | RDF_Term.S_BNode b -> RDF_Term.T_BNode b
let match_subj (b : binding) (ps : RDF_Term.subject) (gs : RDF_Term.subject)
  : binding FStar_Pervasives_Native.option=
  match ps with
  | RDF_Term.S_BNode lbl ->
      (match FStar_List_Tot_Base.assoc lbl b with
       | FStar_Pervasives_Native.Some t ->
           if RDF_Term.rdf_term_eq t (subj_as_term gs)
           then FStar_Pervasives_Native.Some b
           else FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.None ->
           FStar_Pervasives_Native.Some ((lbl, (subj_as_term gs)) :: b))
  | RDF_Term.S_IRI i ->
      (match gs with
       | RDF_Term.S_IRI j ->
           if i = j
           then FStar_Pervasives_Native.Some b
           else FStar_Pervasives_Native.None
       | RDF_Term.S_BNode uu___ -> FStar_Pervasives_Native.None)
let rec match_term
  (leq : Prims.bool -> RDF_Term.literal -> RDF_Term.literal -> Prims.bool)
  (bnd : RDF_Term.rdf_term -> Prims.bool) (inside_tt : Prims.bool)
  (b : binding) (pat : RDF_Term.rdf_term) (g : RDF_Term.rdf_term) :
  binding FStar_Pervasives_Native.option=
  match pat with
  | RDF_Term.T_BNode lbl ->
      (match FStar_List_Tot_Base.assoc lbl b with
       | FStar_Pervasives_Native.Some t ->
           if RDF_Term.rdf_term_eq t g
           then FStar_Pervasives_Native.Some b
           else FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.None ->
           if bnd g
           then FStar_Pervasives_Native.Some ((lbl, g) :: b)
           else FStar_Pervasives_Native.None)
  | RDF_Term.T_IRI i ->
      (match g with
       | RDF_Term.T_IRI j ->
           if i = j
           then FStar_Pervasives_Native.Some b
           else FStar_Pervasives_Native.None
       | uu___ -> FStar_Pervasives_Native.None)
  | RDF_Term.T_Literal l ->
      (match g with
       | RDF_Term.T_Literal m ->
           if leq inside_tt l m
           then FStar_Pervasives_Native.Some b
           else FStar_Pervasives_Native.None
       | uu___ -> FStar_Pervasives_Native.None)
  | RDF_Term.T_TripleTerm (ps, pp, po) ->
      (match g with
       | RDF_Term.T_TripleTerm (gs, gp, go) ->
           if pp = gp
           then
             (match match_subj b ps gs with
              | FStar_Pervasives_Native.Some b1 ->
                  match_term leq bnd true b1 po go
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
           else FStar_Pervasives_Native.None
       | uu___ -> FStar_Pervasives_Native.None)
let match_triple
  (leq : Prims.bool -> RDF_Term.literal -> RDF_Term.literal -> Prims.bool)
  (bnd : RDF_Term.rdf_term -> Prims.bool) (b : binding)
  (tb : RDF_Triple.triple) (ta : RDF_Triple.triple) :
  binding FStar_Pervasives_Native.option=
  if tb.RDF_Triple.p = ta.RDF_Triple.p
  then
    match match_subj b tb.RDF_Triple.s ta.RDF_Triple.s with
    | FStar_Pervasives_Native.Some b1 ->
        match_term leq bnd false b1 tb.RDF_Triple.o ta.RDF_Triple.o
    | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  else FStar_Pervasives_Native.None
let rec try_match
  (leq : Prims.bool -> RDF_Term.literal -> RDF_Term.literal -> Prims.bool)
  (bnd : RDF_Term.rdf_term -> Prims.bool) (bs : RDF_Triple.triple Prims.list)
  (b : binding) (a : RDF_Triple.triple Prims.list) : Prims.bool=
  match bs with | [] -> true | tb::rest -> try_alts leq bnd bs tb rest b a a
and try_alts
  (leq : Prims.bool -> RDF_Term.literal -> RDF_Term.literal -> Prims.bool)
  (bnd : RDF_Term.rdf_term -> Prims.bool) (bs : RDF_Triple.triple Prims.list)
  (tb : RDF_Triple.triple) (rest : RDF_Triple.triple Prims.list)
  (b : binding) (a : RDF_Triple.triple Prims.list)
  (cand : RDF_Triple.triple Prims.list) : Prims.bool=
  match cand with
  | [] -> false
  | ta::more ->
      (match match_triple leq bnd b tb ta with
       | FStar_Pervasives_Native.Some b1 ->
           if try_match leq bnd rest b1 a
           then true
           else try_alts leq bnd bs tb rest b a more
       | FStar_Pervasives_Native.None -> try_alts leq bnd bs tb rest b a more)
let entails_with
  (leq : Prims.bool -> RDF_Term.literal -> RDF_Term.literal -> Prims.bool)
  (bnd : RDF_Term.rdf_term -> Prims.bool) (a : RDF_Triple.triple Prims.list)
  (b : RDF_Triple.triple Prims.list) : Prims.bool= try_match leq bnd b [] a
let simple_entails (a : RDF_Triple.triple Prims.list)
  (b : RDF_Triple.triple Prims.list) : Prims.bool=
  entails_with (fun uu___ l m -> RDF_Term.literal_term_eq l m)
    (fun uu___ -> true) a b
