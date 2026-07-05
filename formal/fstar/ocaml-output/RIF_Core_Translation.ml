open Prims
let rif_term_to_subject (t : RIF_Core_Syntax.rif_term) :
  SPARQL11_Algebra.pattern_subject FStar_Pervasives_Native.option=
  match t with
  | RIF_Core_Syntax.RIF_Var v ->
      FStar_Pervasives_Native.Some
        (SPARQL11_Algebra.PS_Var (v.RIF_Core_Syntax.var_name))
  | RIF_Core_Syntax.RIF_Const (RDF_Graph_Executable.T_IRI i) ->
      FStar_Pervasives_Native.Some (SPARQL11_Algebra.PS_IRI i)
  | RIF_Core_Syntax.RIF_Const (RDF_Graph_Executable.T_BNode b) ->
      FStar_Pervasives_Native.Some (SPARQL11_Algebra.PS_BNode b)
  | RIF_Core_Syntax.RIF_Const (RDF_Graph_Executable.T_Literal uu___) ->
      FStar_Pervasives_Native.None
  | RIF_Core_Syntax.RIF_TermExternal (uu___, uu___1) ->
      FStar_Pervasives_Native.None
let rif_term_to_pattern (t : RIF_Core_Syntax.rif_term) :
  SPARQL11_Algebra.pattern_term=
  match t with
  | RIF_Core_Syntax.RIF_Var v ->
      SPARQL11_Algebra.PT_Var (v.RIF_Core_Syntax.var_name)
  | RIF_Core_Syntax.RIF_Const (RDF_Graph_Executable.T_IRI i) ->
      SPARQL11_Algebra.PT_IRI i
  | RIF_Core_Syntax.RIF_Const (RDF_Graph_Executable.T_BNode b) ->
      SPARQL11_Algebra.PT_BNode b
  | RIF_Core_Syntax.RIF_Const (RDF_Graph_Executable.T_Literal l) ->
      SPARQL11_Algebra.PT_Literal l
  | RIF_Core_Syntax.RIF_TermExternal (uu___, uu___1) ->
      SPARQL11_Algebra.PT_Var "$$unevaluated-external$$"
let rif_rdf_type : RDF_Graph_Executable.wf_iri= RDF_Graph_Executable.rdf_type
let rif_rdfs_subclassof : RDF_Graph_Executable.wf_iri=
  RDF_Graph_Executable.rdfs_subClassOf
let rif_uniterm_true_marker : RDF_Graph_Executable.rdf_term=
  RDF_Graph_Executable.T_Literal
    {
      RDF_Graph_Executable.lexical_form = "true";
      RDF_Graph_Executable.datatype = RDF_Graph_Executable.xsd_boolean;
      RDF_Graph_Executable.lang_tag = FStar_Pervasives_Native.None
    }
let rif_uniterm_nullary_subject : RDF_Graph_Executable.wf_iri=
  "urn:rif-nullary:subject"
let literal_subject_bnode_label (l : RDF_Graph_Executable.literal) :
  RDF_Graph_Executable.bnode_id=
  FStar_String.concat ""
    ["rif-litsubj:";
    l.RDF_Graph_Executable.datatype;
    ":";
    (match l.RDF_Graph_Executable.lang_tag with
     | FStar_Pervasives_Native.Some t -> t
     | FStar_Pervasives_Native.None -> "");
    ":";
    l.RDF_Graph_Executable.lexical_form]
let rif_term_to_uniterm_subject (t : RIF_Core_Syntax.rif_term) :
  SPARQL11_Algebra.pattern_subject FStar_Pervasives_Native.option=
  match t with
  | RIF_Core_Syntax.RIF_Var v ->
      FStar_Pervasives_Native.Some
        (SPARQL11_Algebra.PS_Var (v.RIF_Core_Syntax.var_name))
  | RIF_Core_Syntax.RIF_Const (RDF_Graph_Executable.T_IRI i) ->
      FStar_Pervasives_Native.Some (SPARQL11_Algebra.PS_IRI i)
  | RIF_Core_Syntax.RIF_Const (RDF_Graph_Executable.T_BNode b) ->
      FStar_Pervasives_Native.Some (SPARQL11_Algebra.PS_BNode b)
  | RIF_Core_Syntax.RIF_Const (RDF_Graph_Executable.T_Literal l) ->
      FStar_Pervasives_Native.Some
        (SPARQL11_Algebra.PS_BNode (literal_subject_bnode_label l))
  | RIF_Core_Syntax.RIF_TermExternal (uu___, uu___1) ->
      FStar_Pervasives_Native.None
let translate_atom (a : RIF_Core_Syntax.rif_atom) :
  SPARQL11_Algebra.triple_pattern FStar_Pervasives_Native.option=
  match a with
  | RIF_Core_Syntax.RIF_Triple (s, p, o) ->
      (match rif_term_to_uniterm_subject s with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some ps ->
           FStar_Pervasives_Native.Some
             {
               SPARQL11_Algebra.tp_s = ps;
               SPARQL11_Algebra.tp_p = (rif_term_to_pattern p);
               SPARQL11_Algebra.tp_o = (rif_term_to_pattern o)
             })
  | RIF_Core_Syntax.RIF_Frame (o, p, v) ->
      (match rif_term_to_subject o with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some ps ->
           FStar_Pervasives_Native.Some
             {
               SPARQL11_Algebra.tp_s = ps;
               SPARQL11_Algebra.tp_p = (rif_term_to_pattern p);
               SPARQL11_Algebra.tp_o = (rif_term_to_pattern v)
             })
  | RIF_Core_Syntax.RIF_Member (o, c) ->
      (match rif_term_to_subject o with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some ps ->
           FStar_Pervasives_Native.Some
             {
               SPARQL11_Algebra.tp_s = ps;
               SPARQL11_Algebra.tp_p = (SPARQL11_Algebra.PT_IRI rif_rdf_type);
               SPARQL11_Algebra.tp_o = (rif_term_to_pattern c)
             })
  | RIF_Core_Syntax.RIF_Sub (sub, sup_) ->
      (match rif_term_to_subject sub with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some ps ->
           FStar_Pervasives_Native.Some
             {
               SPARQL11_Algebra.tp_s = ps;
               SPARQL11_Algebra.tp_p =
                 (SPARQL11_Algebra.PT_IRI rif_rdfs_subclassof);
               SPARQL11_Algebra.tp_o = (rif_term_to_pattern sup_)
             })
  | RIF_Core_Syntax.RIF_Uniterm (pred, args) ->
      (match (pred, args) with
       | (RIF_Core_Syntax.RIF_Const (RDF_Graph_Executable.T_IRI pi), []) ->
           FStar_Pervasives_Native.Some
             {
               SPARQL11_Algebra.tp_s =
                 (SPARQL11_Algebra.PS_IRI rif_uniterm_nullary_subject);
               SPARQL11_Algebra.tp_p = (SPARQL11_Algebra.PT_IRI pi);
               SPARQL11_Algebra.tp_o =
                 (rif_term_to_pattern
                    (RIF_Core_Syntax.RIF_Const rif_uniterm_true_marker))
             }
       | (RIF_Core_Syntax.RIF_Const (RDF_Graph_Executable.T_IRI pi), a1::[])
           ->
           FStar_Pervasives_Native.Some
             {
               SPARQL11_Algebra.tp_s =
                 (SPARQL11_Algebra.PS_IRI rif_uniterm_nullary_subject);
               SPARQL11_Algebra.tp_p = (SPARQL11_Algebra.PT_IRI pi);
               SPARQL11_Algebra.tp_o = (rif_term_to_pattern a1)
             }
       | (uu___, uu___1) -> FStar_Pervasives_Native.None)
let rec translate_body (b : RIF_Core_Syntax.rif_body) :
  SPARQL11_Algebra.bgp FStar_Pervasives_Native.option=
  match b with
  | RIF_Core_Syntax.RIF_BodyAtom a ->
      (match translate_atom a with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some tp -> FStar_Pervasives_Native.Some [tp])
  | RIF_Core_Syntax.RIF_BodyAnd bs -> translate_body_list bs
  | RIF_Core_Syntax.RIF_BodyExternal (uu___, uu___1) ->
      FStar_Pervasives_Native.None
  | RIF_Core_Syntax.RIF_BodyEqual (uu___, uu___1) ->
      FStar_Pervasives_Native.None
and translate_body_list (bs : RIF_Core_Syntax.rif_body Prims.list) :
  SPARQL11_Algebra.bgp FStar_Pervasives_Native.option=
  match bs with
  | [] -> FStar_Pervasives_Native.Some []
  | b::rest ->
      (match translate_body b with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some bgp_b ->
           (match translate_body_list rest with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some bgp_rest ->
                FStar_Pervasives_Native.Some
                  (FStar_List_Tot_Base.append bgp_b bgp_rest)))
type rif_extra_condition =
  | EC_External of RDF_Graph_Executable.wf_iri * RIF_Core_Syntax.rif_term
  Prims.list 
  | EC_Equal of RIF_Core_Syntax.rif_term * RIF_Core_Syntax.rif_term 
let uu___is_EC_External (projectee : rif_extra_condition) : Prims.bool=
  match projectee with | EC_External (_0, _1) -> true | uu___ -> false
let __proj__EC_External__item___0 (projectee : rif_extra_condition) :
  RDF_Graph_Executable.wf_iri=
  match projectee with | EC_External (_0, _1) -> _0
let __proj__EC_External__item___1 (projectee : rif_extra_condition) :
  RIF_Core_Syntax.rif_term Prims.list=
  match projectee with | EC_External (_0, _1) -> _1
let uu___is_EC_Equal (projectee : rif_extra_condition) : Prims.bool=
  match projectee with | EC_Equal (_0, _1) -> true | uu___ -> false
let __proj__EC_Equal__item___0 (projectee : rif_extra_condition) :
  RIF_Core_Syntax.rif_term= match projectee with | EC_Equal (_0, _1) -> _0
let __proj__EC_Equal__item___1 (projectee : rif_extra_condition) :
  RIF_Core_Syntax.rif_term= match projectee with | EC_Equal (_0, _1) -> _1
let rec split_body (b : RIF_Core_Syntax.rif_body) :
  (RIF_Core_Syntax.rif_atom Prims.list * rif_extra_condition Prims.list)=
  match b with
  | RIF_Core_Syntax.RIF_BodyAtom a -> ([a], [])
  | RIF_Core_Syntax.RIF_BodyAnd bs -> split_body_list bs
  | RIF_Core_Syntax.RIF_BodyExternal (op, args) ->
      ([], [EC_External (op, args)])
  | RIF_Core_Syntax.RIF_BodyEqual (lhs, rhs) -> ([], [EC_Equal (lhs, rhs)])
and split_body_list (bs : RIF_Core_Syntax.rif_body Prims.list) :
  (RIF_Core_Syntax.rif_atom Prims.list * rif_extra_condition Prims.list)=
  match bs with
  | [] -> ([], [])
  | b::rest ->
      let uu___ = split_body b in
      (match uu___ with
       | (a1, e1) ->
           let uu___1 = split_body_list rest in
           (match uu___1 with
            | (a2, e2) ->
                ((FStar_List_Tot_Base.append a1 a2),
                  (FStar_List_Tot_Base.append e1 e2))))
let rec translate_atoms_bgp (atoms : RIF_Core_Syntax.rif_atom Prims.list) :
  SPARQL11_Algebra.bgp FStar_Pervasives_Native.option=
  match atoms with
  | [] -> FStar_Pervasives_Native.Some []
  | a::rest ->
      (match translate_atom a with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some tp ->
           (match translate_atoms_bgp rest with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some tps ->
                FStar_Pervasives_Native.Some (tp :: tps)))
let translate_head (a : RIF_Core_Syntax.rif_atom) :
  SPARQL11_Algebra.triple_pattern Prims.list FStar_Pervasives_Native.option=
  match translate_atom a with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some tp -> FStar_Pervasives_Native.Some [tp]
let translate_rule (r : RIF_Core_Syntax.rif_rule) :
  (SPARQL11_Algebra.triple_pattern Prims.list * SPARQL11_Algebra.bgp)
    FStar_Pervasives_Native.option=
  match translate_head r.RIF_Core_Syntax.head with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some hd_tpl ->
      (match translate_body r.RIF_Core_Syntax.body with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some body_bgp ->
           FStar_Pervasives_Native.Some (hd_tpl, body_bgp))
let translate_program (p : RIF_Core_Syntax.rif_program) :
  (SPARQL11_Algebra.triple_pattern Prims.list * SPARQL11_Algebra.bgp)
    Prims.list=
  let opt_pairs =
    FStar_List_Tot_Base.map translate_rule p.RIF_Core_Syntax.rules in
  let rec keep_some xs =
    match xs with
    | [] -> []
    | (FStar_Pervasives_Native.None)::rest -> keep_some rest
    | (FStar_Pervasives_Native.Some pr)::rest -> pr :: (keep_some rest) in
  keep_some opt_pairs
let translate_program_diag (p : RIF_Core_Syntax.rif_program) :
  ((SPARQL11_Algebra.triple_pattern Prims.list * SPARQL11_Algebra.bgp)
    Prims.list * Prims.nat Prims.list)=
  let rec aux rs idx acc_ok acc_err =
    match rs with
    | [] ->
        ((FStar_List_Tot_Base.rev acc_ok), (FStar_List_Tot_Base.rev acc_err))
    | r::rest ->
        (match translate_rule r with
         | FStar_Pervasives_Native.Some pr ->
             aux rest (idx + Prims.int_one) (pr :: acc_ok) acc_err
         | FStar_Pervasives_Native.None ->
             aux rest (idx + Prims.int_one) acc_ok (idx :: acc_err)) in
  aux p.RIF_Core_Syntax.rules Prims.int_zero [] []
