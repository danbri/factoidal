open Prims
let rif_term_to_subject (t : RIF_Core_Syntax.rif_term) :
  SPARQL11_Algebra.pattern_subject FStar_Pervasives_Native.option=
  match t with
  | RIF_Core_Syntax.RIF_Var v ->
      FStar_Pervasives_Native.Some
        (SPARQL11_Algebra.PS_Var (v.RIF_Core_Syntax.var_name))
  | RIF_Core_Syntax.RIF_Const (RDF_Term.T_IRI i) ->
      FStar_Pervasives_Native.Some (SPARQL11_Algebra.PS_IRI i)
  | RIF_Core_Syntax.RIF_Const (RDF_Term.T_BNode b) ->
      FStar_Pervasives_Native.Some (SPARQL11_Algebra.PS_BNode b)
  | RIF_Core_Syntax.RIF_Const (RDF_Term.T_Literal uu___) ->
      FStar_Pervasives_Native.None
  | RIF_Core_Syntax.RIF_TermExternal (uu___, uu___1) ->
      FStar_Pervasives_Native.None
let rif_term_to_pattern (t : RIF_Core_Syntax.rif_term) :
  SPARQL11_Algebra.pattern_term=
  match t with
  | RIF_Core_Syntax.RIF_Var v ->
      SPARQL11_Algebra.PT_Var (v.RIF_Core_Syntax.var_name)
  | RIF_Core_Syntax.RIF_Const (RDF_Term.T_IRI i) -> SPARQL11_Algebra.PT_IRI i
  | RIF_Core_Syntax.RIF_Const (RDF_Term.T_BNode b) ->
      SPARQL11_Algebra.PT_BNode b
  | RIF_Core_Syntax.RIF_Const (RDF_Term.T_Literal l) ->
      SPARQL11_Algebra.PT_Literal l
  | RIF_Core_Syntax.RIF_TermExternal (uu___, uu___1) ->
      SPARQL11_Algebra.PT_Var "$$unevaluated-external$$"
let rif_rdf_type : RDF_Term.wf_iri= RDFS_Closure.rdf_type
let rif_rdfs_subclassof : RDF_Term.wf_iri= RDFS_Closure.rdfs_subClassOf
let rif_uniterm_true_marker : RDF_Term.rdf_term=
  RDF_Term.T_Literal
    {
      RDF_Term.lexical_form = "true";
      RDF_Term.datatype = RDF_Term.xsd_boolean;
      RDF_Term.lang_tag = FStar_Pervasives_Native.None
    }
let rif_uniterm_nullary_subject : RDF_Term.wf_iri= "urn:rif-nullary:subject"
let literal_subject_bnode_label (l : RDF_Term.literal) : RDF_Term.bnode_id=
  FStar_String.concat ""
    ["rif-litsubj:";
    l.RDF_Term.datatype;
    ":";
    (match l.RDF_Term.lang_tag with
     | FStar_Pervasives_Native.Some t -> t
     | FStar_Pervasives_Native.None -> "");
    ":";
    l.RDF_Term.lexical_form]
let rif_term_to_uniterm_subject (t : RIF_Core_Syntax.rif_term) :
  SPARQL11_Algebra.pattern_subject FStar_Pervasives_Native.option=
  match t with
  | RIF_Core_Syntax.RIF_Var v ->
      FStar_Pervasives_Native.Some
        (SPARQL11_Algebra.PS_Var (v.RIF_Core_Syntax.var_name))
  | RIF_Core_Syntax.RIF_Const (RDF_Term.T_IRI i) ->
      FStar_Pervasives_Native.Some (SPARQL11_Algebra.PS_IRI i)
  | RIF_Core_Syntax.RIF_Const (RDF_Term.T_BNode b) ->
      FStar_Pervasives_Native.Some (SPARQL11_Algebra.PS_BNode b)
  | RIF_Core_Syntax.RIF_Const (RDF_Term.T_Literal l) ->
      FStar_Pervasives_Native.Some
        (SPARQL11_Algebra.PS_BNode (literal_subject_bnode_label l))
  | RIF_Core_Syntax.RIF_TermExternal (uu___, uu___1) ->
      FStar_Pervasives_Native.None
let rif_uniterm_arg_pred (i : Prims.nat) : RDF_Term.wf_iri=
  let s =
    FStar_String.concat "" ["urn:rif-uniterm:arg"; Prims.string_of_int i] in
  if RDF_Term.is_iri s then s else rif_uniterm_nullary_subject
let uniterm_subject_anchor_var (v : Prims.string) : Prims.string=
  FStar_String.concat "" ["$$uniterm-subj$"; v]
let uniterm_anchor_var (idx : Prims.nat) : Prims.string=
  FStar_String.concat "" ["$$uniterm-anchor$"; Prims.string_of_int idx]
let rif_term_anchor_fragment (t : RDF_Term.rdf_term) : Prims.string=
  match t with
  | RDF_Term.T_IRI i -> FStar_String.concat "" ["i:"; i]
  | RDF_Term.T_BNode b -> FStar_String.concat "" ["b:"; b]
  | RDF_Term.T_Literal l ->
      FStar_String.concat ""
        ["l:";
        l.RDF_Term.datatype;
        ":";
        (match l.RDF_Term.lang_tag with
         | FStar_Pervasives_Native.Some tg -> tg
         | FStar_Pervasives_Native.None -> "");
        ":";
        l.RDF_Term.lexical_form]
let rec anchor_fragments (ts : RDF_Term.rdf_term Prims.list) :
  Prims.string Prims.list=
  match ts with
  | [] -> []
  | t::rest -> (rif_term_anchor_fragment t) :: (anchor_fragments rest)
let nary_fact_anchor_label (p : RDF_Term.wf_iri)
  (args : RDF_Term.rdf_term Prims.list) : RDF_Term.bnode_id=
  FStar_String.concat ""
    ["rif-uniterm-fact:";
    p;
    "|";
    FStar_String.concat "|" (anchor_fragments args)]
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
       | (RIF_Core_Syntax.RIF_Const (RDF_Term.T_IRI pi), []) ->
           FStar_Pervasives_Native.Some
             {
               SPARQL11_Algebra.tp_s =
                 (SPARQL11_Algebra.PS_IRI rif_uniterm_nullary_subject);
               SPARQL11_Algebra.tp_p = (SPARQL11_Algebra.PT_IRI pi);
               SPARQL11_Algebra.tp_o =
                 (rif_term_to_pattern
                    (RIF_Core_Syntax.RIF_Const rif_uniterm_true_marker))
             }
       | (RIF_Core_Syntax.RIF_Const (RDF_Term.T_IRI pi), a1::[]) ->
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
  | EC_External of RDF_Term.wf_iri * RIF_Core_Syntax.rif_term Prims.list 
  | EC_Equal of RIF_Core_Syntax.rif_term * RIF_Core_Syntax.rif_term 
let uu___is_EC_External (projectee : rif_extra_condition) : Prims.bool=
  match projectee with | EC_External (_0, _1) -> true | uu___ -> false
let __proj__EC_External__item___0 (projectee : rif_extra_condition) :
  RDF_Term.wf_iri= match projectee with | EC_External (_0, _1) -> _0
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
let rec nary_arg_patterns (anchor : Prims.string)
  (args : RIF_Core_Syntax.rif_term Prims.list) (i : Prims.nat) :
  SPARQL11_Algebra.triple_pattern Prims.list=
  match args with
  | [] -> []
  | a::rest ->
      {
        SPARQL11_Algebra.tp_s = (SPARQL11_Algebra.PS_Var anchor);
        SPARQL11_Algebra.tp_p =
          (SPARQL11_Algebra.PT_IRI (rif_uniterm_arg_pred i));
        SPARQL11_Algebra.tp_o = (rif_term_to_pattern a)
      } :: (nary_arg_patterns anchor rest (i + Prims.int_one))
let translate_atom_bgp (idx : Prims.nat) (a : RIF_Core_Syntax.rif_atom) :
  SPARQL11_Algebra.bgp FStar_Pervasives_Native.option=
  match a with
  | RIF_Core_Syntax.RIF_Triple (RIF_Core_Syntax.RIF_Var v, p, o) ->
      let anchor = uniterm_subject_anchor_var v.RIF_Core_Syntax.var_name in
      FStar_Pervasives_Native.Some
        [{
           SPARQL11_Algebra.tp_s = (SPARQL11_Algebra.PS_Var anchor);
           SPARQL11_Algebra.tp_p = (rif_term_to_pattern p);
           SPARQL11_Algebra.tp_o = (rif_term_to_pattern o)
         };
        {
          SPARQL11_Algebra.tp_s = (SPARQL11_Algebra.PS_Var anchor);
          SPARQL11_Algebra.tp_p =
            (SPARQL11_Algebra.PT_IRI (rif_uniterm_arg_pred Prims.int_one));
          SPARQL11_Algebra.tp_o =
            (SPARQL11_Algebra.PT_Var (v.RIF_Core_Syntax.var_name))
        }]
  | RIF_Core_Syntax.RIF_Uniterm
      (RIF_Core_Syntax.RIF_Const (RDF_Term.T_IRI pi), args) ->
      if (FStar_List_Tot_Base.length args) >= (Prims.of_int (3))
      then
        let anchor = uniterm_anchor_var idx in
        FStar_Pervasives_Native.Some
          ({
             SPARQL11_Algebra.tp_s = (SPARQL11_Algebra.PS_Var anchor);
             SPARQL11_Algebra.tp_p = (SPARQL11_Algebra.PT_IRI pi);
             SPARQL11_Algebra.tp_o =
               (rif_term_to_pattern
                  (RIF_Core_Syntax.RIF_Const rif_uniterm_true_marker))
           }
          :: (nary_arg_patterns anchor args Prims.int_one))
      else
        (match translate_atom a with
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some tp ->
             FStar_Pervasives_Native.Some [tp])
  | uu___ ->
      (match translate_atom a with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some tp -> FStar_Pervasives_Native.Some [tp])
let rec translate_atoms_bgp_idx (atoms : RIF_Core_Syntax.rif_atom Prims.list)
  (idx : Prims.nat) : SPARQL11_Algebra.bgp FStar_Pervasives_Native.option=
  match atoms with
  | [] -> FStar_Pervasives_Native.Some []
  | a::rest ->
      (match translate_atom_bgp idx a with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some tps ->
           (match translate_atoms_bgp_idx rest (idx + Prims.int_one) with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some more ->
                FStar_Pervasives_Native.Some
                  (FStar_List_Tot_Base.append tps more)))
let translate_atoms_bgp (atoms : RIF_Core_Syntax.rif_atom Prims.list) :
  SPARQL11_Algebra.bgp FStar_Pervasives_Native.option=
  translate_atoms_bgp_idx atoms Prims.int_zero
let triple_to_pattern (t : RDF_Triple.triple) :
  SPARQL11_Algebra.triple_pattern=
  {
    SPARQL11_Algebra.tp_s =
      (match t.RDF_Triple.s with
       | RDF_Term.S_IRI i -> SPARQL11_Algebra.PS_IRI i
       | RDF_Term.S_BNode b -> SPARQL11_Algebra.PS_BNode b);
    SPARQL11_Algebra.tp_p = (SPARQL11_Algebra.PT_IRI (t.RDF_Triple.p));
    SPARQL11_Algebra.tp_o =
      (match t.RDF_Triple.o with
       | RDF_Term.T_IRI i -> SPARQL11_Algebra.PT_IRI i
       | RDF_Term.T_BNode b -> SPARQL11_Algebra.PT_BNode b
       | RDF_Term.T_Literal l -> SPARQL11_Algebra.PT_Literal l)
  }
let graph_to_bgp (g : RDF_Graph.rdf_graph) : SPARQL11_Algebra.bgp=
  FStar_List_Tot_Base.map triple_to_pattern g
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
