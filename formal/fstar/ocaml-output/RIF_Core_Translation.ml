open Prims
let (rif_term_to_subject :
  RIF_Core_Syntax.rif_term ->
    SPARQL11_Algebra.pattern_subject FStar_Pervasives_Native.option)
  =
  fun t ->
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
let (rif_term_to_pattern :
  RIF_Core_Syntax.rif_term -> SPARQL11_Algebra.pattern_term) =
  fun t ->
    match t with
    | RIF_Core_Syntax.RIF_Var v ->
        SPARQL11_Algebra.PT_Var (v.RIF_Core_Syntax.var_name)
    | RIF_Core_Syntax.RIF_Const (RDF_Graph_Executable.T_IRI i) ->
        SPARQL11_Algebra.PT_IRI i
    | RIF_Core_Syntax.RIF_Const (RDF_Graph_Executable.T_BNode b) ->
        SPARQL11_Algebra.PT_BNode b
    | RIF_Core_Syntax.RIF_Const (RDF_Graph_Executable.T_Literal l) ->
        SPARQL11_Algebra.PT_Literal l
let (rif_rdf_type : RDF_Graph_Executable.wf_iri) =
  RDF_Graph_Executable.rdf_type
let (rif_rdfs_subclassof : RDF_Graph_Executable.wf_iri) =
  RDF_Graph_Executable.rdfs_subClassOf
let (translate_atom :
  RIF_Core_Syntax.rif_atom ->
    SPARQL11_Algebra.triple_pattern FStar_Pervasives_Native.option)
  =
  fun a ->
    match a with
    | RIF_Core_Syntax.RIF_Triple (s, p, o) ->
        (match rif_term_to_subject s with
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
                 SPARQL11_Algebra.tp_p =
                   (SPARQL11_Algebra.PT_IRI rif_rdf_type);
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
let rec (translate_body :
  RIF_Core_Syntax.rif_body ->
    SPARQL11_Algebra.bgp FStar_Pervasives_Native.option)
  =
  fun b ->
    match b with
    | RIF_Core_Syntax.RIF_BodyAtom a ->
        (match translate_atom a with
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some tp ->
             FStar_Pervasives_Native.Some [tp])
    | RIF_Core_Syntax.RIF_BodyAnd bs -> translate_body_list bs
and (translate_body_list :
  RIF_Core_Syntax.rif_body Prims.list ->
    SPARQL11_Algebra.bgp FStar_Pervasives_Native.option)
  =
  fun bs ->
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
let (translate_head :
  RIF_Core_Syntax.rif_atom ->
    SPARQL11_Algebra.triple_pattern Prims.list FStar_Pervasives_Native.option)
  =
  fun a ->
    match translate_atom a with
    | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
    | FStar_Pervasives_Native.Some tp -> FStar_Pervasives_Native.Some [tp]
let (translate_rule :
  RIF_Core_Syntax.rif_rule ->
    (SPARQL11_Algebra.triple_pattern Prims.list * SPARQL11_Algebra.bgp)
      FStar_Pervasives_Native.option)
  =
  fun r ->
    match translate_head r.RIF_Core_Syntax.head with
    | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
    | FStar_Pervasives_Native.Some hd_tpl ->
        (match translate_body r.RIF_Core_Syntax.body with
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some body_bgp ->
             FStar_Pervasives_Native.Some (hd_tpl, body_bgp))
let (translate_program :
  RIF_Core_Syntax.rif_program ->
    (SPARQL11_Algebra.triple_pattern Prims.list * SPARQL11_Algebra.bgp)
      Prims.list)
  =
  fun p ->
    let opt_pairs =
      FStar_List_Tot_Base.map translate_rule p.RIF_Core_Syntax.rules in
    let rec keep_some xs =
      match xs with
      | [] -> []
      | (FStar_Pervasives_Native.None)::rest -> keep_some rest
      | (FStar_Pervasives_Native.Some pr)::rest -> pr :: (keep_some rest) in
    keep_some opt_pairs
let (translate_program_diag :
  RIF_Core_Syntax.rif_program ->
    ((SPARQL11_Algebra.triple_pattern Prims.list * SPARQL11_Algebra.bgp)
      Prims.list * Prims.nat Prims.list))
  =
  fun p ->
    let rec aux rs idx acc_ok acc_err =
      match rs with
      | [] ->
          ((FStar_List_Tot_Base.rev acc_ok),
            (FStar_List_Tot_Base.rev acc_err))
      | r::rest ->
          (match translate_rule r with
           | FStar_Pervasives_Native.Some pr ->
               aux rest (idx + Prims.int_one) (pr :: acc_ok) acc_err
           | FStar_Pervasives_Native.None ->
               aux rest (idx + Prims.int_one) acc_ok (idx :: acc_err)) in
    aux p.RIF_Core_Syntax.rules Prims.int_zero [] []
