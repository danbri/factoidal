open Prims
let resolve_term (mu : RDF_Graph_Executable.solution_mapping)
  (t : RIF_Core_Syntax.rif_term) :
  RDF_Graph_Executable.rdf_term FStar_Pervasives_Native.option=
  match t with
  | RIF_Core_Syntax.RIF_Const c -> FStar_Pervasives_Native.Some c
  | RIF_Core_Syntax.RIF_Var v ->
      SPARQL11_Algebra.sm_lookup v.RIF_Core_Syntax.var_name mu
let resolve_subject (mu : RDF_Graph_Executable.solution_mapping)
  (t : RIF_Core_Syntax.rif_term) :
  RDF_Graph_Executable.subject FStar_Pervasives_Native.option=
  match resolve_term mu t with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some (RDF_Graph_Executable.T_IRI i) ->
      FStar_Pervasives_Native.Some (RDF_Graph_Executable.S_IRI i)
  | FStar_Pervasives_Native.Some (RDF_Graph_Executable.T_BNode b) ->
      FStar_Pervasives_Native.Some (RDF_Graph_Executable.S_BNode b)
  | FStar_Pervasives_Native.Some (RDF_Graph_Executable.T_Literal uu___) ->
      FStar_Pervasives_Native.None
let resolve_predicate (mu : RDF_Graph_Executable.solution_mapping)
  (t : RIF_Core_Syntax.rif_term) :
  RDF_Graph_Executable.wf_iri FStar_Pervasives_Native.option=
  match resolve_term mu t with
  | FStar_Pervasives_Native.Some (RDF_Graph_Executable.T_IRI i) ->
      FStar_Pervasives_Native.Some i
  | uu___ -> FStar_Pervasives_Native.None
let mk_triple_opt
  (s_opt : RDF_Graph_Executable.subject FStar_Pervasives_Native.option)
  (p_opt : RDF_Graph_Executable.wf_iri FStar_Pervasives_Native.option)
  (o_opt : RDF_Graph_Executable.rdf_term FStar_Pervasives_Native.option) :
  RDF_Graph_Executable.triple FStar_Pervasives_Native.option=
  match (s_opt, p_opt, o_opt) with
  | (FStar_Pervasives_Native.Some s, FStar_Pervasives_Native.Some p,
     FStar_Pervasives_Native.Some o) ->
      FStar_Pervasives_Native.Some
        {
          RDF_Graph_Executable.s = s;
          RDF_Graph_Executable.p = p;
          RDF_Graph_Executable.o = o
        }
  | (uu___, uu___1, uu___2) -> FStar_Pervasives_Native.None
let instantiate_atom (mu : RDF_Graph_Executable.solution_mapping)
  (a : RIF_Core_Syntax.rif_atom) :
  RDF_Graph_Executable.triple FStar_Pervasives_Native.option=
  match a with
  | RIF_Core_Syntax.RIF_Triple (s, p, o) ->
      mk_triple_opt (resolve_subject mu s) (resolve_predicate mu p)
        (resolve_term mu o)
  | RIF_Core_Syntax.RIF_Frame (o, p, v) ->
      mk_triple_opt (resolve_subject mu o) (resolve_predicate mu p)
        (resolve_term mu v)
  | RIF_Core_Syntax.RIF_Member (o, c) ->
      mk_triple_opt (resolve_subject mu o)
        (FStar_Pervasives_Native.Some RDF_Graph_Executable.rdf_type)
        (resolve_term mu c)
  | RIF_Core_Syntax.RIF_Sub (sub, sup_) ->
      mk_triple_opt (resolve_subject mu sub)
        (FStar_Pervasives_Native.Some RDF_Graph_Executable.rdfs_subClassOf)
        (resolve_term mu sup_)
let add_one_triple_tracking (g : RDF_Graph_Executable.rdf_graph)
  (t : RDF_Graph_Executable.triple) (changed : Prims.bool) :
  (RDF_Graph_Executable.rdf_graph * Prims.bool)=
  if RDF_Graph_Executable.mem_triple t g
  then (g, changed)
  else ((FStar_List_Tot_Base.op_At g [t]), true)
let rec fire_head_per_bindings (head : RIF_Core_Syntax.rif_atom)
  (bindings : SPARQL11_Algebra.solution_sequence)
  (g : RDF_Graph_Executable.rdf_graph) (changed : Prims.bool) :
  (RDF_Graph_Executable.rdf_graph * Prims.bool)=
  match bindings with
  | [] -> (g, changed)
  | mu::rest ->
      let uu___ =
        match instantiate_atom mu head with
        | FStar_Pervasives_Native.None -> (g, changed)
        | FStar_Pervasives_Native.Some t ->
            add_one_triple_tracking g t changed in
      (match uu___ with
       | (g', changed') -> fire_head_per_bindings head rest g' changed')
let fire_rule (g : RDF_Graph_Executable.rdf_graph)
  (r : RIF_Core_Syntax.rif_rule) :
  (RDF_Graph_Executable.rdf_graph * Prims.bool)=
  match RIF_Core_Translation.translate_body r.RIF_Core_Syntax.body with
  | FStar_Pervasives_Native.None -> (g, false)
  | FStar_Pervasives_Native.Some body_bgp ->
      let bindings = SPARQL11_Algebra.eval_bgp body_bgp g in
      fire_head_per_bindings r.RIF_Core_Syntax.head bindings g false
let rec one_round_aux (rules : RIF_Core_Syntax.rif_rule Prims.list)
  (g : RDF_Graph_Executable.rdf_graph) (changed : Prims.bool) :
  (RDF_Graph_Executable.rdf_graph * Prims.bool)=
  match rules with
  | [] -> (g, changed)
  | r::rest ->
      let uu___ = fire_rule g r in
      (match uu___ with | (g', c') -> one_round_aux rest g' (changed || c'))
let one_round (g : RDF_Graph_Executable.rdf_graph)
  (p : RIF_Core_Syntax.rif_program) :
  (RDF_Graph_Executable.rdf_graph * Prims.bool)=
  one_round_aux p.RIF_Core_Syntax.rules g false
let rec fixpoint (g : RDF_Graph_Executable.rdf_graph)
  (p : RIF_Core_Syntax.rif_program) (fuel : Prims.nat) :
  RDF_Graph_Executable.rdf_graph=
  if fuel = Prims.int_zero
  then g
  else
    (let uu___1 = one_round g p in
     match uu___1 with
     | (g', changed) ->
         if Prims.op_Negation changed
         then g'
         else fixpoint g' p (fuel - Prims.int_one))
let saturate (g : RDF_Graph_Executable.rdf_graph)
  (p : RIF_Core_Syntax.rif_program) (fuel : Prims.nat) :
  RDF_Graph_Executable.rdf_graph= fixpoint g p fuel
type ('g1, 'g2) graph_subset = unit
let v_x : RIF_Core_Syntax.rif_term= RIF_Core_Syntax.mk_var "x"
let v_y : RIF_Core_Syntax.rif_term= RIF_Core_Syntax.mk_var "y"
let v_z : RIF_Core_Syntax.rif_term= RIF_Core_Syntax.mk_var "z"
let v_o : RIF_Core_Syntax.rif_term= RIF_Core_Syntax.mk_var "o"
let v_c : RIF_Core_Syntax.rif_term= RIF_Core_Syntax.mk_var "c"
let v_d : RIF_Core_Syntax.rif_term= RIF_Core_Syntax.mk_var "d"
let iri_alice : RDF_Graph_Executable.wf_iri= "ex:alice"
let iri_Student : RDF_Graph_Executable.wf_iri= "ex:Student"
let iri_Person : RDF_Graph_Executable.wf_iri= "ex:Person"
let iri_Agent : RDF_Graph_Executable.wf_iri= "ex:Agent"
let pred_subclassof : RIF_Core_Syntax.rif_term=
  RIF_Core_Syntax.mk_const_iri RDF_Graph_Executable.rdfs_subClassOf
let rule_subclassof_trans : RIF_Core_Syntax.rif_rule=
  RIF_Core_Syntax.mk_rule
    (RIF_Core_Syntax.RIF_Triple (v_x, pred_subclassof, v_z))
    (RIF_Core_Syntax.RIF_BodyAnd
       [RIF_Core_Syntax.RIF_BodyAtom
          (RIF_Core_Syntax.RIF_Triple (v_x, pred_subclassof, v_y));
       RIF_Core_Syntax.RIF_BodyAtom
         (RIF_Core_Syntax.RIF_Triple (v_y, pred_subclassof, v_z))])
let rule_type_prop : RIF_Core_Syntax.rif_rule=
  RIF_Core_Syntax.mk_rule (RIF_Core_Syntax.RIF_Member (v_o, v_d))
    (RIF_Core_Syntax.RIF_BodyAnd
       [RIF_Core_Syntax.RIF_BodyAtom (RIF_Core_Syntax.RIF_Member (v_o, v_c));
       RIF_Core_Syntax.RIF_BodyAtom
         (RIF_Core_Syntax.RIF_Triple (v_c, pred_subclassof, v_d))])
let smoke_program : RIF_Core_Syntax.rif_program=
  RIF_Core_Syntax.program_of_rules [rule_subclassof_trans; rule_type_prop]
let smoke_input_graph : RDF_Graph_Executable.rdf_graph=
  [{
     RDF_Graph_Executable.s = (RDF_Graph_Executable.S_IRI iri_alice);
     RDF_Graph_Executable.p = RDF_Graph_Executable.rdf_type;
     RDF_Graph_Executable.o = (RDF_Graph_Executable.T_IRI iri_Student)
   };
  {
    RDF_Graph_Executable.s = (RDF_Graph_Executable.S_IRI iri_Student);
    RDF_Graph_Executable.p = RDF_Graph_Executable.rdfs_subClassOf;
    RDF_Graph_Executable.o = (RDF_Graph_Executable.T_IRI iri_Person)
  };
  {
    RDF_Graph_Executable.s = (RDF_Graph_Executable.S_IRI iri_Person);
    RDF_Graph_Executable.p = RDF_Graph_Executable.rdfs_subClassOf;
    RDF_Graph_Executable.o = (RDF_Graph_Executable.T_IRI iri_Agent)
  }]
let smoke_saturated : RDF_Graph_Executable.rdf_graph=
  fixpoint smoke_input_graph smoke_program (Prims.of_int (8))
