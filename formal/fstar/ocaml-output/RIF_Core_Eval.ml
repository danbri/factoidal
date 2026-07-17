open Prims
let rec eval_rif_term (mu : RDF_Graph_Executable.solution_mapping)
  (t : RIF_Core_Syntax.rif_term) :
  RDF_Term.rdf_term FStar_Pervasives_Native.option=
  match t with
  | RIF_Core_Syntax.RIF_Const c -> FStar_Pervasives_Native.Some c
  | RIF_Core_Syntax.RIF_Var v ->
      SPARQL11_Algebra.sm_lookup v.RIF_Core_Syntax.var_name mu
  | RIF_Core_Syntax.RIF_TermExternal (op, args) ->
      (match eval_rif_term_list mu args with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some vals ->
           RIF_Core_Builtins.eval_function op vals)
and eval_rif_term_list (mu : RDF_Graph_Executable.solution_mapping)
  (ts : RIF_Core_Syntax.rif_term Prims.list) :
  RDF_Term.rdf_term Prims.list FStar_Pervasives_Native.option=
  match ts with
  | [] -> FStar_Pervasives_Native.Some []
  | t::rest ->
      (match eval_rif_term mu t with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some v ->
           (match eval_rif_term_list mu rest with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some vs ->
                FStar_Pervasives_Native.Some (v :: vs)))
let resolve_term (mu : RDF_Graph_Executable.solution_mapping)
  (t : RIF_Core_Syntax.rif_term) :
  RDF_Term.rdf_term FStar_Pervasives_Native.option= eval_rif_term mu t
let resolve_subject (mu : RDF_Graph_Executable.solution_mapping)
  (t : RIF_Core_Syntax.rif_term) :
  RDF_Term.subject FStar_Pervasives_Native.option=
  match resolve_term mu t with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some (RDF_Term.T_IRI i) ->
      FStar_Pervasives_Native.Some (RDF_Term.S_IRI i)
  | FStar_Pervasives_Native.Some (RDF_Term.T_BNode b) ->
      FStar_Pervasives_Native.Some (RDF_Term.S_BNode b)
  | FStar_Pervasives_Native.Some (RDF_Term.T_Literal uu___) ->
      FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some (RDF_Term.T_TripleTerm
      (uu___, uu___1, uu___2)) -> FStar_Pervasives_Native.None
let resolve_predicate (mu : RDF_Graph_Executable.solution_mapping)
  (t : RIF_Core_Syntax.rif_term) :
  RDF_Term.wf_iri FStar_Pervasives_Native.option=
  match resolve_term mu t with
  | FStar_Pervasives_Native.Some (RDF_Term.T_IRI i) ->
      FStar_Pervasives_Native.Some i
  | uu___ -> FStar_Pervasives_Native.None
let resolve_uniterm_subject (mu : RDF_Graph_Executable.solution_mapping)
  (t : RIF_Core_Syntax.rif_term) :
  RDF_Term.subject FStar_Pervasives_Native.option=
  match resolve_term mu t with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some (RDF_Term.T_IRI i) ->
      FStar_Pervasives_Native.Some (RDF_Term.S_IRI i)
  | FStar_Pervasives_Native.Some (RDF_Term.T_BNode b) ->
      FStar_Pervasives_Native.Some (RDF_Term.S_BNode b)
  | FStar_Pervasives_Native.Some (RDF_Term.T_Literal l) ->
      FStar_Pervasives_Native.Some
        (RDF_Term.S_BNode
           (RIF_Core_Translation.literal_subject_bnode_label l))
  | FStar_Pervasives_Native.Some (RDF_Term.T_TripleTerm
      (uu___, uu___1, uu___2)) -> FStar_Pervasives_Native.None
let mk_triple_opt (s_opt : RDF_Term.subject FStar_Pervasives_Native.option)
  (p_opt : RDF_Term.wf_iri FStar_Pervasives_Native.option)
  (o_opt : RDF_Term.rdf_term FStar_Pervasives_Native.option) :
  RDF_Triple.triple FStar_Pervasives_Native.option=
  match (s_opt, p_opt, o_opt) with
  | (FStar_Pervasives_Native.Some s, FStar_Pervasives_Native.Some p,
     FStar_Pervasives_Native.Some o) ->
      FStar_Pervasives_Native.Some
        { RDF_Triple.s = s; RDF_Triple.p = p; RDF_Triple.o = o }
  | (uu___, uu___1, uu___2) -> FStar_Pervasives_Native.None
let instantiate_atom (mu : RDF_Graph_Executable.solution_mapping)
  (a : RIF_Core_Syntax.rif_atom) :
  RDF_Triple.triple FStar_Pervasives_Native.option=
  match a with
  | RIF_Core_Syntax.RIF_Triple (s, p, o) ->
      mk_triple_opt (resolve_uniterm_subject mu s) (resolve_predicate mu p)
        (resolve_term mu o)
  | RIF_Core_Syntax.RIF_Frame (o, p, v) ->
      mk_triple_opt (resolve_subject mu o) (resolve_predicate mu p)
        (resolve_term mu v)
  | RIF_Core_Syntax.RIF_Member (o, c) ->
      mk_triple_opt (resolve_subject mu o)
        (FStar_Pervasives_Native.Some RDFS_Closure.rdf_type)
        (resolve_term mu c)
  | RIF_Core_Syntax.RIF_Sub (sub, sup_) ->
      mk_triple_opt (resolve_subject mu sub)
        (FStar_Pervasives_Native.Some RDFS_Closure.rdfs_subClassOf)
        (resolve_term mu sup_)
  | RIF_Core_Syntax.RIF_Uniterm (pred, args) ->
      (match ((resolve_predicate mu pred), args) with
       | (FStar_Pervasives_Native.Some p, []) ->
           mk_triple_opt
             (FStar_Pervasives_Native.Some
                (RDF_Term.S_IRI
                   RIF_Core_Translation.rif_uniterm_nullary_subject))
             (FStar_Pervasives_Native.Some p)
             (FStar_Pervasives_Native.Some
                RIF_Core_Translation.rif_uniterm_true_marker)
       | (FStar_Pervasives_Native.Some p, a1::[]) ->
           mk_triple_opt
             (FStar_Pervasives_Native.Some
                (RDF_Term.S_IRI
                   RIF_Core_Translation.rif_uniterm_nullary_subject))
             (FStar_Pervasives_Native.Some p) (resolve_term mu a1)
       | (uu___, uu___1) -> FStar_Pervasives_Native.None)
let rec arg_value_satellites (anchor : RDF_Term.subject)
  (vals : RDF_Term.rdf_term Prims.list) (i : Prims.nat) :
  RDF_Triple.triple Prims.list=
  match vals with
  | [] -> []
  | v::rest ->
      {
        RDF_Triple.s = anchor;
        RDF_Triple.p = (RIF_Core_Translation.rif_uniterm_arg_pred i);
        RDF_Triple.o = v
      } :: (arg_value_satellites anchor rest (i + Prims.int_one))
let instantiate_atom_all (mu : RDF_Graph_Executable.solution_mapping)
  (a : RIF_Core_Syntax.rif_atom) : RDF_Triple.triple Prims.list=
  match a with
  | RIF_Core_Syntax.RIF_Triple (s, uu___, uu___1) ->
      (match instantiate_atom mu a with
       | FStar_Pervasives_Native.None -> []
       | FStar_Pervasives_Native.Some t ->
           (match ((resolve_uniterm_subject mu s), (resolve_term mu s)) with
            | (FStar_Pervasives_Native.Some subj,
               FStar_Pervasives_Native.Some sval) ->
                [t;
                {
                  RDF_Triple.s = subj;
                  RDF_Triple.p =
                    (RIF_Core_Translation.rif_uniterm_arg_pred Prims.int_one);
                  RDF_Triple.o = sval
                }]
            | (uu___2, uu___3) -> [t]))
  | RIF_Core_Syntax.RIF_Uniterm (pred, args) ->
      if (FStar_List_Tot_Base.length args) >= (Prims.of_int (3))
      then
        (match ((resolve_predicate mu pred), (eval_rif_term_list mu args))
         with
         | (FStar_Pervasives_Native.Some p, FStar_Pervasives_Native.Some
            vals) ->
             let anchor =
               RDF_Term.S_BNode
                 (RIF_Core_Translation.nary_fact_anchor_label p vals) in
             {
               RDF_Triple.s = anchor;
               RDF_Triple.p = p;
               RDF_Triple.o = RIF_Core_Translation.rif_uniterm_true_marker
             } :: (arg_value_satellites anchor vals Prims.int_one)
         | (uu___, uu___1) -> [])
      else
        (match instantiate_atom mu a with
         | FStar_Pervasives_Native.None -> []
         | FStar_Pervasives_Native.Some t -> [t])
  | uu___ ->
      (match instantiate_atom mu a with
       | FStar_Pervasives_Native.None -> []
       | FStar_Pervasives_Native.Some t -> [t])
let add_one_triple_tracking (g : RDF_Graph.rdf_graph) (t : RDF_Triple.triple)
  (changed : Prims.bool) : (RDF_Graph.rdf_graph * Prims.bool)=
  if RDF_Graph.mem_triple t g
  then (g, changed)
  else ((FStar_List_Tot_Base.op_At g [t]), true)
let rec add_triples_tracking (g : RDF_Graph.rdf_graph)
  (ts : RDF_Triple.triple Prims.list) (changed : Prims.bool) :
  (RDF_Graph.rdf_graph * Prims.bool)=
  match ts with
  | [] -> (g, changed)
  | t::rest ->
      let uu___ = add_one_triple_tracking g t changed in
      (match uu___ with | (g', c') -> add_triples_tracking g' rest c')
let rec fire_head_per_bindings (head : RIF_Core_Syntax.rif_atom)
  (bindings : SPARQL11_Algebra.solution_sequence) (g : RDF_Graph.rdf_graph)
  (changed : Prims.bool) : (RDF_Graph.rdf_graph * Prims.bool)=
  match bindings with
  | [] -> (g, changed)
  | mu::rest ->
      let uu___ =
        add_triples_tracking g (instantiate_atom_all mu head) changed in
      (match uu___ with
       | (g', changed') -> fire_head_per_bindings head rest g' changed')
let rif_equal_values (a : RDF_Term.rdf_term) (b : RDF_Term.rdf_term) :
  Prims.bool=
  match RIF_Core_Builtins.numeric_predicate SPARQL11_Algebra.CmpEq a b with
  | FStar_Pervasives_Native.Some r -> r
  | FStar_Pervasives_Native.None ->
      (match RIF_Core_Builtins.string_family_value_equal a b with
       | FStar_Pervasives_Native.Some r -> r
       | FStar_Pervasives_Native.None -> RDF_Term.rdf_term_eq a b)
let apply_iri_string_binding (mu : RDF_Graph_Executable.solution_mapping)
  (a1 : RIF_Core_Syntax.rif_term) (a2 : RIF_Core_Syntax.rif_term) :
  RDF_Graph_Executable.solution_mapping FStar_Pervasives_Native.option=
  match ((eval_rif_term mu a1), (eval_rif_term mu a2)) with
  | (FStar_Pervasives_Native.Some v1, FStar_Pervasives_Native.Some v2) ->
      (match RIF_Core_Builtins.eval_predicate
               RIF_Core_Builtins.rif_pred_iri_string [v1; v2]
       with
       | FStar_Pervasives_Native.Some true -> FStar_Pervasives_Native.Some mu
       | uu___ -> FStar_Pervasives_Native.None)
  | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.Some v2) ->
      (match a1 with
       | RIF_Core_Syntax.RIF_Var v ->
           (match v2 with
            | RDF_Term.T_Literal l ->
                if
                  (RIF_Core_Builtins.is_string_family_dt l.RDF_Term.datatype)
                    && (RDF_Term.is_iri l.RDF_Term.lexical_form)
                then
                  FStar_Pervasives_Native.Some
                    (SPARQL11_Algebra.sm_bind v.RIF_Core_Syntax.var_name
                       (RDF_Term.T_IRI (l.RDF_Term.lexical_form)) mu)
                else FStar_Pervasives_Native.None
            | uu___ -> FStar_Pervasives_Native.None)
       | uu___ -> FStar_Pervasives_Native.None)
  | (FStar_Pervasives_Native.Some v1, FStar_Pervasives_Native.None) ->
      (match a2 with
       | RIF_Core_Syntax.RIF_Var v ->
           (match v1 with
            | RDF_Term.T_IRI i ->
                FStar_Pervasives_Native.Some
                  (SPARQL11_Algebra.sm_bind v.RIF_Core_Syntax.var_name
                     (RIF_Core_Builtins.mk_string_literal i) mu)
            | uu___ -> FStar_Pervasives_Native.None)
       | uu___ -> FStar_Pervasives_Native.None)
  | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) ->
      FStar_Pervasives_Native.None
let apply_extra_condition (mu : RDF_Graph_Executable.solution_mapping)
  (ec : RIF_Core_Translation.rif_extra_condition) :
  RDF_Graph_Executable.solution_mapping FStar_Pervasives_Native.option=
  match ec with
  | RIF_Core_Translation.EC_External (op, args) ->
      if op = RIF_Core_Builtins.rif_pred_iri_string
      then
        (match args with
         | a1::a2::[] -> apply_iri_string_binding mu a1 a2
         | uu___ -> FStar_Pervasives_Native.None)
      else
        (match eval_rif_term_list mu args with
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some vals ->
             (match RIF_Core_Builtins.eval_predicate op vals with
              | FStar_Pervasives_Native.Some true ->
                  FStar_Pervasives_Native.Some mu
              | FStar_Pervasives_Native.Some false ->
                  FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None))
  | RIF_Core_Translation.EC_Equal (lhs, rhs) ->
      (match lhs with
       | RIF_Core_Syntax.RIF_Var v ->
           (match SPARQL11_Algebra.sm_lookup v.RIF_Core_Syntax.var_name mu
            with
            | FStar_Pervasives_Native.None ->
                (match eval_rif_term mu rhs with
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.None
                 | FStar_Pervasives_Native.Some rv ->
                     FStar_Pervasives_Native.Some
                       (SPARQL11_Algebra.sm_bind v.RIF_Core_Syntax.var_name
                          rv mu))
            | FStar_Pervasives_Native.Some existing ->
                (match eval_rif_term mu rhs with
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.None
                 | FStar_Pervasives_Native.Some rv ->
                     if rif_equal_values existing rv
                     then FStar_Pervasives_Native.Some mu
                     else FStar_Pervasives_Native.None))
       | uu___ ->
           (match ((eval_rif_term mu lhs), (eval_rif_term mu rhs)) with
            | (FStar_Pervasives_Native.Some lv, FStar_Pervasives_Native.Some
               rv) ->
                if rif_equal_values lv rv
                then FStar_Pervasives_Native.Some mu
                else FStar_Pervasives_Native.None
            | (uu___1, uu___2) -> FStar_Pervasives_Native.None))
let rec apply_extra_conditions (mu : RDF_Graph_Executable.solution_mapping)
  (ecs : RIF_Core_Translation.rif_extra_condition Prims.list) :
  RDF_Graph_Executable.solution_mapping FStar_Pervasives_Native.option=
  match ecs with
  | [] -> FStar_Pervasives_Native.Some mu
  | ec::rest ->
      (match apply_extra_condition mu ec with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some mu' -> apply_extra_conditions mu' rest)
let rec filter_bindings_by_extras
  (ecs : RIF_Core_Translation.rif_extra_condition Prims.list)
  (bindings : SPARQL11_Algebra.solution_sequence) :
  SPARQL11_Algebra.solution_sequence=
  match bindings with
  | [] -> []
  | mu::rest ->
      (match apply_extra_conditions mu ecs with
       | FStar_Pervasives_Native.Some mu' -> mu' ::
           (filter_bindings_by_extras ecs rest)
       | FStar_Pervasives_Native.None -> filter_bindings_by_extras ecs rest)
let fire_rule (g : RDF_Graph.rdf_graph) (r : RIF_Core_Syntax.rif_rule) :
  (RDF_Graph.rdf_graph * Prims.bool)=
  let uu___ = RIF_Core_Translation.split_body r.RIF_Core_Syntax.body in
  match uu___ with
  | (ordinary_atoms, extras) ->
      (match RIF_Core_Translation.translate_atoms_bgp ordinary_atoms with
       | FStar_Pervasives_Native.None -> (g, false)
       | FStar_Pervasives_Native.Some body_bgp ->
           let bindings0 = SPARQL11_Algebra.eval_bgp body_bgp g in
           let bindings1 = filter_bindings_by_extras extras bindings0 in
           fire_head_per_bindings r.RIF_Core_Syntax.head bindings1 g false)
let rec one_round_aux (rules : RIF_Core_Syntax.rif_rule Prims.list)
  (g : RDF_Graph.rdf_graph) (changed : Prims.bool) :
  (RDF_Graph.rdf_graph * Prims.bool)=
  match rules with
  | [] -> (g, changed)
  | r::rest ->
      let uu___ = fire_rule g r in
      (match uu___ with | (g', c') -> one_round_aux rest g' (changed || c'))
let one_round (g : RDF_Graph.rdf_graph) (p : RIF_Core_Syntax.rif_program) :
  (RDF_Graph.rdf_graph * Prims.bool)=
  one_round_aux p.RIF_Core_Syntax.rules g false
let rec fixpoint (g : RDF_Graph.rdf_graph) (p : RIF_Core_Syntax.rif_program)
  (fuel : Prims.nat) : RDF_Graph.rdf_graph=
  if fuel = Prims.int_zero
  then g
  else
    (let uu___1 = one_round g p in
     match uu___1 with
     | (g', changed) ->
         if Prims.op_Negation changed
         then g'
         else fixpoint g' p (fuel - Prims.int_one))
let saturate (g : RDF_Graph.rdf_graph) (p : RIF_Core_Syntax.rif_program)
  (fuel : Prims.nat) : RDF_Graph.rdf_graph= fixpoint g p fuel
type ('g1, 'g2) graph_subset = unit
let v_x : RIF_Core_Syntax.rif_term= RIF_Core_Syntax.mk_var "x"
let v_y : RIF_Core_Syntax.rif_term= RIF_Core_Syntax.mk_var "y"
let v_z : RIF_Core_Syntax.rif_term= RIF_Core_Syntax.mk_var "z"
let v_o : RIF_Core_Syntax.rif_term= RIF_Core_Syntax.mk_var "o"
let v_c : RIF_Core_Syntax.rif_term= RIF_Core_Syntax.mk_var "c"
let v_d : RIF_Core_Syntax.rif_term= RIF_Core_Syntax.mk_var "d"
let iri_alice : RDF_Term.wf_iri= "ex:alice"
let iri_Student : RDF_Term.wf_iri= "ex:Student"
let iri_Person : RDF_Term.wf_iri= "ex:Person"
let iri_Agent : RDF_Term.wf_iri= "ex:Agent"
let pred_subclassof : RIF_Core_Syntax.rif_term=
  RIF_Core_Syntax.mk_const_iri RDFS_Closure.rdfs_subClassOf
let rule_subclassof_trans : RIF_Core_Syntax.rif_rule=
  RIF_Core_Syntax.mk_rule
    (RIF_Core_Syntax.RIF_Frame (v_x, pred_subclassof, v_z))
    (RIF_Core_Syntax.RIF_BodyAnd
       [RIF_Core_Syntax.RIF_BodyAtom
          (RIF_Core_Syntax.RIF_Frame (v_x, pred_subclassof, v_y));
       RIF_Core_Syntax.RIF_BodyAtom
         (RIF_Core_Syntax.RIF_Frame (v_y, pred_subclassof, v_z))])
let rule_type_prop : RIF_Core_Syntax.rif_rule=
  RIF_Core_Syntax.mk_rule (RIF_Core_Syntax.RIF_Member (v_o, v_d))
    (RIF_Core_Syntax.RIF_BodyAnd
       [RIF_Core_Syntax.RIF_BodyAtom (RIF_Core_Syntax.RIF_Member (v_o, v_c));
       RIF_Core_Syntax.RIF_BodyAtom
         (RIF_Core_Syntax.RIF_Frame (v_c, pred_subclassof, v_d))])
let smoke_program : RIF_Core_Syntax.rif_program=
  RIF_Core_Syntax.program_of_rules [rule_subclassof_trans; rule_type_prop]
let smoke_input_graph : RDF_Graph.rdf_graph=
  [{
     RDF_Triple.s = (RDF_Term.S_IRI iri_alice);
     RDF_Triple.p = RDFS_Closure.rdf_type;
     RDF_Triple.o = (RDF_Term.T_IRI iri_Student)
   };
  {
    RDF_Triple.s = (RDF_Term.S_IRI iri_Student);
    RDF_Triple.p = RDFS_Closure.rdfs_subClassOf;
    RDF_Triple.o = (RDF_Term.T_IRI iri_Person)
  };
  {
    RDF_Triple.s = (RDF_Term.S_IRI iri_Person);
    RDF_Triple.p = RDFS_Closure.rdfs_subClassOf;
    RDF_Triple.o = (RDF_Term.T_IRI iri_Agent)
  }]
let smoke_saturated : RDF_Graph.rdf_graph=
  fixpoint smoke_input_graph smoke_program (Prims.of_int (8))
