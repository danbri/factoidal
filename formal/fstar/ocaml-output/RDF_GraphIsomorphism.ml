open Prims
let normalize_literal (l : RDF_Term.wf_literal) : RDF_Term.wf_literal=
  match l.RDF_Term.lang_tag with
  | FStar_Pervasives_Native.Some t ->
      {
        RDF_Term.lexical_form = (l.RDF_Term.lexical_form);
        RDF_Term.datatype = (l.RDF_Term.datatype);
        RDF_Term.lang_tag =
          (FStar_Pervasives_Native.Some (FStar_String.lowercase t))
      }
  | FStar_Pervasives_Native.None -> l
let normalize_term (t : RDF_Term.rdf_term) : RDF_Term.rdf_term=
  match t with
  | RDF_Term.T_Literal l -> RDF_Term.T_Literal (normalize_literal l)
  | uu___ -> t
let normalize_triple (tr : RDF_Triple.triple) : RDF_Triple.triple=
  {
    RDF_Triple.s = (tr.RDF_Triple.s);
    RDF_Triple.p = (tr.RDF_Triple.p);
    RDF_Triple.o = (normalize_term tr.RDF_Triple.o)
  }
let normalize_graph (g : RDF_Triple.triple Prims.list) :
  RDF_Triple.triple Prims.list= FStar_List_Tot_Base.map normalize_triple g
let iso_budget : Prims.nat= RDF_Canonical.default_hndq_budget
type iso_outcome =
  | Iso_Equal 
  | Iso_NotEqual 
  | Iso_BudgetExceeded 
let uu___is_Iso_Equal (projectee : iso_outcome) : Prims.bool=
  match projectee with | Iso_Equal -> true | uu___ -> false
let uu___is_Iso_NotEqual (projectee : iso_outcome) : Prims.bool=
  match projectee with | Iso_NotEqual -> true | uu___ -> false
let uu___is_Iso_BudgetExceeded (projectee : iso_outcome) : Prims.bool=
  match projectee with | Iso_BudgetExceeded -> true | uu___ -> false
let graph_to_dataset (g : RDF_Triple.triple Prims.list) :
  RDF_Graph.rdf_dataset=
  { RDF_Graph.ds_default = (normalize_graph g); RDF_Graph.ds_named = [] }
let normalize_named (ng : RDF_Graph.named_graph) : RDF_Graph.named_graph=
  {
    RDF_Graph.ng_name = (ng.RDF_Graph.ng_name);
    RDF_Graph.ng_graph = (normalize_graph ng.RDF_Graph.ng_graph)
  }
let normalize_dataset (ds : RDF_Graph.rdf_dataset) : RDF_Graph.rdf_dataset=
  {
    RDF_Graph.ds_default = (normalize_graph ds.RDF_Graph.ds_default);
    RDF_Graph.ds_named =
      (FStar_List_Tot_Base.map normalize_named ds.RDF_Graph.ds_named)
  }
let compare_datasets (da : RDF_Graph.rdf_dataset)
  (db : RDF_Graph.rdf_dataset) : iso_outcome=
  if
    (RDF_Canonical.canonicalize_exceeds_hndq_budget RDF_Canonical.HA_SHA256
       iso_budget da)
      ||
      (RDF_Canonical.canonicalize_exceeds_hndq_budget RDF_Canonical.HA_SHA256
         iso_budget db)
  then Iso_BudgetExceeded
  else
    if
      (RDF_Canonical.canonicalize_to_nquads da) =
        (RDF_Canonical.canonicalize_to_nquads db)
    then Iso_Equal
    else Iso_NotEqual
let graphs_isomorphic_outcome (a : RDF_Triple.triple Prims.list)
  (b : RDF_Triple.triple Prims.list) : iso_outcome=
  compare_datasets (graph_to_dataset a) (graph_to_dataset b)
let graphs_isomorphic (a : RDF_Triple.triple Prims.list)
  (b : RDF_Triple.triple Prims.list) : Prims.bool=
  uu___is_Iso_Equal (graphs_isomorphic_outcome a b)
let datasets_isomorphic_outcome (a : RDF_Graph.rdf_dataset)
  (b : RDF_Graph.rdf_dataset) : iso_outcome=
  compare_datasets (normalize_dataset a) (normalize_dataset b)
let datasets_isomorphic (a : RDF_Graph.rdf_dataset)
  (b : RDF_Graph.rdf_dataset) : Prims.bool=
  uu___is_Iso_Equal (datasets_isomorphic_outcome a b)
let rrv_binding : RDF_Term.wf_iri= "urn:factoidal:resultset#binding"
let rrv_var : RDF_Term.wf_iri= "urn:factoidal:resultset#var"
let rrv_value : RDF_Term.wf_iri= "urn:factoidal:resultset#value"
let rrv_index : RDF_Term.wf_iri= "urn:factoidal:resultset#index"
let iso_plain_literal (s : Prims.string) : RDF_Term.wf_literal=
  {
    RDF_Term.lexical_form = s;
    RDF_Term.datatype = RDF_Term.xsd_string;
    RDF_Term.lang_tag = FStar_Pervasives_Native.None
  }
let rec reify_bindings (rowbn : RDF_Term.bnode_id) (row_ix : Prims.nat)
  (bind_ix : Prims.nat) (bs : (Prims.string * RDF_Term.rdf_term) Prims.list)
  : RDF_Triple.triple Prims.list=
  match bs with
  | [] -> []
  | (v, t)::rest ->
      let bindbn =
        Prims.strcat "__isob_"
          (Prims.strcat (Prims.string_of_int row_ix)
             (Prims.strcat "_" (Prims.string_of_int bind_ix))) in
      let t_link =
        {
          RDF_Triple.s = (RDF_Term.S_BNode rowbn);
          RDF_Triple.p = rrv_binding;
          RDF_Triple.o = (RDF_Term.T_BNode bindbn)
        } in
      let t_var =
        {
          RDF_Triple.s = (RDF_Term.S_BNode bindbn);
          RDF_Triple.p = rrv_var;
          RDF_Triple.o = (RDF_Term.T_Literal (iso_plain_literal v))
        } in
      let t_val =
        {
          RDF_Triple.s = (RDF_Term.S_BNode bindbn);
          RDF_Triple.p = rrv_value;
          RDF_Triple.o = t
        } in
      t_link :: t_var :: t_val ::
        (reify_bindings rowbn row_ix (bind_ix + Prims.int_one) rest)
let rec reify_rows (ordered : Prims.bool) (row_ix : Prims.nat)
  (rows : (Prims.string * RDF_Term.rdf_term) Prims.list Prims.list) :
  RDF_Triple.triple Prims.list=
  match rows with
  | [] -> []
  | row::rest ->
      let rowbn = Prims.strcat "__isorow_" (Prims.string_of_int row_ix) in
      let binding_triples = reify_bindings rowbn row_ix Prims.int_zero row in
      let with_index =
        if ordered
        then
          {
            RDF_Triple.s = (RDF_Term.S_BNode rowbn);
            RDF_Triple.p = rrv_index;
            RDF_Triple.o =
              (RDF_Term.T_Literal
                 (iso_plain_literal (Prims.string_of_int row_ix)))
          } :: binding_triples
        else binding_triples in
      FStar_List_Tot_Base.op_At with_index
        (reify_rows ordered (row_ix + Prims.int_one) rest)
let reify_solutions (ordered : Prims.bool)
  (rows : (Prims.string * RDF_Term.rdf_term) Prims.list Prims.list) :
  RDF_Triple.triple Prims.list= reify_rows ordered Prims.int_zero rows
let solutions_isomorphic_outcome (ordered : Prims.bool)
  (expected : (Prims.string * RDF_Term.rdf_term) Prims.list Prims.list)
  (actual : (Prims.string * RDF_Term.rdf_term) Prims.list Prims.list) :
  iso_outcome=
  graphs_isomorphic_outcome (reify_solutions ordered expected)
    (reify_solutions ordered actual)
let solutions_isomorphic (ordered : Prims.bool)
  (expected : (Prims.string * RDF_Term.rdf_term) Prims.list Prims.list)
  (actual : (Prims.string * RDF_Term.rdf_term) Prims.list Prims.list) :
  Prims.bool=
  uu___is_Iso_Equal (solutions_isomorphic_outcome ordered expected actual)
let ask_results_match (expected : Prims.bool) (actual : Prims.bool) :
  Prims.bool= expected = actual
