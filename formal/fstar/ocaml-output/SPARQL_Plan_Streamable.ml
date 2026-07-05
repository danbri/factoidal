open Prims
type stream_domain =
  | SD_DefaultGraph 
  | SD_AnyNamedGraph 
let uu___is_SD_DefaultGraph (projectee : stream_domain) : Prims.bool=
  match projectee with | SD_DefaultGraph -> true | uu___ -> false
let uu___is_SD_AnyNamedGraph (projectee : stream_domain) : Prims.bool=
  match projectee with | SD_AnyNamedGraph -> true | uu___ -> false
type stream_goal =
  | SG_Count of SPARQL11_Algebra.var_name 
  | SG_Ask 
let uu___is_SG_Count (projectee : stream_goal) : Prims.bool=
  match projectee with | SG_Count _0 -> true | uu___ -> false
let __proj__SG_Count__item___0 (projectee : stream_goal) :
  SPARQL11_Algebra.var_name= match projectee with | SG_Count _0 -> _0
let uu___is_SG_Ask (projectee : stream_goal) : Prims.bool=
  match projectee with | SG_Ask -> true | uu___ -> false
type stream_plan =
  {
  sp_domain: stream_domain ;
  sp_bound: SPARQL11_Algebra.triple_pattern_bound ;
  sp_goal: stream_goal ;
  sp_offset: Prims.nat FStar_Pervasives_Native.option ;
  sp_limit: Prims.nat FStar_Pervasives_Native.option }
let __proj__Mkstream_plan__item__sp_domain (projectee : stream_plan) :
  stream_domain=
  match projectee with
  | { sp_domain; sp_bound; sp_goal; sp_offset; sp_limit;_} -> sp_domain
let __proj__Mkstream_plan__item__sp_bound (projectee : stream_plan) :
  SPARQL11_Algebra.triple_pattern_bound=
  match projectee with
  | { sp_domain; sp_bound; sp_goal; sp_offset; sp_limit;_} -> sp_bound
let __proj__Mkstream_plan__item__sp_goal (projectee : stream_plan) :
  stream_goal=
  match projectee with
  | { sp_domain; sp_bound; sp_goal; sp_offset; sp_limit;_} -> sp_goal
let __proj__Mkstream_plan__item__sp_offset (projectee : stream_plan) :
  Prims.nat FStar_Pervasives_Native.option=
  match projectee with
  | { sp_domain; sp_bound; sp_goal; sp_offset; sp_limit;_} -> sp_offset
let __proj__Mkstream_plan__item__sp_limit (projectee : stream_plan) :
  Prims.nat FStar_Pervasives_Native.option=
  match projectee with
  | { sp_domain; sp_bound; sp_goal; sp_offset; sp_limit;_} -> sp_limit
let extract_single_tp_bgp (p : SPARQL11_Algebra.group_graph_pattern) :
  SPARQL11_Algebra.triple_pattern FStar_Pervasives_Native.option=
  match p with
  | SPARQL11_Algebra.GP_BGP (tp::[]) -> FStar_Pervasives_Native.Some tp
  | uu___ -> FStar_Pervasives_Native.None
let detect_count_star_select (sel : SPARQL11_Algebra.select_clause) :
  SPARQL11_Algebra.var_name FStar_Pervasives_Native.option=
  match sel with
  | SPARQL11_Algebra.Select_Vars ((SPARQL11_Algebra.SI_Expr (e, v))::[]) ->
      (match e with
       | SPARQL11_Algebra.E_Aggregate
           (SPARQL11_Algebra.Agg_Count, distinct, sub_e) ->
           if distinct
           then FStar_Pervasives_Native.None
           else
             (match sub_e with
              | SPARQL11_Algebra.E_Var "*" -> FStar_Pervasives_Native.Some v
              | SPARQL11_Algebra.E_BoolLit true ->
                  FStar_Pervasives_Native.Some v
              | uu___1 -> FStar_Pervasives_Native.None)
       | uu___ -> FStar_Pervasives_Native.None)
  | uu___ -> FStar_Pervasives_Native.None
let pattern_bound_of_tp (tp : SPARQL11_Algebra.triple_pattern) :
  SPARQL11_Algebra.triple_pattern_bound=
  {
    SPARQL11_Algebra.bs =
      (SPARQL11_Algebra.bound_subject_of_pattern tp.SPARQL11_Algebra.tp_s
         SPARQL11_Algebra.sm_empty);
    SPARQL11_Algebra.bp =
      (SPARQL11_Algebra.bound_predicate_of_pattern tp.SPARQL11_Algebra.tp_p
         SPARQL11_Algebra.sm_empty);
    SPARQL11_Algebra.bo =
      (SPARQL11_Algebra.bound_object_of_pattern tp.SPARQL11_Algebra.tp_o
         SPARQL11_Algebra.sm_empty)
  }
let common_modifiers_ok (q : SPARQL11_Algebra.query) : Prims.bool=
  (((((FStar_Pervasives_Native.uu___is_None q.SPARQL11_Algebra.q_group_by) &&
        (FStar_Pervasives_Native.uu___is_None q.SPARQL11_Algebra.q_having))
       && (FStar_Pervasives_Native.uu___is_None q.SPARQL11_Algebra.q_values))
      &&
      (Prims.op_Negation
         (q.SPARQL11_Algebra.q_modifier).SPARQL11_Algebra.sm_distinct))
     &&
     (Prims.op_Negation
        (q.SPARQL11_Algebra.q_modifier).SPARQL11_Algebra.sm_reduced))
    &&
    (FStar_Pervasives_Native.uu___is_None
       (q.SPARQL11_Algebra.q_modifier).SPARQL11_Algebra.sm_order_by)
let detect_count_default (q : SPARQL11_Algebra.query) :
  stream_plan FStar_Pervasives_Native.option=
  match q.SPARQL11_Algebra.q_form with
  | SPARQL11_Algebra.QF_Select sel ->
      (match detect_count_star_select sel with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some alias ->
           if Prims.op_Negation (common_modifiers_ok q)
           then FStar_Pervasives_Native.None
           else
             (match extract_single_tp_bgp q.SPARQL11_Algebra.q_pattern with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some tp ->
                  FStar_Pervasives_Native.Some
                    {
                      sp_domain = SD_DefaultGraph;
                      sp_bound = (pattern_bound_of_tp tp);
                      sp_goal = (SG_Count alias);
                      sp_offset =
                        ((q.SPARQL11_Algebra.q_modifier).SPARQL11_Algebra.sm_offset);
                      sp_limit =
                        ((q.SPARQL11_Algebra.q_modifier).SPARQL11_Algebra.sm_limit)
                    }))
  | uu___ -> FStar_Pervasives_Native.None
let detect_count_any_named_graph (q : SPARQL11_Algebra.query) :
  stream_plan FStar_Pervasives_Native.option=
  match q.SPARQL11_Algebra.q_form with
  | SPARQL11_Algebra.QF_Select sel ->
      (match detect_count_star_select sel with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some alias ->
           if Prims.op_Negation (common_modifiers_ok q)
           then FStar_Pervasives_Native.None
           else
             (match q.SPARQL11_Algebra.q_pattern with
              | SPARQL11_Algebra.GP_Graph (SPARQL11_Algebra.PT_Var gv, inner)
                  ->
                  (match extract_single_tp_bgp inner with
                   | FStar_Pervasives_Native.None ->
                       FStar_Pervasives_Native.None
                   | FStar_Pervasives_Native.Some tp ->
                       (match ((tp.SPARQL11_Algebra.tp_s),
                                (tp.SPARQL11_Algebra.tp_p),
                                (tp.SPARQL11_Algebra.tp_o))
                        with
                        | (SPARQL11_Algebra.PS_Var sv,
                           SPARQL11_Algebra.PT_Var pv,
                           SPARQL11_Algebra.PT_Var ov) ->
                            if ((sv = gv) || (pv = gv)) || (ov = gv)
                            then FStar_Pervasives_Native.None
                            else
                              if ((sv = pv) || (sv = ov)) || (pv = ov)
                              then FStar_Pervasives_Native.None
                              else
                                FStar_Pervasives_Native.Some
                                  {
                                    sp_domain = SD_AnyNamedGraph;
                                    sp_bound =
                                      {
                                        SPARQL11_Algebra.bs =
                                          FStar_Pervasives_Native.None;
                                        SPARQL11_Algebra.bp =
                                          FStar_Pervasives_Native.None;
                                        SPARQL11_Algebra.bo =
                                          FStar_Pervasives_Native.None
                                      };
                                    sp_goal = (SG_Count alias);
                                    sp_offset =
                                      ((q.SPARQL11_Algebra.q_modifier).SPARQL11_Algebra.sm_offset);
                                    sp_limit =
                                      ((q.SPARQL11_Algebra.q_modifier).SPARQL11_Algebra.sm_limit)
                                  }
                        | uu___1 -> FStar_Pervasives_Native.None))
              | uu___1 -> FStar_Pervasives_Native.None))
  | uu___ -> FStar_Pervasives_Native.None
let detect_ask_default (q : SPARQL11_Algebra.query) :
  stream_plan FStar_Pervasives_Native.option=
  match q.SPARQL11_Algebra.q_form with
  | SPARQL11_Algebra.QF_Ask ->
      if FStar_Pervasives_Native.uu___is_Some q.SPARQL11_Algebra.q_values
      then FStar_Pervasives_Native.None
      else
        (match extract_single_tp_bgp q.SPARQL11_Algebra.q_pattern with
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some tp ->
             FStar_Pervasives_Native.Some
               {
                 sp_domain = SD_DefaultGraph;
                 sp_bound = (pattern_bound_of_tp tp);
                 sp_goal = SG_Ask;
                 sp_offset = FStar_Pervasives_Native.None;
                 sp_limit = FStar_Pervasives_Native.None
               })
  | uu___ -> FStar_Pervasives_Native.None
let streamable_shape (q : SPARQL11_Algebra.query) :
  stream_plan FStar_Pervasives_Native.option=
  match detect_count_default q with
  | FStar_Pervasives_Native.Some p -> FStar_Pervasives_Native.Some p
  | FStar_Pervasives_Native.None ->
      (match detect_count_any_named_graph q with
       | FStar_Pervasives_Native.Some p -> FStar_Pervasives_Native.Some p
       | FStar_Pervasives_Native.None -> detect_ask_default q)
type stream_state = {
  ss_count: Prims.nat ;
  ss_found: Prims.bool }
let __proj__Mkstream_state__item__ss_count (projectee : stream_state) :
  Prims.nat= match projectee with | { ss_count; ss_found;_} -> ss_count
let __proj__Mkstream_state__item__ss_found (projectee : stream_state) :
  Prims.bool= match projectee with | { ss_count; ss_found;_} -> ss_found
let stream_init : stream_state=
  { ss_count = Prims.int_zero; ss_found = false }
let triple_matches_stream_bound (b : SPARQL11_Algebra.triple_pattern_bound)
  (t : RDF_Triple.triple) : Prims.bool=
  ((match b.SPARQL11_Algebra.bs with
    | FStar_Pervasives_Native.None -> true
    | FStar_Pervasives_Native.Some s -> RDF_Term.subject_eq s t.RDF_Triple.s)
     &&
     (match b.SPARQL11_Algebra.bp with
      | FStar_Pervasives_Native.None -> true
      | FStar_Pervasives_Native.Some p -> p = t.RDF_Triple.p))
    &&
    (match b.SPARQL11_Algebra.bo with
     | FStar_Pervasives_Native.None -> true
     | FStar_Pervasives_Native.Some o ->
         RDF_Term.rdf_term_eq o t.RDF_Triple.o)
let stream_in_domain (plan : stream_plan)
  (g : RDF_Term.iri FStar_Pervasives_Native.option) : Prims.bool=
  match ((plan.sp_domain), g) with
  | (SD_DefaultGraph, FStar_Pervasives_Native.None) -> true
  | (SD_AnyNamedGraph, FStar_Pervasives_Native.Some uu___) -> true
  | (uu___, uu___1) -> false
let stream_step (plan : stream_plan) (t : RDF_Triple.triple)
  (st : stream_state) : stream_state=
  if triple_matches_stream_bound plan.sp_bound t
  then
    match plan.sp_goal with
    | SG_Count uu___ ->
        { ss_count = (st.ss_count + Prims.int_one); ss_found = (st.ss_found)
        }
    | SG_Ask -> { ss_count = (st.ss_count); ss_found = true }
  else st
let stream_stop (plan : stream_plan) (st : stream_state) : Prims.bool=
  match plan.sp_goal with | SG_Ask -> st.ss_found | SG_Count uu___ -> false
let stream_count_result (st : stream_state) : Prims.nat= st.ss_count
let stream_ask_result (st : stream_state) : Prims.bool= st.ss_found
