open Prims
type store_caps_flags =
  {
  scf_supports_named_graphs: Prims.bool ;
  scf_supports_update: Prims.bool ;
  scf_streaming_shapes: Prims.bool ;
  scf_estimate_is_exact: Prims.bool ;
  scf_can_report_decode_fail: Prims.bool }
let __proj__Mkstore_caps_flags__item__scf_supports_named_graphs
  (projectee : store_caps_flags) : Prims.bool=
  match projectee with
  | { scf_supports_named_graphs; scf_supports_update; scf_streaming_shapes;
      scf_estimate_is_exact; scf_can_report_decode_fail;_} ->
      scf_supports_named_graphs
let __proj__Mkstore_caps_flags__item__scf_supports_update
  (projectee : store_caps_flags) : Prims.bool=
  match projectee with
  | { scf_supports_named_graphs; scf_supports_update; scf_streaming_shapes;
      scf_estimate_is_exact; scf_can_report_decode_fail;_} ->
      scf_supports_update
let __proj__Mkstore_caps_flags__item__scf_streaming_shapes
  (projectee : store_caps_flags) : Prims.bool=
  match projectee with
  | { scf_supports_named_graphs; scf_supports_update; scf_streaming_shapes;
      scf_estimate_is_exact; scf_can_report_decode_fail;_} ->
      scf_streaming_shapes
let __proj__Mkstore_caps_flags__item__scf_estimate_is_exact
  (projectee : store_caps_flags) : Prims.bool=
  match projectee with
  | { scf_supports_named_graphs; scf_supports_update; scf_streaming_shapes;
      scf_estimate_is_exact; scf_can_report_decode_fail;_} ->
      scf_estimate_is_exact
let __proj__Mkstore_caps_flags__item__scf_can_report_decode_fail
  (projectee : store_caps_flags) : Prims.bool=
  match projectee with
  | { scf_supports_named_graphs; scf_supports_update; scf_streaming_shapes;
      scf_estimate_is_exact; scf_can_report_decode_fail;_} ->
      scf_can_report_decode_fail
type store_caps =
  {
  sc_flags: store_caps_flags ;
  sc_solve:
    SPARQL11_Algebra.triple_pattern_bound -> RDF_Triple.triple Prims.list ;
  sc_solve_limited:
    SPARQL11_Algebra.triple_pattern_bound ->
      Prims.nat -> RDF_Triple.triple Prims.list
    ;
  sc_estimate: SPARQL11_Algebra.triple_pattern_bound -> Prims.nat ;
  sc_count_exact: SPARQL11_Algebra.triple_pattern_bound -> Prims.nat ;
  sc_predicate_present: RDF_Term.wf_iri -> Prims.bool ;
  sc_decode_failure: unit -> Prims.bool }
let __proj__Mkstore_caps__item__sc_flags (projectee : store_caps) :
  store_caps_flags=
  match projectee with
  | { sc_flags; sc_solve; sc_solve_limited; sc_estimate; sc_count_exact;
      sc_predicate_present; sc_decode_failure;_} -> sc_flags
let __proj__Mkstore_caps__item__sc_solve (projectee : store_caps) :
  SPARQL11_Algebra.triple_pattern_bound -> RDF_Triple.triple Prims.list=
  match projectee with
  | { sc_flags; sc_solve; sc_solve_limited; sc_estimate; sc_count_exact;
      sc_predicate_present; sc_decode_failure;_} -> sc_solve
let __proj__Mkstore_caps__item__sc_solve_limited (projectee : store_caps) :
  SPARQL11_Algebra.triple_pattern_bound ->
    Prims.nat -> RDF_Triple.triple Prims.list=
  match projectee with
  | { sc_flags; sc_solve; sc_solve_limited; sc_estimate; sc_count_exact;
      sc_predicate_present; sc_decode_failure;_} -> sc_solve_limited
let __proj__Mkstore_caps__item__sc_estimate (projectee : store_caps) :
  SPARQL11_Algebra.triple_pattern_bound -> Prims.nat=
  match projectee with
  | { sc_flags; sc_solve; sc_solve_limited; sc_estimate; sc_count_exact;
      sc_predicate_present; sc_decode_failure;_} -> sc_estimate
let __proj__Mkstore_caps__item__sc_count_exact (projectee : store_caps) :
  SPARQL11_Algebra.triple_pattern_bound -> Prims.nat=
  match projectee with
  | { sc_flags; sc_solve; sc_solve_limited; sc_estimate; sc_count_exact;
      sc_predicate_present; sc_decode_failure;_} -> sc_count_exact
let __proj__Mkstore_caps__item__sc_predicate_present (projectee : store_caps)
  : RDF_Term.wf_iri -> Prims.bool=
  match projectee with
  | { sc_flags; sc_solve; sc_solve_limited; sc_estimate; sc_count_exact;
      sc_predicate_present; sc_decode_failure;_} -> sc_predicate_present
let __proj__Mkstore_caps__item__sc_decode_failure (projectee : store_caps) :
  unit -> Prims.bool=
  match projectee with
  | { sc_flags; sc_solve; sc_solve_limited; sc_estimate; sc_count_exact;
      sc_predicate_present; sc_decode_failure;_} -> sc_decode_failure
type store_write_caps =
  {
  swc_apply_delta:
    RDF_Store_Columnar_DeltaLog.delta_entry Prims.list -> store_caps ;
  swc_delta_stats:
    (SPARQL11_Algebra.triple_pattern_bound -> Prims.nat)
      FStar_Pervasives_Native.option
    }
let __proj__Mkstore_write_caps__item__swc_apply_delta
  (projectee : store_write_caps) :
  RDF_Store_Columnar_DeltaLog.delta_entry Prims.list -> store_caps=
  match projectee with
  | { swc_apply_delta; swc_delta_stats;_} -> swc_apply_delta
let __proj__Mkstore_write_caps__item__swc_delta_stats
  (projectee : store_write_caps) :
  (SPARQL11_Algebra.triple_pattern_bound -> Prims.nat)
    FStar_Pervasives_Native.option=
  match projectee with
  | { swc_apply_delta; swc_delta_stats;_} -> swc_delta_stats
type store =
  {
  st_read: store_caps ;
  st_write: store_write_caps FStar_Pervasives_Native.option }
let __proj__Mkstore__item__st_read (projectee : store) : store_caps=
  match projectee with | { st_read; st_write;_} -> st_read
let __proj__Mkstore__item__st_write (projectee : store) :
  store_write_caps FStar_Pervasives_Native.option=
  match projectee with | { st_read; st_write;_} -> st_write
let rec caps_take_n : 'a . Prims.nat -> 'a Prims.list -> 'a Prims.list =
  fun n xs ->
    if n = Prims.int_zero
    then []
    else
      (match xs with
       | [] -> []
       | hd::tl -> hd :: (caps_take_n (n - Prims.int_one) tl))
let rec union_solve (members : store_caps Prims.list)
  (b : SPARQL11_Algebra.triple_pattern_bound) : RDF_Triple.triple Prims.list=
  match members with
  | [] -> []
  | m::rest -> FStar_List_Tot_Base.op_At (m.sc_solve b) (union_solve rest b)
let rec union_estimate (members : store_caps Prims.list)
  (b : SPARQL11_Algebra.triple_pattern_bound) : Prims.nat=
  match members with
  | [] -> Prims.int_zero
  | m::rest -> (m.sc_estimate b) + (union_estimate rest b)
let rec union_count_exact (members : store_caps Prims.list)
  (b : SPARQL11_Algebra.triple_pattern_bound) : Prims.nat=
  match members with
  | [] -> Prims.int_zero
  | m::rest -> (m.sc_count_exact b) + (union_count_exact rest b)
let rec union_predicate_present (members : store_caps Prims.list)
  (pred : RDF_Term.wf_iri) : Prims.bool=
  match members with
  | [] -> false
  | m::rest ->
      if m.sc_predicate_present pred
      then true
      else union_predicate_present rest pred
let rec union_decode_failure (members : store_caps Prims.list) : Prims.bool=
  match members with
  | [] -> false
  | m::rest -> (m.sc_decode_failure ()) || (union_decode_failure rest)
let union_caps (members : store_caps Prims.list) : store_caps=
  {
    sc_flags =
      {
        scf_supports_named_graphs = true;
        scf_supports_update = false;
        scf_streaming_shapes = true;
        scf_estimate_is_exact = false;
        scf_can_report_decode_fail = true
      };
    sc_solve = (fun b -> union_solve members b);
    sc_solve_limited = (fun b n -> caps_take_n n (union_solve members b));
    sc_estimate = (fun b -> union_estimate members b);
    sc_count_exact = (fun b -> union_count_exact members b);
    sc_predicate_present = (fun pred -> union_predicate_present members pred);
    sc_decode_failure = (fun uu___ -> union_decode_failure members)
  }
let caps_of_indexed (ig : RDF_Indexed.indexed_graph) : store_caps=
  {
    sc_flags =
      {
        scf_supports_named_graphs = true;
        scf_supports_update = true;
        scf_streaming_shapes = true;
        scf_estimate_is_exact = true;
        scf_can_report_decode_fail = false
      };
    sc_solve = (fun b -> SPARQL11_Algebra.ig_search ig b);
    sc_solve_limited =
      (fun b n -> caps_take_n n (SPARQL11_Algebra.ig_search ig b));
    sc_estimate = (fun b -> SPARQL11_Algebra.ig_estimate ig b);
    sc_count_exact = (fun b -> SPARQL11_Algebra.ig_estimate ig b);
    sc_predicate_present =
      (fun pred ->
         (SPARQL11_Algebra.ig_estimate ig
            {
              SPARQL11_Algebra.bs = FStar_Pervasives_Native.None;
              SPARQL11_Algebra.bp = (FStar_Pervasives_Native.Some pred);
              SPARQL11_Algebra.bo = FStar_Pervasives_Native.None
            })
           > Prims.int_zero);
    sc_decode_failure = (fun uu___ -> false)
  }
