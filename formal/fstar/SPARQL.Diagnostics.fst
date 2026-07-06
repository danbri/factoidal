module SPARQL.Diagnostics

// Pure diagnostic stringifiers used by the HTTP server's instrumentation
// layer (qof3-trace stderr lines). These are NOT part of any wire protocol
// — they're for human-readable trace output. Keeping them in F* alongside
// the algebra/backend types they describe ensures every constructor is
// covered (the F* match-totality checker will flag a missing case if the
// underlying ADT grows).

open FStar.List.Tot
open SPARQL11.Algebra
open SPARQL11.Store

// Render a graph_backend's outer constructor name. For GB_Union, recurses
// into the children and emits "GB_Union[c1,c2,...]". Used to correlate
// stderr traces with --data / --data-cottas / --data-hdt configurations.
val graph_backend_kind_string : graph_backend -> Tot string
let rec graph_backend_kind_string g =
  match g with
  | GB_List _        -> "GB_List"
  | GB_Indexed _     -> "GB_Indexed"
  | GB_HDT _         -> "GB_HDT"
  | GB_COTTAS _ _    -> "GB_COTTAS"
  | GB_CottasOnDisk _ _ -> "GB_CottasOnDisk"
  | GB_CottasOnDiskDelta _ _ _ -> "GB_CottasOnDiskDelta"
  | GB_Union gs ->
    "GB_Union[" ^ FStar.String.concat "," (map_kinds gs) ^ "]"

// Helper: map graph_backend_kind_string over each element of [gs].
// Spelled out so the F* termination check sees a structurally-decreasing
// list argument (each recursive call peels one constructor off [gs],
// and the inner call to graph_backend_kind_string runs on a structurally-
// smaller subterm of GB_Union gs).
and map_kinds (gs : list graph_backend)
  : Tot (list string) (decreases gs) =
  match gs with
  | [] -> []
  | g :: rest -> graph_backend_kind_string g :: map_kinds rest

// Render a dataset_backend as "{default=...; named=N graph(s)}".
val dataset_backend_kind_string : dataset_backend -> string
let dataset_backend_kind_string b =
  "{default=" ^ graph_backend_kind_string b.dsb_default
    ^ "; named=" ^ string_of_int (List.Tot.length b.dsb_named)
    ^ " graph(s)}"

// Render a query's query-form name: ASK / SELECT / CONSTRUCT / DESCRIBE.
val query_form_string : query -> string
let query_form_string q =
  match q.q_form with
  | QF_Ask         -> "ASK"
  | QF_Select _    -> "SELECT"
  | QF_Construct _ -> "CONSTRUCT"
  | QF_Describe _  -> "DESCRIBE"

// Smoke test for query_form_string. (graph_backend_kind_string and
// dataset_backend_kind_string are exercised by w3c_runner integration
// since constructing a non-empty graph_backend at compile time
// requires non-trivial backend state.)
let _test_query_form_ask =
  let modifier = {
    sm_order_by = None;
    sm_distinct = false;
    sm_reduced  = false;
    sm_offset   = None;
    sm_limit    = None } in
  let q = {
    q_base     = None;
    q_prefixes = [];
    q_form     = QF_Ask;
    q_dataset  = [];
    q_pattern  = GP_Empty;
    q_group_by = None;
    q_having   = None;
    q_modifier = modifier;
    q_values   = None } in
  query_form_string q = "ASK"
