open Prims
let rec graph_backend_kind_string (g : SPARQL11_Store.graph_backend) :
  Prims.string=
  match g with
  | SPARQL11_Store.GB_List uu___ -> "GB_List"
  | SPARQL11_Store.GB_Indexed uu___ -> "GB_Indexed"
  | SPARQL11_Store.GB_HDT uu___ -> "GB_HDT"
  | SPARQL11_Store.GB_COTTAS (uu___, uu___1) -> "GB_COTTAS"
  | SPARQL11_Store.GB_CottasOnDisk (uu___, uu___1) -> "GB_CottasOnDisk"
  | SPARQL11_Store.GB_Union gs ->
      Prims.strcat "GB_Union["
        (Prims.strcat (FStar_String.concat "," (map_kinds gs)) "]")
and map_kinds (gs : SPARQL11_Store.graph_backend Prims.list) :
  Prims.string Prims.list=
  match gs with
  | [] -> []
  | g::rest -> (graph_backend_kind_string g) :: (map_kinds rest)
let dataset_backend_kind_string (b : SPARQL11_Store.dataset_backend) :
  Prims.string=
  Prims.strcat "{default="
    (Prims.strcat (graph_backend_kind_string b.SPARQL11_Store.dsb_default)
       (Prims.strcat "; named="
          (Prims.strcat
             (Prims.string_of_int
                (FStar_List_Tot_Base.length b.SPARQL11_Store.dsb_named))
             " graph(s)}")))
let query_form_string (q : SPARQL11_Algebra.query) : Prims.string=
  match q.SPARQL11_Algebra.q_form with
  | SPARQL11_Algebra.QF_Ask -> "ASK"
  | SPARQL11_Algebra.QF_Select uu___ -> "SELECT"
  | SPARQL11_Algebra.QF_Construct uu___ -> "CONSTRUCT"
  | SPARQL11_Algebra.QF_Describe uu___ -> "DESCRIBE"
let _test_query_form_ask : Prims.bool=
  let modifier =
    {
      SPARQL11_Algebra.sm_order_by = FStar_Pervasives_Native.None;
      SPARQL11_Algebra.sm_distinct = false;
      SPARQL11_Algebra.sm_reduced = false;
      SPARQL11_Algebra.sm_offset = FStar_Pervasives_Native.None;
      SPARQL11_Algebra.sm_limit = FStar_Pervasives_Native.None
    } in
  let q =
    {
      SPARQL11_Algebra.q_base = FStar_Pervasives_Native.None;
      SPARQL11_Algebra.q_prefixes = [];
      SPARQL11_Algebra.q_form = SPARQL11_Algebra.QF_Ask;
      SPARQL11_Algebra.q_dataset = [];
      SPARQL11_Algebra.q_pattern = SPARQL11_Algebra.GP_Empty;
      SPARQL11_Algebra.q_group_by = FStar_Pervasives_Native.None;
      SPARQL11_Algebra.q_having = FStar_Pervasives_Native.None;
      SPARQL11_Algebra.q_modifier = modifier;
      SPARQL11_Algebra.q_values = FStar_Pervasives_Native.None
    } in
  (query_form_string q) = "ASK"
