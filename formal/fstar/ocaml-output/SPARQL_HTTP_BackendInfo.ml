open Prims
type backend_kind =
  | BK_InMem 
  | BK_CottasOnDisk 
  | BK_Hybrid 
  | BK_Empty 
let (uu___is_BK_InMem : backend_kind -> Prims.bool) =
  fun projectee -> match projectee with | BK_InMem -> true | uu___ -> false
let (uu___is_BK_CottasOnDisk : backend_kind -> Prims.bool) =
  fun projectee ->
    match projectee with | BK_CottasOnDisk -> true | uu___ -> false
let (uu___is_BK_Hybrid : backend_kind -> Prims.bool) =
  fun projectee -> match projectee with | BK_Hybrid -> true | uu___ -> false
let (uu___is_BK_Empty : backend_kind -> Prims.bool) =
  fun projectee -> match projectee with | BK_Empty -> true | uu___ -> false
let (backend_kind_string : backend_kind -> Prims.string) =
  fun k ->
    match k with
    | BK_InMem -> "in-memory"
    | BK_CottasOnDisk -> "binary"
    | BK_Hybrid -> "mixed"
    | BK_Empty -> "empty"
type cottas_summary =
  {
  cs_path: Prims.string ;
  cs_quads: Prims.int ;
  cs_row_groups: Prims.int }
let (__proj__Mkcottas_summary__item__cs_path :
  cottas_summary -> Prims.string) =
  fun projectee ->
    match projectee with | { cs_path; cs_quads; cs_row_groups;_} -> cs_path
let (__proj__Mkcottas_summary__item__cs_quads : cottas_summary -> Prims.int)
  =
  fun projectee ->
    match projectee with | { cs_path; cs_quads; cs_row_groups;_} -> cs_quads
let (__proj__Mkcottas_summary__item__cs_row_groups :
  cottas_summary -> Prims.int) =
  fun projectee ->
    match projectee with
    | { cs_path; cs_quads; cs_row_groups;_} -> cs_row_groups
type backend_info =
  {
  bi_kind: backend_kind ;
  bi_source: Prims.string ;
  bi_in_memory_triples: Prims.int ;
  bi_in_memory_default_graph_triples: Prims.int ;
  bi_in_memory_named_graphs: Prims.int ;
  bi_in_memory_named_graph_triples: Prims.int ;
  bi_cottas: cottas_summary Prims.list }
let (__proj__Mkbackend_info__item__bi_kind : backend_info -> backend_kind) =
  fun projectee ->
    match projectee with
    | { bi_kind; bi_source; bi_in_memory_triples;
        bi_in_memory_default_graph_triples; bi_in_memory_named_graphs;
        bi_in_memory_named_graph_triples; bi_cottas;_} -> bi_kind
let (__proj__Mkbackend_info__item__bi_source : backend_info -> Prims.string)
  =
  fun projectee ->
    match projectee with
    | { bi_kind; bi_source; bi_in_memory_triples;
        bi_in_memory_default_graph_triples; bi_in_memory_named_graphs;
        bi_in_memory_named_graph_triples; bi_cottas;_} -> bi_source
let (__proj__Mkbackend_info__item__bi_in_memory_triples :
  backend_info -> Prims.int) =
  fun projectee ->
    match projectee with
    | { bi_kind; bi_source; bi_in_memory_triples;
        bi_in_memory_default_graph_triples; bi_in_memory_named_graphs;
        bi_in_memory_named_graph_triples; bi_cottas;_} ->
        bi_in_memory_triples
let (__proj__Mkbackend_info__item__bi_in_memory_default_graph_triples :
  backend_info -> Prims.int) =
  fun projectee ->
    match projectee with
    | { bi_kind; bi_source; bi_in_memory_triples;
        bi_in_memory_default_graph_triples; bi_in_memory_named_graphs;
        bi_in_memory_named_graph_triples; bi_cottas;_} ->
        bi_in_memory_default_graph_triples
let (__proj__Mkbackend_info__item__bi_in_memory_named_graphs :
  backend_info -> Prims.int) =
  fun projectee ->
    match projectee with
    | { bi_kind; bi_source; bi_in_memory_triples;
        bi_in_memory_default_graph_triples; bi_in_memory_named_graphs;
        bi_in_memory_named_graph_triples; bi_cottas;_} ->
        bi_in_memory_named_graphs
let (__proj__Mkbackend_info__item__bi_in_memory_named_graph_triples :
  backend_info -> Prims.int) =
  fun projectee ->
    match projectee with
    | { bi_kind; bi_source; bi_in_memory_triples;
        bi_in_memory_default_graph_triples; bi_in_memory_named_graphs;
        bi_in_memory_named_graph_triples; bi_cottas;_} ->
        bi_in_memory_named_graph_triples
let (__proj__Mkbackend_info__item__bi_cottas :
  backend_info -> cottas_summary Prims.list) =
  fun projectee ->
    match projectee with
    | { bi_kind; bi_source; bi_in_memory_triples;
        bi_in_memory_default_graph_triples; bi_in_memory_named_graphs;
        bi_in_memory_named_graph_triples; bi_cottas;_} -> bi_cottas
let rec (sum_cottas_quads : cottas_summary Prims.list -> Prims.int) =
  fun xs ->
    match xs with
    | [] -> Prims.int_zero
    | x::rest -> x.cs_quads + (sum_cottas_quads rest)
let (render_backend_info : backend_info -> Prims.string) =
  fun info ->
    let cottas_quads = sum_cottas_quads info.bi_cottas in
    let n_files = FStar_List_Tot_Base.length info.bi_cottas in
    let triples_total = info.bi_in_memory_triples + cottas_quads in
    let kind_s =
      SPARQL_JSON_Escape.json_escape (backend_kind_string info.bi_kind) in
    let source_s = SPARQL_JSON_Escape.json_escape info.bi_source in
    FStar_String.concat ""
      ["{\"kind\":\"";
      kind_s;
      "\",\"triples\":";
      Prims.string_of_int triples_total;
      ",\"in_memory_triples\":";
      Prims.string_of_int info.bi_in_memory_triples;
      ",\"in_memory_default_graph_triples\":";
      Prims.string_of_int info.bi_in_memory_default_graph_triples;
      ",\"in_memory_named_graphs\":";
      Prims.string_of_int info.bi_in_memory_named_graphs;
      ",\"in_memory_named_graph_triples\":";
      Prims.string_of_int info.bi_in_memory_named_graph_triples;
      ",\"cottas_triples\":";
      Prims.string_of_int cottas_quads;
      ",\"cottas_files\":";
      Prims.string_of_int n_files;
      ",\"source\":\"";
      source_s;
      "\"}\n"]
let rec (sum_named_triples :
  RDF_Graph_Executable.named_graph Prims.list -> Prims.nat) =
  fun ngs ->
    match ngs with
    | [] -> Prims.int_zero
    | ng::rest ->
        (FStar_List_Tot_Base.length ng.RDF_Graph_Executable.ng_graph) +
          (sum_named_triples rest)
let (count_dataset_triples :
  RDF_Graph_Executable.rdf_dataset ->
    (Prims.int * Prims.int * Prims.int * Prims.int))
  =
  fun ds ->
    let dflt = FStar_List_Tot_Base.length ds.RDF_Graph_Executable.ds_default in
    let named_count =
      FStar_List_Tot_Base.length ds.RDF_Graph_Executable.ds_named in
    let named_triples = sum_named_triples ds.RDF_Graph_Executable.ds_named in
    ((dflt + named_triples), dflt, named_count, named_triples)
let (backend_kind_of_flags : Prims.bool -> Prims.bool -> backend_kind) =
  fun has_dataset ->
    fun has_cottas ->
      if has_dataset
      then (if has_cottas then BK_Hybrid else BK_InMem)
      else if has_cottas then BK_CottasOnDisk else BK_Empty
