open Prims
type cottas_encoding =
  | CE_Plain 
  | CE_Dictionary 
  | CE_RLE 
  | CE_Delta 
let uu___is_CE_Plain (projectee : cottas_encoding) : Prims.bool=
  match projectee with | CE_Plain -> true | uu___ -> false
let uu___is_CE_Dictionary (projectee : cottas_encoding) : Prims.bool=
  match projectee with | CE_Dictionary -> true | uu___ -> false
let uu___is_CE_RLE (projectee : cottas_encoding) : Prims.bool=
  match projectee with | CE_RLE -> true | uu___ -> false
let uu___is_CE_Delta (projectee : cottas_encoding) : Prims.bool=
  match projectee with | CE_Delta -> true | uu___ -> false
type cottas_column_kind =
  | CC_Subject 
  | CC_Predicate 
  | CC_Object 
  | CC_Graph 
let uu___is_CC_Subject (projectee : cottas_column_kind) : Prims.bool=
  match projectee with | CC_Subject -> true | uu___ -> false
let uu___is_CC_Predicate (projectee : cottas_column_kind) : Prims.bool=
  match projectee with | CC_Predicate -> true | uu___ -> false
let uu___is_CC_Object (projectee : cottas_column_kind) : Prims.bool=
  match projectee with | CC_Object -> true | uu___ -> false
let uu___is_CC_Graph (projectee : cottas_column_kind) : Prims.bool=
  match projectee with | CC_Graph -> true | uu___ -> false
type cottas_column_summary =
  {
  ccs_kind: cottas_column_kind ;
  ccs_num_values: Prims.nat ;
  ccs_null_count: Prims.nat ;
  ccs_encoding: cottas_encoding }
let __proj__Mkcottas_column_summary__item__ccs_kind
  (projectee : cottas_column_summary) : cottas_column_kind=
  match projectee with
  | { ccs_kind; ccs_num_values; ccs_null_count; ccs_encoding;_} -> ccs_kind
let __proj__Mkcottas_column_summary__item__ccs_num_values
  (projectee : cottas_column_summary) : Prims.nat=
  match projectee with
  | { ccs_kind; ccs_num_values; ccs_null_count; ccs_encoding;_} ->
      ccs_num_values
let __proj__Mkcottas_column_summary__item__ccs_null_count
  (projectee : cottas_column_summary) : Prims.nat=
  match projectee with
  | { ccs_kind; ccs_num_values; ccs_null_count; ccs_encoding;_} ->
      ccs_null_count
let __proj__Mkcottas_column_summary__item__ccs_encoding
  (projectee : cottas_column_summary) : cottas_encoding=
  match projectee with
  | { ccs_kind; ccs_num_values; ccs_null_count; ccs_encoding;_} ->
      ccs_encoding
type cottas_dictionary_summary =
  {
  cds_num_terms: Prims.nat ;
  cds_num_graphs: Prims.nat ;
  cds_bytes_strings: Prims.nat }
let __proj__Mkcottas_dictionary_summary__item__cds_num_terms
  (projectee : cottas_dictionary_summary) : Prims.nat=
  match projectee with
  | { cds_num_terms; cds_num_graphs; cds_bytes_strings;_} -> cds_num_terms
let __proj__Mkcottas_dictionary_summary__item__cds_num_graphs
  (projectee : cottas_dictionary_summary) : Prims.nat=
  match projectee with
  | { cds_num_terms; cds_num_graphs; cds_bytes_strings;_} -> cds_num_graphs
let __proj__Mkcottas_dictionary_summary__item__cds_bytes_strings
  (projectee : cottas_dictionary_summary) : Prims.nat=
  match projectee with
  | { cds_num_terms; cds_num_graphs; cds_bytes_strings;_} ->
      cds_bytes_strings
type cottas_row_group_summary =
  {
  crgs_index: Prims.nat ;
  crgs_num_rows: Prims.nat ;
  crgs_columns: cottas_column_summary Prims.list }
let __proj__Mkcottas_row_group_summary__item__crgs_index
  (projectee : cottas_row_group_summary) : Prims.nat=
  match projectee with
  | { crgs_index; crgs_num_rows; crgs_columns;_} -> crgs_index
let __proj__Mkcottas_row_group_summary__item__crgs_num_rows
  (projectee : cottas_row_group_summary) : Prims.nat=
  match projectee with
  | { crgs_index; crgs_num_rows; crgs_columns;_} -> crgs_num_rows
let __proj__Mkcottas_row_group_summary__item__crgs_columns
  (projectee : cottas_row_group_summary) : cottas_column_summary Prims.list=
  match projectee with
  | { crgs_index; crgs_num_rows; crgs_columns;_} -> crgs_columns
type cottas_artifact_summary =
  {
  cas_path: Prims.string ;
  cas_num_quads: Prims.nat ;
  cas_num_row_groups: Prims.nat ;
  cas_dictionary: cottas_dictionary_summary FStar_Pervasives_Native.option ;
  cas_row_groups: cottas_row_group_summary Prims.list }
let __proj__Mkcottas_artifact_summary__item__cas_path
  (projectee : cottas_artifact_summary) : Prims.string=
  match projectee with
  | { cas_path; cas_num_quads; cas_num_row_groups; cas_dictionary;
      cas_row_groups;_} -> cas_path
let __proj__Mkcottas_artifact_summary__item__cas_num_quads
  (projectee : cottas_artifact_summary) : Prims.nat=
  match projectee with
  | { cas_path; cas_num_quads; cas_num_row_groups; cas_dictionary;
      cas_row_groups;_} -> cas_num_quads
let __proj__Mkcottas_artifact_summary__item__cas_num_row_groups
  (projectee : cottas_artifact_summary) : Prims.nat=
  match projectee with
  | { cas_path; cas_num_quads; cas_num_row_groups; cas_dictionary;
      cas_row_groups;_} -> cas_num_row_groups
let __proj__Mkcottas_artifact_summary__item__cas_dictionary
  (projectee : cottas_artifact_summary) :
  cottas_dictionary_summary FStar_Pervasives_Native.option=
  match projectee with
  | { cas_path; cas_num_quads; cas_num_row_groups; cas_dictionary;
      cas_row_groups;_} -> cas_dictionary
let __proj__Mkcottas_artifact_summary__item__cas_row_groups
  (projectee : cottas_artifact_summary) :
  cottas_row_group_summary Prims.list=
  match projectee with
  | { cas_path; cas_num_quads; cas_num_row_groups; cas_dictionary;
      cas_row_groups;_} -> cas_row_groups
type cottas_handle = unit
type cottas_term_ref = Prims.nat
type cottas_graph_ref = Prims.nat
type cottas_bound_qp =
  {
  cbqp_s: cottas_term_ref FStar_Pervasives_Native.option ;
  cbqp_p: cottas_term_ref FStar_Pervasives_Native.option ;
  cbqp_o: cottas_term_ref FStar_Pervasives_Native.option ;
  cbqp_g: cottas_graph_ref FStar_Pervasives_Native.option }
let __proj__Mkcottas_bound_qp__item__cbqp_s (projectee : cottas_bound_qp) :
  cottas_term_ref FStar_Pervasives_Native.option=
  match projectee with | { cbqp_s; cbqp_p; cbqp_o; cbqp_g;_} -> cbqp_s
let __proj__Mkcottas_bound_qp__item__cbqp_p (projectee : cottas_bound_qp) :
  cottas_term_ref FStar_Pervasives_Native.option=
  match projectee with | { cbqp_s; cbqp_p; cbqp_o; cbqp_g;_} -> cbqp_p
let __proj__Mkcottas_bound_qp__item__cbqp_o (projectee : cottas_bound_qp) :
  cottas_term_ref FStar_Pervasives_Native.option=
  match projectee with | { cbqp_s; cbqp_p; cbqp_o; cbqp_g;_} -> cbqp_o
let __proj__Mkcottas_bound_qp__item__cbqp_g (projectee : cottas_bound_qp) :
  cottas_graph_ref FStar_Pervasives_Native.option=
  match projectee with | { cbqp_s; cbqp_p; cbqp_o; cbqp_g;_} -> cbqp_g
type cottas_qp_row =
  {
  cqpr_s: cottas_term_ref FStar_Pervasives_Native.option ;
  cqpr_p: cottas_term_ref FStar_Pervasives_Native.option ;
  cqpr_o: cottas_term_ref FStar_Pervasives_Native.option ;
  cqpr_g: cottas_graph_ref FStar_Pervasives_Native.option }
let __proj__Mkcottas_qp_row__item__cqpr_s (projectee : cottas_qp_row) :
  cottas_term_ref FStar_Pervasives_Native.option=
  match projectee with | { cqpr_s; cqpr_p; cqpr_o; cqpr_g;_} -> cqpr_s
let __proj__Mkcottas_qp_row__item__cqpr_p (projectee : cottas_qp_row) :
  cottas_term_ref FStar_Pervasives_Native.option=
  match projectee with | { cqpr_s; cqpr_p; cqpr_o; cqpr_g;_} -> cqpr_p
let __proj__Mkcottas_qp_row__item__cqpr_o (projectee : cottas_qp_row) :
  cottas_term_ref FStar_Pervasives_Native.option=
  match projectee with | { cqpr_s; cqpr_p; cqpr_o; cqpr_g;_} -> cqpr_o
let __proj__Mkcottas_qp_row__item__cqpr_g (projectee : cottas_qp_row) :
  cottas_graph_ref FStar_Pervasives_Native.option=
  match projectee with | { cqpr_s; cqpr_p; cqpr_o; cqpr_g;_} -> cqpr_g
type cottas_dataset_store =
  {
  cds_artifact_path: Prims.string ;
  cds_summary: cottas_artifact_summary FStar_Pervasives_Native.option ;
  cds_handle: cottas_handle }
let __proj__Mkcottas_dataset_store__item__cds_artifact_path
  (projectee : cottas_dataset_store) : Prims.string=
  match projectee with
  | { cds_artifact_path; cds_summary; cds_handle;_} -> cds_artifact_path
let __proj__Mkcottas_dataset_store__item__cds_summary
  (projectee : cottas_dataset_store) :
  cottas_artifact_summary FStar_Pervasives_Native.option=
  match projectee with
  | { cds_artifact_path; cds_summary; cds_handle;_} -> cds_summary
let __proj__Mkcottas_dataset_store__item__cds_handle
  (projectee : cottas_dataset_store) : cottas_handle=
  match projectee with
  | { cds_artifact_path; cds_summary; cds_handle;_} -> cds_handle
type cottas_named_graph_store =
  {
  cngs_name: RDF_Graph_Executable.iri ;
  cngs_ref: cottas_graph_ref ;
  cngs_dataset: cottas_dataset_store }
let __proj__Mkcottas_named_graph_store__item__cngs_name
  (projectee : cottas_named_graph_store) : RDF_Graph_Executable.iri=
  match projectee with | { cngs_name; cngs_ref; cngs_dataset;_} -> cngs_name
let __proj__Mkcottas_named_graph_store__item__cngs_ref
  (projectee : cottas_named_graph_store) : cottas_graph_ref=
  match projectee with | { cngs_name; cngs_ref; cngs_dataset;_} -> cngs_ref
let __proj__Mkcottas_named_graph_store__item__cngs_dataset
  (projectee : cottas_named_graph_store) : cottas_dataset_store=
  match projectee with
  | { cngs_name; cngs_ref; cngs_dataset;_} -> cngs_dataset

module Ballyhoo_cottas_runtime = struct
  open Stdlib

  type quad_row = {
    qr_s: Z.t;
    qr_p: Z.t;
    qr_o: Z.t;
    qr_g: Z.t option;
  }

  type cache = {
    quads: quad_row list;
    subject_to_id: (string, Z.t) Hashtbl.t;
    predicate_to_id: (string, Z.t) Hashtbl.t;
    object_to_id: (string, Z.t) Hashtbl.t;
    graph_to_id: (string, Z.t) Hashtbl.t;
    id_to_subject: (Z.t, RDF_Graph_Executable.subject) Hashtbl.t;
    id_to_predicate: (Z.t, RDF_Graph_Executable.wf_iri) Hashtbl.t;
    id_to_object: (Z.t, RDF_Graph_Executable.rdf_term) Hashtbl.t;
    id_to_graph: (Z.t, RDF_Graph_Executable.iri) Hashtbl.t;
    summary: cottas_artifact_summary FStar_Pervasives_Native.option;
  }

  let caches : (string, cache) Hashtbl.t = Hashtbl.create 17

  let subject_key = function
    | RDF_Graph_Executable.S_IRI i -> "I:" ^ i
    | RDF_Graph_Executable.S_BNode b -> "B:" ^ b

  let object_key = function
    | RDF_Graph_Executable.T_IRI i -> "I:" ^ i
    | RDF_Graph_Executable.T_BNode b -> "B:" ^ b
    | RDF_Graph_Executable.T_Literal l ->
      let lang = match l.RDF_Graph_Executable.lang_tag with
        | FStar_Pervasives_Native.None -> ""
        | FStar_Pervasives_Native.Some tag -> tag in
      "L:" ^ l.RDF_Graph_Executable.lexical_form ^ "|" ^ l.RDF_Graph_Executable.datatype ^ "|" ^ lang

  let find_unescaped_quote s =
    let rec loop i escaped =
      if i >= String.length s then None
      else
        match s.[i] with
        | '"' when not escaped -> Some i
        | '\\' when not escaped -> loop (i + 1) true
        | _ -> loop (i + 1) false
    in
    loop 1 false

  let unescape_literal s =
    let b = Buffer.create (String.length s) in
    let rec loop i =
      if i >= String.length s then Buffer.contents b
      else
        match s.[i] with
        | '\\' when i + 1 < String.length s ->
          Buffer.add_char b s.[i + 1];
          loop (i + 2)
        | c ->
          Buffer.add_char b c;
          loop (i + 1)
    in
    loop 0

  let parse_iri_token s =
    let len = String.length s in
    if len >= 2 && s.[0] = '<' && s.[len - 1] = '>' then
      Some (String.sub s 1 (len - 2))
    else
      None

  let parse_literal_token s =
    if String.length s < 2 || s.[0] <> '"' then
      None
    else
      match find_unescaped_quote s with
      | None -> None
      | Some q ->
        let lexical = unescape_literal (String.sub s 1 (q - 1)) in
        let suffix =
          if q + 1 >= String.length s then ""
          else String.sub s (q + 1) (String.length s - q - 1) in
        if suffix = "" then
          Some {
            RDF_Graph_Executable.lexical_form = lexical;
            datatype = RDF_Graph_Executable.xsd_string;
            lang_tag = FStar_Pervasives_Native.None;
          }
        else if String.length suffix >= 1 && suffix.[0] = '@' then
          Some {
            RDF_Graph_Executable.lexical_form = lexical;
            datatype = RDF_Graph_Executable.rdf_lang_string;
            lang_tag = FStar_Pervasives_Native.Some (String.sub suffix 1 (String.length suffix - 1));
          }
        else if String.length suffix >= 4 && String.sub suffix 0 2 = "^^" then
          (match parse_iri_token (String.sub suffix 2 (String.length suffix - 2)) with
           | Some dt ->
             Some {
               RDF_Graph_Executable.lexical_form = lexical;
               datatype = dt;
               lang_tag = FStar_Pervasives_Native.None;
             }
           | None -> None)
        else
          None

  let parse_subject s =
    match parse_iri_token s with
    | Some iri -> Some (RDF_Graph_Executable.S_IRI iri)
    | None ->
      if String.length s >= 2 && String.sub s 0 2 = "_:" then
        Some (RDF_Graph_Executable.S_BNode (String.sub s 2 (String.length s - 2)))
      else
        None

  let parse_object s =
    match parse_iri_token s with
    | Some iri -> Some (RDF_Graph_Executable.T_IRI iri)
    | None ->
      if String.length s >= 2 && String.sub s 0 2 = "_:" then
        Some (RDF_Graph_Executable.T_BNode (String.sub s 2 (String.length s - 2)))
      else
        match parse_literal_token s with
        | Some lit -> Some (RDF_Graph_Executable.T_Literal lit)
        | None -> None

  let parse_graph s =
    if s = "DEFAULT" then Some None
    else match parse_iri_token s with
      | Some iri -> Some (Some iri)
      | None -> None

  let next_id tables =
    let max_id tbl =
      Hashtbl.fold (fun _ id acc -> if Z.gt id acc then id else acc) tbl Z.zero in
    Z.succ (List.fold_left (fun acc tbl ->
      let m = max_id tbl in if Z.gt m acc then m else acc
    ) Z.zero tables)

  let intern_subject cache s =
    let key = subject_key s in
    match Hashtbl.find_opt cache.subject_to_id key with
    | Some id -> id
    | None ->
      let id = next_id [cache.subject_to_id; cache.predicate_to_id; cache.object_to_id; cache.graph_to_id] in
      Hashtbl.add cache.subject_to_id key id;
      Hashtbl.add cache.id_to_subject id s;
      id

  let intern_predicate cache p =
    match Hashtbl.find_opt cache.predicate_to_id p with
    | Some id -> id
    | None ->
      let id = next_id [cache.subject_to_id; cache.predicate_to_id; cache.object_to_id; cache.graph_to_id] in
      Hashtbl.add cache.predicate_to_id p id;
      Hashtbl.add cache.id_to_predicate id p;
      id

  let intern_object cache o =
    let key = object_key o in
    match Hashtbl.find_opt cache.object_to_id key with
    | Some id -> id
    | None ->
      let id = next_id [cache.subject_to_id; cache.predicate_to_id; cache.object_to_id; cache.graph_to_id] in
      Hashtbl.add cache.object_to_id key id;
      Hashtbl.add cache.id_to_object id o;
      id

  let intern_graph cache g =
    match Hashtbl.find_opt cache.graph_to_id g with
    | Some id -> id
    | None ->
      let id = next_id [cache.subject_to_id; cache.predicate_to_id; cache.object_to_id; cache.graph_to_id] in
      Hashtbl.add cache.graph_to_id g id;
      Hashtbl.add cache.id_to_graph id g;
      id

  let build_summary artifact_path quads graph_count =
    let num_quads = Z.of_int (List.length quads) in
    let row_groups =
      match Parquet_Footer.probe_parquet_row_group_count artifact_path with
      | FStar_Pervasives_Native.None -> Z.one
      | FStar_Pervasives_Native.Some n -> n in
    let mk_col kind =
      {
        ccs_kind = kind;
        ccs_num_values = num_quads;
        ccs_null_count = Z.zero;
        ccs_encoding = CE_Delta;
      } in
    FStar_Pervasives_Native.Some {
      cas_path = artifact_path;
      cas_num_quads = num_quads;
      cas_num_row_groups = row_groups;
      cas_dictionary =
        FStar_Pervasives_Native.Some {
          cds_num_terms = num_quads;
          cds_num_graphs = Z.of_int graph_count;
          cds_bytes_strings = Z.zero;
        };
      cas_row_groups = [{
        crgs_index = Z.zero;
        crgs_num_rows = num_quads;
        crgs_columns = [mk_col CC_Subject; mk_col CC_Predicate; mk_col CC_Object; mk_col CC_Graph];
      }];
    }

  let load_cache artifact_path =
    match Hashtbl.find_opt caches artifact_path with
    | Some cache -> cache
    | None ->
      let value_count =
        match Parquet_Footer.probe_parquet_column_delta_length_byte_array_value_count artifact_path Z.zero with
        | FStar_Pervasives_Native.Some n -> Z.to_int n
        | FStar_Pervasives_Native.None -> failwith "Could not read COTTAS row count from Parquet value stream" in
      let cache = {
        quads = [];
        subject_to_id = Hashtbl.create 257;
        predicate_to_id = Hashtbl.create 257;
        object_to_id = Hashtbl.create 257;
        graph_to_id = Hashtbl.create 257;
        id_to_subject = Hashtbl.create 257;
        id_to_predicate = Hashtbl.create 257;
        id_to_object = Hashtbl.create 257;
        id_to_graph = Hashtbl.create 257;
        summary = FStar_Pervasives_Native.None;
      } in
      let quad_rev = ref [] in
      for i = 0 to value_count - 1 do
        let zi = Z.of_int i in
        let fetch col =
          match Parquet_Footer.probe_parquet_column_delta_length_byte_array_value_string_at artifact_path col zi with
          | FStar_Pervasives_Native.Some v -> v
          | FStar_Pervasives_Native.None ->
            failwith (Printf.sprintf "Missing Parquet value col=%s idx=%d" (Z.to_string col) i) in
        let s = match parse_subject (fetch Z.zero) with
          | Some v -> v | None -> failwith "Invalid COTTAS subject token" in
        let p = match parse_iri_token (fetch Z.one) with
          | Some v -> v | None -> failwith "Invalid COTTAS predicate token" in
        let o = match parse_object (fetch (Z.of_int 2)) with
          | Some v -> v | None -> failwith "Invalid COTTAS object token" in
        let g = match parse_graph (fetch (Z.of_int 3)) with
          | Some v -> v | None -> failwith "Invalid COTTAS graph token" in
        let s_id = intern_subject cache s in
        let p_id = intern_predicate cache p in
        let o_id = intern_object cache o in
        let g_id = match g with
          | None -> None
          | Some name -> Some (intern_graph cache name) in
        quad_rev := { qr_s = s_id; qr_p = p_id; qr_o = o_id; qr_g = g_id } :: !quad_rev
      done;
      let quads = List.rev !quad_rev in
      let summary = build_summary artifact_path quads (Hashtbl.length cache.graph_to_id) in
      let cache = { cache with quads; summary } in
      Hashtbl.add caches artifact_path cache;
      cache

  let cache_for_store ds = load_cache ds.cds_artifact_path

  let graph_name_of_ref cache id =
    match Hashtbl.find_opt cache.id_to_graph id with
    | Some g -> g
    | None -> failwith "Unknown COTTAS graph ref"

  let named_graphs_of_cache ds cache =
    Hashtbl.fold (fun id iri acc ->
      { cngs_name = iri; cngs_ref = id; cngs_dataset = ds } :: acc
    ) cache.id_to_graph []

  let search_rows ds bound =
    let cache = cache_for_store ds in
    let match_opt expected actual =
      match expected with
      | FStar_Pervasives_Native.None -> true
      | FStar_Pervasives_Native.Some e -> Z.equal e actual in
    let match_graph expected actual =
      match expected, actual with
      | FStar_Pervasives_Native.None, _ -> true
      | FStar_Pervasives_Native.Some e, Some a -> Z.equal e a
      | FStar_Pervasives_Native.Some _, None -> false in
    List.fold_right (fun row acc ->
      if match_opt bound.cbqp_s row.qr_s &&
         match_opt bound.cbqp_p row.qr_p &&
         match_opt bound.cbqp_o row.qr_o &&
         match_graph bound.cbqp_g row.qr_g
      then
        {
          cqpr_s = FStar_Pervasives_Native.Some row.qr_s;
          cqpr_p = FStar_Pervasives_Native.Some row.qr_p;
          cqpr_o = FStar_Pervasives_Native.Some row.qr_o;
          cqpr_g = (match row.qr_g with None -> FStar_Pervasives_Native.None | Some g -> FStar_Pervasives_Native.Some g);
        } :: acc
      else
        acc
    ) cache.quads []
end

let cottas_open_dataset_store (artifact_path : Prims.string)
  (summary : cottas_artifact_summary FStar_Pervasives_Native.option) :
  cottas_dataset_store FStar_Pervasives_Native.option=
  let cache = Ballyhoo_cottas_runtime.load_cache artifact_path in
  FStar_Pervasives_Native.Some {
    cds_artifact_path = artifact_path;
    cds_summary =
      (match summary with
       | FStar_Pervasives_Native.Some s -> FStar_Pervasives_Native.Some s
       | FStar_Pervasives_Native.None -> cache.Ballyhoo_cottas_runtime.summary);
    cds_handle = ();
  }

let cottas_close_dataset_store (_ : cottas_dataset_store) : Prims.unit = ()

let cottas_dataset_summary (ds : cottas_dataset_store) :
  cottas_artifact_summary FStar_Pervasives_Native.option=
  (Ballyhoo_cottas_runtime.cache_for_store ds).Ballyhoo_cottas_runtime.summary

let cottas_named_graphs (ds : cottas_dataset_store) :
  cottas_named_graph_store Prims.list=
  let cache = Ballyhoo_cottas_runtime.cache_for_store ds in
  Ballyhoo_cottas_runtime.named_graphs_of_cache ds cache

let cottas_lookup_named_graph (ds : cottas_dataset_store)
  (name : RDF_Graph_Executable.iri) :
  cottas_named_graph_store FStar_Pervasives_Native.option=
  let rec loop = function
    | [] -> FStar_Pervasives_Native.None
    | ng :: rest ->
      if ng.cngs_name = name then FStar_Pervasives_Native.Some ng else loop rest
  in
  loop (cottas_named_graphs ds)

let cottas_encode_subject (ds : cottas_dataset_store)
  (s : RDF_Graph_Executable.subject) :
  cottas_term_ref FStar_Pervasives_Native.option=
  Hashtbl.find_opt (Ballyhoo_cottas_runtime.cache_for_store ds).Ballyhoo_cottas_runtime.subject_to_id
    (Ballyhoo_cottas_runtime.subject_key s)

let cottas_encode_predicate (ds : cottas_dataset_store)
  (p : RDF_Graph_Executable.wf_iri) :
  cottas_term_ref FStar_Pervasives_Native.option=
  Hashtbl.find_opt (Ballyhoo_cottas_runtime.cache_for_store ds).Ballyhoo_cottas_runtime.predicate_to_id p

let cottas_encode_object (ds : cottas_dataset_store)
  (o : RDF_Graph_Executable.rdf_term) :
  cottas_term_ref FStar_Pervasives_Native.option=
  Hashtbl.find_opt (Ballyhoo_cottas_runtime.cache_for_store ds).Ballyhoo_cottas_runtime.object_to_id
    (Ballyhoo_cottas_runtime.object_key o)

let cottas_encode_graph_name (ds : cottas_dataset_store)
  (g : RDF_Graph_Executable.iri) :
  cottas_graph_ref FStar_Pervasives_Native.option=
  Hashtbl.find_opt (Ballyhoo_cottas_runtime.cache_for_store ds).Ballyhoo_cottas_runtime.graph_to_id g

let cottas_decode_subject (ds : cottas_dataset_store)
  (id : cottas_term_ref) : RDF_Graph_Executable.subject=
  match Hashtbl.find_opt (Ballyhoo_cottas_runtime.cache_for_store ds).Ballyhoo_cottas_runtime.id_to_subject id with
  | Some s -> s
  | None -> failwith "Unknown COTTAS subject ref"

let cottas_decode_predicate (ds : cottas_dataset_store)
  (id : cottas_term_ref) : RDF_Graph_Executable.wf_iri=
  match Hashtbl.find_opt (Ballyhoo_cottas_runtime.cache_for_store ds).Ballyhoo_cottas_runtime.id_to_predicate id with
  | Some p -> p
  | None -> failwith "Unknown COTTAS predicate ref"

let cottas_decode_object (ds : cottas_dataset_store)
  (id : cottas_term_ref) : RDF_Graph_Executable.rdf_term=
  match Hashtbl.find_opt (Ballyhoo_cottas_runtime.cache_for_store ds).Ballyhoo_cottas_runtime.id_to_object id with
  | Some o -> o
  | None -> failwith "Unknown COTTAS object ref"

let cottas_decode_graph_name (ds : cottas_dataset_store)
  (id : cottas_graph_ref) : RDF_Graph_Executable.iri=
  (Ballyhoo_cottas_runtime.graph_name_of_ref (Ballyhoo_cottas_runtime.cache_for_store ds) id)

let cottas_search (ds : cottas_dataset_store) (bound : cottas_bound_qp) :
  cottas_qp_row Prims.list=
  Ballyhoo_cottas_runtime.search_rows ds bound

let cottas_estimate (ds : cottas_dataset_store) (bound : cottas_bound_qp)
  : Prims.nat=
  FStar_List_Tot_Base.length (cottas_search ds bound)

let cottas_predicate_present_in_graph (ng : cottas_named_graph_store)
  (pred : RDF_Graph_Executable.wf_iri) : Prims.bool=
  match cottas_encode_predicate ng.cngs_dataset pred with
  | FStar_Pervasives_Native.None -> false
  | FStar_Pervasives_Native.Some pred_ref ->
    cottas_estimate ng.cngs_dataset {
      cbqp_s = FStar_Pervasives_Native.None;
      cbqp_p = FStar_Pervasives_Native.Some pred_ref;
      cbqp_o = FStar_Pervasives_Native.None;
      cbqp_g = FStar_Pervasives_Native.Some ng.cngs_ref;
    } > Prims.int_zero

let cottas_graph_candidates_for_predicate (ds : cottas_dataset_store)
  (pred : RDF_Graph_Executable.wf_iri) :
  cottas_named_graph_store Prims.list=
  FStar_List_Tot_Base.filter
    (fun ng -> cottas_predicate_present_in_graph ng pred)
    (cottas_named_graphs ds)
let cottas_build_bound_qp (ds : cottas_dataset_store)
  (s : RDF_Graph_Executable.subject FStar_Pervasives_Native.option)
  (p : RDF_Graph_Executable.wf_iri FStar_Pervasives_Native.option)
  (o : RDF_Graph_Executable.rdf_term FStar_Pervasives_Native.option)
  (g : RDF_Graph_Executable.iri FStar_Pervasives_Native.option) :
  cottas_bound_qp=
  {
    cbqp_s =
      (match s with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some sv -> cottas_encode_subject ds sv);
    cbqp_p =
      (match p with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some pv -> cottas_encode_predicate ds pv);
    cbqp_o =
      (match o with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some ov -> cottas_encode_object ds ov);
    cbqp_g =
      (match g with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some gv -> cottas_encode_graph_name ds gv)
  }
let cottas_row_to_quad (ds : cottas_dataset_store) (row : cottas_qp_row) :
  (RDF_Graph_Executable.triple * RDF_Graph_Executable.iri
    FStar_Pervasives_Native.option) FStar_Pervasives_Native.option=
  match ((row.cqpr_s), (row.cqpr_p), (row.cqpr_o)) with
  | (FStar_Pervasives_Native.Some sr, FStar_Pervasives_Native.Some pr,
     FStar_Pervasives_Native.Some orf) ->
      FStar_Pervasives_Native.Some
        ({
           RDF_Graph_Executable.s = (cottas_decode_subject ds sr);
           RDF_Graph_Executable.p = (cottas_decode_predicate ds pr);
           RDF_Graph_Executable.o = (cottas_decode_object ds orf)
         },
          ((match row.cqpr_g with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some gr ->
                FStar_Pervasives_Native.Some (cottas_decode_graph_name ds gr))))
  | uu___ -> FStar_Pervasives_Native.None
let rec cottas_rows_to_quads (ds : cottas_dataset_store)
  (rows : cottas_qp_row Prims.list) :
  (RDF_Graph_Executable.triple * RDF_Graph_Executable.iri
    FStar_Pervasives_Native.option) Prims.list=
  match rows with
  | [] -> []
  | row::rest ->
      let rest' = cottas_rows_to_quads ds rest in
      (match cottas_row_to_quad ds row with
       | FStar_Pervasives_Native.Some q -> q :: rest'
       | FStar_Pervasives_Native.None -> rest')
