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
    (* Vav2 (2026-04-25): O(1) per-column id counters. The previous
       [next_id] walked all four hashtables (Hashtbl.fold) on every
       intern call -- O(N) per row per column, which was O(N^2) overall
       for the 3.14 M-quad parliament COTTAS load. Per-column monotonic
       counters preserve semantics (id spaces were never shared across
       columns -- decode functions dispatch off the column-typed
       hashtable) and make each intern O(1). Single-threaded load => no
       lock needed. *)
    subj_counter: int ref;
    pred_counter: int ref;
    obj_counter: int ref;
    graph_counter: int ref;
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

  (* Vav2 (2026-04-25): O(1) per-column allocators. Each call bumps a
     mutable counter and returns the prior value as a Z.t. Counters start
     at 1 to preserve the previous behaviour (old [next_id] folded from
     Z.zero then Z.succ'd, so the first id was always Z.one). *)
  let alloc_subject_id cache =
    let id = !(cache.subj_counter) in
    cache.subj_counter := id + 1;
    Z.of_int id

  let alloc_predicate_id cache =
    let id = !(cache.pred_counter) in
    cache.pred_counter := id + 1;
    Z.of_int id

  let alloc_object_id cache =
    let id = !(cache.obj_counter) in
    cache.obj_counter := id + 1;
    Z.of_int id

  let alloc_graph_id cache =
    let id = !(cache.graph_counter) in
    cache.graph_counter := id + 1;
    Z.of_int id

  let intern_subject cache s =
    let key = subject_key s in
    match Hashtbl.find_opt cache.subject_to_id key with
    | Some id -> id
    | None ->
      let id = alloc_subject_id cache in
      Hashtbl.add cache.subject_to_id key id;
      Hashtbl.add cache.id_to_subject id s;
      id

  let intern_predicate cache p =
    match Hashtbl.find_opt cache.predicate_to_id p with
    | Some id -> id
    | None ->
      let id = alloc_predicate_id cache in
      Hashtbl.add cache.predicate_to_id p id;
      Hashtbl.add cache.id_to_predicate id p;
      id

  let intern_object cache o =
    let key = object_key o in
    match Hashtbl.find_opt cache.object_to_id key with
    | Some id -> id
    | None ->
      let id = alloc_object_id cache in
      Hashtbl.add cache.object_to_id key id;
      Hashtbl.add cache.id_to_object id o;
      id

  let intern_graph cache g =
    match Hashtbl.find_opt cache.graph_to_id g with
    | Some id -> id
    | None ->
      let id = alloc_graph_id cache in
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

  (* Codex Phase 1 (2026-04-25): bulk per-column decode.
     Previously this loop did 4 per-cell calls per row × N rows
     (~12.6 M for the 3.14 M-quad parliament COTTAS), each of which
     re-decompressed the column page and re-walked every prior length —
     a per-column O(N^2) blowup.

     Bet5 / issue #98 Gap B (2026-04-25): walk every row group, not just
     the first. The F* helper `probe_parquet_column_decode_all_row_groups`
     dispatches per-row-group between DELTA_LENGTH_BYTE_ARRAY (cols 0+2:
     subjects + objects) and RLE_DICTIONARY (cols 1+3: predicates + graphs),
     concatenating the per-row-group results. For the 25-row-group
     parliament COTTAS we now load all 3.14 M rows instead of the first
     ~125 k. *)
  let decode_column artifact_path col_idx =
    match Parquet_Footer.probe_parquet_column_decode_all_row_groups
            artifact_path (Z.of_int col_idx) with
    | FStar_Pervasives_Native.None ->
      failwith (Printf.sprintf "Could not bulk-decode COTTAS column %d" col_idx)
    | FStar_Pervasives_Native.Some lst ->
      (* lst : (string option) list  in row order. Convert to an array of
         strings so the row-zip below is O(1) per row. *)
      let arr = Array.of_list lst in
      Array.map (function
        | FStar_Pervasives_Native.Some v -> v
        | FStar_Pervasives_Native.None ->
          failwith (Printf.sprintf "Missing COTTAS cell in column %d" col_idx))
        arr

  let load_cache artifact_path =
    match Hashtbl.find_opt caches artifact_path with
    | Some cache -> cache
    | None ->
      let s_col = decode_column artifact_path 0 in
      let p_col = decode_column artifact_path 1 in
      let o_col = decode_column artifact_path 2 in
      let g_col = decode_column artifact_path 3 in
      let value_count = Array.length s_col in
      if Array.length p_col <> value_count
         || Array.length o_col <> value_count
         || Array.length g_col <> value_count then
        failwith (Printf.sprintf
          "COTTAS column row counts disagree: s=%d p=%d o=%d g=%d"
          value_count (Array.length p_col) (Array.length o_col) (Array.length g_col));
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
        subj_counter = ref 1;
        pred_counter = ref 1;
        obj_counter = ref 1;
        graph_counter = ref 1;
        summary = FStar_Pervasives_Native.None;
      } in
      let quad_rev = ref [] in
      for i = 0 to value_count - 1 do
        let s = match parse_subject s_col.(i) with
          | Some v -> v | None -> failwith "Invalid COTTAS subject token" in
        let p = match parse_iri_token p_col.(i) with
          | Some v -> v | None -> failwith "Invalid COTTAS predicate token" in
        let o = match parse_object o_col.(i) with
          | Some v -> v | None -> failwith "Invalid COTTAS object token" in
        let g = match parse_graph g_col.(i) with
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
type cottas_ondisk_handle = unit
type cottas_ondisk_store =
  {
  cods_artifact_path: Prims.string ;
  cods_summary: cottas_artifact_summary FStar_Pervasives_Native.option ;
  cods_handle: cottas_ondisk_handle }
let __proj__Mkcottas_ondisk_store__item__cods_artifact_path
  (projectee : cottas_ondisk_store) : Prims.string=
  match projectee with
  | { cods_artifact_path; cods_summary; cods_handle;_} -> cods_artifact_path
let __proj__Mkcottas_ondisk_store__item__cods_summary
  (projectee : cottas_ondisk_store) :
  cottas_artifact_summary FStar_Pervasives_Native.option=
  match projectee with
  | { cods_artifact_path; cods_summary; cods_handle;_} -> cods_summary
let __proj__Mkcottas_ondisk_store__item__cods_handle
  (projectee : cottas_ondisk_store) : cottas_ondisk_handle=
  match projectee with
  | { cods_artifact_path; cods_summary; cods_handle;_} -> cods_handle

module Cottas_ondisk_runtime = struct
  open Stdlib
  (* `int` is shadowed by `open Prims` at the top of the file
     (Prims.int = Z.t).  Provide a local alias for plain OCaml int so
     hashtables and array indices keep the native machine-word type. *)
  type pint = Stdlib.Int.t

  (* On-disk handle. Every column is decoded once at open() to produce
     parallel `int array` term-id columns + a distinct-string dictionary
     per column. Parsed RDF terms (subject / wf_iri / rdf_term / iri)
     are decoded only on demand and cached.

     Memory budget for the parliament corpus (3.14M quads):
       4 * 3.14M ints (8 bytes each on 64-bit) ≈ 100 MB
       distinct-strings: 908K + 232 + 956K + ~26 ≈ ~150 MB
       parsed-term lazy caches: O(query coverage)
     vs. the old eager runtime which holds the full quad_row list +
     pre-parsed term hashtables AND a materialised rdf_dataset triple
     list — several hundred MB. *)

  type ondisk_handle = {
    path : string;
    summary : cottas_artifact_summary FStar_Pervasives_Native.option;
    (* Per-row term-ids. Length = total quad count. The id is the
       index into the corresponding distinct-string array below.
       For graphs, -1 represents the default graph (None). *)
    s_ids : pint array;
    p_ids : pint array;
    o_ids : pint array;
    g_ids : pint array;
    (* Distinct token strings, indexed by term-id. Subject/object/graph
       columns reuse the raw row-string set; predicate column is the
       dictionary that the RLE_DICTIONARY decoder produced. *)
    s_strs : string array;
    p_strs : string array;
    o_strs : string array;
    g_strs : string array;
    (* Reverse lookup tables: lazily filled on first encode call. *)
    s_revmap : (string, pint) Hashtbl.t;
    p_revmap : (string, pint) Hashtbl.t;
    o_revmap : (string, pint) Hashtbl.t;
    g_revmap : (string, pint) Hashtbl.t;
    (* Parsed-term decode caches: one per column.
       Filled as cottas_ondisk_decode_* is called for a given id. *)
    s_decoded : (pint, RDF_Graph_Executable.subject) Hashtbl.t;
    p_decoded : (pint, RDF_Graph_Executable.wf_iri) Hashtbl.t;
    o_decoded : (pint, RDF_Graph_Executable.rdf_term) Hashtbl.t;
    g_decoded : (pint, RDF_Graph_Executable.iri) Hashtbl.t;
    (* Predicate-present cache: built from p_ids on first query. *)
    mutable predicates_seen : (pint, unit) Hashtbl.t option;
  }

  (* Cache by artifact path, so re-opening the same file reuses the
     decoded columns. *)
  let handles : (string, ondisk_handle) Hashtbl.t = Hashtbl.create 17

  (* ---- Token parsing helpers (shared with the eager runtime). The
         logic is identical: an RDF token like "<iri>" / "_:b" /
         "\"lit\"^^<dt>" / "\"lit\"@en" gets parsed back to the
         RDF_Graph_Executable subject/wf_iri/rdf_term/iri shape. ---- *)

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
    if String.length s < 2 || s.[0] <> '"' then None
    else match find_unescaped_quote s with
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
        else None

  let parse_subject_str s =
    match parse_iri_token s with
    | Some iri -> Some (RDF_Graph_Executable.S_IRI iri)
    | None ->
      if String.length s >= 2 && String.sub s 0 2 = "_:" then
        Some (RDF_Graph_Executable.S_BNode (String.sub s 2 (String.length s - 2)))
      else
        None

  let parse_object_str s =
    match parse_iri_token s with
    | Some iri -> Some (RDF_Graph_Executable.T_IRI iri)
    | None ->
      if String.length s >= 2 && String.sub s 0 2 = "_:" then
        Some (RDF_Graph_Executable.T_BNode (String.sub s 2 (String.length s - 2)))
      else match parse_literal_token s with
        | Some lit -> Some (RDF_Graph_Executable.T_Literal lit)
        | None -> None

  let subject_key = function
    | RDF_Graph_Executable.S_IRI i -> "<" ^ i ^ ">"
    | RDF_Graph_Executable.S_BNode b -> "_:" ^ b

  let object_key = function
    | RDF_Graph_Executable.T_IRI i -> "<" ^ i ^ ">"
    | RDF_Graph_Executable.T_BNode b -> "_:" ^ b
    | RDF_Graph_Executable.T_Literal l ->
      let lex = l.RDF_Graph_Executable.lexical_form in
      let dt = l.RDF_Graph_Executable.datatype in
      let lang = l.RDF_Graph_Executable.lang_tag in
      let escape s =
        let b = Buffer.create (String.length s + 2) in
        String.iter (fun c ->
          match c with
          | '\\' -> Buffer.add_string b "\\\\"
          | '"' -> Buffer.add_string b "\\\""
          | c -> Buffer.add_char b c) s;
        Buffer.contents b in
      (match lang with
       | FStar_Pervasives_Native.Some tag ->
         "\"" ^ escape lex ^ "\"@" ^ tag
       | FStar_Pervasives_Native.None ->
         if dt = RDF_Graph_Executable.xsd_string then
           "\"" ^ escape lex ^ "\""
         else
           "\"" ^ escape lex ^ "\"^^<" ^ dt ^ ">")

  (* Build distinct-string dictionary + per-row id array from a raw
     row-of-strings array. *)
  let build_column (raw : string array) : (pint array * string array) =
    let revmap : (string, pint) Hashtbl.t = Hashtbl.create (Array.length raw / 2 + 17) in
    let strs : Buffer.t = Buffer.create 0 in
    let _ = strs in (* unused; kept to mirror approach *)
    let strs_list = ref [] in
    let next_id = ref 0 in
    let ids = Array.make (Array.length raw) 0 in
    for i = 0 to Array.length raw - 1 do
      let r = raw.(i) in
      let id =
        match Hashtbl.find_opt revmap r with
        | Some id -> id
        | None ->
          let id = !next_id in
          Hashtbl.add revmap r id;
          strs_list := r :: !strs_list;
          incr next_id;
          id in
      ids.(i) <- id
    done;
    let strs_arr = Array.make !next_id "" in
    List.iteri (fun i s ->
      strs_arr.(!next_id - 1 - i) <- s) !strs_list;
    (ids, strs_arr)

  let build_graph_column (raw : string array) : (pint array * string array) =
    (* Graph column: "DEFAULT" maps to id -1 (sentinel for "no graph").
       Other rows use IRIs (parsed from "<iri>"). *)
    let revmap : (string, pint) Hashtbl.t = Hashtbl.create 257 in
    let strs_list = ref [] in
    let next_id = ref 0 in
    let ids = Array.make (Array.length raw) 0 in
    for i = 0 to Array.length raw - 1 do
      let r = raw.(i) in
      if r = "DEFAULT" then ids.(i) <- -1
      else
        let id = match Hashtbl.find_opt revmap r with
          | Some id -> id
          | None ->
            let id = !next_id in
            Hashtbl.add revmap r id;
            strs_list := r :: !strs_list;
            incr next_id;
            id in
        ids.(i) <- id
    done;
    let strs_arr = Array.make !next_id "" in
    List.iteri (fun i s ->
      strs_arr.(!next_id - 1 - i) <- s) !strs_list;
    (ids, strs_arr)

  (* Decode all cells from a column page. Reuses the same F* helper as
     the eager runtime — `probe_parquet_column_decode_all`. *)
  let decode_column_strings artifact_path col_idx : string array =
    match Parquet_Footer.probe_parquet_column_decode_all
            artifact_path (Z.of_int col_idx) with
    | FStar_Pervasives_Native.None ->
      failwith (Printf.sprintf "COTTAS on-disk: could not decode column %d" col_idx)
    | FStar_Pervasives_Native.Some lst ->
      let arr = Array.of_list lst in
      Array.map (function
        | FStar_Pervasives_Native.Some v -> v
        | FStar_Pervasives_Native.None ->
          failwith (Printf.sprintf "COTTAS on-disk: missing cell in column %d" col_idx))
        arr

  let build_summary_for_handle artifact_path total_rows graph_count =
    let row_groups =
      match Parquet_Footer.probe_parquet_row_group_count artifact_path with
      | FStar_Pervasives_Native.None -> Z.one
      | FStar_Pervasives_Native.Some n -> n in
    let mk_col kind =
      {
        ccs_kind = kind;
        ccs_num_values = Z.of_int total_rows;
        ccs_null_count = Z.zero;
        ccs_encoding = CE_Delta;
      } in
    FStar_Pervasives_Native.Some {
      cas_path = artifact_path;
      cas_num_quads = Z.of_int total_rows;
      cas_num_row_groups = row_groups;
      cas_dictionary =
        FStar_Pervasives_Native.Some {
          cds_num_terms = Z.of_int total_rows;
          cds_num_graphs = Z.of_int graph_count;
          cds_bytes_strings = Z.zero;
        };
      cas_row_groups = [{
        crgs_index = Z.zero;
        crgs_num_rows = Z.of_int total_rows;
        crgs_columns = [mk_col CC_Subject; mk_col CC_Predicate; mk_col CC_Object; mk_col CC_Graph];
      }];
    }

  let load_handle artifact_path =
    match Hashtbl.find_opt handles artifact_path with
    | Some h -> h
    | None ->
      let s_raw = decode_column_strings artifact_path 0 in
      let p_raw = decode_column_strings artifact_path 1 in
      let o_raw = decode_column_strings artifact_path 2 in
      let g_raw = decode_column_strings artifact_path 3 in
      let value_count = Array.length s_raw in
      if Array.length p_raw <> value_count
         || Array.length o_raw <> value_count
         || Array.length g_raw <> value_count then
        failwith (Printf.sprintf
          "COTTAS on-disk: column row counts disagree: s=%d p=%d o=%d g=%d"
          value_count (Array.length p_raw) (Array.length o_raw) (Array.length g_raw));
      let (s_ids, s_strs) = build_column s_raw in
      let (p_ids, p_strs) = build_column p_raw in
      let (o_ids, o_strs) = build_column o_raw in
      let (g_ids, g_strs) = build_graph_column g_raw in
      let h = {
        path = artifact_path;
        summary = build_summary_for_handle artifact_path value_count (Array.length g_strs);
        s_ids; p_ids; o_ids; g_ids;
        s_strs; p_strs; o_strs; g_strs;
        s_revmap = Hashtbl.create (Array.length s_strs * 2 + 17);
        p_revmap = Hashtbl.create (Array.length p_strs * 2 + 17);
        o_revmap = Hashtbl.create (Array.length o_strs * 2 + 17);
        g_revmap = Hashtbl.create (Array.length g_strs * 2 + 17);
        s_decoded = Hashtbl.create 257;
        p_decoded = Hashtbl.create 257;
        o_decoded = Hashtbl.create 257;
        g_decoded = Hashtbl.create 257;
        predicates_seen = None;
      } in
      Hashtbl.add handles artifact_path h;
      h

  (* Fill the reverse map for a column on first encode call. *)
  let ensure_revmap (revmap : (string, pint) Hashtbl.t) (strs : string array) =
    if Hashtbl.length revmap = 0 && Array.length strs > 0 then
      Array.iteri (fun i s -> Hashtbl.add revmap s i) strs

  let encode_subject (h : ondisk_handle) (s : RDF_Graph_Executable.subject) : pint option =
    ensure_revmap h.s_revmap h.s_strs;
    Hashtbl.find_opt h.s_revmap (subject_key s)

  let encode_predicate (h : ondisk_handle) (p : RDF_Graph_Executable.wf_iri) : pint option =
    ensure_revmap h.p_revmap h.p_strs;
    Hashtbl.find_opt h.p_revmap ("<" ^ p ^ ">")

  let encode_object (h : ondisk_handle) (o : RDF_Graph_Executable.rdf_term) : pint option =
    ensure_revmap h.o_revmap h.o_strs;
    Hashtbl.find_opt h.o_revmap (object_key o)

  let encode_graph_name (h : ondisk_handle) (g : RDF_Graph_Executable.iri) : pint option =
    ensure_revmap h.g_revmap h.g_strs;
    Hashtbl.find_opt h.g_revmap ("<" ^ g ^ ">")

  let decode_subject (h : ondisk_handle) (id : pint) : RDF_Graph_Executable.subject =
    match Hashtbl.find_opt h.s_decoded id with
    | Some s -> s
    | None ->
      if id < 0 || id >= Array.length h.s_strs then
        failwith (Printf.sprintf "COTTAS on-disk: subject id %d out of range" id);
      let s = match parse_subject_str h.s_strs.(id) with
        | Some v -> v
        | None ->
          failwith (Printf.sprintf "COTTAS on-disk: invalid subject token %s" h.s_strs.(id)) in
      Hashtbl.add h.s_decoded id s;
      s

  let decode_predicate (h : ondisk_handle) (id : pint) : RDF_Graph_Executable.wf_iri =
    match Hashtbl.find_opt h.p_decoded id with
    | Some p -> p
    | None ->
      if id < 0 || id >= Array.length h.p_strs then
        failwith (Printf.sprintf "COTTAS on-disk: predicate id %d out of range" id);
      let p = match parse_iri_token h.p_strs.(id) with
        | Some iri -> iri
        | None ->
          failwith (Printf.sprintf "COTTAS on-disk: invalid predicate token %s" h.p_strs.(id)) in
      Hashtbl.add h.p_decoded id p;
      p

  let decode_object (h : ondisk_handle) (id : pint) : RDF_Graph_Executable.rdf_term =
    match Hashtbl.find_opt h.o_decoded id with
    | Some o -> o
    | None ->
      if id < 0 || id >= Array.length h.o_strs then
        failwith (Printf.sprintf "COTTAS on-disk: object id %d out of range" id);
      let o = match parse_object_str h.o_strs.(id) with
        | Some v -> v
        | None ->
          failwith (Printf.sprintf "COTTAS on-disk: invalid object token %s" h.o_strs.(id)) in
      Hashtbl.add h.o_decoded id o;
      o

  let decode_graph_name (h : ondisk_handle) (id : pint) : RDF_Graph_Executable.iri =
    match Hashtbl.find_opt h.g_decoded id with
    | Some g -> g
    | None ->
      if id < 0 || id >= Array.length h.g_strs then
        failwith (Printf.sprintf "COTTAS on-disk: graph id %d out of range" id);
      let g = match parse_iri_token h.g_strs.(id) with
        | Some iri -> iri
        | None ->
          failwith (Printf.sprintf "COTTAS on-disk: invalid graph token %s" h.g_strs.(id)) in
      Hashtbl.add h.g_decoded id g;
      g

  (* Search: walk per-row id arrays comparing against bound term-ids.
     Pure integer comparison — no parsed-term materialisation per row.
     Returns the matched rows as cottas_qp_row records (the term-ids).
     Caller uses cottas_ondisk_row_to_quad to decode terms on-demand. *)
  let search_rows (h : ondisk_handle) (bound : cottas_bound_qp) : cottas_qp_row list =
    let opt_to_int = function
      | FStar_Pervasives_Native.None -> None
      | FStar_Pervasives_Native.Some z -> Some (Z.to_int z) in
    let bound_s = opt_to_int bound.cbqp_s in
    let bound_p = opt_to_int bound.cbqp_p in
    let bound_o = opt_to_int bound.cbqp_o in
    let bound_g = opt_to_int bound.cbqp_g in
    let n = Array.length h.s_ids in
    let acc = ref [] in
    let int_match expected actual =
      match expected with
      | None -> true
      | Some e -> e = actual in
    let graph_match expected actual_id =
      match expected with
      | None -> true
      | Some e ->
        if actual_id < 0 then false   (* default-graph row, named bound *)
        else e = actual_id in
    for i = n - 1 downto 0 do
      let sid = h.s_ids.(i) in
      let pid = h.p_ids.(i) in
      let oid = h.o_ids.(i) in
      let gid = h.g_ids.(i) in
      if int_match bound_s sid &&
         int_match bound_p pid &&
         int_match bound_o oid &&
         graph_match bound_g gid
      then
        acc := {
          cqpr_s = FStar_Pervasives_Native.Some (Z.of_int sid);
          cqpr_p = FStar_Pervasives_Native.Some (Z.of_int pid);
          cqpr_o = FStar_Pervasives_Native.Some (Z.of_int oid);
          cqpr_g = if gid < 0 then FStar_Pervasives_Native.None
                   else FStar_Pervasives_Native.Some (Z.of_int gid);
        } :: !acc
    done;
    !acc

  let count_rows (h : ondisk_handle) (bound : cottas_bound_qp) : pint =
    let opt_to_int = function
      | FStar_Pervasives_Native.None -> None
      | FStar_Pervasives_Native.Some z -> Some (Z.to_int z) in
    let bound_s = opt_to_int bound.cbqp_s in
    let bound_p = opt_to_int bound.cbqp_p in
    let bound_o = opt_to_int bound.cbqp_o in
    let bound_g = opt_to_int bound.cbqp_g in
    let n = Array.length h.s_ids in
    let count = ref 0 in
    let int_match expected actual =
      match expected with None -> true | Some e -> e = actual in
    let graph_match expected actual_id =
      match expected with
      | None -> true
      | Some e -> if actual_id < 0 then false else e = actual_id in
    for i = 0 to n - 1 do
      if int_match bound_s h.s_ids.(i) &&
         int_match bound_p h.p_ids.(i) &&
         int_match bound_o h.o_ids.(i) &&
         graph_match bound_g h.g_ids.(i)
      then incr count
    done;
    !count

  let predicate_present (h : ondisk_handle) (pred : RDF_Graph_Executable.wf_iri) : bool =
    match encode_predicate h pred with
    | None -> false
    | Some pid ->
      let cache = match h.predicates_seen with
        | Some c -> c
        | None ->
          let c = Hashtbl.create (Array.length h.p_strs * 2 + 17) in
          for i = 0 to Array.length h.p_ids - 1 do
            Hashtbl.replace c h.p_ids.(i) ()
          done;
          h.predicates_seen <- Some c;
          c in
      Hashtbl.mem cache pid

  let named_graphs (h : ondisk_handle) : (RDF_Graph_Executable.iri * Z.t) list =
    let _ = decode_graph_name in
    let acc = ref [] in
    for i = Array.length h.g_strs - 1 downto 0 do
      match parse_iri_token h.g_strs.(i) with
      | Some iri ->
        acc := (iri, Z.of_int i) :: !acc
      | None -> ()
    done;
    !acc
end

let cottas_ondisk_open (artifact_path : Prims.string) :
  cottas_ondisk_store FStar_Pervasives_Native.option=
  let h = Cottas_ondisk_runtime.load_handle artifact_path in
  FStar_Pervasives_Native.Some {
    cods_artifact_path = artifact_path;
    cods_summary = h.Cottas_ondisk_runtime.summary;
    cods_handle = (Obj.magic h : cottas_ondisk_handle);
  }
let cottas_ondisk_summary (ds : cottas_ondisk_store) :
  cottas_artifact_summary FStar_Pervasives_Native.option=
  let h : Cottas_ondisk_runtime.ondisk_handle = Obj.magic ds.cods_handle in
  h.summary
let cottas_ondisk_encode_subject (ds : cottas_ondisk_store)
  (s : RDF_Graph_Executable.subject) :
  cottas_term_ref FStar_Pervasives_Native.option=
  let h : Cottas_ondisk_runtime.ondisk_handle = Obj.magic ds.cods_handle in
  match Cottas_ondisk_runtime.encode_subject h s with
  | None -> FStar_Pervasives_Native.None
  | Some i -> FStar_Pervasives_Native.Some (Z.of_int i)
let cottas_ondisk_encode_predicate (ds : cottas_ondisk_store)
  (p : RDF_Graph_Executable.wf_iri) :
  cottas_term_ref FStar_Pervasives_Native.option=
  let h : Cottas_ondisk_runtime.ondisk_handle = Obj.magic ds.cods_handle in
  match Cottas_ondisk_runtime.encode_predicate h p with
  | None -> FStar_Pervasives_Native.None
  | Some i -> FStar_Pervasives_Native.Some (Z.of_int i)
let cottas_ondisk_encode_object (ds : cottas_ondisk_store)
  (o : RDF_Graph_Executable.rdf_term) :
  cottas_term_ref FStar_Pervasives_Native.option=
  let h : Cottas_ondisk_runtime.ondisk_handle = Obj.magic ds.cods_handle in
  match Cottas_ondisk_runtime.encode_object h o with
  | None -> FStar_Pervasives_Native.None
  | Some i -> FStar_Pervasives_Native.Some (Z.of_int i)
let cottas_ondisk_encode_graph_name (ds : cottas_ondisk_store)
  (g : RDF_Graph_Executable.iri) :
  cottas_graph_ref FStar_Pervasives_Native.option=
  let h : Cottas_ondisk_runtime.ondisk_handle = Obj.magic ds.cods_handle in
  match Cottas_ondisk_runtime.encode_graph_name h g with
  | None -> FStar_Pervasives_Native.None
  | Some i -> FStar_Pervasives_Native.Some (Z.of_int i)
let cottas_ondisk_decode_subject (ds : cottas_ondisk_store)
  (id : cottas_term_ref) : RDF_Graph_Executable.subject=
  let h : Cottas_ondisk_runtime.ondisk_handle = Obj.magic ds.cods_handle in
  Cottas_ondisk_runtime.decode_subject h (Z.to_int id)
let cottas_ondisk_decode_predicate (ds : cottas_ondisk_store)
  (id : cottas_term_ref) : RDF_Graph_Executable.wf_iri=
  let h : Cottas_ondisk_runtime.ondisk_handle = Obj.magic ds.cods_handle in
  Cottas_ondisk_runtime.decode_predicate h (Z.to_int id)
let cottas_ondisk_decode_object (ds : cottas_ondisk_store)
  (id : cottas_term_ref) : RDF_Graph_Executable.rdf_term=
  let h : Cottas_ondisk_runtime.ondisk_handle = Obj.magic ds.cods_handle in
  Cottas_ondisk_runtime.decode_object h (Z.to_int id)
let cottas_ondisk_decode_graph_name (ds : cottas_ondisk_store)
  (id : cottas_graph_ref) : RDF_Graph_Executable.iri=
  let h : Cottas_ondisk_runtime.ondisk_handle = Obj.magic ds.cods_handle in
  Cottas_ondisk_runtime.decode_graph_name h (Z.to_int id)
let cottas_ondisk_search (ds : cottas_ondisk_store)
  (bound : cottas_bound_qp) : cottas_qp_row Prims.list=
  let h : Cottas_ondisk_runtime.ondisk_handle = Obj.magic ds.cods_handle in
  Cottas_ondisk_runtime.search_rows h bound
let cottas_ondisk_estimate (ds : cottas_ondisk_store)
  (bound : cottas_bound_qp) : Prims.nat=
  let h : Cottas_ondisk_runtime.ondisk_handle = Obj.magic ds.cods_handle in
  Z.of_int (Cottas_ondisk_runtime.count_rows h bound)
let cottas_ondisk_predicate_present (ds : cottas_ondisk_store)
  (pred : RDF_Graph_Executable.wf_iri) : Prims.bool=
  let h : Cottas_ondisk_runtime.ondisk_handle = Obj.magic ds.cods_handle in
  Cottas_ondisk_runtime.predicate_present h pred
let cottas_ondisk_named_graphs (ds : cottas_ondisk_store) :
  (RDF_Graph_Executable.iri * cottas_graph_ref) Prims.list=
  let h : Cottas_ondisk_runtime.ondisk_handle = Obj.magic ds.cods_handle in
  Cottas_ondisk_runtime.named_graphs h
let cottas_ondisk_build_bound_qp_opt (ds : cottas_ondisk_store)
  (s : RDF_Graph_Executable.subject FStar_Pervasives_Native.option)
  (p : RDF_Graph_Executable.wf_iri FStar_Pervasives_Native.option)
  (o : RDF_Graph_Executable.rdf_term FStar_Pervasives_Native.option)
  (g : RDF_Graph_Executable.iri FStar_Pervasives_Native.option) :
  cottas_bound_qp FStar_Pervasives_Native.option=
  let s' =
    match s with
    | FStar_Pervasives_Native.None ->
        FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
    | FStar_Pervasives_Native.Some sv ->
        (match cottas_ondisk_encode_subject ds sv with
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some r ->
             FStar_Pervasives_Native.Some (FStar_Pervasives_Native.Some r)) in
  let p' =
    match p with
    | FStar_Pervasives_Native.None ->
        FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
    | FStar_Pervasives_Native.Some pv ->
        (match cottas_ondisk_encode_predicate ds pv with
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some r ->
             FStar_Pervasives_Native.Some (FStar_Pervasives_Native.Some r)) in
  let o' =
    match o with
    | FStar_Pervasives_Native.None ->
        FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
    | FStar_Pervasives_Native.Some ov ->
        (match cottas_ondisk_encode_object ds ov with
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some r ->
             FStar_Pervasives_Native.Some (FStar_Pervasives_Native.Some r)) in
  let g' =
    match g with
    | FStar_Pervasives_Native.None ->
        FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
    | FStar_Pervasives_Native.Some gv ->
        (match cottas_ondisk_encode_graph_name ds gv with
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some r ->
             FStar_Pervasives_Native.Some (FStar_Pervasives_Native.Some r)) in
  match (s', p', o', g') with
  | (FStar_Pervasives_Native.Some sb, FStar_Pervasives_Native.Some pb,
     FStar_Pervasives_Native.Some ob, FStar_Pervasives_Native.Some gb) ->
      FStar_Pervasives_Native.Some
        { cbqp_s = sb; cbqp_p = pb; cbqp_o = ob; cbqp_g = gb }
  | uu___ -> FStar_Pervasives_Native.None
let cottas_ondisk_row_to_quad (ds : cottas_ondisk_store)
  (row : cottas_qp_row) :
  (RDF_Graph_Executable.triple * RDF_Graph_Executable.iri
    FStar_Pervasives_Native.option) FStar_Pervasives_Native.option=
  match ((row.cqpr_s), (row.cqpr_p), (row.cqpr_o)) with
  | (FStar_Pervasives_Native.Some sr, FStar_Pervasives_Native.Some pr,
     FStar_Pervasives_Native.Some orf) ->
      FStar_Pervasives_Native.Some
        ({
           RDF_Graph_Executable.s = (cottas_ondisk_decode_subject ds sr);
           RDF_Graph_Executable.p = (cottas_ondisk_decode_predicate ds pr);
           RDF_Graph_Executable.o = (cottas_ondisk_decode_object ds orf)
         },
          ((match row.cqpr_g with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some gr ->
                FStar_Pervasives_Native.Some
                  (cottas_ondisk_decode_graph_name ds gr))))
  | uu___ -> FStar_Pervasives_Native.None
let rec cottas_ondisk_rows_to_quads (ds : cottas_ondisk_store)
  (rows : cottas_qp_row Prims.list) :
  (RDF_Graph_Executable.triple * RDF_Graph_Executable.iri
    FStar_Pervasives_Native.option) Prims.list=
  match rows with
  | [] -> []
  | row::rest ->
      let rest' = cottas_ondisk_rows_to_quads ds rest in
      (match cottas_ondisk_row_to_quad ds row with
       | FStar_Pervasives_Native.Some q -> q :: rest'
       | FStar_Pervasives_Native.None -> rest')
