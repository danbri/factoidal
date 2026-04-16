#!/bin/bash
# Experimental runtime glue for Parser.BallyhooCOTTAS.ml
#
# The format semantics remain in F* through Parquet.Footer probing; this glue
# only materializes runtime caches and backend hooks from those verified probes.

set -euo pipefail

OUTDIR="$1"

if [[ -f "$OUTDIR" && "$OUTDIR" == *.ml ]]; then
  OUTDIR="$(dirname "$OUTDIR")"
fi

FILE="$OUTDIR/Parser_BallyhooCOTTAS.ml"
if [[ ! -f "$FILE" ]]; then
  echo "  Warning: $FILE not found, skipping Ballyhoo COTTAS runtime glue" >&2
  exit 0
fi

if grep -q 'module Ballyhoo_cottas_runtime' "$FILE"; then
  echo "  Ballyhoo COTTAS runtime glue already present."
  exit 0
fi

python3 - "$FILE" <<'PYEOF'
import sys
from pathlib import Path

path = Path(sys.argv[1])
content = path.read_text()

marker = """let cottas_open_dataset_store (artifact_path : Prims.string)
  (summary : cottas_artifact_summary FStar_Pervasives_Native.option) :
  cottas_dataset_store FStar_Pervasives_Native.option=
  failwith
    "Not yet implemented: Parser.BallyhooCOTTAS.cottas_open_dataset_store"
"""

runtime = r'''
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
'''

replacements = {
    marker: runtime,
    """let cottas_dataset_summary (uu___ : cottas_dataset_store) :
  cottas_artifact_summary FStar_Pervasives_Native.option=
  failwith
    "Not yet implemented: Parser.BallyhooCOTTAS.cottas_dataset_summary"
""": "",
    """let cottas_named_graphs (uu___ : cottas_dataset_store) :
  cottas_named_graph_store Prims.list=
  failwith "Not yet implemented: Parser.BallyhooCOTTAS.cottas_named_graphs"
""": "",
    """let cottas_lookup_named_graph (uu___ : cottas_dataset_store)
  (uu___1 : RDF_Graph_Executable.iri) :
  cottas_named_graph_store FStar_Pervasives_Native.option=
  failwith
    "Not yet implemented: Parser.BallyhooCOTTAS.cottas_lookup_named_graph"
""": "",
    """let cottas_encode_subject (uu___ : cottas_dataset_store)
  (uu___1 : RDF_Graph_Executable.subject) :
  cottas_term_ref FStar_Pervasives_Native.option=
  failwith "Not yet implemented: Parser.BallyhooCOTTAS.cottas_encode_subject"
""": "",
    """let cottas_encode_predicate (uu___ : cottas_dataset_store)
  (uu___1 : RDF_Graph_Executable.wf_iri) :
  cottas_term_ref FStar_Pervasives_Native.option=
  failwith
    "Not yet implemented: Parser.BallyhooCOTTAS.cottas_encode_predicate"
""": "",
    """let cottas_encode_object (uu___ : cottas_dataset_store)
  (uu___1 : RDF_Graph_Executable.rdf_term) :
  cottas_term_ref FStar_Pervasives_Native.option=
  failwith "Not yet implemented: Parser.BallyhooCOTTAS.cottas_encode_object"
""": "",
    """let cottas_encode_graph_name (uu___ : cottas_dataset_store)
  (uu___1 : RDF_Graph_Executable.iri) :
  cottas_graph_ref FStar_Pervasives_Native.option=
  failwith
    "Not yet implemented: Parser.BallyhooCOTTAS.cottas_encode_graph_name"
""": "",
    """let cottas_decode_subject (uu___ : cottas_dataset_store)
  (uu___1 : cottas_term_ref) : RDF_Graph_Executable.subject=
  failwith "Not yet implemented: Parser.BallyhooCOTTAS.cottas_decode_subject"
""": "",
    """let cottas_decode_predicate (uu___ : cottas_dataset_store)
  (uu___1 : cottas_term_ref) : RDF_Graph_Executable.wf_iri=
  failwith
    "Not yet implemented: Parser.BallyhooCOTTAS.cottas_decode_predicate"
""": "",
    """let cottas_decode_object (uu___ : cottas_dataset_store)
  (uu___1 : cottas_term_ref) : RDF_Graph_Executable.rdf_term=
  failwith "Not yet implemented: Parser.BallyhooCOTTAS.cottas_decode_object"
""": "",
    """let cottas_decode_graph_name (uu___ : cottas_dataset_store)
  (uu___1 : cottas_graph_ref) : RDF_Graph_Executable.iri=
  failwith
    "Not yet implemented: Parser.BallyhooCOTTAS.cottas_decode_graph_name"
""": "",
    """let cottas_search (uu___ : cottas_dataset_store) (uu___1 : cottas_bound_qp) :
  cottas_qp_row Prims.list=
  failwith "Not yet implemented: Parser.BallyhooCOTTAS.cottas_search"
""": "",
    """let cottas_estimate (uu___ : cottas_dataset_store) (uu___1 : cottas_bound_qp)
  : Prims.nat=
  failwith "Not yet implemented: Parser.BallyhooCOTTAS.cottas_estimate"
""": "",
    """let cottas_predicate_present_in_graph (uu___ : cottas_named_graph_store)
  (uu___1 : RDF_Graph_Executable.wf_iri) : Prims.bool=
  failwith
    "Not yet implemented: Parser.BallyhooCOTTAS.cottas_predicate_present_in_graph"
""": "",
    """let cottas_graph_candidates_for_predicate (uu___ : cottas_dataset_store)
  (uu___1 : RDF_Graph_Executable.wf_iri) :
  cottas_named_graph_store Prims.list=
  failwith
    "Not yet implemented: Parser.BallyhooCOTTAS.cottas_graph_candidates_for_predicate"
""": "",
}

for old, new in replacements.items():
    if old not in content:
        if old == marker:
            raise SystemExit("cottas_open_dataset_store stub not found")
        continue
    content = content.replace(old, new, 1)

path.write_text(content)
PYEOF
