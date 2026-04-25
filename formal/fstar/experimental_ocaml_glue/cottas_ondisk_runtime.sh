#!/bin/bash
# Experimental runtime glue for the on-disk COTTAS backend
# (Parser.BallyhooCOTTAS.fst's `cottas_ondisk_*` assume vals).
#
# Issue #100 Phase 2.
#
# All format semantics live in F* through Parquet.Footer. This glue only
# stores the four per-column int arrays (term-ids = dictionary indexes for
# RLE_DICT columns, or per-row indexes into a distinct-string list for
# DELTA_LENGTH columns) and keeps the raw token-string per distinct id.
# Parsed RDF terms (subject / wf_iri / rdf_term) are decoded lazily on
# first decode call and cached.
#
# This is I/O glue + memory layout only. No semantic SPARQL/RDF logic
# lives here.

set -euo pipefail

OUTDIR="$1"

if [[ -f "$OUTDIR" && "$OUTDIR" == *.ml ]]; then
  OUTDIR="$(dirname "$OUTDIR")"
fi

FILE="$OUTDIR/Parser_BallyhooCOTTAS.ml"
if [[ ! -f "$FILE" ]]; then
  echo "  Warning: $FILE not found, skipping COTTAS on-disk runtime glue" >&2
  exit 0
fi

if grep -q 'module Cottas_ondisk_runtime' "$FILE"; then
  echo "  COTTAS on-disk runtime glue already present."
  exit 0
fi

python3 - "$FILE" <<'PYEOF'
import sys
from pathlib import Path

path = Path(sys.argv[1])
content = path.read_text()

# Anchor: the `cottas_ondisk_open` failwith stub (extracted from F*'s
# `assume val cottas_ondisk_open`). Replace with the runtime + the
# implementations of every cottas_ondisk_* assume val.
marker = """let cottas_ondisk_open (artifact_path : Prims.string) :
  cottas_ondisk_store FStar_Pervasives_Native.option=
  failwith "Not yet implemented: Parser.BallyhooCOTTAS.cottas_ondisk_open"
"""

runtime = r'''
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
    Printf.eprintf "[qof3-trace] decode_column_strings col_idx=%d path=%s\n%!" col_idx artifact_path;
    match Parquet_Footer.probe_parquet_column_decode_all
            artifact_path (Z.of_int col_idx) with
    | FStar_Pervasives_Native.None ->
      Printf.eprintf "[qof3-FATAL] decode_column_strings: could not decode column %d\n%!" col_idx;
      failwith (Printf.sprintf "COTTAS on-disk: could not decode column %d" col_idx)
    | FStar_Pervasives_Native.Some lst ->
      let arr = Array.of_list lst in
      Array.map (function
        | FStar_Pervasives_Native.Some v -> v
        | FStar_Pervasives_Native.None ->
          Printf.eprintf "[qof3-FATAL] decode_column_strings: missing cell in column %d\n%!" col_idx;
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
    Printf.eprintf "[qof3-trace] load_handle path=%s\n%!" artifact_path;
    match Hashtbl.find_opt handles artifact_path with
    | Some h ->
      Printf.eprintf "[qof3-trace] load_handle: cache hit\n%!"; h
    | None ->
      Printf.eprintf "[qof3-trace] load_handle: decoding 4 columns…\n%!";
      let s_raw = decode_column_strings artifact_path 0 in
      let p_raw = decode_column_strings artifact_path 1 in
      let o_raw = decode_column_strings artifact_path 2 in
      let g_raw = decode_column_strings artifact_path 3 in
      let value_count = Array.length s_raw in
      Printf.eprintf "[qof3-trace] load_handle: rows s=%d p=%d o=%d g=%d\n%!"
        value_count (Array.length p_raw) (Array.length o_raw) (Array.length g_raw);
      if Array.length p_raw <> value_count
         || Array.length o_raw <> value_count
         || Array.length g_raw <> value_count then begin
        Printf.eprintf "[qof3-FATAL] load_handle: column row counts disagree\n%!";
        failwith (Printf.sprintf
          "COTTAS on-disk: column row counts disagree: s=%d p=%d o=%d g=%d"
          value_count (Array.length p_raw) (Array.length o_raw) (Array.length g_raw))
      end;
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
    let key = subject_key s in
    Printf.eprintf "[qof3-trace] encode_subject key=%s\n%!" key;
    ensure_revmap h.s_revmap h.s_strs;
    Hashtbl.find_opt h.s_revmap key

  let encode_predicate (h : ondisk_handle) (p : RDF_Graph_Executable.wf_iri) : pint option =
    Printf.eprintf "[qof3-trace] encode_predicate iri=<%s>\n%!" p;
    ensure_revmap h.p_revmap h.p_strs;
    Hashtbl.find_opt h.p_revmap ("<" ^ p ^ ">")

  let encode_object (h : ondisk_handle) (o : RDF_Graph_Executable.rdf_term) : pint option =
    let key = object_key o in
    Printf.eprintf "[qof3-trace] encode_object key=%s\n%!" key;
    ensure_revmap h.o_revmap h.o_strs;
    Hashtbl.find_opt h.o_revmap key

  let encode_graph_name (h : ondisk_handle) (g : RDF_Graph_Executable.iri) : pint option =
    Printf.eprintf "[qof3-trace] encode_graph_name iri=<%s>\n%!" g;
    ensure_revmap h.g_revmap h.g_strs;
    Hashtbl.find_opt h.g_revmap ("<" ^ g ^ ">")

  let decode_subject (h : ondisk_handle) (id : pint) : RDF_Graph_Executable.subject =
    Printf.eprintf "[qof3-trace] decode_subject id=%d (s_strs.len=%d)\n%!" id (Array.length h.s_strs);
    match Hashtbl.find_opt h.s_decoded id with
    | Some s -> s
    | None ->
      if id < 0 || id >= Array.length h.s_strs then begin
        Printf.eprintf "[qof3-FATAL] decode_subject: id %d out of range (len=%d)\n%!" id (Array.length h.s_strs);
        failwith (Printf.sprintf "COTTAS on-disk: subject id %d out of range" id)
      end;
      let s = match parse_subject_str h.s_strs.(id) with
        | Some v -> v
        | None ->
          Printf.eprintf "[qof3-FATAL] decode_subject: invalid token %s\n%!" h.s_strs.(id);
          failwith (Printf.sprintf "COTTAS on-disk: invalid subject token %s" h.s_strs.(id)) in
      Hashtbl.add h.s_decoded id s;
      s

  let decode_predicate (h : ondisk_handle) (id : pint) : RDF_Graph_Executable.wf_iri =
    Printf.eprintf "[qof3-trace] decode_predicate id=%d (p_strs.len=%d)\n%!" id (Array.length h.p_strs);
    match Hashtbl.find_opt h.p_decoded id with
    | Some p -> p
    | None ->
      if id < 0 || id >= Array.length h.p_strs then begin
        Printf.eprintf "[qof3-FATAL] decode_predicate: id %d out of range (len=%d)\n%!" id (Array.length h.p_strs);
        failwith (Printf.sprintf "COTTAS on-disk: predicate id %d out of range" id)
      end;
      let p = match parse_iri_token h.p_strs.(id) with
        | Some iri -> iri
        | None ->
          Printf.eprintf "[qof3-FATAL] decode_predicate: invalid token %s\n%!" h.p_strs.(id);
          failwith (Printf.sprintf "COTTAS on-disk: invalid predicate token %s" h.p_strs.(id)) in
      Hashtbl.add h.p_decoded id p;
      p

  let decode_object (h : ondisk_handle) (id : pint) : RDF_Graph_Executable.rdf_term =
    Printf.eprintf "[qof3-trace] decode_object id=%d (o_strs.len=%d)\n%!" id (Array.length h.o_strs);
    match Hashtbl.find_opt h.o_decoded id with
    | Some o -> o
    | None ->
      if id < 0 || id >= Array.length h.o_strs then begin
        Printf.eprintf "[qof3-FATAL] decode_object: id %d out of range (len=%d)\n%!" id (Array.length h.o_strs);
        failwith (Printf.sprintf "COTTAS on-disk: object id %d out of range" id)
      end;
      let o = match parse_object_str h.o_strs.(id) with
        | Some v -> v
        | None ->
          Printf.eprintf "[qof3-FATAL] decode_object: invalid token %s\n%!" h.o_strs.(id);
          failwith (Printf.sprintf "COTTAS on-disk: invalid object token %s" h.o_strs.(id)) in
      Hashtbl.add h.o_decoded id o;
      o

  let decode_graph_name (h : ondisk_handle) (id : pint) : RDF_Graph_Executable.iri =
    Printf.eprintf "[qof3-trace] decode_graph_name id=%d (g_strs.len=%d)\n%!" id (Array.length h.g_strs);
    match Hashtbl.find_opt h.g_decoded id with
    | Some g -> g
    | None ->
      if id < 0 || id >= Array.length h.g_strs then begin
        Printf.eprintf "[qof3-FATAL] decode_graph_name: id %d out of range (len=%d)\n%!" id (Array.length h.g_strs);
        failwith (Printf.sprintf "COTTAS on-disk: graph id %d out of range" id)
      end;
      let g = match parse_iri_token h.g_strs.(id) with
        | Some iri -> iri
        | None ->
          Printf.eprintf "[qof3-FATAL] decode_graph_name: invalid token %s\n%!" h.g_strs.(id);
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
    let str_of_b = function None -> "_" | Some i -> string_of_int i in
    Printf.eprintf "[qof3-trace] search_rows bound={s=%s p=%s o=%s g=%s}\n%!"
      (str_of_b bound_s) (str_of_b bound_p) (str_of_b bound_o) (str_of_b bound_g);
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
    let str_of_b = function None -> "_" | Some i -> string_of_int i in
    Printf.eprintf "[qof3-trace] count_rows bound={s=%s p=%s o=%s g=%s}\n%!"
      (str_of_b bound_s) (str_of_b bound_p) (str_of_b bound_o) (str_of_b bound_g);
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
    Printf.eprintf "[qof3-trace] predicate_present pred=<%s>\n%!" pred;
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
    Printf.eprintf "[qof3-trace] named_graphs (g_strs.len=%d)\n%!" (Array.length h.g_strs);
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
  Printf.eprintf "[qof3-trace] cottas_ondisk_open path=%s\n%!" artifact_path;
  let h = Cottas_ondisk_runtime.load_handle artifact_path in
  Printf.eprintf "[qof3-trace] cottas_ondisk_open: handle ready\n%!";
  FStar_Pervasives_Native.Some {
    cods_artifact_path = artifact_path;
    cods_summary = h.Cottas_ondisk_runtime.summary;
    cods_handle = (Obj.magic h : cottas_ondisk_handle);
  }
'''

# Each remaining cottas_ondisk_* assume val gets the same Obj.magic
# unwrap → call → wrap pattern. We avoid forward references by
# defining a helper in the runtime and using Obj.magic at the boundary.
ondisk_replacements = {
    # Note: cottas_ondisk_close is NOT extracted by F* (Tot unit, no use site).
    # The OCaml runtime hashtable cleanup happens via Hashtbl gc.
    """let cottas_ondisk_summary (uu___ : cottas_ondisk_store) :
  cottas_artifact_summary FStar_Pervasives_Native.option=
  failwith "Not yet implemented: Parser.BallyhooCOTTAS.cottas_ondisk_summary"
""": """let cottas_ondisk_summary (ds : cottas_ondisk_store) :
  cottas_artifact_summary FStar_Pervasives_Native.option=
  Printf.eprintf "[qof3-trace] cottas_ondisk_summary invoked\n%!";
  let h : Cottas_ondisk_runtime.ondisk_handle = Obj.magic ds.cods_handle in
  h.summary
""",
    """let cottas_ondisk_encode_subject (uu___ : cottas_ondisk_store)
  (uu___1 : RDF_Graph_Executable.subject) :
  cottas_term_ref FStar_Pervasives_Native.option=
  failwith
    "Not yet implemented: Parser.BallyhooCOTTAS.cottas_ondisk_encode_subject"
""": """let cottas_ondisk_encode_subject (ds : cottas_ondisk_store)
  (s : RDF_Graph_Executable.subject) :
  cottas_term_ref FStar_Pervasives_Native.option=
  Printf.eprintf "[qof3-trace] cottas_ondisk_encode_subject invoked\n%!";
  let h : Cottas_ondisk_runtime.ondisk_handle = Obj.magic ds.cods_handle in
  match Cottas_ondisk_runtime.encode_subject h s with
  | None -> FStar_Pervasives_Native.None
  | Some i -> FStar_Pervasives_Native.Some (Z.of_int i)
""",
    """let cottas_ondisk_encode_predicate (uu___ : cottas_ondisk_store)
  (uu___1 : RDF_Graph_Executable.wf_iri) :
  cottas_term_ref FStar_Pervasives_Native.option=
  failwith
    "Not yet implemented: Parser.BallyhooCOTTAS.cottas_ondisk_encode_predicate"
""": """let cottas_ondisk_encode_predicate (ds : cottas_ondisk_store)
  (p : RDF_Graph_Executable.wf_iri) :
  cottas_term_ref FStar_Pervasives_Native.option=
  Printf.eprintf "[qof3-trace] cottas_ondisk_encode_predicate invoked\n%!";
  let h : Cottas_ondisk_runtime.ondisk_handle = Obj.magic ds.cods_handle in
  match Cottas_ondisk_runtime.encode_predicate h p with
  | None -> FStar_Pervasives_Native.None
  | Some i -> FStar_Pervasives_Native.Some (Z.of_int i)
""",
    """let cottas_ondisk_encode_object (uu___ : cottas_ondisk_store)
  (uu___1 : RDF_Graph_Executable.rdf_term) :
  cottas_term_ref FStar_Pervasives_Native.option=
  failwith
    "Not yet implemented: Parser.BallyhooCOTTAS.cottas_ondisk_encode_object"
""": """let cottas_ondisk_encode_object (ds : cottas_ondisk_store)
  (o : RDF_Graph_Executable.rdf_term) :
  cottas_term_ref FStar_Pervasives_Native.option=
  Printf.eprintf "[qof3-trace] cottas_ondisk_encode_object invoked\n%!";
  let h : Cottas_ondisk_runtime.ondisk_handle = Obj.magic ds.cods_handle in
  match Cottas_ondisk_runtime.encode_object h o with
  | None -> FStar_Pervasives_Native.None
  | Some i -> FStar_Pervasives_Native.Some (Z.of_int i)
""",
    """let cottas_ondisk_encode_graph_name (uu___ : cottas_ondisk_store)
  (uu___1 : RDF_Graph_Executable.iri) :
  cottas_graph_ref FStar_Pervasives_Native.option=
  failwith
    "Not yet implemented: Parser.BallyhooCOTTAS.cottas_ondisk_encode_graph_name"
""": """let cottas_ondisk_encode_graph_name (ds : cottas_ondisk_store)
  (g : RDF_Graph_Executable.iri) :
  cottas_graph_ref FStar_Pervasives_Native.option=
  Printf.eprintf "[qof3-trace] cottas_ondisk_encode_graph_name invoked\n%!";
  let h : Cottas_ondisk_runtime.ondisk_handle = Obj.magic ds.cods_handle in
  match Cottas_ondisk_runtime.encode_graph_name h g with
  | None -> FStar_Pervasives_Native.None
  | Some i -> FStar_Pervasives_Native.Some (Z.of_int i)
""",
    """let cottas_ondisk_decode_subject (uu___ : cottas_ondisk_store)
  (uu___1 : cottas_term_ref) : RDF_Graph_Executable.subject=
  failwith
    "Not yet implemented: Parser.BallyhooCOTTAS.cottas_ondisk_decode_subject"
""": """let cottas_ondisk_decode_subject (ds : cottas_ondisk_store)
  (id : cottas_term_ref) : RDF_Graph_Executable.subject=
  Printf.eprintf "[qof3-trace] cottas_ondisk_decode_subject invoked id=%s\n%!" (Z.to_string id);
  let h : Cottas_ondisk_runtime.ondisk_handle = Obj.magic ds.cods_handle in
  Cottas_ondisk_runtime.decode_subject h (Z.to_int id)
""",
    """let cottas_ondisk_decode_predicate (uu___ : cottas_ondisk_store)
  (uu___1 : cottas_term_ref) : RDF_Graph_Executable.wf_iri=
  failwith
    "Not yet implemented: Parser.BallyhooCOTTAS.cottas_ondisk_decode_predicate"
""": """let cottas_ondisk_decode_predicate (ds : cottas_ondisk_store)
  (id : cottas_term_ref) : RDF_Graph_Executable.wf_iri=
  Printf.eprintf "[qof3-trace] cottas_ondisk_decode_predicate invoked id=%s\n%!" (Z.to_string id);
  let h : Cottas_ondisk_runtime.ondisk_handle = Obj.magic ds.cods_handle in
  Cottas_ondisk_runtime.decode_predicate h (Z.to_int id)
""",
    """let cottas_ondisk_decode_object (uu___ : cottas_ondisk_store)
  (uu___1 : cottas_term_ref) : RDF_Graph_Executable.rdf_term=
  failwith
    "Not yet implemented: Parser.BallyhooCOTTAS.cottas_ondisk_decode_object"
""": """let cottas_ondisk_decode_object (ds : cottas_ondisk_store)
  (id : cottas_term_ref) : RDF_Graph_Executable.rdf_term=
  Printf.eprintf "[qof3-trace] cottas_ondisk_decode_object invoked id=%s\n%!" (Z.to_string id);
  let h : Cottas_ondisk_runtime.ondisk_handle = Obj.magic ds.cods_handle in
  Cottas_ondisk_runtime.decode_object h (Z.to_int id)
""",
    """let cottas_ondisk_decode_graph_name (uu___ : cottas_ondisk_store)
  (uu___1 : cottas_graph_ref) : RDF_Graph_Executable.iri=
  failwith
    "Not yet implemented: Parser.BallyhooCOTTAS.cottas_ondisk_decode_graph_name"
""": """let cottas_ondisk_decode_graph_name (ds : cottas_ondisk_store)
  (id : cottas_graph_ref) : RDF_Graph_Executable.iri=
  Printf.eprintf "[qof3-trace] cottas_ondisk_decode_graph_name invoked id=%s\n%!" (Z.to_string id);
  let h : Cottas_ondisk_runtime.ondisk_handle = Obj.magic ds.cods_handle in
  Cottas_ondisk_runtime.decode_graph_name h (Z.to_int id)
""",
    """let cottas_ondisk_search (uu___ : cottas_ondisk_store)
  (uu___1 : cottas_bound_qp) : cottas_qp_row Prims.list=
  failwith "Not yet implemented: Parser.BallyhooCOTTAS.cottas_ondisk_search"
""": """let cottas_ondisk_search (ds : cottas_ondisk_store)
  (bound : cottas_bound_qp) : cottas_qp_row Prims.list=
  Printf.eprintf "[qof3-trace] cottas_ondisk_search invoked\n%!";
  let h : Cottas_ondisk_runtime.ondisk_handle = Obj.magic ds.cods_handle in
  let rows = Cottas_ondisk_runtime.search_rows h bound in
  Printf.eprintf "[qof3-trace] cottas_ondisk_search returning %d row(s)\n%!" (List.length rows);
  rows
""",
    """let cottas_ondisk_estimate (uu___ : cottas_ondisk_store)
  (uu___1 : cottas_bound_qp) : Prims.nat=
  failwith
    "Not yet implemented: Parser.BallyhooCOTTAS.cottas_ondisk_estimate"
""": """let cottas_ondisk_estimate (ds : cottas_ondisk_store)
  (bound : cottas_bound_qp) : Prims.nat=
  Printf.eprintf "[qof3-trace] cottas_ondisk_estimate invoked\n%!";
  let h : Cottas_ondisk_runtime.ondisk_handle = Obj.magic ds.cods_handle in
  let n = Cottas_ondisk_runtime.count_rows h bound in
  Printf.eprintf "[qof3-trace] cottas_ondisk_estimate returning %d\n%!" n;
  Z.of_int n
""",
    """let cottas_ondisk_predicate_present (uu___ : cottas_ondisk_store)
  (uu___1 : RDF_Graph_Executable.wf_iri) : Prims.bool=
  failwith
    "Not yet implemented: Parser.BallyhooCOTTAS.cottas_ondisk_predicate_present"
""": """let cottas_ondisk_predicate_present (ds : cottas_ondisk_store)
  (pred : RDF_Graph_Executable.wf_iri) : Prims.bool=
  Printf.eprintf "[qof3-trace] cottas_ondisk_predicate_present invoked pred=<%s>\n%!" pred;
  let h : Cottas_ondisk_runtime.ondisk_handle = Obj.magic ds.cods_handle in
  Cottas_ondisk_runtime.predicate_present h pred
""",
    """let cottas_ondisk_named_graphs (uu___ : cottas_ondisk_store) :
  (RDF_Graph_Executable.iri * cottas_graph_ref) Prims.list=
  failwith
    "Not yet implemented: Parser.BallyhooCOTTAS.cottas_ondisk_named_graphs"
""": """let cottas_ondisk_named_graphs (ds : cottas_ondisk_store) :
  (RDF_Graph_Executable.iri * cottas_graph_ref) Prims.list=
  Printf.eprintf "[qof3-trace] cottas_ondisk_named_graphs invoked\n%!";
  let h : Cottas_ondisk_runtime.ondisk_handle = Obj.magic ds.cods_handle in
  Cottas_ondisk_runtime.named_graphs h
""",
}

if marker not in content:
    raise SystemExit("cottas_ondisk_open stub not found in extracted ML")

content = content.replace(marker, runtime, 1)

for old, new in ondisk_replacements.items():
    if old not in content:
        raise SystemExit(f"on-disk stub not found:\n{old}")
    content = content.replace(old, new, 1)

path.write_text(content)
PYEOF
