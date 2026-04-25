#!/bin/bash
# Experimental runtime glue for the on-disk COTTAS backend
# (RDF.CottasStore.fst's three remaining `assume val`s:
#   `cottas_ondisk_open`, `cottas_ondisk_search`, `cottas_ondisk_estimate`).
#
# Issue #100 — Phase A migration (2026-04-25): 11 of the 13 originally-
# assume_val lookup functions have been LIFTED to F* and now live as
# real `Tot` definitions in RDF.CottasStore.fst. They extract to real
# OCaml directly. This patch only handles the remaining I/O glue.
#
# All format semantics live in F* through Parquet.Footer + RDF.CottasStore.
# This glue's job:
#   - cottas_ondisk_open  : I/O — read the Parquet file, decode 4 columns,
#     parse each distinct token to its F*-shaped subject/wf_iri/rdf_term/iri,
#     build per-column reverse maps using the F*-extracted key functions,
#     and stuff the raw int-id columns inside the F*-side handle's
#     `coh_columns` (a Phase B/C-replaceable opaque blob).
#   - cottas_ondisk_search/_estimate : tight `for`-loop walks of the
#     int-id arrays comparing to the bound term-ids; the resulting
#     cottas_qp_row records are ordinary F*-typed values.
#
# Rule #15: this file is I/O glue + memory layout only. No semantic
# RDF/SPARQL logic. Encoding/decoding/predicate-presence/named-graph
# walk are F*-defined in RDF.CottasStore.

set -euo pipefail

OUTDIR="$1"

if [[ -f "$OUTDIR" && "$OUTDIR" == *.ml ]]; then
  OUTDIR="$(dirname "$OUTDIR")"
fi

FILE="$OUTDIR/RDF_CottasStore.ml"
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

# Anchor: the `cottas_ondisk_open` failwith stub (extracted from
# RDF.CottasStore.fst's `assume val cottas_ondisk_open`). Replace with
# the runtime + the implementations of the 3 remaining assume vals.
marker = """let cottas_ondisk_open (artifact_path : Prims.string) :
  cottas_ondisk_store FStar_Pervasives_Native.option=
  failwith "Not yet implemented: RDF.CottasStore.cottas_ondisk_open"
"""

runtime = r'''
module Cottas_ondisk_runtime = struct
  open Stdlib
  (* `int` is shadowed by `open Prims` at the top of the file
     (Prims.int = Z.t).  Provide a local alias for plain OCaml int so
     hashtables and array indices keep the native machine-word type. *)
  type pint = Stdlib.Int.t

  (* Mutable column-arrays bundle. Owned by the OCaml runtime; the F*
     handle's `coh_columns : columns_handle` field is `unit` after
     extraction (assume type → unit), so we Obj.magic this record into
     and out of that slot. Phase B replaces this with a typed F*-side
     iterator. *)
  type columns_bundle = {
    s_ids : pint array;
    p_ids : pint array;
    o_ids : pint array;
    g_ids : pint array;
    s_count : pint;
    p_count : pint;
    o_count : pint;
    g_count : pint;
  }

  (* Cache by artifact path, so re-opening the same file reuses the
     decoded columns. The cached value is the FULL F* handle, not just
     the columns — re-opens are cheap. *)
  let handles : (string, cottas_ondisk_handle) Hashtbl.t = Hashtbl.create 17

  (* ---- Token parsing helpers. Convert an N-Triples-style raw column
         token (like "<iri>" / "_:b" / "\"lit\"^^<dt>" / "\"lit\"@en")
         to the matching F* RDF type. ---- *)

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

  let parse_literal_token s : RDF_Graph_Executable.wf_literal option =
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

  let parse_subject_str s : RDF_Graph_Executable.subject option =
    match parse_iri_token s with
    | Some iri -> Some (RDF_Graph_Executable.S_IRI iri)
    | None ->
      if String.length s >= 2 && String.sub s 0 2 = "_:" then
        Some (RDF_Graph_Executable.S_BNode (String.sub s 2 (String.length s - 2)))
      else
        None

  let parse_object_str s : RDF_Graph_Executable.rdf_term option =
    match parse_iri_token s with
    | Some iri -> Some (RDF_Graph_Executable.T_IRI iri)
    | None ->
      if String.length s >= 2 && String.sub s 0 2 = "_:" then
        Some (RDF_Graph_Executable.T_BNode (String.sub s 2 (String.length s - 2)))
      else match parse_literal_token s with
        | Some lit -> Some (RDF_Graph_Executable.T_Literal lit)
        | None -> None

  (* Build distinct-string id→token + per-row id arrays from a raw
     row-of-strings array. id is an int index into the distinct-string
     list. *)
  let build_column (raw : string array) : (pint array * string list * pint) =
    let revmap : (string, pint) Hashtbl.t = Hashtbl.create (Array.length raw / 2 + 17) in
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
    (* Reverse the cons-list so position N == id N. *)
    (ids, List.rev !strs_list, !next_id)

  let build_graph_column (raw : string array) : (pint array * string list * pint) =
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
    (ids, List.rev !strs_list, !next_id)

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

  let build_summary_for_handle artifact_path total_rows graph_count
    : Parser_BallyhooCOTTAS.cottas_artifact_summary FStar_Pervasives_Native.option =
    let row_groups =
      match Parquet_Footer.probe_parquet_row_group_count artifact_path with
      | FStar_Pervasives_Native.None -> Z.one
      | FStar_Pervasives_Native.Some n -> n in
    let mk_col kind : Parser_BallyhooCOTTAS.cottas_column_summary =
      {
        ccs_kind = kind;
        ccs_num_values = Z.of_int total_rows;
        ccs_null_count = Z.zero;
        ccs_encoding = Parser_BallyhooCOTTAS.CE_Delta;
      } in
    FStar_Pervasives_Native.Some {
      Parser_BallyhooCOTTAS.cas_path = artifact_path;
      cas_num_quads = Z.of_int total_rows;
      cas_num_row_groups = row_groups;
      cas_dictionary =
        FStar_Pervasives_Native.Some {
          Parser_BallyhooCOTTAS.cds_num_terms = Z.of_int total_rows;
          cds_num_graphs = Z.of_int graph_count;
          cds_bytes_strings = Z.zero;
        };
      cas_row_groups = [{
        Parser_BallyhooCOTTAS.crgs_index = Z.zero;
        crgs_num_rows = Z.of_int total_rows;
        crgs_columns = [
          mk_col Parser_BallyhooCOTTAS.CC_Subject;
          mk_col Parser_BallyhooCOTTAS.CC_Predicate;
          mk_col Parser_BallyhooCOTTAS.CC_Object;
          mk_col Parser_BallyhooCOTTAS.CC_Graph
        ];
      }];
    }

  (* Build the F* handle: parse all distinct tokens to typed RDF terms,
     populate the four revmaps using the F*-extracted canonical key
     functions, and embed the int-id columns inside the opaque
     `coh_columns` slot via Obj.magic. *)
  let build_handle artifact_path : cottas_ondisk_handle =
    Printf.eprintf "[qof3-trace] build_handle path=%s\n%!" artifact_path;
    let s_raw = decode_column_strings artifact_path 0 in
    let p_raw = decode_column_strings artifact_path 1 in
    let o_raw = decode_column_strings artifact_path 2 in
    let g_raw = decode_column_strings artifact_path 3 in
    let value_count = Array.length s_raw in
    Printf.eprintf "[qof3-trace] build_handle: rows s=%d p=%d o=%d g=%d\n%!"
      value_count (Array.length p_raw) (Array.length o_raw) (Array.length g_raw);
    if Array.length p_raw <> value_count
       || Array.length o_raw <> value_count
       || Array.length g_raw <> value_count then begin
      Printf.eprintf "[qof3-FATAL] build_handle: column row counts disagree\n%!";
      failwith (Printf.sprintf
        "COTTAS on-disk: column row counts disagree: s=%d p=%d o=%d g=%d"
        value_count (Array.length p_raw) (Array.length o_raw) (Array.length g_raw))
    end;
    let (s_ids, s_strs, s_count) = build_column s_raw in
    let (p_ids, p_strs, p_count) = build_column p_raw in
    let (o_ids, o_strs, o_count) = build_column o_raw in
    let (g_ids, g_strs, g_count) = build_graph_column g_raw in
    Printf.eprintf "[qof3-trace] build_handle: distinct counts s=%d p=%d o=%d g=%d\n%!"
      s_count p_count o_count g_count;
    (* Parse each distinct token to its F* RDF shape. The id IS the
       index, so the resulting list aligns position-with-id. *)
    let parse_subjects =
      List.mapi (fun i raw ->
        match parse_subject_str raw with
        | Some s -> s
        | None ->
          Printf.eprintf "[qof3-FATAL] build_handle: invalid subject token id=%d val=%s\n%!" i raw;
          failwith (Printf.sprintf "COTTAS on-disk: invalid subject token %s" raw)) in
    let parse_predicates =
      List.mapi (fun i raw ->
        match parse_iri_token raw with
        | Some iri -> (iri : RDF_Graph_Executable.wf_iri)
        | None ->
          Printf.eprintf "[qof3-FATAL] build_handle: invalid predicate token id=%d val=%s\n%!" i raw;
          failwith (Printf.sprintf "COTTAS on-disk: invalid predicate token %s" raw)) in
    let parse_objects =
      List.mapi (fun i raw ->
        match parse_object_str raw with
        | Some t -> t
        | None ->
          Printf.eprintf "[qof3-FATAL] build_handle: invalid object token id=%d val=%s\n%!" i raw;
          failwith (Printf.sprintf "COTTAS on-disk: invalid object token %s" raw)) in
    let parse_graphs =
      List.mapi (fun i raw ->
        match parse_iri_token raw with
        | Some iri -> (iri : RDF_Graph_Executable.iri)
        | None ->
          Printf.eprintf "[qof3-FATAL] build_handle: invalid graph token id=%d val=%s\n%!" i raw;
          failwith (Printf.sprintf "COTTAS on-disk: invalid graph token %s" raw)) in
    let coh_subjects   = parse_subjects   s_strs in
    let coh_predicates = parse_predicates p_strs in
    let coh_objects    = parse_objects    o_strs in
    let coh_graphs     = parse_graphs     g_strs in
    (* Build revmaps: assoc-lists keyed by F*-extracted canonical key,
       value = nat term-id (Z.t). The F*-side encode functions use the
       same key functions, so lookups will match by construction. *)
    let mk_subj_revmap =
      List.mapi (fun i s ->
        (subject_to_revmap_key s, Z.of_int i)) coh_subjects in
    let mk_pred_revmap =
      List.mapi (fun i p ->
        (iri_to_revmap_key p, Z.of_int i)) coh_predicates in
    let mk_obj_revmap =
      List.mapi (fun i o ->
        (object_to_revmap_key o, Z.of_int i)) coh_objects in
    let mk_graph_revmap =
      List.mapi (fun i g ->
        (iri_to_revmap_key g, Z.of_int i)) coh_graphs in
    let columns : columns_bundle = {
      s_ids; p_ids; o_ids; g_ids;
      s_count; p_count; o_count; g_count;
    } in
    let _ = columns.s_count in
    {
      coh_path = artifact_path;
      coh_summary = build_summary_for_handle artifact_path value_count g_count;
      coh_subjects;
      coh_predicates;
      coh_objects;
      coh_graphs;
      coh_subj_revmap = mk_subj_revmap;
      coh_pred_revmap = mk_pred_revmap;
      coh_obj_revmap = mk_obj_revmap;
      coh_graph_revmap = mk_graph_revmap;
      coh_columns = (Obj.magic columns : columns_handle);
    }

  let load_handle artifact_path : cottas_ondisk_handle =
    Printf.eprintf "[qof3-trace] load_handle path=%s\n%!" artifact_path;
    match Hashtbl.find_opt handles artifact_path with
    | Some h ->
      Printf.eprintf "[qof3-trace] load_handle: cache hit\n%!"; h
    | None ->
      let h = build_handle artifact_path in
      Hashtbl.add handles artifact_path h;
      h

  let columns_of (h : cottas_ondisk_handle) : columns_bundle =
    (Obj.magic h.coh_columns : columns_bundle)

  (* Search: walk per-row id arrays comparing against bound term-ids.
     Pure integer comparison — no parsed-term materialisation per row.
     Returns the matched rows as cottas_qp_row records (the term-ids).
     Caller uses cottas_ondisk_row_to_quad to decode terms on-demand. *)
  let search_rows (h : cottas_ondisk_handle) (bound : Parser_BallyhooCOTTAS.cottas_bound_qp)
    : Parser_BallyhooCOTTAS.cottas_qp_row list =
    let cols = columns_of h in
    let opt_to_int = function
      | FStar_Pervasives_Native.None -> None
      | FStar_Pervasives_Native.Some z -> Some (Z.to_int z) in
    let bound_s = opt_to_int bound.Parser_BallyhooCOTTAS.cbqp_s in
    let bound_p = opt_to_int bound.Parser_BallyhooCOTTAS.cbqp_p in
    let bound_o = opt_to_int bound.Parser_BallyhooCOTTAS.cbqp_o in
    let bound_g = opt_to_int bound.Parser_BallyhooCOTTAS.cbqp_g in
    let str_of_b = function None -> "_" | Some i -> string_of_int i in
    Printf.eprintf "[qof3-trace] search_rows bound={s=%s p=%s o=%s g=%s}\n%!"
      (str_of_b bound_s) (str_of_b bound_p) (str_of_b bound_o) (str_of_b bound_g);
    let n = Array.length cols.s_ids in
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
      let sid = cols.s_ids.(i) in
      let pid = cols.p_ids.(i) in
      let oid = cols.o_ids.(i) in
      let gid = cols.g_ids.(i) in
      if int_match bound_s sid &&
         int_match bound_p pid &&
         int_match bound_o oid &&
         graph_match bound_g gid
      then
        acc := {
          Parser_BallyhooCOTTAS.cqpr_s = FStar_Pervasives_Native.Some (Z.of_int sid);
          cqpr_p = FStar_Pervasives_Native.Some (Z.of_int pid);
          cqpr_o = FStar_Pervasives_Native.Some (Z.of_int oid);
          cqpr_g = if gid < 0 then FStar_Pervasives_Native.None
                   else FStar_Pervasives_Native.Some (Z.of_int gid);
        } :: !acc
    done;
    !acc

  let count_rows (h : cottas_ondisk_handle) (bound : Parser_BallyhooCOTTAS.cottas_bound_qp) : pint =
    let cols = columns_of h in
    let opt_to_int = function
      | FStar_Pervasives_Native.None -> None
      | FStar_Pervasives_Native.Some z -> Some (Z.to_int z) in
    let bound_s = opt_to_int bound.Parser_BallyhooCOTTAS.cbqp_s in
    let bound_p = opt_to_int bound.Parser_BallyhooCOTTAS.cbqp_p in
    let bound_o = opt_to_int bound.Parser_BallyhooCOTTAS.cbqp_o in
    let bound_g = opt_to_int bound.Parser_BallyhooCOTTAS.cbqp_g in
    let str_of_b = function None -> "_" | Some i -> string_of_int i in
    Printf.eprintf "[qof3-trace] count_rows bound={s=%s p=%s o=%s g=%s}\n%!"
      (str_of_b bound_s) (str_of_b bound_p) (str_of_b bound_o) (str_of_b bound_g);
    let n = Array.length cols.s_ids in
    let count = ref 0 in
    let int_match expected actual =
      match expected with None -> true | Some e -> e = actual in
    let graph_match expected actual_id =
      match expected with
      | None -> true
      | Some e -> if actual_id < 0 then false else e = actual_id in
    for i = 0 to n - 1 do
      if int_match bound_s cols.s_ids.(i) &&
         int_match bound_p cols.p_ids.(i) &&
         int_match bound_o cols.o_ids.(i) &&
         graph_match bound_g cols.g_ids.(i)
      then incr count
    done;
    !count
end

let cottas_ondisk_open (artifact_path : Prims.string) :
  cottas_ondisk_store FStar_Pervasives_Native.option=
  Printf.eprintf "[qof3-trace] cottas_ondisk_open path=%s\n%!" artifact_path;
  let h = Cottas_ondisk_runtime.load_handle artifact_path in
  Printf.eprintf "[qof3-trace] cottas_ondisk_open: handle ready\n%!";
  FStar_Pervasives_Native.Some {
    cods_artifact_path = artifact_path;
    cods_summary = h.coh_summary;
    cods_handle = h;
  }
'''

# Two remaining failwith stubs -> real implementations.
ondisk_replacements = {
    """let cottas_ondisk_search (uu___ : cottas_ondisk_store)
  (uu___1 : Parser_BallyhooCOTTAS.cottas_bound_qp) :
  Parser_BallyhooCOTTAS.cottas_qp_row Prims.list=
  failwith "Not yet implemented: RDF.CottasStore.cottas_ondisk_search"
""": """let cottas_ondisk_search (ds : cottas_ondisk_store)
  (bound : Parser_BallyhooCOTTAS.cottas_bound_qp) :
  Parser_BallyhooCOTTAS.cottas_qp_row Prims.list=
  Printf.eprintf "[qof3-trace] cottas_ondisk_search invoked\n%!";
  let rows = Cottas_ondisk_runtime.search_rows ds.cods_handle bound in
  Printf.eprintf "[qof3-trace] cottas_ondisk_search returning %d row(s)\n%!" (List.length rows);
  rows
""",
    """let cottas_ondisk_estimate (uu___ : cottas_ondisk_store)
  (uu___1 : Parser_BallyhooCOTTAS.cottas_bound_qp) : Prims.nat=
  failwith "Not yet implemented: RDF.CottasStore.cottas_ondisk_estimate"
""": """let cottas_ondisk_estimate (ds : cottas_ondisk_store)
  (bound : Parser_BallyhooCOTTAS.cottas_bound_qp) : Prims.nat=
  Printf.eprintf "[qof3-trace] cottas_ondisk_estimate invoked\n%!";
  let n = Cottas_ondisk_runtime.count_rows ds.cods_handle bound in
  Printf.eprintf "[qof3-trace] cottas_ondisk_estimate returning %d\n%!" n;
  Z.of_int n
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
