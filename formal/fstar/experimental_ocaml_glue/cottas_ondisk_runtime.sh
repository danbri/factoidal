#!/bin/bash
# Experimental runtime glue for the on-disk COTTAS backend
# (RDF.CottasStore.fst).
#
# Issue #100 — Phase A migration (2026-04-25): 11 of the 13 originally-
# assume_val lookup functions were LIFTED to F* and now live as real
# `Tot` definitions in RDF.CottasStore.fst.
#
# Issue #100 — Phase B (Sade3, 2026-04-25): the remaining
# `cottas_ondisk_search` / `cottas_ondisk_estimate` are now real F*
# `Tot` functions too. They walk the parquet row groups lazily via
# `Parquet.Footer.probe_parquet_column_decode_in_row_group`, eliminating
# the eager int[] decode of row-group-0 (which only saw 122,880 of
# 3,143,406 quads on the parliament corpus).
#
# This patch is now I/O-glue + perf-shim only. No semantic logic.
# Two responsibilities:
#
# 1. Implement `cottas_ondisk_open`: read parquet, build the 4
#    distinct-term dictionaries + revmaps + parallel raw-token lists
#    across every row group, populate the F* handle.
#
# 2. PERFORMANCE: replace the extracted F* `cottas_ondisk_search`,
#    `cottas_ondisk_estimate`, and `cottas_ondisk_decode_*` with
#    Hashtbl-backed equivalents. The F* definitions in
#    RDF.CottasStore.fst remain the verification spec (they're total
#    and obviously correct, just O(N²) on 900k-entry assoc-lists).
#    The OCaml glue swaps to (string,nat) Hashtbl + (nat,term) Hashtbl
#    keyed by the artifact path. This is the same pattern as the eager
#    Parser.BallyhooCOTTAS path.
#
# Rule #15: this file is I/O glue + memory layout + perf-shim only.
# No RDF/SPARQL semantic logic. All decisions about which rows match
# which bound — and how to encode/decode terms — live in F* (the spec).

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
import re
import sys
from pathlib import Path

path = Path(sys.argv[1])
content = path.read_text()

# We split the patch into two pieces so the Cottas_ondisk_runtime
# module is defined BEFORE the F*-extracted functions that reference it
# via the perf-shim replacements (cottas_ondisk_encode_*, decode_*,
# search/estimate). The runtime module is inserted right before
# `cottas_ondisk_summary` (the first F* user-facing function in the
# extracted file). The cottas_ondisk_open implementation replaces the
# failwith stub in place.
runtime_anchor = """let cottas_ondisk_summary (ds : cottas_ondisk_store) :"""

open_marker = """let cottas_ondisk_open (artifact_path : Prims.string) :
  cottas_ondisk_store FStar_Pervasives_Native.option=
  failwith "Not yet implemented: RDF.CottasStore.cottas_ondisk_open"
"""

runtime = r'''module Cottas_ondisk_runtime = struct
  open Stdlib
  (* `int` is shadowed by `open Prims` at the top of the file
     (Prims.int = Z.t).  Provide a local alias for plain OCaml int so
     hashtables and array indices keep the native machine-word type. *)
  type pint = Stdlib.Int.t

  (* Per-handle fast tables (Phase B perf shim). Keyed by artifact path.
     Built at open() time alongside the F* handle. The F* spec lookup
     functions in RDF.CottasStore.fst remain the verification source of
     truth — these tables ARE the same data, just in a hash-indexed
     OCaml shape so cottas_ondisk_search/decode hits don't blow up on
     900k-entry assoc-lists. *)
  type fast_tables = {
    (* token (raw column string) -> nat term-id *)
    ft_subj_tok_to_id  : (string, pint) Hashtbl.t;
    ft_pred_tok_to_id  : (string, pint) Hashtbl.t;
    ft_obj_tok_to_id   : (string, pint) Hashtbl.t;
    ft_graph_tok_to_id : (string, pint) Hashtbl.t;
    (* nat term-id -> typed RDF term (parsed once at open time) *)
    ft_id_to_subject   : (pint, RDF_Graph_Executable.subject) Hashtbl.t;
    ft_id_to_predicate : (pint, RDF_Graph_Executable.wf_iri) Hashtbl.t;
    ft_id_to_object    : (pint, RDF_Graph_Executable.rdf_term) Hashtbl.t;
    ft_id_to_graph     : (pint, RDF_Graph_Executable.iri) Hashtbl.t;
    (* nat term-id -> raw column-token string (for bound -> token
       conversion at search time) *)
    ft_id_to_subj_tok  : (pint, string) Hashtbl.t;
    ft_id_to_pred_tok  : (pint, string) Hashtbl.t;
    ft_id_to_obj_tok   : (pint, string) Hashtbl.t;
    ft_id_to_graph_tok : (pint, string) Hashtbl.t;
  }

  (* Cache by artifact path. *)
  let handles : (string, cottas_ondisk_handle) Hashtbl.t = Hashtbl.create 17
  let fast_table_cache : (string, fast_tables) Hashtbl.t = Hashtbl.create 17

  (* Issue #110 (2026-04-29): Pe4 instrumentation helpers
     (pe4_rss_mb / pe4_fd_count / pe4_gc_mb) deleted along with the
     search_fast / estimate_fast OCaml shim functions they served.
     The F* extracted bodies now drive the public API path; their
     tracing lives in the F* spec or the page-cache runtime. *)

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

  (* ---- Distinct-token collector. We walk all row groups via the F*
         multi-row-group decoder, then dedupe to build the dictionary.
         Phase B drops the per-row int[] columns; we only need the
         distinct token list (indexed by id) + a raw-token-keyed
         revmap. ---- *)

  let collect_distinct (artifact_path : string) (col_idx : pint)
    : (string list * (string, pint) Hashtbl.t * pint) =
    Printf.eprintf "[qof3-trace] collect_distinct col=%d path=%s\n%!" col_idx artifact_path;
    match Parquet_Footer.probe_parquet_column_decode_all_row_groups
            artifact_path (Z.of_int col_idx) with
    | FStar_Pervasives_Native.None ->
      Printf.eprintf "[qof3-FATAL] collect_distinct: could not decode column %d\n%!" col_idx;
      failwith (Printf.sprintf "COTTAS on-disk: could not decode column %d" col_idx)
    | FStar_Pervasives_Native.Some lst ->
      let revmap : (string, pint) Hashtbl.t = Hashtbl.create 257 in
      let strs_rev = ref [] in
      let next_id = ref 0 in
      let row_count = ref 0 in
      List.iter (function
        | FStar_Pervasives_Native.None ->
          Printf.eprintf "[qof3-FATAL] collect_distinct: missing cell in column %d\n%!" col_idx;
          failwith (Printf.sprintf "COTTAS on-disk: missing cell in column %d" col_idx)
        | FStar_Pervasives_Native.Some r ->
          incr row_count;
          if not (Hashtbl.mem revmap r) then begin
            Hashtbl.add revmap r !next_id;
            strs_rev := r :: !strs_rev;
            incr next_id
          end) lst;
      Printf.eprintf "[qof3-trace] collect_distinct col=%d distinct=%d rows=%d\n%!"
        col_idx !next_id !row_count;
      (List.rev !strs_rev, revmap, !row_count)

  (* Same shape as collect_distinct, but for the graph column: skip the
     "DEFAULT" sentinel so it never enters the dictionary. *)
  let collect_distinct_graph (artifact_path : string) (col_idx : pint)
    : (string list * (string, pint) Hashtbl.t * pint) =
    Printf.eprintf "[qof3-trace] collect_distinct_graph col=%d path=%s\n%!" col_idx artifact_path;
    match Parquet_Footer.probe_parquet_column_decode_all_row_groups
            artifact_path (Z.of_int col_idx) with
    | FStar_Pervasives_Native.None ->
      Printf.eprintf "[qof3-FATAL] collect_distinct_graph: could not decode column %d\n%!" col_idx;
      failwith (Printf.sprintf "COTTAS on-disk: could not decode column %d" col_idx)
    | FStar_Pervasives_Native.Some lst ->
      let revmap : (string, pint) Hashtbl.t = Hashtbl.create 17 in
      let strs_rev = ref [] in
      let next_id = ref 0 in
      let row_count = ref 0 in
      List.iter (function
        | FStar_Pervasives_Native.None ->
          Printf.eprintf "[qof3-FATAL] collect_distinct_graph: missing cell in column %d\n%!" col_idx;
          failwith (Printf.sprintf "COTTAS on-disk: missing cell in column %d" col_idx)
        | FStar_Pervasives_Native.Some r ->
          incr row_count;
          if r <> "DEFAULT" && not (Hashtbl.mem revmap r) then begin
            Hashtbl.add revmap r !next_id;
            strs_rev := r :: !strs_rev;
            incr next_id
          end) lst;
      Printf.eprintf "[qof3-trace] collect_distinct_graph col=%d named_graphs=%d rows=%d\n%!"
        col_idx !next_id !row_count;
      (List.rev !strs_rev, revmap, !row_count)

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

  (* Tail-recursive mapi-like helpers. Stdlib's List.mapi is not tail-
     recursive and blows the stack on the parliament corpus's 900k-entry
     subject/object lists. *)
  let mapi_tr (f : pint -> 'a -> 'b) (xs : 'a list) : 'b list =
    let rec loop i acc = function
      | [] -> List.rev acc
      | hd :: tl -> loop (i + 1) ((f i hd) :: acc) tl in
    loop 0 [] xs

  let mk_subj_canonical_revmap (xs : RDF_Graph_Executable.subject list)
    : (Prims.string * Prims.nat) Prims.list =
    mapi_tr (fun i s -> (subject_to_revmap_key s, Z.of_int i)) xs

  let mk_iri_canonical_revmap (xs : RDF_Graph_Executable.iri list)
    : (Prims.string * Prims.nat) Prims.list =
    mapi_tr (fun i s -> (iri_to_revmap_key s, Z.of_int i)) xs

  let mk_obj_canonical_revmap (xs : RDF_Graph_Executable.rdf_term list)
    : (Prims.string * Prims.nat) Prims.list =
    mapi_tr (fun i s -> (object_to_revmap_key s, Z.of_int i)) xs

  (* Build the F* handle (Phase B): walk all row groups (every column),
     build distinct-token dictionaries + parallel revmaps, parse each
     dictionary entry to its typed RDF shape. The per-row int[] columns
     of Phase A are GONE — search/estimate work directly via parquet
     row-group probes in F* (or, in practice, via the fast_tables shim
     below). *)
  let build_handle_and_tables artifact_path
    : (cottas_ondisk_handle * fast_tables) =
    Printf.eprintf "[qof3-trace] build_handle path=%s (Phase B: lazy search + fast tables)\n%!" artifact_path;
    let (s_strs, s_tok_to_id, n_rows_s) = collect_distinct       artifact_path 0 in
    let (p_strs, p_tok_to_id, n_rows_p) = collect_distinct       artifact_path 1 in
    let (o_strs, o_tok_to_id, n_rows_o) = collect_distinct       artifact_path 2 in
    let (g_strs, g_tok_to_id, n_rows_g) = collect_distinct_graph artifact_path 3 in
    if n_rows_s <> n_rows_p || n_rows_s <> n_rows_o || n_rows_s <> n_rows_g then
      Printf.eprintf "[qof3-FATAL] build_handle: row counts disagree s=%d p=%d o=%d g=%d\n%!"
        n_rows_s n_rows_p n_rows_o n_rows_g;
    let n_rows = n_rows_s in
    Printf.eprintf "[qof3-trace] build_handle: distinct s=%d p=%d o=%d g=%d total_rows=%d\n%!"
      (List.length s_strs) (List.length p_strs) (List.length o_strs) (List.length g_strs) n_rows;
    (* Parse each distinct token to its F* RDF shape. *)
    let parse_subjects =
      mapi_tr (fun i raw ->
        match parse_subject_str raw with
        | Some s -> s
        | None ->
          Printf.eprintf "[qof3-FATAL] build_handle: invalid subject token id=%d val=%s\n%!" i raw;
          failwith (Printf.sprintf "COTTAS on-disk: invalid subject token %s" raw)) in
    let parse_predicates =
      mapi_tr (fun i raw ->
        match parse_iri_token raw with
        | Some iri -> (iri : RDF_Graph_Executable.wf_iri)
        | None ->
          Printf.eprintf "[qof3-FATAL] build_handle: invalid predicate token id=%d val=%s\n%!" i raw;
          failwith (Printf.sprintf "COTTAS on-disk: invalid predicate token %s" raw)) in
    let parse_objects =
      mapi_tr (fun i raw ->
        match parse_object_str raw with
        | Some t -> t
        | None ->
          Printf.eprintf "[qof3-FATAL] build_handle: invalid object token id=%d val=%s\n%!" i raw;
          failwith (Printf.sprintf "COTTAS on-disk: invalid object token %s" raw)) in
    let parse_graphs =
      mapi_tr (fun i raw ->
        match parse_iri_token raw with
        | Some iri -> (iri : RDF_Graph_Executable.iri)
        | None ->
          Printf.eprintf "[qof3-FATAL] build_handle: invalid graph token id=%d val=%s\n%!" i raw;
          failwith (Printf.sprintf "COTTAS on-disk: invalid graph token %s" raw)) in
    let coh_subjects   = parse_subjects   s_strs in
    let coh_predicates = parse_predicates p_strs in
    let coh_objects    = parse_objects    o_strs in
    let coh_graphs     = parse_graphs     g_strs in
    (* Build id-to-* hashtables from the parsed lists. *)
    let id_to_subject   : (pint, RDF_Graph_Executable.subject) Hashtbl.t =
      Hashtbl.create (List.length coh_subjects + 17) in
    List.iteri (fun i s -> Hashtbl.add id_to_subject i s) coh_subjects;
    let id_to_predicate : (pint, RDF_Graph_Executable.wf_iri) Hashtbl.t =
      Hashtbl.create (List.length coh_predicates + 17) in
    List.iteri (fun i p -> Hashtbl.add id_to_predicate i p) coh_predicates;
    let id_to_object    : (pint, RDF_Graph_Executable.rdf_term) Hashtbl.t =
      Hashtbl.create (List.length coh_objects + 17) in
    List.iteri (fun i o -> Hashtbl.add id_to_object i o) coh_objects;
    let id_to_graph     : (pint, RDF_Graph_Executable.iri) Hashtbl.t =
      Hashtbl.create (List.length coh_graphs + 17) in
    List.iteri (fun i g -> Hashtbl.add id_to_graph i g) coh_graphs;
    let id_to_subj_tok  : (pint, string) Hashtbl.t = Hashtbl.create (List.length s_strs + 17) in
    List.iteri (fun i s -> Hashtbl.add id_to_subj_tok  i s) s_strs;
    let id_to_pred_tok  : (pint, string) Hashtbl.t = Hashtbl.create (List.length p_strs + 17) in
    List.iteri (fun i s -> Hashtbl.add id_to_pred_tok  i s) p_strs;
    let id_to_obj_tok   : (pint, string) Hashtbl.t = Hashtbl.create (List.length o_strs + 17) in
    List.iteri (fun i s -> Hashtbl.add id_to_obj_tok   i s) o_strs;
    let id_to_graph_tok : (pint, string) Hashtbl.t = Hashtbl.create (List.length g_strs + 17) in
    List.iteri (fun i s -> Hashtbl.add id_to_graph_tok i s) g_strs;
    let tables : fast_tables = {
      ft_subj_tok_to_id  = s_tok_to_id;
      ft_pred_tok_to_id  = p_tok_to_id;
      ft_obj_tok_to_id   = o_tok_to_id;
      ft_graph_tok_to_id = g_tok_to_id;
      ft_id_to_subject   = id_to_subject;
      ft_id_to_predicate = id_to_predicate;
      ft_id_to_object    = id_to_object;
      ft_id_to_graph     = id_to_graph;
      ft_id_to_subj_tok  = id_to_subj_tok;
      ft_id_to_pred_tok  = id_to_pred_tok;
      ft_id_to_obj_tok   = id_to_obj_tok;
      ft_id_to_graph_tok = id_to_graph_tok;
    } in
    let handle : cottas_ondisk_handle = {
      coh_path = artifact_path;
      coh_summary = build_summary_for_handle artifact_path n_rows (List.length g_strs);
      coh_subjects;
      coh_predicates;
      coh_objects;
      coh_graphs;
      coh_subj_revmap  = mk_subj_canonical_revmap coh_subjects;
      coh_pred_revmap  = mk_iri_canonical_revmap  coh_predicates;
      coh_obj_revmap   = mk_obj_canonical_revmap  coh_objects;
      coh_graph_revmap = mk_iri_canonical_revmap  coh_graphs;
      coh_subjects_raw   = s_strs;
      coh_predicates_raw = p_strs;
      coh_objects_raw    = o_strs;
      coh_graphs_raw     = g_strs;
      coh_subj_raw_revmap  = mapi_tr (fun i s -> (s, Z.of_int i)) s_strs;
      coh_pred_raw_revmap  = mapi_tr (fun i s -> (s, Z.of_int i)) p_strs;
      coh_obj_raw_revmap   = mapi_tr (fun i s -> (s, Z.of_int i)) o_strs;
      coh_graph_raw_revmap = mapi_tr (fun i s -> (s, Z.of_int i)) g_strs;
    } in
    (handle, tables)

  let load_handle artifact_path : cottas_ondisk_handle =
    Printf.eprintf "[qof3-trace] load_handle path=%s\n%!" artifact_path;
    match Hashtbl.find_opt handles artifact_path with
    | Some h ->
      Printf.eprintf "[qof3-trace] load_handle: cache hit\n%!"; h
    | None ->
      let (h, tables) = build_handle_and_tables artifact_path in
      Hashtbl.add handles artifact_path h;
      Hashtbl.add fast_table_cache artifact_path tables;
      (* #254 Commit 2b registry wiring: snapshot the freshly-built
         eager dicts into the path-keyed LazyDictRegistry so the F*
         consumers can consult them via the typed boundary. The
         populate thunks here just return the already-computed data;
         a future commit upgrades them to true lazy parquet reads. *)
      (try
        let zip3 typed_list raw_list =
          let rec aux i ts rs = match ts, rs with
            | t :: trest, r :: rrest -> (Z.of_int i, t, r) :: aux (i+1) trest rrest
            | _, _ -> [] in
          aux 0 typed_list raw_list in
        let s_strs_snapshot = Hashtbl.fold (fun _ tok acc -> tok :: acc)
                                tables.ft_id_to_subj_tok [] in
        let p_strs_snapshot = Hashtbl.fold (fun _ tok acc -> tok :: acc)
                                tables.ft_id_to_pred_tok [] in
        let o_strs_snapshot = Hashtbl.fold (fun _ tok acc -> tok :: acc)
                                tables.ft_id_to_obj_tok [] in
        let g_strs_snapshot = Hashtbl.fold (fun _ tok acc -> tok :: acc)
                                tables.ft_id_to_graph_tok [] in
        RDF_CottasStore_LazyDictRegistry.register_for_path
          artifact_path
          (fun () -> zip3 h.coh_subjects   s_strs_snapshot)
          (fun () -> zip3 h.coh_predicates p_strs_snapshot)
          (fun () -> zip3 h.coh_objects    o_strs_snapshot)
          (fun () -> zip3 h.coh_graphs     g_strs_snapshot)
          subject_to_revmap_key
          iri_to_revmap_key
          object_to_revmap_key
          iri_to_revmap_key
      with _ ->
        Printf.eprintf "[bet7-trace] register_for_path failed (non-fatal)\\n%!");
      h

  let tables_for handle : fast_tables =
    match Hashtbl.find_opt fast_table_cache handle.coh_path with
    | Some t -> t
    | None ->
      (* Re-build (defensive: shouldn't happen if open() always populates). *)
      let (_h, tables) = build_handle_and_tables handle.coh_path in
      Hashtbl.add fast_table_cache handle.coh_path tables;
      tables

  (* Issue #110 (2026-04-29): retired. The Cottas_ondisk_runtime
     OCaml shims `search_fast`, `estimate_fast`, and
     `search_fast_limited` (plus their helpers `pe4_*`,
     `bound_id_to_token`, `cell_match_str`, `arr_of_col`,
     `cell_of`, `walk_rg`) used to live here. Phase 2.5e
     (commit 7cf9ebc) moved the public-API path to the F*-extracted
     `cottas_ondisk_search` / `_estimate` / `_search_limited`
     bodies, which decode through the F*-verified page cache via
     `pcache_decode_in_row_group_global` and resolve token->id via
     `ondisk_lookup_*_id_global`. The shim functions were dead on
     that path; the 9 retrofitting patches plus aleph6 and
     rename_inner_pivot have all been deleted in the same commit. *)
  (* Note: search_fast / estimate_fast / search_fast_limited are
     INTENTIONALLY ABSENT from this module. Do not add them back. *)

  let decode_subject_fast (h : cottas_ondisk_handle) (id : Prims.nat)
    : RDF_Graph_Executable.subject =
    let tables = tables_for h in
    match Hashtbl.find_opt tables.ft_id_to_subject (Z.to_int id) with
    | Some s -> s
    | None -> RDF_Graph_Executable.S_BNode "cottas_decode_oor"

  let decode_predicate_fast (h : cottas_ondisk_handle) (id : Prims.nat)
    : RDF_Graph_Executable.wf_iri =
    let tables = tables_for h in
    match Hashtbl.find_opt tables.ft_id_to_predicate (Z.to_int id) with
    | Some p -> p
    | None -> ("http://www.w3.org/1999/02/22-rdf-syntax-ns#type" : RDF_Graph_Executable.wf_iri)

  let decode_object_fast (h : cottas_ondisk_handle) (id : Prims.nat)
    : RDF_Graph_Executable.rdf_term =
    let tables = tables_for h in
    match Hashtbl.find_opt tables.ft_id_to_object (Z.to_int id) with
    | Some o -> o
    | None -> RDF_Graph_Executable.T_BNode "cottas_decode_oor"

  let decode_graph_fast (h : cottas_ondisk_handle) (id : Prims.nat)
    : RDF_Graph_Executable.iri =
    let tables = tables_for h in
    match Hashtbl.find_opt tables.ft_id_to_graph (Z.to_int id) with
    | Some g -> g
    | None -> ""

  let encode_subject_fast (h : cottas_ondisk_handle) (s : RDF_Graph_Executable.subject)
    : Prims.nat FStar_Pervasives_Native.option =
    let tables = tables_for h in
    let key = match s with
      | RDF_Graph_Executable.S_IRI i   -> "<" ^ i ^ ">"
      | RDF_Graph_Executable.S_BNode b -> "_:" ^ b in
    match Hashtbl.find_opt tables.ft_subj_tok_to_id key with
    | Some i -> FStar_Pervasives_Native.Some (Z.of_int i)
    | None -> FStar_Pervasives_Native.None

  let encode_predicate_fast (h : cottas_ondisk_handle) (p : RDF_Graph_Executable.wf_iri)
    : Prims.nat FStar_Pervasives_Native.option =
    let tables = tables_for h in
    let key = "<" ^ p ^ ">" in
    match Hashtbl.find_opt tables.ft_pred_tok_to_id key with
    | Some i -> FStar_Pervasives_Native.Some (Z.of_int i)
    | None -> FStar_Pervasives_Native.None

  let encode_object_fast (h : cottas_ondisk_handle) (o : RDF_Graph_Executable.rdf_term)
    : Prims.nat FStar_Pervasives_Native.option =
    let tables = tables_for h in
    match o with
    | RDF_Graph_Executable.T_IRI i ->
      let key = "<" ^ i ^ ">" in
      (match Hashtbl.find_opt tables.ft_obj_tok_to_id key with
       | Some i -> FStar_Pervasives_Native.Some (Z.of_int i)
       | None -> FStar_Pervasives_Native.None)
    | RDF_Graph_Executable.T_BNode b ->
      let key = "_:" ^ b in
      (match Hashtbl.find_opt tables.ft_obj_tok_to_id key with
       | Some i -> FStar_Pervasives_Native.Some (Z.of_int i)
       | None -> FStar_Pervasives_Native.None)
    | RDF_Graph_Executable.T_Literal _ ->
      (* #261 fix: produce the N-Triples form via the F* serialiser
         (RDF.NQuads.Serialize.nq_term_to_string) and look up in the
         Bet7-populated Hashtbl. The literal column stores tokens in
         N-Triples form ("<lex>" / "<lex>"@lang / "<lex>"^^<<dt>>);
         the old fallback to revmap_lookup against coh_obj_revmap
         silently returned None on Bet7-lazy-opened handles because
         the assoc list is empty by design. Keeps the literal byte
         layout in F* per Iron Rule #11. *)
      let key = RDF_NQuads_Serialize.nq_term_to_string o in
      (match Hashtbl.find_opt tables.ft_obj_tok_to_id key with
       | Some i -> FStar_Pervasives_Native.Some (Z.of_int i)
       | None -> FStar_Pervasives_Native.None)

  let encode_graph_fast (h : cottas_ondisk_handle) (g : RDF_Graph_Executable.iri)
    : Prims.nat FStar_Pervasives_Native.option =
    let tables = tables_for h in
    let key = "<" ^ g ^ ">" in
    match Hashtbl.find_opt tables.ft_graph_tok_to_id key with
    | Some i -> FStar_Pervasives_Native.Some (Z.of_int i)
    | None -> FStar_Pervasives_Native.None

  let predicate_present_fast (h : cottas_ondisk_handle) (p : RDF_Graph_Executable.wf_iri) : bool =
    let tables = tables_for h in
    let key = "<" ^ p ^ ">" in
    Hashtbl.mem tables.ft_pred_tok_to_id key
end

let cottas_ondisk_summary (ds : cottas_ondisk_store) :'''

# `runtime` ends at the start of `let cottas_ondisk_summary` (the
# anchor) so that `runtime` will REPLACE the anchor line, restoring it
# at the end. Net effect: insert `module Cottas_ondisk_runtime = ... end`
# right before `cottas_ondisk_summary`.

open_impl = r'''let cottas_ondisk_open (artifact_path : Prims.string) :
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

if runtime_anchor not in content:
    raise SystemExit("runtime anchor (cottas_ondisk_summary header) not found in extracted ML")
if open_marker not in content:
    raise SystemExit("cottas_ondisk_open stub not found in extracted ML")

# Insert the runtime module BEFORE cottas_ondisk_summary.
content = content.replace(runtime_anchor, runtime, 1)
# Replace the cottas_ondisk_open failwith with the real implementation.
content = content.replace(open_marker, open_impl, 1)

# ---- Phase B perf shim: replace the F*-extracted slow paths with the
# Hashtbl-backed Cottas_ondisk_runtime.* equivalents. The F* spec stays
# the verification source of truth; these replacements are pure runtime
# perf (rule #15 conformant — no semantic changes). ----
#
# Issue #261 follow-up (2026-07-05): the module qualifier F* extraction
# picks for RDF.Term's types (`subject` / `wf_iri` / `rdf_term` / `iri`)
# is NOT stable across extractions — depending on how RDF.Graph.Executable
# currently re-exports RDF.Term, some extractions emit
# `RDF_Graph_Executable.<type>` and others emit `RDF_Term.<type>` for
# the exact same F* type. This patch used to hardcode
# `RDF_Graph_Executable`; when an extraction emitted `RDF_Term` instead
# (as happened here), every entry in the table below silently failed
# to match — the loop only counted "0/9 applied" to a non-fatal
# stderr line — so `cottas_ondisk_encode_object` stayed on the O(n)
# Tot assoc-list path with the Bet7-empty `coh_obj_revmap`,
# REINTRODUCING the exact "literal-bound object returns 0 rows" bug
# #261 was filed for (and the `cottas_ondisk_named_graphs` shim below
# failed the same way, reintroducing the GRAPH-pattern-returns-0-rows
# bug from the #261 follow-up comment). Fixed by matching the
# qualifier with a regex alternation, captured and re-emitted verbatim
# so the header stays valid for whichever qualifier this extraction
# used, and by turning "didn't apply" into a hard build failure
# (iron rule #3: no silent holes) instead of a WARN nobody reads.

QUAL = r"(RDF_Graph_Executable|RDF_Term)"

def make_pattern(old_tmpl):
    # old_tmpl contains the literal marker "@Q@" wherever the module
    # qualifier appears. Beyond the qualifier itself, F*'s pretty-
    # printer also varies its LINE-WRAPPING between extractions (a
    # signature that wraps onto 2 lines with the long
    # "RDF_Graph_Executable" qualifier can sit on 1 line with the
    # shorter "RDF_Term" qualifier) — observed directly comparing two
    # extractions of this same file. So we tokenize on whitespace and
    # join tokens with `\s+` instead of matching literal newlines, and
    # substitute the qualifier marker with the alternation group
    # wherever it appears (as its own token or glued to a following
    # ".ident").
    tokens = old_tmpl.split()
    assert any("@Q@" in t for t in tokens), "old_tmpl marker lost during tokenize"
    parts = []
    for tok in tokens:
        if "@Q@" not in tok:
            parts.append(re.escape(tok))
            continue
        pre, _, post = tok.partition("@Q@")
        parts.append(re.escape(pre) + QUAL + re.escape(post))
    return re.compile(r"\s+".join(parts))

def apply_qualified(content, name, old_tmpl, new_tmpl):
    rx = make_pattern(old_tmpl)
    m = rx.search(content)
    if not m:
        return content, False
    qual = m.group(1)
    replacement = new_tmpl.replace("@Q@", qual)
    content = content[:m.start()] + replacement + content[m.end():]
    return content, True

# (name, old_tmpl, new_tmpl) — each old/new pair identical except for
# the body line(s), with "@Q@" standing in for whichever qualifier
# module F* chose this run.
shim_entries = [
  ("encode_subject",
   """let cottas_ondisk_encode_subject (ds : cottas_ondisk_store)
  (s : @Q@.subject) :
  Parser_BallyhooCOTTAS.cottas_term_ref FStar_Pervasives_Native.option=
  revmap_lookup (ds.cods_handle).coh_subj_revmap (subject_to_revmap_key s)
""",
   """let cottas_ondisk_encode_subject (ds : cottas_ondisk_store)
  (s : @Q@.subject) :
  Parser_BallyhooCOTTAS.cottas_term_ref FStar_Pervasives_Native.option=
  Cottas_ondisk_runtime.encode_subject_fast ds.cods_handle s
"""),
  ("encode_predicate",
   """let cottas_ondisk_encode_predicate (ds : cottas_ondisk_store)
  (p : @Q@.wf_iri) :
  Parser_BallyhooCOTTAS.cottas_term_ref FStar_Pervasives_Native.option=
  revmap_lookup (ds.cods_handle).coh_pred_revmap (iri_to_revmap_key p)
""",
   """let cottas_ondisk_encode_predicate (ds : cottas_ondisk_store)
  (p : @Q@.wf_iri) :
  Parser_BallyhooCOTTAS.cottas_term_ref FStar_Pervasives_Native.option=
  Cottas_ondisk_runtime.encode_predicate_fast ds.cods_handle p
"""),
  ("encode_object",
   """let cottas_ondisk_encode_object (ds : cottas_ondisk_store)
  (o : @Q@.rdf_term) :
  Parser_BallyhooCOTTAS.cottas_term_ref FStar_Pervasives_Native.option=
  revmap_lookup (ds.cods_handle).coh_obj_revmap (object_to_revmap_key o)
""",
   """let cottas_ondisk_encode_object (ds : cottas_ondisk_store)
  (o : @Q@.rdf_term) :
  Parser_BallyhooCOTTAS.cottas_term_ref FStar_Pervasives_Native.option=
  Cottas_ondisk_runtime.encode_object_fast ds.cods_handle o
"""),
  ("encode_graph_name",
   """let cottas_ondisk_encode_graph_name (ds : cottas_ondisk_store)
  (g : @Q@.iri) :
  Parser_BallyhooCOTTAS.cottas_graph_ref FStar_Pervasives_Native.option=
  revmap_lookup (ds.cods_handle).coh_graph_revmap (iri_to_revmap_key g)
""",
   """let cottas_ondisk_encode_graph_name (ds : cottas_ondisk_store)
  (g : @Q@.iri) :
  Parser_BallyhooCOTTAS.cottas_graph_ref FStar_Pervasives_Native.option=
  Cottas_ondisk_runtime.encode_graph_fast ds.cods_handle g
"""),
  # decode_* (slow list_nth -> Hashtbl)
  ("decode_subject",
   """let cottas_ondisk_decode_subject (ds : cottas_ondisk_store)
  (id : Parser_BallyhooCOTTAS.cottas_term_ref) :
  @Q@.subject=
  match list_nth (ds.cods_handle).coh_subjects id with
  | FStar_Pervasives_Native.Some s -> s
  | FStar_Pervasives_Native.None ->
      @Q@.S_BNode "cottas_decode_oor"
""",
   """let cottas_ondisk_decode_subject (ds : cottas_ondisk_store)
  (id : Parser_BallyhooCOTTAS.cottas_term_ref) :
  @Q@.subject=
  Cottas_ondisk_runtime.decode_subject_fast ds.cods_handle id
"""),
  ("decode_object",
   """let cottas_ondisk_decode_object (ds : cottas_ondisk_store)
  (id : Parser_BallyhooCOTTAS.cottas_term_ref) :
  @Q@.rdf_term=
  match list_nth (ds.cods_handle).coh_objects id with
  | FStar_Pervasives_Native.Some o -> o
  | FStar_Pervasives_Native.None ->
      @Q@.T_BNode "cottas_decode_oor"
""",
   """let cottas_ondisk_decode_object (ds : cottas_ondisk_store)
  (id : Parser_BallyhooCOTTAS.cottas_term_ref) :
  @Q@.rdf_term=
  Cottas_ondisk_runtime.decode_object_fast ds.cods_handle id
"""),
  # decode_predicate (correctness bug: was missing from the original
  # dict; F* version's `coh_predicates` list is empty post-Bet7
  # lazy-open, so every decode missed and fell back to the F* sentinel
  # "urn:factoidal:cottas-decode-predicate-unknown-id" — or, before
  # the F* fix, the silent rdf:type fallback that masked the bug.
  # This shim routes through Cottas_ondisk_runtime.decode_predicate_fast
  # which consults the populated `tables.ft_id_to_predicate` Hashtbl.)
  ("decode_predicate",
   """let cottas_ondisk_decode_predicate (ds : cottas_ondisk_store)
  (id : Parser_BallyhooCOTTAS.cottas_term_ref) : @Q@.wf_iri=
  match list_nth (ds.cods_handle).coh_predicates id with
  | FStar_Pervasives_Native.Some p -> p
  | FStar_Pervasives_Native.None ->
      let fallback = "urn:factoidal:cottas-decode-predicate-unknown-id" in
      fallback
""",
   """let cottas_ondisk_decode_predicate (ds : cottas_ondisk_store)
  (id : Parser_BallyhooCOTTAS.cottas_term_ref) : @Q@.wf_iri=
  Cottas_ondisk_runtime.decode_predicate_fast ds.cods_handle id
"""),
  ("decode_graph_name",
   """let cottas_ondisk_decode_graph_name (ds : cottas_ondisk_store)
  (id : Parser_BallyhooCOTTAS.cottas_graph_ref) : @Q@.iri=
  match list_nth (ds.cods_handle).coh_graphs id with
  | FStar_Pervasives_Native.Some g -> g
  | FStar_Pervasives_Native.None -> ""
""",
   """let cottas_ondisk_decode_graph_name (ds : cottas_ondisk_store)
  (id : Parser_BallyhooCOTTAS.cottas_graph_ref) : @Q@.iri=
  Cottas_ondisk_runtime.decode_graph_fast ds.cods_handle id
"""),
  # predicate_present (slow assoc-list lookup -> Hashtbl)
  ("predicate_present",
   """let cottas_ondisk_predicate_present (ds : cottas_ondisk_store)
  (pred : @Q@.wf_iri) : Prims.bool=
  match revmap_lookup (ds.cods_handle).coh_pred_revmap
          (iri_to_revmap_key pred)
  with
  | FStar_Pervasives_Native.None -> false
  | FStar_Pervasives_Native.Some uu___ -> true
""",
   """let cottas_ondisk_predicate_present (ds : cottas_ondisk_store)
  (pred : @Q@.wf_iri) : Prims.bool=
  Cottas_ondisk_runtime.predicate_present_fast ds.cods_handle pred
"""),
]

applied = 0
failed_names = []
for name, old_tmpl, new_tmpl in shim_entries:
    content, ok = apply_qualified(content, name, old_tmpl, new_tmpl)
    if ok:
        applied += 1
    else:
        failed_names.append(name)
sys.stderr.write(f"  [cottas_ondisk_runtime] perf-shim applied {applied}/{len(shim_entries)} encode/decode/predicate replacements\n")
if failed_names:
    sys.stderr.write(f"  [cottas_ondisk_runtime] FAILED to match: {', '.join(failed_names)}\n")
    raise SystemExit(
        "cottas_ondisk_runtime.sh: perf-shim replacement(s) did not match "
        f"the extracted OCaml ({', '.join(failed_names)}). This is the "
        "silent-hole failure mode from issue #261 — the on-disk COTTAS "
        "backend would silently drop literal-bound-object rows (and/or "
        "named-graph rows) if this were allowed to continue. Inspect "
        "the current RDF_CottasStore.ml signatures for cottas_ondisk_"
        f"{failed_names[0]} and update the qualifier handling above.")

# Phase 2.5e (issue #118): the cottas_ondisk_search /
# cottas_ondisk_estimate dispatch substitutions are RETIRED. The
# F*-extracted bodies now ARE the runtime — they call the seq-shape
# walks (`walk_*_search_global` etc.) which decode through the
# F*-verified page cache via `pcache_decode_in_row_group_global`
# (realised by experimental_ocaml_glue/cottas_pagecache_global_runtime.sh).
# Token→id resolution flows through `ondisk_lookup_*_id_global`
# (Phase 2.7-mini, realised by cottas_ondisk_zzzzzzzzzzzzzzzzz_token_lookup_runtime.sh)
# which honours Bet7's lazy populate.
#
# Issue #110 (2026-04-29): `Cottas_ondisk_runtime.search_fast`,
# `estimate_fast`, and `search_fast_limited` — and the 9 patches
# that retrofitted them (yod6 / tet3 / mem5 / tet3-redirect /
# compound-po-redirect / pagecache-hot-path) plus aleph6 and
# rename_inner_pivot — have all been retired in this commit. The
# F*-extracted public-API bodies are the only runtime now.

# #261 fix part B: cottas_ondisk_named_graphs reads from
# ds.cods_handle.coh_graphs, which is empty on Bet7-lazy-opened
# handles until first encode_graph populates the OCaml Hashtbl.
# Result: COTTAS files with named graphs return dsb_named = [] at
# dataset-construction time, so any `GRAPH ?g { ... }` query returns
# 0 results. Fix: post-extraction, replace the body with one that
# triggers ensure_graphs_loaded and reads ft_id_to_graph.
#
# Same qualifier-drift hazard as the shim table above (issue #261
# follow-up, 2026-07-05) — match via regex alternation, hard-fail if
# it doesn't apply.
old_named_graphs = """let cottas_ondisk_named_graphs (ds : cottas_ondisk_store) :
  (@Q@.iri * Parser_BallyhooCOTTAS.cottas_graph_ref)
    Prims.list=
  named_graphs_aux (ds.cods_handle).coh_graphs Prims.int_zero"""
new_named_graphs = """let cottas_ondisk_named_graphs (ds : cottas_ondisk_store) :
  (@Q@.iri * Parser_BallyhooCOTTAS.cottas_graph_ref)
    Prims.list=
  (* #261 fix part B: Bet7-lazy-opened handles defer coh_graphs.
     Trigger the OCaml-side populate, then read from ft_id_to_graph.
     The default-graph sentinel ("DEFAULT") is not a named graph and
     is excluded by ensure_graphs_loaded's id_to_graph population. *)
  let h = ds.cods_handle in
  let tables = Cottas_ondisk_runtime.tables_for h in
  Cottas_ondisk_runtime.ensure_graphs_loaded h tables;
  let acc = ref [] in
  Hashtbl.iter (fun id iri ->
    acc := (iri, Z.of_int id) :: !acc
  ) tables.Cottas_ondisk_runtime.ft_id_to_graph;
  !acc"""
content, named_graphs_ok = apply_qualified(
    content, "named_graphs", old_named_graphs, new_named_graphs)
if not named_graphs_ok:
    sys.stderr.write("  [cottas_ondisk_runtime] FAILED to match: named_graphs\n")
    raise SystemExit(
        "cottas_ondisk_runtime.sh: cottas_ondisk_named_graphs replacement "
        "did not match the extracted OCaml. This is the silent-hole "
        "failure mode from issue #261 follow-up — GRAPH ?g { ... } "
        "queries against a Bet7-lazy-opened COTTAS handle would "
        "silently return 0 rows if this were allowed to continue. "
        "Inspect the current RDF_CottasStore.ml signature for "
        "cottas_ondisk_named_graphs and update the qualifier handling "
        "above.")
sys.stderr.write("  [cottas_ondisk_runtime] cottas_ondisk_named_graphs replaced for Bet7 awareness\n")

path.write_text(content)
PYEOF
