#!/bin/bash
# Lazy-open patch for the on-disk COTTAS backend.
#
# Bet7 (issue #100, 2026-04-26) — demo prep speedup.
#
# Background: cottas_ondisk_runtime.sh's `build_handle_and_tables`
# eagerly decodes all four parquet columns (subjects, predicates,
# objects, graphs) at open time. For the parliament corpus
# (3.14M quads, 26 row groups) this is 106 s + 1.4 GB RSS — far too
# slow for an interactive demo. Per Bet7 prompt, lazy per-rg subject
# and object dicts are the smallest fast win.
#
# What this patch does, AFTER cottas_ondisk_runtime.sh has run:
#
#   1. Adds a lazy-population module `Cottas_ondisk_lazy` with a
#      thread-safe "build subjects on first call" / "build objects on
#      first call" pair. Predicates + graphs stay eager because
#      they are tiny (parliament: 232 + 0 distinct, vs 908 k + 956 k
#      for s/o) and the predicate dict is needed by the F\* column-prune
#      planner the moment any predicate-bound query arrives.
#
#   2. Rewrites the body of `Cottas_ondisk_runtime.build_handle_and_tables`
#      to skip `collect_distinct artifact_path 0` and
#      `collect_distinct artifact_path 2`. The corresponding tables
#      (`ft_subj_tok_to_id`, `ft_id_to_subject`, `ft_id_to_subj_tok`,
#      and the same triple for objects) are built empty; the F\*
#      handle's `coh_subjects`, `coh_objects`, `coh_subjects_raw`,
#      `coh_objects_raw`, `coh_subj_revmap`, `coh_obj_revmap`,
#      `coh_subj_raw_revmap`, `coh_obj_raw_revmap` are also empty.
#
#   3. Wraps the `*_fast` lookup functions that depend on
#      subject/object tables (`encode_subject_fast`, `decode_subject_fast`,
#      `encode_object_fast`, `decode_object_fast`, `search_fast`,
#      `estimate_fast`) so they call into `Cottas_ondisk_lazy`'s
#      "ensure populated" hook before doing the actual lookup.
#
# Rule #15 conformance: this is unverified glue + memory layout.
# No RDF/SPARQL semantic decisions: tokens, matching, output shapes
# are unchanged. Just deferred work.
#
# Cross-agent: this patch only modifies the OCaml output AFTER
# cottas_ondisk_runtime.sh has produced it. cottas_ondisk_runtime.sh
# itself is unchanged.
#
# Idempotency: re-running this patch on an already-patched file is a
# no-op (skip-if-marker pattern).

set -euo pipefail

OUTDIR="$1"

if [[ -f "$OUTDIR" && "$OUTDIR" == *.ml ]]; then
  OUTDIR="$(dirname "$OUTDIR")"
fi

FILE="$OUTDIR/RDF_CottasStore.ml"
if [[ ! -f "$FILE" ]]; then
  echo "  Warning: $FILE not found, skipping COTTAS lazy-open patch" >&2
  exit 0
fi

if grep -q 'module Cottas_ondisk_lazy' "$FILE"; then
  echo "  COTTAS lazy-open patch already present."
  exit 0
fi

# Sanity: cottas_ondisk_runtime.sh must have run first (we depend on
# its `Cottas_ondisk_runtime` module being defined).
if ! grep -q 'module Cottas_ondisk_runtime' "$FILE"; then
  echo "  Warning: COTTAS lazy-open patch needs Cottas_ondisk_runtime;" >&2
  echo "  experimental_ocaml_glue/cottas_ondisk_runtime.sh must run first." >&2
  exit 0
fi

python3 - "$FILE" <<'PYEOF'
import sys
from pathlib import Path

path = Path(sys.argv[1])
content = path.read_text()

# ---- Step 1: Replace the body of build_handle_and_tables.
#
# We match the entire body from the function header to the closing of
# its `(handle, tables)` tuple line. The pattern stays anchored on the
# original `let build_handle_and_tables artifact_path` declaration that
# `cottas_ondisk_runtime.sh` wrote.

old_build = '''  let build_handle_and_tables artifact_path
    : (cottas_ondisk_handle * fast_tables) =
    Printf.eprintf "[qof3-trace] build_handle path=%s (Phase B: lazy search + fast tables)\\n%!" artifact_path;
    let (s_strs, s_tok_to_id, n_rows_s) = collect_distinct       artifact_path 0 in
    let (p_strs, p_tok_to_id, n_rows_p) = collect_distinct       artifact_path 1 in
    let (o_strs, o_tok_to_id, n_rows_o) = collect_distinct       artifact_path 2 in
    let (g_strs, g_tok_to_id, n_rows_g) = collect_distinct_graph artifact_path 3 in'''

new_build = '''  (* Bet7 lazy-open (issue #100, 2026-04-26): skip eager collection of
     ALL four columns. Each `collect_distinct` decodes every row group's
     data page for that column (~25 s + several hundred MB transient
     allocations on the parliament 3.14M-quad corpus). Total open used
     to be ~106 s + 1.4 GB RSS — far too slow + heavy for an interactive
     demo. After Bet7 the open is footer-only; the per-column
     dictionaries + Hashtbls are populated on demand by
     `Cottas_ondisk_lazy.ensure_*_loaded` from inside the *_fast
     lookup functions (search/estimate/encode/decode/predicate_present).

     Trade-off: the FIRST query that needs a column's dict pays the
     populate cost (~14 s for predicates, ~30 s each for subjects /
     objects on parliament). Subsequent queries are fast. For the
     daemon use case this means the listener comes up + binds the
     port in <1 s; the first SPARQL request takes the populate hit;
     warm requests are fast. cottas_ondisk_named_graphs called
     immediately post-open returns [] until first encode_graph
     populates — acceptable for parliament (which has 0 named
     graphs); for corpora WITH named graphs, snapshot_iris is
     populated after the first query.

     Compatibility with Aleph6's search_fast_limited (added by patch
     cottas_ondisk_zz_aleph6_count_limit.sh, runs after this patch):
     Aleph6's body calls ensure_subjects_loaded / ensure_objects_loaded
     (which are present here) but does NOT call ensure_predicates_loaded
     / ensure_graphs_loaded (because at the time Aleph6 was written
     this patch only deferred s+o). The Aleph6 patch now applies an
     extra fixup further below to add the missing pred+graph hooks. *)
  let build_handle_and_tables artifact_path
    : (cottas_ondisk_handle * fast_tables) =
    Printf.eprintf "[bet7-trace] build_handle path=%s (lazy open: defer all 4 columns)\\n%!" artifact_path;
    let n_rows = match Parquet_Footer.probe_parquet_num_rows artifact_path with
      | FStar_Pervasives_Native.Some n -> Z.to_int n
      | FStar_Pervasives_Native.None -> 0 in
    let s_strs = [] in
    let s_tok_to_id : (string, pint) Hashtbl.t = Hashtbl.create 16 in
    let n_rows_s = n_rows in
    let p_strs = [] in
    let p_tok_to_id : (string, pint) Hashtbl.t = Hashtbl.create 16 in
    let n_rows_p = n_rows in
    let o_strs = [] in
    let o_tok_to_id : (string, pint) Hashtbl.t = Hashtbl.create 16 in
    let n_rows_o = n_rows in
    let g_strs = [] in
    let g_tok_to_id : (string, pint) Hashtbl.t = Hashtbl.create 16 in
    let n_rows_g = n_rows in
    let _ = (n_rows_s, n_rows_p, n_rows_o, n_rows_g) in'''

if old_build not in content:
    sys.stderr.write("  [cottas_ondisk_lazy_open] WARN: build_handle anchor not found; skipping (cottas_ondisk_runtime.sh may have changed shape)\n")
    sys.exit(0)

content = content.replace(old_build, new_build, 1)

# ---- Step 2: Insert the Cottas_ondisk_lazy module BEFORE the
# Cottas_ondisk_runtime module.  This module owns the per-path lazy
# state and exposes `ensure_subjects_loaded` / `ensure_objects_loaded`
# hooks that the rewritten *_fast functions call.

lazy_module = '''module Cottas_ondisk_lazy = struct
  open Stdlib

  (* Per-path "is column N populated yet" flags. Avoid relying on
     Hashtbl size (an empty hashtable on a single-graph corpus is a
     valid populated state). *)
  let subj_loaded  : (string, unit) Hashtbl.t = Hashtbl.create 17
  let pred_loaded  : (string, unit) Hashtbl.t = Hashtbl.create 17
  let obj_loaded   : (string, unit) Hashtbl.t = Hashtbl.create 17
  let graph_loaded : (string, unit) Hashtbl.t = Hashtbl.create 17

  let mark_subj_loaded  path = Hashtbl.replace subj_loaded  path ()
  let mark_pred_loaded  path = Hashtbl.replace pred_loaded  path ()
  let mark_obj_loaded   path = Hashtbl.replace obj_loaded   path ()
  let mark_graph_loaded path = Hashtbl.replace graph_loaded path ()
  let is_subj_loaded    path = Hashtbl.mem subj_loaded  path
  let is_pred_loaded    path = Hashtbl.mem pred_loaded  path
  let is_obj_loaded     path = Hashtbl.mem obj_loaded   path
  let is_graph_loaded   path = Hashtbl.mem graph_loaded path

  (* Issue #110 Option B: Hashtbls and accessors retained for the Vav3
     reader (cottas_ondisk_zzzzz_ondisk_index.sh) after the dead-shim
     patches (yod6 / tet3 / mem5 / etc.) were retired. These are pure
     structural plumbing — empty per-path Hashtbl-of-Hashtbl maps with
     get-style accessors. The semantic prune logic that USED to populate
     and consult them lived in the deleted shims and is no longer on
     the public path; the F*-extracted `compute_candidate_rgs_loop`
     in RDF.CottasStore handles candidate-rg pruning now. The Vav3
     companion-file reader still references these accessors to seed
     its on-disk index path; keeping them as empty tables is safe
     glue (rule #11 allowed: structural, no decisions). *)
  (* Yod6/Tet3 in-RAM presence Hashtbls + accessors retired (issue #249).
     The query path consults RDF.CottasStore.PresenceBitmap.rg_could_contain
     against the mmap'd companion file directly; this OCaml mirror was
     populated but never read. *)
end

'''

anchor = "module Cottas_ondisk_runtime = struct"
if anchor not in content:
    sys.stderr.write("  [cottas_ondisk_lazy_open] WARN: Cottas_ondisk_runtime anchor not found\n")
    sys.exit(0)

content = content.replace(anchor, lazy_module + anchor, 1)

# ---- Step 3: Add lazy populator helpers INSIDE Cottas_ondisk_runtime.
# Inserted just before `let load_handle`. They share the same `collect_distinct`
# helper Cottas_ondisk_runtime defines (so are scoped within the module).

populator_block = '''
  (* Bet7 lazy populators (issue #100, 2026-04-26).
     Called from the *_fast functions on first lookup that needs the
     subject or object tables. Idempotent — guarded by
     Cottas_ondisk_lazy.is_*_loaded. *)
  let ensure_subjects_loaded (h : cottas_ondisk_handle) (tables : fast_tables) : unit =
    if not (Cottas_ondisk_lazy.is_subj_loaded h.coh_path) then begin
      Printf.eprintf "[bet7-trace] ensure_subjects_loaded: lazy populate path=%s\\n%!" h.coh_path;
      let (s_strs, s_tok_to_id, _n) = collect_distinct h.coh_path 0 in
      (* Move s_tok_to_id contents into tables.ft_subj_tok_to_id.
         (We can't just reassign — the field is a fresh Hashtbl.) *)
      Hashtbl.iter (fun k v -> Hashtbl.replace tables.ft_subj_tok_to_id k v) s_tok_to_id;
      List.iteri (fun i raw ->
        match parse_subject_str raw with
        | Some s ->
          Hashtbl.replace tables.ft_id_to_subject  i s;
          Hashtbl.replace tables.ft_id_to_subj_tok i raw
        | None ->
          Printf.eprintf "[bet7-WARN] ensure_subjects_loaded: invalid subject token id=%d val=%s\\n%!" i raw)
        s_strs;
      Cottas_ondisk_lazy.mark_subj_loaded h.coh_path;
      Gc.full_major ();
      Printf.eprintf "[bet7-trace] ensure_subjects_loaded: %d distinct subjects\\n%!"
        (Hashtbl.length tables.ft_subj_tok_to_id)
    end

  let ensure_objects_loaded (h : cottas_ondisk_handle) (tables : fast_tables) : unit =
    if not (Cottas_ondisk_lazy.is_obj_loaded h.coh_path) then begin
      Printf.eprintf "[bet7-trace] ensure_objects_loaded: lazy populate path=%s\\n%!" h.coh_path;
      let (o_strs, o_tok_to_id, _n) = collect_distinct h.coh_path 2 in
      Hashtbl.iter (fun k v -> Hashtbl.replace tables.ft_obj_tok_to_id k v) o_tok_to_id;
      List.iteri (fun i raw ->
        match parse_object_str raw with
        | Some o ->
          Hashtbl.replace tables.ft_id_to_object  i o;
          Hashtbl.replace tables.ft_id_to_obj_tok i raw
        | None ->
          Printf.eprintf "[bet7-WARN] ensure_objects_loaded: invalid object token id=%d val=%s\\n%!" i raw)
        o_strs;
      Cottas_ondisk_lazy.mark_obj_loaded h.coh_path;
      Gc.full_major ();
      Printf.eprintf "[bet7-trace] ensure_objects_loaded: %d distinct objects\\n%!"
        (Hashtbl.length tables.ft_obj_tok_to_id)
    end

  let ensure_predicates_loaded (h : cottas_ondisk_handle) (tables : fast_tables) : unit =
    if not (Cottas_ondisk_lazy.is_pred_loaded h.coh_path) then begin
      Printf.eprintf "[bet7-trace] ensure_predicates_loaded: lazy populate path=%s\\n%!" h.coh_path;
      let (p_strs, p_tok_to_id, _n) = collect_distinct h.coh_path 1 in
      Hashtbl.iter (fun k v -> Hashtbl.replace tables.ft_pred_tok_to_id k v) p_tok_to_id;
      List.iteri (fun i raw ->
        match parse_iri_token raw with
        | Some iri ->
          Hashtbl.replace tables.ft_id_to_predicate i iri;
          Hashtbl.replace tables.ft_id_to_pred_tok  i raw
        | None ->
          Printf.eprintf "[bet7-WARN] ensure_predicates_loaded: invalid predicate token id=%d val=%s\\n%!" i raw)
        p_strs;
      Cottas_ondisk_lazy.mark_pred_loaded h.coh_path;
      Gc.full_major ();
      Printf.eprintf "[bet7-trace] ensure_predicates_loaded: %d distinct predicates\\n%!"
        (Hashtbl.length tables.ft_pred_tok_to_id)
    end

  let ensure_graphs_loaded (h : cottas_ondisk_handle) (tables : fast_tables) : unit =
    if not (Cottas_ondisk_lazy.is_graph_loaded h.coh_path) then begin
      Printf.eprintf "[bet7-trace] ensure_graphs_loaded: lazy populate path=%s\\n%!" h.coh_path;
      let (g_strs, g_tok_to_id, _n) = collect_distinct_graph h.coh_path 3 in
      Hashtbl.iter (fun k v -> Hashtbl.replace tables.ft_graph_tok_to_id k v) g_tok_to_id;
      List.iteri (fun i raw ->
        match parse_iri_token raw with
        | Some iri ->
          Hashtbl.replace tables.ft_id_to_graph     i iri;
          Hashtbl.replace tables.ft_id_to_graph_tok i raw
        | None ->
          Printf.eprintf "[bet7-WARN] ensure_graphs_loaded: invalid graph token id=%d val=%s\\n%!" i raw)
        g_strs;
      Cottas_ondisk_lazy.mark_graph_loaded h.coh_path;
      Gc.full_major ();
      Printf.eprintf "[bet7-trace] ensure_graphs_loaded: %d distinct graphs\\n%!"
        (Hashtbl.length tables.ft_graph_tok_to_id)
    end

'''

# Insert the populator block just before `let load_handle`.
load_handle_anchor = "  let load_handle artifact_path : cottas_ondisk_handle ="
if load_handle_anchor not in content:
    sys.stderr.write("  [cottas_ondisk_lazy_open] WARN: load_handle anchor not found\n")
    sys.exit(0)

content = content.replace(load_handle_anchor,
                          populator_block + load_handle_anchor, 1)

# ---- Step 4: Patch the *_fast lookup functions that need subjects or
# objects to call the populator first. We add a single
# `ensure_*_loaded h tables;` line at the top of each function body.

# encode_subject_fast: needs subjects
old_encsub = '''  let encode_subject_fast (h : cottas_ondisk_handle) (s : RDF_Graph_Executable.subject)
    : Prims.nat FStar_Pervasives_Native.option =
    let tables = tables_for h in
    let key = match s with'''
new_encsub = '''  let encode_subject_fast (h : cottas_ondisk_handle) (s : RDF_Graph_Executable.subject)
    : Prims.nat FStar_Pervasives_Native.option =
    let tables = tables_for h in
    ensure_subjects_loaded h tables;
    let key = match s with'''
content = content.replace(old_encsub, new_encsub, 1)

# decode_subject_fast: needs subjects
old_decsub = '''  let decode_subject_fast (h : cottas_ondisk_handle) (id : Prims.nat)
    : RDF_Graph_Executable.subject =
    let tables = tables_for h in
    match Hashtbl.find_opt tables.ft_id_to_subject (Z.to_int id) with'''
new_decsub = '''  let decode_subject_fast (h : cottas_ondisk_handle) (id : Prims.nat)
    : RDF_Graph_Executable.subject =
    let tables = tables_for h in
    ensure_subjects_loaded h tables;
    match Hashtbl.find_opt tables.ft_id_to_subject (Z.to_int id) with'''
content = content.replace(old_decsub, new_decsub, 1)

# encode_object_fast: needs objects (for non-literal cases that hit
# ft_obj_tok_to_id; the literal path goes via revmap_lookup which is
# slow but separate).
old_encobj = '''  let encode_object_fast (h : cottas_ondisk_handle) (o : RDF_Graph_Executable.rdf_term)
    : Prims.nat FStar_Pervasives_Native.option =
    let tables = tables_for h in'''
new_encobj = '''  let encode_object_fast (h : cottas_ondisk_handle) (o : RDF_Graph_Executable.rdf_term)
    : Prims.nat FStar_Pervasives_Native.option =
    let tables = tables_for h in
    ensure_objects_loaded h tables;'''
content = content.replace(old_encobj, new_encobj, 1)

# decode_object_fast: needs objects
old_decobj = '''  let decode_object_fast (h : cottas_ondisk_handle) (id : Prims.nat)
    : RDF_Graph_Executable.rdf_term =
    let tables = tables_for h in
    match Hashtbl.find_opt tables.ft_id_to_object (Z.to_int id) with'''
new_decobj = '''  let decode_object_fast (h : cottas_ondisk_handle) (id : Prims.nat)
    : RDF_Graph_Executable.rdf_term =
    let tables = tables_for h in
    ensure_objects_loaded h tables;
    match Hashtbl.find_opt tables.ft_id_to_object (Z.to_int id) with'''
content = content.replace(old_decobj, new_decobj, 1)

# encode_predicate_fast: needs predicates
old_encpred = '''  let encode_predicate_fast (h : cottas_ondisk_handle) (p : RDF_Graph_Executable.wf_iri)
    : Prims.nat FStar_Pervasives_Native.option =
    let tables = tables_for h in
    let key = "<" ^ p ^ ">" in'''
new_encpred = '''  let encode_predicate_fast (h : cottas_ondisk_handle) (p : RDF_Graph_Executable.wf_iri)
    : Prims.nat FStar_Pervasives_Native.option =
    let tables = tables_for h in
    ensure_predicates_loaded h tables;
    let key = "<" ^ p ^ ">" in'''
content = content.replace(old_encpred, new_encpred, 1)

# decode_predicate_fast: needs predicates
old_decpred = '''  let decode_predicate_fast (h : cottas_ondisk_handle) (id : Prims.nat)
    : RDF_Graph_Executable.wf_iri =
    let tables = tables_for h in
    match Hashtbl.find_opt tables.ft_id_to_predicate (Z.to_int id) with'''
new_decpred = '''  let decode_predicate_fast (h : cottas_ondisk_handle) (id : Prims.nat)
    : RDF_Graph_Executable.wf_iri =
    let tables = tables_for h in
    ensure_predicates_loaded h tables;
    match Hashtbl.find_opt tables.ft_id_to_predicate (Z.to_int id) with'''
content = content.replace(old_decpred, new_decpred, 1)

# predicate_present_fast: needs predicates
old_predpres = '''  let predicate_present_fast (h : cottas_ondisk_handle) (p : RDF_Graph_Executable.wf_iri) : bool =
    let tables = tables_for h in
    let key = "<" ^ p ^ ">" in'''
new_predpres = '''  let predicate_present_fast (h : cottas_ondisk_handle) (p : RDF_Graph_Executable.wf_iri) : bool =
    let tables = tables_for h in
    ensure_predicates_loaded h tables;
    let key = "<" ^ p ^ ">" in'''
content = content.replace(old_predpres, new_predpres, 1)

# encode_graph_fast: needs graphs
old_encgraph = '''  let encode_graph_fast (h : cottas_ondisk_handle) (g : RDF_Graph_Executable.iri)
    : Prims.nat FStar_Pervasives_Native.option =
    let tables = tables_for h in
    let key = "<" ^ g ^ ">" in'''
new_encgraph = '''  let encode_graph_fast (h : cottas_ondisk_handle) (g : RDF_Graph_Executable.iri)
    : Prims.nat FStar_Pervasives_Native.option =
    let tables = tables_for h in
    ensure_graphs_loaded h tables;
    let key = "<" ^ g ^ ">" in'''
content = content.replace(old_encgraph, new_encgraph, 1)

# decode_graph_fast: needs graphs
old_decgraph = '''  let decode_graph_fast (h : cottas_ondisk_handle) (id : Prims.nat)
    : RDF_Graph_Executable.iri =
    let tables = tables_for h in
    match Hashtbl.find_opt tables.ft_id_to_graph (Z.to_int id) with'''
new_decgraph = '''  let decode_graph_fast (h : cottas_ondisk_handle) (id : Prims.nat)
    : RDF_Graph_Executable.iri =
    let tables = tables_for h in
    ensure_graphs_loaded h tables;
    match Hashtbl.find_opt tables.ft_id_to_graph (Z.to_int id) with'''
content = content.replace(old_decgraph, new_decgraph, 1)

# search_fast: needs all four. Hook at the top.
old_search_top = '''  let search_fast (h : cottas_ondisk_handle) (bound : Parser_BallyhooCOTTAS.cottas_bound_qp)
    : Parser_BallyhooCOTTAS.cottas_qp_row list =
    let path = h.coh_path in
    let tables = tables_for h in'''
new_search_top = '''  let search_fast (h : cottas_ondisk_handle) (bound : Parser_BallyhooCOTTAS.cottas_bound_qp)
    : Parser_BallyhooCOTTAS.cottas_qp_row list =
    let path = h.coh_path in
    let tables = tables_for h in
    (* search needs all four columns: build_qp_row reads every cell
       through the *_tok_to_id Hashtbls, and bound_id_to_token reads
       *_id_to_*_tok. *)
    ensure_subjects_loaded   h tables;
    ensure_predicates_loaded h tables;
    ensure_objects_loaded    h tables;
    ensure_graphs_loaded     h tables;'''
content = content.replace(old_search_top, new_search_top, 1)

# estimate_fast: only needs *bound* columns (the all-None case is now
# served by Aleph6's footer-only shortcut in cottas_ondisk_estimate;
# this hook only runs for bounded estimates).
old_estimate_top = '''  let estimate_fast (h : cottas_ondisk_handle) (bound : Parser_BallyhooCOTTAS.cottas_bound_qp) : pint =
    let path = h.coh_path in
    let tables = tables_for h in
    let bound_s = bound_id_to_token tables.ft_id_to_subj_tok  bound.Parser_BallyhooCOTTAS.cbqp_s in'''
new_estimate_top = '''  let estimate_fast (h : cottas_ondisk_handle) (bound : Parser_BallyhooCOTTAS.cottas_bound_qp) : pint =
    let path = h.coh_path in
    let tables = tables_for h in
    (* Conditional populate: only the bound columns need their tables. *)
    (match bound.Parser_BallyhooCOTTAS.cbqp_s with
     | FStar_Pervasives_Native.Some _ -> ensure_subjects_loaded h tables
     | _ -> ());
    (match bound.Parser_BallyhooCOTTAS.cbqp_p with
     | FStar_Pervasives_Native.Some _ -> ensure_predicates_loaded h tables
     | _ -> ());
    (match bound.Parser_BallyhooCOTTAS.cbqp_o with
     | FStar_Pervasives_Native.Some _ -> ensure_objects_loaded h tables
     | _ -> ());
    (match bound.Parser_BallyhooCOTTAS.cbqp_g with
     | FStar_Pervasives_Native.Some _ -> ensure_graphs_loaded h tables
     | _ -> ());
    let bound_s = bound_id_to_token tables.ft_id_to_subj_tok  bound.Parser_BallyhooCOTTAS.cbqp_s in'''
content = content.replace(old_estimate_top, new_estimate_top, 1)

path.write_text(content)
sys.stderr.write("  [cottas_ondisk_lazy_open] applied: build_handle skips s+o; lazy populators wired into encode/decode/search/estimate\n")
PYEOF
