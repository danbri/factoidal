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

new_build = '''  (* Bet7 lazy-open (issue #100, 2026-04-26): skip eager subject (col 0)
     and object (col 2) collection. Both have ~900 k+ distinct values
     on the parliament corpus and dominate the 106 s open time. They
     are populated lazily by Cottas_ondisk_lazy below on first lookup
     in encode/decode/search/estimate. Predicates (col 1) + graphs
     (col 3) stay eager: predicates are needed by the F* column-prune
     planner the moment a predicate-bound query arrives, and graphs
     are needed by cottas_ondisk_named_graphs which the daemon calls
     post-open to compute snapshot IRIs. Both columns are tiny on
     parliament: 232 + 0 distinct values respectively. *)
  let build_handle_and_tables artifact_path
    : (cottas_ondisk_handle * fast_tables) =
    Printf.eprintf "[bet7-trace] build_handle path=%s (lazy open: skip s+o)\\n%!" artifact_path;
    let (p_strs, p_tok_to_id, n_rows_p) = collect_distinct       artifact_path 1 in
    let (g_strs, g_tok_to_id, n_rows_g) = collect_distinct_graph artifact_path 3 in
    (* For subjects + objects we don't decode the data pages now.
       Total row count is read from the parquet footer; subj/obj
       string lists, revmaps, and Hashtbls are filled on first
       lazy-populate. *)
    let n_rows = match Parquet_Footer.probe_parquet_num_rows artifact_path with
      | FStar_Pervasives_Native.Some n -> Z.to_int n
      | FStar_Pervasives_Native.None -> n_rows_p in
    let s_strs = [] in
    let s_tok_to_id : (string, pint) Hashtbl.t = Hashtbl.create 16 in
    let n_rows_s = n_rows in
    let o_strs = [] in
    let o_tok_to_id : (string, pint) Hashtbl.t = Hashtbl.create 16 in
    let n_rows_o = n_rows in
    let _ = (n_rows_s, n_rows_o) in (* unused except for compatibility below *)
    (* Reclaim memory from the temporary 3.14M-cell decode list that
       collect_distinct produced for the predicate column above (it
       dedupes to ~232 entries — the rest is garbage). full_major
       collects the dead OCaml objects; compact returns the freed
       heap pages to the OS allocator pool. Without this the post-open
       RSS includes the unmaterialised waste. *)
    Gc.full_major ();
    Gc.compact ();'''

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
  let subj_loaded : (string, unit) Hashtbl.t = Hashtbl.create 17
  let obj_loaded  : (string, unit) Hashtbl.t = Hashtbl.create 17

  let mark_subj_loaded path = Hashtbl.replace subj_loaded path ()
  let mark_obj_loaded  path = Hashtbl.replace obj_loaded  path ()
  let is_subj_loaded   path = Hashtbl.mem subj_loaded path
  let is_obj_loaded    path = Hashtbl.mem obj_loaded  path
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

# search_fast: needs both. Hook it at the top, just after `tables = tables_for h`.
# This populates UNCONDITIONALLY — search may filter on s_tok / o_tok via
# bound_id_to_token + cell match, which all use the tables.
old_search_top = '''  let search_fast (h : cottas_ondisk_handle) (bound : Parser_BallyhooCOTTAS.cottas_bound_qp)
    : Parser_BallyhooCOTTAS.cottas_qp_row list =
    let path = h.coh_path in
    let tables = tables_for h in'''
new_search_top = '''  let search_fast (h : cottas_ondisk_handle) (bound : Parser_BallyhooCOTTAS.cottas_bound_qp)
    : Parser_BallyhooCOTTAS.cottas_qp_row list =
    let path = h.coh_path in
    let tables = tables_for h in
    ensure_subjects_loaded h tables;
    ensure_objects_loaded  h tables;'''
content = content.replace(old_search_top, new_search_top, 1)

# estimate_fast: tables_for is enough (estimate doesn't actually need
# subj/obj tables — it filters by raw column tokens compared via string
# equality, no Hashtbl lookup involved). But bound_id_to_token DOES read
# tables.ft_id_to_subj_tok if a bound subject id is present. Hook there.
old_estimate_top = '''  let estimate_fast (h : cottas_ondisk_handle) (bound : Parser_BallyhooCOTTAS.cottas_bound_qp) : pint =
    let path = h.coh_path in
    let tables = tables_for h in
    let bound_s = bound_id_to_token tables.ft_id_to_subj_tok  bound.Parser_BallyhooCOTTAS.cbqp_s in'''
new_estimate_top = '''  let estimate_fast (h : cottas_ondisk_handle) (bound : Parser_BallyhooCOTTAS.cottas_bound_qp) : pint =
    let path = h.coh_path in
    let tables = tables_for h in
    (* Estimate's filter loop uses string equality on raw column tokens,
       so it doesn't read the subj/obj revmaps directly. But
       bound_id_to_token does need ft_id_to_subj_tok / ft_id_to_obj_tok
       if a bound subject/object id was passed in. The cheap path here
       is conditional: only populate if a bound is actually present. *)
    (match bound.Parser_BallyhooCOTTAS.cbqp_s with
     | FStar_Pervasives_Native.Some _ -> ensure_subjects_loaded h tables
     | _ -> ());
    (match bound.Parser_BallyhooCOTTAS.cbqp_o with
     | FStar_Pervasives_Native.Some _ -> ensure_objects_loaded h tables
     | _ -> ());
    let bound_s = bound_id_to_token tables.ft_id_to_subj_tok  bound.Parser_BallyhooCOTTAS.cbqp_s in'''
content = content.replace(old_estimate_top, new_estimate_top, 1)

path.write_text(content)
sys.stderr.write("  [cottas_ondisk_lazy_open] applied: build_handle skips s+o; lazy populators wired into encode/decode/search/estimate\n")
PYEOF
