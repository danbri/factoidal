#!/bin/bash
# Route the hot-path column decodes (search_fast_inner /
# search_fast_limited_inner walk loops) through the F*-resident
# RDF.CottasStore.PageCache module.
#
# Why: Mim2 (issue #100 Phase C) added an F*-verified page cache that
# memoises decoded `list (option string)` per (rg, col). It's used in
# the column-prune-planner code paths (see RDF_CottasStore.ml line ~2406)
# but the SEARCH hot paths bypass it — they call Parquet_Footer.
# probe_parquet_column_decode_in_row_group directly.
#
# Result: every repeat query that walks the same rg pays the full
# DLBA decode cost (~6s for parliament's 122k-row rgs). Q01 runs at
# ~6s on EVERY invocation, not just the first.
#
# The fix: a thin OCaml dispatch shim (`Cottas_pagecache_hot.cached_decode`)
# that holds a mutable cache ref, calls the F*-pure
# `pcache_decode_in_row_group`, and re-binds the ref to the returned
# fresh cache. The cache LOGIC and the LRU bookkeeping live in F*.
# This module only threads state across pure F* calls — rule #11(c)
# thin dispatch shim. No new semantic logic.
#
# Net F*-vs-OCaml shift: a previously-OCaml-only decision (when to
# memoise a decoded column) gains F* as the source of truth via
# RDF_CottasStore_PageCache.pcache_decode_in_row_group. The F* module
# already had the soundness shape (LRU eviction with monotone clock);
# this patch just makes the hot path actually USE it.
#
# Sort order: cottas_ondisk_zzzzzzzzzzzzzzzz_* (16 z's) — runs after
# all existing patches.

set -euo pipefail

OUTDIR="$1"

if [[ -f "$OUTDIR" && "$OUTDIR" == *.ml ]]; then
  ML="$OUTDIR"
else
  ML="$OUTDIR/RDF_CottasStore.ml"
fi

if [[ ! -f "$ML" ]]; then
  echo "  [pagecache-hot-path] WARN: $ML not found; skipping."
  exit 0
fi

if grep -q '__PAGECACHE_HOT_PATH_APPLIED__' "$ML"; then
  echo "  [pagecache-hot-path] already applied; skipping."
  exit 0
fi

# Sanity check: page-cache helper module must exist (extracted from
# RDF.CottasStore.PageCache.fst).
if ! grep -q 'RDF_CottasStore_PageCache' "$ML"; then
  echo "  [pagecache-hot-path] FATAL: RDF_CottasStore_PageCache not visible in $ML; aborting."
  exit 1
fi

python3 - "$ML" <<'PYEOF'
import sys, pathlib

path = pathlib.Path(sys.argv[1])
content = path.read_text()

# ----------------------------------------------------------------------
# 1. Insert the helper module just BEFORE the Cottas_ondisk_runtime
#    module declaration. The helper must be visible to the hot-path
#    rewrites later in the file.
# ----------------------------------------------------------------------

helper_module = '''(* Cottas_pagecache_hot: thread the F*-resident page cache through the
   search/estimate hot-path column decodes. The cache LOGIC (LRU
   eviction, monotone clock, key match) lives in
   RDF_CottasStore_PageCache (Mim2's module). This OCaml shim only
   maintains a mutable ref holding the current cache record and re-binds
   it after each pure F* call.

   __PAGECACHE_HOT_PATH_APPLIED__
   *)
module Cottas_pagecache_hot = struct
  (* Capacity 256 covers parliament's 26 rgs * 4 cols = 104 entries
     plus headroom for future larger corpora. Future tuning point. *)
  let initial_cap = Z.of_int 256

  let cache_ref : RDF_CottasStore_PageCache.page_cache ref =
    ref (RDF_CottasStore_PageCache.pcache_empty initial_cap)

  (* Stdlib.Int.t-typed counters — `open Prims` in this file shadows
     `int` to `Z.t`, so we name the native OCaml int explicitly. *)
  let n_hits : Stdlib.Int.t ref = Stdlib.ref 0
  let n_misses : Stdlib.Int.t ref = Stdlib.ref 0

  (* Drop-in replacement for
     Parquet_Footer.probe_parquet_column_decode_in_row_group. Same
     argument shape, same return type. The F* `pcache_decode_in_row_group`
     returns a `(value, new_cache)` tuple; we re-bind the ref to thread
     state. *)
  let cached_decode (path : string) (rg : Z.t) (col : Z.t)
    : string FStar_Pervasives_Native.option Prims.list
        FStar_Pervasives_Native.option =
    let cap = (!cache_ref).RDF_CottasStore_PageCache.pc_capacity in
    let key_present =
      let (v, _) = RDF_CottasStore_PageCache.pcache_get !cache_ref (rg, col) in
      match v with FStar_Pervasives_Native.Some _ -> true | _ -> false in
    let (result, c') =
      RDF_CottasStore_PageCache.pcache_decode_in_row_group
        !cache_ref path rg col cap in
    cache_ref := c';
    (if key_present then Stdlib.incr n_hits else Stdlib.incr n_misses);
    let total : Stdlib.Int.t = Stdlib.(!n_hits + !n_misses) in
    (if Stdlib.(total mod 32 = 0) then
      Printf.eprintf "[pagecache-hot-trace] hits=%d misses=%d entries=%d cap=%d\\n%!"
        !n_hits !n_misses
        (Stdlib.List.length (!cache_ref).RDF_CottasStore_PageCache.pc_entries)
        (Z.to_int cap));
    result
end

'''

# Anchor: the line right before `module Cottas_ondisk_runtime = struct`.
runtime_anchor = "module Cottas_ondisk_runtime = struct"
if runtime_anchor not in content:
    sys.stderr.write("  [pagecache-hot-path] FATAL: could not find 'module Cottas_ondisk_runtime = struct' anchor.\n")
    sys.exit(1)

content = content.replace(runtime_anchor, helper_module + runtime_anchor, 1)

# ----------------------------------------------------------------------
# 2. Substitute hot-path probe_parquet calls in walk_rg (search_fast_inner)
#    and the search_fast_limited inner walk. We anchor on the
#    surrounding structure so we don't touch lazy-populate or
#    Lamed3-reader call sites.
#
# search_fast_inner walk_rg has 4 calls (cols 0..3). We replace each
# with cached_decode.
# ----------------------------------------------------------------------

# Pattern is the same column-decode line. We substitute ALL occurrences
# in a CONTROLLED region by walking through the source and only
# substituting between known anchors.
#
# The simplest correct approach: find the `walk_rg` body for
# search_fast_inner and the loop body for search_fast_limited, and
# substitute within each. Use precise multi-line anchors (3-line minimum)
# for uniqueness.

substitutions = [
    # search_fast_inner walk_rg subject column (line ~1758)
    ('''      let s_lst = Parquet_Footer.probe_parquet_column_decode_in_row_group path (Z.of_int rg) Z.zero in
      Printf.eprintf "[pe4-trace] search_fast rg=%d decoded col=0 (subject) rss=%dMB heap=%dMB\\n%!"
        rg (pe4_rss_mb ()) (pe4_gc_mb ());''',
     '''      let s_lst = Cottas_pagecache_hot.cached_decode path (Z.of_int rg) Z.zero in
      Printf.eprintf "[pe4-trace] search_fast rg=%d decoded col=0 (subject) rss=%dMB heap=%dMB\\n%!"
        rg (pe4_rss_mb ()) (pe4_gc_mb ());'''),
    # search_fast_inner walk_rg predicate column
    ('''      let p_lst = Parquet_Footer.probe_parquet_column_decode_in_row_group path (Z.of_int rg) Z.one in
      Printf.eprintf "[pe4-trace] search_fast rg=%d decoded col=1 (predicate) rss=%dMB heap=%dMB\\n%!"
        rg (pe4_rss_mb ()) (pe4_gc_mb ());''',
     '''      let p_lst = Cottas_pagecache_hot.cached_decode path (Z.of_int rg) Z.one in
      Printf.eprintf "[pe4-trace] search_fast rg=%d decoded col=1 (predicate) rss=%dMB heap=%dMB\\n%!"
        rg (pe4_rss_mb ()) (pe4_gc_mb ());'''),
    # search_fast_inner walk_rg object column
    ('''      let o_lst = Parquet_Footer.probe_parquet_column_decode_in_row_group path (Z.of_int rg) (Z.of_int 2) in
      Printf.eprintf "[pe4-trace] search_fast rg=%d decoded col=2 (object) rss=%dMB heap=%dMB\\n%!"
        rg (pe4_rss_mb ()) (pe4_gc_mb ());''',
     '''      let o_lst = Cottas_pagecache_hot.cached_decode path (Z.of_int rg) (Z.of_int 2) in
      Printf.eprintf "[pe4-trace] search_fast rg=%d decoded col=2 (object) rss=%dMB heap=%dMB\\n%!"
        rg (pe4_rss_mb ()) (pe4_gc_mb ());'''),
    # search_fast_inner walk_rg graph column
    ('''      let g_lst = Parquet_Footer.probe_parquet_column_decode_in_row_group path (Z.of_int rg) (Z.of_int 3) in
      Printf.eprintf "[pe4-trace] search_fast rg=%d decoded col=3 (graph) rss=%dMB heap=%dMB\\n%!"
        rg (pe4_rss_mb ()) (pe4_gc_mb ());''',
     '''      let g_lst = Cottas_pagecache_hot.cached_decode path (Z.of_int rg) (Z.of_int 3) in
      Printf.eprintf "[pe4-trace] search_fast rg=%d decoded col=3 (graph) rss=%dMB heap=%dMB\\n%!"
        rg (pe4_rss_mb ()) (pe4_gc_mb ());'''),
    # search_fast_limited_inner: 4 column decodes inline (variable `r` not `rg`)
    ('''        let s_lst = Parquet_Footer.probe_parquet_column_decode_in_row_group path (Z.of_int r) Z.zero in
        let s_arr = arr_of_col s_lst in
        let p_lst = Parquet_Footer.probe_parquet_column_decode_in_row_group path (Z.of_int r) Z.one in
        let p_arr = arr_of_col p_lst in
        let o_lst = Parquet_Footer.probe_parquet_column_decode_in_row_group path (Z.of_int r) (Z.of_int 2) in
        let o_arr = arr_of_col o_lst in
        let g_lst = Parquet_Footer.probe_parquet_column_decode_in_row_group path (Z.of_int r) (Z.of_int 3) in
        let g_arr = arr_of_col g_lst in''',
     '''        let s_lst = Cottas_pagecache_hot.cached_decode path (Z.of_int r) Z.zero in
        let s_arr = arr_of_col s_lst in
        let p_lst = Cottas_pagecache_hot.cached_decode path (Z.of_int r) Z.one in
        let p_arr = arr_of_col p_lst in
        let o_lst = Cottas_pagecache_hot.cached_decode path (Z.of_int r) (Z.of_int 2) in
        let o_arr = arr_of_col o_lst in
        let g_lst = Cottas_pagecache_hot.cached_decode path (Z.of_int r) (Z.of_int 3) in
        let g_arr = arr_of_col g_lst in'''),
]

applied = 0
for old, new in substitutions:
    if old in content:
        content = content.replace(old, new, 1)
        applied += 1
    else:
        sys.stderr.write(f"  [pagecache-hot-path] WARN: substitution not found (skipping):\n    head: {old[:80]}\n")

if applied == 0:
    sys.stderr.write("  [pagecache-hot-path] FATAL: no substitutions applied; aborting (anchors all failed).\n")
    sys.exit(1)

path.write_text(content)
sys.stderr.write(f"  [pagecache-hot-path] applied: helper module + {applied}/5 hot-path column-decode substitutions routed through F* page cache\n")
PYEOF

echo "  Page-cache hot-path patch applied."
