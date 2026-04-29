#!/bin/bash
# Phase 2.5e (issue #118) — realise the F* `assume val
# pcache_decode_in_row_group_global` declared in
# RDF.CottasStore.PageCache.fst.
#
# The F* spec layer reasons about the LRU + clock semantics via the
# pure `pcache_get` / `pcache_put` / `pcache_decode_in_row_group`
# functions. The CROSS-CALL STORAGE CELL — a process-level mutable
# `ref` holding the current `page_cache` record — lives in OCaml,
# because F* is pure-by-default and threading the cache record
# through every public-API call chain would (a) be noisy and (b) not
# survive multiple HTTP requests anyway.
#
# Rule #11(c) compliant: thin dispatch shim. No semantic decisions —
# only state plumbing. Capacity 256 covers parliament's 26 rgs * 4
# cols = 104 entries with headroom.

set -euo pipefail

OUTDIR="$1"

if [[ -f "$OUTDIR" && "$OUTDIR" == *.ml ]]; then
  ML="$OUTDIR"
else
  ML="$OUTDIR/RDF_CottasStore_PageCache.ml"
fi

if [[ ! -f "$ML" ]]; then
  echo "  [pagecache-global] WARN: $ML not found; skipping."
  exit 0
fi

if grep -q '__PAGECACHE_GLOBAL_APPLIED__' "$ML"; then
  echo "  [pagecache-global] already applied; skipping."
  exit 0
fi

python3 - "$ML" <<'PYEOF'
import sys, pathlib, re

path = pathlib.Path(sys.argv[1])
content = path.read_text()

# F* 2025.x extracts the assume val. Match permissively for header
# (one-line vs split params) and failwith body (one-line vs split).
fn = "pcache_decode_in_row_group_global"
pattern = re.compile(
    r"let " + re.escape(fn) +
    r"\s*\(path\s*:\s*Prims\.string\)\s*"
    r"\(rg_index\s*:\s*Prims\.nat\)\s*"
    r"\(col_index\s*:\s*Prims\.nat\)\s*"
    r":\s*RDF_CottasStore_ColumnSeq\.cottas_column\s+FStar_Pervasives_Native\.option=\s*"
    r"failwith\s*"
    r'"Not yet implemented: RDF\.CottasStore\.PageCache\.' + re.escape(fn) + r'"',
    re.MULTILINE,
)

new_block = '''(* Phase 2.5e (issue #118): cross-call cache storage cell + realisation
   of the F*-pure `pcache_decode_in_row_group_global` assume val.

   The cache logic (LRU eviction, monotone clock, key match) lives in
   the F*-verified `pcache_get` / `pcache_put` / `pcache_decode_in_row_group`
   functions above. This shim only threads the mutable storage ref
   across calls. Rule #11(c). __PAGECACHE_GLOBAL_APPLIED__ *)
let pcache_global_capacity : Z.t = Z.of_int 256

let pcache_global_ref : page_cache ref =
  ref (pcache_empty pcache_global_capacity)

(* Stdlib.Int.t-typed counters; `open Prims` shadows `int` to `Z.t`
   in this file, so qualify with Stdlib explicitly. *)
let pcache_global_n_hits   : Stdlib.Int.t ref = Stdlib.ref 0
let pcache_global_n_misses : Stdlib.Int.t ref = Stdlib.ref 0

let pcache_decode_in_row_group_global (path : Prims.string)
  (rg_index : Prims.nat) (col_index : Prims.nat)
  : RDF_CottasStore_ColumnSeq.cottas_column FStar_Pervasives_Native.option =
  let cap = (!pcache_global_ref).pc_capacity in
  let key_present =
    let (v, _) = pcache_get !pcache_global_ref (rg_index, col_index) in
    match v with FStar_Pervasives_Native.Some _ -> true | _ -> false in
  let (result, c') =
    pcache_decode_in_row_group !pcache_global_ref path rg_index col_index cap in
  pcache_global_ref := c';
  (if key_present then Stdlib.incr pcache_global_n_hits
   else Stdlib.incr pcache_global_n_misses);
  let total : Stdlib.Int.t = Stdlib.(!pcache_global_n_hits + !pcache_global_n_misses) in
  (if Stdlib.(total mod 32 = 0) then
    Printf.eprintf "[pagecache-global-trace] hits=%d misses=%d entries=%d cap=%d\\n%!"
      !pcache_global_n_hits !pcache_global_n_misses
      (Stdlib.List.length (!pcache_global_ref).pc_entries)
      (Z.to_int cap));
  result'''

new_content, n = pattern.subn(new_block, content, count=1)
if n != 1:
    sys.stderr.write("  [pagecache-global] WARN: assume-val stub not matched (regex didn't fire)\n")
    sys.exit(1)

path.write_text(new_content)
sys.stderr.write("  [pagecache-global] replaced pcache_decode_in_row_group_global stub\n")
PYEOF

echo "  Cottas page-cache global decoder applied."
