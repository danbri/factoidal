#!/bin/bash
# Realises the F* `assume val pcache_decode_column_at_indices_global_
# from_table` declared in RDF.CottasStore.PageCache.fst (OPTIONAL/FILTER
# row-index-selective decode design, docs/designissues/2026-07-13-
# optional-filter-selective-decode.md, stage 2). Open gap: issue #295.
#
# Contract (see the assume val's own banner for the full text): given a
# row-group-offset table, a column, and a list of REQUESTED row indices,
# return `Some pairs` of `(index, token)` for every requested index that
# has a decoded value (omitting out-of-range indices and `None` cells),
# or `None` if the row group's column could not be decoded at all.
#
# THIS realisation is the fallback-only half of the contract: it decodes
# the FULL column via the existing table-threaded decoder
# (`Parquet_Footer.probe_parquet_column_decode_in_row_group_from_table`,
# the exact same call `RDF_CottasStore_ColumnSeq`'s own `_from_table`
# sibling already uses — see cottas_column_seq_runtime.sh) and then
# filters to the requested indices. Correct for every encoding
# (RLE_DICTIONARY, DLBA, PLAIN alike); NOT yet accelerated for
# RLE_DICTIONARY (the design's targeted win — index-array + dict-page
# lookup restricted to the requested rows, touching none of the other
# rows' cells) — that fast path is issue #295's acknowledged remaining
# gap. Rule #11(c) compliant: thin dispatch shim, no semantic decisions,
# reuses the SAME underlying F*-realised decoder every other
# `_from_table` caller already goes through.

set -euo pipefail

OUTDIR="$1"

ML="$OUTDIR/RDF_CottasStore_PageCache.ml"

if [[ ! -f "$ML" ]]; then
  echo "  [pagecache-indexed] WARN: $ML not found; skipping."
  exit 0
fi

if grep -q '__PAGECACHE_INDEXED_APPLIED__' "$ML"; then
  echo "  [pagecache-indexed] already applied; skipping."
  exit 0
fi

python3 - "$ML" <<'PYEOF'
import sys, pathlib, re

path = pathlib.Path(sys.argv[1])
content = path.read_text()

fn = "pcache_decode_column_at_indices_global_from_table"
pattern = re.compile(
    r"let " + re.escape(fn) + r"\s*"
    r"\(table\s*:\s*Parquet_Footer\.parquet_row_group_offset_table\)\s*"
    r"\(path\s*:\s*Prims\.string\)\s*\(rg_index\s*:\s*Prims\.nat\)\s*\(col_index\s*:\s*Prims\.nat\)\s*"
    r"\(indices\s*:\s*Prims\.nat\s+Prims\.list\)\s*:\s*"
    r"\(Prims\.nat\s*\*\s*Prims\.string\)\s+Prims\.list\s+FStar_Pervasives_Native\.option=\s*"
    r"failwith\s*"
    r'"Not yet implemented: RDF\.CottasStore\.PageCache\.' + re.escape(fn) + r'"',
    re.MULTILINE,
)

new_block = '''(* OPTIONAL/FILTER row-index-selective decode design (stage 2, issue
   #295 tracks the acknowledged RLE_DICTIONARY-fast-path gap):
   realisation of the F*-pure `pcache_decode_column_at_indices_global_
   from_table` assume val. Fallback-only: decodes the full column via
   the SAME table-threaded decoder every other `_from_table` caller
   already uses, then filters to the requested indices. Correct for
   every Parquet encoding; not yet accelerated for RLE_DICTIONARY (see
   this file's own header comment and issue #295).
   __PAGECACHE_INDEXED_APPLIED__ *)
let pcache_decode_column_at_indices_global_from_table
  (table : Parquet_Footer.parquet_row_group_offset_table)
  (path : Prims.string) (rg_index : Prims.nat) (col_index : Prims.nat)
  (indices : Prims.nat Prims.list)
  : (Prims.nat * Prims.string) Prims.list FStar_Pervasives_Native.option =
  match Parquet_Footer.probe_parquet_column_decode_in_row_group_from_table
          table path rg_index col_index with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some lst ->
    let arr = Array.of_list lst in
    let len = Array.length arr in
    let pick (i : Prims.nat) : (Prims.nat * Prims.string) option =
      (* Z-domain comparisons: >=/< in this module scope may be
      rebound over Z.t (Prims), so avoid bare int operators entirely. *)
      if Z.geq i Z.zero && Z.lt i (Z.of_int len) then
        (let iv = Z.to_int i in
         match arr.(iv) with
         | FStar_Pervasives_Native.Some tok -> Some (i, tok)
         | FStar_Pervasives_Native.None -> None)
      else None
    in
    FStar_Pervasives_Native.Some (List.filter_map pick indices)'''

new_content, n = pattern.subn(new_block, content, count=1)
if n != 1:
    sys.stderr.write("  [pagecache-indexed] WARN: assume-val stub not matched (regex didn't fire)\n")
    sys.exit(1)

path.write_text(new_content)
sys.stderr.write("  [pagecache-indexed] replaced pcache_decode_column_at_indices_global_from_table stub\n")
PYEOF

echo "  Cottas page-cache indexed decoder applied."
