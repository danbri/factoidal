#!/bin/bash
# Realises the F* `assume val pcache_decode_column_at_indices_global_
# from_table` declared in RDF.CottasStore.PageCache.fst (OPTIONAL/FILTER
# row-index-selective decode design, docs/designissues/2026-07-13-
# optional-filter-selective-decode.md, stage 2). Issue #295.
#
# Contract (see the assume val's own banner for the full text): given a
# row-group-offset table, a column, and a list of REQUESTED row indices,
# return `Some pairs` of `(index, token)` for every requested index that
# has a decoded value (omitting out-of-range indices and `None` cells),
# or `None` if the row group's column could not be decoded at all. For a
# genuinely empty `indices` list, return `Some []` without probing the
# page at all.
#
# THIS realisation is the RLE_DICTIONARY fast path the design targets:
# it decodes the per-row dictionary INDEX ints (cheap — small ints, one
# hybrid-RLE/bit-packed pass, `Parquet_Footer.probe_parquet_column_
# rle_dictionary_row_indices_in_row_group_from_table`, a NEW F*-pure
# function added alongside this patch that stops the existing
# RLE_DICTIONARY decode pipeline one step before the dictionary lookup)
# plus the dictionary-page entries (tiny — distinct values only,
# `Parquet_Footer.probe_parquet_column_dictionary_in_row_group_from_
# table`, already existed), then resolves strings ONLY at the requested
# row positions via array indexing on the two decoded arrays. This is
# what the assume val's banner pre-approved as "resolve only requested
# positions against the dict-page entries array" — the decode algorithms
# (hybrid RLE/bit-packed run decode, dictionary PLAIN decode, encoding
# dispatch) all stay in F* (Parquet.Footer.fst); this shim only does
# array-index selection, no semantic decisions. Skips the O(n)
# `map_indices_to_dict` full-column STRING materialization that the
# fallback-only realisation (and every other `_decode_all`-family
# caller) pays for every row, not just the requested ones — that
# materialization was the measured q6 regression (9.5s -> 15.9s,
# 1ad16cf/86b188d/2500743) this patch fixes.
#
# DLBA/PLAIN-encoded pages (and any encoding this reader doesn't
# implement) have no such index/dictionary split and keep the
# documented full-decode-then-filter fallback: decode the FULL column
# via the existing table-threaded decoder
# (`Parquet_Footer.probe_parquet_column_decode_in_row_group_from_table`,
# the exact same call `RDF_CottasStore_ColumnSeq`'s own `_from_table`
# sibling already uses — see cottas_column_seq_runtime.sh) and then
# filter to the requested indices. Correct, simply unaccelerated for
# those encodings — same trade-off `RDF.CottasStore.fst`'s
# `filter_column_by_indices` already documents for the no-table branch.
# Rule #11(c) compliant: thin dispatch shim, no semantic decisions,
# reuses the SAME underlying F*-realised decoders every other
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
   #295 -- RLE_DICTIONARY fast path landed): realisation of the F*-pure
   `pcache_decode_column_at_indices_global_from_table` assume val.
   RLE_DICTIONARY pages: decode the per-row dictionary INDEX ints
   (Parquet_Footer.probe_parquet_column_rle_dictionary_row_indices_
   in_row_group_from_table, new F*-pure function, stops the existing
   decode pipeline before the dictionary lookup) and the dictionary
   entries (Parquet_Footer.probe_parquet_column_dictionary_in_row_
   group_from_table, tiny -- distinct values only), then resolve
   strings ONLY at the requested row positions via array indexing --
   skips the O(n) full-column string materialization
   (`map_indices_to_dict`) every `_decode_all`-family caller otherwise
   pays for every row. DLBA/PLAIN pages (and any encoding this reader
   doesn't implement) keep the documented full-decode-then-filter
   fallback via the SAME table-threaded decoder every other
   `_from_table` caller already uses. No semantic decisions here --
   the decode algorithms (hybrid RLE/bit-packed run decode, dictionary
   PLAIN decode, encoding dispatch) all stay in F* (Parquet.Footer.fst);
   this shim only selects array positions. See this file's own header
   comment for the full rationale. __PAGECACHE_INDEXED_APPLIED__ *)
let pcache_decode_column_at_indices_global_from_table
  (table : Parquet_Footer.parquet_row_group_offset_table)
  (path : Prims.string) (rg_index : Prims.nat) (col_index : Prims.nat)
  (indices : Prims.nat Prims.list)
  : (Prims.nat * Prims.string) Prims.list FStar_Pervasives_Native.option =
  match indices with
  | [] -> FStar_Pervasives_Native.Some []
  | _ ->
    (* Z-domain comparisons: >=/< in this module scope may be rebound
       over Z.t (Prims), so avoid bare int operators entirely
       throughout this function. *)
    let in_bounds (i : Prims.nat) len : bool =
      Z.geq i Z.zero && Z.lt i (Z.of_int len)
    in
    match Parquet_Footer.probe_parquet_column_page_header_data_encoding_in_row_group_from_table
            table path rg_index col_index with
    | FStar_Pervasives_Native.Some "RLE_DICTIONARY" ->
      (match Parquet_Footer.probe_parquet_column_rle_dictionary_row_indices_in_row_group_from_table
               table path rg_index col_index with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some idx_lst ->
         (match Parquet_Footer.probe_parquet_column_dictionary_in_row_group_from_table
                  table path rg_index col_index with
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some dict_lst ->
            let idx_arr = Array.of_list idx_lst in
            let idx_len = Array.length idx_arr in
            let dict_arr = Array.of_list dict_lst in
            let dict_len = Array.length dict_arr in
            let pick (i : Prims.nat) : (Prims.nat * Prims.string) option =
              if in_bounds i idx_len then
                let dict_idx = idx_arr.(Z.to_int i) in
                if in_bounds dict_idx dict_len then
                  Some (i, dict_arr.(Z.to_int dict_idx))
                else None
              else None
            in
            FStar_Pervasives_Native.Some (List.filter_map pick indices)))
    | _ ->
      (match Parquet_Footer.probe_parquet_column_decode_in_row_group_from_table
               table path rg_index col_index with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some lst ->
         let arr = Array.of_list lst in
         let len = Array.length arr in
         let pick (i : Prims.nat) : (Prims.nat * Prims.string) option =
           if in_bounds i len then
             (let iv = Z.to_int i in
              match arr.(iv) with
              | FStar_Pervasives_Native.Some tok -> Some (i, tok)
              | FStar_Pervasives_Native.None -> None)
           else None
         in
         FStar_Pervasives_Native.Some (List.filter_map pick indices))'''

new_content, n = pattern.subn(new_block, content, count=1)
if n != 1:
    sys.stderr.write("  [pagecache-indexed] WARN: assume-val stub not matched (regex didn't fire)\n")
    sys.exit(1)

path.write_text(new_content)
sys.stderr.write("  [pagecache-indexed] replaced pcache_decode_column_at_indices_global_from_table stub\n")
PYEOF

echo "  Cottas page-cache indexed decoder applied."
