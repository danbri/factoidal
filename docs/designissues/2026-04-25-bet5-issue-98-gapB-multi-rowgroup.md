# Bet5 — Issue #98 Gap B: multi-row-group iteration

> **Provenance note:** the actual changes in this work landed in commit
> `75315bc` (titled "sparql-store: scratch design — Phase 1 compound
> indexes (issue #100)"). That title is misleading: the commit
> mechanically picked up Bet5's `Parquet.Footer.fst` (+368 LoC),
> `cottas_runtime.sh` (+16 LoC), and this scratch doc, alongside Het's
> sparql-store scratch doc. Separate commits would have been cleaner;
> the work is correct, the message is just under-credited. Functions of
> interest: `probe_parquet_column_decode_in_row_group`,
> `probe_parquet_column_decode_all_row_groups`,
> `probe_parquet_column_chunk_in_row_group_locator`.

## Problem

Resh's Gap A (commit `832d2f2`) added a working RLE_DICTIONARY decoder so that
COTTAS columns 1 (predicates) and 3 (graphs) can now be read alongside columns
0/2 (subjects/objects via DELTA_LENGTH_BYTE_ARRAY).

But every column-decode helper in `Parquet.Footer.fst` walks the parquet
metadata to the **first row group only**:

```fstar
match nth_compact_list_element_start_hex meta_hex
        row_groups_field.cf_value_start /* implicit row_group=0 */
        meta_hex_len with
| Some row_group_start -> ...
```

Then drills into `columns[col_index]` of that row group. The parliament COTTAS
has ~25 row groups (~125k rows each, ~3.14M total). Today the loader sees only
the first 122,880.

## Fix shape

Add row-group-indexed siblings of the existing helpers, then concatenate
across all row groups for the bulk loader.

The minimal contract for Bet4 (lazy backend) is:

```fstar
val probe_parquet_row_group_count : path -> option nat   (* exists *)

val probe_parquet_column_decode_in_row_group
  : path -> rg_index:nat -> col_index:nat -> option (list (option string))

val probe_parquet_column_decode_all_row_groups
  : path -> col_index:nat -> option (list (option string))   (* eager loader *)
```

For the eager loader to actually find a row group beyond the first, we need
to thread `rg_index` through:

  - `probe_parquet_column_data_page_offset`
  - `probe_parquet_column_dictionary_page_offset`
  - `probe_parquet_column_page_header_compressed_size`
  - `probe_parquet_column_page_header_uncompressed_size`
  - `probe_parquet_column_page_header_num_values`
  - `probe_parquet_column_decompressed_payload_hex`
  - and the DLBA + RLE_DICTIONARY page-cache builders that compose them.

## Strategy: don't touch existing helpers

To minimise blast radius and stay strictly additive (Bet4 also editing
the same area), I'll add a parallel family of `_in_row_group` functions
and have the existing ones `_at_rg0 = _in_row_group ... 0`.

Concretely:

  1. `nth_compact_list_element_start_hex` already takes an index → trivially
     pass `rg_index` instead of hard-coded 0.
  2. Add `probe_parquet_column_data_page_offset_in_row_group`,
     `_dictionary_page_offset_in_row_group`, `_decompressed_payload_hex_in_row_group`,
     etc. — copies of the existing functions but with `rg_index` parameter.
  3. Re-build `_dlba_decode_all_in_row_group` and
     `_rle_dictionary_decode_all_in_row_group` on top.
  4. `probe_parquet_column_decode_in_row_group` = dispatcher.
  5. `probe_parquet_column_decode_all_row_groups` = walk
     `[0..row_group_count)` calling `_in_row_group` and concat the lists.

The existing `probe_parquet_column_decode_all` stays for backward compat
(it'll keep returning row-group-0 only). The cottas_runtime glue switches
to `probe_parquet_column_decode_all_row_groups`.

## Termination

  - Walking `[0..row_group_count)` is a `for i in range` style fold, easy
    `decreases` on `remaining`.
  - All existing `Tot` measures are preserved.

## Verification & smoke test

  1. `fstar.exe Parquet.Footer.fst` (verify).
  2. After main thread runs `./build-ocaml.sh extract && build`, smoke
     test with `factoidal cottas-info parliament.cottas`. Expect
     `quads: 3143406` (was 122,880).
  3. W3C sweep: should be no-op (1656/1658 unchanged).

## Files touched

  - `formal/fstar/Parquet.Footer.fst` — only file required.
  - `formal/fstar/experimental_ocaml_glue/cottas_runtime.sh` — switch
    `probe_parquet_column_decode_all` → `probe_parquet_column_decode_all_row_groups`.
