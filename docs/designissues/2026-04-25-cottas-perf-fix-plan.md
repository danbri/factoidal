# COTTAS load-path perf fix plan (Codex Phase 1)

**Date:** 2026-04-25
**Agent:** Cottas-Perf
**Scope:** items #1 and #2 of Codex's ranked recommendation in
`2026-04-25-cottas-parquet-load-path-perf.md`. F\*-first per Chi's review
(`2026-04-25-second-backend-options-review.md` Step A).

## What we are fixing

`factoidal --data-cottas` on the 3.14 M-quad UK Parliament artifact
spends ~90 s in `load_cottas_dataset` / `load_cache` before any algebra
evaluation begins. The hot frames are
`Parquet_Footer.skip_varint_hex` / `decode_varint_hex` /
`BatUTF8.nth_aux` — i.e. **per-cell** footer probing through
hex-string/UTF-8 traversals. ~12.6 M per-cell fetches for one `COUNT(*)`.

Two compounding O(N²) blowups:

1. **Footer / metadata is re-decoded on every cell.** Each
   `probe_parquet_column_*` call re-reads the file tail, re-parses the
   compact-thrift footer, re-walks the column metadata.
2. **Per-cell page decode.** Inside one column,
   `probe_parquet_column_delta_length_byte_array_value_hex_at` calls
   `sum_previous_lengths` which re-decompresses the entire zstd payload
   for every prior length, and then again for the current length, and
   then again to slice the value bytes. ~3 N varint walks **per row**
   over a fully-decompressed payload, then × 4 columns × N rows.

## Plan

### Step 1 (F\*) — page cache record

In `Parquet.Footer.fst`, add a pure record that captures **everything
needed to decode a DELTA_LENGTH_BYTE_ARRAY column page**, computed
once:

```fstar
noeq type dlba_page_cache = {
  dpc_payload_hex : string;          // decompressed page bytes (hex)
  dpc_values_offset : nat;           // byte offset to varint header start
  dpc_value_count : nat;             // total values on the page
  dpc_first_length : nat;
  dpc_min_delta : int;
  dpc_bit_width : nat;
  dpc_packed_start : nat;            // start of bit-packed length deltas
  dpc_value_data_offset : nat;       // start of contiguous value bytes
                                     // (relative to values_offset)
  dpc_lengths : list nat;            // all decoded lengths, in order
  dpc_value_starts : list nat;       // prefix sums (start-byte for each value)
}
```

`build_dlba_page_cache : string -> nat -> option dlba_page_cache`
performs *one* pass over `decompressed_payload_hex`, walks the four
varints to land on `bit_width`, then loops `value_count - 1` times
through `packed_lsb_value_hex` to materialise all length deltas, then
computes the running prefix-sum so per-row indexing is O(1).

`dlba_page_value_hex_from_cache : dlba_page_cache -> nat -> option string`
indexes into `dpc_value_starts` / `dpc_lengths` and slices
`dpc_payload_hex`.

`dlba_page_value_string_from_cache : dlba_page_cache -> nat -> option string`
chains the above with `ascii_string_of_hex_slice`.

`dlba_page_decode_all_strings : dlba_page_cache -> list (option string)`
returns every value as a string in row order — the **bulk** API the
glue actually wants.

### Step 2 (F\*) — multi-column entry point

`probe_parquet_column_delta_length_byte_array_page_cache : string -> nat -> option dlba_page_cache`
wraps Step 1 starting from a path + column index. This is the cache key
the OCaml glue will memoise.

`probe_parquet_column_delta_length_byte_array_decode_all : string -> nat -> option (list string)`
is the column-bulk entry: returns the decoded string for every row in
the column. Per-call work is now O(N) instead of O(N²) per column.

### Step 3 (OCaml glue) — replace the per-cell loop

In `experimental_ocaml_glue/cottas_runtime.sh`:

* Call `Parquet_Footer.probe_parquet_column_delta_length_byte_array_decode_all`
  once for each of the 4 columns (s, p, o, g).
* Zip the four resulting lists into the existing `quad_row` form.
* Drop the `for i = 0 to value_count - 1 do … fetch col` inner loop —
  no more 12.6 M per-cell calls.

Net work for the parliament corpus: **4 page-decode passes, not
~12.6 M re-probes**. Footer is decoded as part of the first
`probe_parquet_column_decompressed_payload_hex`; we don't yet add a
second-tier "footer cache" record (Step 4 below) — the page cache
already amortises footer decode across ~3.1 M lookups in one column,
which is the dominant cost.

### Step 4 (deferred) — explicit per-file footer record

A `parquet_footer_cache` keyed on path is the obvious next move and
matches Codex's #1 rec, but inspecting the metadata path shows that
each `probe_*` only re-reads the file tail (8 / `pf_footer_len` bytes)
and walks the compact-thrift struct — bounded by metadata size, not by
row count. The dominant cost is **per-cell page rewalk**, not
**per-cell footer reread**. We get the bigger win first by collapsing
the per-cell page rewalk; per-file footer caching is a follow-up.

## Verification

```bash
fstar.exe --include . --cache_dir .cache Parquet.Footer.fst
```

No `--lax`. New helpers stay in `Parquet.Footer.fst`. The bulk decode
helper threads a `fuel` parameter explicitly so totality is obvious to
the SMT solver.

## Wallclock target

> 64 MB parliament COTTAS, single `ASK { ?s ?p ?o }` (returns true after
the load): from ~90 s to < 10 s.

## Out of scope (Phase 2 / Phase 3)

- Lazy / streaming COUNT(*) (Codex #3).
- HDT-style buffer pool (MillenniumDB study).
- Per-page cache eviction.
- Multi-row-group support — current code assumes the parliament corpus
  is one row group; we do not regress that.
- Replacing the OCaml-side `Hashtbl.find_opt` interning (still O(1)
  amortised; not the bottleneck).

## Files touched

* `formal/fstar/Parquet.Footer.fst` — new pure helpers (~150 LoC F\*).
* `formal/fstar/experimental_ocaml_glue/cottas_runtime.sh` — replace
  per-cell loop with column-bulk decode.

No new patches in `minimal_regrettable_glue_code_each_with_an_open_issue/`.
No changes to `Parser.BallyhooCOTTAS.fst`.
