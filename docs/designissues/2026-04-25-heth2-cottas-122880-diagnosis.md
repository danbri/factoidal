# Heth2 — COTTAS 122,880 quads diagnosis (2026-04-25)

Task: figure out why `factoidal cottas-info parliament/data.cottas` still
reports 122,880 quads after Bet5's `f3763a0` (multi-row-group iteration,
issue #98 Gap B) was merged and the binary rebuilt at 14:45Z.

## Hypothesis tree (from prompt)

1. cottas-info path doesn't go through `probe_parquet_column_decode_all_row_groups`.
2. Multi-row-group function silently returns first row group only (off-by-one).
3. Upstream cap on `value_count` (hardcoded 122880).
4. Patch `cottas_runtime.sh` was NOT re-applied due to early-exit guard
   `grep -q 'module Ballyhoo_cottas_runtime'`.

## Evidence collected

### File timestamps (fresh post-Wave-19)

```
bin/darwin-arm64/factoidal                              25 Apr 14:45
formal/fstar/ocaml-output/Parser_BallyhooCOTTAS.ml      25 Apr 14:44
formal/fstar/ocaml-output/Parquet_Footer.ml             25 Apr 14:44
formal/fstar/experimental_ocaml_glue/cottas_runtime.sh  25 Apr 14:27
```

Binary post-dates the .ml files — so the binary really was rebuilt from
the new extraction.

### Hypothesis 4 — early-exit guard

`cottas_runtime.sh` lines 21-23:
```sh
if grep -q 'module Ballyhoo_cottas_runtime' "$FILE"; then
  echo "  Ballyhoo COTTAS runtime glue already present."
  exit 0
fi
```

This guard exists. BUT — `build-ocaml.sh extract` regenerates the .ml
fresh from F\* (line 99-150), then runs `ocaml-patches.sh` (line 164),
which runs `cottas_runtime.sh`. Because the `.ml` is freshly extracted,
it does NOT contain `module Ballyhoo_cottas_runtime` yet, so the guard
does not trigger and the patch IS applied.

Verification: `Parser_BallyhooCOTTAS.ml` currently contains the new
text from the patch:

```
ocaml-output/Parser_BallyhooCOTTAS.ml:415-417:
  let decode_column artifact_path col_idx =
    match Parquet_Footer.probe_parquet_column_decode_all_row_groups
            artifact_path (Z.of_int col_idx) with
```

Compared with the patch source `experimental_ocaml_glue/cottas_runtime.sh:262`:
```
    match Parquet_Footer.probe_parquet_column_decode_all_row_groups
```

They match. Hypothesis 4 is **NOT** the cause — the patch DID get applied.

### Hypothesis 1 — wrong code path

Trace from `factoidal cottas-info`:

- `factoidal_cli.ml:702`: `Parser_BallyhooCOTTAS.Ballyhoo_cottas_runtime.cache_for_store store`
- `Parser_BallyhooCOTTAS.ml:481`: `cache_for_store ds = load_cache ds.cds_artifact_path`
- `Parser_BallyhooCOTTAS.ml:430` `load_cache`: calls `decode_column artifact_path 0..3`
- `Parser_BallyhooCOTTAS.ml:415-417` `decode_column`: calls
  `Parquet_Footer.probe_parquet_column_decode_all_row_groups`
- `factoidal_cli.ml:704`: `n_quads = List.length cache.quads`

Hypothesis 1 is **NOT** the cause — the cottas-info path goes through
the multi-row-group decoder.

### Binary symbol check

```
$ strings bin/darwin-arm64/factoidal | grep probe_parquet_column_decode
Parquet_Footer.probe_parquet_column_decode_all
Parquet_Footer.probe_parquet_column_decode_all_row_groups
Parquet_Footer.probe_parquet_column_decode_in_row_group
```

All three symbols are in the binary.

### F\* logic of `probe_parquet_column_decode_all_row_groups`

`Parquet.Footer.fst:2538-2546`:
```
let probe_parquet_column_decode_all_row_groups
  (path:string) (col_index:nat)
  : option (list (option string)) =
  match probe_parquet_row_group_count path with
  | None -> None
  | Some rg_count ->
    match collect_row_group_columns path col_index 0 rg_count rg_count [] with
    | None -> None
    | Some acc_rev -> Some (list_rev acc_rev)
```

`collect_row_group_columns` (line 2520-2533): `Tot` recursive accumulator,
walks `[rg_index .. rg_count)`. Looks correct.

If `probe_parquet_row_group_count` returned `1` instead of `25`, we'd see
exactly first-row-group behaviour.

### Per-row-group decoder pipeline (likely-broken-link candidates)

For RLE_DICTIONARY columns (predicates + graphs):

`probe_parquet_column_rle_dictionary_decode_all_in_row_group`
(Parquet.Footer.fst:2463) reads ONE data page only — its
`probe_parquet_column_page_header_num_values_in_row_group`
returns the num_values field of the FIRST data page header in the row
group's column chunk. If row group N has multiple data pages, only
page 0 is decoded.

Same for DLBA: `probe_parquet_column_delta_length_byte_array_decode_all_in_row_group`
(line 2451) builds ONE `dlba_page_cache` from the first data page of the
column chunk, then `dlba_page_decode_all_strings` decodes that single page.

For rg_index=0: if the file's row group 0 has its 122,880 rows split
across multiple data pages, we'd see fewer than 122,880. If 122,880 is
exactly one page, we'd see all of row group 0 and miss row groups 1-24.

122,880 = 120 × 1024. Most likely each row group has its rows in ONE
data page, but the iteration over row groups never advances. This points
back to either `probe_parquet_row_group_count` returning 1, OR
`probe_parquet_column_chunk_in_row_group_locator` failing for `rg_index ≥ 1`.

### Hypothesis 2 — silent off-by-one in `collect_row_group_columns`

The collect function:
```
if fuel = 0 then Some acc_rev
else if rg_index >= rg_count then Some acc_rev
```

`fuel` starts at `rg_count`, decrements each step. So for `rg_count=25`,
fuel covers rg_index 0..24. Looks correct. The accumulator gets
`Some acc_rev` even on the early-stop branches, so a too-low rg_count
WOULD return only the first rg's data successfully (no error, just less
data) — exactly the symptom.

## Most-likely root cause

`probe_parquet_row_group_count` returns `1` (or equivalent low value)
for the parliament file. Its implementation
(Parquet.Footer.fst:433-448) only consults
`decode_compact_list_count_hex` on field 4 of the metadata struct.

Looking at `decode_compact_list_info_hex` (line 302-316):

```
let count_nibble = high_nibble header in
...
if count_nibble < 15 then
  Some { cli_count = count_nibble; ... }
else
  match decode_varint_value_with_end_hex hex (pos + 2) 0 0 fuel with ...
```

For 25 row groups, the header byte's high nibble is `0xf` (sentinel for
"varint follows"), low nibble is `0xc` (compact_t_struct). The varint
decode reads from pos+2.

**However, there's a subtle issue** I cannot fully diagnose without
running the binary: `nth_field_hex meta_hex 4 0 0 meta_hex_len`
(Parquet.Footer.fst:443) walks fields by id starting from field 0
inside the file metadata struct. The Thrift compact protocol uses
field-id deltas, so if any prior field is missing or out-of-order, we
may land on the wrong field. If we accidentally land on a singleton-list
field (e.g. schema), we'd get count=1.

A second possibility is that `probe_parquet_column_chunk_in_row_group_locator`
fails for rg_index≥1 because it walks the row_groups list element-by-element
via `nth_compact_list_element_start_hex`, which uses
`skip_compact_value_hex` on a struct element type. If `skip_compact_value_hex`
miscomputes the size of the first row-group struct, the walk goes off
into garbage and `nth_field_hex 1 ...` (looking for the columns list)
returns None. Then `probe_parquet_column_decode_in_row_group` returns
None → `collect_row_group_columns` returns None → the whole call returns
None and the caller `failwith`s. But the user sees 122,880 (no failure),
so this branch is NOT what's happening.

Therefore the BEST hypothesis is:
**`probe_parquet_row_group_count` is returning a small value
(probably 1), so `collect_row_group_columns` walks only that one
row group successfully and returns its 122,880 rows.**

## Recommended fix (one line)

In `formal/fstar/Parquet.Footer.fst:2541`, instrument by replacing the
single-call dispatch with a debug trace, or alternatively bypass
`probe_parquet_row_group_count` and use the row-group iteration
implicit in walking until `nth_compact_list_element_start_hex` returns
None. But for a true one-line fix:

`Parquet.Footer.fst:443`: change `nth_field_hex meta_hex 4 0 0 meta_hex_len`
to verify the field type **is** a list before extracting count, AND
cross-check by walking the actual row_groups list and counting elements
until the walker returns None. The simpler debug step is:

**Add a tiny CLI subcommand `parquet-row-group-count` that prints the
result of `Parquet_Footer.probe_parquet_row_group_count` on the file**,
to verify whether the count itself is wrong vs the iteration.

If row-group-count returns 25 but iteration still stops at 1, then the
locator (`probe_parquet_column_chunk_in_row_group_locator`) is the bug.

## Confidence

**Medium.** Without running the binary I can't tell whether the bug is
in `probe_parquet_row_group_count` (returning 1 silently), the
per-row-group locator (failing for rg≥1 silently — but we'd see a
failwith, not 122880), or upstream. The early-exit guard is NOT
the cause; the patch IS applied; the binary IS fresh; the call
chain IS correct in source. The 122,880-not-3.1M behaviour is
diagnostic of "rg_count is small, not iteration-failure".

## Next-step suggestions for whoever takes the bug

1. Add `factoidal parquet-row-group-count FILE` CLI subcommand and
   verify it returns 25 on parliament/data.cottas.
2. If it returns 1 — bug is in `probe_parquet_row_group_count` (line
   433-448). The list-count decode for the row_groups field is wrong.
   Likely cause: wrong field id (#4 vs schema's list at #2 etc), or
   `decode_compact_list_count_hex` failing the varint path.
3. If it returns 25 — bug is somewhere downstream in `collect_row_group_columns`
   or `probe_parquet_column_chunk_in_row_group_locator`. Add prints
   inside the loop.

Estimated 30-min fix once the print is wired up.
