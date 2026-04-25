# Issue #98 (Agent Resh) — RLE_DICTIONARY decoder + multi-row-group plan

**Started:** 2026-04-25
**Branch:** `claude/main`
**Issue:** https://github.com/danbri/factoidal/issues/98
**Plan parent:** `docs/designissues/2026-04-25-issue-98-rle-dictionary-plan.md`

## Resh's reading of the gap

After Yod3's #97 fix:
- DLBA columns 0 (subjects) + 2 (objects) decode in `~4.3s`.
- Columns 1 (predicates) + 3 (graph names) are RLE_DICTIONARY → decode_all returns None → `failwith "Could not bulk-decode COTTAS column 1"`.
- Even on success, only the first of ~25 row groups is read (122,880 / 3,143,406 rows).

## Strategy

Pick A first (plan recommendation). It unlocks predicates+graphs immediately. Multi-row-group iteration (B) is a follow-up.

### A. RLE_DICTIONARY decoder (this commit)

Two pages per column:
1. **Dictionary page** (page header type=`DICTIONARY_PAGE`, encoding `PLAIN_DICTIONARY`):
   sequence of length-prefixed BYTE_ARRAY. Length = LE u32 (4 bytes), then value bytes.
2. **Data page** (page header type=`DATA_PAGE`, encoding `RLE_DICTIONARY` or `PLAIN_DICTIONARY`):
   first byte = bit-width of indices, remaining bytes = hybrid RLE-bit-packed indices.

Today the code only reads the *data page* (via `probe_parquet_column_data_page_offset` which returns col `data_page_offset` — actually the metadata field 9 = `dictionary_page_offset` for dictionary-encoded columns? need to verify). The dictionary page is at `dictionary_page_offset` (Thrift field 10 of `column_metadata`).

**Wire-format check:** Parquet column_metadata Thrift (parquet.thrift):
```
struct ColumnMetaData {
  1: required Type type
  2: required list<Encoding> encodings
  3: required list<string> path_in_schema
  4: required CompressionCodec codec
  5: required i64 num_values
  6: required i64 total_uncompressed_size
  7: required i64 total_compressed_size
  ...
  9: required i64 data_page_offset
  10: optional i64 index_page_offset
  ...
  14: optional i64 dictionary_page_offset
}
```

So I need `probe_parquet_column_dictionary_page_offset` (field 14). Looking at the existing `_data_page_offset` (field 9) lookup — same shape, different field id.

But wait — in pycottas-emitted parquet, the *page header* of the first page has its own encoding/type info. If `data_page_offset` actually points at the dictionary page (which is then immediately followed by the data page in storage), we can chain: read first page header at `data_page_offset`, if `DICTIONARY_PAGE`, parse its payload as the dictionary, then advance past the page (header_len + compressed_size) and read the next page header (data page).

Actually looking at parquet-format more carefully: when both dictionary and data pages exist, `dictionary_page_offset` points to the dictionary page, and `data_page_offset` points to the *first data page*. So normally they're at different offsets.

**Decision tree**:
- Add `probe_parquet_column_dictionary_page_offset` (Thrift field 14, i64) — returns `option nat`.
- If field 14 is present (column is dictionary-encoded):
  1. Read the dictionary page header at that offset.
  2. Decompress its payload.
  3. Parse as PLAIN_DICTIONARY: list of length-prefixed byte strings (LE u32 + bytes), count = page_header.num_values (which is the number of dictionary entries).
  4. Read the data page header at `data_page_offset` (existing code already does this).
  5. Decompress data page payload.
  6. First byte = bit-width.
  7. Decode hybrid RLE-bit-packed indices (count = page_header.num_values).
  8. Map each index → dictionary[index] string.

### Helper plan

New F* helpers in `Parquet.Footer.fst` after the DLBA section (around line 1780+):

1. `probe_parquet_column_dictionary_page_offset : path -> col_idx -> option nat`
   — mirrors `_data_page_offset` but Thrift field 14 instead of 9.

2. `parse_plain_dictionary_at : payload_hex -> num_values -> Tot (option (list string)) (decreases num_values)`
   — walks `num_values` length-prefixed byte strings (LE u32 length, then ASCII bytes).

3. Hybrid RLE-bit-packed decoder (the wire format of a SPARQL bit-packed run is a varint header `(run_len << 1) | mode`, where mode=0 => RLE run of length `run_len`, mode=1 => bit-packed run of `run_len * 8` values):
   - `decode_hybrid_rle_run : values_hex -> pos -> bit_width -> remaining -> acc -> Tot (option (list nat)) (decreases remaining)`
   - This is the canonical Parquet hybrid; same decode logic should also serve DLBA bit-packing in future cleanup. For now I'll keep DLBA separate to avoid scope creep.

4. `decode_rle_dictionary_indices : payload_hex -> value_count -> Tot (option (list nat))`
   — first byte is bit_width, then loop `decode_hybrid_rle_run` until value_count consumed.

5. `pick_dict_value : list string -> nat -> option string` — list lookup.

6. `map_indices_to_dict : list nat -> list string -> list (option string)` — map.

7. `probe_parquet_column_rle_dictionary_decode_all : path -> col_idx -> option (list (option string))`
   — composes all of the above.

8. `probe_parquet_column_decode_all : path -> col_idx -> option (list (option string))`
   — top-level dispatcher: try DLBA first, then RLE_DICTIONARY. Caller (Parser_BallyhooCOTTAS.ml) switches to this.

### Verification approach

All new functions are total. Use `decreases value_count` / `decreases remaining` patterns matching the existing style. No `--lax`, no `--admit_smt_queries`.

### Smoke test

```bash
./bin/darwin-arm64/factoidal cottas-info \
  tmp/ukparliament/CorpusCOTTAS/ukparliament/v1/data.cottas
```
Expect quad count > 122,880 (column 1+3 now decode, but multi-RG still missing → expect ~122,880 still since first row group is what we're reading; HOWEVER if RLE_DICTIONARY was the failing column, we should now successfully report ALL first-row-group rows with no error).

Actually wait — re-reading the brief: "Parliament COTTAS now loads 122,880 / 3,143,406 quads — only the first row group, and only DLBA columns (subjects + objects). Predicates (col 1) and graph-names (col 3) are RLE_DICTIONARY which our F* decoder doesn't support."

So 122,880 IS what's being loaded today even with the missing-column error? Let me re-check by looking at the runner. Probably what happens: it succeeds for cols 0+2, fails for cols 1+3, but somehow still returns 122,880 quads (maybe a fallback path builds quads from just s+o with empty predicate/graph?). Or the failure is silently caught and only s+o are populated.

Looking at `Parser_BallyhooCOTTAS.ml:413-414`: `failwith` is hard-fail, no catch. So if col 1 fails, the whole load fails, and the 122,880 figure must be from a different code path or the brief is slightly off.

I'll proceed with the plan regardless — RLE_DICTIONARY is a real gap that needs filling, and once fixed:
- If first-RG-only is the bottleneck, we get full first-RG → 122,880 quads loaded successfully.
- If multi-row-group also was needed, that's still gap B.

### Files touched

- `formal/fstar/Parquet.Footer.fst` (additions ~150 LOC)
- `formal/fstar/ocaml-output/Parquet_Footer.ml` (regenerated by patch — but rule #13 forbids hand-edit; I'll add a compatible patch in `ocaml-patches.sh` only if absolutely required, otherwise wait for main-thread `extract`)
- `formal/fstar/ocaml-output/Parser_BallyhooCOTTAS.ml` (call site swap to `decode_all` dispatcher)

Per agent discipline, I should **not** run `build-ocaml.sh extract`. So this commit will be:
1. F* additions + F* verify clean.
2. (Optional) prepare a `Parser_BallyhooCOTTAS.ml` edit that compiles once main-thread does extract.

That means no smoke test from this agent run if the binary needs rebuild. I'll note this in the report and the main thread can run extract+build+smoke.

### Out of scope for this agent

- Multi-row-group iteration (gap B) — separate commit.
- Snappy/GZIP codecs.
- KaRaMeL extraction.
