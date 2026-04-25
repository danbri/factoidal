# Issue #98 plan — RLE_DICTIONARY columns + multi-row-group

**Filed:** 2026-04-25T09:53Z. Follow-up to #97 (closed by `71f7e6b` —
per-miniblock bit_width in DELTA_LENGTH_BYTE_ARRAY).

## What works after #97

Yod3's fix made `build_dlba_length_list` boundary-aware. Smoke test:

```
$ ./bin/darwin-arm64/factoidal cottas-info \
    third_party/data/ukparliament/cottas/<corpus>/...
```

Now decodes columns 0 (subjects) and 2 (objects) — both
DELTA_LENGTH_BYTE_ARRAY — in ~4.3s, then fails:

```
Could not bulk-decode COTTAS column 3
```

## What's still missing

### Gap A — RLE_DICTIONARY decoder for cols 1 + 3

pycottas writes predicates (col 1) and graph-names (col 3) as
RLE_DICTIONARY because their cardinality is small and repetition is
heavy. Gap A is the primary blocker for parliament.

**Encoding wire format** (Parquet 2.x):

1. Dictionary page (header type = `DICTIONARY_PAGE`, encoding =
   `PLAIN_DICTIONARY`):
   - Sequence of length-prefixed byte strings, length is little-endian
     u32, value bytes follow.
   - Number of entries = `dictionary_page_header.num_values`.
2. Data page (header type = `DATA_PAGE`, encoding = `RLE_DICTIONARY`,
   sometimes also written as `PLAIN_DICTIONARY` for the data page —
   they're synonymous in v2 contexts):
   - First byte: bit-width of dictionary indices (≤ 5 bits typically
     for small dictionaries).
   - Remaining bytes: hybrid RLE-bit-packed-encoded indices, MSB
     framing identical to the bit-width header used in DLBA.

**F\* sketch (target file: `formal/fstar/Parquet.Footer.fst`):**

```fstar
// Parse the dictionary page payload into a list of byte strings.
// The `num_values` is read from the dictionary-page header.
val parse_plain_dictionary
  : (payload_hex : string)
  -> (num_values : nat)
  -> Tot (option (list string))

// Decode RLE_DICTIONARY data page: read bit-width byte, then decode
// `value_count` indices via the same hybrid RLE-bit-packed scheme
// already used by DLBA bit_widths.
val decode_rle_dictionary_indices
  : (payload_hex : string)
  -> (value_count : nat)
  -> Tot (option (list nat))

// Compose: produce the values list for an RLE_DICTIONARY column.
val probe_parquet_column_rle_dictionary_values
  : (path : string)
  -> (col_index : nat)
  -> Tot (option (list string))
```

Helper to reuse: the bit-packed index decoder shares logic with
`build_dlba_length_list`'s `widths_byte_at` pattern. Lift that into a
shared `unpack_bit_packed_uints : hex -> bit_width -> count -> list nat`
helper and use it for both.

### Gap B — multi-row-group iteration

Parliament Parquet has 25 row groups (`first row_group` only sees
122,880 of 3,143,406 rows). Current `cottas_info` uses
`probe_parquet_first_row_group_*` helpers — single-page only.

**F\* sketch:**

```fstar
// Existing: `probe_parquet_row_group_count` returns total row-group count.

val probe_parquet_column_in_row_group
  : (path : string)
  -> (rg_index : nat)
  -> (col_index : nat)
  -> Tot (option column_chunk_metadata)

val probe_parquet_column_all_row_groups
  : (path : string)
  -> (col_index : nat)
  -> Tot (option (list string))  // concatenated across row groups
```

The existing footer parser already walks row groups — the helpers just
need to take a row-group index instead of hard-coding 0.

## Acceptance

```
$ ./bin/darwin-arm64/factoidal serve --port 3030 \
    --data-cottas third_party/data/ukparliament/cottas/<corpus>
$ curl -G http://localhost:3030/sparql \
    --data-urlencode 'query=SELECT (COUNT(*) AS ?n) WHERE { ?s ?p ?o }'
```

Returns `?n = 3143406` in &lt;5s.

## Constraints (per CLAUDE.md)

- F\*-first; new decoders go in `Parquet.Footer.fst`.
- No `--lax`, no `--admit_smt_queries`. All bulk-decode helpers must
  verify with `Tot (decreases <fuel-or-nat>)`.
- No semantic logic in patches; patch infra wires `assume val` stubs
  and I/O glue only.

## Out-of-scope for this issue

- KaRaMeL C/WASM extraction of the new decoders (separate issue).
- pycottas-side encoding tweaks.
- Compression codecs other than ZSTD (Snappy / GZIP — also separate).

## Estimated agent budget

- **Reading**: ~30 min (dictionary page format + bit-packing wire layout
  + existing F\* unpack patterns).
- **F\***: ~80 LoC for the dictionary decoder, ~40 LoC for multi-row-group
  iteration, ~20 LoC of caller plumbing in `factoidal_cli.ml` /
  `cottas_bridge.py` consumers.
- **Verification**: should be straightforward; reuse `decreases` pattern
  from DLBA decoders.
- **Smoke**: parliament COTTAS load + `COUNT(*)` &lt;5s.

## Coordination

Issue #98 is P1 per user's priority lattice (binary parquet deploy after
today's P0). Two agents could split A and B if scope ramps. Single
agent recommended — they overlap heavily on the bit-pack helper.
