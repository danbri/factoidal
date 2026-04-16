# Backend Roadmap

## Current State

- COTTAS artifacts are generated with upstream `pycottas` and verified upstream.
- Direct Parquet probing now exists as a verified F* module over real `.cottas` files.
- The verified Parquet path currently reads:
  - footer magic and metadata length
  - `FileMetaData.num_rows`
  - `FileMetaData.row_groups` list count
  - all four quad `ColumnChunk` names, offsets, codecs, and sizes
  - `DATA_PAGE` header fields for the first page of each quad column
  - Zstd frame structure through the first compressed block
  - decompressed first-page payload bytes via a thin native Zstd runtime primitive
  - the `DELTA_LENGTH_BYTE_ARRAY` value-stream boundary and header fields:
    - first level-section length
    - value-stream offset
    - delta block size
    - miniblock count
    - value count
    - first decoded length
    - first min-delta
    - first miniblock bit width
    - the full first-block decoded length stream for the sample quad columns
  - the first-block reconstructed string values for the sample quad columns, including `DEFAULT`
- `factoidal --data-cottas ... --query ...` now runs against real `data.cottas` without `data.nq`, using a native COTTAS runtime that reconstructs values from the verified Parquet reader and serves the existing SPARQL evaluator.
  - printable metadata strings for debugging
- `data.factbin` exists as older scaffolding, but it is not the target architecture.
- HDT query support is native at query time inside Factoidal's OCaml runtime, but HDT artifact generation still depends on an external `rdf2hdt` tool.

## Next Work

- Keep extending the verified Parquet compact-protocol reader over real `data.cottas` bytes:
  - decode `schema` list count and per-column schema entries
  - decode `row_groups` entries, then `ColumnChunk` offsets and encodings
  - decode `key_value_metadata` and `created_by` structurally instead of string-mining
  - decode per-column physical/logical types and nullability
- Use those decoded `ColumnChunk` offsets to read actual Parquet data pages directly from F*/extracted OCaml.
- Extend the verified page-body reader from header parsing into value decoding:
  - generalize reconstructed `DELTA_LENGTH_BYTE_ARRAY` values beyond the current first-block/sample path
  - handle multiple pages and row groups natively rather than only the currently exercised first-page path
  - then replace the current in-memory reconstructed quad scan with direct page-aware scans
- Define the first native COTTAS scan path over real Parquet columns:
  - full-column scan for one bound/unbound quad pattern
  - then filtered joins
  - then graph-aware scans
- Add backend parity coverage that compares plain N-Quads, direct-Parquet COTTAS, and HDT answers across the same query corpus.
- Add larger synthetic datasets and query corpora for compatibility and performance work.
- Add fuzz/property tests around Parquet metadata decoding and SPARQL parity.
- Decide the eventual fast path for "in memory":
  - memory-mapped Parquet files
  - cached decoded column metadata
  - optional fully resident column pages
- Replace the external HDT build dependency if possible:
  - either a native HDT writer in Factoidal,
  - or a checked-in bridge/runtime path that does not require system `rdf2hdt`.
- Add result-parity tests that compare output rows after stable ordering, not just pass/fail spot checks.
- Investigate backend-specific planning hooks so COTTAS and HDT can exploit predicate presence and cardinality estimates more aggressively.

## Notes

- The only target COTTAS path is direct native reading of real `data.cottas` Parquet files from F*/extracted OCaml.
- The current native Zstd step is intentionally narrow runtime support for decompression only; the Parquet and value-decoding semantics stay in F*.
- `data.factbin` is not a substitute for that and should not be extended further.
- Any claim of COTTAS speedup should come after benchmark data on realistic datasets and after real direct-Parquet scans exist.
- HDT is closer to native query support than COTTAS today, but still not fully self-hosted end-to-end because artifact generation depends on external tooling.
