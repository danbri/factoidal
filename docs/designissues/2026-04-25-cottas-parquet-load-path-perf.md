# COTTAS / Parquet query load-path bottleneck

**Date:** 2026-04-25
**Source:** external profiling by Codex on a 3 143 406-quad parliament
COTTAS artifact (generated from `third_party/data/ukparliament/ukparliament-rdf-2019-07-27.trig`).
**Status:** diagnosis committed; fix deferred.

## Symptoms

- `factoidal --data-cottas <file> -e 'SELECT (COUNT(*) AS ?n) …'`
  pegs CPU at ~99% for over 90 seconds before anything SPARQL-like
  starts.
- macOS `sample` of the live process shows nearly all time is in
  **`load_cottas_dataset` / `load_cache`**, not in the algebra evaluator.

## Hot frames (from the sampled stack)

- `camlBatUTF8__nth_aux_414`
- `camlBatUTF8__next_390`
- `camlParquet_Footer__skip_varint_hex_1927`
- `camlParquet_Footer__decode_varint_hex_1956`

Interpretation: time is spent inside UTF-8 string indexing and inside
Parquet-footer varint probing.

## Critical path

- Glue entry: `formal/fstar/experimental_ocaml_glue/cottas_runtime.sh:248`
- F* footer reader: `formal/fstar/Parquet.Footer.fst:1449`
- Per-cell string fetch routine:
  `formal/fstar/experimental_ocaml_glue/cottas_runtime.sh:269` (loops
  every row) → `:271` (fetches each column per row) →
  `Parquet.Footer.fst:1449` (one requested cell → string).
- Footer-tail probing pattern: `Parquet.Footer.fst:103` and `:111`.

## What is actually happening

1. `load_cache` iterates over **every row** in the Parquet file.
2. For each row, it fetches **all 4 columns individually** (s, p, o, g).
3. Each fetch calls
   `probe_parquet_column_delta_length_byte_array_value_string_at`.
4. That path re-probes Parquet metadata / footer and decodes through
   hex-string helpers on every call.

At 3 143 406 rows × 4 columns = **~12.6 million per-cell fetches** just
to reconstruct the in-memory quad list **before** the query runs.

So the current F* COTTAS runtime is effectively using Parquet as an
"expensive random-access string store", then rebuilding the whole
dataset eagerly. That is the opposite of what a column-store like
Parquet is for.

## The three wastes

1. **Full eager materialisation** of all quads for a one-shot query.
2. **Per-cell Parquet probing** instead of per-column/page decoding.
3. **Heavy hex-string/UTF-8 traversal** inside the footer / runtime layer.

## Recommended fixes (ordered by leverage)

1. **Cache the Parquet footer / metadata once per file.** Currently the
   footer is re-probed on every value lookup.
2. **Decode column payloads once per column/page, not one cell at a time.**
   Parquet stores values column-wise by design; reading one page should
   yield many values at once.
3. **Stop rebuilding the full quad list eagerly for single-query CLI use.**
   Stream pages through the SPARQL evaluator instead. For `COUNT(*)` the
   evaluator should only need row counts per page, not the payloads.
4. **Instrumentation**: add timing logs around `load_cottas_dataset`,
   `load_cache`, and actual query evaluation so regressions are visible
   on the public test-results page.

## Related

- Parser-side analog: `docs/designissues/2026-04-24-turtle-parser-perf-diagnosis.md`
  identified `graph_add` as O(N²) for bulk parse. The
  `graph_add_unchecked` prepend variant was tried (commit `a5cf381`)
  but reverted (`bb6f9d7`) because reversed insertion order broke 19
  rdf-xml round-trip tests. Cache + per-page decode is a safer win.
- `tools/corpus_pipeline.py` (commit `af0ab89`, extended by the user
  with pyoxigraph streaming) shows the ingest path works end-to-end
  on the 331 MB parliament TriG in ~3 min; the slow path is purely the
  query-time COTTAS reload, not the build path.

## Next step

A short instrumentation patch first (wall-clock + RSS at each phase),
then the footer cache, then per-page column decode. Tracked; no
implementation started at this commit.
