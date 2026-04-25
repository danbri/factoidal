# 2026-04-25 — Parquet DELTA_LENGTH_BYTE_ARRAY per-miniblock bit_width fix (#97)

## Problem

`build_dlba_length_list` in `formal/fstar/Parquet.Footer.fst` (and the
single-cell `accumulate_lengths` path inside
`probe_parquet_column_delta_length_byte_array_length_at`) reads **one**
`bit_width` byte from the values stream and uses it for **every** value on
the page.

Per the Parquet DELTA_LENGTH_BYTE_ARRAY (delta-binary-packed) format:

* Each block has its own `min_delta` (varint) followed by an array of
  `miniblocks` bytes — one `bit_width` per miniblock.
* Each miniblock holds `block_size / miniblocks` packed deltas at that
  miniblock's width.
* When the next block starts, a fresh `min_delta` and a new `bit_widths`
  array follow.

Because the writer in practice emits a single block per page (Arrow / parquet
default), the visible bug is that the **second miniblock onward uses the
wrong width** — and because the first miniblock's width is usually larger
than later ones (where deltas are smaller), the decoded `current_len` goes
strongly negative one value past the first miniblock boundary:

| Corpus | block_size | miniblocks | bit_width[0] | values/miniblock | First failing delta_index |
|--------|-----------:|-----------:|-------------:|-----------------:|--------------------------:|
| Parliament 64 MB | 2048 | 8 | 7 | 256 | **258** |
| protein__protein1 (1.2 MB) | 2048 | 8 | 2 | 256 | **2080** (= block_size + 32) |

(The second case is wider — 8 miniblocks at width 2 sums correctly through
one full block, then misaligns at the next block's `min_delta` byte.)

## Plan

1. In `Parquet.Footer.fst`, refactor `build_dlba_length_list` so it knows
   where it is in the (block, miniblock, value) hierarchy and reads each
   miniblock's width from a new helper that resolves `(block, miniblock_idx)
   -> bit_width` from the page header bytes.
2. Add a per-block re-read of `min_delta` + the `miniblocks` width bytes at
   each block boundary (every `block_size` values).
3. Update `probe_parquet_column_delta_length_byte_array_page_cache` to pass
   `block_size`, `miniblocks` (and therefore `values_per_miniblock`) into
   `build_dlba_length_list` instead of a flat `bit_width`.
4. Mirror the fix into `accumulate_lengths` so the per-cell path is also
   correct (the bulk path is the hot path now, but the per-cell path is
   still reachable).
5. Re-extract + recompile, run smoke + W3C regression.

## Out of scope

* The legacy `_value_string_at` per-row API remains O(N²) regardless of this
  fix — that's a perf concern, not a correctness one. Bug 1 from
  `2026-04-25-cottas-http-hang-diagnosis.md` is already addressed by patch
  103.

## Verify discipline

No `--lax`. If verification needs a localized SMT-admit, narrow it to a
single `#push-options` block. Goal: keep `Tot` everywhere with `decreases`
on `remaining`.

## Acceptance

* `factoidal --data-cottas /tmp/ukpar_corpus/.../data.cottas --count`
  returns 3 143 406 in single-digit seconds.
* `factoidal-http --data-cottas ...` binds and ASK answers.
* `w3c_runner` regression unchanged (1031/1031 RDF + SPARQL totals).
