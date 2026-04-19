# Ballyhoo binary formats in F\* — status as of 2026-04-19

*Originally titled "HDT in F\* — status"; scope widened 2026-04-19 to cover
the full ballyhoo binary-format stack (HDT, HDTQ, COTTAS, and Parquet) after
a fuller audit found that `Parquet.Footer.fst` is substantial real F\* code
that the first pass missed.*

Audit of the ballyhoo track to answer: **how much of ballyhoo binary-format
parsing is actually done in F\* today?**

Short answer, by format:

- **HDT:** none. F\* fixes the API shape; the binary reader is the external
  `hdtSearch` CLI shelled out via `Unix.open_process_full`.
- **HDTQ:** none. Interface only.
- **COTTAS (as a columnar dataset concept):** interface only — but the
  current COTTAS artifacts are Parquet files, and the Parquet parsing path
  *is* in F\* (next bullet), so in practice COTTAS reads are F\*-verified
  at the metadata + value-decoder layer.
- **Parquet (`Parquet.Footer.fst`, 1453 lines):** **substantial real F\*
  code.** Thrift Compact Protocol, metadata navigation, and the
  DeltaLengthByteArray value decoder are all implemented and verified.
  Only file I/O and Zstd decompression are `assume val`.
- **Surrounding scaffolding:** the N-Quads streaming `Parser.Ballyhoo.fst`
  (201 lines) and the value-level `Parser.BallyhooBloom.fst` (114 lines)
  are fully F\*, but neither is a binary format reader.

### Build-wiring caveat (important — new in this revision)

The six source files (`Parquet.Footer.fst` + five `Parser.Ballyhoo*.fst`)
were cherry-picked onto `claude/main` in commit `8d4fa67`. However, the
cherry-pick did **not** bring across the `build-ocaml.sh` changes that
include them in the extraction list. On `claude/main` today:

- `formal/fstar/build-ocaml.sh`'s `for fst in …` list (~line 71) does not
  mention `Parquet.Footer.fst` or any `Parser.Ballyhoo*.fst`.
- The `COMMON_MODULES` compile list (~line 101) also omits them.
- The pre-extracted `.ml` files in `ocaml-output/` are older than the
  `.fst` sources (verified via `stat -f "%m"`), so even the stale
  extraction is out of sync.
- `SPARQL11.Store.fst` / `SPARQL11_Store.ml` (which wires HDT + COTTAS
  into the SPARQL evaluator) is likewise not in the build list; the
  stale extracted `.ml` references `Parser_BallyhooHDT.*` and
  `Parser_BallyhooCOTTAS.*` but nothing compiles it.

On `origin/codex/ballyhoo-baseline`, all of these *are* in the extraction
and compile lists and do build.

**Implication:** anyone building from `claude/main` today with
`./build-ocaml.sh` gets no ballyhoo / Parquet code — it's dormant source.
To actually use the F\* Parquet parser, the build wiring from the ballyhoo
branch needs to be re-applied. That's a one-commit fix, but currently open.

## The five Ballyhoo F\* modules

| File | Lines | What it is | `assume val`? |
|---|---|---|---|
| `Parser.Ballyhoo.fst` | 201 | **Real F\* code.** Streaming/chunked N-Quads parser: `feed_ballyhoo_nquads_chunk`, carry-buffer line splitting, event emission (`BE_DefaultTriple` / `BE_NamedTriple`), dataset assembly from events. | none |
| `Parser.BallyhooBloom.fst` | 114 | **Real F\* code.** Pure-F\* Bloom filter: `bloom_bits = list bool`, `bloom_empty/insert/might_contain/union`, double-hashing with two modular string hashes. Self-contained, verifies. | none |
| `Parser.BallyhooHDT.fst` | 173 | Types + interface only. Defines `hdt_graph_store`, `hdt_term_ref`, `hdt_bound_tp`, `hdt_tp_row`, `corpus_graph_binding`, plus logic-level helpers `hdt_build_bound_tp` / `hdt_rows_to_triples` / `hdt_search_triples`. | 10 `assume val` (open/close/summary, encode×3, decode×3, search, estimate, predicate_present, named_candidate_graphs) + `assume type hdt_handle` |
| `Parser.BallyhooHDTQ.fst` | 174 | Quad/dataset sibling of HDT: `hdtq_dataset_store`, `hdtq_named_graph_store`, `hdtq_bound_qp`, annotation-mode enum (`HQ_AnnotatedGraphs` / `HQ_AnnotatedTriples`). | 14 `assume val` + `assume type hdtq_handle` |
| `Parser.BallyhooCOTTAS.fst` | 165 | Columnar-quad backend model (`CE_Plain/Dictionary/RLE/Delta`, row groups, per-column summaries). | all ops `assume val` + `assume type cottas_handle` |

All five are listed in `build-ocaml.sh`'s extraction set **on
`origin/codex/ballyhoo-baseline` only**. On `claude/main` they are
orphaned source — see the build-wiring caveat above.
`ocaml-patches.sh` applies `experimental_ocaml_glue/ballyhoo_hdt_runtime.sh`
(and sibling `cottas_runtime.sh`, `parquet_footer_runtime.sh`) after
extraction, but those scripts only do anything if the corresponding
`.ml` files were extracted in the first place.

## The outlier: `Parquet.Footer.fst` (1453 lines)

This is the **most substantial F\* binary-format work in the repo** and
was missed by the first pass of this audit. Three `assume val` at the
top, everything else verified F\*:

| `assume val` | Purpose | Stub |
|---|---|---|
| `parquet_read_tail_hex` (`:27`) | Read last N bytes of file, return as hex string | OCaml `open_in_bin` + `really_input_string` in `parquet_footer_runtime.sh` |
| `parquet_read_range_hex` (`:30`) | Read byte range, return as hex | same |
| `parquet_zstd_decompress_hex` (`:33`) | Zstd-decompress a hex blob | `parquet_zstd_stubs.c` (79 lines) — hex→bytes, `ZSTD_decompress`, bytes→hex |

What the F\* code actually does:

- Hex byte access, LE u32/u24 decoding (`:36-62`, `:158-164`)
- **Thrift Compact Protocol** decoder: varints, zigzag, delta-encoded
  field IDs, struct/list/map skipping (`:120-411`)
- Parquet metadata navigation: `num_rows`, `row_group_count`, column
  chunks, compression codec, data-page offsets, page-header encodings
  (`:413-1061`)
- Zstd frame-header inspection (not decompression itself — that's the
  C stub) — frame descriptor, window descriptor, block type, block
  size (`:885-1165`)
- **DeltaLengthByteArray value decoder**: bit-packed miniblocks, zigzag
  deltas, bit-widths, length-at-index, plus a `probe_parquet_column_
  delta_length_byte_array_value_string_at` that returns the Nth string
  value of a column (`:1194-1449`)

### The "hex string" design choice

The whole parser operates on hex-encoded strings, not raw bytes.
`byte_at_hex` (`:43`) reads two hex nibbles per byte; `parquet_read_*_hex`
returns bytes already hex-encoded; `parquet_zstd_decompress_hex` takes
and returns hex. This sidesteps F\*'s weak `bytes` support — strings are
well-supported in F\*, bytes aren't. Cost is ~2× memory and per-byte ops.
Benefit is that the parser stays inside the verified surface end-to-end.
For a 50-100 KB Parquet footer this is acceptable; for decompressing a
multi-MB data page, the C stub's hex round-trip becomes a real cost
worth revisiting.

### Load-bearing in the COTTAS path

`experimental_ocaml_glue/cottas_runtime.sh:253` calls
`Parquet_Footer.probe_parquet_column_delta_length_byte_array_value_count`
and `:272` calls `probe_parquet_column_delta_length_byte_array_value_string_at`
to extract the four quad columns (subject, predicate, object, graph) from
a Parquet-encoded COTTAS artifact. So for COTTAS datasets **the F\* code
is doing the real structural decode**, not decoration — the OCaml glue
just iterates indices and interns the returned strings into RDF terms.

### Gap to "full Parquet"

What's NOT in F\*:
- Zstd decompression (C stub via libzstd). Unavoidable without a
  verified Zstd in F\*, which is a multi-year project on its own.
- Encodings other than DeltaLengthByteArray: PLAIN, DICTIONARY,
  DELTA_BINARY_PACKED, RLE-bit-packed-hybrid, BYTE_STREAM_SPLIT. A
  Parquet file emitted by any writer other than the specific COTTAS
  producer will likely use at least one of these.
- Parallel row groups. The probes named `_first_row_group_*` or
  hard-code `Z.zero` as the column index for row-count lookups.
- Schema / logical-type handling. The parser reads bytes but doesn't
  know whether a column is `UTF8 STRING`, `ENUM`, `DECIMAL`, etc.
- Predicate pushdown, column statistics, page indexes, bloom filters
  (the Parquet-native bloom, separate from `BallyhooBloom.fst`).

## How the HDT stubs are actually implemented

`formal/fstar/experimental_ocaml_glue/ballyhoo_hdt_runtime.sh` (555 lines) is
**not** F\* — it's a post-extraction patch that rewrites the
`failwith "Not yet implemented"` bodies in the generated
`Parser_BallyhooHDT.ml`. It installs an OCaml module `Ballyhoo_hdt_runtime`
with:

- **Term interning.** Per-artifact-path `Hashtbl`s map subject/predicate/object
  strings ↔ `Z.t` ids. So `hdt_encode_*` / `hdt_decode_*` are a process-local
  dictionary — nothing to do with the HDT file's own dictionary sections.
- **`hdt_search`** shells out: `Unix.open_process_full "hdtSearch <path>"`,
  writes the S/P/O pattern with `?` for unbound slots, reads stdout line by
  line, parses each line with a hand-written tokenizer (`_:bnode`, IRIs,
  `"lit"@lang`, `"lit"^^<dt>`, backslash escapes), re-interns the results.
  **The real HDT binary reader is the external `hdtSearch` binary from
  rdfhdt; the F\* side never touches the bytes.**
- **`hdt_predicate_present`** — if sidecar files `graph.bloom.pred.json` +
  `graph.bloom.pred.bin` exist, it loads `bit_count` / `hash_count` from
  JSON and runs a bloom test. Hashes go through `sha256sum` via
  `Unix.open_process_in` (sic), split into two 16-byte halves for double
  hashing. Falls back to `hdt_estimate` when no sidecar is present.
  Note: this is a *different* bloom from `Parser.BallyhooBloom.fst` —
  it operates on raw bytes from disk, not on the F\* `bloom_bits = list bool`.
  The two do not share code.
- **`hdt_estimate`** is `List.length (hdt_search …)` — not the HDT library's
  index-backed estimate.
- **`hdt_named_candidate_graphs`** is a stub: returns all bindings regardless
  of the predicate hint.

### Implications

- Running the HDT backend requires `hdtSearch` on `$PATH`. This is an
  undeclared runtime dependency not captured anywhere in the F\* boundary.
- Every query pays `fork+exec+parse-stdout`. Anything that is slow because
  of this will not be fixed by F\* work — it's an OCaml-glue shape problem.
- Because decoding returns interned ids assigned on first sight, term ids
  have no stable relationship to HDT's own dictionary ids. If a later pass
  wants to short-circuit on id equality across runs, it can't.
- The sha256 shell-out in the bloom path is particularly rough: every
  `predicate_present` call spawns a subprocess. Anyone running this under
  load should expect it to dominate the profile.

## Stated direction

From `ballyhoo-backlog.md` and `hdtq-native-backend.md`, both unchanged
since the ballyhoo cherry-pick:

- "choose a smallest useful binary subset to parse directly in F\*:
  likely container/header plus graph dictionary metadata first" — **not
  started.**
- "Investigate which HDT metadata and structural checks are suitable for
  F\* binary parsing techniques" — open.
- Parquet-like and SQL backends are anticipated under the same
  `assume val` seam.

## What's actually done in F\*, end-to-end

1. Define the *interface* a verified SPARQL evaluator can rely on (bound
   triple-pattern search, predicate-presence check, named-graph candidate
   pruning) so `SPARQL11.Algebra` can target a real backend instead of
   `list triple`. ✅
2. Define the intended *shape* of HDT / HDTQ / COTTAS artifacts
   (dictionary summary, triples summary, SPO order, annotation mode,
   column encodings, row groups). These are descriptive records, not
   readers. ✅
3. Provide a verified value-level Bloom filter so the F\* side has a
   semantics for the sidecar. ✅ (but the runtime uses a different
   byte-level bloom, so this is documentation, not load-bearing code)
4. Parse the HDT container header. ❌
5. Parse the HDT dictionary section (plain-front-coding, bitmap, etc.). ❌
6. Parse the HDT triples section (bitmap triples, compact indexes). ❌
7. Parse the HDTQ quad annotations. ❌
8. Parse Parquet metadata (Thrift Compact Protocol, footer, row group
   descriptors, column chunk descriptors). ✅ via `Parquet.Footer.fst`.
9. Parse Parquet DeltaLengthByteArray string columns. ✅ via
   `Parquet.Footer.fst`.
10. Parse Parquet PLAIN / DICTIONARY / DELTA_BINARY_PACKED / RLE etc.
    encodings. ❌
11. Zstd decompression. ❌ (C stub via libzstd; no verified Zstd exists.)

## Not to be confused with

- **The quoted earlier assessment** ("F\*-level interface to HDT, but the
  actual binary-format reader is native OCaml glue rather than extracted
  F\* code") was correct at the time and remains correct today. This
  note exists so future sessions don't re-do that audit.
- **`Parser.Ballyhoo.fst`** itself is a real F\* streaming N-Quads parser
  and is not part of the HDT gap — it's a separate experimental text-parser
  ingestion track.

## Related docs

- [`hdt-backed-sparql-subset.md`](hdt-backed-sparql-subset.md) — what SPARQL
  features work over the (stubbed) HDT backend
- [`hdtq-native-backend.md`](hdtq-native-backend.md) — HDTQ design intent
- [`cottas-native-backend.md`](cottas-native-backend.md) — COTTAS design intent
- [`ballyhoo-backlog.md`](ballyhoo-backlog.md) — overall ballyhoo track
- [`ballyhoo-bloom-fstar.md`](ballyhoo-bloom-fstar.md) — the verified
  F\* bloom filter (not wired to the HDT runtime glue; see above)
- [`sparql-store-backend.md`](sparql-store-backend.md) — the storage/query
  boundary the HDT interface is meant to plug into
- `formal/fstar/Parquet.Footer.fst` — the real F\* Parquet metadata +
  DeltaLengthByteArray value decoder (no standalone design doc yet)
- [`2026-04-19-cottas-parquet-wiring-plan.md`](2026-04-19-cottas-parquet-wiring-plan.md)
  — plan to restore the build wiring on `claude/main` and extend to
  js_of_ocaml + wasm_of_ocaml
