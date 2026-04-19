# HDT in F\* — status as of 2026-04-19

Audit of the ballyhoo track to answer one question: **how much of HDT binary
parsing is actually done in F\* today?**

Short answer: **none.** The F\* layer fixes the HDT API shape; the binary
reading is still delegated to the external `hdtSearch` CLI via
`Unix.open_process_full`. Surrounding scaffolding (streaming N-Quads parser,
pure-F\* Bloom filter, dataset / columnar backend types) does exist.

This is the same on `claude/main` and on `origin/codex/ballyhoo-baseline` —
the five `Parser.Ballyhoo*.fst` files and the runtime glue were cherry-picked
(commit `8d4fa67`) and are byte-identical to the ballyhoo branch.

## The five Ballyhoo F\* modules

| File | Lines | What it is | `assume val`? |
|---|---|---|---|
| `Parser.Ballyhoo.fst` | 201 | **Real F\* code.** Streaming/chunked N-Quads parser: `feed_ballyhoo_nquads_chunk`, carry-buffer line splitting, event emission (`BE_DefaultTriple` / `BE_NamedTriple`), dataset assembly from events. | none |
| `Parser.BallyhooBloom.fst` | 114 | **Real F\* code.** Pure-F\* Bloom filter: `bloom_bits = list bool`, `bloom_empty/insert/might_contain/union`, double-hashing with two modular string hashes. Self-contained, verifies. | none |
| `Parser.BallyhooHDT.fst` | 173 | Types + interface only. Defines `hdt_graph_store`, `hdt_term_ref`, `hdt_bound_tp`, `hdt_tp_row`, `corpus_graph_binding`, plus logic-level helpers `hdt_build_bound_tp` / `hdt_rows_to_triples` / `hdt_search_triples`. | 10 `assume val` (open/close/summary, encode×3, decode×3, search, estimate, predicate_present, named_candidate_graphs) + `assume type hdt_handle` |
| `Parser.BallyhooHDTQ.fst` | 174 | Quad/dataset sibling of HDT: `hdtq_dataset_store`, `hdtq_named_graph_store`, `hdtq_bound_qp`, annotation-mode enum (`HQ_AnnotatedGraphs` / `HQ_AnnotatedTriples`). | 14 `assume val` + `assume type hdtq_handle` |
| `Parser.BallyhooCOTTAS.fst` | 165 | Columnar-quad backend model (`CE_Plain/Dictionary/RLE/Delta`, row groups, per-column summaries). | all ops `assume val` + `assume type cottas_handle` |

All five are listed in `build-ocaml.sh`'s extraction set.
`ocaml-patches.sh` applies `experimental_ocaml_glue/ballyhoo_hdt_runtime.sh`
(and sibling `cottas_runtime.sh`, `parquet_footer_runtime.sh`) after extraction.

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

## What's actually done in F\*, end-to-end, for HDT

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
8. Parse COTTAS / Parquet row groups. ❌ (Parquet has a footer runtime
   glue script too, same story as HDT)

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
