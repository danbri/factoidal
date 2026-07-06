# Disk-backed RDF++/SPARQL DB — performance & memory review

**Date:** 2026-07-05.
**Author context:** measurement + prose review only. No code, `.fst`, or
build changes were made. All fresh measurements use the **committed**
binary `git show HEAD:bin/linux-x86_64/factoidal` (HEAD
`b4249260`), extracted to a scratch dir, because several working-tree
`bin/linux-x86_64/*` files are locally modified mid-rebuild by a sibling
session (notably `factoidal-dump-nq.byte`, which SIGABRTs on a missing
`dllnums.so` in this tree). Peak RSS is measured with a
`resource.getrusage(RUSAGE_CHILDREN).ru_maxrss` wrapper (no
`/usr/bin/time` in this sandbox); wall time is process wall-clock. Host:
4-core Linux sandbox. Every ad-hoc run was capped at `timeout` ≤ 600 s
per anti-pattern #17 and logged to a scratch dir.

**Corpus caveat (stated plainly).** The full 3,143,406-quad UK Parliament
COTTAS store is **not present in this sandbox** — the deploy doc
([`docs/deploy/flyio.md`](../deploy/flyio.md):19-28) locates it only on
the owner's laptop at `tmp/ukparliament/CorpusCOTTAS/ukparliament/v1/`
(~325 MiB bundle). It could not be fetched. Fresh measurements therefore
use the largest local corpus, the vendored Wikidata life-sci KGX subset
(`examples/wikidata/subsets/lifesci-kgx/data/gene.ttl`, 888,949 triples,
17 MB Turtle), plus small fixtures. Parliament-scale numbers are **cited**
from the project's own recorded measurements and labelled as such.

---

## 1. Current architecture inventory (read, not guessed)

### 1.1 The on-disk format: COTTAS-on-Parquet v1

Contract: [`docs/cottas-format-v1.md`](../cottas-format-v1.md). A `.cottas`
file is an **Apache Parquet** file with exactly four `BYTE_ARRAY`/`STRING`
columns `s, p, o, g` (in that order), one row per quad, ZSTD-compressed.
Each cell is an N-Quads *token* for one term (`<iri>`, `_:bnode`,
`"lex"@lang`, `"lex"^^<dt>`); the default graph is the literal sentinel
`DEFAULT` in column `g` (§6 of the spec). Row order is producer-chosen and
semantically free — the `index=spog` KV key is advisory (§3).

- **Row groups:** DuckDB default 122,880 rows/group (parliament: 26
  groups; my gene build: 8 groups). Readers must iterate all groups.
- **Encodings (measured, this session, via duckdb `parquet_metadata`):**
  DuckDB does **not** emit a uniform encoding. On my gene build the `g`
  column is `RLE_DICTIONARY` in every row group (constant `DEFAULT`,
  56→74 bytes/group), `p` is `RLE_DICTIONARY` in every group, and `s`/`o`
  are `DELTA_LENGTH_BYTE_ARRAY` (DLBA) **only in row group 0** — groups
  1-7 switch `s`/`o` to `RLE_DICTIONARY` adaptively. The format doc's
  "parliament uses DLBA for all four columns" is the *exception*, not the
  rule; RLE_DICTIONARY is DuckDB's default for repetitive columns.
- **No delta/zone-map/min-max stats are used by the reader.** Parquet
  column statistics and page indexes are OPTIONAL and treated as advisory
  (spec §2); the reader does not consult min/max for row-group pruning.

### 1.2 Companion sidecar / prune layer (built outside the Parquet file)

Around the four-column Parquet file the project layers *sidecars* that
prune at row-group granularity (none change what is stored):

- **Per-column presence bitmaps** — Yod6 (predicate present-in-rg),
  Tet3 (subject/object present-in-rg): `RDF.CottasStore.PresenceBitmap.fst`.
- **Compound (p,o) presence bitmap** — `CompoundPresenceBitmap.fst`
  (needed because per-column presence saturates: parliament has
  60-100k distinct (p,o) pairs per row group).
- **Per-rg predicate offset index (Lamed3)** — `data.cottas.p.offsets`
  (magic `COTO`), giving exact row positions per (row-group, predicate),
  so bound-predicate queries skip decoding the whole predicate column.
  Spec'd partly in `RDF.Store.Columnar.OffsetIndex.fst`.
- **Per-graph predicate Bloom sidecars** (F\* Bloom core), page cache
  (`RDF.CottasStore.PageCache.fst`), lazy dictionaries (`LazyDict*.fst`).

Critically, **none of these sidecars are produced by the import
pipeline** — a fresh `cottas-import` writes only `data.cottas` +
`data.nq` + `data.factbin`. Sidecars are built lazily at server open time
by the OCaml runtime layer (see §1.4), so a cold artifact carries no
compact index at all.

### 1.3 What is F\*-verified vs OCaml glue (iron rule #11 status)

The dividing line runs through the read path:

- **Verified F\* (the substantial part):**
  [`Parquet.Footer.fst`](../../formal/fstar/Parquet.Footer.fst) (~2,200
  lines) — Thrift compact-protocol footer decode, row-group navigation,
  the DLBA miniblock decoder (per-miniblock `bit_width`, #97) and the
  RLE_DICTIONARY decoder (#98). The presence-bitmap, page-cache,
  offset-index, and compound-bitmap modules are F\* spec. Parquet bytes
  are handled as **hex-encoded strings** (F\* has weak native `bytes`),
  costing ~2× per-byte memory.
- **`assume val` I/O only (rule-#11-acceptable):** file `map_file`/read,
  clock, and the ZSTD block decompress (79-line C stub over libzstd).
- **Unverified OCaml shadow logic (the debt):**
  `experimental_ocaml_glue/cottas_ondisk_runtime.sh` — **718 lines**
  (per #118 / the retirement plan) that override the extracted F\* bodies
  with Hashtbl-backed search/estimate/decode plus the fast prune cascade
  (Yod6→Tet3→Lamed3→presence). This is the single largest rule-#11
  violation and the reason `RDF.CottasStore.fst` is called "decorative."
  Eight further shadow modules exist for the query-planning path
  (Yod6/Tet3/Lamed3/Mem5/Pe5/Bet7/Tav5/Heth3), all currently OCaml glue,
  each with an F\* recovery target in
  [`2026-05-07-query-planning-fstar-recovery.md`](2026-05-07-query-planning-fstar-recovery.md)
  (Phases 0-9, ~3-4 weeks). The `#118` first slice
  ([`2026-07-03-issue-118-first-slice-plan.md`](2026-07-03-issue-118-first-slice-plan.md))
  narrows the immediate target to 10 sed substitutions of real F\* `Tot`
  bodies.

Consequence for this review: the fast on-disk path that serves parliament
is the **OCaml override**, not the extracted F\* code. The extracted F\*
path exists but is (a) 2-3 orders of magnitude slower on parliament
(#118, asserted) and (b) as measured below, unable to decode
default-encoded artifacts.

### 1.4 HDT and other backends

- **HDT is not F\*.** `Parser.BallyhooHDT.fst` (173 lines) is types +
  10 `assume val`; the real reader shells out to the external `hdtSearch`
  CLI via `ballyhoo_hdt_runtime.sh` (555 lines of OCaml), which even
  `sha256sum`-shells per `predicate_present` for a Bloom check
  ([`2026-04-19-hdt-fstar-status.md`](2026-04-19-hdt-fstar-status.md);
  retirement plan #253). HDTQ/COTTAS Ballyhoo modules are likewise
  interface-only.
- **In-memory store** is the default. Indexing is patch-97: three
  per-graph single-position Hashtbls (S/P/O), smallest-bucket-wins, an
  OCaml post-extraction patch (`RDF.Indexed.fst` is the F\* sibling). No
  compound indexes, no named-graph index, no selectivity BGP reorder
  ([`2026-04-24-indexing-audit.md`](2026-04-24-indexing-audit.md)).

### 1.5 Durability / UPDATE

There is **no durable on-disk UPDATE path today**. `.cottas` files are
write-once, produced by pycottas via `tools/corpus_pipeline.py` (the
project has no F\*-side COTTAS *writer*). INSERT/DELETE against a
persistent store is Phase 4 of the #100 umbrella
("`RDF.Persistent.fst`, page format, on-disk term dictionary,
`pwrite`") — not started. The 2026-04-25 cited issue numbers #22/#24 in
the tasking map to unrelated old PRs; the live umbrella is **#100** (P0
real on-disk indexed backend), with RLE_DICTIONARY+multi-rg being the
closed **#98** and load-perf being **#99**.

---

## 2. Measurements

All fresh numbers: HEAD committed `factoidal`, 2026-07-05, this sandbox.
Logs in the session scratch dir (`perf-review/m-*.log`).

### 2.a Load / convert (N-Quads → COTTAS build)

| Input | Triples/quads | Build wall | Peak RSS | `data.cottas` size | bytes/quad (cottas) | bytes/quad (raw .nq) |
|---|---:|---:|---:|---:|---:|---:|
| `medication.ttl` | 6,780 | 1.11 s | 148 MiB | 15,100 B | **2.23** | 129.7 |
| `gene.ttl` | 888,949 | 32.3 s | **1,732 MiB** | 1,012,509 B | **1.14** | 130.5 |

Pipeline: `tools/corpus_pipeline.py materialize-nq-cottas-corpus
--parser python` (pyoxigraph front end; the `factoidal` front end aborts
in this tree, see caveat). Findings:

- **Compactness is the format's main win:** gene serializes to
  **1.14 bytes/quad**, a **114× reduction** vs raw N-Quads, because ZSTD +
  RLE_DICTIONARY collapse the constant `g` column, the low-cardinality
  `p` column, and the repetitive `s`/`o` runs.
- **Build is O(store) in RAM and time:** 1,732 MiB peak for 888,949 quads
  — the pyoxigraph parse + DuckDB conversion buffers the whole dataset.
  This will not scale to corpora larger than RAM without a streaming
  importer.
- **No compact sidecars are emitted at build time** (§1.2): the artifact
  ships `data.cottas` + `data.nq` + `data.factbin` only.

### 2.b On-disk query latency — **could not measure; the reader fails**

Every attempt to query a freshly-built COTTAS store on the on-disk path
(`--data-cottas`) failed, in two distinct modes:

| Store | Rows | `g`/`p` encoding | On-disk `COUNT(*)` result |
|---|---:|---|---|
| medication (built here) | 6,780 | `g`=RLE_DICT | **hard error** `could not decode column 3` |
| gene (built here) | 888,949 | `g`,`p`=RLE_DICT (8 rg) | **hard error** `could not decode column 3` |
| g21 (prior session, named graphs) | 818 | `p`,`g`=RLE_DICT | **silent `COUNT(*) = 0`** (true 818) |

Root cause: the committed HEAD reader cannot decode **RLE_DICTIONARY**
columns, which — as measured in §1.1 — is DuckDB/pycottas's *default*
encoding for the constant graph column and low-cardinality predicate
column. The g21 case is worse than the error case: it is a **silent wrong
answer** (0 instead of 818), the exact soundness failure class the #118
plan warns about. Note #98 ("RLE_DICTIONARY + multi-row-group") is marked
*closed/completed* and the format spec cites an F\* RLE_DICTIONARY decoder
at `Parquet.Footer.fst:1786-2167`; the HDT-status doc separately warns
that `Parquet.Footer.fst` was cherry-picked but **not wired into
`build-ocaml.sh`** on some branches, so the committed binary may not
carry the #98 decoder. Either way, the reproducible fact stands: **the
shipped on-disk reader serves only the all-DLBA parliament fixture, and
fails or lies on default-encoded corpora.** This is the dominant blocker
for "scalable disk-backed."

On-disk latency on the reference corpus is therefore taken from the
project's own records (§2.e).

### 2.c Memory scaling — anything O(store) that should be O(result)?

Yes — the in-memory query path is O(store), not O(result):

| Query on gene.ttl (888,949 triples) | Result rows | Wall | Peak RSS |
|---|---:|---:|---:|
| streaming `count FILE` (parse only) | — (1 int) | 6.62 s | **44 MiB** |
| `SELECT (COUNT(*)) …` (materialized) | 1 | 27.2 s | **731 MiB** |
| point lookup `wd:Q287043 ?p ?o` | 1 | 26.7 s | **731 MiB** |

The streaming parse-count path is bounded (44 MiB for 17 MB of Turtle).
The **query** path materializes the entire graph into the in-memory
indexed store first: a one-row aggregate and a one-row point lookup both
cost **731 MiB** (~862 bytes/triple) — RSS is a function of store size,
not answer size. This is the same wall the perf docs record as ~1.2 KB
RAM/quad; at parliament's 3.14M quads it projects to ~4 GB, above the
2 GB Fly VM (`performance.md`:107-118). Nothing in the CLI query path
pushes point-lookup or aggregation through a bounded store scan.

### 2.d In-memory vs on-disk baseline

The intended comparison (same query, both paths) is not possible because
the on-disk path fails on the buildable corpora (§2.b). What can be
stated: in-memory load+query of gene is 27 s / 731 MiB and answers
correctly; the on-disk path returns in 0.05 s but with an error or a
wrong count. So today the on-disk path offers no *usable* win over
in-memory for freshly-built corpora — the win only materialises on the
hand-blessed all-DLBA parliament artifact via the OCaml override.

### 2.e Cited baselines (not re-measured)

- **Parse throughput** (`performance.md`, 2026-07-03, committed linux
  binary): ~104k triples/s through 1M; 500 MB Turtle (10,117,857
  triples) streaming-count in 195 s at 971 MB RSS; materialized
  load+query ~1 KB/triple → ~10 GB extrapolated for 500 MB.
- **UK Parliament query bench** (`ukparliament-bench-modern.json`,
  2026-04-25, full 3.14M-quad corpus over on-disk COTTAS, laptop
  endpoint): 24 queries → **11 OK / 11 error / 2 timeout**, avg 3,598 ms,
  total 86.4 s, slowest a 30 s timeout. Even on the reference corpus,
  under half the sample queries completed successfully at that date.
- **Lamed3 predicate offset index** (2026-04-26, parliament 3.14M):
  offsets file 12.0 MB; first boot (build+mmap) 28.98 s (build 24.61 s),
  warm mmap boot 4.11 s; `?s rdf:type ?o LIMIT 5` = **5.2 s warm**
  (target <200 ms, missed); LIMIT 1000 = 30 s timeout (148/1000 rows,
  9/26 rgs walked); rare predicate `geosparql:asWKT LIMIT 5` = **9 ms**
  (presence prune short-circuits). W3C suite unchanged.
- **COTTAS load perf** (#99): 1,600 quads/s to open the pre-built
  parliament artifact vs 57,000 quads/s to re-parse the source TriG —
  the pre-built path was 35× *slower* than re-parsing (the specific
  string-interning cost that #99 targets).

---

## 3. Gap analysis vs "scalable disk-backed"

Ordered by how hard they block the goal today:

1. **The on-disk reader is not robust to producer encoding (measured,
   §2.b).** DuckDB emits RLE_DICTIONARY by default; the shipped reader
   fails or silently under-counts. Until this is fixed and regression-
   pinned against default-encoded artifacts, "disk-backed" works only for
   one blessed file. This gates everything else.
2. **Memory is O(store) on both build and query (measured, §2.a/§2.c).**
   Build buffers the whole corpus (1.7 GB for 888k quads); query
   materializes the whole store (731 MiB for a 1-row answer). Dataset >
   RAM does not work in either phase. This is the #100 acceptance
   criterion ("memory bounded by working-set, not corpus") and it is
   unmet.
3. **The fast on-disk path is unverified OCaml (§1.3).** The 718-line
   `cottas_ondisk_runtime.sh` is load-bearing; the extracted F\* path is
   too slow to replace it (#118). So the project's verified-engine claim carries
   the rule-#11 qualifier, and none of the on-disk hot path extracts to
   C/WASM.
4. **Prune sidecars are ineffective at current row order (cited).** The
   Lamed3 offset index moves `?s rdf:type ?o LIMIT 5` only 6 s→5.2 s
   because rows are in SPOG order — a frequent predicate appears in every
   row group, so per-rg pruning kills almost nothing
   ([`2026-07-03-shapes-canon-storage-strategies.md`](2026-07-03-shapes-canon-storage-strategies.md)
   §1.3). The prune machinery exists but is starved of selectivity by row
   placement.
5. **No index is built at import (§1.2, §2.a).** Sidecars are lazily
   built at first server open (part of the 24.6 s Lamed3 build cost, the
   28.98 s first-boot), competing with query latency; a cold VM pays it
   every restart unless `min_machines_running=1`.
6. **No durable UPDATE / crash safety / concurrency story (§1.5).**
   Write-once files; INSERT/DELETE persistence is #100 Phase 4
   (unstarted); process-global Hashtbl handles are hit from multiple HTTP
   threads without Mutexes (latent bug flagged in #253/#118).

---

## 4. Compact-representation options (grounded in the measurements)

### 4.a COTTAS / Parquet improvements

The format is already compact (1.14 bytes/quad, §2.a); the leverage is in
the **read path and the ordering**, not the container:

- **Fix + pin RLE_DICTIONARY multi-row-group decode** (blocks everything,
  §2.b). Confirm whether `Parquet.Footer.fst`'s #98 decoder is wired into
  the shipped build; add a regression corpus that is *default-encoded*
  (RLE_DICT on `g`/`p`, adaptive on `s`/`o`), not just the all-DLBA
  fixture.
- **Row-group min/max zone maps / statistics-based pruning.** Parquet
  already can carry per-column-chunk min/max; the reader ignores them
  (§1.1). For a bound-object or range pattern, min/max lets whole row
  groups be skipped without decoding — a near-free selectivity source the
  DLBA/RLE sidecars approximate more expensively. This is an F\* reader
  change in `Parquet.Footer.fst` (parse the `Statistics` thrift struct)
  plus a planner consult.
- **Characteristic-set / subject row clustering (E1 in the shapes-canon
  doc).** Re-sort rows by `(CS(s), s, p, o)` at *write* time (producer-
  side Python, **zero F\* change, v1-conformant** since order is free).
  Measured lever: the existing prune cascade goes from
  "kills nothing" to "kills most row groups" for bound-predicate patterns,
  and RLE runs lengthen (better compression). This is the cheapest large
  win and needs no format change.
- **Dictionary-ID COTTAS v2** (shapes-canon §4.3, #118 second slice):
  replace repeated string cells with u32 IDs + a `.dict` companion —
  `RDF.CottasStore.OnDiskIndex.fst` already byte-specifies
  `dict_encode_token`/`dict_decode_token`. Cuts both size and decode cost;
  clustering makes ID runs longer. This is a v2 design doc, sequenced
  behind the reader fix and E1.
- **A second permutation file** (POSG sibling) for bound-`p`/bound-`o`
  scans — deferred until E1's prune numbers are known (2× storage, planner
  work).

### 4.b HDT (Header-Dictionary-Triples)

What HDT actually is, and how it could enter this codebase under the iron
rules:

- **Format.** HDT (Fernández et al., JWS 2013) has three components.
  *Header*: metadata. *Dictionary*: four sections (subjects, predicates,
  objects, shared subject∩object), each **front-coded** (incremental
  prefix compression over sorted terms) — this is the compactness lever
  and it is mmap-friendly and random-access via a bit-vector of section
  offsets. *Triples*: **Bitmap-Triples**, an adjacency encoding of the SPO
  tree — two coordinate sequences (predicate ids, object ids) plus two
  **rank/select** bit-sequences marking level boundaries; a triple pattern
  with bound subject resolves to a `select` + range walk. HDT-FoQ adds
  extra indexes (wavelet/permutation) for the other access orders.
- **What it buys:** very compact, **mmap-able read-only querying** (no
  parse-to-RAM — the antidote to the §2.c O(store) materialization), a
  mature publication/exchange ecosystem, and rank/select gives O(1)-ish
  navigation instead of the current column decode.
- **What it costs:** **read-only** (no updates — same write-once limit as
  COTTAS today); **no quads in HDT 1.0** (default graph only) — quads need
  the HDTq extension (extra graph bitmaps) or a per-graph HDT set. And the
  compactness depends on building the rank/select structures at import
  (index build cost, like §3.5).
- **How it fits the iron rules.** An HDT reader belongs in F\* as a
  `Parser.*`-style module (front-coded dictionary decode as a `Tot`
  function over the mmap'd bytes; the current `ballyhoo_hdt_runtime.sh`
  shell-out to `hdtSearch` is exactly the rule-#11 debt to retire, #253).
  The **rank/select over compact bit-sequences is the Roaring-adjacent
  track** already scoped in
  [`2026-05-07-c-build-and-roaring-plan.md`](2026-05-07-c-build-and-roaring-plan.md)
  (Phase B bitmap container with `popcount`, Phases C-E) — a verified
  `popcount`/rank/select core would serve both a Roaring bitmap store and
  an HDT Bitmap-Triples reader. A serializer would be
  `serialize : hdt -> Tot (list u8)` per rule #11, with the OCaml side
  reduced to `write_bytes` + `mmap`.

### 4.c In-memory index representations

Today's in-memory index (`RDF.Indexed` bucket maps / patch-97 three
Hashtbls) costs the **~862 bytes/triple measured in §2.c** and offers no
compound or named-graph index (§1.4, indexing-audit). Near-term F\* wins
(compound SPO/POS/OSP keys, named-graph index, BGP reorder) are XS-M
effort. Longer term, CSA/wavelet-tree self-indexes (the HDT-FoQ family)
would fold the dictionary and the index into one compact mmap-able
structure — but that is a research track behind the rank/select core in
§4.b, not a near-term item.

---

## 5. Prioritized roadmap (commit-sized, wins tied to measurements)

Ordered. Each flags **F\* spec** vs **IO/runner glue** per rule #11 and
whether a design doc is needed first.

1. **Fix + regression-pin RLE_DICTIONARY multi-row-group decode on the
   on-disk reader.** *Win:* takes the on-disk path from "fails on 3/3
   fresh corpora" (§2.b) to usable; unblocks all other on-disk work.
   *Type:* F\* spec (`Parquet.Footer.fst`) **and** a build-wiring check
   (confirm #98 decoder is in the shipped `build-ocaml.sh` lists). *First:*
   add a default-encoded regression corpus (RLE on `g`/`p`) to
   `tests/local/`. No new design doc.

   **DONE 2026-07-05 (same day, this fix).** The build-wiring question
   is settled: NOT a wiring gap — `Parquet.Footer.fst`/`Parquet_Footer.ml`
   were in the shipped binary all along; the #98 decoder had simply
   never decoded a real DuckDB/pycottas artifact correctly, and #98's
   own acceptance run (parliament) predates artifacts with these
   encodings in the sandbox. Three distinct F\* defects in
   `Parquet.Footer.fst`, all fixed and verified (z3 4.13.3, no `--lax`):
   (a) `probe_parquet_column_dictionary_page_offset[_in_row_group]` read
   Thrift field 14 (`bloom_filter_offset`) instead of field 11
   (`dictionary_page_offset`) — DuckDB writes a bloom filter by default,
   so the offset looked valid but pointed at bloom bytes and every
   dictionary decode failed; (b) the RLE_DICTIONARY data-page decoder
   treated payload byte 0 as the index bit-width, but every
   DuckDB/pycottas column is Parquet-schema OPTIONAL (SQL `NOT NULL` is
   not propagated), so each data page opens with a definition-level
   section (4-byte LE length + RLE levels) that the DLBA path already
   skipped and the RLE path did not; (c) the decode dispatcher was
   "try DLBA, fall back to RLE_DICTIONARY" — the DLBA parser, fed
   RLE_DICTIONARY bytes, can return a spurious `Some []` instead of
   `None` (this is the exact mechanism of the g21 silent `COUNT=0`); it
   now dispatches on the page header's declared encoding and returns a
   loud `None` for encodings the reader does not implement. Measured
   after the fix, committed binary: medication `COUNT(*)` = 6,780 (was
   hard error), gene `COUNT(*)` = 888,949 across 8 row groups with
   adaptive DLBA/RLE encodings (was hard error), 818-quad all-named-graph
   store decodes all 818 rows with the correct 2-entry graph dictionary
   (was silent 0). Regression pin:
   `tests/unit/parquet_rle_dictionary_multi_row_group.ml` with three
   committed fixtures under `tests/unit/fixtures/` (multi-row-group
   adaptive-encoding, truncated loud-failure variant, all-named-graph
   RLE column).
2. **Add a default-encoded on-disk corpus + query to the CI gate.** *Win:*
   turns the silent-`COUNT=0` soundness bug (g21, §2.b) into a red test.
   *Type:* runner/test glue. Pairs with item 1. **Partially covered by
   item 1's committed unit fixtures (2026-07-05)**; an end-to-end CLI
   query gate over a default-encoded corpus is still worth adding to
   `tests/local/`.
3. **Emit the compact sidecars (.dict/.presence/.offsets) at import
   time, and cluster rows by subject/CS (shapes-canon E1).** *Win:*
   measured — the offset index gives only 6 s→5.2 s today because SPOG
   order defeats per-rg pruning (§3.4/§2.e); clustering is a producer-side
   Python change (zero F\* cost, v1-conformant) that makes the existing
   prune cascade actually prune, and lengthens RLE runs. *Type:* pipeline
   (Python) glue for E1; sidecar-at-import is glue + existing F\* writers.
   Design doc exists (shapes-canon §5-E1); measure prune kill-rate
   before/after.

   **DONE 2026-07-05 (this session, producer-side, gene corpus).**
   `tools/corpus_pipeline.py materialize-nq-cottas-corpus` gained
   `--row-order {producer,cs}` and `--build-sidecars`
   (`write_cottas_clustered` + `build_cottas_sidecars_eager`, both new
   functions in that file). Default behaviour (`--row-order producer`,
   no `--build-sidecars`) is byte-for-byte unchanged, so every existing
   caller (`tests/local/cottas_corpus_regressions.sh`,
   `backend_parity_regressions.sh`, `tools/backend_benchmark.py`, …) is
   untouched.

   **Ordering chosen: `(CS(s), s, p, o, g)` characteristic-set
   clustering, not plain `(p, s, o, g)`.** CS clustering subsumes most
   of a POS-style predicate sort's benefit for bound-predicate scans
   (predicates confined to one shape still land in a small set of row
   groups) while additionally preserving subject locality, which a
   pure predicate sort destroys — a subject's own triples would be
   scattered across up to *n*-predicates-many row groups under POS
   order, making every subject point-lookup and every star join
   (`?s p1 ?a . ?s p2 ?b`) a multi-row-group scan. This is exactly the
   E1 write-up's own conclusion
   ([`2026-07-03-shapes-canon-storage-strategies.md`](2026-07-03-shapes-canon-storage-strategies.md)
   §4, item 1) and the 2026-07-03 prototype's own recommendation
   ([`2026-07-03-e1-cs-clustering-results.md`](2026-07-03-e1-cs-clustering-results.md)
   §7). Implementation: `cs_cluster_nq.py` (already existed, unchanged)
   re-sorts the normalised `data.nq` into `data.cs-clustered.nq`; a new
   `write_cottas_clustered` writes the Parquet directly via DuckDB
   (mirroring `pycottas.rdf2cottas`'s schema/dedup/compression options)
   because `pycottas.rdf2cottas` cannot preserve a producer-chosen row
   order — it always re-`ORDER BY`s by the `index` string's column
   letters (confirmed in the venv's `pycottas/__init__.py`; this is the
   same finding the E1 prototype made).

   **Row-group size: kept at DuckDB's own default (122,880 rows/group,
   8 groups on gene), not reduced.** The task brief asked to "set a
   row-group size that gives multiple groups" (today's SPOG build
   already produces 8, i.e. already "multiple"); the natural next step
   — shrink `ROW_GROUP_SIZE` to raise row-group *count* so CS
   partitions map onto fewer, more homogeneous groups — was tried
   (20,000 rows/group → 44 groups) and **measured to regress query
   latency by roughly 24×** (`?s rdf:type ?o LIMIT 5`: 73–74 ms at 8
   groups vs. 1,877–1,885 ms at 44 groups, same clustered row content,
   only `ROW_GROUP_SIZE` changed — isolated by rebuilding the identical
   clustered `.nq` at both row-group sizes). The same query at 8 groups
   with CS-clustered content matched the SPOG baseline almost exactly
   (78 ms). Conclusion: the current on-disk reader pays a per-row-group
   cost that does not stay flat as row-group count rises on an
   889K-quad corpus, and that cost dominates any pruning gain from
   finer-grained groups. This is exactly the kind of "prune cascade
   needs a small wiring/reader change" this round was scoped to
   *describe, not fix* (see the four-bullet gap list below) —
   `--row-group-size` defaults to 122,880 and is documented in
   `corpus_pipeline.py` as unsafe to lower until that cost is
   characterised.

   **Sidecars at import: wired, but only half the lazy-boot cost is
   actually avoided — a pre-existing reader bug limits the other
   half.** `build_cottas_sidecars_eager` shells out to
   `factoidal query --data-cottas <path> --explain '<trivial query>'`
   (no new OCaml/F\*): opening a COTTAS store for `--explain`
   already calls `Cottas_companion_boot.prewarm_via_companions`
   (`bin/factoidal-explain/factoidal_explain.ml`), the same call
   `factoidal-http` makes at server boot
   (`bin/factoidal-http/factoidal_http.ml:prewarm_cottas_columns`), so
   this reuses the existing writer rather than reimplementing it.
   Measured on gene (server boot via `factoidal serve --data-cottas`,
   HTTP `/query`, `resource.getrusage` + wall-clock): building all
   sidecars lazily at first server boot costs **~101 s** (57.2 s for
   the four `Cottas_companion_writer` `.{s,p,o,g}.dict`/`.presence`
   pairs — the Yod6/Tet3 per-column presence bitmaps — + 1.4 s for the
   Lamed3 `.p.offsets` file + 40.0 s for the compound-po
   `.po.presence` bitmap). Eager-at-import only recovers **~41 s of
   that ~101 s** (the offsets + compound-po pieces), because
   **`Cottas_companion_boot.companions_present_and_valid`
   (`formal/fstar/ocaml-output/RDF_CottasStore.ml:3292-3317`, from the
   `cottas_ondisk_zzzzz_ondisk_index.sh` patch) reports "header verify
   FAILED" for the four dict/presence companions on every single
   invocation, even immediately after writing them in the same
   process** — reproduced with the unmodified producer/SPOG path too
   (this is not something the clustering/eager-sidecar change
   introduced), so every server boot rebuilds those four files
   unconditionally regardless of whether they were built eagerly.
   `.p.offsets` and `.po.presence` have their own, correctly-working
   "already present, skip" checks (`ensure_offsets_built`,
   `existing_file_matches`) and do benefit from eager building. **Not
   fixed this round** (producer-side-only constraint; the bug is in
   OCaml boot-wiring / F\* header validators, out of scope for "no new
   OCaml logic this round") — filing as a followup is the right next
   step; described here rather than patched.

   **FIXED 2026-07-05 (same day, follow-up session).** Root cause was
   a one-constant writer/validator mismatch in F\*, not in the OCaml
   boot wiring: `RDF.CottasStore.DictWriter.fst`'s `dict_magic` was
   `0x444b4f43` ('COKD') — introduced when the #200 PR2 migration
   moved the `.dict` byte assembly from OCaml into F\* — while the
   reader/validator `RDF.CottasStore.OnDiskIndex.fst`
   (`cotd_magic_u32`, checked by `dict_header_ok`, which
   `companions_present_and_valid` calls per column) expects
   `0x44544f43` ('COTD'), the magic the pre-migration OCaml writer
   used. Every `.dict` written since that migration carries the wrong
   magic and fails the boot-time header verify; the `.presence`
   headers match on both sides ('COTP'), but
   `companions_present_and_valid` ANDs all four dict+presence pairs,
   so all four rebuilt on every boot. The non-validating readers
   (`read_dict_header` consumers such as the bulk-load path and
   `ensure_compound_po_built`) never check the magic, which is why
   the mis-stamped files still *worked* — they were just never
   *trusted*. Fix: one constant in `RDF.CottasStore.DictWriter.fst`
   (verified, z3 4.13.3, no `--lax`; re-extracted;
   `tests/unit/dict_writer_roundtrip.ml` hashes re-pinned to the
   corrected 'COTD' bytes — round-trip parse/serialize equalities
   were unaffected since `parse_dict` compares against the same
   constant). Measured on the gene store (888,949 quads, 10
   eagerly-built sidecars, `factoidal query --explain` boot, this
   sandbox): pre-fix HEAD binary, second boot = **57.3 s** ("header
   verify FAILED" ×4 + full rebuild of the four dict/presence pairs,
   on every boot); post-fix binary, second boot = **0.26–0.27 s**,
   all six companion types skipping ("mmap'd companion files,
   skipping pre-warm"; offsets "skipping build"; compound-po "header
   matches; skip"). Eager-at-import now recovers the full lazy-boot
   cost, not just the ~41 s offsets/compound-po share. Old
   'COKD'-stamped stores self-heal: the fixed binary rebuilds them
   once (they do fail verify — wrong magic on disk) and skips
   thereafter. Query
   results are unchanged: `COUNT(*)` = 888,949 and a 3-triple subject
   point lookup return byte-identical CSV from the pre-fix and
   post-fix binaries. Regression pin: a ninth check in
   [`tests/local/cottas_row_order_regressions.sh`](../../tests/local/cottas_row_order_regressions.sh)
   (second-boot-must-not-rebuild: boots the eagerly-built store and
   fails on any rebuild marker in the boot log; 9 checks, 9 pass, 0
   fail), plus the re-pinned serializer hashes above. Floors after
   the fix: SPARQL suite 631 pass, 0 fail (of 631, `w3c_runner` from
   repo root); RDF suite 1031 pass, 0 fail (of 1031, `w3c_runner
   --rdf`); `tests/unit/run-all.sh` from repo root: 28 files pass, 0
   files fail (of 28).

   **Query measurements (gene corpus, 888,949 quads, 8 row groups both
   builds, `factoidal serve` + HTTP `/query`, 3 warm runs each,
   median-equivalent — all three runs agreed to within 2 ms):**

   | query | SPOG (today) | CS-clustered (this change) | delta |
   |---|---:|---:|---:|
   | `?s rdf:type ?o LIMIT 5` (the review's own case) | 73–81 ms | 80–82 ms | ~flat |
   | rare/shape-confined predicate (`wdt:P682`, 4 quads, present in only 2 of 12 characteristic sets) | 94–97 ms | 83–93 ms | ~11% faster |
   | subject point lookup (`<Q100085837> ?p ?o`, 3 result triples) | 193–199 ms | 159–163 ms | ~17% faster |
   | `COUNT(*)` (full scan, default graph) | 32 ms | 31–37 ms | ~flat |

   The `?s rdf:type ?o` case — the review's own headline query — shows
   **no material change**, and this is explained, not just observed:
   every one of gene's 12 characteristic sets includes `rdf:type` (91,871
   of 91,871 subjects have a type triple), so CS clustering cannot
   confine this predicate to a subset of row groups — the mechanism the
   roadmap description assumed only pays off for shape-*specific*
   predicates, and `rdf:type` on this corpus is universal, not
   shape-specific. The rare predicate and the point lookup, which
   *are* shape/subject-specific, show the expected modest wins. This
   is a smaller effect than the roadmap language ("kills most row
   groups") implied, because gene's 8 row groups (vs. parliament's 26)
   leave little room for CS-confinement to matter, and item 2 above
   (the row-group-size regression) rules out compensating with more,
   smaller groups this round.

   **Correctness:** `COUNT(*)` == 888,949 on both builds (exact,
   confirmed via the HTTP endpoint's SPARQL-JSON response); the point
   lookup returns byte-identical bindings on both builds; the g21
   fixture's `GRAPH ?g { ?s ?p ?o } GROUP BY ?g` returns identical
   per-graph counts (g1=500, g2=300, g3=7) on both a SPOG and a
   CS-clustered build of the same 818-quad input. New regression:
   [`tests/local/cottas_row_order_regressions.sh`](../../tests/local/cottas_row_order_regressions.sh)
   (8 checks, 8 pass, 0 fail) builds a SPOG and a CS-clustered artifact
   from the same 5-quad fixture
   (`tests/local/data/cottas_sample.nq`, shared with
   `cottas_corpus_regressions.sh`) and pins: artifact files exist, all
   10 sidecar files exist after `--build-sidecars`, named-graph
   SELECT/default-graph ASK/`COUNT(*)`/`GRAPH ?g GROUP BY` all agree
   between the two builds, and the raw Parquet row count is 5 on both
   (clustering is a pure permutation, no rows dropped or duplicated).
   `cottas_corpus_regressions.sh` (the pre-existing, untouched-path
   suite) still passes 4/4.

   **Size and cost, honestly reported (gene, 888,949 quads):**

   | metric | SPOG (today) | CS-clustered + eager sidecars | delta |
   |---|---:|---:|---:|
   | `data.cottas` size | 1,012,509 B (1.139 B/quad) | 1,037,905 B (1.168 B/quad) | **+2.5% larger**, not smaller |
   | sidecar files total | 0 B (built lazily elsewhere) | 13,642,038 B (13.6 MB, 10 files) | new cost, shipped with the artifact |
   | import wall time | 28.96 s | 144.08 s | +115 s (includes the ~101 s eager-sidecar build, run once at import instead of at every cold server boot) |
   | import peak RSS | 1,789.4 MiB | 1,882.8 MiB | +93.4 MiB |

   The file-size result contradicts the E1 prototype's synthetic-corpus
   finding (−3.3% vs. SPOG there); on gene it is **+2.5% larger**. This
   is corpus-dependent, not a measurement error: gene's characteristic-
   set distribution is dominated by one CS (742,734 of 888,949 quads,
   83.5%, over 12 total CS's), unlike the E1 prototype's evenly-split
   4-shape synthetic corpus, and Wikidata's arbitrary `Q`-number
   subject IRIs give SPOG's plain lexicographic-subject sort no
   correlation with shape to begin with — so there is little headroom
   for CS clustering to add compression on top of SPOG here, and
   assembling the DuckDB row-group dictionaries in CS order instead of
   subject order cost slightly more than it saved. The E1 doc's own
   caveat ("corpora whose subject IRIs do not correlate with structure
   should show a larger clustered-vs-spog gap … parliament sits in
   between") did not anticipate a *negative* gap; gene demonstrates one
   is possible, and this should be re-checked against parliament rather
   than assumed away.

   **Floors (unchanged, confirmed 2026-07-05 after this change, no F\*/
   OCaml touched — `git status` shows only `tools/corpus_pipeline.py`
   modified and `tests/local/cottas_row_order_regressions.sh` added):**
   RDF suite 1,031 pass, 0 fail (of 1,031, via `w3c_runner --rdf`).
   SPARQL suite 629 pass, 2 fail (of 631, via `w3c_runner`) — the 2
   fails are the `:rif01`/`:rif03` RIF-entailment-regime manifest
   entries, which `docs/claude-rules/scope.md` documents as passing
   only through the dedicated `rif_runner` (4 pass, 0 fail of 4), not
   the general SPARQL `w3c_runner`; this is pre-existing and unrelated
   to this change. `tests/unit/run-all.sh` (run from repo root, per its
   `Sys.getcwd()`-relative fixture paths): 28 file(s) pass, 0 file(s)
   fail (of 28).

   **What was NOT done this round, on purpose (per the task's
   producer-side-only, no-new-F\*-logic constraint), and should be the
   next items:**
   1. Fix `Cottas_companion_boot.companions_present_and_valid`'s
      always-fails header check for the four dict/presence
      companions, so eager-at-import actually saves the full ~101 s
      instead of ~41 s. **DONE 2026-07-05** — the check itself was
      correct; the `.dict` *writer's* magic constant in
      `RDF.CottasStore.DictWriter.fst` was wrong ('COKD' vs the
      validator's 'COTD'). See the "FIXED 2026-07-05" paragraph
      above: gene second boot 57.3 s → 0.26 s.
   2. Characterise and fix the on-disk reader's per-row-group cost
      that made 44 row groups 24× slower than 8, so `--row-group-size`
      can be safely lowered to let CS partitions map onto more,
      smaller, more homogeneous groups — the change that would let a
      shape-confined predicate actually "kill most row groups" instead
      of the ~11-17% wins measured here.

      **CHARACTERISED and PARTIALLY FIXED 2026-07-05 (this session,
      follow-up).** Reproduced small first, per the redispatch brief:
      a 50,000-quad fixture (first 50k lines of the gene corpus's
      N-Quads, `--row-order cs`, identical clustered content, only
      `ROW_GROUP_SIZE` varied: 30,000 -> 2 row groups, 2,048 (DuckDB's
      vector-size floor) -> 25 row groups) reproduced the effect at
      small scale before touching the gene corpus: a full-scan query
      (`?s <rdf:type> "no-such-object"`, forcing every touched row
      group to be decoded with zero matches) went from 0.60 s at 2
      groups to 10.3 s at 25 groups, ~17×, on a fixture 18× smaller
      than gene. `strace -c` showed the cost is **not** I/O (2-3
      `read()` syscalls total per run; the whole file is mmap'd once
      via the existing `__mim2_file_bytes_cache`) — it is CPU-bound.

      Root cause, read directly from the OCaml realisation of the
      `assume val`s in `Parquet.Footer.fst`
      (`experimental_ocaml_glue/parquet_footer_runtime.sh`):
      `parquet_read_tail_hex`/`parquet_read_range_hex` cache the raw
      file **bytes** per path (the pre-existing "Mim2" cache, added for
      issue #100) but re-**hex-encode** the requested byte range from
      scratch on every single call, using `Printf.sprintf "%02X"` per
      byte inside a `String.iter` loop — no memoization of the
      hex-encoded result itself. Every one of the ~15
      `probe_parquet_*` call sites in `Parquet.Footer.fst` that locates
      a (row_group, column) pair — via
      `probe_parquet_column_chunk_in_row_group_locator`, called once
      per row group whenever a column is walked in full (the
      lazy-dictionary `collect_distinct` path at first use, or an
      unpruned per-row-group search when the bound predicate is
      present in every row group, as `rdf:type` is on gene's 12
      characteristic sets) — re-reads and re-hex-encodes the **entire
      Parquet footer** from scratch. Measured directly: the fixture's
      footer metadata length grows from 1,638 bytes at 2 row groups to
      18,703 bytes at 25 row groups (roughly linear in row-group count,
      since each row group adds ~4 more column-chunk stat structs to
      the footer). Because both (a) the footer size and (b) the number
      of per-row-group locate calls during an unpruned column walk grow
      with row-group count, the unmemoized cost is quadratic-ish in
      row-group count for a fixed corpus size — the exact mechanism
      behind the 24-25× (gene, 8→44 groups) and 17× (this fixture,
      2→25 groups) slowdowns.

      **Fix shipped**, OCaml I/O-glue side only, no F\* or decode-logic
      change (rule #11(c)/#15: pure memoization of a deterministic
      computation over already-cached bytes; returned hex strings are
      byte-identical to the unmemoized path, confirmed by diffing
      query output before/after): `parquet_footer_runtime.sh` now (1)
      memoizes `parquet_read_tail_hex` per `(path, count)` and
      `parquet_read_range_hex` per `(path, start, count)` in two new
      "Mim3" hashtables, so every probe after the first for a given
      key is an O(1) hit instead of an O(footer_size) re-encode, and
      (2) replaces the per-byte `Printf.sprintf "%02X"` hex encoder
      with a precomputed 256-entry lookup table (same output, no
      per-call format-string parsing). Applied by re-extracting just
      `Parquet.Footer.fst` (unchanged .fst, so `--cache_checked_modules`
      made this sub-second — no re-verification needed) and re-running
      `ocaml-patches.sh` + `build-ocaml.sh compile`.

      **Measured improvement** (both scales, query output byte-
      identical pre/post-fix): the 50,000-quad fixture's full-scan
      query went from 10.3 s to 8.0 s at 25 groups (2 groups unchanged
      at 0.60 s) — ratio 17.2× → 13.3×. On the actual gene corpus
      (888,949 quads, `factoidal serve` + HTTP `/query`, 3 warm runs
      each, companions valid/mmap'd, matching this doc's own §"Query
      measurements" methodology above): `?s rdf:type ?o LIMIT 5` at 8
      row groups is unchanged (71-74 ms vs the previously-recorded
      73-81 ms, within noise); at 44 row groups it improved from
      1,877-1,885 ms to 1,437-1,462 ms — **about 23% faster**, ratio
      24.4× → ~19.8×. Correctness unaffected: `COUNT(*)` = 888,949
      (exact) and the `Q100085837` subject point lookup return
      identical bindings on both the 8- and 44-group builds, post-fix.
      Regression floors after the fix (repo root only — other cwds
      show a misleading 629/2 for the SPARQL suite): SPARQL suite 631
      pass, 0 fail (of 631); RDF suite 1,031 pass, 0 fail (of 1,031);
      `tests/unit/run-all.sh` 28 file(s) pass, 0 file(s) fail (of 28);
      `tests/local/cottas_row_order_regressions.sh` 9 checks, 9 pass, 0
      fail; `tests/local/cottas_corpus_regressions.sh` 4 checks, 4
      pass, 0 fail.

      **Not closed — the remaining ~20× is a second, larger, non-
      commit-sized issue, characterised but not fixed this round.**
      The Mim3 cache removes the *re-hex-encoding* cost but not the
      per-locate *structural walk*: `probe_parquet_column_chunk_in_row_group_locator`
      still calls `nth_compact_list_element_start_hex`, whose inner
      `loop` walks and decodes (skips) `rg_index` preceding
      compact-protocol row-group structs **on every single call**,
      fresh, with no memoization of "row group N starts at hex offset
      X" across calls. Summed over every row group touched during an
      unpruned column walk, this is still O(row_groups²) even with the
      footer bytes/hex now cached — which is why the fixture's ratio
      only fell to 13.3× (not to something close to the 12.5× row-
      group-count ratio a clean O(n) cost would give) and gene's ratio
      only fell to ~19.8× (not close to the 5.5× row-group-count
      ratio). Unlike the Mim3 fix, this one is **not** OCaml I/O glue:
      the repeated walk lives inside `Parquet.Footer.fst` itself (a
      verified F\* function, not an `assume val` realisation), so
      closing it means adding a new F\* function that computes every
      row group's start offset in a single linear pass over the footer
      once per file (e.g. `probe_parquet_row_group_offsets_all : path
      -> option (list nat)`), re-pointing the ~15 per-row-group probe
      call sites at an O(1) index into that list, and re-verifying
      `Parquet.Footer.fst` under z3 4.13.3 — real F\* work, not a
      caching patch, and out of scope for this redispatch. Filing as
      the next item in this list.

      **DONE 2026-07-06 (follow-up session). The O(row_groups)
      per-locate walk is eliminated, in F\*.** New in
      `Parquet.Footer.fst` (all verified, z3 4.13.3, no `--lax`):
      `parquet_row_group_offset_table` (a record bundling the footer
      meta hex + every row group's struct start offset),
      `collect_compact_list_starts_loop` (ONE linear pass performing
      the same `skip_compact_value_hex` steps the old per-call
      `nth_compact_list_element_start_hex` loop performed, recording
      every element start instead of discarding the walk),
      `probe_parquet_row_group_offset_table` (builds the table from
      one footer read), and a `_from_table` sibling family of the
      `_in_row_group` probes (locator, data/dictionary page offsets,
      page-header probes, payload decompress, DLBA + RLE_DICTIONARY
      decode, declared-encoding dispatch, dictionary-only decode) that
      indexes `List.Tot.nth table.prgt_row_group_starts rg_index`
      instead of re-walking. The #98 encoding dispatch and
      definition-levels skip are body-identical in the siblings; the
      original path-based family is untouched. Threading (justified in
      the module banner): the table is built ONCE per public query
      entry point in `RDF.CottasStore.fst` (`cottas_ondisk_search` /
      `_search_limited` / `_estimate` / `_count_exact`) and passed
      down as an ordinary F\* argument through `plan_candidate_rgs` →
      `populate_dict_cache_for_column` and through the `walk_*_global`
      row-group walks; the whole-column eager walk
      `probe_parquet_column_decode_all_row_groups` builds it once per
      call internally. Two new `assume val`s pass the table through
      the existing page-cache boundary
      (`probe_parquet_column_decode_in_row_group_seq_from_table` in
      ColumnSeq, `pcache_decode_in_row_group_global_from_table` in
      PageCache); their OCaml realisations (same two glue scripts as
      their non-table siblings) only FORWARD the F\*-computed table —
      no OCaml-side computation or caching of offsets, per rule #11.

      **Measured (this sandbox, 3 warm runs each; all outputs
      byte-identical pre-fix vs post-fix on both stores AND identical
      between the 8- and 44-group builds; COUNT(\*) = 888,949 exact on
      both gene builds).** Pre-fix = committed HEAD `fa62460`;
      post-fix = this change. 50,000-quad fixture (first 50k gene
      quads, CS-clustered, identical content, only `ROW_GROUP_SIZE`
      varied; full-scan CLI query `?s rdf:type "no-such-object"`):

      | build | pre-fix | post-fix |
      |---|---:|---:|
      | 2 row groups | 0.76–0.80 s | 0.70–0.71 s |
      | 25 row groups | 7.46–7.62 s | **0.80–0.82 s** |
      | 25-vs-2 ratio | ~9.8× | **~1.15×** |

      Gene corpus (888,949 quads, CS-clustered + eager sidecars,
      `factoidal-http` + HTTP `/query`, warm):

      | query | 8 rg pre | 8 rg post | 44 rg pre | 44 rg post |
      |---|---:|---:|---:|---:|
      | `?s rdf:type ?o LIMIT 5` | 62–63 ms | **20 ms** | 1,427–1,446 ms | **83–84 ms** |
      | point lookup (`Q100085837 ?p ?o`) | 149–154 ms | **101–103 ms** | 1,492–1,513 ms | **160–162 ms** |
      | rare predicate (`wdt:P682` LIMIT 5) | 69–70 ms | **28–29 ms** | 1,419–1,473 ms | **84–85 ms** |
      | `COUNT(*)` | 35–36 ms | 35–37 ms | 39–41 ms | 60–62 ms |

      The 44-vs-8 ratio on the review's own query fell from ~22.9×
      (measured pre-fix here; the earlier session recorded ~19.8×) to
      **~4.1×** (83 ms vs 20 ms) — short of the ~2× target, but the
      remaining gap is now BELOW the 5.5× row-group-count ratio: the
      quadratic per-locate component is gone and what remains is at
      most linear in row-group count (the per-query `dict_cache`
      rebuild and per-rg walk overheads; a cross-query dict cache, the
      Tsade2 "Phase E refinement", is the next lever if ~2× is wanted
      strictly). The 44-group absolute warm time (83–84 ms) now sits
      inside the previous 8-group baseline range (62–81 ms). One shape
      regressed slightly: `COUNT(*)` on the 44-group build went 39–41
      → 60–62 ms (graph-column-only exact-count walk, still dominated
      by the 888,949-cell fold; small in absolute terms, 8-group build
      unchanged). Regression pin:
      `tests/unit/parquet_rle_dictionary_multi_row_group.ml` grew a
      correctness section — the offset table on the 3-group fixture
      must have exactly 3 entries, and for every (row group, column)
      pair the table-indexed decode and the table-indexed dictionary
      probe must equal the path-based originals (80 assertions in the
      file, 0 fail). Floors after the change (repo root): SPARQL suite
      631 pass, 0 fail (of 631); RDF suite 1,031 pass, 0 fail (of
      1,031); `tests/unit/run-all.sh` 28 file(s) pass, 0 file(s) fail
      (of 28); `tests/local/cottas_row_order_regressions.sh` 9 pass, 0
      fail; `tests/local/cottas_corpus_regressions.sh` 4 pass, 0 fail.

      **Row-group-size default decision (the question this item
      gates): keep 122,880.** With the fix in, the 20,000-rows/group
      gene build (44 groups) was re-measured against the default build
      (8 groups) on the rare/shape-confined predicate query the E1
      clustering work targets (`wdt:P682`, 4 quads, 2 of 12
      characteristic sets): 84–85 ms at 44 groups vs 28–29 ms at 8
      groups. Smaller groups still LOSE on this corpus — the linear
      per-row-group planner cost still exceeds what CS-confined
      pruning saves at gene's scale — so `--row-group-size` keeps
      DuckDB's default; revisit after a cross-query dict cache lands
      or against parliament's 232-predicate shape.

      **DONE 2026-07-06 (follow-up session): the cross-query
      dictionary cache (Tsade2 "Phase E refinement") is in.** The
      residual linear per-row-group warm cost was profiled first, by
      attribution against a kill switch (below): the column-prune
      planner's per-QUERY `dict_cache`
      (`RDF.CottasStore.fst` § Tsade2, rebuilt from `[]` on every
      `plan_candidate_rgs` call) redid the per-row-group dictionary
      page decompress + plain-dictionary decode
      (`Parquet.Footer.probe_parquet_column_dictionary_in_row_group_from_table`)
      on EVERY query, even though a read-only store's dictionaries are
      invariant for the handle's lifetime. Measured share of the warm
      per-query time on the gene 44-group build (same server process,
      cache on vs off): 54% of `?s rdf:type ?o LIMIT 5` (87.4 →
      39.9 ms), 70% of the point lookup (170 → 50.5 ms), 54% of the
      rare predicate (90.3 → 41.0 ms), ~0% of `COUNT(*)` (66 → 63 ms —
      no bound column, planner never probes dictionaries). A
      planner-only probe (bound predicate absent from the store, so
      candidates prune to zero and no data page is touched) runs in
      4.3 ms warm at 44 groups — the planner's per-row-group cost is
      now effectively gone; what remains of the 44-vs-8 gap is
      data-walk-side (per-candidate-rg decode/filter restarts), not
      dictionary or locate work.

      **Design split (rule #11).** WHAT is cached and its correctness
      contract is F\*: `RDF.CottasStore.PageCache.fst` gained
      `dict_page_cache` — an LRU cache keyed `(rg_index, col_index)`
      holding `list string` dictionaries, mirroring the existing
      verified `page_cache`/`pcache_*` LRU exactly (same age-stamp
      eviction, same key shape; only the value type differs) — plus
      `dpcache_get`/`dpcache_put`/`dpcache_probe_dict_in_row_group_from_table`
      (all verified, z3 4.13.3, no `--lax`). Store identity is the
      artifact path via the F\*-computed row-group-offset table, and
      invalidation is store-handle/process lifetime (stores are
      write-once read-only; same contract the existing page cache
      relies on). The CROSS-CALL STORAGE CELL is the same rule-#11(c)
      shim shape as the two existing `pcache_*_global` realisations
      and lives in the SAME glue file
      (`experimental_ocaml_glue/cottas_pagecache_global_runtime.sh`,
      extended, not duplicated): a `dict_page_cache ref` threaded
      through the F\*-pure functions, zero OCaml decode logic (rule
      #15 — decode stays solely in `Parquet.Footer`).
      `RDF.CottasStore.populate_dict_cache_loop`'s table branch now
      calls the global probe instead of the raw per-call probe; the
      per-query `dict_cache` remains as the intra-query memo, and the
      no-table fallback branch is untouched. Kill switch:
      `FACTOIDAL_DISABLE_DICT_GLOBAL_CACHE=1` bypasses the ref
      entirely and takes the pre-change per-query path (the
      `FACTOIDAL_DISABLE_STREAM_FASTPATH` precedent).

      **Memory bound.** Capacity 1024 entries with LRU eviction
      (44 rgs × 4 cols = 176 on the finest gene build; parliament
      26 × 4 = 104), so growth is capped on pathological stores —
      past capacity the planner just redecodes evicted entries,
      degrading to pre-change behavior rather than growing. Gene's
      total decoded dictionary footprint (whole-store distinct token
      bytes: `.s.dict` 4.99 MB + `.o.dict` 4.07 MB + `.p.dict` 372 B +
      `.g.dict` 59 B) is ~9.1 MB; measured server peak RSS after 3
      rounds of the 4-query set on the 44-group build: 126.0 MiB cache
      on vs 126.4 MiB cache off — no measurable growth (the cache
      displaces transient decode allocations of the same strings).

      **Measured (gene, 888,949 quads, CS-clustered + eager sidecars,
      `factoidal serve` + HTTP `/query`, one server process per
      config, 3 warm runs each; "pre" = same binary with the kill
      switch set, which reproduces the previous section's committed-
      HEAD numbers within noise — e.g. 44-group type 87.4 ms vs the
      83–84 ms recorded above):**

      | query | 8 rg pre | 8 rg post | 44 rg pre | 44 rg post |
      |---|---:|---:|---:|---:|
      | `?s rdf:type ?o LIMIT 5` | 19.9–20.3 ms | **12.2–13.7 ms** | 87.0–90.0 ms | **39.3–40.0 ms** |
      | point lookup (`Q100085837 ?p ?o`) | 110–111 ms | **20.0–21.5 ms** | 170–173 ms | **50.5–50.7 ms** |
      | rare predicate (`wdt:P682` LIMIT 5) | 29.1–30.6 ms | **19.7–21.2 ms** | 90.2–91.7 ms | **40.9–41.2 ms** |
      | `COUNT(*)` | 35.9–36.1 ms | 34.6–36.1 ms | 66.4 ms | 62.8–63.8 ms |

      The 44-group probe lands at 39.9 ms — exactly 2.0× the previous
      8-group baseline (20 ms, the "≤2× the 8-group time" target as
      posed, from 4.1×). Against the CONCURRENT post-change 8-group
      time (12.2 ms, itself improved 39% by the same cache) the ratio
      is 3.2× — the dictionary component of the gap is gone and the
      remainder is data-walk-side, at most linear in row-group count.
      The 8-group build did not regress on any shape (COUNT flat,
      everything else faster). One pre-existing slow shape noted while
      profiling, unchanged by this work (identical at ~55 s with the
      cache on and off, correct answer 91,871 both ways): a COUNT over
      a bound predicate present in every row group
      (`COUNT` of `?s rdf:type ?o`) on the 8-group build pays a full
      cold s/p/o/g decode of 122,880-row groups in one CLI shot — that
      is the unbounded data-walk cost of roadmap item 4, not planner
      work.

      **Correctness.** All 24 HTTP response bodies (2 stores × 4
      queries × 3 runs) are byte-identical cache-on vs cache-off;
      `COUNT(*)` = 888,949 exact on both builds; the point lookup
      returns the same 3 bindings on both builds. Regression pins:
      [`tests/local/dict_global_cache_parity.sh`](../../tests/local/dict_global_cache_parity.sh)
      (6 checks, 6 pass, 0 fail — builds a CS-clustered store from the
      shared 5-quad fixture and byte-diffs five query shapes across
      the kill switch, including an absent-predicate full-prune and a
      no-bound full walk), and
      `tests/unit/parquet_rle_dictionary_multi_row_group.ml` grew a
      section 8 (96 assertions in the file now, 0 fail): the global
      cached probe must equal the raw path-based probe on both the
      miss and the hit call for every dictionary-bearing (rg, col) of
      the 3-row-group fixture, plus pure-F\* LRU pins
      (get-returns-stored, LRU eviction at capacity,
      recently-used+new survive, capacity-0 stores nothing).

      **Row-group-size decision, re-measured with the cache in: keep
      122,880.** The rare/shape-confined predicate probe (`wdt:P682`)
      is 41 ms warm at 44 groups vs 20 ms at 8 groups — smaller groups
      still lose about 2× on this corpus even with planner cost per
      group now near zero, because the data-walk side retains a
      per-candidate-group cost and gene's CS-confinement only halves
      the candidate set. Report only, per the tasking; revisit against
      parliament's 26-group/232-predicate shape where confinement
      kills a larger fraction.

      **Floors after the change (repo root only — other cwds show a
      misleading 629 pass, 2 fail for the SPARQL suite):** SPARQL
      suite 631 pass, 0 fail (of 631); RDF suite 1,031 pass, 0 fail
      (of 1,031); `tests/unit/run-all.sh` 28 file(s) pass, 0 file(s)
      fail (of 28); `tests/local/cottas_row_order_regressions.sh` 9
      pass, 0 fail; `tests/local/cottas_corpus_regressions.sh` 4 pass,
      0 fail; `tests/local/dict_global_cache_parity.sh` 6 pass, 0
      fail (new).
   3. Re-run this whole comparison against the UK Parliament corpus
      (absent from this sandbox, per §0's caveat) once it is
      reachable, since gene's 8-row-group / 12-CS / 6-predicate shape
      is a poor structural match for the "kills most row groups"
      mechanism the roadmap describes — parliament's 26 row groups and
      232 predicates is the corpus this technique was designed for.
   4. **Fix the cold full-column-decode cost of a COUNT over a
      universally-present bound predicate** (the "one pre-existing
      slow shape" noted above, filed against roadmap item 4).

      **DONE 2026-07-06 (follow-up session).** Reproduced first,
      before touching anything: a fresh CS-clustered + eager-sidecar
      gene build (888,949 quads, 8 row groups, same pipeline as this
      item), `factoidal query --data-cottas` (native CLI, not HTTP,
      this sandbox), `SELECT (COUNT(*) AS ?n) WHERE { ?s a ?o }`
      (`rdf:type`, present in every one of gene's 12 characteristic
      sets — the dict-cache candidate prune cannot narrow the
      row-group set for this predicate): **58.26 s wall**, correct
      answer 91,871. `strace -f -c` on the same run attributed only
      **22.6 ms of syscall time total** (93.7% of that in `munmap` at
      process exit; 16 `read()` calls, 41 `mmap()` calls) — confirming
      the perf review's own prior finding that this cost is CPU-bound
      userspace work, not I/O, ruling out hypothesis (c)
      (list-append quadratics would show as CPU too, but see below —
      it wasn't the cause) and pointing at decode/materialisation
      cost.

      **Root cause, read directly from `RDF.CottasStore.fst`
      (hypothesis (a), decoding entire unneeded columns): confirmed,
      not hypothesis (d) (per-row dictionary-index re-resolution —
      that was already fixed by the dict-cache work one item up) and
      not (b) (hex-string materialisation — real, but not what this
      query pays extra for) or (c) (list-append quadratics — the
      hot walk already uses the array-shape `cottas_column`
      seq-decoder from Phase 2.5b, not `list`).**
      `cottas_ondisk_count_exact`'s bounds-present branch dispatched
      to `walk_row_groups_estimate_global`, which unconditionally
      decoded **all four** s/p/o/g columns of every row group via
      `pcache_decode_global_auto`, then fed them to
      `count_zipped_rows_seq` — even though `?s rdf:type ?o` has
      `bound_s = None` and `bound_o = None`. `cell_match None _` is
      `true` unconditionally, so neither the match test nor the
      COUNT's output (a bare integer, no bindings) ever needed the
      subject or object column's decoded VALUE — but the walk paid a
      full string-materialising decode of both anyway. On gene, s and
      o are exactly the two high-cardinality columns (adaptively
      DLBA/RLE_DICTIONARY, tens of thousands of distinct tokens across
      888,949 rows, per §1.1); p and g are cheap (6 and ≤1 distinct
      values respectively on this corpus). This is the dominant cost:
      the walk decoded 2 of the 4 columns for no reason a COUNT could
      ever use.

      **Fix, in F\* (verified, z3 4.13.3, no `--lax`; no extension
      of `experimental_ocaml_glue/` beyond the pre-existing rule-#11
      pass-through shims per the dispatch brief).**
      `RDF.CottasStore.fst` gained `bound_col_match` (mirrors
      `cell_match`'s contract exactly — `None` bound matches
      unconditionally, without even inspecting an undecoded column),
      `count_selective_matches_seq` (the zipped-match loop,
      parameterised over `option cottas_column` for s/p/o so a
      column whose bound is `None` never needs a value), and
      `walk_row_groups_count_exact_global` (the per-row-group driver:
      decodes column 3 (graph) unconditionally — cheap, and needed
      both to source the row count `n` and because a live
      `GB_CottasOnDisk` query always carries a graph bound per issue
      #267 — and decodes columns 0/1/2 (s/p/o) ONLY when that
      column's bound is `Some`). `cottas_ondisk_count_exact`'s
      bounds-present branch now calls this selective walk instead of
      the old all-four-columns `walk_row_groups_estimate_global`.
      Semantics preserved exactly for the columns that ARE bound
      (a bound column's decode failure still zeroes the whole row
      group's contribution, matching the old all-or-nothing
      fallback) and, as a side effect, no longer let an UNRELATED
      unbound column's decode failure zero out a row group the query
      never needed that column for — a latent under-counting risk in
      the old code that this change also closes, though it was not
      observed on this corpus (no decode failures occur post-#98).

      **Measured (this sandbox, fresh gene CS-clustered + eager-sidecar
      build, native CLI, `timeout` per anti-pattern #17, 3 warm-process
      runs for the after column — the earlier §"Query measurements"
      cells above show cache-on/off pairs from a warm HTTP server;
      this table is the on-CLI, cold-per-invocation shape the ~55 s
      case actually is). "Before" is the git-committed HEAD binary
      (re-extracted to a scratch dir, unmodified by this fix) run
      against the identical artifact, confirming the reproduction
      independently of my working-tree state:**

      | query | before | after |
      |---|---:|---:|
      | `SELECT (COUNT(*) AS ?n) WHERE { ?s a ?o }` (bound p only, universal predicate, 8 rg) | 58.26 s (first repro) / 54.99 s (HEAD binary, re-confirmed) | **2.77–2.82 s** |
      | `SELECT (COUNT(*) AS ?n) WHERE { ?s ?p ?o }` (COUNT(*), unbound — graph-only walk, untouched by this fix) | 0.740 s | 0.727 s (unchanged, within noise) |

      **~19–20× faster** on the target case (~55 s → ~2.8 s), and now
      proportional to the cheap columns actually needed rather than to
      the whole store's s/o content. The remaining ~2.8 s is the graph
      + predicate column decode plus the per-row match loop over
      888,949 rows (an O(rows), not O(store-content), cost) — smaller
      than the ~55 s baseline by an order of magnitude but not yet
      "milliseconds"; a further reduction would mean predicate-pushdown
      by dictionary ID (resolve `rdf:type` to its per-row-group
      dictionary index once, then compare integers against the RLE
      index stream instead of decoding every matching cell to a string
      at all) — the hypothesis (d) mechanism, not implemented here
      because (a) alone already closed the dominant 2-of-4-columns
      waste and delivered an order-of-magnitude win from a
      commit-sized change; revisit hypothesis (d) if a future
      corpus/predicate combination still shows a multi-second
      selective-decode COUNT.

      **Correctness, and an unrelated pre-existing bug found while
      building the regression pin.** `COUNT(*)` = 888,949 exact
      (unbound path, unchanged); the bound-`rdf:type` COUNT = 91,871
      exact, identical before and after. The first regression-pin
      draft wrapped its bound-p/bound-o/bound-s probe queries in
      `GRAPH ?g { ... }` (mirroring the existing named-graph checks in
      the same file) and one of them — a bound-p-and-bound-o pattern
      against the CS-clustered build only — came back `0` instead of
      `1`. Root cause was NOT this fix: `SPARQL11.Store.fst`'s
      `detect_streaming_count_star` (the only caller of
      `cottas_ondisk_count_exact`) matches via `extract_single_tp_bgp`,
      which requires a bare `GP_BGP [tp]`; a `GRAPH ?g { tp }`-wrapped
      COUNT never reaches `cottas_ondisk_count_exact` at all — it falls
      through to the generic materialise-then-search evaluator, which
      on the CS-clustered build's `filter_candidates_by_compound_po`
      (the pre-existing `.po.presence` compound bitmap consult,
      untouched by this change and never called by
      `cottas_ondisk_count_exact`) apparently mis-prunes the one
      row group that has both bound tokens present as a pair when the
      corpus has been CS-clustered. Confirmed independent of this fix
      by reproducing the same `0` on the unmodified git-committed HEAD
      binary with a plain `SELECT ?g ?s WHERE { GRAPH ?g { ?s <p> <o>
      } }` (no COUNT at all) — bound-p alone and bound-o alone each
      correctly return the row; only the conjunction, only on the
      clustered build, returns none. This is a real, separate bug in
      the CS-clustered on-disk SEARCH path (roadmap item 3's
      territory, not item 4's) — out of scope for this change, not
      fixed, and reported here rather than silently worked around;
      worth its own issue. The regression pin below was corrected to
      use bare (non-`GRAPH`-wrapped) BGP COUNT queries against the
      fixture's single default-graph quad instead, which DO exercise
      `cottas_ondisk_count_exact` / this fix's code path, and all pass
      on both builds.

      Regression pins: five new checks in
      [`tests/local/cottas_row_order_regressions.sh`](../../tests/local/cottas_row_order_regressions.sh)
      (bound-p-only, bound-p-and-bound-o, bound-s-only, and a
      zero-match bound-p-and-o case, each checked for cross-build
      agreement AND a literal expected count — 1, 1, 1, 0 respectively
      — so a regression that returns the same wrong number on both
      builds still fails; the file is 17 checks total now, 17 pass, 0
      fail, up from 9), and a new section 9 in
      [`tests/unit/parquet_rle_dictionary_multi_row_group.ml`](../../tests/unit/parquet_rle_dictionary_multi_row_group.ml)
      (102 assertions in the file now, 0 fail, up from 96) pinning
      `count_selective_matches_seq` against a naive full-column
      reference scan across six bound-pattern shapes (bound-p-only,
      bound-p-and-o, bound-s-only, bound-g-only, all-four-bound,
      no-bounds-at-all) on all 3 row groups of the existing
      multi-row-group fixture, including the 4-row trailing group
      where the object column adaptively switches encoding.

      **Floors after the change (repo root only):** SPARQL suite 631
      pass, 0 fail (of 631); RDF suite 1,031 pass, 0 fail (of 1,031);
      `tests/unit/run-all.sh` 28 file(s) pass, 0 file(s) fail (of 28 —
      a 29th file, `delta_log_roundtrip.ml`, fails to build in this
      tree, but it is a concurrent sibling session's new,
      not-yet-wired-in test, untouched by and unrelated to this
      change); `tests/local/cottas_row_order_regressions.sh` 17 pass,
      0 fail (of 17, up from 9); `tests/local/cottas_corpus_regressions.sh`
      4 pass, 0 fail; `tests/local/dict_global_cache_parity.sh` 6
      pass, 0 fail.
4. **Make the in-memory query path bound memory (push aggregation /
   point-lookup through a streaming store scan).** *Win:* measured — a
   1-row answer costs 731 MiB today (§2.c); target O(working-set+result).
   Directly serves #100's "memory bounded by working-set." *Type:* F\*
   eval + store-capability work (`SPARQL11.Store` / `RDF.Store.Capabilities`
   from the recovery plan). Design: recovery plan already covers the
   capability record.

   **First slice landed (2026-07-05, measured).** A parse-stream fast
   path in the CLI now answers the analytically-streamable query
   shapes in one pass over the parse stream, never building the graph:
   `SELECT (COUNT(*) AS ?v) WHERE { tp }` (tp a single triple pattern,
   any position constant or variable), the `GRAPH ?g { ?s ?p ?o }`
   named-graph-wildcard COUNT sibling for N-Quads, and
   `ASK { tp }` (with early parse stop on first match). The shape
   decision is pure F\* (`SPARQL.Plan.Streamable.streamable_shape`,
   new module) and the per-triple fold is F\* too (`stream_step`);
   the CLI wires them into new generic fold entry points on the F\*
   parsers (`Parser.Turtle.fold_turtle_triples`,
   `Parser.NTriples.fold_ntriples`, `Parser.NQuads.fold_nquads`) —
   the same one-pass mechanism behind `factoidal count`. Everything
   else falls through to the materialise path unchanged.
   Measured on gene.ttl (888,949 triples, this sandbox, same
   getrusage wrapper as §2.c): COUNT(\*) went from 28.4 s / 730.5 MiB
   peak RSS (HEAD `8bf6d82` committed binary) to **6.6 s / 44.1 MiB**
   — the streaming-count bound from §2.c, a 16.6× RSS and 4.3× wall
   reduction; `ASK { ?s ?p ?o }` answers in **0.05 s / 41.8 MiB**
   (early stop). Output is byte-identical to the materialise path
   (pinned: `tests/local/streamable_fastpath_regressions.sh`, 13
   pass, 0 fail, fast-vs-slow diffed per query via
   `FACTOIDAL_DISABLE_STREAM_FASTPATH=1`;
   `tests/unit/streamable_fastpath_unit.ml`, 26 pass, 0 fail; SPARQL
   suite 631 pass, 0 fail; RDF suite 1031 pass, 0 fail). The general
   O(store) wall remains for every non-streamable shape — point
   lookups still cost 731 MiB — so the store-capability work above is
   still the real fix; this slice bounds the aggregate/existence
   class only.
5. **Retire `cottas_ondisk_runtime.sh` (718 lines) per the #118 first
   slice.** *Win:* removes the largest rule-#11 violation, lets the
   on-disk hot path extract to C/WASM, and concentrates the soundness
   surface onto 8 documented oracles. *Type:* F\* spec
   (`RDF.CottasStore.fst`) + glue deletion. Design doc exists
   (`2026-07-03-issue-118-first-slice-plan.md`); gate on ukparliament-bench
   — which requires the corpus, so this item is partly blocked in this
   sandbox.
6. **Parquet row-group min/max zone-map pruning.** *Win:* near-free
   row-group skips for bound-object/range patterns, independent of the
   sidecars. *Type:* F\* reader (`Parquet.Footer.fst` Statistics decode) +
   planner consult. Small design note.
7. **Dictionary-ID COTTAS v2 + HDT reader track.** *Win:* smaller files +
   cheaper decode (v2); mmap-able read-only querying that sidesteps the
   O(store) materialization (HDT). *Type:* F\* spec + new design docs
   (v2 format doc; HDT reader spec), sharing the rank/select core with the
   Roaring track (§4.b). Sequenced last; both need their own design docs
   before code.
8. **Durable UPDATE / crash safety** (#100 Phase 4). *Win:* the missing
   write path (§1.5, §3.6). *Type:* F\* spec (`RDF.Persistent.fst` page
   format + on-disk term dictionary) + `pwrite`/`fsync` glue. Needs a
   design doc; largest single item.

Items 1-3 are the highest win-per-cost and are mostly unblocked in this
sandbox; items 5 and 8 need the parliament corpus / a design doc first.

---

## Appendix — measurement provenance

- Binary: `git show HEAD:bin/linux-x86_64/factoidal` (HEAD `b4249260`),
  extracted to scratch; chosen because working-tree `bin/linux-x86_64/*`
  are locally modified mid-rebuild.
- Corpora: `examples/wikidata/subsets/lifesci-kgx/data/{gene,medication}.ttl`;
  `tests/…`-adjacent g21 fixture from a prior session's scratch.
- Timer: `resource.getrusage(RUSAGE_CHILDREN).ru_maxrss` (KiB→MiB) +
  wall-clock, `perf-review/timer.py`.
- COTTAS builds via `_tmp.junk/pycottas-venv` + `tools/corpus_pipeline.py
  materialize-nq-cottas-corpus --parser python`.
- Encodings inspected with DuckDB `parquet_metadata()` (pyarrow absent).
- Could-not-measure items, stated in-line: full parliament on-disk latency
  (corpus absent), F\*-front-end import (`factoidal-dump-nq.byte` SIGABRT
  in this tree), in-memory-vs-on-disk head-to-head (on-disk reader fails).
