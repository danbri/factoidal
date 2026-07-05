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
