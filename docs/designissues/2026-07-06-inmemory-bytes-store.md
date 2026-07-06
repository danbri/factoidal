# In-memory bytes store: can in-memory SPARQL be more byte-efficient?

**Date:** 2026-07-06.
**Owner question (verbatim):** "consider whether in memory sparql can be
made more byte efficient by exploiting new design eg in memory files?"
**Scope:** measurement + design only. No `.fst`/OCaml/build changes.
Reads freely across the tree; writes only this file plus scratch scripts
under this session's scratchpad (not committed). Composes with, but does
not touch, the in-flight native `RDF.CottasStore.BaseWriter.fst`
(`serialize_cottas : list cottas_quad -> Tot (list u8)`) landing in
parallel this session.

**Corpus:** the vendored Wikidata life-sci KGX subset
(`examples/wikidata/subsets/lifesci-kgx/data/gene.ttl`, 888,949 triples,
17,363,312 bytes Turtle), the same corpus
[`2026-07-05-disk-backed-db-perf-review.md`](2026-07-05-disk-backed-db-perf-review.md)
uses, for direct comparability. A pre-built COTTAS artifact for it
already existed in this sandbox at
`.claude-runs/repro/corpus-gene/gene/v1/data.cottas` (1,012,509 bytes);
this task copies it, never mutates it in place.

**Method note.** Several repo binaries (`bin/linux-x86_64/factoidal` and
siblings) were mid-rebuild by other sessions in this sandbox for the
entire duration of this task (`git status` showed them modified
throughout; no `.build-running` lock was present, so this was a live
F*→OCaml→C fan-out, not a stale lock). To avoid reading a
partially-written binary or perturbing a concurrent build, every
measurement below runs against **copies** made once at the start into
`/tmp/.../scratchpad/bytes-store/` (`factoidal`, `gene.ttl`, and the
gene `data.cottas`) — the repo's `bin/` and `.claude-runs/` trees were
read, never written, by this task. Peak RSS via
`resource.getrusage(RUSAGE_CHILDREN).ru_maxrss)` (`tools/bench_rusage_
run.py`, reused as-is) for one-shot CLI runs, and `/proc/<pid>/status`
`VmHWM` for the long-lived `factoidal serve` processes used in the
tmpfs-vs-disk comparison. All server processes were killed at the end
of this task; nothing was left running.

---

## 1. Measurements

### 1.a Representation size, three ways (gene corpus, 888,949 triples)

| Representation | Bytes | Bytes/quad | Command |
|---|---:|---:|---|
| Turtle (prefixed, as shipped) | 17,363,312 | 19.5 | `wc -c gene.ttl` |
| Raw N-Quads (expanded, cited) | ~116,000,000 | 130.5 | perf-review doc §2.a |
| COTTAS/Parquet base file | 1,012,509 | **1.14** | `ls -la data.cottas` (pre-built, this sandbox) |
| COTTAS base + all 10 sidecars (measured this session — dict/presence×4 cols + `.po.presence` + `.p.offsets`) | 14,659,603 | 16.5 | `du -cb gene-cottas/` after a `factoidal serve --data-cottas` cold boot |

The base-file number (1.14 B/quad) matches the perf-review doc's own
figure exactly (`1,012,509 / 888,949`). The sidecar total here
(13,647,094 B, 10 files) is close to but not identical to that doc's
13,642,038 B — expected, since sidecar byte-for-byte content depends on
build/companion-writer versions that moved under both sessions this
week; the order of magnitude and the point below are unaffected.

### 1.b In-memory heap cost (the `RDF.Indexed` bucket-map store)

Fresh `factoidal query --data gene.ttl -e '<query>'` process each run —
this is the ONLY way to exercise the heap path today; there is no
persistent "load once, serve many" mode for a plain `--data` graph in
this CLI (only `factoidal serve --dataset` keeps one hot, not measured
separately here since the cost driver, `RDF.Indexed.build_indexed`, is
identical either way). 3 warm runs each, `tools/bench_rusage_run.py`:

| query | wall (s) | peak RSS | bytes/triple |
|---|---:|---:|---:|
| `SELECT (COUNT(*) AS ?c) WHERE { ?s ?p ?o }` | 6.46–6.54 | **44.9 MiB** (45,968 KB, all 3 runs identical) | 53 |
| `?s rdf:type ?o LIMIT 5` | 25.6–26.2 | 743.9–744.0 MiB | 878 |
| point lookup (`wd:Q100085837 ?p ?o`) | 25.8–26.6 | 743.7–744.0 MiB | 877 |
| bound-p (`?s wdt:P682 ?o`, 4 rows) | 25.6–26.0 | 743.7–744.4 MiB | 877 |

**Finding not anticipated by the brief: `COUNT(*)` is now cheap.** The
perf-review doc (yesterday) measured `SELECT (COUNT(*))` at 731 MiB —
full materialization. Today's build answers it in 45 MiB, a ~16×
reduction, evidently because of `SPARQL.Plan.Streamable`'s streaming-
shapes path (`RDF.Store.Capabilities.fst`'s `scf_streaming_shapes` flag,
landed this week) now covers plain `COUNT(*)`. Every OTHER query shape
here — anything that needs the triple to be found by pattern, not just
counted — still pays the full materialize-and-index cost, landing at a
**consistent 877–878 bytes/triple** across three structurally different
queries (LIMIT scan, point lookup, bound-predicate). This is the number
to treat as "today's in-memory floor": `RDF.Indexed.build_indexed`
allocates the same `indexed_graph` (§2 below) regardless of which
triple-pattern-shaped query eventually runs over it.

**Structural accounting for the 877 B/triple (analytic, not
instrumented — see the "not done" note at the end of §1.b).**
`RDF.Indexed.fsti`'s `indexed_graph` (lines 126-138) holds `ig_triples`
plus six bucket maps (`ig_pred/ig_subj/ig_obj/ig_sp/ig_po/ig_so`), each
`bucket_map a = list (string * list a)` — a plain association list, not
a hashtable. `RDF.Triple.fsti:23` — `type triple = { s : subject; p :
wf_iri; o : rdf_term }` — and `RDF.Term.fsti`'s `subject`/`rdf_term` are
boxed sum types wrapping raw OCaml strings (`iri = string`,
`wf_literal` a 3-field record). On a 64-bit OCaml runtime (8-byte
words, no compaction by default):

- One `triple` record is allocated ONCE and shared by pointer across
  every list it appears in (OCaml doesn't copy on `cons`) — so the
  per-triple marginal cost is: the record block itself (1 header + 3
  fields = 32 B) + the `subject`/`rdf_term` variant wrapper blocks
  (16 B each) + the raw strings (`8 + 8·⌈(len+1)/8⌉` B each: subject
  IRI, predicate IRI, object lexical form/datatype, none shared or
  interned across triples even when the same predicate string
  recurs — the Turtle parser expands each occurrence to a fresh OCaml
  string) — roughly 250–380 B depending on term lengths and whether the
  object is a literal (extra datatype-IRI string + record box) or an
  IRI.
- PLUS list-cons overhead for bucket-map membership: a triple with a
  non-literal object is `cons`'d onto 7 lists (`ig_triples` + 6
  buckets); one with a literal object skips `ig_obj`/`ig_po`/`ig_so`
  (`RDF.Indexed.fsti:151-155`'s `term_to_key_opt` returns `None` for
  literals) and lands in only 4. Each cons cell is 1 header + 2 fields
  = 24 B. That's 96–168 B of pure list-spine overhead per triple, on
  top of the term bytes above.

Summing gives a naive lower bound around 350–400 B/triple — roughly
half the measured 877. The gap is real overhead this estimate doesn't
capture: no string interning across the ~50–100 distinct predicate
values (a term dictionary would collapse this — see §3.6), no major-
heap compaction (OCaml's default allocator leaves free-list
fragmentation as memory is recycled during the O(N log N)
`build_bucket` sort-and-group pass, `RDF.Indexed.fsti:109-112`), and
transient doubling during that same build pass (the sorted
intermediate list is live alongside the pre-sort list until the fold
completes, once per one of the six buckets). **Not done: a `Gc.stat`-
instrumented breakdown** (would need a small standalone OCaml harness
linking the extracted modules with debug prints — safe to build in
isolation, but out of scope for a same-session, no-new-OCaml
measurement task, and risky to attempt against binaries mid-rebuild by
siblings). The measured 877 B/triple is the number to design against;
the structural estimate above explains DIRECTIONALLY where it goes,
not to the byte.

### 1.c On-disk COTTAS: cold-open cost is dictionary materialization, not file size

Ran two persistent `factoidal serve --data-cottas <path>` processes
against the SAME 1,012,509-byte `data.cottas` (no pre-built sidecars,
so both pay a full cold-open): one pointed at a copy on this sandbox's
regular filesystem (`/tmp/.../gene-cottas/data.cottas`, `ext4`), one at
a copy on `/dev/shm` (`tmpfs`). Boot log (`prewarm_via_companions`,
`bin/factoidal-http/factoidal_http.ml`) reports the dictionary sizes it
decoded: `subjs=91871 preds=6 objs=75142 graphs=1` — **167,020 distinct
terms** for 888,949 quads (a 5.3:1 quad:term ratio on this corpus).

| store | cold boot wall | peak RSS (`VmHWM`) | on-disk footprint | "B/quad"-equivalent |
|---|---:|---:|---:|---:|
| ext4 copy | 99.9 s | 231,272 KB (225.9 MiB) | 14.66 MB | 266 |
| tmpfs copy | 99.3 s | 226,904 KB (221.6 MiB) | 14.66 MB (in RAM already) | 261 |

Both numbers are within 2% — **storage medium made no measurable
difference**, cold boot and warm query alike (§1.d). That is not a
tmpfs-approximates-a-future-design footnote; it is because the existing
reader ALREADY treats the file as an opaque byte blob cached once in
process memory (see §2.1) — tmpfs vs ext4 only changes the cost of that
FIRST read, and for a 1 MB file that cost is noise next to the ~100 s
`prewarm_via_companions` dictionary-decode pass.

**The important number here: on-disk-open uses ~226–231 MiB vs the
heap store's ~744 MiB for the SAME corpus — a ~3.3× reduction,
available TODAY, with zero new code, just by using `--data-cottas`
instead of `--data`.** But it is not "bytes held for querying" in the
sense the owner's question asks about: `cottas_ondisk_handle`
(`RDF.CottasStore.fst:37-78`) decodes and materializes, at open time,
**four full representations per column** — `coh_subjects` (typed
`list subject`), `coh_subj_revmap` (canonical-key → id), `coh_subjects_
raw` (raw column-token strings), `coh_subj_raw_revmap` (raw-token → id)
— repeated for predicates/objects/graphs. That's ~1,380 B of live heap
per distinct term (231,272 KB·1024 / 167,020 terms ≈ 1,383), not per
quad. It scales with **term cardinality**, which is why gene's 5.3:1
quad:term ratio gives a 3.3× win over the heap store today — a corpus
with less term reuse (wide provenance metadata, random identifiers)
would see this ratio compress toward 1:1 and the win shrink
correspondingly. This eager, 4-way-redundant dictionary is realized by
`prewarm_via_companions`/`Cottas_ondisk_runtime.load_handle`
(`experimental_ocaml_glue/cottas_ondisk_runtime.sh`); a **lazy**
per-column dictionary already exists in the tree
(`RDF.CottasStore.LazyDict.fst`, issue #254/"Bet7", populate-on-first-
lookup) but the HTTP server's boot path calls the eager prewarm anyway,
trading memory for avoiding first-query latency. This is the layer
where "in-memory-bytes design" and "reduce the dictionary's constant
factor" are two DIFFERENT, complementary levers — see §3.6.

### 1.d Warm query latency, ext4 vs tmpfs (the tmpfs-as-buffer-proxy prototype)

Same two servers, 3 warm HTTP `/query` requests each (`curl` timed
externally), after the ~100 s cold boot above:

| query | ext4 run1 / run2 / run3 | tmpfs run1 / run2 / run3 |
|---|---:|---:|
| `COUNT(*)` | 57.4 / 52.0 / 63.2 ms | 55.5 / 46.4 / 45.9 ms |
| `?s rdf:type ?o LIMIT 5` | 2,192 / 22.0 / 20.7 ms | 2,268 / 21.1 / 21.7 ms |
| point lookup | 719.8 / 43.0 / 35.1 ms | 678.2 / 34.8 / 35.0 ms |
| bound-p (`wdt:P682`, rare) | timeout(>15,000) / 15,014 / 11,359 / **37.6** ms | timeout(>15,000) / 15,014 / 11,458 / **39.4** ms |

Correctness: `COUNT(*)` = 888,949 on both stores; the bound-p query
returns the same 4 rows; the point lookup returns identical bindings —
matches the sibling review's own correctness checks.

Two findings:

1. **ext4 and tmpfs are indistinguishable within noise, on every query,
   at every warm/cold state.** This validates the brief's premise: for
   this reader, "the byte source is a real file" and "the byte source
   is a tmpfs file" cost the same, because — as the runtime glue's own
   comment says (`parquet_footer_runtime.sh:76-80`) — "the path IS the
   region handle, the cache IS the mapped pages": the first
   `parquet_read_*` call for a path slurps the whole file into an
   OCaml string once (`__mim2_file_bytes_cache`), and every subsequent
   probe is a `String.sub` against that cached string, never touching
   the filesystem again. tmpfs only saves the ONE-TIME initial
   `open_in_bin`/`really_input_string`, which is sub-millisecond for a
   1 MB file either way. This is direct evidence that an in-memory
   buffer backend would perform IDENTICALLY to today's on-disk reader
   for files that fit in RAM (which they always do, once read once) —
   the approximation the brief predicted holds, and holds exactly, not
   approximately, for this reason.
2. **An unexplained, reproducible-on-both-stores cold-start tax on the
   bound-predicate query**: the FIRST TWO invocations of
   `?s wdt:P682 ?o` (against the SAME warm server, after `rdf:type` and
   the point lookup had already gone warm) took 11.4–15.0 s before the
   THIRD invocation dropped to 37–39 ms — identically on ext4 and
   tmpfs, which rules out storage medium as the cause. This looks like
   a per-predicate (not per-query-shape, since `rdf:type` warmed on its
   OWN first call) lazy structure that needs 2 misses before it's
   populated — plausibly `RDF.CottasStore.LazyDict`'s "all four views
   populate together on the first lookup of any kind" (banner, lines
   12-13) interacting with a SEPARATE cache that needs its own first
   touch. Filed as an open question in §5, not chased further here —
   orthogonal to the disk-vs-memory question this task was scoped to
   answer, but material to any latency SLA a buffer-backed design
   would want to state.

### Summary table (as requested: representation × {RSS, COUNT, point-lookup, bound-p})

| representation | peak RSS | `COUNT(*)` | `?s rdf:type ?o LIMIT 5` | point lookup | bound-p (rare) |
|---|---:|---:|---:|---:|---:|
| in-memory heap (`RDF.Indexed`) | 744 MiB | 6.5 s (streamed) | 26 s (materialize) | 26 s | 26 s |
| on-disk COTTAS, ext4, cold boot then warm | 226 MiB | 52–63 ms | 21–22 ms warm (2.2 s cold) | 35–43 ms warm (720 ms cold) | 37.6 ms warm (11–15 s ×2 cold) |
| on-disk COTTAS, tmpfs, cold boot then warm | 222 MiB | 46–56 ms | 21–22 ms warm (2.3 s cold) | 35–35 ms warm (678 ms cold) | 39.4 ms warm (11–15 s ×2 cold) |

The heap store's "wall" column is a single fresh-process cost (no warm
state exists in the CLI today); the on-disk numbers separate cold
(first touch, pays dictionary/cache population) from warm (repeat
query, the number that matters for a server under load).

---

## 2. The design: an in-memory-bytes backend

### 2.1 The byte-source abstraction already exists — it's an accident of the cache design, not a deliberate seam

`Parquet.Footer.fst:27-31` declares two `assume val`s:

```fstar
assume val parquet_read_tail_hex :  path:string -> count:nat -> Tot (option string)
assume val parquet_read_range_hex : path:string -> start:nat -> count:nat -> Tot (option string)
```

Their OCaml realization (`experimental_ocaml_glue/parquet_footer_
runtime.sh`) treats `path` as **an opaque cache key**, not a filesystem
call site: `__mim2_load_file_bytes` (line 97) checks a
`(string, string) Hashtbl.t` FIRST and only falls through to
`Sys.file_exists`/`open_in_bin` on a cache miss. Every one of the ~15
`probe_parquet_*` call sites in `Parquet.Footer.fst`, and everything in
`RDF.CottasStore.fst` built on top (all of it threads `h.coh_path`
as a plain string argument — grep count: 30+ call sites,
`RDF.CottasStore.fst:506-1308`), reaches the file exclusively through
this cache. **This means an in-memory-bytes backend needs no new
`assume val` and no F\* signature change**: pre-populate
`__mim2_file_bytes_cache` under a synthetic key (e.g. `"mem:<n>"`) with
the `serialize_cottas`-produced byte string, and every existing probe,
decoder, and query path works unmodified, because as far as they can
tell they're reading a file that happens to already be cached.

Two things DO need a few lines of new glue, both rule-#11-acceptable
(pure I/O realization, no new decode/query logic):

1. A `register_memory_buffer : string -> string -> unit` entry point in
   `parquet_footer_runtime.sh` that does
   `Hashtbl.replace __mim2_file_bytes_cache handle bytes` — bypassing
   the `Sys.file_exists` check entirely for a synthetic handle (there is
   no file to exist).
2. `cottas_ondisk_open`'s own OCaml realization
   (`cottas_ondisk_runtime.sh:597-612`, `Cottas_ondisk_runtime.
   load_handle`) does its own file access to build the dictionary
   (§1.c/§3.6) — this needs to accept the same synthetic handle and
   route its column-scan reads through `parquet_read_range_hex`
   (already true — `load_handle` calls the F\*-extracted probes, not
   raw `open_in_bin`, per the module's own banner: "the OCaml glue at
   `cottas_ondisk_runtime.sh` now does only ONE thing: at open() time,
   read 4 columns ... via the F\* runtime"), so this should already
   work once (1) is in place — worth confirming empirically before
   relying on it, not assumed here.

### 2.2 What plugs where: `RDF.Store.Capabilities` / `caps_of_cottas`

`RDF.Store.Capabilities.Cottas.fst`'s `caps_of_cottas` (landed this
week, stage U1/U2 of
[`2026-07-06-unified-store-architecture.md`](2026-07-06-unified-store-architecture.md))
already takes a `cottas_ondisk_store` — a record whose ONLY path-shaped
field is `cods_handle.coh_path : string` — and builds a `store_caps`
from it (`sc_solve`/`sc_estimate`/`sc_count_exact`/etc., all wrapping
existing `cottas_ondisk_*` entry points 1:1, `RDF.Store.Capabilities.
Cottas.fst:31-91`). **Nothing in `caps_of_cottas` or the `store_caps`
record cares whether `coh_path` names a real file or a synthetic
in-memory handle** — the seam already generalizes for free. A new
`caps_of_cottas_bytes : list u8 -> cottas_ondisk_graph_scope -> ML
store_caps` (or an OCaml-side helper wrapping the existing
`caps_of_cottas` after registering the buffer) is the entire new public
surface this design needs at the F\*/seam layer: convert bytes to a
handle, open it, hand the result to the SAME `caps_of_cottas`.

### 2.3 Composition with the in-flight native writer

The sibling work landing in parallel this session,
`RDF.CottasStore.BaseWriter.fst`'s
`serialize_cottas : list cottas_quad -> Tot (list u8)`, is exactly the
producer half of this design: **parse → `serialize_cottas` → `list u8`
→ `register_memory_buffer` → `cottas_ondisk_open` (synthetic handle) →
`caps_of_cottas` → query, entirely in one process, no file ever
touches a disk.** This is a new capability, not just a memory
optimization: today, going from parsed RDF to a queryable COTTAS store
requires shelling out to `pycottas`/DuckDB (Python) to write a real
file, then opening it. With a native F\* writer AND an in-memory-bytes
reader, `factoidal query --data X.ttl --via-cottas` (a new CLI mode,
not built here) could parse, serialize, and query through the compact
columnar path with no external process and no filesystem round-trip —
useful independent of the memory story for short-lived CLI queries
where writing 1 MB to disk just to immediately mmap it back is pure
overhead.

### 2.4 What this buys

- **Memory, for read-mostly workloads on large graphs**: today's
  on-disk-open path already gets 3.3× under the heap store (§1.c) with
  zero code change; the buffer-backed design's marginal ADD is
  eliminating the disk round-trip for data that either (a) never had a
  file (§2.3's parse-and-hold case) or (b) is small enough to hold
  entirely in RAM as bytes rather than as `.cottas` + `.nq` +
  `.factbin` on a mounted filesystem (relevant for sandboxed/ephemeral
  environments — CI runners, serverless functions — where a real
  filesystem is either absent or wiped between invocations).
- **One reader, verified once — the clean-architecture argument.**
  Because the seam generalizes for free (§2.1/§2.2), there is no
  separate "in-memory COTTAS reader" to write, test, or keep in sync
  with the on-disk one. The F\* proof burden for `Parquet.Footer.fst`
  and `RDF.CottasStore.fst` is paid exactly once and covers both
  targets. This is the strongest argument in the whole design — it is
  not a new engine, it is the SAME engine pointed at a different byte
  source.
- **Dictionary sharing.** If two queries (or two requests in a
  long-lived server) open the SAME bytes, the existing
  `__mim2_file_bytes_cache` is keyed by handle string — a synthetic
  handle reused across opens shares the cached bytes for free, same as
  two processes/threads opening the same real path today.
- **The write/delta-overlay story composes unchanged.** `RDF.Store.
  Capabilities.fst`'s `store_write_caps`
  (`swc_apply_delta : list DL.delta_entry -> ML store_caps`) is layered
  ON TOP of a base `store_caps`, not baked into `caps_of_cottas` itself
  — the durable-UPDATE delta log (`RDF.Store.Columnar.DeltaLog.fst`)
  already composes with `GB_CottasOnDisk` via merge-on-read
  (`SPARQL11.Store.fst`'s `--delta-log` wiring, `factoidal query
  --delta-log`/`factoidal serve --delta-log --rw`). A buffer-backed
  base store slots into the identical overlay: the delta log itself
  stays a real, fsync'd, append-only file (durability requires a real
  device — an in-memory delta log is a contradiction in terms for a
  durable-UPDATE claim), but the READ-MOSTLY base it overlays can be
  bytes-in-RAM. Nothing about the overlay mechanism inspects what kind
  of `store_caps` it wraps.
- **The js/wasm story is the actual kicker, and it is not
  hypothetical — it is ALREADY the shipped architecture for the
  browser build.** `build-ocaml.sh:1318-1328`'s own comment: "The
  `js_of_ocaml` build can open COTTAS/Parquet artifacts in the browser
  via: the Zstd JS shim ... [and] the `js_of_ocaml` pseudo-FS for
  `/`-rooted local paths." `Parquet_Footer.ml`, `Parser_BallyhooCOTTAS.
  ml`, and the full `RDF_CottasStore*.ml` family (12 modules, lines
  1356-1378 of the JS module list) are ALREADY in the `js_of_ocaml`
  build. `js_of_ocaml`'s public `Sys_js.create_file : name:string ->
  content:string -> unit` (the standard API for this exact pattern —
  not confirmed as already CALLED anywhere in `bin/npm-entry/entry_
  jsoo.ml`/`bin/factoidal-serve/factoidal_serve_jsoo.ml` in this repo;
  the build-ocaml.sh comment asserts the CAPABILITY exists via the
  linked runtime, not that a call site uses it yet) is exactly the
  browser-side equivalent of §2.1's `register_memory_buffer`: fetch the
  `.cottas` bytes over HTTP, hand them to `Sys_js.create_file`, then
  `open_in_bin` that virtual path — the OCaml stdlib calls inside
  `Parquet.Footer`'s realization don't know or care that there is no
  real disk underneath. **Browser memory is the tightest constraint in
  this whole design space** (a phone browser tab has low-hundreds-of-MB
  before the tab gets killed, not the multi-GB budget a server VM has);
  holding COTTAS bytes (1.14 B/quad) instead of `RDF.Indexed` heap
  triples (877 B/quad, §1.b) in that budget is a ~770× density
  difference for the SAME data, which is the difference between "the
  UK Parliament corpus fits in a browser tab" and "it does not, by two
  orders of magnitude." This is not a new architectural bet — it is
  documenting and completing a design the `build-ocaml.sh` JS module
  list already committed to in April 2026 (per its own "Phase 2
  (2026-04-20)" comment) but that no `bin/` entry point has finished
  wiring end-to-end yet (confirmed: no `Sys_js.create_file`/`register_
  file` call site found in `bin/npm-entry/` or `bin/factoidal-serve/
  *_jsoo.ml` in this tree today).

### 2.5 What this costs

- **Term materialization per access, not O(1) heap-pointer navigation.**
  Every matched row still round-trips through `cottas_ondisk_rows_tok_
  to_triples` (parse the column token back into a typed `rdf_term`) —
  the buffer removes the disk-vs-RAM distinction, not the decode cost.
  For a query touching many rows this is real CPU, not memory; §1.d's
  warm-query numbers (20–63 ms on an 889 K-quad corpus) show it is a
  small constant today, but it is a per-row constant the heap store
  doesn't pay (a heap `triple` is already a live OCaml value; a COTTAS
  row is bytes that must be re-parsed into one).
- **The dictionary cache is what makes this affordable, and it is the
  SAME dictionary the on-disk path pays for today (§1.c) — a buffer
  backend does not reduce it, only removes the disk round-trip to
  build it once.** If the eager-prewarm dictionary stays as-is, a
  buffer-backed store on a term-cardinality-heavy corpus (low quad:term
  ratio) inherits the SAME ~1,380 B/term cost measured here — §3.6
  below is the lever that actually shrinks this, and it is orthogonal
  to "disk vs memory."
- **No O(1) heap-pointer navigation — the current selective-walk
  performance ceiling.** `RDF.Indexed`'s bucket maps give an exact
  bucket lookup by key; COTTAS's row-group walk (even with the offset
  index / presence bitmaps) is a decode-and-filter over whichever row
  groups survive pruning, not a direct index probe. The Lamed3 offset
  index and the in-flight pushdown work (perf-review doc §"Row-group
  offset table", 2026-07-06, already landed as of this session) close
  most of this gap for bound-predicate patterns but the ceiling is
  real: this backend will not beat a well-tuned in-memory index on
  point lookups by predicate/subject at small scale, only on MEMORY
  FOOTPRINT at large scale.
- **Cold-start cost (§1.d finding 2, the 11–15 s bound-p tax) is
  unexplained and needs to be understood before this backend is
  offered as a latency-sensitive default** — a buffer-backed store
  inherits whatever this is exactly, since it lives in the SAME code
  path (§2.1).

---

## 3. Recommendation and staging

**Yes, worth building — for large, read-mostly graphs, staged behind
the item that makes it worth building on native (dictionary cost) and
the item that makes it usable on browser (a real call site).**
`RDF.Indexed` is not being replaced; small graphs and update-heavy
workloads stay on the heap store (§3.5 below explains why explicitly).

### Stage list

1. **Confirm the seam holds** (half a day, no F\* change): add
   `register_memory_buffer` to `parquet_footer_runtime.sh` (§2.1 item
   1), verify `cottas_ondisk_open` on a synthetic handle round-trips a
   small fixture (`tests/local/data/cottas_sample.nq`'s pre-built
   artifact, read as bytes and re-registered under a fake path) against
   the SAME query results as the real-file path. This is the empirical
   check §2.1 item 2 above flags as "not assumed here" — do it first,
   because if `cottas_ondisk_open`'s dictionary-build phase turns out
   to do its OWN raw file I/O outside the `parquet_read_*` cache
   (plausible — `Cottas_ondisk_runtime.load_handle` predates the
   Parquet.Footer Phase-B lift and may have legacy direct-file-read
   paths), that's a second glue point to patch, not zero.
2. **`caps_of_cottas_bytes` at the seam** (§2.2): a thin OCaml/glue
   wrapper — register bytes, open, delegate to the existing
   `caps_of_cottas`. No new F\* logic; the interesting design work
   (§2.1/§2.2) is already done by this point.
3. **Wire `serialize_cottas` → buffer → query, native CLI, as a new
   mode** (§2.3): `factoidal query --data X.ttl --via-cottas-mem` or
   similar — parse, serialize in-process, hold bytes, query. This is
   the first end-to-end proof the composition works and gives a REAL
   bytes/quad-in-RAM number to replace §1.c's disk-open number (which
   still pays the eager dictionary; this stage's number should be
   close to it, since the dictionary cost is unchanged — see stage 4).
4. **Shrink the dictionary cost** (the actual memory win beyond what
   on-disk-open already gets): either (a) stop calling
   `prewarm_via_companions` eagerly at boot and let
   `RDF.CottasStore.LazyDict` (already in the tree, §1.c) populate
   per-column on first touch — a config/wiring change, not new F\*
   logic — or (b) collapse the 4-way redundant per-column
   representation (typed list + raw list + 2 revmaps) that
   `cottas_ondisk_handle` carries today (§1.c) into one canonical
   representation with the other three derived/cached lazily. (a) is
   commit-sized; (b) is a real `RDF.CottasStore.fst` refactor and
   should get its own design doc if picked up.
5. **The browser call site** (§2.4's "kicker"): wire `Sys_js.create_
   file` (or the wasm_of_ocaml equivalent, once that track — 
   [`2026-05-07-c-build-and-roaring-plan.md`](2026-05-07-c-build-and-roaring-plan.md)
   — reaches Parquet.Footer) into the actual demo fetch path
   (`bin/npm-entry/entry_jsoo.ml` or the site's demo JS), fetch a
   `.cottas` artifact over HTTP, and measure real browser heap (not a
   proxy) for a corpus at the scale where this matters — the UK
   Parliament COTTAS bundle (~325 MiB, per the perf-review doc's §
   corpus caveat, not present in this sandbox) is the right target,
   not gene. This stage is where the "two orders of magnitude" claim
   in §2.4 gets an actual measurement instead of an arithmetic
   projection.
6. **Understand the cold-start tax** (§1.d finding 2) before offering
   this as a latency-sensitive default for anything — it currently
   reads as "some predicates cost 11-15 seconds the first two times,"
   which is a correctness-adjacent surprise (not wrong, just
   unpredictably slow) regardless of byte source.

### Stage outcomes (implemented 2026-07-06, same day, this round)

Stages 1-4 landed; measured results below. Stage 5 (browser call
site) and stage 6 (cold-start tax) remain open.

| stage | outcome | evidence |
|---|---|---|
| 1. Confirm the seam | **Held, with zero extra glue points.** `register_memory_buffer` added (`experimental_ocaml_glue/parquet_footer_zz_register_memory_buffer.sh`, one `Hashtbl.replace` on the existing Mim2 cache). The §2.1-item-2 worry did NOT materialise: `cottas_ondisk_open` on a synthetic handle worked with no second patch — `load_handle`'s column scans reach bytes exclusively through `parquet_read_*`, as the module banner claimed. | `tests/unit/cottas_memory_buffer_unit.ml`: 73 pass, 0 fail (out of 73) — file-path vs memory-handle open of the same fixture bytes, identical solve/solve_limited/estimate/count_exact across the full 8-shape bound matrix, both graph scopes, plus named-graph inventory and re-registration idempotency. |
| 2. Capability seam | **No new F\* surface needed, as §2.2 predicted.** Composing `register_memory_buffer` + `cottas_ondisk_open` + the EXISTING `caps_of_cottas` at the call site IS the "(name, bytes) → store_caps" builder; a separate `caps_of_cottas_bytes` would have wrapped exactly that composition and was not added. | `tests/unit/store_capabilities_unit.ml` buffer-scope block: every `store_caps` field over the buffer handle equals the same field over the real file, both scopes, full shape matrix; file total now 521 pass, 0 fail (out of 521). |
| 3. CLI composition + delta overlay | **`factoidal query --data-cottas-mem FILE` shipped** (`bin/factoidal-cli/factoidal_cli.ml`: read file → `register_memory_buffer` under `mem:<n>:<path>` → push the synthetic handle onto the ordinary `--data-cottas` list; every downstream consumer unchanged). The `--delta-log` overlay composes over the buffer base unmodified, confirming §2.4's claim end-to-end. | `tests/local/inmemory_bytes_store_stage3.sh`: 23 pass, 0 fail (out of 23) — SELECT/ASK/GRAPH/bound-p identical file-vs-mem; the durable-UPDATE scenario batch gives identical post-delta answers over `--data-cottas` and `--data-cottas-mem`; missing-file fails loudly. |
| 4. Dictionary cost | **Two findings.** (a) The "make prewarm lazy per column" half already shipped long before this doc (Bet7, commit 7ecf720): `cottas_ondisk_open` is footer-only (~0.02 s) and all four `coh_*` handle lists are EMPTY on the lazy path — §1.c's 226 MiB is `factoidal serve`'s own eager `prewarm_via_companions` boot choice, which plain `factoidal query` never pays. (b) The profiled remaining cost was NOT the retained dictionary but the populate TRANSIENT: `collect_distinct` materialised the whole column (888,949 `string option` cells) via `probe_parquet_column_decode_all_row_groups` before deduping. Fixed by streaming per row group through the same F\*-verified per-rg decoder (`cottas_ondisk_runtime.sh`, memory layout only, identical values/order/failures). | RSS table below; `tests/local/cottas_lazy_dictionary_stage4.sh`: 12 pass, 0 fail (out of 12), incl. per-column-laziness trace pins (predicate-bound query populates predicates ONLY; graph dict populates at dataset construction by design, finding 0 named graphs on gene). |

**Peak RSS, gene corpus (888,949 quads, 1,012,509-byte artifact),
one-shot `factoidal query`, max of 3 runs, `bench_rusage_run.py`:**

| query shape | before streaming fix | after | `serve` eager-prewarm (§1.c) | heap store (§1.b) |
|---|---:|---:|---:|---:|
| open + `COUNT(*)` | 86,328 KB (84.3 MiB) | **56,000 KB (54.7 MiB)** | 231,272 KB (225.9 MiB) | 45,968 KB |
| open + point lookup (subject-bound) | 156,408 KB (152.7 MiB) | **139,724 KB (136.4 MiB)** | 231,272 KB | ~744 MiB |
| bound-p (`rdf:type` LIMIT 5) | 121,812 KB (119.0 MiB) | **95,048 KB (92.8 MiB)** | 231,272 KB | ~744 MiB |
| buffer mode (`--data-cottas-mem`) `COUNT(*)` | — | **55,932 KB (54.6 MiB)** | — | — |
| buffer mode point lookup | — | **139,664 KB (136.4 MiB)** | — | — |

Process baseline (same binary, 1-quad fixture, `COUNT(*)`): 11,540 KB
— subtract it for marginal-cost accounting.

**Bytes per quad held in memory (whole-process peak RSS ÷ 888,949
quads; marginal = after subtracting the 11,540 KB process baseline):**

- open + `COUNT(*)`, buffer mode: **64.4 B/quad** (marginal 51.1) —
  13.6× under the heap store's 877 B/quad, 4.1× under the
  serve-eager 266 B/quad-equivalent.
- open + point lookup, buffer mode: **160.9 B/quad** (marginal 147.6)
  — 5.5× under the heap store. Above the 100 MiB absolute target on
  this corpus (136.4 MiB): the residual is the retained subject
  dictionary (91,871 distinct tokens × {token string + typed copy +
  3 hashtable slots}) plus the page cache's decoded columns for the
  one row group the LIMIT-pushdown search touched. Getting THIS
  shape under 100 MiB needs the bound-side encode to stop
  round-tripping through the corpus-wide dictionary (serialize the
  bound term to its column token directly in F\*, the same way the
  output side already went tok-direct at 9750eb7) — follow-up, its
  own commit.
- Buffer mode vs file mode is within 0.2% on every shape (the image
  IS the cache entry either way, §2.1) — the buffer backend costs
  nothing over the on-disk reader, exactly as §1.d predicted.

### What this means for `RDF.Indexed`'s future

**Complement, not replacement**, for two concrete reasons visible in
this task's own numbers:

- **Update-heavy workloads.** `caps_of_indexed`
  (`RDF.Store.Capabilities.fst:294-310`) sets
  `scf_supports_update = true` because rebuilding an `indexed_graph`
  from a mutated triple list is O(N log N) and cheap at small-to-
  medium scale; a COTTAS artifact (buffer-backed or on-disk) is
  `scf_supports_update = false` at the base layer (§2.4's delta-overlay
  paragraph) precisely because Parquet is write-once by format. A
  workload doing frequent small mutations wants the heap store's direct
  rebuild, not a base-plus-delta-log composition, until the delta log
  itself grows large enough to need its own compaction discipline
  (`factoidal compact`, already built for the on-disk case).
- **Small graphs.** At gene's scale (889 K quads), the heap store's
  6.5 s/45 MiB `COUNT(*)` is already fine; the entire question this
  task investigates only bites at a scale where 744 MiB (or the
  multi-GB the perf-review doc projects for parliament-scale data,
  §1.b of that doc) is the actual constraint — a few thousand to a few
  hundred thousand triples do not need this.

### Open decisions

1. **Whether `caps_of_cottas_bytes` takes ownership of the byte buffer
   or borrows it** — matters for the native embedding case (§2.3: does
   the CLI process free the `list u8`/`string` after handoff, or does
   the cache own it for the process lifetime the way `__mim2_file_
   bytes_cache` already does for real paths?). Affects whether a
   long-running server that opens MANY short-lived in-memory stores
   (e.g. one per request, each a different small graph) leaks the
   cache — `__mim2_file_bytes_cache` today is a process-lifetime
   Hashtbl keyed by path with no eviction, which is fine for a handful
   of real files opened once at boot and wrong for N synthetic handles
   created per request.
2. **Whether stage 4(a) (stop eager prewarm, rely on `LazyDict`) is
   safe to flip as a config default today**, given §1.d's unexplained
   cold-start tax (finding 2) — turning MORE things lazy without
   understanding the EXISTING lazy path's occasional 11-15 s cost is
   the wrong order of operations.
3. **Whether the wasm_of_ocaml track (Roaring-adjacent, cited plan)
   needs its OWN `Sys_js`-equivalent** or whether `wasm_of_ocaml`
   inherits `js_of_ocaml`'s pseudo-FS story for free — not checked in
   this task, gating item for stage 5's wasm variant specifically (the
   jsoo variant's story is confirmed at the build-ocaml.sh comment
   level, §2.4).
4. **The E1 characteristic-set clustering finding from the perf-review
   doc (gene: CS-clustering made the file 2.5% LARGER, not smaller) —
   does that change once row order feeds a buffer instead of a disk
   read-path?** Not investigated here; row order affects row-group
   pruning locality (I/O-shaped reasoning) which is moot once the whole
   file is bytes-in-RAM either way (§1.d finding 1) — plausible that
   clustering's payoff DECREASES for a pure-memory backend, since the
   "skip a row group without decoding it" benefit is about avoiding
   decode CPU, not avoiding disk seeks, and decode CPU is paid
   regardless of medium. Worth re-measuring once stage 3 exists.
