# Quad-store layout RFC — one position-independent paged byte format for disk, wire, ArrayBuffer, and wasm linear memory

Date: 2026-08-25. Status: **RFC — design only, no code, no format
change.** Nothing below is implemented; every section needs owner
review before any byte is written. Program issue:
https://github.com/danbri/factoidal/issues/595 (Workstream B of the
approved kickoff plan; Workstream A, the measured baseline, runs in
parallel and its numbers are inputs to the open decisions here).

The owner's five persistence plans and the wasm memory-layout
direction are recorded verbatim in
[performance.md § "Persistence program (owner, 2026-08-25) — verbatim"](../claude-rules/performance.md#persistence-program-owner-2026-08-25--verbatim).
All owner quotes below are taken from that section; none are
paraphrased into new wording.

Every performance claim in this document carries one of two labels,
per [skills/measuring-inference](../../skills/measuring-inference/SKILL.md):
**measured** (with the place the number lives) or **assumed — needs
measurement**. §11 collects them.

## 1. Goals, mapped to the owner's plans

The proposal: define ONE quad-store byte layout in the formal source
(F\* first, Lean parity per the standing two-tree rule) that is
byte-identical in four places — a file on disk, an HTTP response
body, a JS `ArrayBuffer`, and wasm linear memory — so that moving a
dataset between them is a bounded copy of pages, with no parse step
between "bytes arrived" and "queries run".

| Owner plan (verbatim fragment, from the [performance.md section](../claude-rules/performance.md#persistence-program-owner-2026-08-25--verbatim)) | What this layout contributes | Section |
|---|---|---|
| 1 — "Become one of a handful of most performant and scaleable rdf databases" | The storage substrate: sorted dictionary-encoded permutations, the design the fastest published engines share | §3, §4 |
| 2 — "Implement bit for bit perfect replicas for common rdf on disk storage/indexing patterns, where documented" | The layout keeps enough structure (per-graph sorted runs, full vocabulary) that foreign formats are pure serializations from it | §8 |
| 3 — "Be corpus/datarepo centric: allow for named graphs to be at rest on disk and OPTIONALLY and CLEVERLY brung up into 'hot' use" | Graph-major segmentation: residency decided per graph segment, paging per page | §5 |
| 4 — "Allow for NGs to be further decomposed into large sets of instantiated shapes" | Shape tables as first-class page types with a residual triples table and measurable coverage | §6 |
| 5 — "Be comparable in perf to the likes of Qlever and adopt all public opensource and published perf best practices from high perf systems including compact IDs" | Compact IDs, delta-compressed sorted runs, on-disk vocabulary with an in-memory frontier — each adopted with its citation | §3, §4 |
| wasm direction — "Consider if in memory wasm layout of rdf quads could be same as disk layout and whether memory mapping style techniques could allow subdatasets / nquads to be pages in and out of use" | The page model is chosen so wasm "memory mapping" is manual paging of identical bytes | §2, §9 |

## 2. Page model

An artifact is a sequence of fixed-size pages. Every structure in the
store — vocabulary, permutations, manifest, shape tables — is stored
as pages of one shared framing.

**Page size.** Fixed per artifact, recorded in the file header.
Candidate: **64 KiB**. Arguments, for and against:

- WebAssembly linear memory grows in 64 KiB units (WebAssembly core
  specification, memory page size). A 64 KiB store page occupies
  exactly one wasm page, so the wasm page table in §9 is an identity
  mapping. This is a specification fact, not a measurement.
- RDF-3X used 16 KiB B-tree pages (Neumann & Weikum, "RDF-3X: a
  RISC-style engine for RDF", VLDB 2008). Smaller pages page in less
  waste for point lookups; larger pages amortize per-page headers and
  give delta compression longer runs. Where the crossover sits for
  our workloads is **assumed — needs measurement** (Workstream A's
  point-lookup vs scan numbers are the instrument).
- One HTTP Range request per page: at 64 KiB, request-count overhead
  on a cold scan is 16x lower than at 4 KiB. The latency claim
  behind "64 KiB amortizes better over real CDN round-trips" is
  **assumed — needs measurement**.

The choice is **open** (🧭 in §10). Nothing else in this RFC depends
on the specific value; everything depends on it being fixed and
recorded.

**Byte order.** Little-endian throughout. Every existing Factoidal
artifact family is already LE (the magic table in
[skills/disk-storage-format §1.1](../../skills/disk-storage-format/SKILL.md));
wasm linear memory is LE by specification; x86-64 and AArch64 are LE.
No byte-swapping path exists in v1; a big-endian host would pay a
swap in the accessors, accepted.

**Page header.** Fixed 32 bytes at offset 0 of every page. Field
values below are illustrative; the final constants are set when the
format is specified in F\*:

```
offset  size  field
0       4     magic (u32 LE) — one constant for the format family
4       2     format major version
6       2     format minor version
8       2     page type (file-header / manifest / vocabulary /
              permutation-run / shape-schema / shape-rows /
              residual-triples / reserved)
10      2     flags
12      4     segment id (0 = store-global; else the graph segment
              this page belongs to, §5)
16      8     page sequence number within the segment
24      4     payload byte length
28      4     CRC32C of the payload
```

CRC32C follows the HDT container precedent (CRC8/16/32C per section,
[2026-07-06-hdt-program-plan.md](2026-07-06-hdt-program-plan.md))
rather than the delta log's additive `simple_checksum`; the delta log
itself is unchanged (§7). The SHA-256 hash-witness check stays at the
CI layer per
[2026-05-07-io-verification-and-third-party.md](2026-05-07-io-verification-and-third-party.md)
— it is not a field in the format.

**Position independence.** Inside a page payload, every reference is
a page-relative byte offset. Across pages, every reference is a
(segment id, page sequence number) pair resolved through the page
table (§9) or the manifest (§5). No absolute file offsets appear in
any payload, so a page's bytes mean the same thing at any base
address in any of the four homes. This is the property Parquet does
not have: a Parquet file is navigated from a footer holding absolute
offsets, so a byte range of a Parquet file is not interpretable
alone.

**Self-containment.** Each page is decodable given only (a) its own
bytes and (b) the vocabulary. Delta-compressed runs restart within
the page (§4), so no page needs its predecessor. This is what makes
page-granular eviction and Range-request loading sound.

**Compression stance.** No block compression (ZSTD or otherwise)
inside pages. A compressed page must be decompressed before access,
which reinstates a parse step between bytes and queries and breaks
"identical bytes in all four homes". Instead, pages use encodings
that are queryable in place through the verified accessors:
front-coding with restart points for strings, delta-varint for
sorted id runs. Costs acknowledged: the COTTAS base measures ~1.14–1.17
B/quad with ZSTD and the native uncompressed writer ~13.90 B/quad
(both **measured**, [skills/disk-storage-format §4](../../skills/disk-storage-format/SKILL.md));
delta-compressed sorted id runs land between those bounds, where
exactly is **assumed — needs measurement**. Transparent wire
compression (HTTP `Content-Encoding`) remains available and does not
affect the at-rest or in-memory bytes.

## 3. Compact IDs

**Term ids.** Every RDF term gets an integer id from a dictionary.
The accessor API works in fixed-width **u64** ids with a small tag
field in the high bits distinguishing term kind (IRI / blank node /
literal, with literal-kind subtags), following QLever's practice of
folding type information into the id so comparisons, FILTER
dispatch, and ORDER BY can act without a dictionary lookup (QLever
is open source — https://github.com/ad-freiburg/qlever — and Bast &
Buchhold, CIKM 2017; the id-tagging detail is read from the public
repository and is **assumed — needs re-verification against a pinned
QLever release** before plan 2 targets it).

Width tradeoffs:

- **u32**: halves index volume, but caps the term space at 2^32;
  plan 3's "full corpus might be many times larger than what we
  might expect from a normal rdf db" makes a global 2^32 cap a
  design risk. Viable as a **per-segment local** width (below).
- **u64 fixed**: simple, no overflow path, matches QLever; costs
  space only in memory-resident structures, because…
- **varint at rest**: pages never store raw u64s; sorted runs store
  byte-aligned varint **deltas** (RDF-3X's gap compression of sorted
  triple leaves — Neumann & Weikum 2008). So the at-rest cost of
  u64 logical ids is near the entropy of the gaps, not 8 bytes per
  component. The decode cost per access is bounded by the restart
  interval (**assumed — needs measurement** on real corpora).

Proposal: u64 tagged ids in the API, varint deltas at rest. The
u32-local alternative stays open (🧭 §10).

**Per-corpus vs per-graph dictionaries.** The interaction with plan
3 is the design driver:

- *Per-corpus*: one sorted vocabulary; cross-graph joins compare ids
  directly. But every graph pins the shared vocabulary, so evicting
  a cold graph reclaims its permutation pages and none of its
  dictionary bytes; and a corpus-scale merge on every import touches
  a global structure.
- *Per-graph*: a segment is fully self-contained — evicting a graph
  reclaims everything it brought, and a per-graph HDT export (§8)
  gets its dictionary base for free. But a cross-graph join must
  translate ids or fall back to byte comparison of terms.
- *Two-level (proposed)*: a store-global dictionary for terms that
  occur in more than one graph or in predicate position (predicates
  and schema vocabulary recur across graphs; the skew claim is
  **assumed — needs measurement**, and Workstream (c)'s
  shape-coverage pass over a real corpus can measure term sharing at
  the same time), plus per-segment local sections for single-graph
  terms, distinguished by a tag bit. Cross-graph joins meet almost
  always in the global space; eviction reclaims the local sections.

Open (🧭 §10) — the two-level split is the recommendation, not a
decision.

**FastString re-founding.** The vocabulary layer is byte-oriented:
front-coded blocks of UTF-8 bytes, compared as byte sequences. That
grounds it on the byte-indexed `Parser.FastString` foundation rather
than `FStar.String`, whose trusted interface lacks content
specifications for `sub` (the ulib gap documented in
[2026-08-10-string-foundation-decision.md](2026-08-10-string-foundation-decision.md)).
Term-id assignment and lookup then never depend on the unspecified
primitives.

**On-disk vocabulary, in-memory frontier.** Vocabulary pages are
front-coded string blocks (HDT's plain-front-coding precedent, with
restart points at fixed intervals). Memory keeps only the frontier:
one (first-string, id-range) entry per vocabulary page. A lookup
binary-searches the frontier, then decodes at most one page. Frontier
size is terms/strings-per-page — for a 10^9-term corpus at ~200
strings per 64 KiB page, ~5M entries (**assumed — needs measurement**;
the strings-per-page figure depends on term length distribution).

## 4. Permutations

**Candidate set: GSPO + GPOS + GOSP — graph-major, three orders.**

Graph-major keys make every permutation prefix-partitioned by graph:
all pages of one graph's runs are contiguous, which is what lets §5
treat the graph as the residency unit without a separate per-graph
file per index. Within a graph, the three orders give a contiguous
run for every bound-prefix shape of a triple pattern:

| Pattern bindings (within a graph) | Serving order | Access |
|---|---|---|
| S bound; S,P bound | GSPO | prefix run |
| P bound; P,O bound | GPOS | prefix run |
| O bound; O,S bound | GOSP | prefix run |
| S,P,O bound (existence) | any | prefix run |
| none bound | any | full scan |

RDF-3X ships all six orders plus aggregated indexes (Neumann &
Weikum 2008); QLever builds six with a two-permutation (PSO+POS)
reduced mode (read from the public repository — **assumed, pinned
release check pending**). Six orders buy merge joins on more
variable orders and are what worst-case-optimal join variable
orderings want. Three graph-major orders are the floor that covers
pattern lookup; the delta is a join-processing question, and
[2026-08-22-indexing-and-join-processing.md](2026-08-22-indexing-and-join-processing.md)
already sequences that programme (leapfrog over an iterator seam,
then the Ring). The page layout must not preclude either: a fourth
page type for additional orders, or a Ring structure, joins the same
page family later. Open (🧭 §10).

**Per-page delta compression.** Within a run, quads are sorted in
the permutation's component order and stored as varint deltas with
same-prefix elision (component-level: unchanged leading components
encode as zero-flags), restarting with a full tuple at each restart
point so the page stands alone. This is RDF-3X's leaf-page scheme
adapted to page self-containment.

**Cardinality inputs.** The manifest (§5) carries per-graph,
per-predicate counts as the first estimator feed; characteristic
sets (Neumann & Moerkotte, ICDE 2011 — the citation set verified in
[2026-08-22-indexing-and-join-processing.md](2026-08-22-indexing-and-join-processing.md))
arrive with the shape work in §6, which computes the same grouping.

## 5. Named-graph segmentation (plan 3)

**Segment = the residency unit.** A segment holds one named graph —
or, for graphs far smaller than a page, a bin of small graphs — and
contains that graph's permutation runs, its local vocabulary section
(under the two-level dictionary), and its shape tables (§6), all as
pages carrying the segment id in their headers.

**Graph manifest.** A store-global page type; one row per graph:

- graph IRI id (store-global dictionary);
- segment id, quad count, byte size;
- page extents per permutation (start page, page count);
- index state: which orders are built, which are absent (lazy build
  is allowed — a cold-imported graph may carry GSPO only until first
  use warrants the rest);
- per-predicate counts (the §4 estimator feed);
- optional last-access epoch, advisory.

**Hot / warm / cold as two granularities.** The owner's plan 3 asks
that "useful working subsets sliced and diced to remove the pain of
deciding which named graphs to have hot warm or cold". In this
layout that decision has a mechanical form:

- *cold*: segment pages at rest only (disk or remote);
- *warm*: pages resident (paged in wholly or partly), no derived
  in-memory structures;
- *hot*: pages resident plus in-memory adjuncts (frontier slices,
  decoded-view caches — the successor of
  `RDF.CottasStore.PageCache.fst`'s decoded-column cache, re-keyed
  to pages).

Residency policy operates at graph granularity via the manifest and
at page granularity via the page table (§9) — one mechanism serves
both granularities.

**Small graphs.** A corpus with millions of graphs of a few triples
each would waste a page per graph; binning small graphs into shared
segments (manifest maps graph → segment + run extent) is the
proposed answer. The threshold and the waste it avoids are
**assumed — needs measurement** on a real multi-graph corpus
(Workstream (c)).

## 6. Shape tables (plan 4)

The owner's plan 4: "Allow for NGs to be further decomposed into
large sets of instantiated shapes such that a geaph g1 might be
covered by 1000000 pccurences of shape sh632 sh734 etc." (verbatim,
including spelling, from the
[performance.md section](../claude-rules/performance.md#persistence-program-owner-2026-08-25--verbatim)).

**Model.** A shape occurrence is a **row**; the shape is the
**schema**. For a SHACL node shape whose constrained properties have
cardinality exactly 1, each property is an id column; optional and
multi-valued properties go to an overflow column or stay in the
residual table. Three page types:

- *shape-schema* pages: shape id → column definitions (property id,
  kind, nullability), plus provenance (which shapes graph the
  definition came from);
- *shape-rows* pages: fixed-stride rows of term ids for one shape id
  — columnar-within-page so a column scan touches contiguous bytes;
- *residual-triples* pages: an ordinary permutation run holding every
  quad no shape row covers.

**Coverage is a measurement, per graph.** covered-quads /
total-quads, computable from the manifest counts plus shape-rows
stats. No number is claimed here: Workstream (c) (queued behind A
and B in the kickoff plan) measures coverage on a real corpus before
the format commits to shape tables. All coverage expectations are
**assumed — needs measurement** until then.

**Relation to the literature.** Characteristic sets (Neumann &
Moerkotte, ICDE 2011) mine this grouping from the data — group
subjects by their property set — and property tables (early Jena
storage work) hand-declare it. SHACL changes the epistemic status of
the schema: the shape is explicit, validated, and itself queryable
RDF, so the "schema discovery" step becomes a conformance check, and
a shape-rows table is exactly the characteristic-set grouping with a
declared, stable identity.

**A conflict to record.** The plan-4 analysis in
[performance.md](../claude-rules/performance.md#persistence-program-owner-2026-08-25--verbatim)
frames Parquet as the principled container for shape rows ("shape
occurrence = row … shape-decomposed storage IS columnar storage",
Claude-inferred analysis there, not owner-decided). Parquet as a
container conflicts with §2's requirements: footer-directed absolute
offsets, thrift-framed metadata, and block compression mean Parquet
bytes are not position-independent and not zero-copy-accessible.
Options: (a) columnar **pages** inside this layout — Parquet's
encodings without its container — or (b) actual Parquet files as a
cold-tier shape store, converted to pages on warming. This RFC
recommends (a) and records (b) as the fallback; 🧭 §10.

**v1 or v2.** Page-type codes for the three shape page types are
reserved in v1 either way; whether their payload definitions land in
v1 or wait for the coverage measurement is an open question
(🧭 §10).

## 7. Disposition of every existing on-disk artifact

Per the owner's standing concern (recorded in the
[performance.md section](../claude-rules/performance.md#persistence-program-owner-2026-08-25--verbatim)
context line: COTTAS "consumed many files and lines against little
demonstrated payoff") this RFC reframes the existing artifact set
rather than adding to it. Verdicts: **kept** (byte format and
semantics unchanged), **generalized** (the need survives; the bytes
merge into a layout structure), **superseded** (the need itself
disappears under sorted permutations).

Eight of the eleven sidecars exist to compensate for the base file's
row order being unsorted — presence bitmaps and offset indexes
re-derive locality that a sorted permutation has by construction.
That is the reframing: the sidecar *functions* survive as properties
of the primary structure instead of as companion files.

| # | Artifact | Magic | Verdict | Why (one line) |
|---|---|---|---|---|
| 0 | `data.cottas` (Parquet base) | `PAR1` | superseded | Footer-directed absolute offsets + block compression are incompatible with §2; retained as an import/export interop format, and `Parquet.Footer.fst` stays as the foreign-Parquet reader. |
| 1 | `.s.dict` | COTD | generalized | Per-column dictionaries merge into the single tagged-id vocabulary (§3), front-coded and paged. |
| 2 | `.p.dict` | COTD | generalized | Same; predicate terms live in the store-global level of the two-level dictionary. |
| 3 | `.o.dict` | COTD | generalized | Same as `.s.dict`. |
| 4 | `.g.dict` | COTD | generalized | Graph names become manifest rows (§5) keyed by store-global ids. |
| 5 | `.s.presence` | COTP | superseded | Row-group presence pruning is a workaround for unsorted rows; a GSPO prefix probe answers "does S occur" directly. |
| 6 | `.p.presence` | COTP | superseded | Same via GPOS. |
| 7 | `.o.presence` | COTP | superseded | Same via GOSP. |
| 8 | `.g.presence` | COTP | superseded | The manifest enumerates graphs; graph-major keys make per-graph extent lookup exact, not probabilistic. |
| 9 | `.p.offsets` | COTO | superseded | GPOS runs are the per-predicate contiguous ranges this index reconstructs. |
| 10 | `.po.presence` | COPO | superseded | A bound (P,O) pair is a prefix of GPOS; no compound bitmap needed. |
| 11 | `.s.offsets` | COTS | superseded | Per-subject contiguous global row ranges hold by construction in GSPO. |
| 12 | `data.deltalog` | DLE1/DLB1/DLOG | kept | Mutation path unchanged: append-only log over immutable pages; framing, checksums, and the 270/270 + 25/25 + 25/25 crash-recovery record (measured, [skills/disk-storage-format §3.2](../../skills/disk-storage-format/SKILL.md)) carry over as-is. |
| 13 | `data.compacted-epoch` | CEP1 | kept | Epoch-guard semantics (writers stamp above the compacted epoch) are independent of what the base bytes are. |
| 14 | `current -> vN` symlink layout | n/a | kept | Atomic-visibility-of-a-version-set is exactly what immutable segment versions need; applies unchanged, per store or per segment. |

Supplementary import-time artifacts, for completeness:
`data.nq` (superseded — the store serializes N-Quads on demand;
keeping source text is a provenance option, not a format component),
`data.factbin` (superseded — manifest counts replace it),
`source-info.ttl` + `summary.json` (kept — provenance metadata,
independent of the storage format).

Counts over the fifteen core rows: **kept 3, generalized 4,
superseded 8.**

Nothing is deleted by this RFC: verdicts take effect only when the
owner approves the format and a migration lands with its own tests.
The delta-log F\* modules (`RDF.Store.Columnar.DeltaLog.fst`,
`DeltaMerge.fst`) continue unchanged; the sidecar writer/reader
modules retire together with their files if and when "superseded"
is executed.

## 8. Foreign-format replicas (plan 2)

Rule-#11 discipline for every replica target: the foreign byte format
is specified in the formal source (`serialize : data -> Tot (list
u8)`), OCaml/JS realizes only `write_bytes`, and CI carries a
hash-witness test comparing our bytes against reference-tool bytes on
the same input
([2026-05-07-io-verification-and-third-party.md](2026-05-07-io-verification-and-third-party.md)).
"Bit for bit perfect" then has an executable definition: the CI hash
equality passes.

**HDT writer.** What a bit-perfect `.hdt` writer needs from this
layout:

- a per-graph SPO-sorted quad enumeration — a GSPO run restricted to
  one graph is exactly that;
- the dictionary re-partitioned into HDT's four sections (shared
  subject-object, subject-only, object-only, predicate) in HDT's
  ordering — derivable in one pass given per-term occurrence-position
  flags, which the vocabulary can carry as tag bits or the manifest
  as statistics;
- the byte-level machinery already pinned by the HDT reader
  programme: PFC blocks, VByte with hdt-cpp's inverted
  continuation-bit convention, BitmapTriples' two bit sequences and
  log arrays, CRC8/16/32C — all specified with their hdt-cpp-vs-spec
  discrepancies in
  [2026-07-06-hdt-program-plan.md](2026-07-06-hdt-program-plan.md).

Prerequisite repair: **HDT stage-4 parity is currently 0 pass, 6
fail (out of 6) on the committed binaries** (measured, recorded in
https://github.com/danbri/factoidal/issues/594). The reader-side
gate is the instrument that would validate a writer's round-trip, so
repairing https://github.com/danbri/factoidal/issues/594 comes
before any writer work.

**QLever-index replica.** Needs QLever's vocabulary, permutation,
and metadata file formats. They are open source and readable but not
documented as stable across releases, so the target must pin a
specific QLever release, specify that release's bytes in the formal
source, and hash-witness against an index built by that release on
the same corpus. Feasibility and effort are **assumed — needs a
scoping pass over the QLever source** (a CI-based same-hardware
comparison is already a Workstream A candidate on
https://github.com/danbri/factoidal/issues/595).

**Jena TDB2** is the third candidate named on the program issue;
partially documented; not scoped here.

## 9. wasm paging — identical bytes in linear memory

**Load path.** A page table maps (segment id, page number)
→ linear-memory slot. Bringing a page in is a copy of its bytes into
a free slot (at 64 KiB page size, exactly one wasm memory page);
eviction is dropping the slot. The bytes in the slot are the bytes
on disk; queries run against them immediately through the accessors.

**Where the bytes come from, per host:**

- browser: HTTP Range requests per page (Range support on the
  serving host is **assumed — verify for GitHub Pages and the Fly.io
  endpoint** before relying on it);
- Node: `fs.read` at page offsets;
- native: `pread` or real `mmap` — the same layout admits actual
  memory mapping where the OS provides it, with the page table
  degenerating to pointer arithmetic.

**Outside the managed heap.** The store buffer lives in linear
memory owned by the C shim layer, not in the Lean (or OCaml) managed
heap — the GC never walks pages, and no per-term boxing exists. The
API face is the dataset-handle layer of
https://github.com/danbri/factoidal/issues/585: `datasetOpen` /
`queryByHandle` / `datasetClose`, where a handle resolves to a page
table plus manifest rather than to a parsed heap object. That issue's
handle registry (an `IO.Ref` map in the wasm entry layer, outside
L4Factoidal spec code) is exactly where the page table belongs. The
toolchain constraints for the shim are the ones already documented in
[skills/lean4-wasm-export](../../skills/lean4-wasm-export/SKILL.md).

**Verified accessors — the cost of zero-copy.** For each page type,
the formal source defines `parse_page : bytes -> option view` and
`serialize_page : view -> bytes` with a round-trip lemma, plus an
agreement lemma: the accessor evaluated on bytes equals the
corresponding function on the abstract dataset the artifact denotes.
Without those proofs, flat-buffer access is the "bytes to code"
hazard the owner's wasm steer names — every offset computation is an
unchecked claim about foreign bytes. With them, the zero-copy path
carries the same correctness status as the rest of the engine. This
is deliberately the `Parquet.Footer.fst` pattern (verified
byte-navigation over `assume val` range reads) applied to a format
we control.

**Mutation.** Pages are immutable. Writes go through the existing
delta log (kept, §7): merge-on-read composes base pages with the
replayed log exactly as `DeltaMerge.fst` does today; compaction
materializes a fresh segment version and flips the `current` symlink
(kept, §7). In wasm, the log is an in-memory byte log with the same
framing, exportable verbatim — the framing is already
position-independent.

**Version and endianness costs.** Every page carries
major.minor; readers reject a higher major and ignore unknown page
types and flag bits under the same major. Endianness is fixed LE
(§2). Page size is frozen per artifact at creation. These are the
compatibility costs of keeping the bytes identical everywhere: no
per-host re-layout step exists to absorb variation.

## 10. Open questions for the owner

- 🧭 **ID width**: u64 tagged ids everywhere (recommended), or
  per-segment u32 local ids with a translation layer where corpus
  scale allows?
- 🧭 **Permutation set**: three graph-major orders (GSPO+GPOS+GOSP,
  recommended floor), all six, or reserve the Ring as the planned
  index family and ship three meanwhile?
- 🧭 **Dictionaries**: per-corpus, per-graph, or the two-level split
  recommended in §3?
- 🧭 **Page size**: 64 KiB (wasm-page-aligned) or 16 KiB (RDF-3X
  practice) — freeze after Workstream A's lookup-vs-scan numbers?
- 🧭 **Shape tables**: payload definitions in v1, or reserved page
  types in v1 with definitions in v2 after Workstream (c) measures
  coverage on a real corpus?
- 🧭 **Parquet's remaining role**: import/export interop only, or
  also the cold tier for shape rows (§6's recorded conflict)?

## 11. Assumption ledger

Measured claims used above, with their sources:

- COTTAS ZSTD ~1.14–1.17 B/quad; native uncompressed writer ~13.90
  B/quad — [skills/disk-storage-format §4](../../skills/disk-storage-format/SKILL.md).
- Row-group-count query regression (44-group ~4x slower than 8-group
  after the footer fix) —
  [skills/disk-storage-format §2](../../skills/disk-storage-format/SKILL.md);
  motivates page-granular locality.
- Delta-log crash record: 270/270, 25/25, 25/25 clean recoveries —
  [skills/disk-storage-format §3.2](../../skills/disk-storage-format/SKILL.md).
- HDT stage-4 parity 0 pass, 6 fail (out of 6) —
  https://github.com/danbri/factoidal/issues/594.
- wasm 64 KiB memory page granularity; wasm LE — WebAssembly core
  specification (specification facts, not measurements).

Assumed — needs measurement (each named where it appears):

- 64 KiB vs 16 KiB page-size crossover for our workloads (§2) —
  instrument: Workstream A harness.
- HTTP Range latency amortization at 64 KiB (§2) and Range support
  on GitHub Pages / Fly.io (§9).
- At-rest B/quad of delta-varint sorted runs (§2, §3).
- Per-access decode cost under restart intervals (§3).
- Term-sharing skew justifying the two-level dictionary (§3) and
  frontier size at corpus scale (§3) — instrument: Workstream (c).
- Small-graph binning threshold and waste (§5) — instrument:
  Workstream (c).
- Shape coverage fractions per graph (§6) — instrument: Workstream
  (c).
- QLever id-tagging and permutation details against a pinned
  release; replica feasibility (§3, §4, §8).

No claim above asserts a speed win for the proposed layout. The
baseline (Workstream A) exists so that a future implementation is
judged against measured numbers on the same hardware, per the
standing rules at the top of
[performance.md](../claude-rules/performance.md).
