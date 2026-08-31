# IBK3 decode hot-path: total streaming accumulators

## Names used here

- **IBK3**: Indexed Block, format version 3; the predicate-local RDF data
  artifact.
- **SRI1**: Subject Row Index, format version 1; its subject-to-IBK-row
  posting artifact.
- **SBM3**: Shardborough Manifest, wire version 3; the manifest that commits
  both artifacts and their integrity metadata.

## Change

`PagedTermDictionary.lean` and `IndexedBlockWireV3.lean` previously decoded
data-sized byte streams by constructing results after recursive calls. IBK3
row decoding, PTD1 directory decoding, term decoding, and full PTD1 page
decoding now use reverse accumulators and one final reversal. They remain
total functions; no `partial def` was introduced.

PTD1 page planning previously used `List.contains` plus `seen ++ [page]` for
each row-term reference. A bounded `Array Bool` indexed by declared page ID
now preserves first-occurrence page order while avoiding repeated scans of the
growing page list. Decoded page terms are converted once to `Array Term`, so
each row's local term-ID lookup is indexed rather than a list walk.

The on-disk byte format, page order, RDF denotation, and query result order
are unchanged. Existing build-time guards and the persistent IBK3 smoke test
cover the semantic path.

## Measured executable check

On 2026-08-31, the native Merkle scanner ran against the already published
direct IBK3 life-sciences gene store at:

```text
/private/tmp/l4ibk3-gene-direct.TxTNxG/store
```

The store was published from
`examples/wikidata/subsets/lifesci-kgx/data/gene.ttl`: 888,949 triples in 13
SBM2 artifacts. The `wdt:P684` predicate occupies five artifacts and 759,263
rows. A full-limit scan reported:

```text
rows=759263 artifacts=5/5 logical-read-bytes=16428933
fetched-bytes=16428973 verified-chunks=253 range-requests=391
real 2.30s; user 2.24s; sys 0.04s
```

This is a post-change baseline on the local macOS host, not a comparison with
the prior decoder. The scanner still materialises RDF triples for this full
predicate scan; avoiding that result construction is a separate physical
operator task.

## Rejected one-shot join index

On the same direct gene store, the two-pattern query joining the 759,263-row
`wdt:P684` predicate to the four-row `wdt:P682` predicate returned 14 rows in
2.39 seconds through the normal host. A trial which built the existing Lean
in-memory indexed backend after every physical materialisation was correct,
but took 3.60 seconds. The cost of building a fresh index dominated the
avoided bound scans. That implementation was removed rather than retained as
a nominal fast path. The useful next design is a reusable on-disk or
session-cached subject/object access structure, not a per-query index build.

## Subject posting-index meaning

The first implementation step is now
`formal/lean4/L4Factoidal/Storage/SubjectRowIndex.lean`. It defines the
total meaning of a predicate-local subject posting index before any byte
layout is selected. Each subject maps to source-row offsets; selected
postings are restored to ascending source order. The reference function
`expectedOffsets` states the same result directly over the ID rows, and the
build-time guards cover repeated, singleton, and absent subjects.

This is not yet an IBK3 extension and does not claim a persisted speedup. It
is the contract for a versioned successor: its encoder and range reader must
commit and recover this mapping, reject invalid offsets, and preserve the
existing row denotation. IBK3 remains readable unchanged.

The first codec is `SubjectRowIndexWire.lean`, format `SRI1`: a
checksummed sequence of one `(subject TermId, source-row offset)` u32 pair per
row, canonically ordered by subject and then source offset. Its decoder
refuses unknown framing, bad checksums, non-canonical order, duplicate
offsets, and offsets outside the declared row count. The index is intentionally
a separate immutable object at this stage. A host must validate the selected
IBK row's subject ID before using a posting, because SRI1 by itself cannot
prove a cross-object relationship.

SBM3 now commits that SRI1 object as a second `ArtifactRef` in each entry.
The streaming `l4block-shard-pack INPUT OUTPUT ibk3` publisher writes
`predicate-N.ibk3.sri1` and its Merkle leaves before writing its version-three
manifest. On 2026-08-31, a fresh store packed from the checked-in W3C
`sparql10/basic/data-6.ttl` fixture contained the IBK3 file, its Merkle leaves,
the SRI1 file, its Merkle leaves, and `manifest.sbm2`; parsed SPARQL over the
new store returned the two expected `:p1` rows. Existing IBK3/SBM2 stores
remain readable.

`Harness/IndexedBlockV3Materialize.subjectPostings?` is the matching reader.
It returns no postings unless the manifest digest and extent, Merkle leaves,
SRI1 framing/checksum, and SRI1 row count all agree. It is intentionally not
used for query selection yet: the next scan must also read each selected IBK3
row and verify that its subject ID matches the SRI1 posting.

Activation now makes the same distinction. `l4block-shard-activate` accepts
the `predicate-ibk3-ptd1-sri1-merkle-v0` layout and, before it replaces the
collection's `CURRENT` pointer, checks every IBK3 and SRI1 artifact's declared
full SHA-256 digest. It then opens every SRI1 object through its committed
Merkle leaves and checks its framing, checksum and row count. Manifest keys
must be globally unique: a block cannot alias another block or an index. The
persistent smoke test packs a second generation, corrupts one SRI1 byte, and
proves that activation refuses it. This is an admission check, not yet a proof
that an otherwise well-formed SRI1 posting names the same subject as its IBK3
row; the selective scan will verify that relationship per selected row.

Within an admitted SRI1 payload, lookup now uses a total binary search over
canonical subject ordering, followed by a scan of only that subject's
contiguous offsets. This removes a full posting-list CPU scan. The current
sidecar reader still reads the complete SRI1 object; a paged SRI successor is
needed to reduce cold I/O for very large predicate blocks.

The first executable use is deliberately narrow and visible in the query
diagnostic as `open-mode=ibk3-sri1-subject-join(2)`. It accepts exactly two
default-graph BGP patterns with the same subject variable and two different
constant predicates, with no trailing `VALUES` and no delta overlay. It
materialises the lower-row-count predicate in the ordinary way, resolves its
distinct RDF subjects in the other IBK3 dictionary, uses SRI1 to fetch only
the corresponding fixed-width rows, and verifies each fetched row still has
the indexed local subject ID. The normal parsed Lean SPARQL evaluator then
does the join, projection, ordering and bag semantics on those exact triples.

This is a correctness-first bridge, not a large-store performance claim: it
still reads the complete flat SRI1 sidecar and, when selected rows exist, the
target PTD1 dictionary to reconstruct RDF terms. It avoids the much larger
target *row* area. TLI1 is now committed and activation-verified and the join
uses its Merkle-checked prefix, directory and selected page(s) to obtain local
IDs. Every returned ID is cross-checked against PTD1 before row selection. A
miss avoids opening PTD1 and target rows. A hit now reads the selected fixed-
width rows first, plans their referenced PTD1 pages, and decodes only those
Merkle-verified pages to reconstruct RDF terms. The old complete-PTD1 path is
retained only for pre-SBM4 stores. A paged SRI successor and a large-fixture
benchmark remain the next performance steps.

## Local term-ID boundary

IBK3 currently assigns dictionary IDs per artifact. Therefore an SRI1 posting
key such as subject ID `42` has meaning only with its own IBK3 dictionary; it
cannot be sent directly to another predicate artifact. A cross-predicate join
must first resolve its RDF subject term to the target artifact's local ID, then
use that artifact's SRI1 offsets, and finally validate the selected rows.

This is not a defect in SRI1. It makes the next required component visible: a
committed term-to-local-ID lookup structure, or a later globally coordinated
term-ID regime. The former is the near-term compatibility path. A hash can be
used to narrow candidate terms, but must never be treated as identity without
checking the encoded RDF term, because collisions would otherwise change query
answers.

## Verification

```text
cd formal/lean4
lake build L4Factoidal.Storage.PagedTermDictionary \
  L4Factoidal.Storage.IndexedBlockWireV3 \
  l4block-id-v3-merkle-scan l4block-id-v3-query l4block-shard-activate

cd ../..
tools/blockengine-ibk3-persistent-smoke.sh
```

Both completed successfully after this change.

## SBM4 / TLI1 committed sidecar (2026-08-31)

`Shardborough Manifest` wire version 4 (SBM4) extends each IBK3 entry with a
second mandatory, non-aliasing companion reference: `predicate-N.ibk3.tli1`.
The packing and compaction publishers construct the index only after the
IBK3 digest is known, place that digest in TLI1's `targetIBKSha256` field, and
write independent Merkle leaves for the sidecar. The layout label is now
`predicate-ibk3-ptd1-sri1-tli1-merkle-v0` (and its compacted counterpart).

Before atomically updating `CURRENT`, activation checks every primary, SRI1
and TLI1 file against its full SHA-256 and reconstructed fixed-chunk Merkle
commitment. It then strictly decodes TLI1, checks its complete canonical
term-to-local-ID relation against the IBK3 PTD1 dictionary, and refuses a
sidecar whose target digest does not equal the entry's IBK3 digest. The
persistent smoke test also corrupts a TLI1 byte and establishes that
activation fails closed. This is a real immutable-object admission boundary.

### Large-fixture activation observation

The 889k-triple `gene.ttl` source has been repacked as SBM4 (about 43 MiB of
block and sidecar artifacts). Activation deliberately performs complete
IBK3/TLI1 dictionary agreement, in addition to hashes and Merkle checks. It
therefore takes materially longer than a small-fixture activation and is a
publication-time admission cost, not query latency. The gene benchmark begins
only after that immutable generation has completed activation.

## Format and protocol map

### Physical artifacts

- **BLK0** — original MVP: direct RDF-term block bytes. Useful as the first
  canonical byte boundary, but not the current query layout.
- **IBK1** — first dictionary-plus-ID-row encoding: one complete shared term
  dictionary followed by ID triples. It established framed/checksummed ID
  blocks, but is not selective enough for large persistent reads.
- **IBK2** — adds a predicate-local selective-scan layout and coarse directory.
  It is still supported for existing artifacts.
- **IBK3** — current primary block: one predicate per immutable artifact,
  fixed-width local-ID rows first, then a pageable term dictionary. A host can
  fetch rows before fetching the term pages those rows reference.
- **PTD1** — the pageable term dictionary embedded in IBK3: local ID → RDF
  term. Only the needed pages are read on the sparse path.
- **SRI1** — flat subject-row sidecar: local subject ID → IBK3 row offsets.
  It is the retained legacy index for SBM3/SBM4 artifacts.
- **SRI2** — current paged SRI successor: the same canonical postings with a
  checksummed prefix and inclusive subject-range directory. It can read only
  candidate pages, including a posting list spanning page boundaries.
- **TLI1** — target term lookup sidecar: canonical RDF-term bytes → the
  *target* IBK3 local ID, explicitly bound to that IBK3 SHA-256.

### Manifest generations

- **SBM0** — original Shardborough Manifest: lists immutable artifacts.
- **SBM1** — SBM0 plus fixed-chunk Merkle commitments for verified range reads.
- **SBM2** — SBM1 plus multiple bounded immutable blocks for a predicate.
- **SBM3** — SBM2 plus mandatory SRI1 sidecars for IBK3 entries.
- **SBM4** — legacy current-readable form: SRI1 + TLI1, non-aliasing keys,
  checksums, Merkle roots, and layout/version consistency checks.
- **SBM5** — current writable form: replaces SRI1 with paged SRI2 and retains
  TLI1. Activation checks SRI2's complete canonical posting relation against
  IBK3 before publishing the generation.

### Update and publication protocols

- **DLE1** — one framed, checksummed durable delta operation.
- **DLB1** — one framed, sequenced, checksummed batch of DLE1 operations: the
  all-or-nothing durable unit for a SPARQL Update request.
- **DLOG** — an append-only file header followed by DLB1 batches, replayed in
  commit order over the immutable base.
- **CEP1** — framed compacted-epoch sidecar: recovery skips log batches already
  folded into an immutable compacted base, avoiding double replay.
- **CURRENT** — small atomically replaced generation pointer. It is written
  only after activation has admitted the manifest, hashes, Merkle commitments,
  and cross-artifact sidecar relations.

### Architectural position

This is best understood as an assurance-oriented immutable/delta RDF store:
an HDT-like dictionary-and-ID encoding inside independently readable,
predicate-local artifacts; a vertically partitioned/SSTable-like access
layout; and an LSM-like append, compact, activate lifecycle. It is therefore
conceptually adjacent to HDT-plus-delta systems such as qEndpoint and to
immutable-layer systems such as TerminusDB, while its selective block layout
also resembles vertical partitioning rather than an all-permutations RDF-3X
index family.

These comparisons are architectural vocabulary, not compatibility claims.
In particular, current IDs are local to an IBK3 artifact: TLI1 maps a
canonical RDF term into that particular artifact's ID space, SRI2 maps a
subject ID into its rows, and activation verifies those cross-artifact claims
before the generation becomes queryable. That local-ID/verified-sidecar design
is an intentional difference from a single global HDT dictionary.

### First multi-page result

On the repacked gene fixture, the parsed P682-to-P684 subject join returns the
same 14 result rows through `ibk3-sri1-tli1-subject-join(2)`. After batching
decoded TLI pages, its reported logical reads are 182,146 bytes, compared with 16,429,434 bytes for the older
full-materialisation IBK3 store: about a 98% reduction in logical block bytes.
The first cold run still fetched 1,049,085 whole fixed-size chunks. Wall-clock
time must not yet be advertised as improved: repeated TLI lookup/page planning
and the deliberately simple sidecar implementation need further profiling and
cache-aware batching.

### Sparse PTD1 audit repair (2026-08-31)

An independent audit found an edge case in the SBM4 TLI1/SRI1 join path: a
queried RDF term may exist in a target block's dictionary only as an object,
and therefore have a valid TLI1 local ID but no SRI1 subject postings. The old
page plan used only selected row IDs, loaded no PTD1 page, then incorrectly
failed the deliberate TLI1-to-PTD1 equality check. The repaired planner loads
pages for both selected rows and TLI-returned local IDs; the valid query now
contributes zero rows while retaining the equality check. It also treats an
out-of-range ID as an explicit failed plan rather than as an indistinguishable
empty page list. `tools/blockengine-ibk3-persistent-smoke.sh` passes after the
repair.

### SBM5 paged subject index (2026-08-31)

New IBK3 packs and compacted generations now publish the
`predicate-ibk3-ptd1-sri2-tli1-merkle-v0` layout under manifest wire version
five. SRI2 supplies a Merkle-verified prefix, directory and selected subject
pages to the parsed two-predicate join; a normal small persistent fixture
still returns the established 290 rows and the full update/compaction smoke
tests pass. SRI1/SBM4 remains readable for pre-existing generations.

The fresh 888,949-triple `gene.ttl` stores provide the first like-for-like
read measurement for the parsed P682-to-P684 join (14 result rows). After
repairing SRI1 accounting so its full verified sidecar read is no longer
silently excluded, the preserved SBM4 store reported 470,611 logical bytes
and 1,337,550 newly fetched bytes. The new SBM5 SRI2 store reported 186,459
logical bytes and 852,477 newly fetched bytes: reductions of about 60% and
36% respectively. Both measurements intentionally exclude the small plaintext
`.merkle` leaf-file reads; they include all Merkle-verified artifact ranges.
They are single cold-process observations, not wall-clock performance claims.

### Fixed-width row decoder (2026-08-31)

IBK3 fixed-width rows are now decoded with bounds-checked `ByteArray` offsets
instead of first copying a row range into `List UInt8`. This applies both to
the row-prefix decoder used by selective scans and to the predicate-validation
pass used by ASK/count operators. The wire layout and acceptance conditions are
unchanged; `tools/blockengine-ibk3-persistent-smoke.sh` exercises SELECT,
join, ASK, CONSTRUCT, COUNT, grouping, updates and activation after the change.

### PTD1 fixed-framing decoder (2026-08-31)

PTD1's 17-byte prefix and its fixed eight-byte-per-page directory now decode
directly from bounds-checked `ByteArray` offsets. This removes an avoidable
whole-range `ByteArray → List UInt8` copy from the IBK3 sparse path while
keeping the bytes, rejection conditions, and pageable term semantics the same.
The variable-length RDF-term parser for selected PTD1 pages still uses the
existing list-oriented parser; moving that parser is a separate, proof- and
benchmark-driven increment. The PTD1 module build and the complete persistent
IBK3 smoke suite pass after this narrow change.

### SRI2 fixed-range decoder (2026-08-31)

SRI2 now reads its fixed 61-byte prefix, fixed 16-byte directory entries, and
fixed eight-byte subject/row postings directly from bounds-checked
`ByteArray` offsets. These are the ranges read by the SBM5 shared-subject join,
so this removes another avoidable `ByteArray → List UInt8` copy on the actual
selective-query route. Full SRI2 admission decoding remains available and
unchanged; the wire format and its ordering, bounds, and cross-artifact
activation checks are unchanged. The direct codec build and complete
persistent IBK3 smoke suite pass.

An independent review then identified a remaining direct-file seam: individual
Merkle-verified SRI2 pages can be locally well formed while repeating a
posting across a page boundary. The range reader now sorts its candidate pages
by ordinal and requires the aggregate candidate posting sequence to be
strictly ordered. A normal straddled posting list remains accepted; a repeated
`(subject, row-offset)` across pages is rejected. The reviewer also prompted
removal of the obsolete list decoders and a `u32` admission bound on SRI2 row
counts. A selective read cannot prove that an unfetched page was omitted;
that completeness property intentionally remains the responsibility of full
generation activation before SBM5 is queryable.

### Large-generation activation and join profile (2026-08-31)

Profiling full activation of the 888,949-triple SBM5 gene generation exposed
two publication-time quadratic patterns rather than a query-engine failure:

1. SRI2's complete-admission check used `List.eraseDups` to establish that
   row offsets formed a permutation. It remained inside the first 759,263-row
   sidecar after several minutes. It now uses a bounded `Array Bool` seen-set:
   duplicate or out-of-range offsets are still rejected, while the check is
   linear in postings plus row count.
2. fixed-chunk Merkle reconstruction converted the whole artifact to a list
   for every chunk, and reconstructed a concatenated artifact merely to check
   chunk lengths. It now uses direct `ByteArray.extract` ranges and a linear
   canonical-length check. The same width/final-short-chunk contract remains.

After both repairs, the large full activation completed in under roughly 65
seconds on this MacBook Air (an observed operational bound, not yet a
repeatable benchmark). The activated, OS-warm parsed P682-to-P684 join then
returned its established 14 rows in 0.08 seconds with the already recorded
186,459 logical / 852,477 fetched-byte footprint. This is the first elapsed
time datapoint for the new route; it is explicitly not a cold-cache or
cross-version timing comparison.

`tools/blockengine-ibk3-query-benchmark.sh` now makes that query measurement
repeatable against an explicitly activated collection root. It labels the
first fresh process as `cold` and subsequent fresh processes as `warm`, while
disclosing that it does not evict the OS page cache. On the already activated
local gene store, a four-run sample recorded 83.6 ms / 10.38 MiB for the first
process and 70.19, 70.13, and 70.29 ms / about 10.4 MiB for the following
processes. `tools/bench_rusage_run.py` now normalizes `ru_maxrss`: macOS
reports bytes whereas Linux reports KiB, and benchmark JSON records both
normalized units plus the platform-native source unit.

The same runner also tracks a deliberately different workload: `COUNT(*)` on
the 759,263-row P684 predicate, exercising the fixed-row scan without the
sparse subject join. Its first fresh-process local measurement was 895.0 ms /
31.2 MiB and the following fresh process took 885.6 ms. It reports 12,209,178
logical and 12,320,768 fetched bytes. Keeping both workloads prevents an
improvement to the rare-predicate join from being mistaken for improvement to
the high-cardinality scan path.

### Native hot-path profile and bounded chunk cache (2026-08-31)

The reproducibility runner gained `l4block-id-v3-query --repeat N`: it repeats
fresh query evaluation inside one native process solely to give platform
profilers a useful duration.  It does not turn the command into a stateful
query server or weaken per-query validation.  A macOS `sample` profile of 100
P684 count evaluations located the hot path below SPARQL parsing and planning:
fixed-row validation calls the Merkle-verified positioned reader for many
64-KiB chunks, where pure Lean SHA-256/Merkle verification is substantial.

The host-only verified-chunk cache had also used a `List.find?` association
list.  Every cache hit during a full scan therefore became linearly slower as
more chunks had been admitted.  It is now a fixed `Array (Option ByteArray)`
whose length is the already declared manifest chunk count.  Reads remain
fail-closed: only a successful positioned read plus `verifyChunk` inserts a
value.  This changes neither an artifact byte nor its proof obligation.

On the already activated local gene generation, the three-run follow-up was:

| workload | earlier sample | follow-up sample | interpretation |
| --- | --- | --- | --- |
| P682→P684 selective join | 70.1–83.6 ms, about 10.4 MiB | 71.1–74.9 ms, 10.5–10.6 MiB | consistent; this small join was not cache-lookup bound |
| P684 `COUNT(*)` (759,263 rows) | 885.6–895.0 ms, about 31.2 MiB | 879.2–887.6 ms, 31.7–31.9 MiB | consistent; SHA/Merkle and row validation are the next measured target |

These are explicitly warm-OS-cache, fresh-process observations on this
machine, not general throughput claims.  Logical/fetched byte counts are
unchanged.  The next optimisation decision must come from separating
per-chunk proof work from per-row validation, rather than assuming the
sidecar join result generalises to full scans.
