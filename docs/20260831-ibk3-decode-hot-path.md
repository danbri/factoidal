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

Within an admitted SRI1 payload, lookup now uses a total binary search over
canonical subject ordering, followed by a scan of only that subject's
contiguous offsets. This removes a full posting-list CPU scan. The current
sidecar reader still reads the complete SRI1 object; a paged SRI successor is
needed to reduce cold I/O for very large predicate blocks.

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
