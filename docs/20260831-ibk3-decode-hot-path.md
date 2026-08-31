# IBK3 decode hot-path: total streaming accumulators

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
