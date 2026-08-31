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
currently reads the whole target PTD1 dictionary to translate RDF subjects to
that artifact's local IDs, and reads the complete flat SRI1 sidecar. It avoids
the much larger target *row* area. TLI1 is now committed and activation-
verified, but the range reader has not yet been connected; that and a paged
successor to SRI1 are the next steps before treating this as a serious
cold-query access path.

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
commitment. It then strictly decodes TLI1 and refuses a sidecar whose target
digest does not equal the entry's IBK3 digest. The persistent smoke test also
corrupts a TLI1 byte and establishes that activation fails closed. This is a
real immutable-object admission boundary; execution still uses PTD1 until the
page-at-a-time TLI1 reader is wired into the SRI1 join.
