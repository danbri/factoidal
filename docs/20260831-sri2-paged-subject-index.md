# SRI2: paged Subject Row Index

## Why SRI2

SRI1 is canonical and correct, but its reader currently authenticates and
decodes the entire flat sidecar before selecting a subject's row offsets. The
gene benchmark therefore made TLI1 and PTD1 page-selective while retaining one
large all-at-once SRI1 read. SRI2 is the compatible immutable successor.

It is **not** a new RDF identity scheme. Its keys remain IBK3-local subject
IDs, so it must be bound to the exact target IBK3 digest and every returned
offset must still be checked by reading the corresponding IBK3 row.

## Proposed bytes

```text
magic                 u32le  "SRI2"
version               u8     2
targetIBKSha256       32 bytes
rowCount              u32le
pairCount             u32le
pagePairs             u32le  256
pageCount             u32le
directoryBytes        u32le
pageBytes             u32le
directory             (firstSubjectId, lastSubjectId, offset, length) × pageCount
pages                 sorted (subjectId, sourceRowOffset) u32 pairs
crc32c                u32le over post-version bytes
```

Pairs retain SRI1's strict ordering: first by subject local ID, then by source
row offset. A directory entry names its inclusive subject range. Lookup fetches
the directory and fetches every page whose range can contain the requested
subject. This deliberately handles a very frequent subject whose posting list
spans several pages: it never guesses from a duplicated first-subject boundary
and silently omits earlier postings. Normal lookups select one page; the
multi-page case remains bounded and deterministic.

## Admission and execution rules

- The target digest must equal the paired IBK3 artifact digest.
- `pairCount == rowCount`; offsets are a permutation of `0 .. rowCount-1`.
- Directory byte ranges are contiguous and non-empty. Subject ranges are
  inclusive and a subject may continue in following pages.
- Each page is internally canonical; the boundary pair ordering across pages
  is checked by complete decode at activation.
- A range query proves framing and Merkle inclusion for the prefix, directory
  and fetched pages. It does not trust a posting until the selected IBK3 row
  has the expected subject local ID.

## Delivery sequence

1. Pure Lean SRI2 encoder/strict decoder with single- and two-page guards.
2. Prefix/directory/page reader plus reference lookup agreement with SRI1.
3. A coherent SBM5 sidecar commitment, writer, activation check and smoke.
4. Replace full SRI1 decoding only for newly packed SBM5 generations.

SBM4 and SRI1 remain readable throughout. The new format is deliberately not
being attached to a manifest until the codec, activation relation and range
reader agree as one increment.
