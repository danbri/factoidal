# TLI1: Term-to-Local-ID Index format 1

## Purpose

IBK3 stores compact **local** numeric term identifiers. They are meaningful
only in the dictionary of one immutable block. SRI1 (Subject Row Index format
1) selects rows by such a local subject identifier. A cross-predicate join
therefore needs a safe mapping:

```text
RDF term → target IBK3 local TermId → SRI1 offsets → verified IBK3 rows
```

The current SRI1 join implements this mapping by reading the full target PTD1
(Paged Term Dictionary format 1) dictionary and using complete Lean term
equality. It is correct, but it is not an acceptable cold-query path for a
large dictionary.

TLI1 is the committed companion object which replaces that full dictionary
read. It does not create a global RDF identity scheme and it does not permit a
hash to stand for RDF-term equality.

## Proposed canonical bytes

```text
magic                 u32le  "TLI1"
version               u8     1
targetIBKSha256       32 bytes
termCount             u32le
pageTerms             u32le  256
pageCount             u32le
directoryBytes        u32le
pageBytes             u32le
directory             pageCount entries
pages                 sorted term-key/local-ID entries
crc32c                u32le over post-version bytes
```

Each directory entry contains the first complete canonical RDF-term encoding
of its page plus that page's offset and length. Each page holds at most 256
strictly lexicographically ordered pairs:

```text
canonical term bytes, local TermId
```

The exact term byte representation must reuse the existing supported RDF term
codec, rather than inventing a second spelling. Unsupported terms make TLI1
unavailable and force the existing safe fallback.

## Admission and lookup rules

- The manifest commits TLI1 as a separate artifact in **SBM4**
  (Shardborough Manifest wire version 4) entries emitted by the current IBK3
  packer and compactor.
- TLI1 `targetIBKSha256` must equal that entry's IBK3 artifact digest.
- Its `termCount` must equal the target PTD1 term count.
- Directory ranges, page counts, canonical sort order, page boundaries and
  CRC must all validate before lookup.
- Local IDs must be a permutation of the valid target dictionary IDs.
- Lookup reads the directory and one Merkle-verified TLI1 page, then compares
  the requested RDF term by complete structural equality before returning an
  ID. A hash may reduce candidates later, but never decide equality.

The last point preserves RDF answers even if a hash collides or a publisher
uses a maliciously chosen term.

## Proof and executable gates

The pure Lean reference is now
`formal/lean4/L4Factoidal/Storage/TermLocalIndex.lean`. Its `entriesOf`
constructs the canonical term-byte order and `lookup?` uses a total binary
search followed by structural RDF-term equality. The existing direct
dictionary reference remains:

```lean
PagedTermDictionary.findTermId? dictionary wanted
```

TLI1 needs these targets before it drives an SRI1 join:

```text
decode(encode(dictionary)) = dictionary
lookup(TLI1(dictionary), term) = findTermId?(dictionary, term)
lookup = some id → dictionary[id] = term
```

The host-level range reader must then show that its selected rows equal a
filter of the existing full row scan for the requested subjects. This extends
the present per-row subject-ID check; it does not replace it.

## Delivery order

1. Pure total Lean TLI1 encoder/decoder and reference tests.
2. SBM4 artifact commitment and packer output.
3. Merkle range reader and full structural equality check.
4. Replace the full PTD1 read in `scanEntryForSubjects`.
5. Repack the 889k-triple gene fixture and measure the P682-to-P684 join
   against the current 2.39-second baseline.

This preserves IBK3/SBM3 readers. Existing stores retain the conservative
PTD1 bridge or normal complete materialisation until republished.

The first delivery item is now implemented in
`formal/lean4/L4Factoidal/Storage/TermLocalIndexWire.lean`. It has the TLI1
header, target-IBK3 digest, canonical sorted pages, first-key directory,
strict page/ID checks, and CRC32C validation. Compile-time guards exercise
both a single page and a 257-term two-page round trip. It is intentionally not
now emitted by the IBK3 packer and compactor, referenced by SBM4, and checked
at activation for full digest, Merkle consistency, decoder framing and target
IBK3 digest equality. It is deliberately not yet on the hot query path: the
remaining delivery is the Merkle range reader and its equality-preserving
replacement of the full PTD1 bridge.
