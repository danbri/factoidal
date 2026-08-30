# Segmented IBK design decision

Date: 2026-08-30

## Problem

`IBK1` stores all ID rows in one source-order sequence.  Its decoded
`IndexedBlock` has an in-memory predicate partition, but opening the file must
currently decode every row before that partition exists.  This defeats
predicate-bound selective I/O.

## V2 physical rule

`IBK2` will retain the existing shared term dictionary, then contain a checked
directory of predicate segments.  Each segment is contiguous and contains:

```text
predicate TermId
row count
(originalRowPosition, subjectId, predicateId, objectId)*
```

The directory records each segment's byte offset and length.  A predicate-bound
scan can read only its segment.  `originalRowPosition` preserves the current
observable source ordering: rows from a selected segment are reordered by this
position before they reach the existing SPARQL backend.  An unbound scan uses
the same positions to reconstruct all source order.

## Safety gates

- offsets and lengths must lie within the CRC-covered payload;
- segment predicate IDs and each row's predicate ID must agree;
- every original row position is unique and in range;
- decoded terms and row IDs retain V1's validation;
- the first theorem target is denotation equality with the input ordered block,
  followed by equality of predicate-bound `scanBound` results.

This deliberately separates an ordered physical-block codec from later
content-addressed RDF graph normalization.

## Artifact integrity boundary

CRC32C protects framing against accidental corruption; it is not an adversarial
integrity mechanism. Before a block is accepted as an identified dataset
artifact, the host path must verify a cryptographic content hash against a
trusted manifest. A signed manifest should bind the hash, format version,
dataset/snapshot identity, and (for segmented files) directory/segment
identities. The Lean assurance chain is then conditional on the verified bytes
and the trusted signature/key policy; it cannot prove that an operating-system
or database host was never modified.

`Storage.BlockArtifact` now provides the executable SHA-256 identity check and
guards both a matching artifact and a one-byte mutation. It is intentionally
not a signature implementation: a signed manifest and key policy remain the
host/trust layer that supplies the trusted digest.

### Staged assurance profile

Start with the cheapest useful profile: CRC32C for malformed/accidental damage
plus one SHA-256 digest supplied by a trusted caller or deployment manifest.
The next layer is a signed manifest binding that digest to a snapshot and
format version. A Merkle-tree manifest/root is an optional later layer for a
large collection of blocks: it permits compact dataset identity and inclusion
proofs without changing individual block bytes or the Lean query kernel.

The current query executable accepts the first profile directly:
`l4block-id-file-query BLOCK.ibk1 --digest-file SHA256.bin --query 'SELECT …'`.
The digest file is exactly the 32 SHA-256 bytes expected from a trusted
deployment manifest; a mismatch rejects the artifact before SPARQL evaluation.
