# Segmented IBK design decision

Date: 2026-08-30

## 2026-08-30 executable vertical

The first persisted IBK2 vertical is now executable in Lean:

```text
Turtle → l4block-id-v2-pack → .ibk2 → open? → readOpsRange
       → existing DatasetBackend / SPARQL planner → SELECT results
```

`open?` performs one complete structural/CRC validation and retains the
canonical bytes. For a predicate-bound triple pattern, `readOpsRange` calls
`scanBoundRange`, which obtains the fixed prefix, dictionary range, directory
range and exactly one predicate segment through the V2 range contract. The
backend is the existing `BackendReadOps` route, not a second SPARQL evaluator.

The corpus command below succeeds against the 9,227-triple chromosome graph:

```sh
lake exe l4block-id-v2-pack -- ../../docs/fstar-extracted/lifesci/chromosome.ttl /tmp/chromosome.ibk2
lake exe l4block-id-v2-file-query -- /tmp/chromosome.ibk2 --query 'SELECT ?s WHERE { ?s <http://www.wikidata.org/prop/direct/P31> <http://www.wikidata.org/entity/Q37748> } LIMIT 5'
```

This is intentionally not yet a claim of OS-level selective I/O: the Lean
host currently uses `IO.FS.readBinFile` at open. The byte-range contract is
the established seam for a mmap, PostgreSQL `bytea` slice, TiKV value-range,
or WASM/OPFS provider; the next increment must make that provider physically
read only the planned ranges and report its measured byte count.

`l4block-id-v2-range-plan BLOCK.ibk2 PREDICATE-IRI` exposes the exact logical
two-range request (contiguous framing/dictionary/directory, then the selected
segment). Initial measurements are deliberately diagnostic rather than a
performance claim: the 77-triple music block's `ex:by` segment plans 3,513 of
4,621 bytes because its term dictionary dominates, while the single-predicate
chromosome block plans essentially its entire 562,985-byte artifact. A useful
selectivity benchmark therefore needs a larger multi-predicate corpus with a
comparatively smaller shared dictionary.

A 1.3 MiB local country-information corpus supplied a better immediate check:
38,776 triples encoded as a 2,593,670-byte IBK2 artifact, and its `:capital`
segment is 3,936 bytes. The current plan still reads 1,977,186 bytes because
the one shared dictionary has 34,554 terms. That is an honest result: segment
pruning works, but it identifies dictionary structure/filtering as the next
physical design problem. The corpus is local, untracked benchmark input; it
does not become a repository fixture.

## Follow-up: independently decodable predicate shards

The country result identifies a layout limitation, not a reason to abandon
range planning.  IBK2's directory is keyed by numeric predicate `TermId`, and
both resolving an RDF predicate to that ID and decoding result rows presently
depend on the one global term dictionary.  The directory is consequently not
an associative `IRI -> segment` lookup and a tiny selected segment can still
have a very large prerequisite read.

`Storage.PredicateBlocks` now establishes the simpler next abstraction: an
immutable store with one local `IndexedBlock` dictionary per predicate.  A
predicate-bound call uses exactly that local block through the established
`BackendReadOps`/`DatasetBackend` seam; no second SPARQL evaluator is added.
Unbound-predicate scans retain the source sequence until a manifest-level
multi-shard merge has an explicit ordering contract.

The executable probe is:

```text
l4block-predicate-shards INPUT.ttl PREDICATE-IRI
l4block-predicate-query INPUT.ttl --query 'SELECT ...'
```

On the 77-triple music fixture, `http://example.org/music/by` has eight rows,
a 12-term local dictionary, and a 579-byte independently encodable IBK2 block,
against 4,621 bytes for the present shared-dictionary IBK2 artifact.  This is
an executable size observation, not a timing claim.

The persistence design to pursue is therefore a small checked manifest (with
an associative predicate index) plus canonical local block bytes.  A later
alternative may retain a global dictionary with a hash index and paged term
tables, but must demonstrate the same bounded-read property.  Either layout
can use mmap, `pread`, OPFS, PostgreSQL `bytea`, or TiKV range values once its
byte-level manifest and integrity contract are defined.

### Next external corpus: YAGO

YAGO 4.6 is a suitable scale target because its maintainers describe it as
Schema.org-aligned, Turtle-distributed data with 167 million facts. Start from
its published sample, then materialise a documented bounded facts subset;
do not add a full dump to this repository. Downloaded Turtle, generated IBK2
artifacts, timings and logs belong in a separate `factoidal-builds` location,
while this repository retains the fetch URL/version/checksum, import command,
query corpus and measured-result manifest. This gives reproducibility without
turning source control into an artifact store.

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

## Landed initial codec

`Storage.IndexedBlockWireV2` now implements this layout as `IBK2`.  Its
CRC-covered payload is dictionary count, row count, segment count, dictionary
byte length, variable-length dictionary, fixed-width `(predicate, offset,
length)` directory, then 16-byte `(sourcePosition, subjectId, predicateId,
objectId)` segment rows.  The dictionary byte length is essential: it makes
the directory location discoverable from a fixed prefix rather than requiring
the host to speculate across variable-length term encodings.
Directory offsets are relative to the segment area, so the layout does not
depend on the enclosing storage API.

The decoder rejects directory holes/overlaps/trailing data, non-row-aligned or
empty ranges, duplicate predicate entries, a segment row whose predicate does
not equal its directory predicate, and non-contiguous or duplicate source
positions.  A complete decode rebuilds source order before constructing the
existing indexed SPARQL backend.  `scanPredicateDecoded` parses only the
dictionary, directory and requested predicate segment; it is the executable
meaning a future `pread`/mmap/OPFS/TiKV range reader must preserve.

The current function is selective in *decoding*, not yet in host I/O: its
first signature accepts one `ByteArray`.  The next host boundary must expose
range reads so it can retrieve the header/dictionary/directory and one segment
without materialising the rest of the artifact.  This is intentionally a
separate integration step from the canonical byte-format and validation work.

The executable regression gate is `l4block-id-v2-diff INPUT.ttl --query
SELECT...`; it compares ordinary graph evaluation with an `IBK2` full decode
and the existing indexed SPARQL backend.  `l4block-id-v2-segment INPUT.ttl
PREDICATE-IRI` independently compares a source predicate match to
`scanPredicateDecoded`, so it exercises the directory-selected decode path.

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
This executable path was checked on the 27,256-byte active-site artifact using
`openssl dgst -sha256 -binary` to supply the digest file; the verified Lean
query returned `COUNT(*) = 132`.

### Concrete implementation status

The first profile is implemented, rather than merely planned.  The canonical
`IBK1` bytes are framed with CRC32C, and `Storage.BlockArtifact` defines their
SHA-256 content identity.  `IndexedBlockWireV1.decodeVerified` refuses bytes
whose digest does not equal the caller's trusted 32-byte digest; the native
file-query executable exposes that gate through `--digest-file` before it
calls the existing indexed SPARQL path.

The authoritative trust source is intentionally outside the block decoder.
Initially it can be an operator-pinned digest file.  The compatible next
format is a signed snapshot manifest containing at least the digest, `IBK`
format/version, dataset and snapshot identifiers.  For a snapshot containing
many blocks, the manifest may instead commit to an ordered Merkle root, with
each read supplying its block bytes, leaf metadata and inclusion path.  A
Lean-side verifier would recompute the leaf and root before calling
`decodeVerified`; this leaves the block codec and query kernel unchanged.

This yields a clean assurance boundary:

```text
trusted digest / signed manifest / Merkle root + proof
                         |
                         v
                 SHA-256 block-byte check
                         |
                         v
                  CRC + IBK decoder
                         |
                         v
               indexed scan and SPARQL evaluation
```

Neither a digest nor a Merkle tree proves that a host was never tampered with.
They prove a narrower and useful conditional claim: the bytes accepted by the
Lean decoder are the bytes committed by the already-trusted manifest/root.
Key custody, signature validation, manifest distribution, rollback protection
and a database's access-control/audit policy remain deployment obligations.
