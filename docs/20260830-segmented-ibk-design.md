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

### Native positioned-read probe

`l4block-id-v2-pread BLOCK.ibk2 PREDICATE-IRI` is the first actual host
realisation of that boundary. It is a native-only executable-edge adapter: a
small POSIX C `pread` bridge reads exactly the pure Lean `ByteRange`s, while
the Lean code performs prefix/directory planning and `scanPredicateRanges`.
It is deliberately not imported by the WASM closure and contains no RDF or
SPARQL logic.

On the deterministic 77-triple music fixture, the `ex:by` scan returns eight
rows after reading 3,513 bytes of a 4,621-byte `IBK2` artifact. The number is
a byte-accounting result, not a throughput claim. The shared dictionary still
dominates this small artifact; predicate-local Shardborough blocks remain the
more useful immediate layout for that case.

This probe assumes a trusted/admitted artifact identity. `pread` alone cannot
prove that a file has not changed since admission; the full SHA-256/manifest
check remains the integrity boundary, with later Merkle range proofs as the
way to combine independent range reads with per-read cryptographic evidence.
Run `tools/blockengine-v2-pread-smoke.sh` after building the two native
executables to exercise the C/Lean boundary and its expected byte count.

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

### Lean Merkle proof primitive (landed)

`L4Factoidal.Storage.BlockMerkle` now supplies the format-neutral core for the
later profile: domain-separated SHA-256 leaf and interior-node hashes,
deterministic duplication of an odd final leaf, and compact ordered sibling
proofs. Its executable guards accept all three chunks of a sample artifact,
reject a substituted chunk under a genuine proof, and reject an out-of-range
proof request. This is intentionally not yet `SBM1`: no current `SBM0` reader
claims partial-range integrity from a whole-file SHA-256 digest. The next wire
format must bind its chunk size/alignment, algorithm and Merkle root, then a
native/PostgreSQL/TiKV range reader can admit only the fetched chunks plus
their proof before invoking the existing IBK2 range decoder.

`L4Factoidal.Storage.ChunkedArtifact` now makes that host contract explicit:
the trusted sidecar binds total byte length, fixed chunk size/count and Merkle
root. Given a chunk index, the Lean validator derives its exact byte offset and
permitted length (including the short final chunk), then accepts supplied bytes
only if their inclusion proof reaches the declared root. Guards cover valid
first/final chunks, substituted content, out-of-range indices and an
inconsistent chunk count. This is the direct interface an SBM1 entry should
embed; it is still deliberately separate from the stable SBM0 wire format.

### SBM1 wire commitment (landed)

`ShardManifest` now accepts both `SBM0` and `SBM1`. SBM0 remains byte-for-byte
the existing layout and permits no range-integrity claim. SBM1 preserves every
SBM0 artifact field and appends, per artifact, a fixed chunk size, chunk count
and 32-byte Merkle root. Version-one validation requires that this commitment
has the artifact's declared total byte length and a valid derived count;
unknown versions remain rejected. Both version-zero and version-one
encode/decode round trips are guarded in Lean. The packer emits SBM1 plus a
compatibility SBM0 manifest and untrusted per-artifact leaf sidecars; existing
query hosts prefer SBM1 where it is present while retaining an SBM0 fallback.

### Proof-carrying positioned reads and a verified-range scanner (landed)

`l4block-shard-merkle-pread SHARD-DIR PREDICATE-IRI [OFFSET LENGTH]` consumes
the SBM1 commitment and `.merkle` sidecar. It verifies every fixed chunk
touched by the requested non-empty range through the artifact's committed root
before returning its interior bytes. A malformed sidecar, wrong leaf count,
short positioned read, invalid proof, or out-of-bounds range is a refusal;
there is no unchecked-read fallback.

`l4block-shard-merkle-scan` is the first consumer which turns those admitted
bytes back into RDF values. It obtains the IBK2 fixed prefix, dictionary,
directory and selected predicate segment through `readVerifiedRange?`, then
calls the existing `scanPredicateRanges`. Its input is therefore four
structurally required IBK2 ranges, each verified to the SBM1 root, rather than
a whole artifact admitted by a SHA-256 check.

`tools/blockengine-shard-merkle-scan-smoke.sh` packs the 6,455-triple
life-sciences `sequence_variant.ttl` source. Its P31 artifact is 110,020 bytes:
the smoke first verifies `[65000, 66000)` across chunks 0 and 1, then obtains
1,800 P31 rows and 1,357 P1057 rows through the verified-range scanner. The
reported `logical-read-bytes` excludes the four-byte IBK2 CRC trailer, which
this narrow selective decoder does not need; it is not a physical-I/O or cache
claim.

The standalone scanner is a predicate-local physical primitive. Its parsed
SPARQL integration is `l4block-shard-merkle-query`, which accepts the
same ordinary parsed SELECT surface as `l4block-shard-query`, but only for the
already-conservative native fragment in which every triple pattern has a
constant IRI predicate. It selects those predicate-local entries, verifies
each artifact's required IBK2 ranges, checks the scanned row count against the
manifest entry, materialises the admitted triples, and invokes the existing
`DatasetBackend` evaluator. Its output labels the route
`predicate-selective-merkle(n)`. Queries outside that syntactic fragment are
explicitly refused by this host rather than silently falling back to unchecked
range reads; `l4block-shard-query` remains the full-manifest reference path.

`l4block-shard-merkle-session` makes that same admitted material useful for a
bounded sequence of newline-delimited SELECTs. The first reference to an
artifact verifies and decodes its required ranges; later queries reuse only
the immutable in-process triples already admitted under the same manifest.
The session prints separate cache-hit/cache-miss and newly-verified-byte
counts. This is deliberately a process-scoped warm cache, not a claim that
the on-disk artifact remains unchanged after admission: manifest generation,
snapshot replacement and cross-process cache invalidation remain explicit
host-policy work.

The native materializer coalesces IBK2's framing, dictionary and directory
into the one canonical `planningRange` before requesting it from the range
host. It still reads the fixed prefix first to discover the planning extent,
then reads the selected segment. A per-artifact verified-chunk cache now
eliminates the temporary overlap between discovery, planning and segment
reads: a cache miss is always a positioned read followed by the SBM1 Merkle
check, while a cache hit reuses only bytes already admitted in that process.

The warm Merkle session now reports distinct `logical-bytes`,
`requested-range-bytes`, `fetched-chunk-bytes`, `verified-chunks` and
`range-requests` fields, plus cache hits/misses and `integrity=sbm1-merkle-verified`.
For the two-artifact life-sciences join, the current uncached host reports
192,847 logical bytes, 192,889 explicitly requested bytes (the prefix is used
to plan then appears in the planning range), and 192,855 full fixed-chunk bytes
obtained by `pread` across four independently verified chunks. The latter is
the complete size of the two selected artifacts, including their framing,
because the fixed 64 KiB Merkle chunks span the requested portions. The following
P31-only query is a cache hit and reports zero new logical/requested/fetched
bytes and chunks. These numbers are measured host-boundary accounting, not a
throughput claim and not an assertion about OS page-cache behaviour.

The native Merkle query driver also has an initial non-executing
`--explain SELECT...` surface. It prints the existing SPARQL SSE under an
`(explain ...)` form, the manifest-selected predicate scan nodes, their
declared row estimates, local-file placement and the SBM1/Merkle admission
requirement. It neither opens nor decodes a child artifact. This is the first
planned-explanation projection; `EXPLAIN ANALYZE` still needs the structured
per-node runtime measurements described in `20260830-query-observability.md`.
