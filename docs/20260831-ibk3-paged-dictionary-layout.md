# IBK3: predicate-local rows with a pageable dictionary

## Why a new format

The 889k-triple gene benchmark established that IBK2's fixed row-prefix scan
works but a shared, variable-width dictionary dominates cold small-result I/O.
The existing `PTD1` component already pages a dictionary; `IBK3` composes it
with predicate-local fixed ID rows rather than modifying the experimental
IBK2 format.

## Canonical layout

`L4Factoidal.Storage.IndexedBlockWireV3` defines:

```text
IBK3 magic + version
row count (u32) + PTD1 dictionary byte length (u32)
position, subject-ID, predicate-ID, object-ID × row count
PTD1 canonical dictionary bytes
CRC32C of the post-version payload
```

An IBK3 artifact accepts exactly one predicate.  Its rows retain source
positions, preserving the established `IndexedBlock.Block` denotation and
observable row order.  Its dictionary has the same local array-index `TermId`
meaning as IBK2; no global-ID or vocabulary interpretation is introduced.

## Range plan

The format deliberately places rows before PTD1:

```text
IBK3 header
  -> a row-aligned prefix
  -> PTD1 prefix and fixed page directory
  -> only the PTD1 pages named by subject/predicate/object IDs in those rows
```

The codec now exposes and tests the corresponding `ByteRange` planning APIs.
It also has a pure range-execution kernel: given an exact row-aligned prefix,
PTD1 prefix/directory, and only the absolute PTD1 pages named by those rows,
it reconstructs and filters the same RDF triples as a complete decode. An
omitted, mismatched or malformed page returns `none`, not an empty result and
not an unrelated term. The next adapter supplies those ranges through the
existing Merkle-verified native `pread` boundary.

Empty predicate artifacts are intentionally invalid. A compactor which removes
the last triple for a predicate must remove that artifact and its manifest
entry; it must not write an empty IBK3 file. PTD1 bytes are canonical output
of the current encoder; admission hardening to reject equivalent non-default
PTD1 page sizes is tracked as follow-up work.

## Verification

On 2026-08-31:

```text
lake build L4Factoidal.Storage.IndexedBlockWireV3Tests
lake build L4Factoidal
```

both passed.  The test guards cover canonical full decode/graph denotation,
mixed-predicate rejection, corrupted framing rejection, missing-page
rejection, and the row-prefix to absolute PTD1 page-range plan plus the pure
paged range scan.

## Assurance status

This is executable Lean code with evaluated regression guards, not yet a
universal encode/decode theorem.  It depends on the existing PTD1 codec and
inherits its currently supported RDF-term subset.  The next proof work should
make the IBK3 decode/encode denotation-preservation claim explicit rather
than relying only on the guards.
