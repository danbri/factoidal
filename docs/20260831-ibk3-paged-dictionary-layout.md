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
The current increment establishes canonical full decode and planning; a
subsequent range executor will assemble supplied term pages and apply the
same SPARQL scan semantics under the existing Merkle admission boundary.

## Verification

On 2026-08-31:

```text
lake build L4Factoidal.Storage.IndexedBlockWireV3Tests
lake build L4Factoidal
```

both passed.  The test guards cover canonical full decode/graph denotation,
mixed-predicate rejection, corrupted framing rejection, and the row-prefix to
absolute PTD1 page-range plan.

## Assurance status

This is executable Lean code with evaluated regression guards, not yet a
universal encode/decode theorem.  It depends on the existing PTD1 codec and
inherits its currently supported RDF-term subset.  The next proof work should
make the IBK3 decode/encode denotation-preservation claim explicit rather
than relying only on the guards.
