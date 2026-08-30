# Roaring bitmaps in Lean 4

Status: design input for the block engine

Date: 2026-08-29

## Decision

A verified Roaring32 implementation is feasible and relevant to the block
engine. It belongs after the first uncompressed block and scan vertical.

Use Roaring32 for block-local integer sets such as:

- matching row offsets;
- predicate or graph postings;
- candidate sets produced by pruning;
- intersections between access paths;
- sparse presence data.

Do not use Roaring32 as the global RDF `TermId` domain. A block-local row
offset can stay below `2^32` even when the global term dictionary uses 64-bit
IDs. This keeps the portable Roaring32 format useful and avoids making the
less-uniform Roaring64 formats part of the first storage contract.

Roaring does not replace the sorted quad block, dictionary, manifest, or
backend transaction model. It is one representation for sets inside that
system.

No established public Lean 4 Roaring package was identified during this
2026-08-29 review. Recheck the package ecosystem before starting a new
library.

## Format and semantic model

The [portable Roaring format specification](https://github.com/RoaringBitmap/RoaringFormatSpec/)
partitions a 32-bit value into a high 16-bit container key and a low 16-bit
value. Each non-empty container is one of:

- an array of sorted 16-bit values, for cardinality at most 4096;
- an 8192-byte bitset, for cardinality above 4096;
- sorted, non-overlapping runs.

The format uses little-endian values and defines cookies, container metadata,
optional offsets, and the byte representation of all three container forms.

A suitable Lean shape is:

```lean
inductive Container
  | array  : Array UInt16 -> Container
  | bitmap : ByteArray -> Container
  | runs   : Array Run -> Container

structure Roaring32 where
  containers : Array (UInt16 × Container)
  valid : ValidContainers containers
```

The proof-level meaning should be independent of this layout:

```lean
def Roaring32.Denotes (r : Roaring32) (x : UInt32) : Prop := ...
```

Initial theorem targets:

```text
mem_union:
  Denotes (union a b) x ↔ Denotes a x ∨ Denotes b x

mem_intersection:
  Denotes (intersection a b) x ↔ Denotes a x ∧ Denotes b x

cardinality_correct:
  cardinality r = Finset.card {x | Denotes r x}

decode_encode_denotes:
  decode (encode r) = some r' → Denotes r' = Denotes r
```

The portable format permits more than one byte encoding for some equal
bitmaps. Therefore the main codec theorem must be semantic preservation.
Canonical byte equality is a separate theorem for an encoder with one chosen
normal form.

## Relation to landed Cottas work

The Lean Cottas tree already has flat row-group presence bitmaps, writers,
parsers, bit tests, compound presence information, and pruning soundness
contracts. Roaring can generalize one part of this work:

```text
Cottas flat presence bytes
        │
        ├── current reader/writer agreement
        └── current pruning soundness condition
        │
        ▼
backend-neutral CandidateRows meaning
        │
        ├── flat bitmap realization
        └── Roaring32 realization
```

The first Roaring integration theorem should state that both realizations
denote the same candidate row set. The existing Cottas path can then serve as
a differential oracle during development.

## Lean representation and performance

Pure Lean has a packed `ByteArray`. It does not currently have equivalent
packed `UInt16Array`, `UInt32Array`, or `UInt64Array` types. The open Lean issue
[lean4#14050](https://github.com/leanprover/lean4/issues/14050) proposes native
wide loads and stores on `ByteArray` for codecs and dense integer workloads.

This matters most for an 8192-byte bitset container. The desired fast loop
uses 1024 64-bit words for Boolean operations and population counts. A first
pure Lean implementation can use exact `ByteArray` bytes and simple reference
operations. Measure that version before adding foreign primitives.

If profiles later justify native operations, keep the boundary small:

```text
loadUInt64LE
storeUInt64LE
popcount64
andWords
orWords
xorWords
andNotWords
```

Each operation needs a total pure Lean meaning and an agreement method. The
[Lean FFI reference](https://lean-lang.org/doc/reference/latest/Run-Time-Code/Foreign-Function-Interface/)
states that the current FFI is unstable. Keep database and ABI shims outside
the semantic API.

Wrapping all of CRoaring would give high native speed with a large external
assurance boundary. That is useful as a benchmark and interoperability oracle,
but it is not the default engine implementation.

## Staged work

### R0 — specification and one container

- Define a finite-set meaning for values below `2^32`.
- Implement a sorted array container.
- Prove membership, cardinality, union, and intersection.

### R1 — portable decoder and encoder

- Parse the official test data.
- Add bitset and run containers.
- Prove decoder bounds and semantic codec preservation.
- Test Lean-produced bytes in C, Java, or Go reference implementations and
  read their bytes in Lean.

### R2 — all container-pair operations

- Prove the nine array, bitset, and run intersection combinations.
- Add union, difference, exclusive-or, rank, select, and iteration as demand
  requires.
- Keep a simple extensional implementation for differential checks.

### R3 — block-engine integration

- Define `CandidateRows` independently of representation.
- Add flat-bitmap and Roaring32 realizations.
- Prove both preserve the same block-scan candidate meaning.
- Benchmark RDF distributions from the block-engine corpus.

### R4 — measured native acceleration

- Profile the generated C path.
- Add only the word operations that have a measured effect.
- Run pure Lean, native primitive, and CRoaring differential tests.
- Record the external boundary in Factoidal evidence.

## Order relative to the block-engine plan

The first block milestone remains:

```text
RDF term identity
  -> TermId and GraphId
  -> simple immutable block
  -> block denotation
  -> one scan and refinement theorem
```

Roaring starts after this milestone. It can then improve candidate-set and
posting-list representation without changing the block denotation or SPARQL
semantics.
