# IBK3 parsed-query host packaging boundary

Status: landed. `Harness/IndexedBlockV3Materialize.lean` is the shared,
importable physical-reader layer used by both native IBK3 front ends.

The direct IBK3 publisher and native Merkle predicate scanner are executable
Harness targets. The established ordinary parsed-SPARQL host currently uses
the same evaluator path for IBK2 (`Harness/ShardMerkleQuery.lean`), but a new
IBK3 counterpart must not import one executable Harness root from another:
Lean exposes a top-level `main` from such a root, causing a duplicate-main
declaration in the importing executable.

The implementation uses this explicit split:

```text
Harness/IndexedBlockV3Materialize.lean   importable physical library
    - manifest entry admission
    - Merkle-verified range reads
    - paged IBK3 materialisation and I/O evidence

Harness/IndexedBlockV3MerkleScan.lean    thin predicate-scan CLI
Harness/IndexedBlockV3Query.lean         thin parsed-SPARQL CLI
```

The physical library has no top-level `main`; the two front ends share the
exact scan implementation rather than duplicating file-range logic. This is a
packaging boundary only: it does not weaken the existing pure byte-decoding or
SPARQL-evaluation contracts.
