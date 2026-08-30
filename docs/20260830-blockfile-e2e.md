# Block engine worknote: persisted file to SPARQL

Date: 2026-08-30

## Delivered

Two native executable-edge tools complete the current persistence vertical:

```text
l4block-pack INPUT.ttl OUTPUT.blk0
  Turtle -> direct-term Block -> framed BLK0 bytes

l4block-file-query BLOCK.blk0 --query 'SELECT ...'
  bytes -> checksum/version decoder -> graph -> IndexedBlock -> SPARQL backend
```

The reader rejects malformed, wrong-version, unsupported, or checksum-failing
BLK0 data before it constructs the query block. It does not parse Turtle.
After decode, it builds the shared `TermId` dictionary and predicate partition
once and exposes `IndexedBlock.readOps` through `DatasetBackend`.

The confirmed file-to-query run uses `active_site.ttl`:

```text
input triples: 486
framed file bytes: 64,731
query: SELECT ?object with a predicate BGP and subject FILTER
result: http://www.wikidata.org/entity/Q423026
```

## Boundary

This is durable byte input, but it is not the canonical block persistence
format. BLK0 stores direct terms, then the reader reconstructs the in-memory
ID block. It lacks a cross-position dictionary encoding, block segmentation,
range offset index, and general codec round-trip theorem. It is therefore a
working end-to-end file path and an API seam for memory mapping or PostgreSQL
`bytea`, not the final data format for either.

The next replacement must define canonical bytes for the `IndexedBlock` shape
itself and prove its decoded denotation. The query executable should then open
that object directly, without the direct-term graph reconstruction step.
