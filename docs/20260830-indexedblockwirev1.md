# Block engine worknote: direct ID-block bytes

Date: 2026-08-30

## Delivered

`L4Factoidal.Storage.IndexedBlockWireV1` serializes the executable indexed
layout directly:

```text
IBK1 magic + version
dictionary count + ID-row count
length-delimited dictionary terms
fixed-width (subjectId, predicateId, objectId) rows
CRC32C payload trailer
```

The decoder validates the framing, CRC, term parsing, duplicate dictionary
keys, row references, RDF subject positions, and predicate positions before it
constructs `IndexedBlock`. It rebuilds the ID lookup table and predicate
partitions from decoded rows. The current V1 support boundary is inherited from
the term codec: RDF-star triple terms and directional literals are refused.

`l4block-id-pack` and `l4block-id-file-query` use V1 directly. The query tool
does not reconstruct a direct-term graph and does not parse Turtle:

```text
IBK1 file -> IndexedBlockWireV1.decode -> IndexedBlock.readOps -> SPARQL SELECT
```

## Checks

`IndexedBlockWireV1Tests` checks a concrete denotation round trip, a
predicate-bound scan round trip, and rejection after a CRC byte is changed.

On `active_site.ttl` (486 triples), the direct ID file was 27,256 bytes,
compared with 64,731 bytes for the earlier direct-term BLK0 file. A persisted
V1 query returned the expected filtered SELECT binding.

On `chromosome.ttl` (9,227 triples), V1 produced a 526,057-byte file. A
separate query-only process executed the parsed `COUNT(*)` over the persisted
file in 0.04 seconds (`/usr/bin/time -p`), returning 9,227 rows. The one-time
Turtle parse and pack remains about 25 seconds on the development laptop and
is outside that query-only figure.

## Remaining assurance and layout work

V1 is a direct ID-row layout, but not yet the requested fully canonical format:

- its dictionary order follows the input graph, rather than a specified global
  term ordering;
- it has one whole block rather than sorted block segments and range offsets;
- its current confidence is executable guards, not a general Lean theorem
  `decode (encode b) = some b` or a denotation-preservation theorem;
- it inherits the restricted term codec.

The next codec revision must settle those points before its bytes become the
common PostgreSQL or TiKV persisted object. V1 nevertheless supplies the
first direct file-to-indexed-SPARQL implementation on which that revision can
iterate.
