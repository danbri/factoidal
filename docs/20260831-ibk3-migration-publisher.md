# IBK2 to IBK3 migration publisher

`l4block-id-v3-convert` converts one predicate-local IBK2 artifact into a
one-entry, integrity-addressed IBK3 store. It is a test and migration tool,
not the planned streaming Turtle publisher.

Its input admission check confirms that every decoded IBK2 row has the
supplied predicate. Its output directory contains:

- `predicate-0.ibk3`, encoded with the IBK3/PTD1 layout;
- `predicate-0.ibk3.merkle`, 64 KiB leaf hashes; and
- `manifest.sbm2`, committing the source identity, artifact SHA-256, chunk
  commitment, predicate, row count and IBK3 layout identity.

The first real-corpus exercise converted the 36,056-row Wikidata direct
property P684 gene artifact into a 2,061,235-byte IBK3 file. This provides a
stable input for the next native, Merkle-verified paged-range query host,
without conflating that experiment with Turtle ingestion performance.

The current converter is deliberately non-destructive: it refuses an output
path that already exists.
