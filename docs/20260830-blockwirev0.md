# Block engine worknote: BLK0 byte boundary

Date: 2026-08-30

Commit base: `73209342c23212dca31d7f9ef7dbc37cbbdab814`

## Delivered

`L4Factoidal.Storage.BlockWireV0` adds a versioned `BLK0` direct-term block
format. It contains a magic number, version, row count, the established
length-delimited triple encoding from `Storage.DeltaLog`, and a CRC32C trailer
over the triple payload.

`decode` rejects a wrong magic, a wrong version, a checksum mismatch, malformed
triples, and trailing bytes. `scanDecoded` and `scanBoundDecoded` decode first, then invoke the
existing proved block scans. Their theorems recover `evalTP` and
`tripleMatchesBound` whenever a byte sequence decodes to a block.

`l4block-mvp` now encodes its fixture to BLK0 bytes and gives the byte decoder,
not the construction-time block, to the SPARQL backend seam.

## Boundary

This is not a persistent block format:

- it uses direct RDF terms, not a cross-position TermId relation;
- it preserves source row order and has no sorted access path;
- it inherits the delta codec refusal of RDF 1.2 triple terms and directional
  literals;
- it has executable fixture round trips, not a general encode/decode or
  denotation-preservation theorem.

It therefore demonstrates the required byte-to-semantic execution shape while
leaving the canonical-codec persistence gate intact.

## Checks

From `formal/lean4/` on 2026-08-30:

```text
lake build L4Factoidal.Storage.BlockWireV0      -> Build completed successfully (10 jobs)
lake build L4Factoidal.Storage.BlockWireV0Tests -> Build completed successfully (11 jobs)
lake build l4block-mvp                          -> Build completed successfully (106 jobs)
l4block-mvp                                    -> BLK0 bytes=269, decoded=true, rows=2
lake build l4block-corpus                       -> Build completed successfully (110 jobs)
lake build                                      -> Build completed successfully (742 jobs)
```

`BlockWireV0Tests` also changes one CRC byte of its fixture and checks that
`decode` returns `none`.

## Next unit

Settle RDF 1.2 identity, then introduce a cross-position TermId dictionary and
one sorted block layout. Its canonical codec must prove exact decode/encode or
denotation preservation before PostgreSQL `bytea` or TiKV stores it.
