# Pageable term dictionary prototype

## Why this exists

The completed 889k-triple gene benchmark exposed a specific cold-read limit
in the current IBK2 layout. Predicate rows are properly contiguous and a
single-pattern `LIMIT` scan now stops after a Merkle-verified row prefix, but
the block has to first read its complete variable-width term dictionary. For
the P1057 `LIMIT 5` probe this was 959,508 logical bytes, compared with
1,586,092 bytes for the unbounded predicate scan. The prefix mechanism is
working; the dictionary is now the dominant cost.

## Landed inner component

`L4Factoidal.Storage.PagedTermDictionary` defines a self-contained,
versioned `PTD1` canonical byte representation:

```text
magic + version
term count + terms/page + page count
fixed page directory: (offset, length)*
canonical term bytes, concatenated by page
CRC32C
```

Pages currently contain 256 consecutive `TermId` positions. The reader can:

1. read the fixed prefix and tiny page directory;
2. map a `TermId` to the one page containing it;
3. verify/fetch that page through the enclosing artifact Merkle commitment;
4. decode just that page and obtain the requested RDF term.

The component also plans distinct pages for a list of row IDs in deterministic
first-use order, so a future block reader can turn a decoded row prefix into a
small, de-duplicated list of term-page range reads. Its complete decoder
validates every declared page boundary, not only the concatenated term stream.

The module has full encode/decode round-trip guards and a two-page (257 term)
boundary guard that resolves the first term of the second page through the
range-planning API. It is imported by the Lean umbrella module, so this is
compiled as part of the normal library build.

## Status and next integration

PTD1 is deliberately an **inner-component prototype**, not yet a claim that
existing IBK2 artifacts changed format. It retains the inherited supported
RDF-term subset and array-index `TermId` meaning. The next compatible physical
successor should embed this layout in a new block version (rather than mutate
IBK2), retain predicate segments and source-position semantics, and extend
the manifest/packer/query hosts only after a full canonical decode and
denotation-preservation test exists.

This gives a concrete, measured direction for lowering cold small-limit I/O
without introducing a separate Rust engine or backend-specific RDF model.

## Measured projection on the gene corpus

The new `l4block-paged-dictionary-probe` fully opens an existing IBK2 artifact
only to make a fair offline comparison, then reports what PTD1 would need for
the first N ID rows. It is now part of
`tools/blockengine-gene-shard-benchmark.sh`; it does not change that
benchmark's published artifacts.

For the 18,890-row P1057 artifact (1,196,216 IBK2 bytes), the first five rows
refer to 15 IDs which fall in a single 256-term PTD1 page. Its full dictionary
would be 894,584 PTD1 bytes, but its directory plus required page is only
12,121 bytes (641 bytes of planning plus 11,480 bytes of term page). The
second 6,168-row P1057 artifact similarly projects to 11,855 bytes. A future
IBK3 query will additionally need the row-prefix read and fixed Merkle chunks,
so these figures are deliberately **dictionary-only projections**, not an
end-to-end latency or I/O claim.
