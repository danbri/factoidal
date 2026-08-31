# IBK2 `gene.ttl` ingest gate — 2026-08-31

## Reproducible bounded observation

The current native reference packer was run once against
`examples/wikidata/subsets/lifesci-kgx/data/gene.ttl` (17 MiB; the checked-in
KGX README records 888,949 triples) with a 20-second external wall-clock cap:

```text
gtimeout -s INT 20 l4block-shard-pack gene.ttl OUTPUT-DIR
```

It consumed 20.00 seconds wall time / 19.85 seconds user CPU, exited with the
expected timeout status `124`, and had emitted zero output artifacts. The run
was synchronous and no packer remained running afterwards.

This is intentionally a **gate**, not a throughput result. It establishes
that the current reference encoder cannot publish a usable partial store while
it is still parsing and retaining the full source/buckets. Recent improvements
remove repeat character-list allocation and expected linear predicate-bucket
lookup, but are not enough to change that architectural boundary.

## Consequence

The next implementation must make a true input/event boundary:

1. incremental UTF-8 decoding and Turtle statement parsing while retaining
   prefix/base/mode/blank-node state;
2. a pre-pass or equivalent bounded method for the collision-safe generated
   blank-node prefix and source commitment;
3. bounded predicate/graph spool partitions and immutable IBK2 publication;
4. publication of the SBM1 manifest only after all artifact and Merkle
   commitments have succeeded.

Splitting merely on newlines is explicitly not an acceptable substitute: valid
Turtle permits multi-line strings, comments, directives, blank-node property
lists and collections.

## Landed prerequisite

`L4Factoidal.Crypto.Sha256Stream` now absorbs public source bytes
incrementally, retaining only a final under-64-byte compression tail. Its
chunked digest agrees with the ordinary SHA-256 implementation for both
three one-byte chunks and a 55/1-byte split of the FIPS two-block vector. A
streaming loader can therefore retain the existing SBM1 source-identity
commitment without retaining all source bytes just to call `sha256`.

`TurtleState.initWithBnodePrefix` is also now the explicit parser boundary
for the pre-pass result. The existing whole-document and character-list
initializers are compatibility wrappers around it, and regression guards pin
the same generated prefix. This prevents an eventual stream reader from
quietly changing blank-node identities while optimizing input handling.

`L4Factoidal.Syntax.Utf8Stream` now supplies the byte-read boundary. It
buffers only a syntactically valid partial UTF-8 code point (at most three
bytes), rejects malformed interior data such as `FF`, and has executable
tests for both two- and four-byte code points split across reads. Turtle event
parsing remains above this layer, so these checks do not conflate decoding with
statement segmentation.

`TurtleStatementScan` and `TurtleChunkFold` now supply the grammar-aware
decoded-text boundary. The scanner carries IRI, comment, short-string and
long-string lexical state across chunks and offers only dotted candidates (and
ordinary line-separated `PREFIX`/`BASE`/`VERSION` candidates) to the existing
`readStatement` parser. `TurtleChunkFold` drains and folds each accepted
statement immediately, preserving Turtle prefix/base/mode/blank-node state.
Executable equivalence guards compare it with `parseTurtle` across cuts inside
IRIs, triple-quoted multi-line strings, blank-node syntax, numeric dots and
no-dot prefix directives. This is a real parser-event seam; a file-handle
driver and bounded artifact spooler are still the next integration steps.
