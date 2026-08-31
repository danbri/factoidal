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

The reference `l4block-shard-pack` now uses that seam directly. It makes two
fixed-size file-handle passes: the first calculates the generated blank-node
prefix and streaming SHA-256 source identity; the second performs bounded
UTF-8 decoding and immediate Turtle statement folding. The input digest is
checked again before the final manifest is published. Since block files are
written during that second pass, a changed input can leave unreferenced output
files, but it cannot publish a manifest that commits them; staging-directory
cleanup is a separate operational refinement. The full
`blockengine-shard-merkle-scan-smoke.sh` suite passes through this actual
packer, including verified Merkle range reads and parsed SPARQL execution.

## Multi-block publication prerequisite

The original SBM0/SBM1 invariant deliberately required exactly one artifact
per predicate, which would merely move the memory wall to a very frequent
predicate such as Wikidata `P31`. SBM2 now retains the same fixed-chunk Merkle
entry encoding while permitting multiple immutable IBK2 artifacts for a
predicate. Its verified opener, predicate scan and exact unbound-predicate
row estimate aggregate all matching entries in manifest order. SBM0/SBM1 keep
their unique-predicate acceptance rule; Merkle query/session hosts accept both
range-committed SBM1 and SBM2. Executable guards cover SBM2 encode/decode and
two committed blocks returning/estimating two rows.

## Landed bounded SBM2 publisher

`l4block-shard-pack` now publishes SBM2 directly. Its parser fold accumulator
contains only complete triples encountered since the current bounded
publication batch. It continues UTF-8/Turtle decoding in 64 KiB increments,
then partitions and publishes every 64 such chunks (about 4 MiB of source),
encodes each resulting IBK2 block, writes its leaf-hash sidecar, and retains
only manifest/TSV metadata for it. The final `manifest.sbm2` is written only
after the second source digest agrees with the pre-pass commitment. This makes
the manifest the atomic logical publication boundary: artifacts written before
it are not part of a readable collection.

The deliberate trade-off is that a frequent predicate may have one immutable
block per input batch. SBM2's repeated-predicate entries preserve all those
rows, and the Merkle SPARQL query/session tools now discover `manifest.sbm2`
first (falling back to older SBM1 collections) and select every matching
block. The executable smoke suite demonstrated a parsed two-predicate join
over four selected artifacts and a warm-session cache hit over the same SBM2
store. A future compaction pass can merge/re-sort those bounded artifacts
without weakening the decoder, byte commitment, or SPARQL backend contract.

The only remaining non-fixed-size parser memory is an individual unfinished
Turtle statement, which must be retained to preserve grammar semantics. That
is a documented input limit rather than a whole-corpus graph construction.

## Re-run of the gene gate

The same 20-second cap was re-run after the bounded publisher landed. It
again exited with `124`, as expected for the cap, but had written 899 regular
output files before interruption (artifact/sidecar pairs; no `manifest.sbm2`
was present). This is the expected safe intermediate state: the old packer
had written zero artifacts at the same point, while the new packer has made
forward physical progress without exposing an incomplete collection to a
reader. It is evidence of the new publication boundary, not a claim that the
17 MiB source completes in twenty seconds.
