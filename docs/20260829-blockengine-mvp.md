# Block engine MVP: executable in-memory scan

Date: 2026-08-29 to 2026-08-30

## Decision

The first runnable block-engine vertical is an immutable in-memory block that
uses existing RDF terms directly. It does not allocate persistent `TermId`
values yet. Persistent IDs require the RDF 1.2 identity decision recorded in
[`20260829-blockengine-baseline.md`](20260829-blockengine-baseline.md).

## Delivered shape

`L4Factoidal.Storage.BlockMvp` defines:

```text
Block.rows : Graph
Block.denotes : Block -> Graph
scanRows : TriplePattern -> List Triple -> Binding -> SolutionSeq
scan : TriplePattern -> Block -> Binding -> SolutionSeq
```

`scanRows` is a direct recursive traversal. It uses the existing total SPARQL
`tpMatch` operation for every row. The theorem
`scan_eq_evalTP` proves exact equality with `SPARQL.evalTP` through
`Block.denotes`. The equality preserves row order and solution multiplicity.

`BlockMvpTests` adds build-time guards for a bound-predicate scan and a
repeated-variable pattern. It also prints the theorem's axiom audit.

`l4block-mvp` is the native executable fixture. It prints the result-row count
for a parsed SPARQL `SELECT` query. Its built-in query checks for two rows;
an argument query prints its rows and exits successfully when it parses and
evaluates.
Its block-backed `BackendReadOps.search` function is `scanBound`, whose theorem
equates it to `tripleMatchesBound`. The established SPARQL backend evaluator
then performs planning, triple-pattern matching, projection, and ordering.

The fixture accepts a SPARQL `SELECT` query as arguments. With no arguments it
runs its built-in ordered name query:

```bash
./.lake/build/bin/l4block-mvp
./.lake/build/bin/l4block-mvp 'SELECT ?person ?label WHERE { ?person <http://example.org/name> ?label } ORDER BY ?person'
./.lake/build/bin/l4block-mvp 'SELECT ?person WHERE { ?person <http://example.org/name> "Alice"@en . FILTER(?person = <http://example.org/alice>) }'
```

For a real-Turtle BLK0 probe, see
[`20260830-blockengine-corpora.md`](20260830-blockengine-corpora.md) and run
`l4block-corpus`.

## What this tests

The MVP tests the central implementation route:

```text
existing SPARQL matcher
  -> physical row traversal
  -> block denotation
  -> theorem to semantic evaluator
  -> executable build-time tests
```

It shows that the proposed refinement route is viable in the current Lean tree.
It does not test persistent dictionaries, sorted layouts, codecs, PostgreSQL,
TiKV, PushIR, or performance.

This is full query parsing and the current SELECT evaluator over the block
backend; it is not a claim that every SPARQL form runs natively in a physical
block plan. `StoreDataset` routes BGP, JOIN, UNION, MINUS, and constant GRAPH
patterns through backend search, and materialises other forms before using the
semantic algebra evaluator.

## Byte-boundary increment

`Storage.BlockWireV0` introduces a versioned `BLK0` transition format:

```text
direct-term Block -> BLK0 bytes -> decoded Block -> backend candidate scan
```

The native fixture now stores its test block as `BLK0` bytes and decodes those
bytes for every backend search. Its output records the byte length and decode
status. `scanDecoded_eq_evalTP` and
`scanBoundDecoded_eq_tripleMatchesBound` carry the existing scan meanings
across any successful decode.

V0 reuses the established delta-log triple codec. It refuses RDF 1.2 triple
terms and directional literals, retains input row order, and has fixture-level
round-trip guards only. It is not the planned canonical TermId block codec and
does not authorise PostgreSQL or TiKV persistence yet.

Part Three treats this scan as the first future `PhysicalPlan.scan`
implementation. It is not yet a plan AST or S-expression format. Add those
after the identity, dictionary, and first sorted-scan work, so plan syntax does
not prematurely fix the persistent `TermId` contract.

The architecture therefore has one confirmed seam and three remaining design
gates:

1. Define RDF 1.2 term identity before persistent IDs.
2. Generalize Cottas's per-role dictionary model into one cross-position ID
   relation without losing its access-path proofs.
3. Keep PostgreSQL and TiKV behind byte, range, and snapshot contracts. Their
   adapters need explicit agreement with the pure block model.

## Commands

From `formal/lean4/`:

```bash
/Users/danbri/.elan/bin/lake build l4block-mvp
./.lake/build/bin/l4block-mvp
```

Verified on 2026-08-30:

```text
lake build l4block-mvp  -> Build completed successfully (104 jobs)
l4block-mvp default     -> rows=2; exit 0
l4block-mvp FILTER      -> rows=1; exit 0
lake build               -> Build completed successfully (742 jobs)
```

## Next increment

After this module builds, add an explicit RDF 1.2 term-identity decision.
Then replace direct terms with a local dictionary relation, keep the same
denotation theorem, and add one sorted permutation with a bounded scan. Then
define a canonical block-byte format before persistence: prove decoded
canonical bytes preserve the block denotation, and prove their scan against
`evalTP`. PostgreSQL `bytea` and TiKV can then hold the same physical object.
Wrap that decoded scan in a small typed physical-plan tree and give that tree a
closed S-expression renderer as described in
[`2026-08-blockengine_part3.md`](2026-08-blockengine_part3.md).
