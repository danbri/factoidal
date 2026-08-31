# Parsed SPARQL over direct IBK3 storage

The IBK3 native path now has a shared importable physical reader,
`Harness/IndexedBlockV3Materialize.lean`. It performs manifest admission,
Merkle-verified positioned reads, PTD1 page planning, paged decode, and
materialisation. Two thin executables use it:

- `l4block-id-v3-merkle-scan` for a bounded predicate scan with explicit I/O
  evidence; and
- `l4block-id-v3-query` for ordinary parsed `SELECT`, `ASK`, and `CONSTRUCT`
  over the conservative constant-predicate fragment.

Manifest keys are admitted as leaf names only: empty names, `/`, and `\\` are
rejected before an artifact path is constructed. A query never supplies an
artifact path; it can only select entries already admitted from `manifest.sbm2`.

The query executable does not introduce another query evaluator. It parses
SPARQL, selects exactly the manifest artifacts for its constant predicates,
materialises those through the shared verified IBK3 reader, then invokes the
existing Lean `runSelectQueryBackendDataset`, `runAskQueryBackendDataset`, or
`evalConstruct` evaluator. Thus joins, filters, projection, modifiers, ASK
booleans, and graph construction retain their established semantics.

## End-to-end check

Against the directly published `binding_site.ttl` collection, this query:

```sparql
SELECT ?x ?parent WHERE {
  ?x <http://www.wikidata.org/prop/direct/P31> ?type .
  ?x <http://www.wikidata.org/prop/direct/P361> ?parent .
}
LIMIT 5
```

returned five joined rows. Its diagnostic S-expression shows the parsed BGP
and slice; physical admission reported two selected shards and 25,311 logical
bytes / 25,327 fetched bytes.

This is not yet a complete remote SPARQL service. It deliberately rejects
unbound-predicate plans, named-graph routing, SERVICE, and update/delta
composition until those physical plans are separately connected to the
corresponding existing semantics.

## Durable update replay

The query host now composes the existing epoch-aware DLOG reader and
`mergeOnRead` backend seam with the verified IBK3 base. It therefore uses the
same durable update framing, compacted-epoch filtering, and malformed-sidecar
refusal already exercised by the IBK2 path.

An `INSERT DATA` into the direct IBK3 test store committed one DLOG batch at
epoch 1. A subsequent parsed query for the inserted P31 object reported
`delta=base-plus-delta` and returned the inserted subject. The writer still
rejects update forms which require WHERE evaluation or fresh blank-node
allocation; those remain the next explicitly scoped update extensions.

The reciprocal `DELETE DATA` then committed a second clean batch. Re-running
the same query reported `delta=base-plus-delta` and zero rows; DLOG inspection
reported two committed batches with no torn suffix. This confirms both delta
addition and tombstone replay against the IBK3 immutable base.

`tools/blockengine-ibk3-persistent-smoke.sh` makes this a repeatable native
test. It publishes the checked-in life-sciences `binding_site.ttl` fixture
directly to a fresh IBK3 generation, validates and atomically activates it as
`CURRENT`, verifies a parsed base query through that collection root, applies
an `INSERT DATA`, observes its result, applies the reciprocal `DELETE DATA`,
and verifies that the result disappears. It also verifies that the durable log
has two clean committed batches. The script creates and removes only its own
`/private/tmp/factoidal-ibk3-persistent.*` test directory.

## Safe parsed LIMIT pushdown

The parsed-query host recognizes a deliberately narrow prefix-safe case: one
triple pattern, a constant predicate, distinct unbound subject/object
variables, `LIMIT`, and no live delta. Constants, repeated variables, and
non-empty deltas fall back to full selected-artifact materialisation, because
an earlier physical row may not satisfy those patterns.

On the five-artifact, 759,263-row P684 collection, ordinary parsed SPARQL
`SELECT ?s ?o { ?s wdt:P684 ?o } LIMIT 10` returned ten rows with 12,732
logical bytes and 131,072 fetched bytes. The same path still passes candidate
triples through the established evaluator; the prefix reader is a physical
admission optimisation, not a second SELECT semantics.

## Exact physical `COUNT(*)`

The IBK3 host also uses the existing Lean `detectStreamingCountStar` and
`countStarSolution` contracts for a narrower storage-adjacent case: one
default-graph triple pattern with a constant predicate, two distinct unbound
subject/object variables, and no dataset clause or live DLOG batch. It does
not trust the manifest row count alone. For every selected artifact it
Merkle-verifies the entire fixed-width row range, checks that every row has
one predicate ID, reads the one PTD1 page for that ID, and checks that it
denotes the requested predicate IRI. It then produces the standard one-row
SPARQL count solution, including the normal aggregate `OFFSET`/`LIMIT`
slice.

With an active delta log, or any shape outside that contract, the host falls
back to the composed base-plus-delta evaluator. This avoids claiming a count
that omits inserts or tombstones.

On the 759,263-row `wdt:P684` portion of the direct gene store, the parsed
count returned `759263` in 1.06 seconds (1.03 seconds user CPU), reporting
12,209,178 logical bytes and 12,320,768 fetched bytes across five artifacts.
It avoids subject/object term pages and RDF triple construction; it still
reads all row IDs because that is the evidence that every counted row has the
requested predicate. The count reader validates that fixed-width range with a
total streaming loop, retaining only the shared predicate ID rather than
allocating one `IdTriple` per row.

## Exact physical `GROUP BY ?predicate` count

The host also uses Lean's existing
`detectStreamingCountGroupByPredicate`/`predicateGroupBySolutions` path for
`SELECT ?p (COUNT(*) AS ?count) WHERE { ?s ?p ?o } GROUP BY ?p`, with the
same detector refusals for DISTINCT, HAVING, VALUES, and unsafe variable
shapes. It is limited to the default graph with no dataset clause and no live
delta. Each distinct manifest predicate is run through the verified physical
count reader; the resulting exact counts are supplied to the established Lean
grouping/result-order/modifier code.

The `binding_site.ttl` persistence smoke checks its two groups (P31 = 78,
P361 = 290). The 888,949-triple gene store returned six predicate groups from
13 artifacts without materialising RDF triples. A live DLOG falls back to the
ordinary composed evaluator, since additions and tombstones can change group
membership and counts.

## Immutable generation activation

Both IBK3 native front ends now resolve the existing optional `CURRENT`
generation pointer before opening `manifest.sbm2`. A direct collection remains
valid when no pointer exists; a malformed pointer or missing generation is an
admission failure. This gives the IBK3 path the same atomic immutable
generation-switch boundary used by compaction and publication elsewhere in
Shardborough.

## Format-preserving compaction

`l4block-shard-compact` now detects the admitted source layout. For an IBK3
source, it materialises verified paged entries, applies the existing
epoch-filtered DLOG merge, and publishes fresh `IBK3 + PTD1` artifacts. It
does not reparse Turtle and does not downgrade the collection to IBK2. The
new manifest layout is
`predicate-ibk3-ptd1-merkle-v0-compacted-default-dlog-v1`; this records the
same default-graph/DLOG restrictions as the earlier IBK2 compacted layout
while retaining its physical reader identity.

`ShardActivate` treats both compacted layouts as source-bound candidates. It
recomputes `sha256(source manifest bytes ++ clean source DLOG bytes)` before
replacing `CURRENT`, then verifies each child file's full SHA-256 commitment
and its Merkle-verified readable layout. A source write during compaction
therefore prevents activation rather than silently activating an incomplete
base.

`tools/blockengine-ibk3-compact-smoke.sh` is the regression gate. It creates
an IBK3 source, applies an insert and a delete, compacts to a fresh IBK3
generation, and checks SELECT and physical ASK. It then changes the source
again and verifies that activation of the stale compacted generation fails.
It recompacts the new source, activates that generation, checks physical COUNT
through `CURRENT`, then writes and reads a later DLOG batch at the next epoch.
The existing IBK2 compaction smoke continues to pass.

The pure storage proof is also extended in
`L4Factoidal/RDF/StoreDeltaMerge.lean` as
`mergeOnRead_after_epoch_compaction`. Given the recorded history split and
the CEP1 filter result, it proves that an epoch-filtered merge against the
compacted base has the same triple membership as applying the complete DLOG
history. This is the no-double-replay statement used by compaction. The
remaining I/O obligation is to establish those two hypotheses from committed
on-disk batches and the marker; the smoke test exercises that host boundary.
