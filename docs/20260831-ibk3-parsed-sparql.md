# Parsed SPARQL over direct IBK3 storage

The IBK3 native path now has a shared importable physical reader,
`Harness/IndexedBlockV3Materialize.lean`. It performs manifest admission,
Merkle-verified positioned reads, PTD1 page planning, paged decode, and
materialisation. Two thin executables use it:

- `l4block-id-v3-merkle-scan` for a bounded predicate scan with explicit I/O
  evidence; and
- `l4block-id-v3-query` for ordinary parsed `SELECT` over the conservative
  constant-predicate fragment.

The query executable does not introduce another query evaluator. It parses
SPARQL, selects exactly the manifest artifacts for its constant predicates,
materialises those through the shared verified IBK3 reader, then invokes the
existing Lean `runSelectQueryBackendDataset` evaluator. Thus joins, filters,
projection, modifiers and result construction retain their established
semantics.

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
