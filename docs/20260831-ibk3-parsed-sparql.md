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
