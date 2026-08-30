# Block engine worknote: dictionary-backed indexed block

Date: 2026-08-30

## Delivered

`L4Factoidal.Storage.IndexedBlock` introduces the first executable physical
block after the direct-row MVP:

```text
Graph
  -> shared Array Term dictionary
  -> Array (subjectId, predicateId, objectId)
  -> HashMap predicateId (source-order ID rows)
  -> decoded candidate triples
  -> existing SPARQL bound matcher and evaluator
```

The loader assigns a `TermId` through a structural `Std.HashMap` and retains
the original `Term` in its dictionary. It does not collapse terms using the
engine's coarser equality, so returned bindings retain the source term. The
SPARQL `boundMatches` operation remains the semantic equality check after an
ID-row candidate is decoded.

Predicate partitions accumulate with constant-time cons during load and are
reversed at read time. A predicate-bound pattern therefore reads only that
partition while preserving source-order result sequences. Unbound-predicate
patterns read the source-order row array.

`l4block-corpus` now uses `IndexedBlock.readOps` through the landed
`BackendReadOps` / `DatasetBackend` seam. It accepts either a predicate-count
shortcut or a full SELECT query:

```bash
./.lake/build/bin/l4block-corpus DATA.ttl --query \
  'SELECT ?subject ?object WHERE { ?subject <PREDICATE> ?object } LIMIT 2'
```

## Checks

From `formal/lean4/` on 2026-08-30:

```text
lake build L4Factoidal.Storage.IndexedBlockTests -> Build completed successfully (34 jobs)
lake build l4block-corpus                         -> Build completed successfully (110 jobs)
```

The small `active_site.ttl` corpus produced the first two `wdt:P31` bindings
through a parsed SELECT / LIMIT query. The medium local
`chromosome.ttl` corpus (9,227 triples) completed a parsed `COUNT(*)` query
through the same path in about 25 seconds on the development laptop. That
wall-clock includes whole-file Turtle parsing and index construction; it is a
baseline, not a query-only benchmark.

## Boundary

This is an in-memory executable layout, not the persistence codec. It has no
canonical byte encoding, sorted range layout, block segmentation, statistics,
or cross-process snapshot definition. The next storage unit must turn this
shared dictionary / ID-row shape into a canonical byte format with a
decode/encode denotation theorem before it is written to PostgreSQL `bytea`,
TiKV, or a memory-mapped file.

The current `HashMap` loader uses structural term identity only to assign
stable local IDs. That is deliberately narrower than the RDF/SPARQL matching
relation and does not decide query answers. Any later ID-level filtering for
literals must carry an equality argument equivalent to `Term.eqb`.
