# Block engine worknote: PostgreSQL opaque-byte vertical

Date: 2026-08-30

## Delivered

`tools/blockengine-postgres-smoke.sh` exercises a deliberately narrow host
boundary:

```text
Turtle -> Lean IndexedBlock -> IBK1 bytes
       -> PostgreSQL bytea
       -> exact retrieved bytes
       -> Lean IBK1 decoder -> IndexedBlock.readOps -> parsed SPARQL SELECT
```

Before persistence, it runs `l4block-id-diff` on the same query.  Consequently
the smoke establishes this transitive three-way condition:

```text
ordinary graph SPARQL results = direct IBK1 SPARQL results
PostgreSQL-retrieved IBK1 bytes = direct IBK1 bytes
therefore PostgreSQL-retrieved IBK1 runs the same Lean query path
```

For constrained runners, `SKIP_DIRECT_DIFF=1` reruns only the persistence leg
after the exact Turtle/query pair has already passed the differential command.

The database schema is only:

```sql
CREATE TABLE factoidal_block_smoke (
  block_key text PRIMARY KEY,
  payload bytea NOT NULL
);
```

The script rejects a changed retrieved byte sequence with `cmp` before the
Lean executable sees it.  Its ingestion SQL uses `pg_read_binary_file` only
because it is a self-contained local-cluster smoke.  A production adapter must
instead use a parameterized binary PostgreSQL client protocol; it must not give
the server arbitrary filesystem paths.

## Evidence

With Homebrew PostgreSQL 16.15 started locally, the smoke passed on
`examples/wikidata/subsets/lifesci-kgx/data/active_site.ttl`:

```text
triples: 486
IBK1 bytes: 27,256
PostgreSQL bytea round trip: exact pass
query: SELECT ?item WHERE { ?item wdt:P31 wd:Q423026 } ORDER BY ?item
Lean SPARQL result rows: 132
```

The query executable receives no Turtle and performs no database query.  It
opens the retrieved `IBK1` bytes directly, reconstructs the indexed block,
and routes the parsed query through the existing backend seam.  Thus the
smoke proves the intended host separation, but does **not** claim PostgreSQL
native SPARQL evaluation, snapshot semantics, concurrent transactions, or a
production pool/extension.

The PostgreSQL retrieval leg also passed on `chromosome.ttl`: 9,227 triples and
9,229 terms packed to 526,057 bytes, preserved exactly in `bytea`, then yielded
the Lean aggregate result `COUNT(*) = 9227`. The ordinary/direct differential
for that exact corpus/query passed immediately beforehand.

## Next

Extend the script into a parameterized client adapter and three-way gate:

```text
ordinary graph evaluator = direct IBK1 evaluator = PostgreSQL-retrieved IBK1 evaluator
```

Then introduce the canonical-codec theorem before treating `IBK1` as the
cross-backend durable format.  TiKV should implement the same opaque-byte
contract, rather than a distinct query kernel.
