# Query observability for Shardborough and distributed block execution

## Purpose

Factoidal needs a runtime reporting format that makes semi-distributed query
execution intelligible to application authors, RDF modellers, database
administrators and engine developers. There is no SPARQL-standard `EXPLAIN`
format, so the appropriate convention is the familiar database split between a
planned explanation and an execution profile, supplemented by standard
distributed tracing.

The recommended public surface is:

- `EXPLAIN (FORMAT SEXP|JSON)` — query lowering, chosen dataflow, estimates,
  selected shards/graphs, placement and intended pushdown; it does not execute
  the query.
- `EXPLAIN ANALYZE (FORMAT SEXP|JSON|OTEL)` — executes a read-only query and
  adds observed rows, time, I/O, cache, retries and integrity evidence.
- OpenTelemetry export — a root query trace with spans for work that crosses
  processes, machines or storage systems.

This deliberately follows the mental model of PostgreSQL `EXPLAIN` and
`EXPLAIN ANALYZE`: estimates are shown alongside actual rows and timing, so
cardinality mistakes and expensive physical choices are visible. For read-only
SPARQL SELECT/ASK/CONSTRUCT this is operationally safe; update profiling needs
the usual explicit transaction/rollback discipline.

## One execution, three presentations

The same stable node identity should be used in the symbolic plan, JSON
profile, trace span, provenance record and assurance record. Do not create an
unrelated debugging graph.

```text
SPARQL query
  -> logical algebra
  -> physical dataflow nodes
  -> PushIR/block work
  -> runtime spans and evidence
```

The human-oriented format should use the established Factoidal S-expression
family:

```lisp
(profile q-8f2a
  (query :summary "SELECT variant chromosome"
         :snapshot "sbm1:..."
         :elapsed-ms 18.4
         :rows 20)

  (node scan-p31
    (scan :predicate wdt:P31)
    (placement local-file)
    (estimate :rows 1800)
    (actual :rows 1800 :elapsed-ms 2.1)
    (io :logical-bytes 110016 :physical-bytes 131072
        :chunks 2 :cache miss)
    (integrity :manifest SBM1 :merkle verified))

  (node join-1
    (hash-join :key ?chrom :inputs (@scan-p31 @scan-p1057))
    (estimate :rows 1800)
    (actual :rows 1794 :elapsed-ms 5.8)))
```

JSON is the tool-friendly form, suitable for APIs, saved profiles and a
browser visualiser:

```json
{
  "trace_id": "…",
  "query_id": "q-8f2a",
  "plan_node": "scan-p31",
  "operation": "ibk2.predicate_scan",
  "placement": "local-file",
  "artifact": "sha256:…",
  "estimated_rows": 1800,
  "actual_rows": 1800,
  "logical_bytes": 110016,
  "physical_bytes": 131072,
  "chunks_verified": 2,
  "cache": "miss",
  "elapsed_us": 2100
}
```

OTLP should carry the same node IDs and a low-cardinality query summary. The
root span represents the request; child spans represent planning, manifest
resolution, artifact fetch, Merkle/SHA verification, decode, block scan, join,
filter, result encoding, and remote PostgreSQL/TiKV/WASM calls. Use standard
database attributes where they fit (`db.system.name`, `db.query.summary`,
`db.response.returned_rows`, duration and error status), and add namespaced
Factoidal attributes such as `factoidal.plan.node`,
`factoidal.artifact.sha256`, and `factoidal.integrity.status`.

## Required profile fields

Every physical node should be capable of reporting, as applicable:

- stable query, plan-node, snapshot and artifact identities;
- logical operation and physical realization/placement;
- estimated and actual cardinality, cost and elapsed time;
- logical bytes requested versus physical bytes fetched;
- blocks/chunks consulted, decode work and result rows;
- cache state, queueing, retries, failures and fallback reason;
- named-graph/shard membership and provenance/snapshot identity; and
- assurance information: manifest version/root, verified proof count,
  signature/key-policy result where present, and explicit refusal reason.

`logical_bytes` must mean the requested canonical ranges. `physical_bytes`
must mean bytes actually obtained from a storage/runtime boundary, including
whole chunks fetched to satisfy a small range. Cache accounting must identify
whether a byte count was avoided, served locally, or fetched remotely. Never
present one as the other.

The profile must distinguish a normal optimization from a semantic fallback:

```text
fallback_reason = "variable predicate: full manifest required"
```

is valuable evidence, whereas simply reporting a larger byte count is not.

## Audience-oriented views

Application authors need a query ID, compact summary, total latency, result
count and safe error. RDF modellers need graph membership, provenance,
vocabulary/predicate selectivity, and whether a result is asserted or inferred.
Database administrators need trace IDs, placement/region/backend, I/O/cache
statistics, queueing/retries and integrity failures. Engine developers need the
full lowering chain, exact ranges, PushIR/kernel identity, decoded block IDs and
evidence/refinement links.

All four should be projections of the same profile rather than independently
maintained telemetry systems.

## Privacy and cardinality discipline

Full query text and RDF literal values can be sensitive and highly cardinal.
Record a redacted or parameterised query by default, with a short,
low-cardinality `query.summary` for metrics and span names. Full query text,
parameter values, result bindings and raw artifact keys should be explicit,
audited diagnostic opt-ins.

## References

- PostgreSQL, *Using EXPLAIN*: estimates, actual row counts, timing and the
  fact that `EXPLAIN ANALYZE` executes the statement.
  <https://www.postgresql.org/docs/16/using-explain.html>
- OpenTelemetry, *Semantic conventions for database client spans*: database
  span names, query summaries, returned-row counts and query-text sanitization.
  <https://opentelemetry.io/docs/specs/semconv/db/database-spans/>
- OpenTelemetry, *Trace semantic conventions*: spans are the common unit for
  correlated operations across heterogeneous systems.
  <https://opentelemetry.io/docs/specs/semconv/general/trace/>

## Status

Design guidance only as of 2026-08-30. The existing Shardborough command-line
hosts emit small text summaries. Their future structured profile should reuse
the symbolic dataflow/PushIR identities rather than add a parallel plan model.
