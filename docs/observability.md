# Observability: where the wall clock went

Every SPARQL query against `factoidal-http` produces three layers of
timing/trace data. None of it is opt-in; this is the "no black box" floor.

## 1. stderr line per query (operator's grep target)

Single line per query, fixed-position fields:

```
[timing] form=SELECT status=200 rows=-1 body=412B parse=0.4ms eval=137000.2ms format=0.0ms total=137000.6ms q="SELECT ?g (COUNT(*) AS ?n) WHERE..."
```

Filter for slow queries:

```bash
grep '\[timing\]' factoidal-http.log | awk -F 'total=' '{print $2}' | sort -gr | head
```

## 2. `Server-Timing` HTTP header (per-request, machine-readable)

Standards-compatible header on every SPARQL response:

```
Server-Timing: parse;dur=0.4, eval;dur=137000.2, format;dur=0.5, total;dur=137001.6
```

Renders natively in browser DevTools (Network panel → Timing tab) and in
`curl -i`. Cross-origin reads are enabled via `Timing-Allow-Origin: *`
(emitted alongside the existing CORS headers).

## 3. `/admin/recent.json` (last 50 queries + counters)

Read-only debug surface. JSON shape:

```json
{
  "total_queries_seen": 142,
  "total_wall_ms": 412987.4,
  "status_2xx": 138,
  "status_4xx": 3,
  "status_5xx": 1,
  "recent": [
    {
      "started_at": 1746232800.123,
      "query": "SELECT ?g (COUNT(*) AS ?n) WHERE { ... }",
      "form": "SELECT",
      "status": 200,
      "rows": -1,
      "body_bytes": 412,
      "parse_ms": 0.42,
      "eval_ms": 137000.21,
      "format_ms": 0.0,
      "total_ms": 137000.63
    },
    ...
  ]
}
```

Curl-friendly:

```bash
curl -s http://localhost:3030/admin/recent.json | jq '.recent[0:5] | .[] | {q: .query[0:60], total_ms, eval_ms}'
```

## 4. `--explain` (CLI plan dump, no execution)

Independent of the runtime timing surface; documented in
`docs/designissues/2026-04-26-pe5-explain-mode.md`. Use to inspect the
join order + per-pattern cardinality estimates without paying the cost
of running the query.

```bash
factoidal --explain '<SPARQL>' --data-cottas FILE.cottas
factoidal --explain '<SPARQL>' --data-cottas FILE.cottas --explain-out plan.json
```

## 5. Web demo "Details" pane

The `<factoidal-sparql-client>` component reads `Server-Timing` on every
response and renders a per-stage bar chart in the Details pane:

```
parse (SPARQL)         ▏ <1 ms
eval (engine)          ▕████████████████████ 137.00 s
format (serialise)     ▏ <1 ms
wire round-trip (POST) ▕█████████████████████ 137.05 s
```

Same surface for CLI users (stderr line) and demo users (Details pane).

## What the v1 surface does NOT cover yet

- **Inside-eval breakdown.** `eval_ms` is one number. The streaming-count
  fast path firing or not is not surfaced here yet — only via the
  pre-existing `[qof3]` eprintf trace lines and `--explain`. Future:
  per-stage stamps inside `eval_select_query_backend_dataset` (BGP per
  triple pattern, candidate row groups, presence-bitmap hits/misses).
- **`format_ms` is 0.0.** v1 bundles eval + format into a single
  `eval_ms`. Splitting requires bisecting `run_query` into eval and
  serialise halves.
- **Row count is -1.** v1 does not re-parse the body to count result
  rows. Adding requires either threading the count out of `run_query`
  or peeking at the JSON.
- **No persistence.** The ring buffer dies with the process. Long-term
  history goes via stderr → operator's log aggregator.

## Why this matters

The 2026-05-01 perf hunt
(`docs/designissues/2026-05-01-perf-fast-path-vs-load.md`) ended with:
"Profile breakdown (eyeballed; no actual instrumented profile, so the
exact split is approximate)." That whole class of investigation should
now resolve with one curl: `Server-Timing` on the response says where
the time went, and `/admin/recent.json` says whether the same shape
keeps coming back. Future fast-paths can be measured by their effect on
`eval_ms` directly rather than by squinting at `time` output.
