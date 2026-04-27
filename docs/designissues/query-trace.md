# Query Trace Mode

Date: 2026-04-27
Status: design note
Audience: project owner; future implementers of HTTP/SPARQL tracing; future agents

## Purpose

Define a user-facing and machine-facing **Trace Mode** for SPARQL queries.

Near-term constraint: the system is still immature, and we sometimes need
debug-build-only instrumentation to understand severe correctness bugs. So:

- the **product concept** is `Trace Mode`
- the **initial implementation vehicle** is a debug-instrumented daemon
- the **transport contract** should still be designed as if it will survive
  later migration into normal builds

This note focuses on one question first:

> Given a normal SPARQL Protocol session URL, how do we derive the URL for
> trace JSON?

Then it extends that into a phase-1 protocol and response shape.

---

## Problem

Today we have:

- normal SPARQL Protocol query execution
- `--explain-only` plan introspection
- debug-oriented stderr traces from planner / backend / COTTAS internals

But we do **not** have a stable, machine-readable way for a UI, developer, or
AI client to ask:

- how was this result set produced?
- which triple pattern ran first?
- what bindings were produced step by step?
- which row groups were pruned?
- where did suspicious output first appear?

At this phase we should assume:

- debug builds are prudent
- protocol stability matters more than implementation purity
- UI and API consumers should not depend directly on `ocamldebug` or stderr
  log formatting

---

## Goals

1. Preserve ordinary SPARQL Protocol behavior for ordinary clients.
2. Define a deterministic way to get trace JSON from a normal query URL.
3. Make the trace response contain both:
   - normal query results
   - an execution trace explaining how they were composed
4. Allow heavier debug-only instrumentation in phase 1.
5. Keep the trace schema stable even if:
   - the transport port changes
   - the endpoint path changes
   - normal builds later gain lower-overhead trace support

## Non-goals

- Standardizing this as a W3C SPARQL Protocol extension yet
- Embedding trace text into XML/CSV/TSV SPARQL result formats
- Exposing raw `ocamldebug` mechanics to the UI
- Finalizing the long-term production observability story

---

## Terminology

### Normal query URL

A URL that a regular SPARQL client would use today, for example:

```text
http://localhost:3032/query?query=SELECT%20*%20WHERE%20%7B%3Fs%20%3Fp%20%3Fo%7D
```

### Trace URL

A URL derived from the normal query URL that requests a JSON wrapper response
 containing:

- normal results
- trace metadata
- step-by-step trace events

### Debug trace daemon

A separately run daemon, likely on a different port, built with extra
instrumentation and checks suitable for severe bug-hunting.

---

## Phase 1 deployment model

Phase 1 is intentionally conservative.

- normal daemon stays unchanged
- debug trace daemon runs on a different port
- trace JSON is requested through a separate endpoint
- same query text and request parameters are preserved

Recommended deployment:

- normal daemon:
  - host: same as today
  - port: existing port, e.g. `3032`
  - path: `/query`
- debug trace daemon:
  - host: same host unless explicitly separated
  - port: dedicated debug port, e.g. `3033`
  - path: `/query-trace`

Rationale:

- avoids accidental breakage of ordinary SPARQL clients
- makes trace traffic explicitly opt-in
- keeps room for debug-only latency and payload size
- gives the UI and developers a simple and explicit mental model

---

## URL derivation rule

### Phase 1 canonical rule

Given a normal SPARQL Protocol query URL:

```text
http://HOST:NORMAL_PORT/query?PARAMS...
```

derive the trace URL as:

```text
http://HOST:TRACE_PORT/query-trace?PARAMS...&trace=LEVEL
```

Where:

- `HOST` is unchanged
- `NORMAL_PORT` is replaced with the configured trace/debug port
- `/query` is replaced with `/query-trace`
- the original query string parameters are preserved
- `trace=LEVEL` is added if absent

### Example

Normal URL:

```text
http://127.0.0.1:3032/query?query=SELECT%20*%20WHERE%20%7B%3Fs%20%3Fp%20%3Fo%7D&timeout=10
```

Trace URL:

```text
http://127.0.0.1:3033/query-trace?query=SELECT%20*%20WHERE%20%7B%3Fs%20%3Fp%20%3Fo%7D&timeout=10&trace=exec
```

### Normative manipulation algorithm

Input:

- a valid normal query URL `U`
- trace daemon port `P_trace`
- desired trace level `L`

Algorithm:

1. Parse `U` as a URL.
2. Replace the port with `P_trace`.
3. Replace the path:
   - `/query` -> `/query-trace`
4. Preserve all existing query parameters exactly as supplied.
5. Add query parameter `trace=L` unless already present.
6. Optionally add `trace_format=json` in future versions; phase 1 defaults to
   JSON and does not require it.

Output:

- the resulting trace URL

### Why a path rewrite instead of only `trace=1`?

Because phase 1 should isolate trace behavior operationally:

- different daemon
- different payload shape
- different performance profile

Later phases may allow:

```text
/query?...&trace=exec
```

on the normal daemon too. That is not phase 1.

---

## Trace levels

Phase 1 defines three levels:

- `trace=plan`
- `trace=exec`
- `trace=debug`

### `plan`

Includes:

- query text as received
- parse/algebra summary
- triple-pattern estimates
- chosen BGP order
- index/presence/dictionary consultations

Equivalent in spirit to `--explain-only`, but returned as JSON.

### `exec`

Includes everything from `plan`, plus:

- actual backend search events
- candidate row-group pruning
- emitted bindings counts
- join and optional branch counts
- projection, grouping, ordering, and slicing steps

This is the default trace level for UI use.

### `debug`

Includes everything from `exec`, plus debug-build-only extras such as:

- invariant checks
- suspicious rewrite notices
- unexpected term insertion warnings
- per-step sanity comparisons
- optional sampled intermediate bindings

This level exists to diagnose severe bugs in immature builds.

---

## Response contract

The response is **not** a raw SPARQL Results JSON document.

It is a JSON wrapper containing:

- request metadata
- result payload
- trace metadata
- trace events

Phase 1 recommended `Content-Type`:

```text
application/json
```

### Top-level shape

```json
{
  "trace_mode": "exec",
  "request": {},
  "results": {},
  "trace": {},
  "events": []
}
```

### Top-level fields

#### `trace_mode`

String. One of:

- `"plan"`
- `"exec"`
- `"debug"`

#### `request`

Metadata about the received query request.

Minimum useful fields:

```json
{
  "method": "GET",
  "query_text": "SELECT ?s WHERE { ?s ?p ?o } LIMIT 5",
  "original_path": "/query-trace",
  "dataset_kind": "binary",
  "data_cottas": [
    "tmp/ukparliament/CorpusCOTTAS/ukparliament/v1/data.cottas"
  ]
}
```

#### `results`

The normal query result payload, nested rather than returned as the entire
document.

For `SELECT`, recommended shape is SPARQL Results JSON nested as-is:

```json
{
  "type": "sparql-results+json",
  "head": { "vars": ["house", "name"] },
  "results": {
    "bindings": [
      {
        "house": { "type": "uri", "value": "..." },
        "name": { "type": "literal", "value": "..." }
      }
    ]
  }
}
```

For `ASK`:

```json
{
  "type": "sparql-results+json",
  "head": {},
  "boolean": true
}
```

For errors, see below.

#### `trace`

Summary metadata about the trace run.

Suggested fields:

```json
{
  "engine": "factoidal-debug",
  "engine_build": "debug",
  "backend": "GB_CottasOnDisk",
  "elapsed_ms": {
    "parse": 1.2,
    "open": 4300.0,
    "plan": 20.5,
    "execute": 150.0,
    "total": 4471.7
  },
  "event_count": 42
}
```

#### `events`

Ordered list of trace events. This is the main execution transcript.

---

## Event model

Each event is a JSON object with:

- `seq`: monotonically increasing integer
- `kind`: event type string
- `summary`: one-line human-friendly description
- `data`: machine-readable payload

Example:

```json
{
  "seq": 7,
  "kind": "triple_pattern_chosen",
  "summary": "Chose ?house rdf:type :House as the first pattern in BGP #1.",
  "data": {
    "bgp_id": 1,
    "pattern_label": "T1",
    "pattern": "?house rdf:type :House",
    "estimate_rows": 241800
  }
}
```

### Phase 1 core event kinds

- `request_received`
- `parse_started`
- `parse_completed`
- `algebra_built`
- `cottas_open_started`
- `cottas_open_completed`
- `bgp_entered`
- `triple_pattern_estimated`
- `triple_pattern_chosen`
- `backend_search_started`
- `candidate_row_groups_pruned`
- `row_group_scan_started`
- `row_group_scan_completed`
- `bindings_emitted`
- `join_started`
- `join_completed`
- `left_join_started`
- `left_join_completed`
- `filter_applied`
- `grouping_applied`
- `order_by_applied`
- `projection_applied`
- `slice_applied`
- `results_ready`
- `debug_invariant`
- `warning`

### Event payload discipline

Payloads should be:

- explicit
- small
- structured

Do not dump huge raw row arrays into every event.

Prefer counts and compact examples:

- row-group counts
- binding counts
- selected variable names
- estimates
- dictionary hit/miss
- sampled bindings only at `trace=debug`

---

## Human mental model

The UI should be able to render the event stream as either:

- a step list
- a tree
- both

The best abstraction is:

- **operator tree**
- whose nodes emit **execution events**

Tree nodes are things like:

- `Project`
- `Slice`
- `Join`
- `LeftJoin`
- `Union`
- `Filter`
- `BGP`

Leaf-ish work under a `BGP` node is:

- estimate each triple pattern
- choose one pattern
- search backend
- emit partial bindings
- recurse on remaining patterns using those bindings

That means the execution is **not** just a fixed plan tree. It is better
described as:

- a fixed algebra tree
- with dynamic search steps inside some nodes

Earlier bindings can make later triple-pattern searches more specific.

This is the key conceptual point the trace should communicate clearly.

---

## Real-query explanation target

A trace UI or client should be able to say things like:

1. Parsed the query into `Project -> Slice -> BGP`.
2. Found 2 triple patterns in the BGP.
3. Estimated both patterns at similar cost before execution.
4. Chose `?house rdf:type :House` first.
5. Searched COTTAS with bound predicate `rdf:type` and object `:House`.
6. Pruned candidate row groups from 26 to 2.
7. Emitted N bindings for `?house`.
8. Re-ran the remaining pattern once per emitted binding.
9. Joined each resulting `?name` onto the matching `?house`.
10. Projected the selected variables and applied `LIMIT 5`.

This is the level of description the JSON trace should make possible.

---

## Error handling

Trace JSON must still be returned for many failures, because failures are
precisely when trace is most useful.

Top-level addition:

```json
{
  "ok": false,
  "error": {
    "stage": "parse",
    "message": "SPARQL parse error: expected SELECT, ASK, CONSTRUCT, or DESCRIBE"
  }
}
```

Recommended behavior:

- parse failure:
  - include `request`
  - include `events` up to parse failure
- planning failure:
  - include algebra if available
  - include partial planner events
- execution failure:
  - include all events emitted before failure

This argues strongly for wrapper JSON rather than raw SPARQL result formats.

---

## Debug build requirements for phase 1

Trace Mode phase 1 is expected to run on a debug build and may include:

- extra assertions
- extra invariant events
- sampled intermediate bindings
- expensive sanity checks
- explicit warnings about suspicious terms or rewrites

But the **schema** returned to clients should not depend on debugger internals.

That is:

- UI should consume trace events
- not debugger transcripts
- not ad hoc stderr
- not stack-frame syntax

The debug build may internally use whatever instrumentation is needed.

---

## Security and privacy considerations

Trace Mode exposes substantially more internal detail than ordinary SPARQL
results. That is useful for debugging, but it raises real security and privacy
risks even on a local or semi-private deployment.

### Main risks

#### 1. Query text disclosure

The trace wrapper includes the query text as received. Queries may encode:

- sensitive entity IRIs
- identifiers from private datasets
- user-entered search terms
- internal graph names or endpoint conventions

If trace responses are logged, cached, or shared carelessly, the query itself
may become a data leak.

#### 2. Data-shape disclosure

Even when full result rows are not returned, trace events may reveal:

- predicate existence or absence
- approximate cardinalities
- which row groups contain a term
- whether an OPTIONAL branch matched at all
- counts of emitted bindings at intermediate stages

This can expose corpus structure that a normal result format would reveal less
directly.

#### 3. Intermediate binding disclosure

At `trace=debug`, sampled or full intermediate bindings are especially
sensitive. These may expose:

- rows that are filtered out later
- partial joins not visible in final output
- IRIs or literals not present in the final projection

This is one of the strongest arguments for keeping `debug` mode separate from
ordinary public query traffic.

#### 4. Filesystem and deployment disclosure

Phase 1 examples include local `data.cottas` paths and backend kind strings.
Those details are useful operationally but may reveal:

- local filesystem layout
- host naming conventions
- dataset storage locations
- internal deployment topology

Absolute paths should be treated as privileged debug information.

#### 5. Amplified attack surface

Trace Mode is intentionally more expensive than ordinary query execution:

- more events emitted
- larger responses
- more detailed instrumentation
- optional invariant checks

That makes it more vulnerable to denial-of-service and resource-amplification
attacks if exposed broadly.

### Phase 1 recommendations

#### Separate port and opt-in endpoint

Phase 1 should keep trace behavior on a separate debug port and explicit
endpoint, as described above. This reduces accidental exposure and makes
policy easier to enforce.

#### Default-off in shared/public deployments

Trace Mode should be disabled by default unless the operator intentionally
enables it.

#### Access control

Even in early versions, the debug trace daemon should be treated as privileged.
At minimum, deployments should prefer one or more of:

- loopback-only bind
- reverse-proxy authentication
- VPN-only exposure
- IP allowlists
- developer-only environments

#### Response minimization by level

Trace detail should scale with trace level:

- `plan`: safest default, mostly structural/planner information
- `exec`: include counts and summaries, avoid raw intermediate bindings
- `debug`: allow richer internals, but only in privileged contexts

This is not just a performance concern; it is a security control.

#### Redaction support

The implementation should leave room for redaction policy, for example:

- omit absolute filesystem paths
- hash or shorten internal dataset identifiers
- suppress raw sampled bindings unless explicitly enabled
- truncate very large literal values

The exact redaction policy can be deployment-specific, but the schema should
not assume every debug field is always safe to emit.

#### Cache control

Trace responses should be treated as sensitive debugging artifacts. HTTP
responses should default to restrictive cache headers in deployments where
that is possible.

#### Logging discipline

Operators should assume trace requests and trace responses may contain
sensitive debugging information. Avoid indiscriminate access logging of full
URLs and full JSON payloads when Trace Mode is enabled.

### Safe-by-default payload guidance

Recommended defaults:

- include final results normally
- include intermediate counts freely
- include exact internal paths only in `debug`
- include sampled intermediate bindings only in `debug`
- do not include full decoded row-group contents
- do not include arbitrary host environment details

### Future-proofing note

If Trace Mode later moves into normal builds or ordinary `/query` handling,
its security posture must remain stricter than ordinary query execution.
The stable trace schema should therefore support omission and redaction of
fields without breaking clients.

Clients should not assume that every event kind always includes every possible
debug field.

---

## Suggested HTTP examples

### Example 1: browser/UI normal -> trace

Normal:

```text
http://127.0.0.1:3032/query?query=SELECT%20%3Fs%20WHERE%20%7B%20%3Fs%20%3Fp%20%3Fo%20%7D%20LIMIT%205
```

Trace:

```text
http://127.0.0.1:3033/query-trace?query=SELECT%20%3Fs%20WHERE%20%7B%20%3Fs%20%3Fp%20%3Fo%20%7D%20LIMIT%205&trace=exec
```

### Example 2: same query, plan-only trace

```text
http://127.0.0.1:3033/query-trace?query=SELECT%20%3Fs%20WHERE%20%7B%20%3Fs%20%3Fp%20%3Fo%20%7D%20LIMIT%205&trace=plan
```

### Example 3: severe bug hunt

```text
http://127.0.0.1:3033/query-trace?query=SELECT%20%3Fhouse%20%3Fname%20WHERE%20%7B%20%3Fhouse%20a%20%3AHouse%20.%20%3Fhouse%20rdfs%3Alabel%20%3Fname%20.%20%7D%20LIMIT%205&trace=debug
```

---

## Why not embed trace into ordinary SPARQL Results JSON?

Because ordinary SPARQL clients may reject or ignore unexpected top-level keys,
and because:

- trace payloads can be large
- trace errors are diagnostically important
- trace wants richer metadata than standard result formats carry

Phase 1 should optimize for clarity and debuggability, not standards purity.

If we later want a more protocol-shaped extension, we can layer it on top of
the same event schema.

---

## Open design questions

1. Should the trace endpoint accept both GET and POST exactly like `/query`?
   Recommendation: yes.

2. Should the trace daemon expose `/query` with content negotiation as well as
   `/query-trace`?
   Recommendation: maybe later, not phase 1.

3. How much intermediate binding detail is safe to emit?
   Recommendation:
   - counts in `exec`
   - sampled bindings in `debug`

4. Should `plan` mode reuse the current explain codepath exactly, or should it
   be refactored behind a shared event emitter?
   Recommendation: shared event emitter eventually, but phase 1 may wrap the
   existing explain implementation first.

5. Should there be a request identifier linking normal and trace requests?
   Recommendation: yes, add an optional `trace_request_id`.

---

## Proposed next implementation note

Follow-up work should specify:

- exact JSON schema
- first insertion points in:
  - `factoidal_http.ml`
  - `SPARQL11_Store`
  - `RDF_CottasStore`
- how `trace=plan|exec|debug` maps to instrumentation cost
- how trace responses handle timeouts and partial execution

---

## Bottom line

Phase 1 Trace Mode should be defined as:

- a **derived URL** from a normal SPARQL query URL
- targeting a **debug trace daemon on another port**
- returning **wrapper JSON**
- with **trace levels** `plan`, `exec`, and `debug`
- using a **stable event schema**

The implementation can be debug-build-specific for now. The client contract
should not be.
