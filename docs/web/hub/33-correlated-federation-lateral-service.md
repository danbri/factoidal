---
title: "Correlated federation: LATERAL meets SERVICE"
description: "SERVICE endpoints bound to local graph snapshots, then driven one row at a time by LATERAL — per-row remote lookups, per-row endpoint SELECTION with SERVICE ?endpoint, and SILENT's keep-the-row semantics, all live in the browser."
layout: hub.njk
series: docs-hub
series_order: 33
vocab: none
status: published
tests: tests/hub/post33_test.mjs
---

[The LATERAL post](./19-correlated-joins-lateral.md) showed `LATERAL`
evaluating its right-hand pattern once per left row, with that row's
bindings substituted in. This post points that machinery at
**federation**: the right-hand side is a `SERVICE` block, so every left
row becomes its own remote lookup — and, in the sharpest case, every
left row picks its own *endpoint*.

The engine's `SERVICE` evaluation resolves endpoint IRIs through a
registry — the same hook the W3C federated-query suite fills from its
`qt:serviceData` manifests, and the engine passes that suite
10 pass, 0 fail (out of 10; `service` + `syntax-fed`). Here the cells
fill the registry themselves with `fn.registerServiceEndpoint(iri,
data)`: each IRI is bound to a local graph snapshot, and `SERVICE
<iri> { … }` then evaluates against it in-process. No network I/O
happens in this page — which is exactly what makes the *semantics*
(what gets substituted, what correlates, what survives an error)
visible without a live endpoint's noise. The evaluation path is the
F\*-specified one in
[`SPARQL11.Algebra.fst`](https://github.com/danbri/factoidal/blob/claude/main/formal/fstar/SPARQL11.Algebra.fst):
`lateral_substitute` rewrites the pattern *inside* `GP_Service` /
`GP_ServiceVar` before each per-row evaluation. The native pins for
everything below are
[`tests/unit/lateral_service_unit.ml`](https://github.com/danbri/factoidal/blob/claude/main/tests/unit/lateral_service_unit.ml)
(16 pass, 0 fail).

## Local data: people, but no labels

The local dataset knows *who exists* — it deliberately holds no
labels. Every label in this post can only come from a registered
endpoint, so any labelled row is proof the remote hop happened:

```observable-js
LOCAL_TTL = `
  @prefix :    <https://example.org/> .
  @prefix rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#> .

  :alice rdf:type :Person .
  :bob   rdf:type :Person .
`
```

```observable-js
dataset = fn.parse(LOCAL_TTL)
```

## Two endpoints, deliberately in disagreement

Endpoint A and endpoint B each carry labels for *both* people — and
they disagree about them. That disagreement is the instrument: when a
query is supposed to consult only one endpoint (or a specific endpoint
*per row*), the label text tells you exactly which snapshot answered.

```observable-js
endpoints = {
  await fn.registerServiceEndpoint("https://svc-a.example/sparql", `
    @prefix : <https://example.org/> .
    :alice :label "Alice (endpoint A)" .
    :bob   :label "Bob (endpoint A)" .
  `);
  await fn.registerServiceEndpoint("https://svc-b.example/sparql", `
    @prefix : <https://example.org/> .
    :alice :label "Alice (endpoint B)" .
    :bob   :label "Bob (endpoint B)" .
  `);
  return ["https://svc-a.example/sparql", "https://svc-b.example/sparql"];
}
```

## A remote lookup per row

`LATERAL { SERVICE <A> { … } }`: for each local `?s`, the outer row's
value is substituted into the `SERVICE` body *before* dispatch, so the
remote pattern each person triggers is already about that one person.
Both rows answer from endpoint A only:

```observable-js
endpoints; // ordering: run after registration
const rows = await fn.query(dataset, `
  # Every local person, with a label looked up on endpoint A.
  PREFIX : <https://example.org/>
  PREFIX rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#>
  SELECT ?s ?label WHERE {
    ?s rdf:type :Person .
    # LATERAL evaluates the inner pattern once per row of the outer
    # pattern, substituting that row's ?s first; SERVICE sends the
    # inner pattern to the named remote endpoint.
    LATERAL { SERVICE <https://svc-a.example/sparql> { ?s :label ?label } }
  }
  ORDER BY ?s
`);
return pretty(rows);
```

Two rows, both "(endpoint A)". Nothing from B — the query never asked
it.

## Per-row endpoint SELECTION: SERVICE ?endpoint

Now the endpoint itself is a variable. `SERVICE ?e` cannot dispatch on
its own — `?e` is unbound inside the pattern. Under `LATERAL`, though,
each left row *binds* `?e` before substitution, and
`lateral_substitute` resolves `GP_ServiceVar` to a concrete
`GP_Service` for that row. Alice is routed to A, Bob to B — and the
conflicting labels prove each row consulted only its own endpoint:

```observable-js
endpoints;
const rows = await fn.query(dataset, `
  # Each person's label, looked up on the endpoint listed for that
  # person, not a fixed endpoint for every row.
  PREFIX : <https://example.org/>
  SELECT ?s ?label WHERE {
    # VALUES fixes which endpoint IRI goes with which person.
    VALUES (?s ?e) {
      (:alice <https://svc-a.example/sparql>)
      (:bob   <https://svc-b.example/sparql>)
    }
    # LATERAL evaluates the inner pattern once per row of the outer
    # pattern, substituting that row's ?s and ?e first; SERVICE then
    # sends the inner pattern to whichever endpoint ?e is bound to.
    LATERAL { SERVICE ?e { ?s :label ?label } }
  }
  ORDER BY ?s
`);
return pretty(rows);
```

`Alice (endpoint A)` and `Bob (endpoint B)` — a *different endpoint
per row of the same query*, which is the correlated-federation trick a
symmetric join cannot express at all.

## When the endpoint is missing: SILENT vs not

SPARQL's answer to a failing endpoint is two-valued. A plain `SERVICE`
to an unreachable endpoint is an error — under this engine's total
evaluator, the per-row right side yields nothing and the row drops. A
`SERVICE SILENT` yields one *empty* solution instead: the outer row
survives, unextended (its `?label` stays unbound):

```observable-js
endpoints;
const q = (silent) => `
  # Every local person, with a label looked up on an endpoint that does
  # not exist; SILENT (when set) keeps the row instead of dropping it.
  PREFIX : <https://example.org/>
  PREFIX rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#>
  SELECT ?s ?label WHERE {
    ?s rdf:type :Person .
    # LATERAL evaluates the inner pattern once per row of the outer
    # pattern; SERVICE sends it to the named remote endpoint below.
    LATERAL { SERVICE ${silent ? "SILENT " : ""}<https://nowhere.example/sparql> { ?s :label ?label } }
  }`;
const silentRows = await fn.query(dataset, q(true));
const loudRows   = await fn.query(dataset, q(false));
return {
  silentRowCount: silentRows.length,
  silentLabelsBound: silentRows.filter((r) => r.get("label") !== undefined).length,
  loudRowCount: loudRows.length,
};
```

`silentRowCount` is `2` with `silentLabelsBound` `0`; `loudRowCount`
is `0`. Same missing endpoint, opposite row fates — `SILENT` is the
difference between "annotate what you can" and "fail the join".

## Related

[Post 19](./19-correlated-joins-lateral.md) covers `LATERAL` itself
(top-N-per-group, the projection-masking rule).
[Post 22](./22-reaching-out-to-other-data.md) covers the *network*
side of federation — `query --endpoint` against live SPARQL Protocol
servers and `SERVICE <wrap+http://…>` tool-wrapping. This post is the
semantics layer both of those sit on.

The live cells above are pinned in
[`tests/hub/post33_test.mjs`](https://github.com/danbri/factoidal/blob/claude/main/tests/hub/post33_test.mjs),
running the exact same cell source against the `npm/factoidal` typed
API; the layer below that is
[`tests/unit/lateral_service_unit.ml`](https://github.com/danbri/factoidal/blob/claude/main/tests/unit/lateral_service_unit.ml),
calling the extracted F\* functions directly.
