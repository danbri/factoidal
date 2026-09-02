---
title: "Reactive cells: declare once, use everywhere"
description: "The hub's live cells are now reactive, ObservableHQ-style: declare a value in one cell (ttl = `…`) and reference it in later cells (graph = parse(ttl), query(graph, …), a chart of the result). The runtime orders cells by dependency and re-runs dependents when an input changes — you never hand-order them."
layout: hub.njk
series: docs-hub
series_order: 26
vocab: foaf
status: published
tests: tests/hub/post26_test.mjs
---

Every earlier post in this series wrote each live cell as an island:
the Turtle text, the `parse`, and the `query` all lived in one block,
and the next block repeated the Turtle text from scratch. That is fine
for one example. It is a chore the moment two cells want to share the
same graph.

This post shows the hub's cells doing what an
[ObservableHQ](https://observablehq.com) notebook does:
**declare a value in one cell, reference it by name in later cells.**
A cell of the form `name = <expression>` defines a reactive variable
`name`; any later cell that mentions `name` becomes a dependent. The
vendored [Observable runtime](https://github.com/observablehq/runtime)
computes the dependency order and re-runs only what needs re-running —
you never arrange the cells by hand, and editing an upstream cell
refreshes everything downstream.

## 1. Declare the data

The first cell is just a string, bound to the name `ttl`. A tiny FOAF
social graph — four people, some `foaf:knows` edges between them:

```observable-js
ttl = `
@prefix foaf: <http://xmlns.com/foaf/0.1/> .
@prefix ex:   <http://example.org/> .

ex:alice a foaf:Person ; foaf:name "Alice" ;
  foaf:knows ex:bob , ex:carol , ex:dave .
ex:bob   a foaf:Person ; foaf:name "Bob" ;
  foaf:knows ex:carol .
ex:carol a foaf:Person ; foaf:name "Carol" ;
  foaf:knows ex:alice , ex:dave .
ex:dave  a foaf:Person ; foaf:name "Dave" .
`
```

Nothing computes a graph yet — `ttl` is text. Note the shape:
`name = <value>`. That single leading `name =` is what turns a cell
into a named, referenceable variable instead of an anonymous one.

## 2. Parse it — referencing the previous cell

The next cell never repeats the Turtle. It references `ttl` by name.
`fn.parse()` returns a `Promise<Dataset>`; the runtime treats a
promise-valued cell as a value its dependents wait for, so any cell
that uses `graph` sees a settled `Dataset`, never a pending promise:

```observable-js
graph = fn.parse(ttl, { format: "turtle" })
```

Because `graph` names the parsed dataset, a cell as small as this one
can read it — count the triples without re-parsing anything:

```observable-js
tripleCount = graph.size
```

## 3. Query it — referencing the parsed graph

`results` depends on `graph`, which depends on `ttl`. The runtime
already knows that chain. This cell asks, per person, how many people
they know — a `COUNT` grouped by name:

```observable-js
results = fn.query(graph, `
  # Number of people each person knows, grouped by name.
  PREFIX foaf: <http://xmlns.com/foaf/0.1/>
  SELECT ?name (COUNT(?friend) AS ?friends) WHERE {
    ?p foaf:name ?name .
    # OPTIONAL: a person with no foaf:knows edges still gets a row, with friends = 0.
    OPTIONAL { ?p foaf:knows ?friend }
  } GROUP BY ?name ORDER BY DESC(?friends) ?name
`)
```

Rendered as a table with the `pretty()` helper — again, just by
naming `results`:

```observable-js
table = pretty(results)
```

## 4. Chart it — referencing the query result

`query()` returns `Map<string, Term>[]`. Reshape each row into a plain
`{name, friends}` record so a chart can read it:

```observable-js
chartData = results.map((r) => ({
  name: r.get("name").value,
  friends: Number(r.get("friends").value),
}))
```

And a bar chart, built from `chartData` with the vendored
`Plot` library — the fourth link in the chain, `ttl → graph →
results → chartData → chart`, each step its own cell:

```observable-js
return Plot.plot({
  marks: [
    Plot.barY(chartData, {
      x: "name",
      y: "friends",
      fill: "#2d6a4f",
      sort: { x: "-y" },
    }),
  ],
  marginLeft: 40,
  y: { label: "people known", grid: true },
  x: { label: "person" },
})
```

## Try it: change one cell, watch the rest follow

Tap **Edit** on cell 1 and add another person, or give Alice a new
friend, then **Run**. You do not touch cells 2–4. The parse re-runs
because `ttl` changed, the query re-runs because `graph` changed, the
chart redraws because `chartData` changed — the runtime propagates the
change down the dependency graph on its own. That is the whole point of
a reactive cell over a standalone script: one edit, and everything that
depended on it is consistent again.

## How the wiring works

A fenced `observable-js` block still becomes a live cell, exactly as
[the hub intro](../) describes. What changed is how a cell's
free identifiers are resolved:

- A leading `name =` makes the cell a **named runtime variable**. A
  cell without it (starting with `const`, `return`, a bare expression,
  …) stays **anonymous**, exactly as every earlier post's cells work —
  reactivity is additive, not a rewrite of the old model.
- The page infers each cell's **inputs** — the identifiers it
  references that are either a builtin (`fn`, `Factoidal`, `Plot`,
  `d3`, `html`, `md`, `pretty`) or another cell's declared name — and
  hands that list to the runtime. Globals like `Math`, `JSON`, or
  `document` are not inputs; they resolve through ordinary scope, so a
  standalone cell behaves byte-for-byte as before.
- The runtime does the rest: topological order, re-running dependents
  on change, and awaiting promise-valued cells before their dependents
  run.

The compiler that infers those inputs lives in
[`reactive-cells.mjs`](https://github.com/danbri/factoidal/blob/claude/main/docs/web/hub/reactive-cells.mjs)
and is shared, byte-for-byte, with the Node pinning harness — so the
tests exercise the same dependency inference the browser runs. Its one
convention worth remembering: following Observable, `name = { … }` is a
**block body** (write `return` inside it), so use `name = ({ … })` when
you mean an object literal.

Every cell above is pinned in
[`tests/hub/post26_test.mjs`](https://github.com/danbri/factoidal/blob/claude/main/tests/hub/post26_test.mjs),
which builds the same reactive module the page builds and reads each
named cell's value through the dependency chain — proving the
cross-cell references resolve, not merely that each cell runs alone.
