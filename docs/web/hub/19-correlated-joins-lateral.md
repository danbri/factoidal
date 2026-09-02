---
title: "Correlated joins: LATERAL"
description: "LATERAL evaluates its right side once per row of its left side, with that row's bindings substituted in — the SPARQL 1.2-track / Jena extension that makes top-N-per-group expressible, shown live against a small hand-built dataset."
layout: hub.njk
series: docs-hub
series_order: 19
vocab: none
status: published
tests: tests/hub/post19_test.mjs
---

Every join you have written in SPARQL so far is *symmetric*: `{ A } { B }`
matches `A`, matches `B`, and keeps the pairs that agree on shared
variables. The order doesn't matter, and neither side can see the other
side's rows one at a time. `LATERAL` breaks that symmetry on purpose.
It evaluates its right-hand pattern **once for every row the left-hand
pattern produces**, with that row's bindings already substituted in —
a `foreach` over the left rows, not a set intersection. That one change
is what makes "the top-N rows *per group*" expressible in a single
query, which an ordinary join cannot do.

`LATERAL` is a SPARQL 1.2-track construct, matching
[Apache Jena's `LATERAL` extension](https://jena.apache.org/documentation/query/lateral-join.html)
verb-for-verb. In this engine it's a first-class algebra node —
[`SPARQL11.Algebra.fst`](https://github.com/danbri/factoidal/blob/claude/main/formal/fstar/SPARQL11.Algebra.fst)'s
`GP_Lateral : group_graph_pattern -> group_graph_pattern ->
group_graph_pattern` — evaluated by taking each solution `mu` of the
left pattern, applying `lateral_substitute mu` to the right pattern
(so the right side sees the left row's values as constants), evaluating
that substituted right pattern, and flat-mapping the results. The local
regression + Jena differential suite lives in
[`tests/local/lateral_joins.sh`](https://github.com/danbri/factoidal/blob/claude/main/tests/local/lateral_joins.sh);
every query below is drawn from it.

## A small dataset

Three people; two of them have two labels each, one has none:

```turtle
@prefix :    <https://example.org/> .
@prefix rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#> .

:alice rdf:type :Person ; :label "Alice A" ; :label "Alice B" .
:bob   rdf:type :Person ; :label "Bob A"   ; :label "Bob B" .
:carol rdf:type :Person .
```

Parse it and count the triples — three `rdf:type` triples plus four
`:label` triples. The dataset and its parse are named once, below, and
every cell in this post references `LAT_TTL`/`dataset` by name instead
of repeating them:

```observable-js
LAT_TTL = `
  @prefix :    <https://example.org/> .
  @prefix rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#> .

  :alice rdf:type :Person ; :label "Alice A" ; :label "Alice B" .
  :bob   rdf:type :Person ; :label "Bob A"   ; :label "Bob B" .
  :carol rdf:type :Person .
`
```

```observable-js
dataset = fn.parse(LAT_TTL)
```

```observable-js
return dataset.size;
```

Seven triples. `carol` is deliberately label-less: `LATERAL` is a
join, not a left-join, so a row whose right side produces nothing
disappears entirely — you'll see her drop out below.

## A plain correlated pattern

Start with the degenerate case where `LATERAL` behaves exactly like an
ordinary join. The right side only *matches* triples — it never
*assigns* a new binding at its top level — so substituting the left
row's `?s` in and evaluating gives the same answer a symmetric join
would:

```observable-js
const rows = await fn.query(dataset, `
  # Every person paired with every label they have. LATERAL evaluates
  # its inner pattern once per row of the outer pattern.
  PREFIX : <https://example.org/>
  PREFIX rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#>
  SELECT ?s ?label WHERE {
    ?s rdf:type :Person .
    # for each ?s bound above, look up its :label values
    LATERAL { ?s :label ?label }
  }
  ORDER BY ?s ?label
`);
return pretty(rows);
```

Four rows: both of Alice's labels, both of Bob's. Carol contributes
none — she matches `?s rdf:type :Person`, but the `LATERAL` right side
`?s :label ?label` produces zero solutions for her, so the row is
dropped. When the right side is a bare pattern like this, `LATERAL`
degenerates to `JOIN`; the interesting cases are the ones where the
right side does something a plain join can't correlate.

## Top-N per group

Here is what `LATERAL` is actually for. "One label per person, chosen
deterministically" — an `ORDER BY … LIMIT 1` that has to apply *per
subject*, not once across the whole result. The `LIMIT` lives inside a
sub-`SELECT` on the right side of the `LATERAL`, and because the left
row's `?s` is substituted in *before* that sub-query runs, the
`ORDER BY`/`LIMIT` ranks only that one person's labels:

```observable-js
const rows = await fn.query(dataset, `
  # One label per person, the alphabetically first. LATERAL evaluates
  # its inner sub-SELECT once per row of the outer pattern, so LIMIT 1
  # ranks only that one person's labels, not the whole result.
  PREFIX : <https://example.org/>
  PREFIX rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#>
  SELECT ?s ?label WHERE {
    ?s rdf:type :Person .
    LATERAL {
      # SELECT * re-projects ?s so the outer row's value correlates in
      SELECT * WHERE { ?s :label ?label } ORDER BY ?label LIMIT 1
    }
  }
  ORDER BY ?s
`);
return pretty(rows);
```

Two rows: `Alice A` (the first of Alice's two labels in sort order) and
`Bob A`. The `LIMIT 1` fired *twice*, once inside each person's
substituted sub-query — that is the per-group top-N an ordinary join
cannot express. Note the inner `SELECT *`: it must project `?s` for the
outer row's value to be substituted in. A sub-`SELECT` that projects
only `?label` would not correlate — the inner `?s` would be a fresh,
unrelated variable, and the `LIMIT 1` would then apply globally (Jena
calls this "sub-SELECT projection masking", and this engine matches it).

## LATERAL vs. an ordinary join

The difference is not subtle — it's a different row count. Take the
same "one label" idea and write it as a *plain* join with a global
`ORDER BY … LIMIT 1` instead of a correlated one. Now the `LIMIT`
applies once, to the whole joined result, so you get exactly one row
total rather than one per person:

```observable-js
const lateralRows = await fn.query(dataset, `
  # One label per person: LATERAL evaluates its inner sub-SELECT once
  # per outer row, so LIMIT 1 applies per person.
  PREFIX : <https://example.org/>
  PREFIX rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#>
  SELECT ?s ?label WHERE {
    ?s rdf:type :Person .
    LATERAL { SELECT * WHERE { ?s :label ?label } ORDER BY ?label LIMIT 1 }
  }
  ORDER BY ?s
`);

const plainJoinRows = await fn.query(dataset, `
  # The same join written as an ordinary pattern: LIMIT 1 applies once,
  # to the whole joined result, not per person.
  PREFIX : <https://example.org/>
  PREFIX rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#>
  SELECT ?s ?label WHERE {
    ?s rdf:type :Person .
    ?s :label ?label
  }
  ORDER BY ?label
  LIMIT 1
`);

return {
  lateralRowCount: lateralRows.length,
  plainJoinRowCount: plainJoinRows.length,
  lateralLabels: lateralRows.map((r) => r.get("label").value),
  plainJoinLabels: plainJoinRows.map((r) => r.get("label").value),
};
```

`lateralRowCount` is `2`, `plainJoinRowCount` is `1`. Same data, same
`ORDER BY ?label LIMIT 1`, same triple patterns — the only difference
is whether the `LIMIT` sits inside a `LATERAL`'s per-row sub-query or
outside it applying to the whole join. That gap, "the `LIMIT` I want is
per-group, not global," is the reason SPARQL needed `LATERAL` at all.

## Related

[The full-text search post](./20-fulltext-search-text-query.md) covers
`text:query` — a magic predicate that searches literals instead of
matching triples,
also Jena-compatible and also plain SPARQL query text through the same
`fn` adapter.

The live cells above are pinned in
[`tests/hub/post19_test.mjs`](https://github.com/danbri/factoidal/blob/claude/main/tests/hub/post19_test.mjs) —
the exact same source, executed against the real `npm/factoidal` typed
API instead of the in-browser `fn` adapter.
