---
title: "Full-text search: text:query"
description: "text:query is a magic predicate — it searches literals for words rather than matching a triple — using the jena-text vocabulary and conjunctive token matching (a literal matches only if it contains every token), shown live against a small labelled dataset."
layout: hub.njk
series: docs-hub
series_order: 20
vocab: none
status: published
tests: tests/hub/post20_test.mjs
---

Every other pattern in this series matches a *triple*: `?s ?p ?o` finds
edges that exist in the graph. Full-text search is a different question
— "which subjects have a literal *containing the word* panel?" — and it
does not correspond to any triple in the data. There is no
`?s :contains "panel"` edge to match. `text:query` answers it anyway,
by being a **magic predicate**: the engine intercepts the predicate
`http://jena.apache.org/text#query` at parse time and, instead of
looking for a matching triple, runs a search over the graph's literals
and binds the subject variable to whatever it finds.

This is the same `text:query` shape
[Apache Jena's jena-text](https://jena.apache.org/documentation/query/text-query.html)
exposes, down to the vocabulary IRI (`http://jena.apache.org/text#`) —
so query text written for a jena-text endpoint runs here unchanged. In
this engine it's specified in
[`SPARQL.FullText.fst`](https://github.com/danbri/factoidal/blob/claude/main/formal/fstar/SPARQL.FullText.fst).
The matching is exact-token, with a pure-F\* tokenizer (lowercase +
punctuation split) and conjunctive multi-word semantics: a literal
matches only if it contains every token. There is no relevance ranking
— `text:score` is not part of the vocabulary the engine answers, so a
result limit returns matches in dataset order, not by relevance. The
regression suite is
[`tests/local/fulltext_slice1.sh`](https://github.com/danbri/factoidal/blob/claude/main/tests/local/fulltext_slice1.sh);
every query below is drawn from it.

## A small labelled dataset

Five things, each with an `rdfs:label`, a `dc:title`, and an
`ex:status`. The word "panel" is scattered across labels and titles on
purpose, so the different query forms below select different subsets:

```turtle
@prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .
@prefix dc:   <http://purl.org/dc/elements/1.1/> .
@prefix ex:   <http://example.org/> .

ex:panel1 rdfs:label "Solar panel array"   ; dc:title "Rooftop installation" ; ex:status "active" .
ex:panel2 rdfs:label "Solar panel kit"     ; dc:title "Backyard installation" ; ex:status "active" .
ex:heater rdfs:label "Water heater"        ; dc:title "Boiler room unit"       ; ex:status "retired" .
ex:battery rdfs:label "Battery storage panel" ; dc:title "Energy storage unit" ; ex:status "retired" .
ex:controlpanel rdfs:label "Interface unit"   ; dc:title "Control panel interface" ; ex:status "active" .
```

Parse it and count — five subjects, three literals each. The dataset
and its parse are named once, below, and every cell in this post
references `FT_TTL`/`dataset` by name instead of repeating them:

```observable-js
FT_TTL = `
  @prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .
  @prefix dc:   <http://purl.org/dc/elements/1.1/> .
  @prefix ex:   <http://example.org/> .

  ex:panel1 rdfs:label "Solar panel array" ; dc:title "Rooftop installation" ; ex:status "active" .
  ex:panel2 rdfs:label "Solar panel kit" ; dc:title "Backyard installation" ; ex:status "active" .
  ex:heater rdfs:label "Water heater" ; dc:title "Boiler room unit" ; ex:status "retired" .
  ex:battery rdfs:label "Battery storage panel" ; dc:title "Energy storage unit" ; ex:status "retired" .
  ex:controlpanel rdfs:label "Interface unit" ; dc:title "Control panel interface" ; ex:status "active" .
`
```

```observable-js
dataset = fn.parse(FT_TTL)
```

```observable-js
return dataset.size;
```

Fifteen triples. Note where "panel" lives: `panel1`/`panel2` have it in
their label, `battery` has it in its label, and `controlpanel` has it
only in its `dc:title` — its label is "Interface unit". That last
distinction is what the field-restricted form below turns on.

## The 2-arity form: search every literal

The simplest form is `?s text:query "term"` — no field restriction. It
scans every literal of every subject, regardless of predicate, and
binds `?s` to each subject that has a matching one:

```observable-js
const rows = await fn.query(dataset, `
  # Subjects with any literal containing "panel", regardless of predicate.
  PREFIX text: <http://jena.apache.org/text#>
  SELECT ?s WHERE { ?s text:query "panel" }
`);
return pretty(rows);
```

Four subjects — `panel1`, `panel2`, `battery` (all three via their
labels), and `controlpanel` (via its `dc:title`, since the unrestricted
form ignores which predicate the literal hangs off).

## AND by default

Give `text:query` more than one word and it matches as a
conjunction: a literal matches only if it contains **all** the tokens.
"solar panel" therefore keeps `panel1` and `panel2` (whose labels have
both words) but drops `battery` — its label "Battery storage panel" has
"panel" but not "solar":

```observable-js
const rows = await fn.query(dataset, `
  # Subjects with a literal containing both "solar" and "panel" (AND, not phrase match).
  PREFIX text: <http://jena.apache.org/text#>
  SELECT ?s WHERE { ?s text:query "solar panel" }
`);
return pretty(rows);
```

Two subjects, `panel1` and `panel2`. Conjunctive matching is the
jena-text default; token order does not matter, but every token must be
present.

## The list form: restrict to a property

`?s text:query (rdfs:label "panel")` is the list-argument form. The
first element names a *property* to restrict the search to, so now only
literals reached by `rdfs:label` count. That drops `controlpanel` — its
`rdfs:label` is "Interface unit", and only its `dc:title` mentioned
"panel", which this form no longer looks at:

```observable-js
const rows = await fn.query(dataset, `
  # Subjects whose rdfs:label (only) contains "panel"; the property in
  # the argument list restricts which literals are searched.
  PREFIX text: <http://jena.apache.org/text#>
  PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>
  SELECT ?s WHERE { ?s text:query (rdfs:label "panel") }
`);
return pretty(rows);
```

Three subjects — `panel1`, `panel2`, `battery`. `controlpanel` is gone:
the field restriction is doing exactly its job.

## The limit form: cap the result count

A third element in the list is a result limit: `(rdfs:label "panel" 2)`
returns at most two matches. Because `text:query` makes no ranking
claim, *which* two you get is dataset order, not a relevance ranking —
so the thing to assert is the count, not the identities:

```observable-js
const rows = await fn.query(dataset, `
  # Same rdfs:label search as above, capped at 2 matches (dataset
  # order, since text:query makes no relevance-ranking claim).
  PREFIX text: <http://jena.apache.org/text#>
  PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>
  SELECT ?s WHERE { ?s text:query (rdfs:label "panel" 2) }
`);
return { matchCount: rows.length };
```

`matchCount` is `2` — the same three-candidate `(rdfs:label "panel")`
search as above, capped. The cap takes the first 2 in dataset order:
without a relevance score, "first 2" is the only meaning the count can
carry, and the module says so.

## A no-match search

A term nothing contains binds nothing — `text:query` produces zero
rows, not an error:

```observable-js
const rows = await fn.query(dataset, `
  # A term no literal contains: zero matches, not an error.
  PREFIX text: <http://jena.apache.org/text#>
  SELECT ?s WHERE { ?s text:query "zzzznonexistentterm" }
`);
return { matchCount: rows.length };
```

`matchCount` is `0`.

## Composing with an ordinary BGP

`text:query` is a magic predicate, but it is still a graph pattern —
it binds `?s` like any other, so it joins with ordinary triple patterns
in the same group. Search for "panel" *and* require `ex:status
"active"`, and the join drops `battery` (whose status is "retired")
while keeping the three active matches:

```observable-js
const rows = await fn.query(dataset, `
  # Subjects matching the full-text search AND with ex:status "active";
  # the magic predicate joins with an ordinary triple pattern on ?s.
  PREFIX text: <http://jena.apache.org/text#>
  PREFIX ex: <http://example.org/>
  SELECT ?s WHERE {
    ?s text:query "panel" .
    ?s ex:status "active" .
  }
`);
return pretty(rows);
```

Three subjects — `panel1`, `panel2`, `controlpanel`. The search half
found four "panel" subjects; the ordinary `?s ex:status "active"`
triple pattern joined on `?s` and removed the one retired match. The
magic predicate and the plain BGP compose exactly as two patterns
sharing a variable should.

## Related

The [LATERAL post](./19-correlated-joins-lateral.md) covers the
correlated join, another way to shape query results. The rest of the
series is mapped in the
[series plan](../../designissues/2026-07-05-docs-hub-plan.md).

The live cells above are pinned in
[`tests/hub/post20_test.mjs`](https://github.com/danbri/factoidal/blob/claude/main/tests/hub/post20_test.mjs) —
the exact same source, executed against the real `npm/factoidal` typed
API instead of the in-browser `fn` adapter.
