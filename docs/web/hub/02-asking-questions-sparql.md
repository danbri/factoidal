---
title: "Asking questions: SPARQL"
description: "SELECT, ASK, CONSTRUCT, and property paths over a small Wikidata-shaped dataset, run live against the F*-extracted SPARQL 1.1 evaluator."
layout: hub.njk
series: docs-hub
series_order: 2
vocab: wikidata
status: published
tests: tests/hub/post02_test.mjs
---

[The previous post](./01-triples-rdf-from-first-principles.md) parsed
a graph and read it by hand, triple by triple. That's fine for five
triples; it stops working the moment a graph has five thousand.
SPARQL is the query language that scales past "read every line" —
this post runs it live, against the same F\*-extracted evaluator the
W3C SPARQL 1.1 test suite scores 631 pass, 0 fail (of 631) against.

## A small Wikidata-shaped dataset

The examples below use real Wikidata entity and property IRIs — `wd:`
for entities, `wdt:` for "direct" (truthy) property statements — so
the query syntax matches what you'd actually run against
`query.wikidata.org`. The dataset itself is a small, hand-authored,
easily-verified excerpt (not a live fetch — no network dependency in a
docs page or its pinned test):

```turtle
@prefix wd:   <http://www.wikidata.org/entity/> .
@prefix wdt:  <http://www.wikidata.org/prop/direct/> .
@prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .

wd:Q42 rdfs:label "Douglas Adams" ;
  wdt:P31  wd:Q5 ;        # instance of: human
  wdt:P106 wd:Q36180 .    # occupation: writer

wd:Q5     rdfs:label "human" .
wd:Q36180 rdfs:label "writer" .
```

Five triples: one entity (Douglas Adams, `wd:Q42`) with a label, an
instance-of edge, an occupation edge, and labels for the two things it
points at. Every cell below parses that same Turtle text and queries
it live, using the `fn` typed API (see [`README.md`](./README.md) for
the cell-authoring contract).

Both the dataset and its parse are named once, below, and every query
cell in this post references `ttl`/`dataset` by name instead of
repeating them — the same declare-once, use-everywhere pattern
[post 26](./26-reactive-cells-declare-once-use-everywhere.md) covers
in full:

```observable-js
ttl = `
  @prefix wd:   <http://www.wikidata.org/entity/> .
  @prefix wdt:  <http://www.wikidata.org/prop/direct/> .
  @prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .

  wd:Q42 rdfs:label "Douglas Adams" ;
    wdt:P31  wd:Q5 ;
    wdt:P106 wd:Q36180 .

  wd:Q5     rdfs:label "human" .
  wd:Q36180 rdfs:label "writer" .
`
```

```observable-js
dataset = fn.parse(ttl)
```

## SELECT

```observable-js
const rows = await fn.query(dataset, `
  PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>
  SELECT ?label WHERE {
    <http://www.wikidata.org/entity/Q42> ?p ?o .
    OPTIONAL { ?o rdfs:label ?label }
  }
`);
return pretty(rows); // one row per outgoing edge from Q42: label, instance-of, occupation
```

`query()` returns an array of `Map<string, Term>` — one map per
solution row, keyed by variable name; `pretty()` (see
[`README.md`](./README.md)) renders that shape as a table, one column
per variable, with a "N rows" caption.

## ASK

A yes/no question — does this fact exist:

```observable-js
return await fn.query(dataset, `
  PREFIX wdt: <http://www.wikidata.org/prop/direct/>
  ASK { <http://www.wikidata.org/entity/Q42> wdt:P106 <http://www.wikidata.org/entity/Q36180> }
`);
```

## Property paths

`wdt:P31|wdt:P106` is a property path: "either instance-of or
occupation." Alternation (`|`), sequence (`/`), and transitive closure
(`+`, `*`) all compose the same way the property-path suite (33 pass,
0 fail of 33) tests them:

```observable-js
const types = await fn.query(dataset, `
  PREFIX wd:  <http://www.wikidata.org/entity/>
  PREFIX wdt: <http://www.wikidata.org/prop/direct/>
  SELECT ?type WHERE { wd:Q42 (wdt:P31|wdt:P106) ?type }
`);
return types.map((r) => r.get("type").value);
```

Both the instance-of target (`Q5`, human) and the occupation target
(`Q36180`, writer) come back from one path expression. On live
Wikidata, the same pattern extended to `wdt:P31/wdt:P279*` (instance
of, then subclass-of zero-or-more times) is the standard way to ask
"is this a member of some broad class" — walking the transitive
closure of `P279` in one query instead of writing a recursive client.
This dataset only has the direct `P31` edge, so the `*` part matches
zero additional hops here; the syntax is identical either way.

## A music path in practice

The compact music corpus behind the original query gallery is also available
here. This two-hop path walks from an album to its band and then to each
musician, without exposing the intermediate band variable.

```observable-js
musicTurtle = await fetch("../../../fstar-extracted/samples/music.ttl").then(async (response) => {
  if (!response.ok) throw new Error(`music.ttl: HTTP ${response.status}`);
  return response.text();
})
```

```observable-js
musicDataset = fn.parse(musicTurtle)
```

```observable-js
const performers = await fn.query(musicDataset, `
  PREFIX ex: <http://example.org/music/>
  PREFIX dc: <http://purl.org/dc/terms/>
  PREFIX mo: <http://purl.org/ontology/mo/>
  SELECT ?album ?musician WHERE {
    ?a a mo:Album ; dc:title ?album ; ex:by/ex:member ?m .
    ?m dc:title ?musician .
  }
  ORDER BY ?album ?musician
`);
return pretty(performers);
```

## CONSTRUCT

SELECT returns bindings; CONSTRUCT returns a new graph:

```observable-js
const derived = await fn.query(dataset, `
  PREFIX wdt:  <http://www.wikidata.org/prop/direct/>
  PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>
  CONSTRUCT { ?person <http://example.org/hasOccupationLabel> ?label }
  WHERE { ?person wdt:P106 ?occ . ?occ rdfs:label ?label }
`);
return { size: derived.size, nquads: derived.toNQuads() };
```

`WHERE` joins the occupation edge to the occupation's label; `CONSTRUCT`
builds one new triple per match. `derived` is an ordinary `Dataset`,
the same type `parse()` returns — it can be queried again, unioned
with another graph, or serialized.

## What's next

[RDFS and OWL 2 RL](./03-schemas-that-infer-rdfs-owl.md) show what
happens when the graph itself, not the query, is the thing doing the
implying — types nobody asserted, derived from a subclass axiom or an
`owl:equivalentClass` mapping.

Every live cell above is pinned in
[`tests/hub/post02_test.mjs`](https://github.com/danbri/factoidal/blob/claude/main/tests/hub/post02_test.mjs) —
the exact same source, executed against the real `npm/factoidal`
typed API instead of the in-browser `fn` adapter.
