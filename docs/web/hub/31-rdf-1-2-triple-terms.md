---
title: "RDF 1.2: triple terms, reifiers & directional text"
description: "Statements about statements, provenance annotations, and right-to-left literals — RDF 1.2 / SPARQL 1.2 run live against the F*-extracted Mode_12 parsers and evaluator."
layout: hub.njk
series: docs-hub
series_order: 31
status: published
tests: tests/hub/post31_test.mjs
---

Every post before this one used RDF 1.1: a graph is a set of triples,
and a triple relates three terms. RDF 1.2 — the next revision, in W3C
Working Draft as this is written — adds one structural thing and two
smaller ones. The structural change is the **triple term**: a triple
can now appear *as a term inside another triple*, so you can say things
*about* a statement (who claimed it, when, with what confidence)
without the awkward four-triple `rdf:Statement` reification of RDF 1.1.

Everything on this page runs live against the same F\*-extracted engine
the W3C tests score **212 pass, 0 fail** on for the RDF 1.2 syntax/eval
suites (N-Triples, N-Quads, Turtle, TriG) and **248 pass, 6 fail (of
254)** for SPARQL 1.2. RDF 1.2 parsing is off by default — RDF 1.1
output stays byte-identical — so you opt in per call with
`{format: "turtle12"}` when parsing and `{version: "1.2"}` when querying.

## A dataset with triple terms

The syntax `<<( s p o )>>` is a *triple term*. Below, `:einstein
:claimed <<( :light :travelsAt :c )>>` is a single triple whose object
is itself the triple `:light :travelsAt :c`. The `~:obs {| ... |}` form
is a **reifier + annotation**: it names an occurrence of `:sunrise
:happensIn :east` as `:obs` and hangs metadata off it — the engine
expands that to `:obs rdf:reifies <<( :sunrise :happensIn :east )>>`
plus the annotation triple. The `@ar--rtl` / `@en--ltr` suffixes are
**directional language-tagged literals** — a base direction for
right-to-left scripts.

```turtle
PREFIX : <http://example.org/>
PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>
VERSION "1.2"

:einstein  :claimed <<( :light :travelsAt :c )>> .
:aristotle :claimed <<( :earth :hasShape :flat )>> .

:sunrise :happensIn :east ~:obs {| :confidence "0.99"^^xsd:decimal |} .

:relativity :title "نظرية النسبية"@ar--rtl .
:relativity :title "Theory of Relativity"@en--ltr .
```

```observable-js
ttl = `
  PREFIX : <http://example.org/>
  PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>
  VERSION "1.2"

  :einstein  :claimed <<( :light :travelsAt :c )>> .
  :aristotle :claimed <<( :earth :hasShape :flat )>> .

  :sunrise :happensIn :east ~:obs {| :confidence "0.99"^^xsd:decimal |} .

  :relativity :title "نظرية النسبية"@ar--rtl .
  :relativity :title "Theory of Relativity"@en--ltr .
`
```

`fn.parse(ttl, {format: "turtle12"})` runs the Turtle Mode_12 parser.
The opt-in is load-bearing: parse the *same* text as plain `"turtle"`
and the lenient 1.1 parser silently **skips** every `<<( )>>` and
reifier statement — you get 2 triples (the two titles) instead of 7,
with no triple terms at all. The default deliberately never changes
1.1 behaviour, so 1.2 syntax has to be asked for by name.

```observable-js
dataset = fn.parse(ttl, {format: "turtle12"})
```

## Statements as values

A triple term is a first-class term, so a variable can bind to one. The
query below asks *who claimed what*, leaving the claimed statement whole
in `?statement` — the table renders each as `<<( s p o )>>`.

```observable-js
const rows = await fn.query(dataset, `
  # Who claimed which statement; ?statement binds a whole triple term.
  PREFIX : <http://example.org/>
  SELECT ?who ?statement WHERE { ?who :claimed ?statement }
`, {version: "1.2"});
return pretty(rows); // two rows: einstein / aristotle, each with a <<( )>> statement
```

## Matching inside a triple term

The `<<( ?s ?p ?o )>>` pattern reaches *into* the triple term and binds
its three positions — so you can query the structure of the statements,
not just carry them around.

```observable-js
const rows = await fn.query(dataset, `
  # Subject, predicate, and object of each claimed statement, matched with
  # the <<( ?s ?p ?o )>> triple-term pattern.
  PREFIX : <http://example.org/>
  SELECT ?who ?s ?p ?o WHERE { ?who :claimed <<( ?s ?p ?o )>> }
`, {version: "1.2"});
return pretty(rows); // einstein: light/travelsAt/c ; aristotle: earth/hasShape/flat
```

SPARQL 1.2 also adds the `isTRIPLE()` test and the `TRIPLE()`,
`SUBJECT()`, `PREDICATE()`, `OBJECT()` accessors. Here `isTRIPLE(?t)` is
`true` for every claimed value because each is a triple term:

```observable-js
const rows = await fn.query(dataset, `
  # Whether each claimed value is a triple term, tested with isTRIPLE().
  PREFIX : <http://example.org/>
  SELECT ?who (isTRIPLE(?t) AS ?isQuoted) WHERE { ?who :claimed ?t }
`, {version: "1.2"});
return pretty(rows); // isQuoted = true for both
```

## Annotations carry provenance

The `~:obs {| :confidence 0.99 |}` block attached metadata to a specific
occurrence of `:sunrise :happensIn :east`. That metadata is ordinary
triples, so a plain pattern reads it back:

```observable-js
const rows = await fn.query(dataset, `
  # Confidence value attached via the ~:obs {| |} reifier and annotation.
  PREFIX : <http://example.org/>
  SELECT ?conf WHERE { ?obs :confidence ?conf }
`, {version: "1.2"});
return pretty(rows); // 0.99
```

## What's here, and what isn't yet

Landed and verified (no `--lax`), and — as of this post — reachable
from the browser and the npm package, not just the `w3c_runner`:

- Triple terms `<<( s p o )>>` in **N-Triples, N-Quads, Turtle, TriG**,
  the `~` reifier and `{| |}` annotation forms, the `VERSION` directive,
  and directional literals `"…"@lang--dir`.
- SPARQL 1.2 triple-term patterns and the `TRIPLE` / `isTRIPLE` /
  `SUBJECT` / `PREDICATE` / `OBJECT` / base-direction builtins.

Not yet implemented — do not read this page as "RDF 1.2 is finished":
**RDF/XML 1.2**, the RDF 1.2 **canonicalization** (86 tests) and
**entailment** (74 tests) suites, six residual SPARQL 1.2 evaluation
cases, and RML-star mapping generation. Those are tracked under
[epic #305](https://github.com/danbri/factoidal/issues/305).
