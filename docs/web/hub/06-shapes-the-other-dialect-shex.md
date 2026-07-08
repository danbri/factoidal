---
title: "Shapes, the other dialect: ShEx"
description: "ShEx validates by writing a schema a node's shape must match, not a set of independent constraints — the same job as SHACL, approached from the opposite direction, checked live against Wikidata-shaped data."
layout: hub.njk
series: docs-hub
series_order: 6
vocab: wikidata
status: published
tests: tests/hub/post06_test.mjs
---

[The previous post](./05-shapes-that-validate-shacl.md) validated data
with SHACL: a `sh:NodeShape` bundles independent property shapes, each
one constraint (`sh:minCount`, `sh:datatype`, `sh:class`, …) that fires
or doesn't on its own. ShEx (Shape Expressions) checks the same kind
of thing — does this node's neighborhood in the graph look right? —
but starts from a different question. Instead of "what constraints
does every `foaf:Person` have to satisfy," ShEx asks "what triple
pattern does a conforming node's *set* of outgoing triples have to
match," written the way a grammar describes a sentence rather than the
way a rulebook lists prohibitions. For a lot of ordinary validation the
two land in the same place; this project implements both.

## A schema, in the syntax people read

ShExC is the human-readable concrete syntax ShEx schemas are usually
written in. A schema for "a human, per Wikidata's model" — has a
`wdt:P31` (instance of) triple pointing at `wd:Q5` (human), and an
`rdfs:label`:

```turtle
PREFIX wd:   <http://www.wikidata.org/entity/>
PREFIX wdt:  <http://www.wikidata.org/prop/direct/>
PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>

<HumanShape> {
  wdt:P31    [wd:Q5] ;
  rdfs:label LITERAL
}
```

Read as prose: a node matching `<HumanShape>` must have exactly one
`wdt:P31` triple whose object is the single value `wd:Q5`, and exactly
one `rdfs:label` triple whose object is any literal. That's the whole
shape — no separate "target" declaration the way SHACL's
`sh:targetClass` needs one; a ShEx shape is checked against whichever
node you name at validation time.

This project's validator parses ShExC directly now —
[`Parser.ShExC.fst`](https://github.com/danbri/factoidal/blob/claude/main/formal/fstar/Parser.ShExC.fst)
is a from-scratch F\* parser for the compact syntax above, checked
against the vendored shexSpec/shexTest corpus's own ShExC↔ShExJ twin
pairs: 433 of 433 `schemas/` fixtures parse to the exact same AST as
the reference ShExJ decoding (`bin/shex-runner --differential`; see
[the score section](#score) below). `shexValidate`'s schema argument
now accepts either form — the dispatch rule is simple: the first
non-whitespace character of the schema text decides the format, `{`
means ShExJ, anything else is parsed as ShExC (no valid ShExC document
starts with `{`). ShExJ is ShEx's JSON Schema form — the same schema
above, hand-translated once, is what the first pair of live cells
below sends to `Factoidal.shexValidate`; a later section on this page
sends the ShExC text you just read straight through instead.

```js
{
  type: "Schema",
  shapes: [{
    type: "ShapeDecl",
    id: "http://example.org/HumanShape",
    shapeExpr: {
      type: "Shape",
      expression: {
        type: "EachOf",
        expressions: [
          {
            type: "TripleConstraint",
            predicate: "http://www.wikidata.org/prop/direct/P31",
            valueExpr: { type: "NodeConstraint", values: ["http://www.wikidata.org/entity/Q5"] },
          },
          {
            type: "TripleConstraint",
            predicate: "http://www.w3.org/2000/01/rdf-schema#label",
            valueExpr: { type: "NodeConstraint", nodeKind: "literal" },
          },
        ],
      },
    },
  }],
}
```

`shexValidate` is a raw `Factoidal` export, not one of the `fn` typed
adapter's methods (see [`README.md`](./README.md) for the full
bindings table) — its signature is `shexValidate(dataNQuads,
schemaText, focus, shapeLabel)`: dataset-handle N-Quads text, the
schema as ShExJ (JSON string) or ShExC (compact-syntax string) text,
the focus node's IRI, and the shape's `id`. `fn.parse()` gets from
Turtle to N-Quads text via `dataset.toNQuads()`.

## A small Wikidata-shaped dataset

```turtle
@prefix wd:   <http://www.wikidata.org/entity/> .
@prefix wdt:  <http://www.wikidata.org/prop/direct/> .
@prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .

wd:Q42 wdt:P31   wd:Q5 ;
       rdfs:label "Douglas Adams"@en .

wd:Q5  rdfs:label "human"@en .
```

`wd:Q42` (Douglas Adams) is instance-of `wd:Q5` (human) and has a
label — the same real, well-attested Wikidata IRIs
[post 02](./02-asking-questions-sparql.md) used. `wd:Q5` itself has a
label but, being the class rather than an instance of it, no `wdt:P31`
triple of its own — a deliberate non-conforming case, not a mistake.
Parse it and check the triple count:

```observable-js
const WD_TTL = `
  @prefix wd:   <http://www.wikidata.org/entity/> .
  @prefix wdt:  <http://www.wikidata.org/prop/direct/> .
  @prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .

  wd:Q42 wdt:P31   wd:Q5 ;
         rdfs:label "Douglas Adams"@en .

  wd:Q5  rdfs:label "human"@en .
`;

const dataset = await fn.parse(WD_TTL);
return dataset.size;
```

Three triples: `Q42`'s `P31` and `label`, `Q5`'s `label`.

## Validating a conforming node

`shexValidate` needs a capability check the way
[`fn.shaclValidate`](./04-concept-schemes-skos.md) does — it's built on
the same npm-entry ABI bundle, so a stale build might not expose it.
Wrap the call and degrade to an explanatory value rather than a hard
`.observable-cell-error`:

```observable-js
const WD_TTL = `
  @prefix wd:   <http://www.wikidata.org/entity/> .
  @prefix wdt:  <http://www.wikidata.org/prop/direct/> .
  @prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .

  wd:Q42 wdt:P31   wd:Q5 ;
         rdfs:label "Douglas Adams"@en .

  wd:Q5  rdfs:label "human"@en .
`;

const HUMAN_SHAPE_SCHEMA = JSON.stringify({
  type: "Schema",
  shapes: [{
    type: "ShapeDecl",
    id: "http://example.org/HumanShape",
    shapeExpr: {
      type: "Shape",
      expression: {
        type: "EachOf",
        expressions: [
          {
            type: "TripleConstraint",
            predicate: "http://www.wikidata.org/prop/direct/P31",
            valueExpr: { type: "NodeConstraint", values: ["http://www.wikidata.org/entity/Q5"] },
          },
          {
            type: "TripleConstraint",
            predicate: "http://www.w3.org/2000/01/rdf-schema#label",
            valueExpr: { type: "NodeConstraint", nodeKind: "literal" },
          },
        ],
      },
    },
  }],
});

async function tryShexValidate(dataNQuads, focus) {
  try {
    if (typeof Factoidal.shexValidate !== "function") {
      throw new Error("Factoidal.shexValidate is not exposed by this build");
    }
    const result = await Factoidal.shexValidate(
      dataNQuads, HUMAN_SHAPE_SCHEMA, focus, "http://example.org/HumanShape");
    return { available: true, verdict: result.verdict, deferred: result.deferred };
  } catch (err) {
    return { available: false, note: err.message };
  }
}

const dataset = await fn.parse(WD_TTL);
return tryShexValidate(dataset.toNQuads(), "http://www.wikidata.org/entity/Q42");
```

`verdict: true` — `wd:Q42` has both triples the shape requires.
`deferred: false` means the engine reached a definite answer inside
its decidable ShEx fragment, not a guess.

## Validating a non-conforming node

Same schema, same dataset, different focus node — `wd:Q5` has a label
but no `wdt:P31` triple of its own:

```observable-js
const WD_TTL = `
  @prefix wd:   <http://www.wikidata.org/entity/> .
  @prefix wdt:  <http://www.wikidata.org/prop/direct/> .
  @prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .

  wd:Q42 wdt:P31   wd:Q5 ;
         rdfs:label "Douglas Adams"@en .

  wd:Q5  rdfs:label "human"@en .
`;

const HUMAN_SHAPE_SCHEMA = JSON.stringify({
  type: "Schema",
  shapes: [{
    type: "ShapeDecl",
    id: "http://example.org/HumanShape",
    shapeExpr: {
      type: "Shape",
      expression: {
        type: "EachOf",
        expressions: [
          {
            type: "TripleConstraint",
            predicate: "http://www.wikidata.org/prop/direct/P31",
            valueExpr: { type: "NodeConstraint", values: ["http://www.wikidata.org/entity/Q5"] },
          },
          {
            type: "TripleConstraint",
            predicate: "http://www.w3.org/2000/01/rdf-schema#label",
            valueExpr: { type: "NodeConstraint", nodeKind: "literal" },
          },
        ],
      },
    },
  }],
});

async function tryShexValidate(dataNQuads, focus) {
  try {
    if (typeof Factoidal.shexValidate !== "function") {
      throw new Error("Factoidal.shexValidate is not exposed by this build");
    }
    const result = await Factoidal.shexValidate(
      dataNQuads, HUMAN_SHAPE_SCHEMA, focus, "http://example.org/HumanShape");
    return { available: true, verdict: result.verdict, deferred: result.deferred };
  } catch (err) {
    return { available: false, note: err.message };
  }
}

const dataset = await fn.parse(WD_TTL);
return tryShexValidate(dataset.toNQuads(), "http://www.wikidata.org/entity/Q5");
```

`verdict: false` — the `wdt:P31` triple constraint has nothing to
match. A `verdict: null` with `deferred: true` is the third possible
answer this engine can give (not exercised by either cell above): a
schema construct outside the currently-decidable ShEx fragment reports
"can't say" rather than guessing true or false.

## The same schema, sent as ShExC text

Every cell above sent the hand-translated ShExJ form. `shexValidate`
also accepts the ShExC text from
["A schema, in the syntax people read"](#a-schema-in-the-syntax-people-read)
directly (via `Parser.ShExC.fst`) — no translation step, no separate entry point, just the
same `shexValidate(dataNQuads, schemaText, focus, shapeLabel)` call
with a ShExC string instead of a JSON one:

```observable-js
const WD_TTL = `
  @prefix wd:   <http://www.wikidata.org/entity/> .
  @prefix wdt:  <http://www.wikidata.org/prop/direct/> .
  @prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .

  wd:Q42 wdt:P31   wd:Q5 ;
         rdfs:label "Douglas Adams"@en .

  wd:Q5  rdfs:label "human"@en .
`;

const HUMAN_SHAPE_SHEXC = `
  PREFIX wd:   <http://www.wikidata.org/entity/>
  PREFIX wdt:  <http://www.wikidata.org/prop/direct/>
  PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>

  <http://example.org/HumanShape> {
    wdt:P31    [wd:Q5] ;
    rdfs:label LITERAL
  }
`;

async function tryShexValidate(dataNQuads, focus) {
  try {
    if (typeof Factoidal.shexValidate !== "function") {
      throw new Error("Factoidal.shexValidate is not exposed by this build");
    }
    const result = await Factoidal.shexValidate(
      dataNQuads, HUMAN_SHAPE_SHEXC, focus, "http://example.org/HumanShape");
    return { available: true, verdict: result.verdict, deferred: result.deferred };
  } catch (err) {
    return { available: false, note: err.message };
  }
}

const dataset = await fn.parse(WD_TTL);
return tryShexValidate(dataset.toNQuads(), "http://www.wikidata.org/entity/Q42");
```

`verdict: true` — same conforming node, same shape, no JSON in sight.
And the non-conforming node still comes back `false` through the exact
same ShExC schema text:

```observable-js
const WD_TTL = `
  @prefix wd:   <http://www.wikidata.org/entity/> .
  @prefix wdt:  <http://www.wikidata.org/prop/direct/> .
  @prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .

  wd:Q42 wdt:P31   wd:Q5 ;
         rdfs:label "Douglas Adams"@en .

  wd:Q5  rdfs:label "human"@en .
`;

const HUMAN_SHAPE_SHEXC = `
  PREFIX wd:   <http://www.wikidata.org/entity/>
  PREFIX wdt:  <http://www.wikidata.org/prop/direct/>
  PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>

  <http://example.org/HumanShape> {
    wdt:P31    [wd:Q5] ;
    rdfs:label LITERAL
  }
`;

async function tryShexValidate(dataNQuads, focus) {
  try {
    if (typeof Factoidal.shexValidate !== "function") {
      throw new Error("Factoidal.shexValidate is not exposed by this build");
    }
    const result = await Factoidal.shexValidate(
      dataNQuads, HUMAN_SHAPE_SHEXC, focus, "http://example.org/HumanShape");
    return { available: true, verdict: result.verdict, deferred: result.deferred };
  } catch (err) {
    return { available: false, note: err.message };
  }
}

const dataset = await fn.parse(WD_TTL);
return tryShexValidate(dataset.toNQuads(), "http://www.wikidata.org/entity/Q5");
```

`verdict: false` — `wd:Q5` still has no `wdt:P31` triple of its own,
whether the schema arrived as ShExC or ShExJ. The dispatch is a pure
sniff of the schema text: first non-whitespace character `{` is
parsed as ShExJ, anything else (a `PREFIX`/`BASE` directive, a shape
label, `START`, …) is parsed as ShExC.

## Wikidata's EntitySchemas

ShEx isn't a niche dialect invented for this post's convenience — it's
the shape language behind Wikidata's own
[EntitySchema namespace](https://www.wikidata.org/wiki/Wikidata:EntitySchemas):
pages like `E10` (human) or `E4` (educational institution) let editors
say, in ShExC, exactly what a well-formed instance of that class looks
like — which properties, which cardinalities, which value types.
Wikibase runs an editor-facing "does this item match schema E10"
check the same shape this post's cells ran, just against the full
Wikidata graph instead of a two-triple excerpt. The `HumanShape` schema
above is a toy, but the property it checks (`wdt:P31 [wd:Q5]`) is the
one real `E10` schemas open with.

## Score

Factoidal's ShEx validator scores **1181 pass, 1 mismatch, 0 deferred,
0 skipped (of 1182)** against the shexSpec/shexTest validation
manifest — see [the test-results dashboard]({{ '/test-results/' | url }})
for the current run. The one mismatch is an upstream fixture defect,
not an engine bug: `start2RefS2.json` has `p1` where the corresponding
canonical `.shex` file has `p2` — a typo in the test data itself, not
something this validator gets wrong. Validation uses
descendant-witness semantics (per
[arXiv:2503.24299](https://arxiv.org/abs/2503.24299)), differentially
confirmed against the reference `@shexjs/validator` implementation.

The ShExC parser itself is scored separately, against the same
corpus's `schemas/` directory: **433 of 433 ShExC↔ShExJ pairs
structurally equal** (`bin/shex-runner --differential`) — every
vendored `.shex` fixture parses to the exact same AST as the
reference ShExJ decoding of its `.json` twin (the `start2RefS2` typo
above counts as a correct disagreement here too: this parser's ShExC
reading is `p2`, matching the canonical `.shex`, not the buggy
`.json`).

## What's next

[JSON-LD: RDF as JSON](./07-json-ld-rdf-as-json.md) moves from shapes
to syntax — the JSON developer's on-ramp into RDF. The rest of the
series (RDFC-1.0 canonicalization, RML, and the engineering story) is
listed in the [series plan](../../designissues/2026-07-05-docs-hub-plan.md).

Every live cell above is pinned in
[`tests/hub/post06_test.mjs`](https://github.com/danbri/factoidal/blob/claude/main/tests/hub/post06_test.mjs) —
the exact same source, executed against the real `npm/factoidal` typed
API instead of the in-browser `fn`/`Factoidal` adapters.
