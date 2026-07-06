---
title: "Shapes that validate: SHACL"
description: "SHACL shapes as reusable data contracts — minCount, datatype, and class constraints each catching a distinct violation in a FOAF-ish profile."
layout: hub.njk
series: docs-hub
series_order: 5
vocab: foaf
status: published
tests: tests/hub/post05_test.mjs
---

[The previous post](./04-concept-schemes-skos.md) used SHACL as one
tool among several to check SKOS's own integrity conditions. This post
looks at SHACL on its own terms: a **shape** is a reusable contract —
"a `foaf:Person` must have at least one name" — checked against any
graph, independent of whatever vocabulary that graph happens to use.
Factoidal's SHACL Core validator scores 120 pass, 0 fail (of 120: 98
core constraint-component tests plus 22 `sh:sparql`-based tests,
including custom constraint components) against the W3C test suite —
see [the test-results dashboard]({{ '/test-results/' | url }}) for the
current run.

## A shape for `foaf:Person`

Back to [post 01](./01-triples-rdf-from-first-principles.md)'s Alice
and Bob. A shape requiring every `foaf:Person` to have a name, and
every `foaf:knows` edge to point at another `foaf:Person`:

```turtle
@prefix sh:   <http://www.w3.org/ns/shacl#> .
@prefix foaf: <http://xmlns.com/foaf/0.1/> .
@prefix xsd:  <http://www.w3.org/2001/XMLSchema#> .
@prefix ex:   <http://example.org/shapes/> .

ex:PersonShape
    a sh:NodeShape ;
    sh:targetClass foaf:Person ;
    sh:property [
        sh:path foaf:name ;
        sh:minCount 1 ;
        sh:message "foaf:Person needs at least one foaf:name" ;
    ] ;
    sh:property [
        sh:path foaf:name ;
        sh:datatype xsd:string ;
        sh:message "foaf:name must be a plain xsd:string" ;
    ] ;
    sh:property [
        sh:path foaf:knows ;
        sh:class foaf:Person ;
        sh:message "foaf:knows must point to another foaf:Person" ;
    ] .
```

Three property shapes, three distinct constraint kinds:
`sh:minCount` (cardinality — at least one value), `sh:datatype` (the
literal's datatype must match), `sh:class` (the value must belong to a
class). All three target the same path or a sibling one; each fails
independently of the others.

## Validating conforming data

Alice and Bob, unchanged from post 01, against the shape above:

```observable-js
const PEOPLE_TTL = `
  @prefix foaf: <http://xmlns.com/foaf/0.1/> .
  @prefix ex:   <http://example.org/> .

  ex:alice a foaf:Person ;
    foaf:name  "Alice" ;
    foaf:knows ex:bob .

  ex:bob a foaf:Person ;
    foaf:name "Bob" .
`;

const PERSON_SHAPE_TTL = `
  @prefix sh:   <http://www.w3.org/ns/shacl#> .
  @prefix foaf: <http://xmlns.com/foaf/0.1/> .
  @prefix xsd:  <http://www.w3.org/2001/XMLSchema#> .
  @prefix ex:   <http://example.org/shapes/> .

  ex:PersonShape
      a sh:NodeShape ;
      sh:targetClass foaf:Person ;
      sh:property [
          sh:path foaf:name ;
          sh:minCount 1 ;
          sh:message "foaf:Person needs at least one foaf:name" ;
      ] ;
      sh:property [
          sh:path foaf:name ;
          sh:datatype xsd:string ;
          sh:message "foaf:name must be a plain xsd:string" ;
      ] ;
      sh:property [
          sh:path foaf:knows ;
          sh:class foaf:Person ;
          sh:message "foaf:knows must point to another foaf:Person" ;
      ] .
`;

const result = await fn.shaclValidate(PEOPLE_TTL, PERSON_SHAPE_TTL);
return { conforms: result.conforms, reportSize: result.report.size };
```

`conforms: true` — both Alice and Bob have a `foaf:name`, it's a plain
string in both cases, and Bob (the only `foaf:knows` target here) is
himself a `foaf:Person`. `result.report` is still a real `Dataset`
even when there's nothing wrong — `sh:conforms true` plus a
`sh:ValidationReport` type triple, no `sh:ValidationResult` entries.

## Breaking it

Delete Bob's `foaf:name` and validate again:

```observable-js
const NO_NAME_TTL = `
  @prefix foaf: <http://xmlns.com/foaf/0.1/> .
  @prefix ex:   <http://example.org/> .

  ex:alice a foaf:Person ;
    foaf:name  "Alice" ;
    foaf:knows ex:bob .

  ex:bob a foaf:Person .
`;

const PERSON_SHAPE_TTL = `
  @prefix sh:   <http://www.w3.org/ns/shacl#> .
  @prefix foaf: <http://xmlns.com/foaf/0.1/> .
  @prefix xsd:  <http://www.w3.org/2001/XMLSchema#> .
  @prefix ex:   <http://example.org/shapes/> .

  ex:PersonShape
      a sh:NodeShape ;
      sh:targetClass foaf:Person ;
      sh:property [
          sh:path foaf:name ;
          sh:minCount 1 ;
          sh:message "foaf:Person needs at least one foaf:name" ;
      ] ;
      sh:property [
          sh:path foaf:name ;
          sh:datatype xsd:string ;
          sh:message "foaf:name must be a plain xsd:string" ;
      ] ;
      sh:property [
          sh:path foaf:knows ;
          sh:class foaf:Person ;
          sh:message "foaf:knows must point to another foaf:Person" ;
      ] .
`;

const RDF_TYPE = "http://www.w3.org/1999/02/22-rdf-syntax-ns#type";
const SH_VALIDATION_RESULT = "http://www.w3.org/ns/shacl#ValidationResult";

const result = await fn.shaclValidate(NO_NAME_TTL, PERSON_SHAPE_TTL);
const quads = [...result.report];

const rows = quads
  .filter((q) => q.predicate.value === RDF_TYPE && q.object.value === SH_VALIDATION_RESULT)
  .map((resultTypeQuad) => {
    const resultNode = resultTypeQuad.subject.value;
    const fieldOf = (predSuffix) => {
      const hit = quads.find(
        (q) => q.subject.value === resultNode && q.predicate.value.endsWith(predSuffix)
      );
      return hit ? hit.object.value : null;
    };
    return {
      focusNode: fieldOf("#focusNode"),
      path: fieldOf("#resultPath"),
      message: fieldOf("#resultMessage"),
    };
  });

return { conforms: result.conforms, violations: rows };
```

One violation row: focus node `ex:bob`, path `foaf:name`, message
"foaf:Person needs at least one foaf:name" — the report is itself an
RDF graph (`sh:ValidationReport`/`sh:ValidationResult`, SHACL §3), read
here the same way every other post's live cells read a `Dataset`:
iterate the quads, filter by predicate.

## Three constraints, three distinct violations

`sh:minCount`, `sh:datatype`, and `sh:class` each catch a different
kind of mistake. Break the graph three separate ways, one constraint
at a time, and validate each against the same shape:

```observable-js
const PERSON_SHAPE_TTL = `
  @prefix sh:   <http://www.w3.org/ns/shacl#> .
  @prefix foaf: <http://xmlns.com/foaf/0.1/> .
  @prefix xsd:  <http://www.w3.org/2001/XMLSchema#> .
  @prefix ex:   <http://example.org/shapes/> .

  ex:PersonShape
      a sh:NodeShape ;
      sh:targetClass foaf:Person ;
      sh:property [
          sh:path foaf:name ;
          sh:minCount 1 ;
          sh:message "foaf:Person needs at least one foaf:name" ;
      ] ;
      sh:property [
          sh:path foaf:name ;
          sh:datatype xsd:string ;
          sh:message "foaf:name must be a plain xsd:string" ;
      ] ;
      sh:property [
          sh:path foaf:knows ;
          sh:class foaf:Person ;
          sh:message "foaf:knows must point to another foaf:Person" ;
      ] .
`;

const MIN_COUNT_VIOLATION_TTL = `
  @prefix foaf: <http://xmlns.com/foaf/0.1/> .
  @prefix ex:   <http://example.org/> .
  ex:alice a foaf:Person ; foaf:name "Alice" ; foaf:knows ex:bob .
  ex:bob a foaf:Person .
`;

const DATATYPE_VIOLATION_TTL = `
  @prefix foaf: <http://xmlns.com/foaf/0.1/> .
  @prefix xsd:  <http://www.w3.org/2001/XMLSchema#> .
  @prefix ex:   <http://example.org/> .
  ex:alice a foaf:Person ; foaf:name "42"^^xsd:integer ; foaf:knows ex:bob .
  ex:bob a foaf:Person ; foaf:name "Bob" .
`;

const CLASS_VIOLATION_TTL = `
  @prefix foaf: <http://xmlns.com/foaf/0.1/> .
  @prefix ex:   <http://example.org/> .
  ex:alice a foaf:Person ; foaf:name "Alice" ; foaf:knows ex:mallory .
  ex:mallory foaf:name "Mallory" .
`;

const SH_COMPONENT = "http://www.w3.org/ns/shacl#sourceConstraintComponent";

async function violatedComponent(dataTtl) {
  const result = await fn.shaclValidate(dataTtl, PERSON_SHAPE_TTL);
  const quads = [...result.report];
  const componentQuad = quads.find((q) => q.predicate.value === SH_COMPONENT);
  return {
    conforms: result.conforms,
    component: componentQuad ? componentQuad.object.value.split("#")[1] : null,
  };
}

return {
  minCount: await violatedComponent(MIN_COUNT_VIOLATION_TTL),
  datatype: await violatedComponent(DATATYPE_VIOLATION_TTL),
  class: await violatedComponent(CLASS_VIOLATION_TTL),
};
```

Each broken graph is otherwise identical to the conforming one — one
triple changed, one constraint tripped:
`MinCountConstraintComponent` when Bob's `foaf:name` is missing
entirely, `DatatypeConstraintComponent` when Alice's name is an
`xsd:integer` instead of a plain string, `ClassConstraintComponent`
when Alice's `foaf:knows` points at `ex:mallory`, who is never typed
`foaf:Person`. `sh:sourceConstraintComponent` is SHACL's own way of
naming which constraint fired — the same IRI the W3C test suite's 98
core-constraint tests check against.

## What's next

The rest of this series — the other RDF syntaxes, SPARQL Update and
the HTTP protocol, ShEx, JSON-LD, RDFC-1.0 canonicalization, and the
engineering story — is still planned. See the
[series plan](../../designissues/2026-07-05-docs-hub-plan.md) for the
full map.

Every live cell above is pinned in
[`tests/hub/post05_test.mjs`](https://github.com/danbri/factoidal/blob/claude/main/tests/hub/post05_test.mjs) —
the exact same source, executed against the real `npm/factoidal`
typed API instead of the in-browser `fn` adapter.
