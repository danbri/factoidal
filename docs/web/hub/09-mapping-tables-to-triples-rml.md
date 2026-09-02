---
title: "Mapping tables to triples: RML"
description: "RML declares, as an RDF graph itself, how rows of CSV or JSON become triples — checked live against real fixtures from the rml-core and rml-io W3C-community test suites."
layout: hub.njk
series: docs-hub
series_order: 9
vocab: schema.org
status: published
tests: tests/hub/post09_test.mjs
---

Every dataset in this series so far started life as RDF — Turtle or
JSON-LD text this project's parsers read directly. Most of the world's
data doesn't: it's rows in a CSV export, or records in a JSON API
response, with no `@prefix` or `@context` in sight. RML (the RDF
Mapping Language) is a vocabulary for describing, once, as an RDF
graph, how to turn *that* kind of source into triples — a
`rml:TriplesMap` says which rows to iterate, how to build each row's
subject IRI, and which columns become which predicates. Write the
mapping once; run it against as many matching CSV or JSON documents as
you have.

## A mapping is itself RDF

```turtle
@prefix ex: <http://example.com/> .
@prefix foaf: <http://xmlns.com/foaf/0.1/> .
@prefix rml: <http://w3id.org/rml/> .

<http://example.com/base/TriplesMap1> a rml:TriplesMap;
  rml:logicalSource [ a rml:LogicalSource;
      rml:iterator "$.students[*]";
      rml:referenceFormulation rml:JSONPath;
      rml:source [ a rml:RelativePathSource;
          rml:root rml:MappingDirectory;
          rml:path "student.json"
        ]
    ];
  rml:predicateObjectMap [
      rml:objectMap [ rml:reference "$.ID" ];
      rml:predicate ex:id
    ], [
      rml:objectMap [ rml:reference "$.Name" ];
      rml:predicate foaf:name
    ];
  rml:subjectMap [
      rml:class foaf:Person;
      rml:template "http://example.com/{$.ID}/{$.Name}"
    ] .
```

Read as prose: for every element of the JSON array at path
`$.students[*]`, build a subject IRI from the template
`http://example.com/{$.ID}/{$.Name}`, type it `foaf:Person`, and emit
one `ex:id` triple and one `foaf:name` triple per row, reading
`$.ID`/`$.Name` out of that row with JSONPath. `rml:iterator` +
`rml:referenceFormulation` say *how* to walk the source (JSONPath
here; RML also supports CSV's flat rows, XPath for XML, and others);
`rml:template`/`rml:reference` say how to pull a value out of one
iterated row.

This exact mapping, byte for byte, is a real W3C-community rml-core
test fixture —
[`RMLTC0002a-JSON`](https://github.com/danbri/factoidal/blob/claude/main/third_party/testing/rml-modules/rml-core/test-cases/RMLTC0002a-JSON/mapping.ttl),
one of the 76 cases the score below covers.

## Running it, live

`Factoidal.rmlMap(mappingNQuads, sourceData, sourceKind)` is a raw ABI
export (see [`README.md`](./README.md)'s bindings table): the mapping
graph as N-Quads text (`fn.parse()`'s Turtle-to-N-Quads step gets
there from the Turtle above), the raw source data as text (JSON or
CSV, never RDF), and `sourceKind` telling it which. The source data
here is
[`RMLTC0002a-JSON`'s own `student.json`](https://github.com/danbri/factoidal/blob/claude/main/third_party/testing/rml-modules/rml-core/test-cases/RMLTC0002a-JSON/student.json):

```json
{
  "students": [{
    "ID": 10,
    "Name":"Venus"
  }]
}
```

```observable-js
const MAPPING_TTL = `
  @prefix ex: <http://example.com/> .
  @prefix foaf: <http://xmlns.com/foaf/0.1/> .
  @prefix rml: <http://w3id.org/rml/> .

  <http://example.com/base/TriplesMap1> a rml:TriplesMap;
    rml:logicalSource [ a rml:LogicalSource;
        rml:iterator "$.students[*]";
        rml:referenceFormulation rml:JSONPath;
        rml:source [ a rml:RelativePathSource;
            rml:root rml:MappingDirectory;
            rml:path "student.json"
          ]
      ];
    rml:predicateObjectMap [
        rml:objectMap [ rml:reference "$.ID" ];
        rml:predicate ex:id
      ], [
        rml:objectMap [ rml:reference "$.Name" ];
        rml:predicate foaf:name
      ];
    rml:subjectMap [
        rml:class foaf:Person;
        rml:template "http://example.com/{$.ID}/{$.Name}"
      ] .
`;

const STUDENT_JSON = JSON.stringify({
  students: [{ ID: 10, Name: "Venus" }],
});

const mappingNQuads = (await fn.parse(MAPPING_TTL)).toNQuads();
const result = await Factoidal.rmlMap(mappingNQuads, STUDENT_JSON, "json");

return { tripleCount: result.nquads.trim().split("\n").length, nquads: result.nquads };
```

Three triples: `foaf:name "Venus"`, `ex:id "10"^^xsd:integer` (RML
casts numeric JSON values), and `rdf:type foaf:Person` — subject
`http://example.com/10/Venus`, exactly as the template predicted.

## The same idea, over CSV

RML's own W3C-community conformance suite — rml-core, the one the
score below covers — happens to be JSON-only; its CSV coverage lives
in a sibling module, rml-io. This CSV fixture,
[`RMLSTC0007b`](https://github.com/danbri/factoidal/blob/claude/main/third_party/testing/rml-modules/rml-io/test-cases/RMLSTC0007b/mapping.ttl),
is real and vendored the same way, just scored by rml-io's own
(separate) suite rather than rml-core's 76:

```turtle
@prefix rml: <http://w3id.org/rml/> .
@prefix foaf: <http://xmlns.com/foaf/0.1/> .
@base <http://example.com/rules/> .

<#TriplesMap> a rml:TriplesMap;
  rml:logicalSource [ a rml:LogicalSource;
    rml:source [ a rml:FilePath;
      rml:root rml:MappingDirectory;
      rml:path "Friends.csv";
    ];
    rml:referenceFormulation rml:CSV;
  ];
  rml:subjectMap [ a rml:SubjectMap;
    rml:template "http://example.org/{id}";
  ];
  rml:predicateObjectMap [ a rml:PredicateObjectMap;
    rml:predicateMap [ a rml:PredicateMap; rml:constant foaf:name; ];
    rml:objectMap [ a rml:ObjectMap; rml:reference "name"; ];
  ];
  rml:predicateObjectMap [ a rml:PredicateObjectMap;
    rml:predicateMap [ a rml:PredicateMap; rml:constant foaf:age; ];
    rml:objectMap [ a rml:ObjectMap; rml:reference "age"; ];
  ];
.
```

Same shape as the JSON mapping — a logical source, a subject template,
predicate/object maps — with `rml:referenceFormulation rml:CSV` and
plain column names (`"name"`, `"age"`) instead of JSONPath
expressions, because a CSV row has no nested structure to path into.
[`Friends.csv`](https://github.com/danbri/factoidal/blob/claude/main/third_party/testing/rml-modules/rml-io/test-cases/RMLSTC0007b/Friends.csv):

```
id,name,age
0,Monica Geller,33
1,Rachel Green,34
2,Joey Tribbiani,35
3,Chandler Bing,36
4,Ross Geller,37
```

```observable-js
const MAPPING_TTL = `
  @prefix rml: <http://w3id.org/rml/> .
  @prefix foaf: <http://xmlns.com/foaf/0.1/> .
  @base <http://example.com/rules/> .

  <#TriplesMap> a rml:TriplesMap;
    rml:logicalSource [ a rml:LogicalSource;
      rml:source [ a rml:FilePath;
        rml:root rml:MappingDirectory;
        rml:path "Friends.csv";
      ];
      rml:referenceFormulation rml:CSV;
    ];
    rml:subjectMap [ a rml:SubjectMap;
      rml:template "http://example.org/{id}";
    ];
    rml:predicateObjectMap [ a rml:PredicateObjectMap;
      rml:predicateMap [ a rml:PredicateMap; rml:constant foaf:name; ];
      rml:objectMap [ a rml:ObjectMap; rml:reference "name"; ];
    ];
    rml:predicateObjectMap [ a rml:PredicateObjectMap;
      rml:predicateMap [ a rml:PredicateMap; rml:constant foaf:age; ];
      rml:objectMap [ a rml:ObjectMap; rml:reference "age"; ];
    ];
  .
`;

const FRIENDS_CSV = `id,name,age
0,Monica Geller,33
1,Rachel Green,34
2,Joey Tribbiani,35
3,Chandler Bing,36
4,Ross Geller,37
`;

const mappingNQuads = (await fn.parse(MAPPING_TTL)).toNQuads();
const result = await Factoidal.rmlMap(mappingNQuads, FRIENDS_CSV, "csv");

const dataset = await fn.parse(result.nquads, { format: "nquads" });
const rows = await fn.query(dataset, `# List every person's name and age produced by the mapping,
  # ordered by subject IRI.
  PREFIX foaf: <http://xmlns.com/foaf/0.1/>
  SELECT ?person ?name ?age WHERE { ?person foaf:name ?name ; foaf:age ?age }
  ORDER BY ?person
`);

return rows.map((r) => ({ name: r.get("name").value, age: r.get("age").value }));
```

Five rows in, five `foaf:name`/`foaf:age` pairs out, queried with the
same SPARQL every other post in this series uses — `rmlMap`'s output
is an ordinary N-Quads dataset the moment it exists, same as
[post 07](./07-json-ld-rdf-as-json.md)'s JSON-LD round trip.

## Score

Factoidal's rml-core conformance scores **76 pass, 0 fail (of 76)** —
joins (index-paired `RefObjectMap`s) and error-fixture validations
included — see [the test-results dashboard]({{ '/test-results/' | url }})
for the current run. That figure is rml-core specifically (JSON
sources, as both cells above used one of); the CSV fixture is real and
vendored the same way but belongs to the sibling rml-io module, which
this figure does not cover.

`Factoidal.rmlMap` reads every triples map in one mapping graph against
the *same* source data — joining two different logical sources isn't
reachable through this single-call entry point (the full multi-source
join driver is `bin/rml-runner/rml_runner.ml`, this project's native
test-runner). CSVW — the W3C's own CSV-with-metadata standard, a
different design from RML's row-to-triple templates — is a sibling
post still to come, and makes a natural point of comparison once it
lands.

## What's next

This batch closes out ShEx, JSON-LD, RDFC-1.0, and RML. See the
[series plan](../../designissues/2026-07-05-docs-hub-plan.md) for the
rest of the map: SPARQL Update and the HTTP protocol, RIF, the RDF/JS
and functional dataset APIs, the performance story, and the
verified-in-F\* engineering story.

Every live cell above is pinned in
[`tests/hub/post09_test.mjs`](https://github.com/danbri/factoidal/blob/claude/main/tests/hub/post09_test.mjs) —
the exact same source, executed against the real `npm/factoidal` typed
API instead of the in-browser `fn`/`Factoidal` adapters.
