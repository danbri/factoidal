---
title: "Concept schemes: SKOS and its integrity conditions"
description: "SKOS models thesauri and taxonomies as RDF, then adds its own layer of correctness rules the RDF/OWL layer doesn't enforce — checked live with this project's SHACL and SPARQL engines."
layout: hub.njk
series: docs-hub
series_order: 4
vocab: skos
status: published
tests: tests/hub/post04_test.mjs
---

[The previous post](./03-schemas-that-infer-rdfs-owl.md) showed a
graph implying triples through RDFS and OWL 2 RL closure. SKOS (Simple
Knowledge Organization System) sits at a different layer: it's a
vocabulary *for describing vocabularies* — thesauri, taxonomies, and
subject-heading schemes — as RDF graphs. A `skos:ConceptScheme` groups
`skos:Concept`s; `skos:broader`/`skos:narrower` link them into a
hierarchy; `skos:prefLabel`/`altLabel`/`hiddenLabel` attach human-
readable names. None of that needs a new query language — it's read
and queried with the same SPARQL every other post in this series uses.

## A small concept scheme

```turtle
@prefix skos: <http://www.w3.org/2004/02/skos/core#> .
@prefix ex:   <http://example.org/skos-integrity/animals#> .
@prefix ext:  <http://example.org/skos-integrity/external#> .

ex:scheme a skos:ConceptScheme ;
    skos:prefLabel "Animals"@en ;
    skos:hasTopConcept ex:Animal .

ex:Animal a skos:Concept ;
    skos:inScheme ex:scheme ;
    skos:topConceptOf ex:scheme ;
    skos:prefLabel "Animal"@en ;
    skos:prefLabel "Animal"@en-GB .

ex:Mammal a skos:Concept ;
    skos:inScheme ex:scheme ;
    skos:prefLabel "Mammal"@en ;
    skos:broader ex:Animal .

ex:Cat a skos:Concept ;
    skos:inScheme ex:scheme ;
    skos:prefLabel "Cat"@en ;
    skos:altLabel "Feline"@en ;
    skos:hiddenLabel "Kat"@en ;
    skos:broader ex:Mammal ;
    skos:exactMatch ext:Cat .

ex:Dog a skos:Concept ;
    skos:inScheme ex:scheme ;
    skos:prefLabel "Dog"@en ;
    skos:broader ex:Mammal ;
    skos:related ex:Cat .

ex:PetsCollection a skos:Collection ;
    skos:prefLabel "Pets"@en ;
    skos:member ex:Cat ;
    skos:member ex:Dog .
```

One scheme, four concepts (`Animal`, `Mammal`, `Cat`, `Dog`), and one
`skos:Collection` — this exact fixture comes from
[`skills/skos-integrity/sample-vocab.ttl`](https://github.com/danbri/factoidal/blob/claude/main/skills/skos-integrity/sample-vocab.ttl),
built for this project's SKOS-checking skill. Every cell below reuses
this same fixture, so it's named once here:

```observable-js
SKOS_VALID_TTL = `
  @prefix skos: <http://www.w3.org/2004/02/skos/core#> .
  @prefix ex:   <http://example.org/skos-integrity/animals#> .
  @prefix ext:  <http://example.org/skos-integrity/external#> .

  ex:scheme a skos:ConceptScheme ;
      skos:prefLabel "Animals"@en ;
      skos:hasTopConcept ex:Animal .

  ex:Animal a skos:Concept ;
      skos:inScheme ex:scheme ;
      skos:topConceptOf ex:scheme ;
      skos:prefLabel "Animal"@en ;
      skos:prefLabel "Animal"@en-GB .

  ex:Mammal a skos:Concept ;
      skos:inScheme ex:scheme ;
      skos:prefLabel "Mammal"@en ;
      skos:broader ex:Animal .

  ex:Cat a skos:Concept ;
      skos:inScheme ex:scheme ;
      skos:prefLabel "Cat"@en ;
      skos:altLabel "Feline"@en ;
      skos:hiddenLabel "Kat"@en ;
      skos:broader ex:Mammal ;
      skos:exactMatch ext:Cat .

  ex:Dog a skos:Concept ;
      skos:inScheme ex:scheme ;
      skos:prefLabel "Dog"@en ;
      skos:broader ex:Mammal ;
      skos:related ex:Cat .

  ex:PetsCollection a skos:Collection ;
      skos:prefLabel "Pets"@en ;
      skos:member ex:Cat ;
      skos:member ex:Dog .
`
```

Parse it once and share the result:

```observable-js
dataset = fn.parse(SKOS_VALID_TTL)
```

Pull out each concept's English label:

```observable-js
const rows = await fn.query(dataset, `# The English preferred label (skos:prefLabel) of each skos:Concept.
  PREFIX skos: <http://www.w3.org/2004/02/skos/core#>
  SELECT ?concept ?label WHERE {
    ?concept a skos:Concept ; skos:prefLabel ?label .
    # keep only the plain "en" tagged label, not "en-GB"
    FILTER(LANG(?label) = "en")
  }
  ORDER BY ?concept
`);

return { tripleCount: dataset.size, concepts: rows.map((r) => r.get("label").value) };
```

Twenty-eight triples, four concepts. Note `ex:Animal` has *two*
`en`-tagged... no — one `en` and one `en-GB` `skos:prefLabel`, which
the filter above narrows to the single plain-`en` label. That
narrowing matters: SKOS has a rule about how many `en` labels one
concept is allowed to have, covered further down.

## Walking the hierarchy: `skos:broader+`

`skos:broader` is single-hop by design — `ex:Dog skos:broader
ex:Mammal` says nothing about `ex:Animal` directly. Getting "everything
broader than Dog, at any distance" is exactly the property-path
`+` (one-or-more) operator [post 02](./02-asking-questions-sparql.md)
introduced:

```observable-js
const ancestors = await fn.query(dataset, `# Every concept above ex:Dog in the broader hierarchy, at any distance.
  PREFIX skos: <http://www.w3.org/2004/02/skos/core#>
  PREFIX ex:   <http://example.org/skos-integrity/animals#>
  SELECT ?ancestor WHERE { ex:Dog skos:broader+ ?ancestor }
`);

return ancestors.map((r) => r.get("ancestor").value);
```

Both hops come back from one query: `Mammal` (one hop) and `Animal`
(two hops). This is the same shape of question
[post 02](./02-asking-questions-sparql.md)'s `wdt:P31/wdt:P279*`
example asked over Wikidata's subclass hierarchy — but `skos:broader`
and `wdt:P279` (subclass of) are not the same relation, deliberately.
`P279` is (modeled as) formal class subsumption: if `A wdt:P279 B`,
every instance of `A` is an instance of `B`. `skos:broader` only means
"this concept sits under that one in *this* thesaurus" — a cataloguer's
judgment call about scope, not a subsumption a reasoner can chain
through instance data. A thesaurus can legitimately have `Tomato
skos:broader Vegetable` for shelving purposes while a taxonomist
insists a tomato is botanically a fruit; SKOS is explicit that this is
fine, because `skos:broader` was never claiming `rdfs:subClassOf`'s
guarantee in the first place.

## Integrity conditions the RDF layer won't catch

SKOS has no W3C conformance test suite the way SPARQL or SHACL do —
there is no `w3c/rdf-tests`-style manifest to run and score. What it
does have is the [SKOS Reference](https://www.w3.org/TR/skos-reference/)
(W3C Recommendation, 18 August 2009) itself, which names six numbered
paragraphs as formal **integrity conditions**: constraints a
conformant SKOS graph is expected to satisfy, on top of whatever OWL
axioms `skos.rdf` asserts. The checks below come straight from that
prose and are verified with this project's own SHACL and SPARQL
machinery — no SKOS-specific engine code, and no external answer key
to score against. That's a documented gap in coverage, not a weaker
one: the [`skos-integrity` skill](https://github.com/danbri/factoidal/blob/claude/main/skills/skos-integrity/SKILL.md)
this section reuses records exactly how each condition was checked.

| S# | Statement | Checked by |
|---|---|---|
| S9 | `skos:ConceptScheme` is disjoint with `skos:Concept`. | SHACL, SPARQL |
| S13 | `skos:prefLabel`, `skos:altLabel`, `skos:hiddenLabel` are pairwise disjoint. | SHACL, SPARQL |
| S14 | At most one `skos:prefLabel` per language tag, per resource. | SHACL, SPARQL |
| S27 | `skos:related` is disjoint with `skos:broaderTransitive`. | SPARQL only (needs `+` or closure) |
| S37 | `skos:Collection` is disjoint with `skos:Concept` and `skos:ConceptScheme`. | SHACL, SPARQL |
| S46 | `skos:exactMatch` is disjoint with `skos:broadMatch`/`skos:relatedMatch`. | SHACL, SPARQL |

The broken fixture below is `sample-vocab.ttl` with exactly one
planted violation per condition — the same fixture pair the
`skos-integrity` skill runs its own checks against:

```turtle
# sample-vocab-broken.ttl — one deliberate violation per condition
ex:scheme a skos:ConceptScheme ;
    a skos:Concept ;                       # VIOLATION-S9
    skos:prefLabel "Animals"@en ;
    skos:hasTopConcept ex:Animal .

ex:Animal a skos:Concept ;
    skos:prefLabel "Animal"@en ;
    skos:prefLabel "Creature"@en ;          # VIOLATION-S14: 2nd prefLabel, same @en tag
    skos:prefLabel "Animal"@en-GB .

ex:Cat a skos:Concept ;
    skos:prefLabel "Cat"@en ;
    skos:exactMatch ext:Cat ;
    skos:broadMatch ext:Cat .               # VIOLATION-S46

ex:Dog a skos:Concept ;
    skos:prefLabel "Dog"@en ;
    skos:altLabel "Dog"@en ;                # VIOLATION-S13
    skos:broader ex:Mammal ;
    skos:broader ex:Cat ;                   # VIOLATION-S27 (paired with related, below)
    skos:related ex:Cat .

ex:PetsCollection a skos:Collection ;
    a skos:Concept ;                        # VIOLATION-S37
    skos:prefLabel "Pets"@en .
```

That broken fixture gets its own named cell too, shared by the checks
below and by the SHACL section further down:

```observable-js
SKOS_BROKEN_TTL = `
  @prefix skos: <http://www.w3.org/2004/02/skos/core#> .
  @prefix ex:   <http://example.org/skos-integrity/animals#> .
  @prefix ext:  <http://example.org/skos-integrity/external#> .

  ex:scheme a skos:ConceptScheme ;
      a skos:Concept ;
      skos:prefLabel "Animals"@en ;
      skos:hasTopConcept ex:Animal .

  ex:Animal a skos:Concept ;
      skos:inScheme ex:scheme ;
      skos:topConceptOf ex:scheme ;
      skos:prefLabel "Animal"@en ;
      skos:prefLabel "Creature"@en ;
      skos:prefLabel "Animal"@en-GB .

  ex:Mammal a skos:Concept ;
      skos:inScheme ex:scheme ;
      skos:prefLabel "Mammal"@en ;
      skos:broader ex:Animal .

  ex:Cat a skos:Concept ;
      skos:inScheme ex:scheme ;
      skos:prefLabel "Cat"@en ;
      skos:altLabel "Feline"@en ;
      skos:hiddenLabel "Kat"@en ;
      skos:broader ex:Mammal ;
      skos:exactMatch ext:Cat ;
      skos:broadMatch ext:Cat .

  ex:Dog a skos:Concept ;
      skos:inScheme ex:scheme ;
      skos:prefLabel "Dog"@en ;
      skos:altLabel "Dog"@en ;
      skos:broader ex:Mammal ;
      skos:broader ex:Cat ;
      skos:related ex:Cat .

  ex:PetsCollection a skos:Collection ;
      a skos:Concept ;
      skos:prefLabel "Pets"@en ;
      skos:member ex:Cat ;
      skos:member ex:Dog .
`
```

Run all six SPARQL checks against both the valid scheme and this
broken one:

```observable-js
const PREFIX = "PREFIX skos: <http://www.w3.org/2004/02/skos/core#>\n";
const QUERIES = {
  S9: PREFIX + `# True if any resource is asserted as both a skos:ConceptScheme and a skos:Concept.
ASK { ?x a skos:ConceptScheme , skos:Concept . }`,
  S13: PREFIX + `# Resources holding the same label value under two of the three pairwise-disjoint label properties.
SELECT DISTINCT ?resource ?value ?p1 ?p2 WHERE {
    # ?p1/?p2 range over each disjoint pair: prefLabel/altLabel, prefLabel/hiddenLabel, altLabel/hiddenLabel
    VALUES (?p1 ?p2) {
      (skos:prefLabel skos:altLabel)
      (skos:prefLabel skos:hiddenLabel)
      (skos:altLabel skos:hiddenLabel)
    }
    ?resource ?p1 ?value .
    ?resource ?p2 ?value .
  }`,
  S14: PREFIX + `# Resources with more than one skos:prefLabel sharing the same language tag.
SELECT ?resource ?lang (COUNT(DISTINCT ?label) AS ?count) WHERE {
    ?resource skos:prefLabel ?label .
    # ?lang is the language tag of ?label
    BIND(LANG(?label) AS ?lang)
  }
  # group per resource and language, then keep only groups with more than one distinct label
  GROUP BY ?resource ?lang
  HAVING (COUNT(DISTINCT ?label) > 1)`,
  S27: PREFIX + `# True if any pair related by skos:related is also linked by the transitive closure of skos:broader.
ASK { ?a skos:related ?b . { ?a skos:broader+ ?b } UNION { ?b skos:broader+ ?a } }`,
  S37: PREFIX + `# True if any skos:Collection is also asserted as a skos:Concept or a skos:ConceptScheme.
ASK {
    ?x a skos:Collection .
    ?x a ?other .
    # ?other must be one of the two classes skos:Collection is disjoint with
    FILTER(?other = skos:Concept || ?other = skos:ConceptScheme)
  }`,
  S46: PREFIX + `# Pairs linked by skos:exactMatch that also carry a mapping property disjoint from it.
SELECT DISTINCT ?a ?b WHERE {
    ?a skos:exactMatch ?b .
    # true if the pair is also skos:broadMatch, skos:relatedMatch, or the inverse skos:narrowMatch
    { ?a skos:broadMatch ?b } UNION { ?a skos:relatedMatch ?b } UNION { ?b skos:narrowMatch ?a }
  }`,
};

const validDs = await fn.parse(SKOS_VALID_TTL);
const brokenDs = await fn.parse(SKOS_BROKEN_TTL);

const summarize = (r) => (typeof r === "boolean" ? r : r.length);
const results = {};
for (const [name, q] of Object.entries(QUERIES)) {
  const validResult = summarize(await fn.query(validDs, q));
  const brokenResult = summarize(await fn.query(brokenDs, q));
  results[name] = { valid: validResult, broken: brokenResult };
}
return results;
```

Every condition reads clean (`false` or `0`) against the valid scheme
and catches exactly its planted defect against the broken one — no
false positives, no false negatives, matching what the
`skos-integrity` skill's own command transcript records.

## The same check, via SHACL

Five of the six conditions (everything except S27, which needs
transitive-path evaluation) are also expressible as SHACL shapes —
`sh:disjoint` for the pairwise-property conditions, `sh:uniqueLang`
for S14, `sh:not`/`sh:class` for the class-disjointness ones. [The next
post](./05-shapes-that-validate-shacl.md) covers SHACL itself; here,
run this project's `shaclValidate` capability against the same two
fixtures — checked and degraded gracefully if the loaded engine build
doesn't expose it:

```observable-js
const SKOS_SHAPES_TTL = `
  @prefix sh:   <http://www.w3.org/ns/shacl#> .
  @prefix skos: <http://www.w3.org/2004/02/skos/core#> .
  @prefix xsd:  <http://www.w3.org/2001/XMLSchema#> .
  @prefix si:   <http://example.org/skos-integrity/shapes#> .

  si:LabelDisjointnessShape a sh:NodeShape ;
      sh:targetSubjectsOf skos:prefLabel , skos:altLabel , skos:hiddenLabel ;
      sh:property [ sh:path skos:prefLabel ; sh:disjoint skos:altLabel ] ;
      sh:property [ sh:path skos:prefLabel ; sh:disjoint skos:hiddenLabel ] ;
      sh:property [ sh:path skos:altLabel ; sh:disjoint skos:hiddenLabel ] .

  si:UniquePrefLabelPerLanguageShape a sh:NodeShape ;
      sh:targetSubjectsOf skos:prefLabel ;
      sh:property [ sh:path skos:prefLabel ; sh:uniqueLang "true"^^xsd:boolean ] .

  si:ConceptSchemeNotConceptShape a sh:NodeShape ;
      sh:targetClass skos:ConceptScheme ;
      sh:not [ a sh:NodeShape ; sh:class skos:Concept ] .

  si:CollectionNotConceptShape a sh:NodeShape ;
      sh:targetClass skos:Collection ;
      sh:not [ a sh:NodeShape ; sh:class skos:Concept ] .

  si:ExactMatchNotBroadMatchShape a sh:NodeShape ;
      sh:targetSubjectsOf skos:exactMatch ;
      sh:property [ sh:path skos:exactMatch ; sh:disjoint skos:broadMatch ] ;
      sh:property [ sh:path skos:exactMatch ; sh:disjoint skos:relatedMatch ] .
`;

const SH_VALIDATION_RESULT = "http://www.w3.org/ns/shacl#ValidationResult";
const RDF_TYPE = "http://www.w3.org/1999/02/22-rdf-syntax-ns#type";

async function tryShaclCheck(dataTtl) {
  try {
    if (typeof fn.shaclValidate !== "function") {
      throw new Error("fn.shaclValidate is not exposed by this build");
    }
    const result = await fn.shaclValidate(dataTtl, SKOS_SHAPES_TTL);
    const violations = [...result.report].filter(
      (q) => q.predicate.value === RDF_TYPE && q.object.value === SH_VALIDATION_RESULT
    ).length;
    return { available: true, conforms: result.conforms, violations };
  } catch (err) {
    return { available: false, note: err.message };
  }
}

return { valid: await tryShaclCheck(SKOS_VALID_TTL), broken: await tryShaclCheck(SKOS_BROKEN_TTL) };
```

The valid scheme conforms; the broken one reports five violations —
one per SHACL-checkable condition (S9, S13, S14, S37, S46). S27
doesn't show up here, exactly as the condition table above predicts:
SHACL Core has no transitive-path operator, so a SHACL shape can't
express "disjoint with the *transitive* closure of broader" the way
the SPARQL `+` path did. If a build's engine bundle predates the
`shaclValidate` export, the `try`/`catch` above reports
`{available: false, note: '...'}` instead of throwing — the cell keeps
rendering either way.

## What's next

[Shapes that validate: SHACL](./05-shapes-that-validate-shacl.md) goes
deeper into the validator this post leaned on: shapes as reusable
contracts for *any* RDF data, not just SKOS's own integrity rules.

Every live cell above is pinned in
[`tests/hub/post04_test.mjs`](https://github.com/danbri/factoidal/blob/claude/main/tests/hub/post04_test.mjs) —
the exact same source, executed against the real `npm/factoidal`
typed API instead of the in-browser `fn` adapter.
