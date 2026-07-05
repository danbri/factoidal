---
name: skos-integrity
description: Check a SKOS vocabulary against the SKOS Reference (W3C Rec. 18 Aug 2009) integrity conditions using this project's own engines — the SHACL validator (98 pass, 0 fail on the W3C core suite), SPARQL 1.1 with property paths (631 pass, 0 fail), and the generic OWL 2 RL closure. Use when asked to validate a SKOS taxonomy or thesaurus, when auditing skos:prefLabel/altLabel/hiddenLabel usage, skos:broader/narrower/related consistency, or mapping-property (exactMatch/broadMatch/narrowMatch/relatedMatch) clashes, or when the user references SKOS "integrity conditions" / S-numbers from the Reference. A prose skill rather than an F* module by design — the checks mix shapes, SPARQL, and axiom data rather than new engine logic.
---

# SKOS integrity checking with Factoidal's own engines

The [SKOS Reference](https://www.w3.org/TR/skos-reference/) (W3C
Recommendation, 18 August 2009) designates six numbered paragraphs as
formal **Integrity Conditions** — normative constraints a conformant
SKOS graph is expected to satisfy, kept separate from the vocabulary's
own OWL axioms. This skill checks all six with artifacts that already
exist in this repository: no new F\* module, no SKOS-specific engine
code. Everything here is prose, SHACL shapes, SPARQL queries, and RDF
data — which is why it ships as a skill instead of a `.fst` file.

## Why these six conditions aren't OWL axioms

The Reference's own machine-readable vocabulary
([`skos.rdf`](https://www.w3.org/TR/skos-reference/skos.rdf)) asserts
`owl:disjointWith` between the three core **classes**
(`skos:ConceptScheme`, `skos:Concept`, `skos:Collection` — this is
S9 and S37) but does **not** assert `owl:disjointWith` between any of
the **properties** the other four conditions talk about
(`skos:prefLabel`/`altLabel`/`hiddenLabel`, `skos:related`/
`broaderTransitive`, `skos:exactMatch`/`broadMatch`/`relatedMatch`).
That is deliberate, not an oversight: `skos:broadMatch` is a
sub-property of both `skos:mappingRelation` and `skos:broader`, so an
OWL axiom declaring `skos:exactMatch owl:disjointWith
skos:broadMatch` would make a large fraction of real-world SKOS
graphs OWL-*inconsistent* rather than merely non-conformant. The
Reference calls S13/S14/S27/S46 "integrity conditions" rather than
axioms for exactly this reason, and says implementations should check
them separately. That separation is why SHACL and SPARQL — not the
OWL-RL closure — do the checking here.

## The six conditions

| S# | Section | Statement | Checked by |
|---|---|---|---|
| S9 | 4.4 | `skos:ConceptScheme` is disjoint with `skos:Concept`. | SHACL (`sh:not`/`sh:class`), SPARQL |
| S13 | 5.4 | `skos:prefLabel`, `skos:altLabel` and `skos:hiddenLabel` are pairwise disjoint properties. | SHACL (`sh:disjoint`), SPARQL |
| S14 | 5.4 | A resource has no more than one value of `skos:prefLabel` per language tag. | SHACL (`sh:uniqueLang`), SPARQL |
| S27 | 8.4 | `skos:related` is disjoint with the property `skos:broaderTransitive`. | SPARQL only (needs closure or a property path) |
| S37 | 9.4 | `skos:Collection` is disjoint with each of `skos:Concept` and `skos:ConceptScheme`. | SHACL (`sh:not`/`sh:class`), SPARQL |
| S46 | 10.4 | `skos:exactMatch` is disjoint with each of the properties `skos:broadMatch` and `skos:relatedMatch`. | SHACL (`sh:disjoint`), SPARQL |

**Labelled total: 6 conditions checked. 5 catchable by SHACL (S9,
S13, S14, S37, S46). All 6 catchable by SPARQL. 1 (S27) needs either
a property-path traversal over `skos:broader+` or an OWL-RL closure
pass, because `skos:broaderTransitive` is a derived relation that is
almost never asserted directly in real data.**

Every command below was actually run against
[`sample-vocab.ttl`](sample-vocab.ttl) (valid — every check reports
no violation) and
[`sample-vocab-broken.ttl`](sample-vocab-broken.ttl) (the same
vocabulary with exactly one planted violation per condition,
commented `VIOLATION-S<n>` at the offending triple). Output below is
abridged but not edited for content.

## Artifacts in this directory

- [`skos-shapes.ttl`](skos-shapes.ttl) — SHACL shapes for S9, S13,
  S14, S37, S46 (the five conditions expressible without transitive
  closure).
- [`queries/`](queries) — one SPARQL file per condition, including
  both the property-path and the closure-dependent variant of S27.
- [`skos-axioms.ttl`](skos-axioms.ttl) — the SKOS OWL axioms
  (`owl:TransitiveProperty`, `owl:SymmetricProperty`, `owl:inverseOf`,
  `rdfs:subPropertyOf` ladders) transcribed from `skos.rdf` as plain
  data, so this project's existing generic OWL 2 RL closure derives
  SKOS entailments with no SKOS-specific engine code.
- [`sample-vocab.ttl`](sample-vocab.ttl) / [`sample-vocab-broken.ttl`](sample-vocab-broken.ttl)
  — the valid/broken fixture pair every command below runs against.

## Commands

### SHACL: S9, S13, S14, S37, S46

```
bin/linux-x86_64/factoidal validate \
  --shapes skills/skos-integrity/skos-shapes.ttl \
  skills/skos-integrity/sample-vocab.ttl
```
```
sh:conforms true
```

```
bin/linux-x86_64/factoidal validate \
  --shapes skills/skos-integrity/skos-shapes.ttl \
  skills/skos-integrity/sample-vocab-broken.ttl
```
```
sh:conforms false
  [Violation] focus=...#Cat path=...#exactMatch value=...#Cat source=_:d0__anon7
  [Violation] focus=...#PetsCollection path=(none) value=...#PetsCollection source=...#CollectionNotConceptShape
  [Violation] focus=...#scheme path=(none) value=...#scheme source=...#ConceptSchemeNotConceptShape
  [Violation] focus=...#Animal path=...#prefLabel source=_:d0__anon3
  [Violation] focus=...#Dog path=...#prefLabel value="Dog"@en source=_:d0__anon0
```
Five violations, one per planted SHACL-checkable condition: S46
(Cat's `exactMatch`/`broadMatch` clash), S37 (`PetsCollection` also
typed `Concept`), S9 (`scheme` also typed `Concept`), S14 (`Animal`
has two `en` `prefLabel`s), S13 (`Dog`'s `prefLabel`/`altLabel`
share the value `"Dog"@en`). The planted S27 violation (`Dog`
`related` and `broader` the same concept) does not appear here — it
needs the SPARQL check below, as designed.

### SPARQL: all six, direct or property-path

```
bin/linux-x86_64/factoidal query --data skills/skos-integrity/sample-vocab.ttl \
  --query skills/skos-integrity/queries/s09-conceptscheme-concept-disjoint.rq
# false
bin/linux-x86_64/factoidal query --data skills/skos-integrity/sample-vocab-broken.ttl \
  --query skills/skos-integrity/queries/s09-conceptscheme-concept-disjoint.rq
# true
```

```
bin/linux-x86_64/factoidal query --data skills/skos-integrity/sample-vocab-broken.ttl \
  --query skills/skos-integrity/queries/s13-label-disjointness.rq -o csv
```
```
resource,value,p1,p2
http://example.org/skos-integrity/animals#Dog,Dog,http://www.w3.org/2004/02/skos/core#prefLabel,http://www.w3.org/2004/02/skos/core#altLabel
```

```
bin/linux-x86_64/factoidal query --data skills/skos-integrity/sample-vocab-broken.ttl \
  --query skills/skos-integrity/queries/s14-preflabel-unique-lang.rq -o csv
```
```
resource,lang,count
http://example.org/skos-integrity/animals#Animal,en,2
```

```
bin/linux-x86_64/factoidal query --data skills/skos-integrity/sample-vocab.ttl \
  --query skills/skos-integrity/queries/s27-related-broadertransitive-property-path.rq
# false
bin/linux-x86_64/factoidal query --data skills/skos-integrity/sample-vocab-broken.ttl \
  --query skills/skos-integrity/queries/s27-related-broadertransitive-property-path.rq
# true
```

```
bin/linux-x86_64/factoidal query --data skills/skos-integrity/sample-vocab.ttl \
  --query skills/skos-integrity/queries/s37-collection-disjoint.rq
# false
bin/linux-x86_64/factoidal query --data skills/skos-integrity/sample-vocab-broken.ttl \
  --query skills/skos-integrity/queries/s37-collection-disjoint.rq
# true
```

```
bin/linux-x86_64/factoidal query --data skills/skos-integrity/sample-vocab-broken.ttl \
  --query skills/skos-integrity/queries/s46-exactmatch-mapping-clash.rq -o csv
```
```
a,b
http://example.org/skos-integrity/animals#Cat,http://example.org/skos-integrity/external#Cat
```

All six ran clean (no rows / `false`) against `sample-vocab.ttl` and
caught exactly the planted violation against
`sample-vocab-broken.ttl` — no false positives, no false negatives.

### S27, the materialized-closure variant

The property-path variant above needs no closure. The literal
reading of S27 — `skos:related` disjoint with `skos:broaderTransitive`
— only makes sense once `skos:broaderTransitive` has actually been
derived. Load `skos-axioms.ttl` alongside the data and turn on the
OWL-RL closure:

```
bin/linux-x86_64/factoidal query --data skills/skos-integrity/sample-vocab.ttl \
  --data skills/skos-integrity/skos-axioms.ttl --entail owl-rl \
  --query skills/skos-integrity/queries/s27-related-broadertransitive-materialized.rq
# false
bin/linux-x86_64/factoidal query --data skills/skos-integrity/sample-vocab-broken.ttl \
  --data skills/skos-integrity/skos-axioms.ttl --entail owl-rl \
  --query skills/skos-integrity/queries/s27-related-broadertransitive-materialized.rq
# true
```

Confirm the closure is doing real work, not coincidentally matching:
without the axioms and `--entail`, zero `skos:broaderTransitive`
triples exist in the data (`skos:broaderTransitive` is never asserted
in the fixtures); with them, the closure derives it including the
two-hop case (`Dog` broader `Mammal` broader `Animal`):

```
bin/linux-x86_64/factoidal query --data skills/skos-integrity/sample-vocab.ttl \
  --data skills/skos-integrity/skos-axioms.ttl --entail owl-rl \
  -e 'PREFIX skos: <http://www.w3.org/2004/02/skos/core#> SELECT ?a ?b WHERE { ?a skos:broaderTransitive ?b }' -o csv
```
```
a,b
http://example.org/skos-integrity/animals#Mammal,http://example.org/skos-integrity/animals#Animal
http://example.org/skos-integrity/animals#Dog,http://example.org/skos-integrity/animals#Mammal
http://example.org/skos-integrity/animals#Dog,http://example.org/skos-integrity/animals#Animal
http://example.org/skos-integrity/animals#Cat,http://example.org/skos-integrity/animals#Mammal
http://example.org/skos-integrity/animals#Cat,http://example.org/skos-integrity/animals#Animal
```

```
bin/linux-x86_64/factoidal query --data skills/skos-integrity/sample-vocab.ttl \
  -e 'PREFIX skos: <http://www.w3.org/2004/02/skos/core#> SELECT ?a ?b WHERE { ?a skos:broaderTransitive ?b }' -o csv
```
```
a,b
```

The derivation runs through two generic OWL-RL rules, neither of
which knows anything about SKOS:
`RDF.Graph.Executable.fst`'s `rdfs_rule_subPropertyOf` (rule
"rdfs7": `skos:broader rdfs:subPropertyOf skos:broaderTransitive`
plus the asserted `broader` edges yields `broaderTransitive` edges)
followed by the transitive-property rule ("prp-trp":
`skos:broaderTransitive rdf:type owl:TransitiveProperty` plus the
two-hop `Dog broaderTransitive Mammal` / `Mammal broaderTransitive
Animal` yields `Dog broaderTransitive Animal`). `skos-axioms.ttl`
also declares `skos:related` `owl:SymmetricProperty` (rule
"prp-symp") and the full mapping-property ladder
(`owl:inverseOf`, `rdfs:subPropertyOf`) for the same reason — none of
it is exercised by the six integrity checks directly, but it is what
lets any other SPARQL query over this data see real SKOS entailments
(e.g. `skos:narrower` derived from an asserted `skos:broader`) without
hand-writing SKOS-aware code anywhere in the engine.

## Engine notes

No engine gaps were found while building this skill. Everything
needed already existed: `sh:disjoint`, `sh:uniqueLang`, `sh:not` +
`sh:class`, `sh:targetClass`, `sh:targetSubjectsOf` on the SHACL
side; property paths (`+`, `^`, alternation) and `--entail owl-rl`
with generic `rdfs:subPropertyOf` / `owl:TransitiveProperty` /
`owl:SymmetricProperty` / `owl:inverseOf` rules on the SPARQL/OWL-RL
side. If a future SKOS check needs something not on this list (for
example, `owl:AllDisjointProperties` as a first-class SHACL or OWL-RL
construct, which would let S13/S27/S46 be expressed as data-level
axioms instead of external checks), that is an engine gap worth
opening an issue for — it is not a gap this skill's checks depend on
today.

## Future work: skosdex as the scale corpus

[github.com/danbri/skosdex](https://github.com/danbri/skosdex) is
the owner's running attempt to aggregate "all the SKOS in the world"
— it tracks an arbitrary number of third-party SKOS vocabularies one
folder each, fetches and caches each from its canonical source,
normalizes to N-Quads, and canonicalizes with RDFC-1.0. The live
instance (skosdex.fly.dev) currently embeds roughly 26,000 concepts
across multiple bundled, openly-licensed vocabularies.

That corpus is a natural next step for this skill, in two directions:

- **Perf**: the six checks here are all single-pass SHACL/SPARQL
  over property paths or a single OWL-RL closure — skosdex's ~26k
  concepts (and whatever larger pull a future fetch does) is a
  realistic size class to benchmark against, alongside the existing
  UK Parliament corpus (see the `perf-benchmarking` skill).
- **Integrity sweep**: running `skos-shapes.ttl` and every query in
  `queries/` across every vocabulary skosdex bundles would surface
  which real-world published SKOS vocabularies actually violate S9,
  S13, S14, S27, S37, S46 — none of the small literature on SKOS
  integrity checking has done this at any scale, as far as this
  skill's research turned up.

This is future work, not implemented here: skosdex's data was not
cloned or fetched into this repository (only its README, via
WebFetch), per the task's scope.

## What this skill does not cover

- SKOS-XL (the label-as-resource extension) — not modeled by any
  Factoidal engine yet.
- The non-integrity-condition parts of the SKOS Reference (concept
  scheme membership recommendations, notation datatypes, collection
  ordering) — out of scope for an *integrity* skill.
- Enforcing S13/S27/S46 as hard OWL-RL inconsistencies. As explained
  above, the Reference deliberately does not do this either.
