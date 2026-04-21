# wikidata lifesci KGX subset

A snapshot of the Wikidata life-sciences KGX export — genes, diseases,
chromosomes, sequence variants, and related entities — packaged as a
demo dataset for Factoidal's SPARQL engine.

This subset exists to (a) exercise the F*-extracted evaluator on
real-world-shaped data, (b) show multi-file / multi-named-graph
queries, and (c) pin a regression benchmark for the stack-safe BGP
evaluator landed in issue #95.

## Provenance

The source KGX dump was pulled from the public Wikidata life-sciences
KGX pipeline on 2026-04-20 and cached under `tmp/wikidata-lifesci-kgx/`
during that morning's exploration. These files are subsets of
Wikidata (CC0) — no modification beyond re-serialising to Turtle.

## Contents

Twenty-one Turtle files. Everything under `data/` is plain Turtle;
gene.ttl is the largest at 17 MB (888,949 triples).

| file                           | size  | shape                                              |
| ------------------------------ | ----: | -------------------------------------------------- |
| active_site.ttl                | 17 KB | `?site wdt:P31 wd:Q2512590`                        |
| anatomical_structure.ttl       | 3.6MB | `?x wdt:P31 / P527 / P361 …`                       |
| binding_site.ttl               | 13 KB | binding sites                                      |
| biological_pathway.ttl         | 1.4MB | pathways, has-part (P527), part-of (P361)          |
| chemical_compound.ttl          | 6.6KB | chemical compounds                                 |
| chromosome.ttl                 | 312KB | `?c wdt:P31 wd:Q37748` — 9,227 chromosomes         |
| disease.ttl                    | 836KB | `?d wdt:P2293 ?gene` (genetic assoc) — 4,188 rows  |
| gene.ttl                       |  17MB | `?g a bio:Gene` (92k), P684 ortholog (99k), P1057  |
|                                |       | chromosome (11k), P688 encodes (1.6k) — 889k total |
| mechanism_of_action.ttl        |  9 KB | mechanisms                                         |
| medication.ttl                 | 173KB | P2176 treats-disease                               |
| pharmaceutical_product.ttl     | 160KB | products                                           |
| pharmacologic_action.ttl       |  8 KB | actions                                            |
| protein_domain.ttl             | 652KB | domains                                            |
| protein_family.ttl             | 2.2MB | families                                           |
| Protein__protein2.ttl          | 1.3MB | proteins subset 2                                  |
| Protein__protein4.ttl          |  11KB | proteins subset 4                                  |
| ribosomal_RNA.ttl              | 94 KB | rRNA                                               |
| sequence_variant.ttl           | 236KB | P3433 (variant-of-gene) 1,702; P1057 chrom 1,351   |
| supersecondary_structure.ttl   |  40KB | structures                                         |
| symptom.ttl                    |  44KB | symptoms                                           |
| therapeutic_use.ttl            |  5 KB | therapeutic uses                                   |

## Files not included in this subset

Three files from the upstream KGX export are too large for a plain
git commit and are **not** checked in:

| file                    | size   | why skipped                               |
| ----------------------- | -----: | ----------------------------------------- |
| Protein__protein1.ttl   |  34 MB | large, not central to demo joins          |
| Protein__protein3.ttl   |  50 MB | at GitHub's 50 MB soft-warning threshold  |
| taxon (timesout).ttl    | 140 MB | over GitHub's 100 MB hard limit           |

If you need them, pull them locally from the upstream source. To
commit them into this repo you would need to set up `git lfs` first
(`brew install git-lfs && git lfs install && git lfs track "*.ttl"`),
which this repo has not adopted yet. Recommendation: keep this subset
as-is and lean on LFS only if gene.ttl starts bloating history. For
now, a single 17 MB gene.ttl is acceptable.

## Running the queries

All queries live under `queries/`. They assume each file is loaded as
a named graph keyed by the URN `urn:kgx:<basename>`.

### Small, fast examples (complete in under a second)

**03 — sequence variants on each chromosome** (cross-graph join):

```bash
./bin/darwin-arm64/factoidal \
  --named urn:kgx:chromosome=examples/wikidata/subsets/lifesci-kgx/data/chromosome.ttl \
  --named urn:kgx:sequence_variant=examples/wikidata/subsets/lifesci-kgx/data/sequence_variant.ttl \
  --query examples/wikidata/subsets/lifesci-kgx/queries/03_variant_on_chromosome.rq
```

**04 — top diseases by count of genetically-associated genes**
(single-graph aggregation):

```bash
./bin/darwin-arm64/factoidal \
  --named urn:kgx:disease=examples/wikidata/subsets/lifesci-kgx/data/disease.ttl \
  --query examples/wikidata/subsets/lifesci-kgx/queries/04_diseases_with_most_gene_associations.rq
```

### Queries that touch gene.ttl (the 889k-triple one)

Measured on macOS arm64 (Apple Silicon) against the checked-in
factoidal binary, post-issue-#95.

**01 — count triples per named graph**: group-by over (?g ?s ?p ?o).
Fast on small graphs (~7 s for disease + chromosome + sequence_variant
= ~43k triples). Slow with gene.ttl added (~6 min, because the
GROUP BY aggregator is O(n²)). For a fast per-file count, use
`factoidal --count <file>` instead — the Turtle fast path reports
~889k triples for gene.ttl in ~4 s without materialising a triple
list.

**02 — top types across all graphs**: union over two instance-of
predicates (P31 and rdf:type), grouped by class. ~2 m 30 s with
gene + chromosome + disease + sequence_variant loaded. Reports
91,871 bio:Gene + 13,283 disease + 9,227 chromosome + 1,800 variant
instances. Pre-#95 this query would stack-overflow; it now
completes correctly, just slowly.

**05 — disease-gene cross-graph join**: nominally interesting but
naive BGP evaluation is O(outer × inner_graph_size) ≈
4,188 × 889,000 ≈ 3.7 × 10^9 ops. Included as a stress test: it
completes without stack overflow (that was the #95 bug) but is slow
without an indexed store (see
`docs/designissues/sparql-store-backend.md`). Not run to completion
in the reference timings above.

### Running count-only via the Turtle fast path

`--count` short-circuits any Turtle input to the F*-verified
codepoint counter, no triple list materialised:

```bash
./bin/darwin-arm64/factoidal --count examples/wikidata/subsets/lifesci-kgx/data/gene.ttl
# → gene.ttl: 888949 triples   (~4 s)
```

## Performance notes

The default backend is a list-backed in-memory graph. BGP evaluation
scans the triple list per pattern, so joins cost O(outer × graph_size).
For two small named graphs (chromosome × sequence_variant ≈ 9k × 3.6k)
this finishes in well under a second; for anything that iterates gene.ttl
per outer solution, the cost is measured in seconds to minutes.

The fix for that is an indexed in-memory store — tracked at
`docs/designissues/sparql-store-backend.md`. Until then, pick
queries that either (a) don't join at all (just count/aggregate on
one graph), (b) join between small graphs, or (c) tolerate multi-
minute runs for the headline disease-gene join.
