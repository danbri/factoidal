# Shardborough corpus ladder — catalogue and rules (2026-09-01)

Purpose: make Lean 4 block-engine measurements comparable and
reproducible across sessions and machines. This is a metadata
catalogue with retrieval rules — no large data is committed to this
repository. Requested in `tmp_podman_codexfablesync.txt` (Codex,
2026-08-31/09-01); written by the review session.

## Rules (apply to every rung)

1. A corpus enters the ladder only with: source URL, retrieval date,
   sha256 of the exact bytes used, license, triple count as MEASURED
   by our own parser, and predicate/object-cardinality distribution
   emitted by a script in `tools/`. No number is written from a
   website's claim (counting-coverage discipline).
2. Every benchmark names its rung and the corpus sha256. A number
   without both is not citable.
3. Licenses: prefer CC0. CC BY is acceptable with attribution in
   this file. Avoid share-alike (CC BY-SA) for anything we may
   redistribute in fixtures; it is fine for local-only measurement,
   marked "measure-only".
4. Every rung gets the SAME workload classes run differentially
   against the in-memory Lean evaluator: subject-bound, object-bound,
   predicate COUNT, two-pattern join, literal/lang/datatype object
   match, negative lookups (absent term), and (where the rung's size
   permits) update + compaction + re-query.

## Rung 1 — tiny correctness fixtures (in repo, done)

- W3C SPARQL 1.1 / RDF 1.1/1.2 suites, vendored under
  `third_party/testing/` — term-shape coverage (lists, typed and
  language-tagged literals) now exercised through the persisted path
  (`da5886c42`, `23941fe7e`, `de85aec57`).
- Deterministic SBM6 generator (`258cbac9c`) — controlled shape/skew
  fixtures, seed-stable.

## Rung 2 — medium, real, moderately heterogeneous (in repo, done)

- `examples/wikidata/subsets/lifesci-kgx/data/gene.ttl` — 888,949
  triples (measured), Wikidata-derived, CC0. Predicate-skew-heavy,
  weak on language tags.
- Anatomical-structure Turtle — 112,742 triples (measured; see
  Codex worknotes 2026-09-01). Same provenance family.
- Gap this rung does NOT cover: language-tag diversity, datatype
  breadth, many-predicate heterogeneity, named graphs.

## Rung 3 — medium-large, heterogeneous (candidates; fetch scripts to
   be added, hashes recorded at first retrieval)

| Candidate | Why | License | Scale (order) | Notes |
|---|---|---|---|---|
| UK Parliament curated store dump | Already a project corpus (`tools/bench_ukpar_*`); ontology-rich; dates, gYear, lang strings | Open Parliament Licence | ~10^6–10^7 | The natural first heterogeneous rung; pipeline exists |
| Wikidata lexemes subset | Extreme language-tag diversity, CC0 | CC0 | 10^6+ (subset recipe) | Cut via existing lifesci-kgx-style extraction; record the query + dump date |
| DBLP RDF dump | Real bibliographic heterogeneity; stable monthly snapshots with checksums | CC0 | 10^8 full; slice to 10^6–10^7 | Good literal/typed-value mix |
| Nobel Prize Linked Data | Small but genuinely multi-lingual, multi-class | CC0 | ~10^5 | Cheap heterogeneity smoke |
| WatDiv generator | Deterministic synthetic skew/structuredness control | Academic open | any | For controlled physical-layout experiments; seed recorded |

URLs deliberately not written from memory — the fetch script records
the URL it actually used, next to the sha256, at first retrieval.

## Rung 4 — large realistic (candidates)

| Candidate | Why | License | Scale | Notes |
|---|---|---|---|---|
| Wikidata truthy subset, recipe-defined | The stated project target; CC0 | CC0 | 10^7–10^8 by recipe | Define by an extraction query committed to the repo, not by a frozen file; record dump date + sha256 of the extract |
| UniProt RDF (taxonomy or citations slice) | Real datatypes at scale | CC BY 4.0 | 10^7+ | Attribution required; measure-only until attribution added |
| Full DBLP | Real, single-file, checksummed upstream | CC0 | ~4×10^8 | Ingest-scaling rung |

## Workload (differential, all rungs)

Base: the six competitive-bench queries
(`docs/test-results/competitive-bench.json`) plus, per the SBM6
work: object-bound lookups (IRI and literal objects, language-tagged
and typed), negative object/subject lookups, and a two-pattern join
driven from each side. Every run compares rows (not counts) against
the in-memory Lean evaluator on the same data. Updates: an INSERT
DATA / DELETE DATA / compaction / re-query cycle at rungs 1–3.

## Next actions

1. `tools/corpus-fetch.sh <name>` — downloads, hashes, and appends
   the measured record to this file (script to be written when the
   first Rung-3 corpus is pulled; owner approval for anything over
   ~100 MB).
2. Distribution profiler: `tools/corpus-profile.sh` emitting
   predicate counts, object cardinality per predicate, literal
   datatype/lang histograms, via the existing engines.
3. First target, recommended: the UK Parliament corpus — it is the
   only candidate that adds heterogeneity while reusing existing
   project tooling and license clarity.
