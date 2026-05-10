# RDF dataset survey for engine testing

Date: 2026-05-10
Branch: `claude/research-rdf-datasets-tvQYj`

## Why this list

We want a stable of RDF dumps for testing the F\*-extracted parser /
algebra / store across scales without leaning on the obvious crutches
(Wikidata, MusicBrainz, full DBpedia). Selection criteria:

- real-world data, not synthetic;
- public-domain or Creative-Commons licensed (no commercial / privacy
  fuss);
- socially constructive subject matter (heritage, science, civic,
  scholarly);
- something to link with other datasets *beyond* the trivial place +
  time joins (people, concepts, works, taxa, periods, …);
- a payoff if you SPARQL across them — i.e. interesting joins exist;
- not the usual demo suspects;
- not so niche that the engine cannot be exercised on common SPARQL
  patterns;
- spread across scales useful for engine testing.

Triple counts and file sizes are approximate; check the download page
before sizing a benchmark. URLs are the canonical bulk-download
locations as of May 2026.

## Scale buckets

| Bucket | Triples (rough) | Use for                                  |
|--------|-----------------|------------------------------------------|
| Tiny   | < 1 M           | parser unit + correctness regression     |
| Small  | 1 M – 10 M      | algebra correctness, planner sanity      |
| Medium | 10 M – 200 M    | join performance, index build timings    |
| Large  | 200 M – 3 B     | scale-out, COTTAS benchmarking           |

Anything over ~3 B drops into "huge" (LinkedGeoData, SemOpenAlex,
LOD-a-lot HDT) and is excluded by request.

---

## Tiny (under 1 M triples)

### Nobel Prize Linked Data

- ~14.8 MB dump; few hundred thousand triples covering laureates,
  prizes, motivations, affiliations.
- CC0; SPARQL endpoint at `data.nobelprize.org/sparql`; RDF dump
  linked from [Linked Data examples](https://www.nobelprize.org/about/linked-data-examples/).
- Linkable: country / institution / DOB joins to DBpedia and VIAF; a
  classic "name a Nobel laureate born in country X" demo.
- Why it's good: socially constructive, broad-interest, small enough
  to load into memory. Great smoke test.

### PeriodO — Periods, Organized

- Single JSON-LD file (~10 MB), thousands of period definitions with
  spatial + temporal extents, OWL-Time + SKOS.
- Download: [perio.do/](https://perio.do/) (entire gazetteer as one
  file).
- Linkable: period URIs are designed to annotate other datasets
  (Pleiades, Nomisma, museum records).
- Why it's good: temporal reasoning that is *not* `xsd:dateTime` —
  fuzzy historical periods. Forces a SPARQL engine to deal with
  approximations.

### BBC Wildlife Ontology + data

- A few thousand species pages with taxonomy / habitat / conservation
  status. Mirror at [github.com/rdmpage/bbc-wildlife](https://github.com/rdmpage/bbc-wildlife).
- Linkable: NCBI Taxonomy IDs, IUCN Red List, Wikipedia.
- Why it's good: small and clean; the ontology itself is a textbook
  example used in semantic-web courses.

### Schema.org / FOAF / SKOS / RDFS / OWL vocabularies

- Each is kilobytes-to-low-megabytes RDF.
- Discovery: [Linked Open Vocabularies (LOV)](https://lov.linkeddata.es/dataset/lov)
  catalogues 600+; [DBpedia Archivo](https://www.dbpedia.org/resources/archivo/)
  crawls 1300+.
- Why they're good: terminology consistency / OWL reasoning tests
  with no I/O drama.

---

## Small (1 M – 10 M triples)

### Pleiades — gazetteer of ancient places

- ~31 K places + 26 K name variants + 31 K locations, with
  time-period links. Daily Turtle / RDF/XML / GeoJSON dumps at
  [atlantides.org/downloads/pleiades/dumps](http://atlantides.org/downloads/pleiades/dumps).
  Estimated 1–3 M triples.
- Linkable: PeriodO, Nomisma, Pelagios consortium, Wikidata.
- Why it's good: classics + GIS overlap, well-curated, hub of the
  ancient-world LOD network. Beyond-place-time joins land naturally
  on people (rulers, deities) and works (inscriptions).

### AGROVOC (FAO multilingual thesaurus)

- 32 K+ concepts, 21 languages, ~3 M triples in CORE; LOD release
  with mappings to 16 other vocabularies.
- Download: [www.fao.org/agrovoc/releases](https://www.fao.org/agrovoc/releases) — N-Triples + RDF/XML.
- Linkable: EuroVoc, NAL Thesaurus, GEMET, Wikidata.
- Why it's good: multilingual SKOS at scale (great for language-tag
  + collation tests), socially constructive (food / agriculture
  domain), unusual cross-language joins.

### Princeton WordNet RDF / Open English WordNet

- ~5 M triples (synsets, senses, lemmas, ontolex-lemon).
- Download: [wordnet-rdf.princeton.edu](http://wordnet-rdf.princeton.edu/about),
  [globalwordnet.github.io/english-wordnet](https://github.com/globalwordnet/english-wordnet).
- Linkable: BabelNet, DBnary, multilingual wordnets, lexical
  resources for almost every language.
- Why it's good: the canonical lexical knowledge graph; a *lot* of
  hops are needed to navigate it (synset → sense → lemma → other
  synsets), so query plans matter.

### Nomisma — numismatics

- Concept vocabulary regenerated nightly + 134 K+ Greek/Roman coin
  records via federated partner sites (OCRE, CRRO, …).
- Download: [www.nomisma.org/datasets](https://www.nomisma.org/datasets);
  GitHub mirror with full git history back to 2012.
- Linkable: Pleiades (mints), PeriodO (eras), Getty AAT (materials),
  museum catalogues.
- Why it's good: niche-feeling, but the schema is general (places,
  people, materials, dates, types) so it exercises the whole
  algebra. Bonus: data goes back centuries.

### Project Gutenberg metadata RDF

- ~100 MB compressed concatenated RDF/XML over the entire ebook
  catalogue; per-book RDF files also available.
- Download: [www.gutenberg.org/cache/epub/feeds/](https://www.gutenberg.org/cache/epub/feeds/).
- Linkable: VIAF, LCNAF, Wikidata authors, BNF, GND.
- Why it's good: stable, public-domain, clean Dublin Core / DCMI
  terms — a very gentle real-world parser test.

### Getty AAT (Art & Architecture Thesaurus)

- Several million triples, ~50 K subject IDs, monthly N-Triples dump.
- Download: [www.getty.edu/research/tools/vocabularies/obtain/download.html](https://www.getty.edu/research/tools/vocabularies/obtain/download.html).
- Linkable: Wikidata, LCSH, Rijksmuseum, Library of Congress, every
  serious museum catalogue.
- Why it's good: SKOS + ISO 25964 thesaurus; dense hierarchy makes
  property-path queries (`skos:broader+`) interesting.

---

## Medium (10 M – 200 M triples)

### Getty TGN (Thesaurus of Geographic Names)

- ~2.4 M place records, monthly N-Triples dump (estimated tens of
  millions of triples).
- Same download page as AAT.
- Linkable: Pleiades, GeoNames, Wikidata, GND geographika.
- Why it's good: includes historical place names with temporal
  qualifiers — a nice complement to GeoNames / LinkedGeoData.

### Getty ULAN (Union List of Artist Names)

- ~370 K artist / patron / studio records, several tens of millions
  of triples.
- Linkable: VIAF, Rijksmuseum, British Museum, Wikidata.
- Why it's good: agent / role / event modelling that is not just
  "person born in country."

### Library of Congress Subject Headings (LCSH)

- SKOS/RDF: ~40 MB Turtle (low tens of millions of triples).
- Download: [id.loc.gov/download/](https://id.loc.gov/download/) under
  `authorities/subjects.[fmt].gz`. Weekly incrementals also available.
- Linkable: pretty much every cataloguing system in the
  English-speaking world.
- Why it's good: clean SKOS, tractable size, *the* US authority
  vocabulary.

### Rijksmuseum collection as Linked Data

- 350 K+ objects, CIDOC-CRM (Linked Art profile) + Schema.org,
  N-Triples dumps.
- Download: [data.rijksmuseum.nl/docs/data-dumps](https://data.rijksmuseum.nl/docs/data-dumps/).
- Linkable: Getty AAT/TGN/ULAN, Wikidata, IIIF image manifests.
- Why it's good: heavy reification (events, productions, materials,
  acquisitions) — a real CIDOC-CRM workout.

### FactGrid (humanities Wikibase)

- ~1.3 M items across ~50 historical / Assyriological / cuneiform
  projects. RDF dumps via the standard
  [Wikibase RDF dump format](https://www.mediawiki.org/wiki/Wikibase/Indexing/RDF_Dump_Format)
  at [database.factgrid.de](https://database.factgrid.de/) (estimated
  tens of millions of triples).
- Linkable: Wikidata via mirrored properties; VIAF and GND for people.
- Why it's good: Wikibase semantics (qualifiers, references, ranks)
  on a manageable scale, and it covers history that Wikidata
  notability would never accept (Sumerian scribes, minor 18th-century
  jurists).

### GeoNames (gazetteer)

- ~12 M features, ~182 M triples in the official RDF dump.
- Download: [www.geonames.org/ontology](https://www.geonames.org/ontology)
  (note: dump format is one-toponym-per-line RDF/XML, not flat
  N-Triples, which is itself a useful parser test).
- Linkable: every place dataset on this list.
- Why it's good: borderline medium / large; an honest stress test for
  IRI handling without committing to billions of triples.

### lobid-resources / lobid-organisations / lobid-gnd

- German library bibliographic + authority data; lobid-gnd alone is
  the entire GND (Integrated Authority File). RDF dumps from
  [data.dnb.de/opendata/](https://data.dnb.de/opendata/) under CC0;
  also on [hbz/lobid-gnd](https://github.com/hbz/lobid-gnd).
- Linkable: VIAF, LCNAF, Wikidata, Europeana, Rijksmuseum.
- Why it's good: high-quality cataloguing data with strong
  cross-walks; mid-sized partition of the `lobid-resources` dump
  is a good benchmark target.

---

## Large (200 M – 3 B triples)

### DBLP RDF (computer science bibliography)

- ~7 M publications + 3 M persons, ~250 M triples (March 2022,
  growing). Daily-synced with the XML release.
- Download: [DROPS Dagstuhl monthly snapshots](https://drops.dagstuhl.de/entities/collection/10.4230/dblp.rdf.ntriples) — single
  N-Triples file per release; CC0.
- Linkable: ORCID, Crossref / DOI, OpenCitations, Wikidata.
- Why it's good: clean schema, monotonic growth, every CS researcher
  has a dog in this fight; useful for joining against citation graphs.

### VIAF (Virtual International Authority File)

- Cluster dataset ~2.1 GB gzipped RDF (high hundreds of millions of
  triples). Monthly dumps.
- Download: [viaf.org/en/viaf/data](https://viaf.org/en/viaf/data).
- Linkable: every national library authority, ORCID, GND, LCNAF,
  Wikidata.
- Why it's good: the people-identity backbone of the linked-data
  cultural-heritage world. Provenance-heavy (each cluster cites
  source authorities) — exercises named-graph / quad handling.

### Library of Congress NAF (Name Authority File)

- ~3 GB Turtle (low billions of triples in MADS/RDF; SKOS/RDF view is
  smaller).
- Download: [id.loc.gov/download/](https://id.loc.gov/download/) under
  `authorities/names.[fmt].gz`.
- Why it's good: the largest "people + corporate body" SKOS dataset
  the US issues. Great for testing aggressive blank-node + reified
  relationship handling.

### EU Cellar / EUR-Lex

- ~2.7 M legislative works in the Common Data Model; full bulk RDF
  via [data.europa.eu/data/datasets](https://data.europa.eu/data/datasets) and
  the [Cellar bulk-download service](https://op.europa.eu/en/web/cellar/users)
  (low billions of triples). Weekly updated.
- Linkable: EuroVoc, ECLI, national legal portals.
- Why it's good: legally important real-world data, multilingual,
  with deep ELI-versioning that exercises temporal / version-aware
  query patterns.

### OpenCitations Index (COCI + family)

- ~3.5 B RDF statements (citation data + provenance) as of 2025
  releases. CSV + N-Triples + the entire triplestore on Internet
  Archive.
- Download: [opencitations.net/download](https://opencitations.net/download).
- Linkable: Crossref DOIs, DBLP, ORCID, OpenAlex.
- Why it's good: scholarly knowledge-graph data the size of a serious
  benchmark, but still bounded — no need to take in OpenAlex's 26 B
  triples to get a real workload.

---

## Honourable mentions (not surveyed in detail)

- **British Museum** — RDF / CIDOC-CRM via SPARQL endpoint at
  [collection.britishmuseum.org/resource/sparql](https://collection.britishmuseum.org/resource/sparql);
  no straightforward bulk dump, so harder to ingest off-line.
- **EuroVoc** — EU multilingual thesaurus, SKOS, registration required
  to download. Sits naturally next to AGROVOC and CELLAR.
- **Pelagios annotations** — graph linking ancient-world resources
  via Pleiades. Distributed across partner sites; harder to pull
  as one dump.
- **DataCite + ORCID + Crossref** — research-identifier metadata.
  Crossref / ORCID dumps are bulk-downloadable but mostly JSON;
  RDF derivations exist (e.g. ORCID-as-OWL on Zenodo) but are
  unofficial. OpenAIRE's SPARQL endpoint was retired in May 2023.
- **Bio2RDF** — life-sciences mashup, ~45 B triples across ~20
  datasets. Most individual datasets fall in the medium bucket if
  taken alone; mirroring the whole thing is huge.

## Pairings worth trying

- **Pleiades × PeriodO × Nomisma** — ancient places × periods ×
  coins. Beautiful three-way join through small datasets; total
  well under 10 M triples.
- **DBLP × OpenCitations × ORCID** — scholarly graph; tests how
  the engine joins across two different bibliographic universes.
- **Getty AAT × Rijksmuseum × ULAN** — museum metadata pipeline,
  exercises CIDOC-CRM reasoning and SKOS broader-narrower hops.
- **AGROVOC × EuroVoc × CELLAR** — agriculture vocabulary mapped to
  EU thesaurus mapped to legislative texts that cite them. Real
  policy-research workflow.
- **lobid-gnd × VIAF × DBLP** — cross-walking three different
  authority files for the same people; classic owl:sameAs /
  skos:exactMatch handling.

## Acquisition and licensing summary

| Source                    | License       | Bulk dump? | Format              |
|---------------------------|---------------|------------|---------------------|
| Nobel Prize               | CC BY-NC      | yes        | RDF/XML             |
| PeriodO                   | CC BY         | yes        | JSON-LD             |
| BBC Wildlife              | OGL           | yes (mirror) | RDF/XML           |
| Pleiades                  | CC BY         | yes        | Turtle, RDF/XML     |
| AGROVOC                   | CC BY         | yes        | NT, RDF/XML, NQ     |
| Princeton WordNet         | WordNet 3.0   | yes        | NT                  |
| Nomisma                   | CC BY         | yes        | RDF/XML, JSON-LD    |
| Project Gutenberg         | PD            | yes        | RDF/XML             |
| Getty AAT/TGN/ULAN        | ODC-By        | yes        | NT                  |
| LCSH / LCNAF              | CC0           | yes        | NT, TTL, JSON-LD, XML |
| Rijksmuseum LOD           | CC0           | yes        | NT                  |
| FactGrid                  | CC0           | yes        | Wikibase RDF        |
| GeoNames                  | CC BY         | yes        | RDF/XML (line-based) |
| lobid / GND               | CC0           | yes        | NT, TTL, RDF/XML, HDT |
| DBLP                      | CC0           | yes        | NT (monthly)        |
| VIAF                      | ODC-By        | yes        | RDF/XML clusters    |
| EU Cellar / EUR-Lex       | EU re-use     | yes (login) | RDF/XML            |
| OpenCitations             | CC0           | yes        | NT + CSV            |

## Next steps

If we want to commit to this as the F\* engine's regression corpus,
the obvious moves are:

1. Pick one tiny + one small + one medium + one large for the
   nightly benchmark (e.g. Nobel + Pleiades + DBLP + OpenCitations).
2. Mirror those dumps on a stable URL we control (originals rot).
3. Pin a snapshot date; bump it deliberately, not silently, so
   regressions can be attributed to the engine, not the data.
4. Record VoID / triple-count / format-distribution metadata next to
   each mirrored copy.
