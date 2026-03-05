# KGX — Knowledge Graph eXchange

SPARQL CONSTRUCT queries for extracting life science data from Wikidata as structured RDF.

Extracted from [google/schemarama](https://github.com/google/schemarama/tree/main/kgx/).

## Structure

```
kgx/
└── wikidata/
    ├── basic/          # Raw Wikidata property IRIs in CONSTRUCT templates
    └── bioschemas/     # Remapped to Schema.org / Bioschemas vocabulary
```

## Entity Types (20)

| Entity | Wikidata Class | Description |
|--------|---------------|-------------|
| active_site | Q423026 | Protein active sites |
| anatomical_structure | Q4936952 | Anatomical structures |
| binding_site | Q616005 | Protein binding sites |
| biological_pathway | Q4915012 | Biological pathways |
| chemical_compound | Q11173 | Chemical compounds |
| chromosome | Q37748 | Chromosomes |
| disease | Q12136 | Diseases |
| gene | Q7187 | Genes |
| mechanism_of_action | Q3271540 | Drug mechanisms of action |
| medication | Q12140 | Medications / drugs |
| pharmaceutical_product | Q28885102 | Pharmaceutical products |
| pharmacologic_action | Q50377224 | Pharmacologic actions |
| protein_domain | Q898273 | Protein domains |
| protein_family | Q417841 | Protein families |
| ribosomal_RNA | Q215980 | Ribosomal RNA |
| sequence_variant | Q15304597 | Genomic sequence variants |
| supersecondary_structure | Q7644128 | Protein supersecondary structures |
| symptom | Q169872 | Medical symptoms |
| taxon | Q16521 | Biological taxa (times out on full Wikidata) |
| therapeutic_use | Q50379781 | Therapeutic uses |

## basic/ vs bioschemas/

- **basic/**: CONSTRUCT templates use raw Wikidata property IRIs (wdt:P31, wdt:P703, etc.)
- **bioschemas/**: CONSTRUCT templates remap to Schema.org/Bioschemas vocabulary where possible:
  - `wdt:P31 wd:Q7187` → `a bio:Gene`
  - `wdt:P703` → `bio:taxonomicRange`
  - `wdt:P688` → `bio:encodesBioChemEntity`
  - `wdt:P31 wd:Q12136` → `a schema:MedicalCondition`
  - `wdt:P780` → `schema:signOrSymptom`
  - `wdt:P769` → `schema:interactingDrug`

Both variants share the same WHERE clause (querying Wikidata), only the CONSTRUCT template differs.

## Execution Target

These queries are designed to run against **QLever** (https://qlever.dev/api/wikidata) for high-performance materialization of life science knowledge graphs.

See [`docs/designissues/kgx-pipeline.md`](../docs/designissues/kgx-pipeline.md) for the full execution plan with attestation requirements.
