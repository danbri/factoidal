# KGX Pipeline: Wikidata Materialization with Attestation

## Overview

This document describes the plan for running KGX (Knowledge Graph eXchange) SPARQL CONSTRUCT queries against the QLever endpoint to materialize life science triples from Wikidata, with full attestation logging and verifiable timestamps for every operation.

## Background

### KGX (Knowledge Graph eXchange)

KGX is a collection of SPARQL CONSTRUCT queries originally from [google/schemarama](https://github.com/google/schemarama/tree/main/kgx/) that extract structured life science data from Wikidata. The queries cover 20 entity types spanning genes, proteins, diseases, chemicals, and related biomedical concepts.

Two query variants exist:
- **basic/**: Raw Wikidata property IRIs in CONSTRUCT templates
- **bioschemas/**: CONSTRUCT templates remapped to Schema.org/Bioschemas vocabulary

### QLever

[QLever](https://qlever.cs.uni-freiburg.de/) is a high-performance SPARQL engine developed at the University of Freiburg. It provides public endpoints for major knowledge bases:

- **Wikidata**: `https://qlever.dev/api/wikidata`
- **UniProt**: `https://qlever.dev/api/uniprot`
- **DBLP**: `https://qlever.dev/api/dblp`

QLever supports full SPARQL 1.1 including CONSTRUCT, scales to billions of triples, and provides fast query execution suitable for bulk materialization.

### API Usage

```bash
# Execute a CONSTRUCT query against QLever Wikidata
curl -X POST https://qlever.dev/api/wikidata \
  -H "Content-type: application/sparql-query" \
  -H "Accept: text/turtle" \
  --data-binary @kgx/wikidata/basic/gene.sparql
```

## Pipeline Architecture

### Phase 1: Query Execution

For each of the 40 SPARQL CONSTRUCT queries (20 basic + 20 bioschemas):

1. **Load query** from `kgx/wikidata/{basic,bioschemas}/{entity}.sparql`
2. **Execute** against `https://qlever.dev/api/wikidata` via HTTP POST
3. **Receive** materialized triples as Turtle/N-Triples
4. **Store** results in `kgx/output/{basic,bioschemas}/{entity}.ttl`
5. **Log attestation** for each query execution (see Attestation Model below)

### Phase 2: Graph Assembly

1. **Parse** all materialized Turtle files using our own Turtle parser (`rdf-wasm/src/turtle.rs`)
2. **Merge** into a unified RDF graph per variant (basic, bioschemas)
3. **Canonicalize** the merged graph (URDNA2015 / RDFC-1.0)
4. **Compute** cryptographic hash of canonical form (SHA-256)
5. **Sign** the graph assertion with a transform certificate

### Phase 3: Verification

1. **Validate** each materialized graph against expected SHACL shapes
2. **Cross-check** basic vs bioschemas graphs for consistency
3. **Verify** attestation chain from query execution through graph assembly
4. **Publish** verified graph bundles with provenance metadata

## Attestation Model

Every operation in the pipeline MUST produce an attestation record. The system logs verifiable timestamps and evidence for each step.

### Per-Query Attestation

Each SPARQL CONSTRUCT execution produces a `QueryExecutionAttestation`:

```turtle
:exec_gene_basic_20260305T123456Z a tr:QueryExecutionEvent ;
  tr:queryFile "kgx/wikidata/basic/gene.sparql" ;
  tr:queryHash "sha256:..." ;
  tr:endpoint <https://qlever.dev/api/wikidata> ;
  tr:httpMethod "POST" ;
  tr:httpStatus 200 ;
  tr:requestTimestamp "2026-03-05T12:34:56.123Z"^^xsd:dateTime ;
  tr:responseTimestamp "2026-03-05T12:34:58.456Z"^^xsd:dateTime ;
  tr:executionDuration "PT2.333S"^^xsd:duration ;
  tr:resultTripleCount 15234 ;
  tr:resultHash "sha256:..." ;
  tr:resultFile "kgx/output/basic/gene.ttl" ;
  tr:signature :sig_exec_gene .
```

### Verifiable Timestamps

All timestamps MUST be:
- **ISO 8601** format with millisecond precision
- **UTC timezone** (Z suffix)
- **Monotonically ordered** within a pipeline run
- **Independently verifiable** via timestamp authority or signed log

For production deployments, timestamps SHOULD be anchored to an external timestamp authority (RFC 3161 TSA or similar) to prevent backdating.

### Graph Assembly Attestation

```turtle
:assembly_basic_20260305T130000Z a tr:GraphAssemblyEvent ;
  tr:assemblyType tr:UnionMerge ;
  tr:inputGraphs ( :exec_gene_basic :exec_disease_basic ... ) ;
  tr:inputGraphCount 20 ;
  tr:totalInputTriples 245678 ;
  tr:outputGraph :merged_basic_graph ;
  tr:outputTripleCount 198432 ;
  tr:deduplicatedTriples 47246 ;
  tr:canonicalizationAlgorithm "URDNA2015" ;
  tr:outputHash "sha256:..." ;
  tr:timestamp "2026-03-05T13:00:00.000Z"^^xsd:dateTime ;
  tr:signature :sig_assembly_basic .
```

### Pipeline Run Attestation

```turtle
:pipeline_run_20260305 a tr:PipelineRunEvent ;
  tr:pipelineVersion "0.1.0" ;
  tr:softwareArtifact :factoidal_artifact ;
  tr:startTimestamp "2026-03-05T12:30:00.000Z"^^xsd:dateTime ;
  tr:endTimestamp "2026-03-05T13:15:00.000Z"^^xsd:dateTime ;
  tr:totalDuration "PT45M"^^xsd:duration ;
  tr:queryExecutions ( :exec_gene_basic :exec_disease_basic ... ) ;
  tr:graphAssemblies ( :assembly_basic :assembly_bioschemas ) ;
  tr:status tr:Completed ;
  tr:signature :sig_pipeline_run .
```

## Output Structure

```
kgx/
├── wikidata/
│   ├── basic/              # 20 SPARQL CONSTRUCT queries
│   └── bioschemas/         # 20 SPARQL CONSTRUCT queries (Schema.org vocab)
├── output/
│   ├── basic/              # Materialized Turtle per entity type
│   ├── bioschemas/         # Materialized Turtle per entity type
│   ├── merged_basic.ttl    # Union of all basic materializations
│   └── merged_bioschemas.ttl
├── attestations/
│   ├── executions/         # Per-query attestation records
│   ├── assemblies/         # Graph assembly attestations
│   └── pipeline_run.ttl    # Top-level pipeline attestation
└── README.md
```

## Implementation Plan

### Step 1: CLI Runner (Rust)

Build a `kgx-runner` CLI tool in Rust that:
- Reads .sparql files from `kgx/wikidata/`
- Executes queries against QLever via HTTP
- Writes results to `kgx/output/`
- Produces attestation records for each step
- Handles rate limiting and retry with exponential backoff

### Step 2: Attestation Logger

Implement an attestation logging module that:
- Captures timestamps with millisecond precision
- Computes SHA-256 hashes of queries and results
- Signs attestation records with Ed25519
- Serializes attestations as Turtle RDF
- Supports both file-based and in-memory attestation stores

### Step 3: Graph Assembly

Use our own Turtle parser and RDF graph implementation to:
- Parse all materialized .ttl files
- Merge into unified graphs with set-based deduplication
- Canonicalize using URDNA2015
- Produce signed graph assertions

### Step 4: Verification Pipeline

Build verification tooling to:
- Replay attestation chain
- Verify all signatures
- Confirm hash integrity
- Validate timestamp ordering
- Check SHACL shape conformance of materialized data

## Entity Type Coverage

| Entity Type | Basic Query | Bioschemas Query | Wikidata Properties |
|-------------|-------------|------------------|---------------------|
| gene | wdt:P703, P684, P682, P688, P527, P1057 | bio:taxonomicRange, bio:encodesBioChemEntity, bio:isInvolvedInBiologicalProcess | 7 UNION clauses |
| disease | wdt:P780, P828, P2293, P927, P2176 | schema:signOrSymptom, schema:associatedAnatomy, schema:drug | 6 UNION clauses |
| chemical_compound | wdt:P2868, P769, P279, P3780, P2175, P527, P361, P129, P703, P3364 | schema:chemicalRole, schema:associatedDisease, schema:hasBioChemEntityPart | 11 UNION clauses |
| medication | wdt:P2175, P3780, P527, P769, P2868 | schema:Drug, schema:interactingDrug | 8 UNION clauses |
| protein_domain | wdt:P527, P361 | (same) | 3 UNION clauses |
| protein_family | wdt:P527 | (same) | 2 UNION clauses |
| sequence_variant | wdt:P3355, P3354, P3433, P1057 | (same) | 5 UNION clauses |
| symptom | — | bio:MedicalSignOrSymptom | 1 clause |
| taxon | — | bio:Taxon | 1 clause (times out) |
| therapeutic_use | wdt:P3781, P2175 | schema:MedicalTherapy, schema:Drug | 3 UNION clauses |
| (10 others) | various | various | 1-3 UNION clauses |

## QLever Considerations

- **Rate limiting**: QLever public endpoints may throttle heavy usage. Implement exponential backoff (1s, 2s, 4s, 8s).
- **Timeouts**: Some queries (especially taxon) may time out. Add LIMIT clauses for initial runs.
- **Result size**: Large entity types (gene, chemical_compound) may return millions of triples. Stream results rather than buffering.
- **Alternative endpoints**: For production, consider running a local QLever instance with a Wikidata dump.

## Relationship to Attestation Model

This pipeline is a concrete instantiation of the general attestation architecture described in [`attestation-model.md`](attestation-model.md). The KGX query execution maps directly to `tr:TransformEvent`, with:
- SPARQL CONSTRUCT query = transformation semantics
- QLever endpoint = execution environment
- Materialized triples = output graph
- Attestation records = transform certificates

The pipeline demonstrates the full evidence chain: query provenance → execution attestation → result hashing → graph assembly → signed assertion.

## References

- [google/schemarama KGX](https://github.com/google/schemarama/tree/main/kgx/)
- [QLever](https://qlever.cs.uni-freiburg.de/)
- [Bioschemas](https://bioschemas.org/)
- [Schema.org](https://schema.org/)
- [Wikidata](https://www.wikidata.org/)
- [RFC 3161 — Internet X.509 Time Stamp Protocol](https://tools.ietf.org/html/rfc3161)
