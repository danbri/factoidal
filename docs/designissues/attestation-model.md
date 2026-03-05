# Verified RDF Transform System Documentation Bundle

This document combines three design artifacts into a single reference:
1. System overview (CLAUDE.md)
2. System architecture (verified-rdf-transform-design.md)
3. RDF data model for attestations (rdf-transform-attestation-model.md)

The goal is to define an infrastructure where RDF graphs become verifiable units of knowledge and graph transformations become cryptographically attestable events.

The design targets post-LLM infrastructure, where automated tools and services must generate machine-verifiable evidence about the data they produce.

---

## System Overview

### Verified RDF Transform System

This repository contains a clean-room implementation of a formally grounded RDF graph transformation system intended for high-trust environments.

The system targets infrastructure where automated agents, reasoning services, and data pipelines must provide cryptographically verifiable assertions about graph data and the transformations applied to it.

Core goals include:
- Treat graphs as units of assertability
- Produce signed transformation assertions
- Support verifiable credentials for graph provenance
- Enable formally verified reasoning kernels
- Integrate with modern supply-chain attestation ecosystems
- Meet the needs of regulated industries and safety-critical environments

Key concepts include:
- **Graph Transform Certificates**
- **Named Graph Operation Structures**
- **Verifiable Credentials** representing reasoning events
- **Formally verified semantics** implemented in F*
- **Supply-chain provenance** using Sigstore and in-toto
- **Runtime attestation** using confidential computing platforms

The design assumes that in modern automated systems:

trust must be computable,
assertions must be machine-verifiable,
and tools must emit evidence rather than mere results.

---

## Architecture and Design

### Introduction

Modern computing infrastructure increasingly relies on automated reasoning systems, machine-generated data, and distributed data pipelines. In such environments, traditional trust assumptions—where users implicitly trust the software that produced a dataset—are insufficient.

Instead, systems must produce verifiable evidence describing the computations that generated their outputs.

This architecture treats RDF graphs as portable, assertable knowledge objects and graph transformations as verifiable computational events.

A transformation therefore produces not only an output graph but also a signed certificate describing the computation that generated it.

The system integrates four complementary assurance mechanisms:
- formally verified reasoning semantics
- cryptographically signed transformation artifacts
- supply-chain provenance attestations
- optional runtime attestation within trusted execution environments

Together these mechanisms establish a chain of evidence connecting mathematical specification, compiled software artifact, execution environment, and resulting data.

---

### Graphs as Assertable Knowledge Units

Traditional RDF infrastructure treats graphs as passive containers of triples.

This design instead models a graph as a verifiable assertion object consisting of:
- a dataset of triples
- a canonical representation
- a cryptographic digest
- provenance and transformation metadata

This structure allows graphs to circulate between systems while preserving their identity and verifiability.

The identity of a graph is derived from a canonicalized representation produced by a deterministic dataset canonicalization algorithm.

This canonical representation is hashed using a cryptographic digest algorithm such as SHA-256 or SHA-3.

A digital signature can then bind the hash to an identity.

This approach enables independent verification of graph integrity without requiring trust in the system that originally produced the graph.

---

### Dataset and Named Graph Structure

The system operates over RDF datasets containing multiple named graphs.

Different graphs represent different semantic roles within a transformation pipeline.

Typical dataset structure:
- **assertion graph** containing original triples
- **inference graph** containing derived triples
- **provenance graph** describing the transformation
- **metadata graph** containing signatures and attestations

Separating these components enables independent verification of reasoning results and provenance records.

Named graphs therefore function as operational units within reasoning pipelines.

---

### RDF Dataset Canonicalization

Cryptographic signatures over RDF graphs require deterministic canonicalization.

The system supports dataset canonicalization algorithms compatible with emerging standards including:
- URDNA2015
- RDFC-1.0 (when finalized)

Canonicalization performs deterministic blank node labeling and normalized dataset serialization.

The canonical dataset representation enables:
- deterministic hashing
- reproducible reasoning results
- stable graph identity across serializations

The canonicalization pipeline is:
1. canonicalize dataset
2. serialize canonical dataset
3. compute cryptographic hash
4. encode digest using multihash

---

### Verified Reasoning Kernel

The semantic reasoning kernel is specified and verified using the F* verification language.

Rather than verifying an entire RDF store, the architecture isolates a small reasoning kernel implementing core graph transformations such as RDFS closure.

Within the F* specification:
- RDF terms are modeled as typed values
- triples are structured objects
- graphs are finite sets of triples

The RDFS closure algorithm is defined according to the RDF semantics specification.

Formal proofs establish:

**Soundness**
Every produced triple is logically entailed by the input graph.

**Termination**
Closure computation halts for finite graphs.

**Idempotence**
closure(closure(G)) = closure(G)

**Determinism**
Identical inputs produce identical outputs.

The verified kernel therefore defines the authoritative semantics of reasoning operations.

---

### Cryptographic Foundations

Cryptographic primitives are implemented using components derived from the Project Everest ecosystem, particularly HACL\* and EverCrypt.

These libraries provide formally verified implementations of widely used cryptographic algorithms including:
- SHA-2 and SHA-3 hash functions
- Ed25519 digital signatures
- X25519 key exchange primitives

Using verified cryptographic libraries reduces the risk of implementation errors in security-critical components.

---

### Transform Certificates

Every graph transformation produces a transform certificate describing the computation.

A certificate binds together:
- input graph hash
- output graph hash
- transformation semantics
- transformation artifact identity
- build provenance references
- runtime attestation references
- timestamp
- digital signature

Certificates may be serialized in JSON-LD, RDF, or CBOR-LD.

The signature ensures the transformation record cannot be altered without detection.

---

### Supply-Chain Provenance

Transformation artifacts are accompanied by signed build provenance.

Provenance metadata is generated using:
- in-toto attestations
- Sigstore / cosign signatures
- software bill of materials (SBOM)

Attestations describe:
- source repository
- commit identifier
- build environment
- dependency graph
- artifact hashes

This allows verifiers to confirm that the artifact used for a transformation corresponds to known source code and a documented build pipeline.

---

### Containerized Execution

Transformations run inside minimal container environments.

Container images contain:
- reasoning engine
- canonicalization implementation
- runtime dependencies

Images are referenced by immutable digests rather than mutable tags.

Images are signed using Sigstore cosign.

Containerization improves reproducibility but does not by itself guarantee trusted execution.

---

### Runtime Attestation

For stronger guarantees, transformations may execute inside trusted execution environments (TEEs).

Examples include:
- AMD SEV-SNP
- Intel TDX
- ARM Confidential Compute Architecture
- confidential container platforms

These environments produce attestation tokens describing the measured software environment.

Attestation tokens may be embedded in transform certificates.

Verifiers can validate these tokens against platform root keys to confirm the execution environment.

---

### Evidence Chain

The system constructs an evidence chain linking specification to data.

Formal semantics define algorithm correctness.

Signed artifacts ensure binary integrity.

Supply-chain attestations document build processes.

Runtime attestations verify execution environments.

Transform certificates bind the resulting data to this evidence chain.

Each layer addresses a different trust boundary.

---

### Verifiable Credentials

Transform certificates may be issued as verifiable credentials.

The credential subject represents a graph transformation event.

Credential claims include:
- input graph hash
- output graph hash
- semantics version
- artifact digest
- attestation references

This allows graph reasoning evidence to integrate with decentralized identity infrastructure.

---

### Application Domains

The architecture supports environments requiring strong guarantees about data provenance and computational correctness.

Examples include:
- financial analytics pipelines
- healthcare knowledge graph infrastructure
- defense data integration systems
- AI training data certification
- cross-organizational knowledge exchange networks

---

### Future Directions

Possible future extensions include:
- verified SPARQL algebra
- proof-carrying query results
- incremental reasoning certificates
- streaming transform attestations
- distributed reasoning pipelines

---

## RDF Transform Attestation Model

### Data Model Specification

#### Graph Assertion

A graph assertion represents a named RDF graph with canonical identity and provenance metadata.

Structure:

```
GraphAssertion
  graph
  canonicalHash
  canonicalizationAlgorithm
  signature
  metadata
```

The canonical hash is derived from deterministic dataset canonicalization.

---

#### Transform Event

A transform event represents a graph transformation execution.

Example RDF structure:

```turtle
:transform123 a tr:TransformEvent ;
  tr:transformType tr:RDFSClosure ;
  tr:semanticsVersion "rdfs-core-v1" ;
  tr:inputGraph :graphA ;
  tr:outputGraph :graphB ;
  tr:artifact :artifactDigest ;
  tr:buildProvenance :buildAttestation ;
  tr:runtimeAttestation :runtimeEvidence ;
  tr:timestamp "2026-03-05T12:34:56Z" ;
  tr:signature :sig1 .
```

#### Artifact Identity

Artifacts are identified by cryptographic digest.

```turtle
:artifactDigest a tr:Artifact ;
  tr:digest "sha256:abcd..." ;
  tr:containerImage "registry.example.org/rdf-transform@sha256:abcd..." .
```

#### Build Attestation

Build provenance records describe artifact creation.

```turtle
:buildAttestation a tr:BuildProvenance ;
  tr:builder "github-actions" ;
  tr:sourceRepository <https://github.com/example/repo> ;
  tr:sourceCommit "abcdef12345" ;
  tr:sbom <sbom.json> ;
  tr:attestationDigest "sha256:xyz..." .
```

#### Runtime Attestation

Runtime attestation evidence describes execution environment.

```turtle
:runtimeEvidence a tr:RuntimeAttestation ;
  tr:attestationType tr:SEVSNP ;
  tr:measurementDigest "sha256:..." ;
  tr:reportBlob "...encoded evidence..." ;
  tr:verificationService <https://attest.example.org> .
```

---

### Shadow Graphs

Large graphs may be decomposed into shadow graphs.

Shadow graphs represent subsets of triples corresponding to logical partitions, typically defined by SHACL shapes.

Example decomposition:

```turtle
:largeGraph a tr:GraphAssertion ;
  tr:canonicalHash "sha256:..." ;
  tr:hasShadowGraph :sg1 ;
  tr:hasShadowGraph :sg2 ;
  tr:hasShadowGraph :sg3 .
```

Example shadow graph:

```turtle
:sg1 a tr:ShadowGraph ;
  tr:shape :PersonShape ;
  tr:canonicalHash "sha256:..." ;
  tr:sourceGraph :largeGraph .
```

The union of shadow graphs reconstructs the original dataset.

`Union(shadowGraphs) = originalGraph`

Shadow graphs enable:
- modular verification
- partial reasoning
- per-shape signatures
- scalable graph processing

---

### Verification Workflow

To verify a transformation:
1. canonicalize input graph
2. verify input graph hash
3. canonicalize output graph
4. verify output graph hash
5. validate artifact signature
6. verify build provenance
7. verify runtime attestation (optional)
8. verify transform certificate signature

If shadow graphs exist, reconstruct the dataset and verify canonical identity.

---

### Summary

This model enables RDF systems to produce portable, verifiable evidence describing graph transformations.

Key properties include:
- canonical graph identities
- signed transformation certificates
- supply-chain provenance integration
- optional runtime attestation
- graph decomposition through shadow graphs
- compatibility with verifiable credential ecosystems

Together these mechanisms allow graph reasoning infrastructure to produce not only results but verifiable claims about how those results were computed.
