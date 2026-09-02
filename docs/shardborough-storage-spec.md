---
title: Shardborough Storage and Execution Artifact Specification
description: Versioned storage, index, integrity, update, and semantic-context formats for the Factoidal block engine.
layout: spec.njk
permalink: /shardborough-storage-spec/
specStatus: Alpha Draft 0.3
specDate: "2026-09-01"
---

# Shardborough storage and execution artifact specification

## Abstract

Shardborough is Factoidal's storage architecture for large RDF datasets and
SPARQL execution. It groups dictionary-encoded RDF rows into immutable,
predicate-partitioned blocks. Separate indexes support narrow range reads.
Manifests bind the blocks and indexes into an atomic dataset generation and
record their cryptographic identities. An append-only delta log supplies
updates between generations.

The formats and their validators are implemented in Lean 4. The same bytes are
intended to work in local files, database values, object stores, native
executables, and WebAssembly hosts. The immediate goals are selective I/O,
portable execution, and explicit evidence relating stored bytes to SPARQL
results.

## Status of this document

This document defines the current Factoidal format family. It is an alpha
draft, not a W3C publication or an RDF interchange standard. Standard RDF
syntaxes remain the data-exchange boundary.

During alpha, the cited Lean definitions are normative for executable byte
layouts. Before beta, this document must contain complete field tables and
portable golden vectors so an independent implementation need not inspect Lean
source.

## 1. Scope and purpose

### 1.1 What Shardborough is

Shardborough consists of:

- immutable RDF block formats and local term dictionaries;
- independently readable subject, object, and term indexes;
- manifests that publish a checked set of artifacts as one generation;
- SHA-256 and fixed-chunk Merkle commitments for complete and range reads;
- a durable delta log, compaction epoch, and atomic generation pointer;
- Lean query paths that decode selected data and connect it to the Factoidal
  SPARQL evaluator.

A **block** is an independently encoded physical artifact. Current IBK3 blocks
contain rows for one predicate. A **generation** is an immutable set of blocks
and indexes admitted by one manifest. The current code calls this manifest a
`ShardManifest`; distribution across machines is optional.

The generation is read-only after publication. The database is not. Updates
are appended to a durable log, merged with the active generation during reads,
and periodically compacted into a new generation.

### 1.2 Intended uses

The design is intended for:

- large RDF dumps and derived knowledge graphs;
- collections of named graphs prepared in advance and selected as working
  sets;
- selective SPARQL scans and joins that should not fetch unrelated block,
  dictionary, or index pages;
- local, browser, edge, and distributed execution over the same physical
  artifacts;
- deployments that require corruption detection, reproducible generations,
  or evidence linking an execution to exact input bytes.

Predicate partitioning, sorted sidecar postings, term indexes, and manifest
summaries are performance mechanisms. They reduce bytes read and decoded;
they do not change RDF or SPARQL meaning. IBK3 primary rows currently retain
source order within each predicate-local artifact.

### 1.3 Adoption and interoperability

Shardborough is first a Factoidal storage format. Other RDF databases do not
need to adopt it. PostgreSQL, TiKV, object stores, and browser storage can host
the artifacts as opaque byte ranges behind small adapters.

It is not an RDF syntax, a replacement for SPARQL, or a global RDF term-ID
registry. A backend need not implement RDF semantics or run Lean internally;
it may provide durable bytes and range access to a native or WASM worker.

Byte-level interoperability with independent readers is a beta goal. It
requires complete field tables, golden files, feature negotiation, and
cross-implementation tests. The alpha code does not yet make that claim.

## 2. System model

### 2.1 Bulk publication

Bulk loading does not require SPARQL Update. The current Lean harness can parse
Turtle and publish predicate-local IBK3 blocks, dictionaries, indexes, Merkle
sidecars, and an SBM6 manifest. A complete publisher follows this order:

```text
RDF input
   -> parse and assign block-local term IDs
   -> partition source-order rows by predicate
   -> encode IBK blocks and index sidecars
   -> compute lengths, SHA-256 identities, and Merkle commitments
   -> write an immutable generation
   -> validate every cross-artifact relation
   -> atomically replace CURRENT
```

Readers continue to use the preceding generation until the final activation
step. A failed build is not made current.

### 2.2 Query execution

The query path keeps reference semantics and physical access separate:

```text
SPARQL text
   -> parsed SPARQL algebra
   -> physical block and index selection
   -> verified range reads
   -> row and term decoding
   -> joins, filters, projection, and result formation
   -> comparison or refinement against the Lean SPARQL evaluator
```

The current on-disk path accelerates a growing subset of triple-pattern and
join shapes. Unsupported shapes require a complete fallback; they must not
produce a partial answer. Full storage-backed SPARQL coverage is a project
goal, not an alpha claim.

### 2.3 Updates, recovery, and compaction

SPARQL Update and other mutation interfaces may translate accepted operations
to durable delta batches. The storage protocol does not require bulk imports
to pass through SPARQL Update.

Each committed batch has a sequence and compaction epoch. Readers replay valid
batches after the active generation's compacted epoch. Compaction applies the
eligible history to a new immutable generation, validates it, records its
epoch, and activates it through `CURRENT`. This prevents a crash between base
publication and log maintenance from applying an update twice.

### 2.4 Block query workers

A Shardborough block query worker is a small executable over authenticated
block bytes. It is intended for use beside local files, PostgreSQL, TiKV,
object storage, browser storage, or a remote range service. The host provides
bytes and resource limits. The worker validates and decodes those bytes and
performs a typed physical operation. RDF semantics do not move into the
storage adapter.

Here, *worker* names an execution role. It does not require a JavaScript Web
Worker, an operating-system process, or a remote service. The browser example
runs the operation in the page's existing Lean WASM runtime; another host may
place the same operation in a thread or separate process.

The responsibilities are deliberately split:

```text
coordinator
  parse SPARQL; choose blocks, indexes and operations; combine fragments
       |
       v
block worker
  validate supplied bytes; execute a bounded scan or join fragment
       |
       v
result fragment
  typed rows or result bytes, counters, and evidence identities
```

The worker is not a second SPARQL implementation and is not necessarily a
SPARQL Protocol endpoint. A deployment may put parsing and planning in the
coordinator and send only a small physical program to workers. A self-contained
edge application may run the coordinator and workers in one native or WASM
process.

#### 2.4.1 Current diagnostic API

The Lean dispatch ABI currently exposes complete-artifact predicate scans:

```text
scanIBK2Predicate(ibk2Hex, predicateIri)
scanIBK3Predicate(ibk3Hex, predicateIri, blankNodeScope)
queryIBK3BlockSetPreview(blocksJson, blankNodeScope, sparql)
```

The IBK3 operation accepts three strings and returns a JSON envelope:

```json
{
  "ok": true,
  "format": "IBK3",
  "blankNodeScope": "source:example-2026-09-01",
  "rows": 3,
  "ntriples": "<s1> <p> <o1> .\n..."
}
```

Invalid hexadecimal text, an invalid predicate IRI, a failed IBK checksum,
bad row positions or term references, a malformed PTD1 dictionary, and a
non-predicate-local block are rejected. The operation uses the same Lean
decoder and scan definition in native and WASM builds. The current diagnostic
ABI also rejects a blank-node scope longer than 256 UTF-8 bytes.

`blankNodeScope` is mandatory because N-Triples blank-node labels are local to
an RDF document or dataset import unit. Blocks partitioned from the same unit
use the same scope, so a blank node described under several predicates keeps
one identity. Blocks from unrelated units use different scopes, so equal local
labels do not merge when result fragments are composed. The worker encodes the
scope to a grammar-safe prefix and applies it at every blank-node position.
The scope is an import identity, not an IBK artifact identity: using a
different scope for every predicate block would incorrectly split one source
blank node. Reusing a scope for unrelated imports would incorrectly merge
nodes. A production generation manifest must therefore commit the scope used
for each source partition rather than accepting an arbitrary value at query
time. The scope may span several named graphs when one imported RDF dataset
shares blank nodes across them; it is not mechanically the graph IRI. A
content digest is sufficient only when the publication profile also says that
repeated imports of those bytes share one blank-node allocation. Otherwise the
scope must include the import occurrence or equivalent provenance identity.

The current operation emits N-Triples and carries no graph-name field. It
therefore composes a default graph only. `blankNodeScope` preserves local node
identity; it is not a substitute for a `GraphId`. A dataset-aware worker and
future block layout must carry graph identity explicitly before this operation
can preserve named graphs.

The older two-argument IBK2 operation predates this rule and its N-Triples
output must be treated as a single-document fragment. Multi-block composition
uses the scoped IBK3 operation.

`queryIBK3BlockSetPreview(blocksJson, blankNodeScope, sparql)` composes a
small explicit set of complete IBK3 blocks — `blocksJson` is an array of
`[predicateIri, ibk3Hex]` pairs — and evaluates one SPARQL query over them
inside Lean, so no N-Triples text crosses the host boundary between decoding
and evaluation. It is a browser-preview operation, named so it is not
mistaken for the bounded protocol of section 2.4.2. Its limits bound INPUT
and OUTPUT, not intermediate work: at most eight blocks, eight MiB of
artifact bytes and 100,000 rows, checked against the hexadecimal length and
the 13-byte IBK3 header before any artifact is decoded; only a basic graph
pattern of at most four triple patterns, no `FROM`, `GROUP BY`, `HAVING` or
`VALUES`; and `SELECT`/`CONSTRUCT` require `LIMIT <= 1000`. A join of two
unbound patterns over thousands of rows a side is still evaluated in full by
the reference evaluator before `LIMIT` applies, and one blank-node scope
applies to the whole set. Every block must decode completely, and its
declared predicate must identify every row, or the operation is refused.

This API is useful for testing the execution boundary and for small browser
demos. Hexadecimal transport, complete-block decoding, and N-Triples output
copy the data and have no artifact or output-size limit. They are not the
production remote-worker protocol. The caller must also authenticate the
expected block identity: a self-consistent IBK3 file alone does not establish
that it belongs to the active generation.

The browser query operations (`queryDataset`, `datasetQuery`, and the
block-set preview) evaluate `SELECT` and `ASK` through the same optimized
Lean physical-plan path as the native host — `indexedDatasetBackend` with
`runSelectQueryBackendDataset` — and fall back to the reference evaluator
for any shape that path declines, so answers are never partial. A dataset
handle builds its indexes once when opened.

The native `l4block-id-v3-query` host has a broader, implemented path. It
parses SPARQL, opens the active SBM generation, checks committed artifacts,
uses SRI2/TLI1/OLI2 where the admitted query shape permits, merges durable
deltas, and evaluates the selected materialization through the Lean SPARQL
engine. It also has complete fallbacks for supported query forms. This native
host demonstrates the intended coordinator role; it is not yet packaged as a
network service.

#### 2.4.2 Bounded worker protocol target

The production boundary will use byte buffers or authenticated ranges and a
versioned typed request. Its logical shape is:

```text
request
  API version
  operation or validated PushIR program
  artifact identities and supplied byte ranges
  blank-node import scope committed by the generation
  snapshot / compaction epoch
  row, byte, memory and output limits

response
  success or typed failure
  row/result buffer
  bytes requested, bytes consumed and rows produced
  kernel, program and input identities
```

PushIR is the planned multi-operation language for this boundary. It is
separate from IBK block bytes and from SPARQL algebra. It will be typed,
versioned, deterministic and bounded, with operations such as range scan,
column load, exact ID comparison, revision filtering, sorted intersection,
projection, count and emit. It will not provide arbitrary recursion, network
access, dynamic code loading, or unrestricted memory access.

The protocol is backend-neutral. PostgreSQL may supply `bytea` values, TiKV
may supply values or fixed chunks, and a browser may supply `ArrayBuffer`
ranges from HTTP or OPFS. Each can run the same Lean-derived native or WASM
kernel. Backend adapters therefore need storage, identity, range and resource
control operations rather than their own RDF query engine.

Before an internet-facing worker profile is specified, it requires:

- a canonical binary request and response format with independent golden
  vectors;
- mandatory size, time, memory and output limits;
- SBM generation and artifact-identity binding before decode;
- authenticated range proofs where partial artifacts are supplied;
- precise PushIR validation and denotation-preservation statements;
- replay-safe snapshot and compaction-epoch handling;
- conformance tests across native and WASM kernels.

## 3. Deployment profiles

| Profile | Artifact host | Execution | Alpha status |
|---|---|---|---|
| Local | directory of files with positioned range reads | native Lean executable and thin C I/O boundary | primary implemented path |
| PostgreSQL | `bytea` values and metadata rows | coordinator or nearby worker using the same codecs | byte round-trip demonstrated; no Lean client adapter yet |
| TiKV | values or fixed-size chunks addressed by manifest keys | colocated or nearby worker | planned |
| Browser or edge | HTTP ranges, OPFS, or supplied buffers | Lean-derived WASM block kernel | complete-artifact IBK2/IBK3 scan ABI implemented; buffer/range protocol planned |
| Distributed | content-addressed blocks in one or more hosts | coordinator sends bounded physical work to native or WASM workers | architectural target |

The stable backend boundary is a manifest plus byte-range reads, not a second
backend-specific RDF model. PushIR can describe bounded work near storage,
but PushIR is not part of the block byte format.

## 4. Design requirements

1. **One physical object across hosts.** Local files, memory maps, PostgreSQL
   `bytea`, TiKV values, browser storage, native Lean, and WASM may host the
   same versioned bytes. A host supplies storage and positioned I/O; it does
   not redefine RDF identity or SPARQL results.
2. **Semantics remain above representation.** A block stores RDF terms and
   rows. It must not silently privilege RDFS, OWL, SHACL, ShEx, RIF, another
   rule language, Common Logic, IKL, or one application's ontology.
3. **Semantic acceleration is explicit.** A derived block or index may exploit
   a named semantic profile only when it is bound to the exact source,
   schema/rules, graph scope, trust policy, and derivation identity that make
   the optimization sound.
4. **Unknown or stale metadata means fallback.** Missing evidence may make a
   plan slower. It must not cause false negatives or silently broaden the
   requested entailment regime.
5. **Versioned meaning.** Existing magic/version pairs never acquire a new
   byte interpretation or denotation. A change of bytes or meaning requires a
   new version.
6. **Integrity precedes decoding.** Activated generations bind artifact
   lengths, SHA-256 identities, fixed-chunk Merkle roots, and role-specific
   sidecar relations before selective reads are trusted.
7. **Assertions and derivations remain distinguishable.** Physical
   duplication for locality is permitted, but query multiplicity and source
   provenance must not be inferred from duplicate storage rows.

## 5. Authority and terminology

The specification has three connected levels:

```text
RDF/SPARQL denotation and semantic-profile contracts
                         |
                         v
versioned Lean data types, encoders, decoders, validators and refinements
                         |
                         v
host realization: files / mmap / PostgreSQL / TiKV / OPFS / WASM buffers
```

- **Canonical bytes** means one admitted encoding for a stated physical
  value. It does not by itself mean canonical RDF dataset identity.
- **Canonical dataset identity** is a separate RDFC-1.0 or other explicitly
  named normalization-and-hash operation over a declared dataset scope.
- **Artifact identity** is the SHA-256 of exact stored bytes.
- **Term ID** is an execution identifier. Current IBK3 IDs are local to one
  artifact and are translated through its dictionary/TLI1 relation.
- **Graph identity** must distinguish the default graph from an RDF term used
  to name a graph. A normal term ID is not reserved as a default-graph
  sentinel in the target model.

## 6. Format registry

### 6.1 Primary blocks and dictionaries

| Name | Role | Current status | Executable definition |
|---|---|---|---|
| `BLK0` | Direct RDF-term transition block | superseded MVP format | [BlockWireV0.lean](https://github.com/danbri/factoidal/blob/claude/main/formal/lean4/L4Factoidal/Storage/BlockWireV0.lean) |
| `IBK1` | One dictionary plus fixed ID triples | readable prototype | [IndexedBlockWireV1.lean](https://github.com/danbri/factoidal/blob/claude/main/formal/lean4/L4Factoidal/Storage/IndexedBlockWireV1.lean) |
| `IBK2` | Predicate-selective segmented ID block | superseded; retained range-soundness results | [IndexedBlockWireV2.lean](https://github.com/danbri/factoidal/blob/claude/main/formal/lean4/L4Factoidal/Storage/IndexedBlockWireV2.lean) |
| `IBK3` | Current predicate-local fixed ID rows followed by an embedded pageable dictionary | current primary alpha block | [IndexedBlockWireV3.lean](https://github.com/danbri/factoidal/blob/claude/main/formal/lean4/L4Factoidal/Storage/IndexedBlockWireV3.lean) |
| `PTD1` | IBK3-local ID to RDF term, split into independently readable pages | current embedded dictionary | [PagedTermDictionary.lean](https://github.com/danbri/factoidal/blob/claude/main/formal/lean4/L4Factoidal/Storage/PagedTermDictionary.lean) |

IBK3 contains triples and requires one predicate per artifact. Its current
term codec accepts IRIs, blank nodes, and RDF 1.1-style literals, but refuses
RDF 1.2 triple terms and directional literals. Current IDs and row counts use
32-bit wire fields. These are explicit alpha limits.

The target full RDF-store model is quad-aware. Current IBK3/SBM6 is
default-graph-oriented and does not define the final `GraphId` layout.
`Manifest.sourceIdentity` is not a substitute for graph identity.

### 6.2 Index sidecars

| Name | Relation | Status |
|---|---|---|
| [`SRI1`](https://github.com/danbri/factoidal/blob/claude/main/formal/lean4/L4Factoidal/Storage/SubjectRowIndexWire.lean) | local subject ID to row offsets | flat readable predecessor |
| [`SRI2`](https://github.com/danbri/factoidal/blob/claude/main/formal/lean4/L4Factoidal/Storage/SubjectRowIndexWireV2.lean) | pageable, target-bound local ID to row offsets | current generic postings codec used in the subject role |
| [`TLI1`](https://github.com/danbri/factoidal/blob/claude/main/formal/lean4/L4Factoidal/Storage/TermLocalIndexWire.lean) | canonical RDF-term bytes to one target IBK3 local ID | current cross-artifact term bridge |
| `OLI2` | local object ID to row offsets | current SBM6 object role, encoded with the generic SRI2 postings codec |

The role of OLI2 is not inferred from its bytes. SBM6 places the artifact in
the object-index field, and activation recomputes the canonical object-to-row
relation from the target IBK3 block. SRI2 and OLI2 therefore share a codec but
not a semantic role.

### 6.3 Manifests and range integrity

| Name | Adds |
|---|---|
| `SBM0` | ordered immutable artifact entries |
| `SBM1` | fixed-chunk Merkle commitments |
| `SBM2` | multiple bounded blocks for one predicate |
| `SBM3` | mandatory SRI1 subject indexes |
| `SBM4` | TLI1 term indexes |
| `SBM5` | pageable SRI2 replacing SRI1 |
| `SBM6` | mandatory object-role OLI2 indexes |

The current manifest structure records a wire version, source identity,
term-registry version, physical-layout label, and ordered predicate/artifact
entries. Each current artifact reference records a safe relative key, byte
extent, SHA-256, and fixed-chunk Merkle reference.

The companion `.merkle` file is currently the raw concatenation of 32-byte
leaf hashes in chunk order. It has no independent magic/version. Its authority
comes only from rebuilding its root and matching the root committed by SBM;
activation additionally checks that the leaf sequence was derived from the
same complete bytes whose SHA-256 is in the manifest. A future change to this
sidecar requires explicit framing rather than silently changing this layout.

Merkle admission of selected ranges establishes that returned bytes belong to
the committed artifact. It does not establish that an index contains every
required posting. A reader may claim complete query results only for a
generation that passed full activation, including complete block decoding and
recomputation of each required sidecar relation. Direct selective reads from
merely Merkle-committed files can be sound without being complete.

### 6.4 Durable update and generation protocol

| Name | Role |
|---|---|
| `DLE1` | one framed and checksummed durable delta operation |
| `DLB1` | sequenced, epoch-stamped, all-or-nothing batch of DLE1 operations |
| `DLOG` | append-only header and DLB1 history |
| `CEP1` | compacted epoch already folded into an immutable generation |
| `CURRENT` | atomically replaced UTF-8 safe child-generation name |

The DLE1/DLB1 checksum detects framing corruption and torn append tails; it is
not a cryptographic identity. A writer validates the existing committed
history, stamps new batches after the compacted epoch, appends under the host
locking/fsync boundary, and never rewrites the immutable base in place.
Compaction builds a fresh generation, writes its CEP1 marker, verifies it, and
only then atomically replaces `CURRENT`. Recovery replays exactly the valid
history suffix after CEP1.

### 6.5 Related formats, not redefined here

- **COTTAS v1** is the earlier Parquet-based quad store and remains a useful
  import/export, compatibility, and differential path. Its detailed contract
  is the [COTTAS v1 format](cottas-format-v1.md), and its operational sidecars
  are catalogued in the
  [disk-storage-format skill](https://github.com/danbri/factoidal/blob/claude/main/skills/disk-storage-format/SKILL.md).
- **HDT** is an external RDF format with its own specification. Factoidal's
  Lean HDT implementation is separate; IBK does not implement the HDT format.
- **[RDFC-1.0 canonical N-Quads and hashes](https://www.w3.org/TR/rdf-canon/)**
  identify declared RDF dataset content. They may identify a source or derived
  generation but are not the IBK byte layout.
- **S-expressions, physical plans, PushIR, execution records, and proof
  certificates** are separately typed symbolic/execution languages. They may
  refer to stored artifacts; they are not block bytes.

## 7. Semantic neutrality and semantic context

The base row denotation is RDF data, not “RDFS data”, “OWL data”, or “SHACL
data”. Schema and rules are themselves data or separately identified programs.
This permits the same asserted generation to be queried under simple RDF,
RDF/RDFS, an OWL profile, a SPARQL entailment regime, a rule system, or no
additional semantics.

SBM6 does **not yet** encode enough information to make derived semantic
artifacts self-describing. A successor manifest must be extensible by
content-addressed, typed references rather than by a closed enumeration of
favoured standards. At minimum it must be able to identify:

```text
artifact semantic role
    asserted RDF | derived RDF | schema | ruleset | shapes |
    validation report | derivation/evidence | application-defined role IRI

source dataset and named-graph set
RDF term-identity/canonicalization profile
semantic or entailment profile IRI and version
exact schema/rules/program artifact hashes
graph and dataset scoping policy
publisher/voice/authority boundary
trust-policy identity
derivation time and source generation identities
implementation/program identity and evidence reference
```

The existing `sourceIdentity` and `termRegistryVersion` fields are the starting
points for source and term-identity context. A successor should extend their
contract rather than introduce parallel identities.

An IRI names the language/profile; a digest fixes the exact artifact or
program. This accommodates, without granting any one of them storage-level
privilege:

- [RDF](https://www.w3.org/TR/rdf11-mt/) and
  [RDFS](https://www.w3.org/TR/rdf-schema/) semantics, including experimental
  RDFS-Plus profiles;
- [OWL profiles](https://www.w3.org/TR/owl2-profiles/) and
  [SPARQL entailment regimes](https://www.w3.org/TR/sparql11-entailment/);
- [RIF](https://www.w3.org/TR/rif-core/) and other rule languages such as
  Datalog, N3 rules, SPARQL rule forms, SHACL Rules, application rules, and
  typed Lean rule programs;
- [SHACL](https://www.w3.org/TR/shacl/), SHACL extensions, and
  [ShEx](https://shex.io/shex-semantics/) validation artifacts;
- Common Logic and IKL propositions about datasets, programs, executions,
  provenance, and assurance.

SHACL and ShEx validation are not silently treated as entailment. A validator
may produce a report, evidence, or a separately named derived graph. Likewise,
Common Logic/IKL may describe and make claims about a computation without
being required by the storage execution kernel.

Asserted and derived triples should normally occupy separately identifiable
graph/artifact layers. A client requesting simple semantics must be able to
exclude derived closure data. A client accepting a named profile may select a
validated materialized closure or run the profile on demand.

## 8. Optional semantic access summaries

This section describes optional derived indexes. SBM6 does not require them,
and no wire identifiers have been assigned for them.

### 8.1 Current exact-predicate behaviour

Current Shardborough selection is exact-predicate only. A constant query
predicate selects manifest entries whose predicate IRI is exactly equal. The
Lean RDFS and OWL layers implement and reason about `rdfs:subPropertyOf`
(`rdfs5`, `rdfs7`, and related OWL RL rules), but no current SBM6 sidecar or
IBK3 physical planner turns a superproperty query into subordinate predicate
block reads.

Consequently, today a query for `dc:description` under an RDFS entailment
regime must first use the logical materialization/closure route or another
complete fallback. The fast exact-predicate path alone would be incomplete if
it ignored trusted declarations such as:

```turtle
@prefix dc: <http://purl.org/dc/elements/1.1/> .
@prefix ex: <http://example.org/> .
@prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .

ex:shortDescription rdfs:subPropertyOf dc:description .
```

### 8.2 Predicate-entailment map

One proposed acceleration is a separately committed derived
artifact, provisionally called a **predicate-entailment map**; no wire magic is
allocated by this draft. For a fixed semantic context it maps a queried
superproperty to the exact predicate partitions whose rows can contribute:

```text
(source generation hash,
 schema/rules hash,
 entailment-profile identity,
 graph-scope policy,
 trust-policy hash)
        + queried predicate q
        -> admitted source predicates {p | profile licenses p <= q}
```

For plain/simple SPARQL the candidate set is `{q}`. Under an admitted RDFS
profile it may include the reflexive-transitive `rdfs:subPropertyOf` closure
below `q`. An OWL profile may additionally license equivalent-property
relationships, but only if the profile's proved semantics says so.

The physical planner may then either:

1. scan and merge the listed exact-predicate blocks at query time; or
2. open a content-addressed materialized superproperty block derived from the
   same source and semantic-context identities.

The earlier F* [OWL query rewriter](https://github.com/danbri/factoidal/blob/claude/main/formal/fstar/OWL.QueryRewrite.fst)
implements superproperty access as a logical `UNION` rewrite. Its documented
row-multiplication problem is one reason inferred triples must be deduplicated
before SPARQL solution multiplicity is calculated; see
[issue #236](https://github.com/danbri/factoidal/issues/236).

The logical denotation is a graph set. If identical `(subject, object)` pairs
reach the queried superproperty through multiple source predicates in the same
graph, the inferred superproperty triple exists once. A physical union must
therefore deduplicate at the inferred-triple boundary before exposing SPARQL
solution multiplicity. In a quad layout, the deduplication key includes graph
identity. Storage duplication must not become duplicate logical answers.

The map does not establish schema authority. It is usable only when every
context identity matches the query's requested regime and admitted trust/graph
boundary. A missing, stale, conflicting, or untrusted map falls back to
complete evaluation.

### 8.3 Limits of predicate expansion

Not every property rule reduces to a union of predicate blocks:

- `owl:inverseOf` also swaps subject and object access roles;
- transitive properties require reachability;
- property chains require joins;
- `owl:sameAs` may affect term identity in the semantic result without
  changing raw RDF term identity;
- non-monotonic or scoped rules may invalidate simple closure reuse.

These need distinct typed physical operators or separately materialized,
profile-bound derived artifacts. They must not be represented as one
`subPropertyOf` bitmap or as global TermId allocation.

### 8.4 Predicate-map proof obligations

Before the predicate-entailment map becomes an exact fast path, Lean should
establish, for each admitted profile:

1. every selected subordinate predicate is licensed to entail the queried
   predicate under the named context (soundness);
2. every source predicate capable of contributing is selected when the path
   claims completeness (no false-negative pruning);
3. verified block rows denote the exact predicate fragments named by the map;
4. merge plus inferred-triple deduplication gives the same solution bag as the
   reference Lean evaluator under that entailment regime.

The existing RDFS `rdfs5`/`rdfs7` definitions and soundness results are the
semantic starting point. The missing work is the persisted context/index
contract and its planner refinement. This work is tracked in
[issue #636](https://github.com/danbri/factoidal/issues/636).

### 8.5 Endpoint-type summaries

A predicate block may have a small derived summary of the classes associated
with its subject and object endpoints. The summary is intended to reject
irrelevant blocks before their row and dictionary pages are fetched.

For a role, class, and threshold, the summarized claim has this form:

```text
fraction of endpoints in role R having type C under context K >= threshold Q
```

The endpoint population must be stated. Useful choices include distinct RDF
terms, distinct RDF resources, and row occurrences; they give different
fractions. Subject and object roles are kept separate.

A compact representation may use one Bloom filter per role and threshold, or
one filter with domain-separated keys such as:

```text
at_least_1:subject:<canonical class key>
at_least_half:subject:<canonical class key>
all:object:<canonical class key>
```

Other quantized thresholds are allowed. Each version fixes its thresholds,
hash functions, key encoding, bit count, and claimed false-positive rate.

The interpretation follows the Bloom filter's one-sided error:

- a negative `at_least_1` result proves that the block cannot satisfy the
  corresponding type join, provided the summary was completely constructed;
- a negative result at a higher threshold supplies a sound upper bound for
  join ordering and bandwidth estimates;
- a positive result is only a candidate claim. It may guide planning but does
  not prove the threshold;
- in particular, a positive `all` result cannot by itself justify removing a
  type join. That requires an exact set, a checked certificate, or subsequent
  verification.

The indexed type relation may contain asserted types only, or it may include
materialized supertypes. A summary containing supertypes must bind the exact
source generation, named-graph scope, schema or rule-set digest, entailment
profile, trust policy, and endpoint-population rule used to construct it. This
permits a selected common vocabulary to be projected from many named graphs
without making that vocabulary part of the base block format.

Class keys may be canonical RDF-term keys or entries in a content-addressed
vocabulary dictionary. A small exact bitmap for a common vocabulary can be
combined with a Bloom filter for the long tail. Local IBK3 IDs are suitable
only when the summary is bound to that exact block.

The summary belongs in the manifest or in a content-addressed sidecar so it
can be read before the block. No wire magic is allocated by this draft. An
exact pruning path requires Lean results for complete construction, absence
soundness, context matching, and equivalence with the unpruned evaluator.

## 9. Named graphs, provenance, and trust

Semantic profiles are scoped to a dataset, not presumed global. A schema
triple in one untrusted Web page must not automatically govern every graph in
a corpus. The target quad manifest must preserve:

- default versus named graph identity;
- site, publisher, user, extractor, and snapshot voice where supplied;
- which graph set provided schema/rule premises;
- whether a derived view flattens graphs for execution while retaining the
  source graph relation;
- retraction and recomputation dependencies.

Publisher hints—including property characteristics, entity boundaries, and
identifier assignments—are provenance-bearing inputs. They become physical
accelerators only after validation under an explicit trust/profile boundary.
The same rule applies to inverse-functional-property identity candidates and
subproperty maps.

## 10. Alpha compatibility and beta gates

The current family is suitable for an experimental MVP/alpha in which data can
be repacked after a version bump. It is not yet a stable external storage
standard. Beta requires at least:

1. complete field tables and portable golden vectors in this specification;
2. general round-trip or denotation-preservation theorems for IBK3, PTD1,
   SRI2/OLI2, TLI1, SBM6, and Merkle range admission;
3. a proved bridge from verified selected rows to the reference Lean SPARQL
   evaluator;
4. a settled RDF 1.2 term codec and tagged GraphId/quad layout, and a
   generation manifest that commits the blank-node scope of each source
   partition instead of accepting a scope at query time (section 2.4.1);
5. explicit semantic-context and provenance references for derived artifacts;
6. identical-byte interoperability in at least two host paths;
7. migration and feature-negotiation rules, including unknown-version refusal;
8. crash, corruption, fuzz, and update/compaction regression coverage stated
   by format and version;
9. a generation pointer that commits the selected manifest identity rather
   than only a directory name;
10. a portable activation record or equivalent host contract distinguishing a
    fully validated generation from files that have only passed range-level
    integrity checks.

### 10.1 Gate 2 progress (2026-09-02)

Kernel-checked round-trip theorems now exist for the complete-artifact codecs
of the current family. Each depends only on the three standard Lean axioms.

| Codec | Theorem | Module | Admission hypotheses |
| --- | --- | --- | --- |
| Term codec (`serializeTerm` / `parseTerm`) | `parseTerm_serializeTerm` | [`Storage/TermCodecTheorems.lean`](https://github.com/danbri/factoidal/blob/claude/main/formal/lean4/L4Factoidal/Storage/TermCodecTheorems.lean) | `termSupported` (no base direction, no triple term); `termFitsU32` (every length-prefixed string below the u32 limit) |
| PTD1 | `decode?_encode?` | [`Storage/PagedTermDictionaryTheorems.lean`](https://github.com/danbri/factoidal/blob/claude/main/formal/lean4/L4Factoidal/Storage/PagedTermDictionaryTheorems.lean) | none beyond `encode? terms = some bytes`: `supported` checks both term conditions |
| IBK3 | `decode_encode?`, `denotes_decode_encode?` | [`Storage/IndexedBlockWireV3Theorems.lean`](https://github.com/danbri/factoidal/blob/claude/main/formal/lean4/L4Factoidal/Storage/IndexedBlockWireV3Theorems.lean) | none beyond `encode? block = some bytes`: `supported` runs the decoder's own `fromParts?` admission |

Findings recorded by these proofs:

- `termFitsU32` was a real admission condition that `encode?` did not check:
  the dictionary encoder calls the total term encoder, which writes a
  truncated u32 length prefix for a string of 2^32 bytes or more. The guard
  is now in `PagedTermDictionary.supported` (`termFitsU32b`), so the
  encoder refuses such a term before it reaches the wire.
- `IndexedBlock.fromParts?` refuses a dictionary with repeated terms and rows
  whose IDs do not resolve to a subject, a predicate IRI and an object.
  `IndexedBlockWireV3.supported` now runs that same test, so the encoder
  refuses exactly the blocks the decoder would refuse.
- `IndexedBlockWireV3.orderedRows?` takes a direct path when row positions are
  already `0, 1, 2, ...`, which is what the encoder emits, and sorts only
  otherwise. The answer is the same for every input; the direct path is what
  the proof reasons about, because Lean core has no theorems about
  `Array.qsort`.
- The IBK3 theorem is stated on the two array fields and on the block
  denotation, not on block equality: `IndexedBlock.Block` also carries two
  hash maps.

Still open under gate 2: SRI2/OLI2, TLI1, SBM6 and Merkle range admission.

## 11. Implementation map and supporting design records

- Current codecs and pure validators:
  [formal/lean4/L4Factoidal/Storage/](https://github.com/danbri/factoidal/tree/claude/main/formal/lean4/L4Factoidal/Storage)
- Host I/O, publication, activation, compaction and query probes:
  [formal/lean4/Harness/](https://github.com/danbri/factoidal/tree/claude/main/formal/lean4/Harness)
- Native/WASM block-worker operations and their dispatch ABI:
  [formal/lean4/Wasm/Ops/Block.lean](https://github.com/danbri/factoidal/blob/claude/main/formal/lean4/Wasm/Ops/Block.lean)
  and
  [formal/lean4/Wasm/Dispatch.lean](https://github.com/danbri/factoidal/blob/claude/main/formal/lean4/Wasm/Dispatch.lean)
- Block-worker implementation milestone:
  https://github.com/danbri/factoidal/issues/637
- SPARQL reference semantics and refinements:
  [formal/lean4/L4Factoidal/SPARQL/](https://github.com/danbri/factoidal/tree/claude/main/formal/lean4/L4Factoidal/SPARQL)
- RDFS and RDFS-Plus semantics:
  [formal/lean4/L4Factoidal/RDFS/](https://github.com/danbri/factoidal/tree/claude/main/formal/lean4/L4Factoidal/RDFS)
- OWL and rule implementations:
  [formal/lean4/L4Factoidal/OWL/](https://github.com/danbri/factoidal/tree/claude/main/formal/lean4/L4Factoidal/OWL)
  and
  [formal/lean4/L4Factoidal/RIF/](https://github.com/danbri/factoidal/tree/claude/main/formal/lean4/L4Factoidal/RIF)
- Common Logic/IKL:
  [formal/lean4/L4Factoidal/CL/](https://github.com/danbri/factoidal/tree/claude/main/formal/lean4/L4Factoidal/CL)
- Symbolic execution architecture:
  [Block engine, part 3](2026-08-blockengine_part3.md)
- Web working sets, graph voice, RDFC, publisher hints, and identity profiles:
  [Web-corpus working sets](20260830-web-corpus-working-sets.md)
- Current physical-format chronology and measurements:
  [IBK3 decode hot path](20260831-ibk3-decode-hot-path.md)

## 12. Design authorship

The Shardborough architecture and the design requirements in this document are
by Dan Brickley. Implementation and editorial contributions are recorded in
the Factoidal repository history.
