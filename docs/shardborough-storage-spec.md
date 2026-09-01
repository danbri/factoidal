# Shardborough storage and execution artifact specification

**Status:** alpha umbrella draft 0.1

**Date:** 2026-09-01

**Scope:** the Lean 4 block, index, manifest, integrity, update, compaction,
activation, and semantic-context formats used by the Factoidal block engine.

This is the single entry point for the format family. It is not a W3C
document, Submission, Recommendation, conformance claim, or compatibility
claim about an external RDF store. W3C and other specifications are cited only
where they define the RDF/SPARQL semantics or supply test material.

During alpha, the cited Lean definitions are the executable byte-layout source
of truth. A disagreement between this document and those definitions is a
defect to repair, not permission for a reader to guess. Before beta, this
document must contain complete field tables and portable golden vectors so an
independent reader need not reverse-engineer Lean source.

## 1. Design requirements

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

## 2. Authority and terminology

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

## 3. Format registry

### 3.1 Primary blocks and dictionaries

| Name | Role | Current status | Executable definition |
|---|---|---|---|
| `BLK0` | Direct RDF-term transition block | readable MVP lineage; not the current scalable layout | `formal/lean4/L4Factoidal/Storage/BlockWireV0.lean` |
| `IBK1` | One dictionary plus fixed ID triples | readable prototype | `Storage/IndexedBlockWireV1.lean` |
| `IBK2` | Predicate-selective segmented ID block | readable predecessor with range soundness results | `Storage/IndexedBlockWireV2.lean` |
| `IBK3` | Current predicate-local fixed ID rows followed by an embedded pageable dictionary | current primary alpha block | `Storage/IndexedBlockWireV3.lean` |
| `PTD1` | IBK3-local ID to RDF term, split into independently readable pages | current embedded dictionary | `Storage/PagedTermDictionary.lean` |

IBK3 contains triples and requires one predicate per artifact. Its current
term codec accepts IRIs, blank nodes, and RDF 1.1-style literals, but refuses
RDF 1.2 triple terms and directional literals. Current IDs and row counts use
32-bit wire fields. These are explicit alpha limits.

The target full RDF-store model is quad-aware. Current IBK3/SBM6 is a
default-graph-oriented implementation rung, not the final `GraphId` layout.
`Manifest.sourceIdentity` is not a substitute for graph identity.

### 3.2 Index sidecars

| Name | Relation | Status |
|---|---|---|
| `SRI1` | local subject ID to row offsets | flat readable predecessor |
| `SRI2` | pageable, target-bound local ID to row offsets | current generic postings codec used in the subject role |
| `TLI1` | canonical RDF-term bytes to one target IBK3 local ID | current cross-artifact term bridge |
| `OLI2` | local object ID to row offsets | current SBM6 object role, encoded with the generic SRI2 postings codec |

The role of OLI2 is not inferred from its bytes. SBM6 places the artifact in
the object-index field, and activation recomputes the canonical object-to-row
relation from the target IBK3 block. SRI2 and OLI2 therefore share a codec but
not a semantic role.

### 3.3 Manifests and range integrity

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

### 3.4 Durable update and generation protocol

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

### 3.5 Related formats, not redefined here

- **COTTAS v1** is the earlier Parquet-based quad store and remains a useful
  import/export, compatibility, and differential path. Its detailed contract
  is `docs/cottas-format-v1.md` and its operational sidecars are catalogued in
  `skills/disk-storage-format/SKILL.md`.
- **HDT** is an external RDF format with its own specification. Factoidal's
  Lean HDT work is reusable implementation lineage, not evidence that IBK is
  HDT-compatible.
- **RDFC-1.0 canonical N-Quads and hashes** identify declared RDF dataset
  content. They may identify a source or derived generation but are not the
  IBK byte layout.
- **S-expressions, physical plans, PushIR, execution records, and proof
  certificates** are separately typed symbolic/execution languages. They may
  refer to stored artifacts; they are not block bytes.

## 4. Semantic neutrality and semantic context

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

An IRI names the language/profile; a digest fixes the exact artifact or
program. This accommodates, without granting any one of them storage-level
privilege:

- RDF and RDFS semantics, including experimental RDFS-Plus profiles;
- OWL profiles and SPARQL entailment regimes;
- RIF and other rule languages such as Datalog, N3 rules, SPARQL rule forms,
  SHACL Rules, application rules, and typed Lean rule programs;
- SHACL, SHACL extensions, and ShEx validation artifacts;
- Common Logic and IKL propositions about datasets, programs, executions,
  provenance, and assurance.

SHACL and ShEx validation are not silently treated as entailment. A validator
may produce a report, evidence, or a separately named derived graph. Likewise,
Common Logic/IKL may describe and make claims about a computation without
being loaded into the block-core hot path.

Asserted and derived triples should normally occupy separately identifiable
graph/artifact layers. A client requesting simple semantics must be able to
exclude derived closure data. A client accepting a named profile may select a
validated materialized closure or run the profile on demand.

## 5. Schema-aware predicate access

### 5.1 Current implementation

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

### 5.2 Proposed predicate-entailment map

The first storage acceleration should be a separately committed derived
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

The logical denotation is a graph set. If identical `(subject, object)` pairs
reach the queried superproperty through multiple source predicates in the same
graph, the inferred superproperty triple exists once. A physical union must
therefore deduplicate at the inferred-triple boundary before exposing SPARQL
solution multiplicity. In a quad layout, the deduplication key includes graph
identity. Storage duplication must not become duplicate logical answers.

This map is an acceleration certificate, not an authority to believe schema.
It is usable only when every context identity matches the query's requested
regime and admitted trust/graph boundary. A missing, stale, conflicting, or
untrusted map falls back to complete evaluation.

### 5.3 Limits of predicate expansion

Not every property rule reduces to a union of predicate blocks:

- `owl:inverseOf` also swaps subject and object access roles;
- transitive properties require reachability;
- property chains require joins;
- `owl:sameAs` may affect term identity in the semantic result without
  changing raw RDF term identity;
- non-monotonic or scoped rules may invalidate simple closure reuse.

These need distinct typed physical operators or separately materialized,
profile-bound derived artifacts. They must not be smuggled into one
`subPropertyOf` bitmap or into global TermId allocation.

### 5.4 Proof obligations

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

## 6. Named graphs, provenance, and trust

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

## 7. Alpha compatibility and beta gates

The current family is suitable for an experimental MVP/alpha in which data can
be repacked after a version bump. It is not yet a stable external storage
standard. Beta requires at least:

1. complete field tables and portable golden vectors in this specification;
2. general round-trip or denotation-preservation theorems for IBK3, PTD1,
   SRI2/OLI2, TLI1, SBM6, and Merkle range admission;
3. a proved bridge from verified selected rows to the reference Lean SPARQL
   evaluator;
4. a settled RDF 1.2 term codec and tagged GraphId/quad layout;
5. explicit semantic-context and provenance references for derived artifacts;
6. identical-byte interoperability in at least two host paths;
7. migration and feature-negotiation rules, including unknown-version refusal;
8. crash, corruption, fuzz, and update/compaction regression coverage stated
   by format and version.

## 8. Implementation map and supporting design records

- Current codecs and pure validators: `formal/lean4/L4Factoidal/Storage/`
- Host I/O, publication, activation, compaction and query probes:
  `formal/lean4/Harness/`
- SPARQL reference semantics and refinements:
  `formal/lean4/L4Factoidal/SPARQL/`
- RDFS and RDFS-Plus semantics: `formal/lean4/L4Factoidal/RDFS/`
- OWL and rule implementations: `formal/lean4/L4Factoidal/OWL/` and
  `formal/lean4/L4Factoidal/RIF/`
- Common Logic/IKL: `formal/lean4/L4Factoidal/CL/`
- Symbolic execution architecture: `docs/2026-08-blockengine_part3.md`
- Web working sets, graph voice, RDFC, publisher hints, and identity profiles:
  `docs/20260830-web-corpus-working-sets.md`
- Current physical-format chronology and measurements:
  `docs/20260831-ibk3-decode-hot-path.md`

## 9. Design provenance

The open semantic-profile architecture, graph/voice trust scoping,
publisher-assisted identity design, and schema-driven predicate-block
selection recorded here derive from Dan Brickley's Factoidal design sessions
of 2026-08-30 through 2026-09-01. Codex consolidated those requirements with
the landed Lean implementation into this umbrella draft. This records project
provenance and does not itself make a legal conclusion about intellectual
property rights.
