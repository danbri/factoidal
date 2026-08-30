# Web corpus working sets and derived RDF blocks — 2026-08-30

## Design provenance and attribution

The architectural proposals in this note were supplied by **Dan Brickley** in
the Factoidal working session dated 2026-08-30.  They include the Web-scale
crawl/named-graph working-set model; modest warm composition of many prepared
graphs; decentralized numeric IDs; reusable merged/resorted derived blocks;
the distinction between page graphs and site/user/product/offer views;
assertion-plus-evidence deduplication; RDFC-1.0 as a derivation boundary; and
identity-neighbourhood-aware partitioning with publisher hints.  Codex
recorded, organized, and elaborated the proposals in this repository.

This is contemporaneous project provenance, not a legal conclusion about
ownership, inventorship, patentability, copyright, or contractual rights.

## Architectural direction captured from design discussion

The target is a Web-scale collection of immutable crawl/extraction snapshots,
where a named graph commonly corresponds to a page but must not be treated as
the sole useful knowledge-graph boundary.  A site can contribute both
site-authored and user-attributed material; an e-commerce page can combine
site-wide organisation facts, product facts, offer facts, and page-local
presentation/extraction observations.

The physical system must therefore support both page provenance and derived,
non-page-shaped views such as all offers for a product, all organisation facts
for a site, or a selected cross-source authority neighbourhood.

## Cold source blocks, modest warm state

Many independently prepared named graphs and their blocks should be composable
within milliseconds without fully decoding every graph.  Warm state means
manifests, graph/block directories, common-vocabulary dictionary pages,
workload statistics/sketches, and recently used mapped pages — not a resident
parsed RDF graph per crawl page.

When selected blocks already share compatible numeric term IDs, joins require
no semantic ID reconciliation.  They can still cost many manifest lookups,
small reads, and a k-way merge of separately sorted streams.  Repeatedly used
graph groups should therefore be eligible for content-addressed derived blocks
whose rows are globally resorted for their workload (for example `PSOG`,
`SPOG`, `OSPG`, or `GSPO`).

Derived blocks should normally retain `graphId` as a quad column.  A flattened
union is a declared view over those blocks, not an irreversible loss of named
graph identity.  This retains `GRAPH` semantics, source trust, retraction, and
provenance while permitting union-like execution.

## Assertion/evidence separation

Derived mini-KGs should deduplicate compatible assertion content without
erasing evidence:

```text
canonical assertion (s, p, o)
        <- asserted-in / observed-in -> page graph, snapshot, extractor, voice role
```

Repeated equivalent site/product assertions can then occupy one execution row
with multiple evidence links.  Context-sensitive or contradictory claims stay
distinct via their assertion/evidence records.  This is the right model for
site voice versus user voice and for site-wide versus offer/page-local facts.

## IDs

Canonical RDF term identity remains the semantic ground truth.  Compact IDs
are execution keys.  Publisher-announced scoped numeric IDs (for common
vocabularies, controlled identifiers, or datasets) are welcome acceleration
certificates with issuer, namespace and version provenance; they are not
unqualified global RDF identity.  A practical representation admits
well-known registry IDs, issuer-scoped IDs, and content-derived fallback IDs
behind one `TermRef`/dictionary contract.

## RDFC-1.0 boundary

Use the existing/formal RDFC-1.0 work at immutable ingestion and derivation
boundaries: canonicalize a declared RDF dataset scope, preserve canonical
N-Quads and a digest, and record source/derivation identity.  This supports
isomorphism-aware comparison, signatures, change detection, and reproducible
derived working-set keys.

Do not put RDFC-1.0 on the hot block scan path.  In particular, blank-node
canonicalization has graph-wide and potentially adversarially costly behaviour.
Runtime blocks use established compact IDs and sorted layouts after the
canonicalization/assurance step.

## Partitioning must respect identity neighbourhoods

Block boundaries must not be a rigid byte, character, or quad count.  A
payload block may contain five execution quads while its manifest records a
larger declared identity/canonicalization neighbourhood used to establish the
term references in those quads.  This is particularly important for blank
nodes and richly described entities: splitting away all identifying context can
make canonicalization and entity reconciliation unstable or needlessly
expensive.

The required distinction is:

```text
payload quads                 -- scanned by the physical operator
identity neighbourhood        -- bounded contextual evidence used at derivation
assertion/evidence links      -- provenance and duplicate observations
```

Term identity itself remains stable and is not recomputed per block.  The
neighbourhood yields a checked mapping from source terms/blank nodes to
canonical and compact IDs at ingest/derivation time; runtime blocks carry the
resulting IDs plus an artifact reference to the evidence that established
them.

Publisher partition hints should be accepted as advisory, provenance-bearing
input: entity roots, record boundaries, blank-node closure groups, stable
Skolem IRIs, and safe co-location groups.  The importer must validate bounds
and may enlarge a declared neighbourhood or reject a malformed one.  This
allows a publisher to keep an entity description together without making an
untrusted page author control execution layout.

`owl:FunctionalProperty` and `owl:InverseFunctionalProperty` statements are
logical evidence, not licence to silently merge arbitrary Web terms.  They may
inform a separately named reconciliation/entailment profile with explicit
scope, source trust, time/version, and explanation.  Physical partitioning
should retain the relevant declaration and supporting neighbourhood together
where practical, but never detach it and then claim unconditional identity.

Duplication is permitted at the physical/evidence level when it improves
locality: a context quad or entity neighbourhood can be present in several
derived blocks.  Canonical assertion identity and artifact provenance ensure
this does not become duplicated logical content or double-counted query
results.

## Follow-on implementation work

1. Define the canonical predicate-shard manifest, including row-order and
   integrity contracts.
2. Generalise it to a quad/block manifest with `graphId` and provenance links.
3. Specify content-addressed derived working-set manifests from source artifact
   hashes, selection policy, canonicalization/ID-registry version, and layout.
4. Build a bounded crawl/YAGO-style corpus outside the source repository in
   `factoidal-builds`, retaining only provenance, commands, queries and result
   manifests here.

## Landed first manifest boundary

The first executable manifestation of this direction is `SBM0`, a deliberately
small Shardborough manifest format in
`formal/lean4/L4Factoidal/Storage/ShardManifest.lean`.  It names an ordered
set of predicate-local IBK2 artifacts, each with a relative key, byte length,
SHA-256 digest and row count, together with source identity, term-registry
version and layout label.

`SBM0` has strict Lean `encode?` and `decode?` functions.  The decoder rejects
bad magic/version, malformed UTF-8 or predicate IRI, truncated fields,
incorrect digest width, trailing bytes and structurally invalid manifests.
This is a host-neutral control plane: an artifact key may later resolve to a
local file/range, PostgreSQL `bytea`, a TiKV value, browser OPFS, or object
storage.  It is not yet a general graph/quad manifest or a Merkle tree; those
belong in the next layout versions once the checked child-artifact opening path
exists.

The next increment landed that opening path and the reference local host
vertical.  `ShardManifest.openStore?` takes an injected `ArtifactKey →
Option ByteArray` reader, checks each child's listed byte length and SHA-256,
then accepts it only if `IndexedBlockWireV2.open?` accepts its framing,
dictionary, directory and checksum.  Its `readOps` is the established Lean
SPARQL backend capability.  `l4block-shard-pack` now writes `manifest.sbm0`
as well as its TSV, while `l4block-shard-query DIR --query SELECT...` is the
first local-file host harness.

Its 2026-08-30 smoke used the 77-triple music Turtle fixture.  A parsed,
two-predicate join with a filter and `ORDER BY` returned the three Radiohead
albums via seven verified child blocks.  The eager opener was deliberately a
correctness reference. The local query host now adds a conservative first
lazy-selection step for ordinary parsed SPARQL: when the pattern is a native
BGP/join/union/minus composition and every triple pattern has a constant IRI
predicate, it reads, hash-verifies and opens only the corresponding predicate
artifacts. Its status line reports `open-mode=predicate-selective(n)` and
`artifact-bytes=loaded/total`. A deliberately small native FILTER subset
(constants, variables, comparisons, boolean logic and arithmetic) also retains
that path: it depends only on each solution mapping, not the active graph. The
PostgreSQL smoke's `FILTER(?band = ex:radiohead)` consequently opens only the
two `by`/`title` artifacts and still returns the three expected rows. OPTIONAL,
property paths, GRAPH, SERVICE, sub-SELECT, variable predicates, EXISTS and
other graph-dependent expressions deliberately use `open-mode=full-manifest`,
because those current evaluator paths can materialise the active graph. This
is a sound artifact-level I/O reduction, not yet mmap/range I/O inside a
selected IBK2 artifact. A later lazy/mmap/range reader must preserve the same
acceptance and `readOps` behavior before replacing it.

The same route was exercised on the bundled life-sciences `chromosome.ttl`
fixture: 9,227 triples packed to one predicate-local IBK2 child plus SBM0,
occupying 560 KiB, in approximately 25.5 seconds on the development Mac.
The parsed `P31` `SELECT … ORDER BY` returned 9,227 rows from the manifested
artifact.  The current packer is correctness-first and its load time is not a
throughput claim; it establishes the next corpus-sized regression point for
streaming and mmap/range work.

The same canonical-object contract has now crossed PostgreSQL `bytea` in a
local smoke: the manifest and every child block round-trip byte-for-byte, then
the Lean verifier and ordinary parsed SPARQL evaluation run on the retrieved
objects.  This demonstrates an interchangeable persistence realization, not
yet PostgreSQL-side execution.  TiKV should implement this exact artifact and
reader contract before any coprocessor/pushdown work is attempted.

## Landed bounded warm-session host

`Harness/ShardManifestSession.lean` adds `l4block-shard-session`, a native
batch-session host for the same `SBM0`/IBK2 reader contract. It reads the
manifest once, accepts one complete `SELECT` query per input line, and keeps
only successfully length- and SHA-256-verified `OpenBlock` values in a local
in-memory cache for the duration of that request batch. A cache hit therefore
uses the immutable already-admitted bytes; an external change to the file
after admission cannot alter that session's cached execution input. A cache
miss repeats the normal safe leaf-name, file read, digest, and IBK2 structural
validation path before it is admitted.

The session remains deliberately bounded and line-oriented rather than using
an unbounded Lean `partial` loop. It is a host-level warm-working-set building
block: a supervisor can choose request batching/process lifetime, while the
shared parser, physical-planner guard, `OpenStore.readOps`, and SPARQL
evaluator are unchanged. Each result reports its shard count, selective or
full-manifest mode, cache hits/misses, newly admitted bytes, and cache size.

`tools/blockengine-shard-session-smoke.sh` establishes the concrete behavior
on the music fixture: a two-predicate parsed join admits two artifacts; a
subsequent native `FILTER` query over `m:by` has one cache hit and zero new
artifact bytes; a later variable-predicate query safely expands to all seven
predicate artifacts (two hits, five new admissions). This is an observable
modest warm state, not an assertion that mmap, PostgreSQL workers, TiKV, or
per-segment positioned reads are complete.
