# Quad-aware block layout: the design decision behind spec gate 4

Status: decided by the owner 2026-09-02 evening (table below the options).
Option B's block layer landed 2026-09-03: `IBK4` is specified byte for byte in
section 6.1.1 of `docs/shardborough-storage-spec.md` and implemented in
`formal/lean4/L4Factoidal/Storage/IndexedBlockWireV4.lean`, with the round-trip
and denotation theorems in `IndexedBlockWireV4Theorems.lean`. The packer, the
manifest (`SBM7`), the graph-aware sidecars, the planner and the query path are
not implemented.

## Why now

- Owner, 2026-08-31, verbatim: "Please acknowledge that named graphs remain
  at the heart of our vision! Even if not in the MVP."
- Owner goal, 2026-09-02: "snappy searches against increasingly large dataset
  converted to Shardborough formed rdf indexed data." The next rung on the
  corpus ladder is the UK Parliament dump, 347 MB of TriG with named graphs
  (`third_party/data/ukparliament/`). The packer reads Turtle only, and the
  current family (IBK3 + SBM6) is default-graph-oriented: hub post 50 assigns
  a graph name to each block from its manifest, and the specification says
  in section 6.1 that this is not graph identity.
- Specification section 10, beta gate 4: "a settled RDF 1.2 term codec and
  tagged GraphId/quad layout, and a generation manifest that commits the
  blank-node scope of each source partition".

## What the specification already fixes

1. Versioned meaning (section 4.5): a change of bytes or meaning is a new
   magic/version, never a reinterpretation. Whatever is chosen is `SBM7`
   and, if rows change, `IBK4`.
2. Blank-node scope (section 2.4.1): the manifest commits the scope used for
   each source partition; the scope may span several named graphs of one
   imported dataset; it is not the graph IRI.
3. Named graphs, provenance, trust (section 9): the quad manifest preserves
   default-versus-named identity, source voice where supplied, and which
   graph set supplied schema premises.
4. Assertions and derivations stay distinguishable (section 4.7): physical
   duplication is allowed; query multiplicity is never inferred from
   duplicate rows.
5. Semantic neutrality (section 7): the layout stores quads; it does not
   privilege a vocabulary.

## Two ways to put the graph in the bytes

### A. Graph-partitioned entries (manifest-level)

Keep IBK3, PTD1, SRI2/OLI2 and TLI1 exactly as they are. Partition the
source by (graph, predicate) instead of by predicate. `SBM7` adds to each
manifest entry:

- `graph : Option WfIri` (`none` is the default graph);
- `blankNodeScope : String` (per source partition, section 2.4.1);
- the existing predicate, artifact, sidecar and Merkle fields unchanged.

A quad (g, s, p, o) is stored once, in the entry (g, p). The same triple in two
graphs is two quads and is stored twice, which is the RDF dataset semantics,
not duplication in the section 4.7 sense.

Query planning: `GRAPH <iri> { … }` selects entries with that graph;
`GRAPH ?g { … }` runs the pattern once per distinct graph and binds `?g`;
patterns outside `GRAPH` select the default-graph entries; `FROM` and
`FROM NAMED` become entry selections too. Every block-level theorem of today
(round trips, hash joins, backend arms) carries over unchanged, because no
block changes. The planner's completeness argument extends by one clause:
every quad with graph g and predicate p lies in exactly one entry.

Cost: the number of entries is (graphs × predicates present in each graph).
For the UK Parliament dump and a Wikidata truthy extract that is small. For
a Web corpus with one provenance graph per page
(`docs/20260830-web-corpus-working-sets.md`) it is one small block per page
and predicate, which defeats the per-block dictionary and the Merkle chunking
(65,536-byte chunks against blocks of a few hundred bytes).

### B. Graph column in the rows (block-level)

`IBK4`: rows of five u32 fields (position, g, s, p, o) with g a local ID into
the block's PTD1, one block per predicate across all graphs. Sidecars gain a
graph dimension: SRI2 postings keyed by (g, s) or a separate graph postings
sidecar; TLI1 unchanged. `GRAPH <iri>` becomes a bounded filter inside the
block, with a graph index for selectivity.

Cost: a new row codec, new sidecar semantics, new round-trip theorems for
IBK4 and the graph-aware postings, a new physical scan with its refinement
proof, and a repack of every existing generation (allowed: alpha).

### C. A, then B where it is needed

A now, because it unblocks the next rung with no byte-format change and
every theorem intact. B later, as the layout for the many-small-graphs case
(per-page provenance), chosen by a manifest-level `layout` label so both can
coexist in one collection: an entry is either a graph-partitioned IBK3 or an
IBK4 with an in-block graph column, and the planner reads the label.

## Recommendation

C, starting with A as `SBM7` + a TriG/N-Quads packer input. Reasons:

- The UK Parliament rung is reachable in agent-days, not weeks: the TriG
  parser exists (`Syntax/TriG`), the fast N-Quads parser exists, and the
  packer's partition step changes from `p` to `(g, p)`.
- The persisted executability census stops at "single-default-graph
  QueryEvaluationTests" (535 eligible). With A, the eligibility extends to
  the tests with `qt:graphData`, which gives an exact, official measure of
  named-graph coverage on the persisted path the day it lands.
- Hub post 50 stops assigning graph identity from its page manifest and
  reads it from the `SBM7` entries, closing the caveat its prose carries.
- Nothing about A is wasted if B follows: B is an additional entry kind under
  the same manifest, and the blank-node-scope commitment is needed by both.

## Work plan for A

1. `Storage/ShardManifest.lean`: `SBM7` with `graph` and `blankNodeScope` per
   entry; encoder admission equals decoder admission; a round-trip theorem in
   the style of the five landed on 2026-09-02; `SBM6` stays readable.
2. `Harness/PredicateShardPack.lean`: accept `.trig` and `.nq` input (the
   existing parsers), partition by (graph, predicate), write the scope per
   source file (a content digest is enough for a single import; section
   2.4.1 says when it is not).
3. `Harness/IndexedBlockV3Query.lean` and `ShardManifest.selectAll`: entry
   selection by graph; `GRAPH <iri>`, `GRAPH ?g`, default-graph patterns;
   the constant-predicate collector learns `.graph`.
4. `tools/w3c-persisted-census.sh`: eligibility extended to `qt:graphData`
   tests; the number becomes the named-graph coverage gate.
5. Hub post 50: read graph identity from the manifest entries.
6. The UK Parliament rung: pack, activate, the workload, plus the
   `bench_ukpar_*` queries that already exist for the F\* store.

## Owner decisions, 2026-09-02 evening (recorded from the four-question form)

| Decision | Owner's choice | Note |
| --- | --- | --- |
| 1. Layout order | **B first** (graph column in the rows, `IBK4`), against the recommendation of A | The A-first argument (no byte change, theorems carry over) was put to the owner and overruled. One layout for all cases. |
| 2. Default graph | `graph = none` | As recommended. |
| 3. Blank-node scope | Content digest per source file, with the section 2.4.1 caveat as a manifest profile flag | As recommended. |
| 4. Next work after the Turtle parser fix | Scale first: profile `l4block-shard-pack` and `l4block-shard-activate` on the UK Parliament store | Named-graph work (B) starts after pack and activate are linear. |

The work plan for A above is kept as the record of the alternative; the
plan to execute is B. Status of this document: decided, not implemented.

## 🧭 Decisions for the owner (as put, 2026-09-02 afternoon)

1. A first (recommended), or B first?
2. Default graph: `graph = none` in the entry (recommended), or a reserved
   IRI?
3. Blank-node scope per source file: the file's content digest for the
   corpus-ladder files (recommended for now), with the section 2.4.1 caveat
   recorded in the manifest as a profile flag.
4. The UK Parliament dump's graph count decides how much of this the next
   rung needs. Measured 2026-09-02 (text scan; the full Lean profile of the
   347 MB file was stopped before it finished): the file has exactly one
   graph block, an unlabelled `{ … }` opened at line 20, which in TriG is
   the default graph. 5,325,830 lines, 2,581,138 of them statement-ending,
   so of the order of 5 million triples once `;` and `,` continuations are
   counted. So the UK Parliament rung is a scale rung, not a named-graph
   rung: it can go through today's family with TriG input to the packer
   (or the one-line conversion that drops the block braces), and the
   quad-aware layout is what the Web-corpus and provenance-bearing rungs
   need, not this one.
