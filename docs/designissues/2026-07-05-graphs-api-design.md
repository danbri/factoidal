# A graphs-first API for Factoidal — design

**Date:** 2026-07-05.
**Status:** design proposal, ready to slice. No code changes here.
**Owner's goal:** "rich factoidal with graphs api" — surface named
graphs, and per
[`2026-07-04-blogic-surfaces-graphs-review.md`](2026-07-04-blogic-surfaces-graphs-review.md),
*component* graphs with substructure, as first-class values at every
layer: F* core, CLI, npm/JS — not just an implicit dimension of
`match(s,p,o,g)`.

This doc turns that review's §2/§4 findings into a concrete, gated,
commit-sized slice. It does not repeat the literature review; read
that doc first for citations.

## 0. What the review already settled

Four findings this design depends on:

1. **RDF 1.1 assigns no semantics to the relation between named
   graphs** (Zimmermann Note, review §1.5). A component-graph layer is
   vocabulary + convention on top of `rdf_dataset`, not a change to
   it. `ds_named : list named_graph`
   ([`RDF.Graph.Executable.fst:151`](../../formal/fstar/RDF.Graph.Executable.fst))
   stays exactly as it is.
2. **Component-contiguous storage** (review §2.2) — sort COTTAS rows
   by `(shape-id, component-id, s, p, o)` so per-row-group `g` ranges
   and the graph-Bloom sidecars become selective. Not needed for
   slice 1; it is the on-disk-scale continuation (§5 below).
3. **RDFC-1.0 hashes are the content-addressed naming scheme**
   (review §2.3, following Kuhn & Dumontier's Trusty URIs): a
   component's name can be derived from its own canonical hash.
4. **Depth-≤2 negative surfaces are Horn rules** (review §3.1) — a
   distinct, larger effort (new F* AST + parser + rule compiler). Not
   a graphs-API concern; out of scope here (§5).

## 1. API surface, three layers

### 1.1 F* core

New module `RDF.Dataset.Graphs.fst` — a pragmatics/accessor module
per [`skills/fstar-module-style/SKILL.md`](../../skills/fstar-module-style/SKILL.md),
no new proof obligations beyond what `rdf_dataset` already carries:

```fstar
module RDF.Dataset.Graphs
open FStar.List.Tot
open RDF.Graph.Executable

// An IRI, not a new term kind. Includes the "_:<label>" blank-node
// graph-name convention (RDF.Dataset.Merge.rename_graph_name).
type graph_ref = iri

// All (name, graph) pairs, default graph excluded — SPARQL's
// FROM NAMED universe.
let graphs (ds : rdf_dataset) : list (graph_ref * rdf_graph) =
  List.Tot.map (fun (ng : named_graph) -> (ng.ng_name, ng.ng_graph)) ds.ds_named

// Re-export of lookup_named_graph under the graphs-API name.
let component_of (ds : rdf_dataset) (name : graph_ref) : option rdf_graph =
  lookup_named_graph name ds.ds_named
```

Both are `Tot` compositions of existing accessors — no new semantics.

One function with actual new content, added to
[`RDF.Canonical.fst`](../../formal/fstar/RDF.Canonical.fst) — the
per-graph sibling of `canonicalize_to_nquads` the review's §4 asked
for:

```fstar
// Canonicalize one named graph as a single-graph dataset. Composes
// two existing things (component projection, whole-dataset
// canonicalize_to_nquads) — not a new algorithm. Inherits the
// existing HFDQ-only limitation (HNDQ not implemented, 23/86
// rdf-canon fails) unchanged.
let canonicalize_named_graph (ds : rdf_dataset) (name : RDF.Dataset.Graphs.graph_ref)
    : option string =
  match lookup_named_graph name ds.ds_named with
  | None -> None
  | Some g -> Some (canonicalize_to_nquads ({ ds_default = g; ds_named = [] }))
```

### 1.2 CLI

Follows the existing subcommand style
([`bin/factoidal-cli/factoidal_cli.ml:537-539`](../../bin/factoidal-cli/factoidal_cli.ml)
`known_subcommands`, help text at line 607):

```
factoidal graphs list  FILE          list named-graph IRIs
factoidal graphs get   FILE <iri>    dump one graph's triples (N-Triples)
factoidal graphs hash  FILE <iri>    RDFC-1.0 canonical hash of one graph
factoidal graphs diff  FILE1 FILE2   added/removed/changed component hashes
```

Each is a thin `bin/` wrapper (iron rule #11: consumer, not library
boundary) over §1.1 plus the existing loader (`load_dataset`, line
128) and printer (`RDF_Pretty.term_to_ntriples`, line 29):

- `list` — `RDF_Dataset_Graphs.graphs dataset`, print each name.
- `get` — `RDF_Dataset_Graphs.component_of dataset iri`; print the
  `Some` graph's triples, or exit 1 on `None`.
- `hash` — `RDF_Canonical.canonicalize_named_graph dataset iri`,
  print the resulting canonical N-Quads (or `sha256:<hex>` of it,
  once wired to the `hash_sha256` `assume val` already declared at
  `RDF.Canonical.fst:36`).
- `diff` — run `list`+`hash` over both files, compare `(iri, hash)`
  pairs as OCaml string sets. Set comparison over two already-verified
  strings, not new RDF/SPARQL semantics — stays in `bin/` under rule
  #11.

`known_subcommands` gains `"graphs"`; help text gains one line.

### 1.3 npm / JS

`npm/factoidal/lib/api.js` already shapes `parse`/`query`/
`canonicalize` (line 356) /`capabilities` (line 392). Additive
functions only — no `DatasetCore` interface change:

```js
// graphs(ds) -> Iterable<[iri: string, graph: DatasetCore]>
// DatasetCore.match(null,null,null,graphNode) already gives per-graph
// read access; this adds enumeration, which match() alone cannot
// (no way to ask "what graph names exist").
function graphs(dataset) { ... }

// canonicalHash(datasetOrGraph) -> Promise<string>
// Graph-scoped sibling of canonicalize(); gated via capabilities()
// the same way canonicalize() is today.
async function canonicalHash(datasetOrGraph) { ... }
```

`DatasetCore.match` already covers reading a component — confirming
the review's §4 finding that RDF/JS needs nothing new for read
access.

## 2. Component graphs: naming and membership

### 2.1 Naming scheme

Content-addressed names under a `urn:rdfc:` prefix, following the
RDFC-1.0-as-identity finding (§0.3) and the review's `c14n:sha256:...`
sketch (review §2.1, §4), written as a legal IRI:

```
urn:rdfc:sha256:<lowercase-hex-of-hash_sha256(canonical_nquads(graph))>
```

This buys, matching the nanopub/Trusty-URI precedent (review §1.7,
§2.3): isomorphic components get the same name (dedup, idempotent
re-ingest for free); the name is derivable by any consumer running the
same F* canonicalization code, no central minting authority; and it
composes directly with `factoidal graphs hash`, which computes exactly
this name's suffix.

This is a naming *convention*, not an engine change — `ng_name` is
already `iri`-typed and admits any IRI string
([`RDF.Graph.Executable.fst:146`](../../formal/fstar/RDF.Graph.Executable.fst)).
A component may also keep an application-assigned name (e.g. from an
R2RML `rr:graphMap` row); `urn:rdfc:` is the derived, verifiable
identity offered alongside it, not a replacement for it.

### 2.2 Membership representation — three options

How a consumer learns "component C instantiates shape S" / "C is part
of dataset D" / "C came from SQL row R" (review §2.1):

1. **Quad reification** — companion triples (`:component-42
   fct:instantiates :PersonShape ; fct:partOf :dataset-2026-07 .`) in
   the default graph or a metadata graph. RDF-native, zero grammar or
   engine change, queryable with plain SPARQL, visible to any RDF/JS
   consumer as ordinary triples.
2. **Naming-convention encoding** — bake shape/parent into the IRI
   (`urn:component:PersonShape:42`). Cheap to parse, but couples
   identity to classification: a component satisfying a second shape,
   or getting reparented, needs a new name, breaking the
   content-addressing property in §2.1.
3. **Sidecar index** — an out-of-band companion file mapping
   component IRI → `{shape, parent, sourceRow}`, analogous to the
   graph-Bloom sidecars. Fast bulk lookup at millions-of-components
   scale, but duplicates information outside the RDF model and is an
   on-disk/COTTAS-format concern — new byte layout belongs in F* per
   rule #11 and the Option-B hash-witness pattern
   ([`2026-05-07-io-verification-and-third-party.md`](../designissues/2026-05-07-io-verification-and-third-party.md)),
   real design work on its own.

**Recommendation: quad reification for slice 1.** No new format, no
new module beyond §1.1, queryable with the SPARQL the engine already
has (`GRAPH ?g` joins straight into `?g fct:instantiates ?shape`).
Defer the sidecar index to the component-graph-corpus scaling work
(review §5, X1) — that is where a millions-of-components performance
case exists to justify new on-disk structure; minting one now would
be speculative.

## 3. What the engine already does vs. what's new

`GRAPH ?g` / `GROUP BY ?g` already give enumeration and per-component
aggregation with the SPARQL 1.1 the engine has:

```sparql
SELECT DISTINCT ?g WHERE { GRAPH ?g { ?s ?p ?o } }         # list
SELECT ?g (COUNT(*) AS ?n) WHERE { GRAPH ?g {?s ?p ?o} }
  GROUP BY ?g                                               # per-component counts
```

Status, from measurement on record: the **in-memory** path is
confirmed correct for both forms — the parity harness
([`2026-07-04-backend-parity-harness.md`](2026-07-04-backend-parity-harness.md))
traced an earlier suspected `GRAPH ?g` regression to a false alarm
there (issue #267). The **on-disk** path has a live bug: `GROUP BY ?g`
over a COTTAS file returns the same wrong count for every graph while
the ungrouped `COUNT(*)` forms are correct
([`2026-07-03-e1-cs-clustering-results.md`](2026-07-03-e1-cs-clustering-results.md)
§6.2). Not yet filed as its own issue as of this writing.

Consequence: every slice-1 call — `list`/`get`/`hash`/`diff`,
`graphs()`/`canonicalHash()` — is expressible as a query or direct
accessor over an **in-memory** `rdf_dataset`, where enumeration is
already correct. None requires a new SPARQL evaluator feature. The one
genuinely new piece of code is `canonicalize_named_graph` (§1.1), and
that is composition of two existing functions, not new algebra,
grammar, or a closure rule.

**Slice-1 scope decision:** restrict `factoidal graphs *` and the npm
`graphs()`/`canonicalHash()` to in-memory-loaded datasets, exactly
like `factoidal query`/`dump`/`canonicalize` already are (all call
`load_dataset`, which parses whole files into memory — there is no
COTTAS on-disk path in this CLI today). This sidesteps the on-disk
`GROUP BY ?g` bug entirely for slice 1; filing and fixing it becomes a
blocking prerequisite only when a COTTAS-backed `graphs` command is
proposed.

## 4. First commit-sized slice

**Lands:**

| File | Change |
|---|---|
| `formal/fstar/RDF.Dataset.Graphs.fst` | new: `graph_ref`, `graphs`, `component_of` (§1.1) |
| `formal/fstar/RDF.Canonical.fst` | add `canonicalize_named_graph` (§1.1) |
| `bin/factoidal-cli/factoidal_cli.ml` | `"graphs"` in `known_subcommands` (line 538); dispatch for `list\|get\|hash\|diff`; one help line |
| `npm/factoidal/lib/api.js` | `graphs()`, `canonicalHash()` (§1.3), gated through `capabilities()` (line 392) |
| `npm/factoidal/index.d.ts`, `index.js`, `index.mjs` | export the two new functions |
| `npm/factoidal/README.md` | two new API-table rows, matching the existing table (line 98) |

**Tests:**

- F*: a focused test extending whichever local regression exercises
  `RDF.Graph.Executable` dataset helpers, checking: `graphs` on a
  3-named-graph dataset returns all three, in `ds_named` order;
  `component_of` returns `None` for an unknown name, `Some` for a
  known one; `canonicalize_named_graph` on a bnode-free graph matches
  hand-computed canonical N-Quads, and returns `None` for an unknown
  name.
- CLI: `tests/local/graphs_cli_regressions.sh` (naming matches
  `tests/local/backend_parity_regressions.sh`) — load a small TriG
  fixture with 2-3 named graphs; check `graphs list` output, `graphs
  get` round-trips a triple count, `graphs hash` is stable across two
  runs and changes when a triple is added, `graphs diff` reports 0
  differences between a file and itself.
- npm: extend `npm/factoidal/test/api.test.js` with `graphs()`
  enumeration over a parsed TriG string and `canonicalHash()`
  stability under blank-node relabeling, mirroring the existing
  `canonicalize()` stability test in that suite.

**Gating:** F* verifies under z3 4.13.3, no `--lax`; `build-ocaml.sh
extract` then `compile` (extract, not compile, picks up new modules —
anti-pattern #11); W3C suites unchanged (631/631 SPARQL, 1031/1031 RDF
parsing — this slice touches no parser or evaluator code); rdf-canon
suite unchanged (62 pass, 23 fail, 1 skip of 86 — the wrapper reuses
`canonicalize_to_nquads` unmodified); new CLI script green; `npm test`
green including the two new cases.

**Not in this slice:** `factoidal component split|compose` (review
§4's candidate for materializing/exploding component corpora) — that
is corpus-pipeline tooling, its own commit once naming/membership have
been exercised by a real consumer.

## 5. Non-goals for slice 1

- **Surfaces / depth-≤2 Horn rules** (review §3, X3). A distinct F*
  module (`RDF.Surfaces.fst`), a new N3-sublanguage parser, and a
  rule-compiler into the existing closure engine — new semantics, not
  a graphs-API concern. Its own future slice.
- **SQL/XML mapping** (R2RML `rr:graphMap`, GRDDL). `factoidal import
  --r2rml mapping.ttl` is future CLI surface once R2RML parsing exists
  in F* (rule #4: parsers are F*-first); this slice only defines the
  graph-shaped target such an importer would populate.
- **Millions-of-components scaling.** Linear `lookup_named_graph`
  ([`RDF.Graph.Executable.fst:159-162`](../../formal/fstar/RDF.Graph.Executable.fst)),
  per-graph in-memory overhead, component-contiguous COTTAS row order,
  and the sidecar-index option (§2.2, option 3) are deferred to the
  storage-scaling track, which resumes at
  [`2026-07-03-e1-cs-clustering-results.md`](2026-07-03-e1-cs-clustering-results.md)
  and experiment X1 in the review's §5 — a component-graph corpus on
  COTTAS, measuring size, prune rate, and in-memory RSS at
  10k/100k/1M components. Slice 1 stays in-memory-scale (same scale
  `factoidal query`/`dump` already operate at) so it can land without
  waiting on that track.
- **Canonical-hash sidecars / Merkle roll-ups on disk** (E3 in
  [`2026-07-03-shapes-canon-storage-strategies.md`](2026-07-03-shapes-canon-storage-strategies.md)
  §5). Slice 1 computes a hash on demand from an in-memory graph;
  persisting per-component `.c14n.sha256` companion files in the
  corpus pipeline is the E3 experiment, not this slice.
- **HNDQ / full RDFC-1.0 tie-breaking.** `canonicalize_named_graph`
  inherits the HFDQ-only limitation unchanged (23/86 rdf-canon fails);
  it adds no tie-detection or decline-to-hash guard beyond what
  `canonicalize_to_nquads` already does. If the whole-dataset
  `canonicalize()` later gets a decline-on-tie guard, the per-graph
  wrapper should pick it up in the same change, not diverge.
