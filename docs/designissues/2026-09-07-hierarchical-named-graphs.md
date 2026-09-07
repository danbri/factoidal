# Configurable named-graph IRI patterns: a big graph made of millions of small ones

2026-09-07. Owner, verbatim:

> "Think about some configurable named graph URL patterns where a big named
> graph breaks down into potentially 1000s or millions of subgraphs eg per
> record or triple or shape, but the composition of the latter into the
> former is implied by the URL string structures of all the named graphs
> concerned."

Design record only. The Lean sketch is
[`formal/lean4/L4Factoidal/RDF/GraphPatterns.lean`](../../formal/lean4/L4Factoidal/RDF/GraphPatterns.lean):
types, the grammar, the matcher, the order, the view, and the theorem
statements. No implementation has landed and no gate has been run.


Tracking issue: <https://github.com/danbri/factoidal/issues/660>. The Lean
sketch `formal/lean4/L4Factoidal/RDF/GraphPatterns.lean` compiles under
`lake env lean` (checked 2026-09-07, 0 errors).

## 0. What the specifications do and do not give us

[RDF 1.1 Concepts §4](https://www.w3.org/TR/rdf11-concepts/#section-dataset)
defines a dataset as a default graph plus zero or more (name, graph) pairs,
and says of the names only that they are IRIs or blank nodes. It assigns no
relation between the graphs of a dataset. The
[RDF 1.1 Datasets note](https://www.w3.org/TR/rdf11-datasets/) records that
several semantics for datasets were in use and that the Working Group
standardised none of them. So a composition relation over graph names is a
LOCAL declaration made by a store, not a fact about RDF, and it must be
written down as a declaration that a reader can see.

Two things follow, and they shape everything below.

1. The composed dataset is an ordinary RDF dataset. The query language does
   not change. [SPARQL 1.1 Query §13.1](https://www.w3.org/TR/sparql11-query/#specifyingDataset)
   lets a service supply the dataset a query runs against, so a store may
   expose the composed dataset and every `GRAPH`, `FROM` and `FROM NAMED`
   rule applies unchanged to it.
2. Nothing in RDF makes a reader of our data see the composition. A client
   that fetches the leaf graphs and unions them gets our answer; a client
   that assumes `…/g/x/c/y` is unrelated to `…/g/x` is also right by the
   specification. The declaration must therefore be published (§5), not
   inferred.

[RDF 1.2 Concepts §4](https://www.w3.org/TR/rdf12-concepts/#section-dataset)
keeps the same dataset definition and adds no composition relation; its
additions that touch this project are triple terms and base direction.
Re-check that sentence against the current draft before it is quoted
outside the repository.

---

## 1. The pattern language

### 1.1 Grammar

A declaration is a list of TEMPLATES plus a list of COMPOSITION EDGES over
their indices. A template is
[RFC 6570](https://www.rfc-editor.org/rfc/rfc6570) level 1
([§1.2](https://www.rfc-editor.org/rfc/rfc6570#section-1.2)), restricted
further:

```
template   ::= literal ( expression literal? )*
expression ::= "{" varname "}"
literal    ::= one or more characters, none of them "{" or "}"
varname    ::= RFC 6570 varname, no operator, no modifier, no explode
```

with three side conditions, all decidable (`Template.wf`):

* the template starts with a non-empty literal;
* no two expressions are adjacent (otherwise a match is ambiguous);
* a variable name appears at most once.

Level 1 is chosen and the higher levels are refused for one reason: level-1
simple string expansion
([RFC 6570 §3.2.2](https://www.rfc-editor.org/rfc/rfc6570#section-3.2.2))
percent-encodes every character outside the unreserved set, `/` included, so
an expanded value never introduces a path segment.
[RFC 3986 §3.3](https://www.rfc-editor.org/rfc/rfc3986#section-3.3) makes `/`
the segment delimiter, so the segment structure of an instantiated IRI is
fixed by the template and not by the data. Level 2's `{+var}` and `&#123;#var}`
would break that, and with it the matcher's determinism and the interval
argument in §4.

### 1.2 Matching

`Template.match? : Template → String → Option Bindings` walks the segment
list against the characters of the IRI: a literal must match exactly; an
expression consumes the longest non-empty run of characters that is not `/`.
The function is total and is structural recursion on the segment list.

A declaration matches an IRI by scanning its templates in order and taking
the first that matches. Determinism is a REQUIREMENT on the declaration,
stated as `Decl.deterministic`: at most one template matches any IRI. The
function is defined either way so that a declaration violating the
requirement still has a meaning rather than an undefined one; the check that
it holds is the declaration's admission test.

Determinism is what gives "each graph IRI matches at most one leaf
template", which §3 states as T2. It is decidable for the templates we
admit — two level-1 templates overlap only when their literal skeletons
unify — but the decision procedure is not written yet, and the first slice
checks determinism by an admission test over the declared templates plus the
per-instance evidence that no stored graph name matches twice.

### 1.3 Composition

`parent ≤ child` (`below` in the sketch) holds when

1. both IRIs match, at template indices `i` and `j`, and
2. `(i, j)` is a DECLARED composition edge, and
3. the parent's string is a prefix of the child's string.

Condition 3 is the part the owner's sentence asks for: composition is read
off the IRI strings. Condition 2 is what §1.5 calls the part that is not
implied and must be declared. Well-formedness (`Decl.wf`) requires that a
declared edge is supported by the template structure — the child's segment
list extends the parent's and the first extra segment is a literal starting
with `/` — and that the edge set is reflexive on the declared templates and
transitive. With those, condition 3 follows from the bindings agreeing on
the parent's variables, and the check on the strings is cheap and needs no
bindings.

### 1.4 The three cases the owner named

**Per record.** One graph per source record.

```
parent  https://skosdex.example/g/{scheme}
child   https://skosdex.example/g/{scheme}/c/{concept}
```

This is the skosdex case: today one graph per concept scheme, 717 of them,
injected by skosdex's `graphed` step; the next level is one graph per
concept, about 14 million. The leaf's `{concept}` value is normally the
local name of the record's subject IRI, which §4 uses.

**Per triple.** One graph per triple, for provenance and for retraction by
content.

```
child   https://s.example/g/{scheme}/t/{hash}
```

`{hash}` is a hash of the canonical form of the one-triple graph under
[RDFC-1.0](https://www.w3.org/TR/rdf-canon/). Two consequences. The graph
name then DETERMINES the triple (T5), so `DROP GRAPH <name>` is retraction
by content and needs no scan. And the graph column of a stored row becomes
derivable from the row, so a store need not keep it (§4.5). A per-triple
pattern is only well defined for triples with no blank node, because a blank
node has no canonical name outside its graph; a source with blank nodes must
be skolemized first
([RDF 1.1 Concepts §3.5](https://www.w3.org/TR/rdf11-concepts/#section-skolemization),
`/.well-known/genid/`).

**Per shape.** The grouping key is a shape:

```
child   https://s.example/g/{shape}/r/{record}
```

with `{shape}` the local name of a [SHACL](https://www.w3.org/TR/shacl/)
node shape or a [ShEx](http://shex.io/shex-semantics/) shape label. It makes
"revalidate every record against this shape" one `GRAPH <parent>` read, and
it makes a validation report addressable.

The risk to state, because it does not arise in the other two cases:
conformance to a shape is not a property of the record alone and it changes
when the data changes, so a shape-keyed graph name is MUTABLE. Moving a
record between shape graphs is a rename, which the delta log must express as
a delete plus an insert under a new name (§4.6), and a client holding the old
name gets 404 rather than stale data. A shape-keyed pattern is therefore
admitted only with an explicit `mutableNames` flag on the declaration.

### 1.5 What the strings do NOT imply

The string structure is necessary, not sufficient. These must be declared:

* **Which extension edges are composition.** `…/g/{scheme}/meta/{key}`
  extends `…/g/{scheme}` as a string and must NOT compose into it: the
  scheme's metadata is about the scheme, not part of it. The sketch's
  `skosdexDecl` declares edge `(0,1)` and no edge `(0,2)`, and the
  `#guard`s pin both outcomes.
* **Whether the parent has triples of its own.** A parent may name a stored
  graph as well as denote a union.
* **Whether `GRAPH ?g` enumerates parents** (§2.2).
* **Whether writes cascade** (§2.5, §2.6).
* **Whether the default graph is the union of the leaves** (§2.4).
* **Depth.** Three levels (`/g/{s}`, `/g/{s}/c/{c}`, `/g/{s}/c/{c}/t/{h}`)
  are admitted by the same machinery; nothing in the grammar caps it.

---

## 2. Semantics

The composed dataset is a VIEW: for a graph name `n` that the declaration
matches, the graph `n` denotes is the union of the graphs named by every IRI
below `n` in the order, `n` itself included, so a parent with its own stored
triples keeps them. `view` and `composedDataset` in the sketch are that
definition. Everything below is a consequence plus the configuration flags
where the specifications leave a choice.

### 2.1 `GRAPH <parent> { P }`

`P` is evaluated with the view of `<parent>` as the active graph.
[SPARQL 1.1 Query §13.3](https://www.w3.org/TR/sparql11-query/#queryDataset)
says `GRAPH` sets the active graph to the graph named by the IRI, and
§13.1 lets the service decide which dataset that is; the view IS the
dataset the service exposes, so no rule of §13 or §18.5 is bent.

One case has teeth and is inherited from the current planner:
[§18.6](https://www.w3.org/TR/sparql11-query/#sparqlAlgebraEval) gives
`GRAPH <g> { }` one solution when `<g>` names a graph of the dataset and
none when it does not. Under a pattern declaration a parent NAMES a graph
whenever any leaf below it exists, even when the parent has no stored
triples. `queryGraphNames?` already adds the constant name for this reason
(`ShardManifest.graphsReadFrom`), and §4.3 says what it must resolve to.

### 2.2 `GRAPH ?g { P }` — leaves, parents, or both

Configurable: `enumerate ∈ {leaves, parents, all}`. **Default: `leaves`.**

Reasons for the default:

* It keeps `GRAPH ?g { ?s ?p ?o }` equal to the stored quads, so
  round-tripping a store through N-Quads and back is the identity. Under
  `all`, one triple is returned under its leaf name and again under every
  ancestor name, and `SELECT (COUNT(*))` over the dataset multiplies by the
  depth.
* RDF 1.1 permits overlapping graphs — §4 requires only that the names be
  distinct — so `all` is legal, but the multiplication is a surprise a
  client cannot see coming from the data.
* Under `leaves` the answer to `GRAPH ?g` is the same before and after the
  declaration is added, so adding a declaration to an existing store cannot
  change an existing query's answer except through a constant parent name.

The cost, stated because it is a real loss: under `leaves`, a name that
`GRAPH <parent>` answers is not enumerated by `GRAPH ?g`, so `?g` is not a
complete enumeration of the names the service will answer for. Service
description (§5) is where that is repaired. This is open decision 1.

### 2.3 `FROM` and `FROM NAMED`

[§13.2](https://www.w3.org/TR/sparql11-query/#specifyingDataset).
`FROM <parent>` merges the VIEW of the parent into the default graph;
`FROM NAMED <parent>` installs the view under the name `<parent>`.
`FROM NAMED <leaf>` installs the leaf alone. This follows from the view
being the dataset: `applyDataset` in `SPARQL/Query.lean` looks graphs up by
name, and the lookup returns the view.

### 2.4 The default graph

Unchanged by a declaration: the pattern relation is over named graphs only.
A store may separately declare that the default graph is the union of every
named graph, which
[SPARQL 1.1 Service Description](https://www.w3.org/TR/sparql11-service-description/#sd-UnionDefaultGraph)
names `sd:UnionDefaultGraph`. The two are independent flags and are not
mixed.

### 2.5 SPARQL Update

[SPARQL 1.1 Update §3.1 Graph Update](https://www.w3.org/TR/sparql11-update/#graphUpdate)
and [§3.2 Graph Management](https://www.w3.org/TR/sparql11-update/#graphManagement).

* `INSERT DATA { GRAPH <leaf> … }` — ordinary insert into the leaf. §3.1.1
  says the graph is created if it does not exist, so the leaf appears and
  every parent's view grows. No new rule.
* `INSERT DATA { GRAPH <parent> … }` — the triples go into the parent's OWN
  graph. They are then in the view of the parent and in no leaf. The
  alternative is a declared routing function from a triple to a leaf name
  (the per-record key function of §1.4 run backwards); it is admitted as an
  option, `routeInsert`, and is OFF by default, because a store that routes
  silently answers `DELETE DATA` of the same triple from a place the client
  did not write it to.
* `DELETE DATA { GRAPH <parent> … }` — deletes from the parent's own graph
  only. It does NOT reach into leaves under the default, for the same
  reason.
* `DROP GRAPH <parent>` —
  [§3.2.2](https://www.w3.org/TR/sparql11-update/#drop) says DROP removes
  the specified graph from the Graph Store. In the composed dataset the
  specified graph is the view, so removing it means removing the leaves.
  **Default: cascade** — `DROP GRAPH <parent>` drops every graph below it.
  `DROP GRAPH <leaf>` drops one. `SILENT` keeps its §3.2.2 meaning.
  Configurable as `dropCascade`, and this is open decision 2: the argument
  against cascading is that Update operates on the Graph Store, which the
  Graph Store Protocol defines over the graphs the store HOLDS, and the
  view is not one of those.
* `CLEAR GRAPH <parent>`, `COPY`, `MOVE`, `ADD` — read the view as the
  source and the cascade flag on the destination, by the same rule as DROP.
* `CREATE GRAPH <parent>` — §3.2.1. Creating a parent creates an empty
  stored graph for it; it does not create leaves and does not fail because
  leaves exist.

### 2.6 Graph Store Protocol

[SPARQL 1.1 Graph Store HTTP Protocol](https://www.w3.org/TR/sparql11-http-rdf-update/).

* `GET` of a parent ([§5.2](https://www.w3.org/TR/sparql11-http-rdf-update/#http-get))
  returns a serialization of the VIEW. This is the operation that makes the
  pattern worth having: one request for a whole scheme, assembled from
  fourteen thousand leaves the client never sees.
* `PUT` of a parent ([§5.3](https://www.w3.org/TR/sparql11-http-rdf-update/#http-put))
  replaces a graph. Under `dropCascade = false` it replaces the parent's own
  graph and leaves the leaves alone, which makes a `GET` then `PUT` round
  trip LOSE nothing but also not do what the client meant. **Default:
  refuse `PUT` on a parent with `409 Conflict`** and say why in the body.
  Under `dropCascade = true`, `PUT` is defined as drop-then-insert into the
  parent's own graph, and the response documents that the leaves were
  removed.
* `DELETE` of a parent follows `dropCascade`, as DROP does.
* `POST` of a parent merges into the parent's own graph.

### 2.7 Blank nodes across leaves

[RDF 1.1 Concepts §3.4](https://www.w3.org/TR/rdf11-concepts/#section-blank-nodes)
scopes blank node labels to the document; §4 puts graph names in the same
scope. Inside one dataset a blank node may therefore be shared between
graphs, and the union that a view takes preserves the sharing.

What breaks is the leaf in ISOLATION. A leaf fetched on its own — a GSP
`GET` of a leaf, a Solid resource read, an N-Triples file per record — is a
document with its own blank-node scope, so a blank node that appeared in two
leaves becomes two distinct blank nodes on the way back in, and the two
records are no longer connected. Rules:

1. A per-record split MUST keep every triple of a blank-node-connected
   component in one leaf. `splitByKey` in the sketch does not check this; the
   packer must, and refuse the split otherwise.
2. A per-triple split cannot satisfy rule 1 for any triple with a blank node,
   so it requires skolemization first (§1.4).
3. A store that serves leaves individually and also serves the view must
   report which of the two it did, because only the view carries the
   sharing. The `Content-Location` of a leaf response is the leaf IRI; that
   is the report.

### 2.8 Where the specifications leave the choice open

Flagged, in one list, because each one is a place a different store could
answer differently and still conform:

| Question | Specification | Our default |
|---|---|---|
| Any relation between the graphs of a dataset | RDF 1.1 Concepts §4; Datasets note — none defined | The declaration |
| What `GRAPH ?g` enumerates | §13.3 enumerates the dataset's names; which names the dataset has is the service's | Leaves |
| Whether a parent with no stored triples "names a graph" for `GRAPH <g> { }` | §18.6 tests the dataset | Yes, when a leaf exists |
| Whether DROP of a composed graph cascades | Update §3.2.2 is about the Graph Store | Cascade |
| PUT of a composed graph | GSP §5.3 replaces "the graph" | 409 |
| Default graph as union | Service Description `sd:UnionDefaultGraph` | Off |

---

## 3. Theorems to state

Statements are in
[`GraphPatterns.lean`](../../formal/lean4/L4Factoidal/RDF/GraphPatterns.lean).
The definitional ones are proved there; the rest are `Prop`-valued `def`s,
which is a statement carrying no proof and no `sorry`.

| Id | Name in the sketch | Statement | Status |
|---|---|---|---|
| T1 | `IsPartialOrder` | On the IRIs a well-formed deterministic declaration matches, `below` is reflexive, antisymmetric and transitive. | Stated |
| T2 | `UniqueLeaf` | A deterministic declaration matches each IRI at one template with one binding: one leaf per graph name, hence one leaf per triple placed by the pattern. | Stated |
| T3a | `view_eq_union` | The view of a parent is the union of the graphs below it. | Proved (`rfl`) |
| T3b | `composed_default`, `composed_names` | The composed dataset keeps the default graph and names exactly the graphs the source names. | Proved |
| T4 | `ViewMonotone` | Adding a named graph only adds triples to a view. | Stated |
| T5 | `ConstantParentEquivalence` | For any function of a graph, the answer over the view of a constant parent equals the answer over the union of the graphs below it. This is the planner obligation: `queryGraphNames?` may map `<parent>` to the leaf set. | Stated |
| T6 | `PerTripleDetermined` | With an injective canonical form, a per-triple graph name determines its triple, so retraction by name is retraction by content. | Stated |
| T7 | `SplitRoundTrip` | Splitting a graph by any key function and recomposing gives back the same triples. | Stated |

T5 is stated over an abstract `eval : Graph → Answer` so that the sketch does
not import `SPARQL/Query.lean`. Its concrete instance is
`evalPatternBackend` at the `indexedDatasetBackend` seam, which is where
`docs/designissues/2026-09-06-planner-soundness-theorem.md` Lemma G lives.
The composition is: Lemma G says an entry whose `graphSet` meets no name the
query reads can be skipped; T5 says the names a constant parent reads are the
leaves below it; together they say an entry outside the parent's leaf
interval can be skipped. The interval form of `graphSet` is §4.3.

T1's antisymmetry needs the prefix condition, not just the declared edge:
two distinct IRIs cannot each be a string prefix of the other. That is why
condition 3 of §1.3 is checked at run time rather than derived.

---

## 4. Storage and planner consequences for Shardborough

Working figures for the scale case, all labelled. The corpus is the skosdex
build of `deploy/fly/skosall/README.md`: 718 `canonical.nq.gz` files, about
65 GB as N-Quads, about 42 GB as a wire-version-10 generation (MEASURED as
compressed sizes and ESTIMATED for the generation). The prompt's working
numbers for the per-concept level are 219 million quads and about 14 million
concepts, so about 15.6 quads per leaf graph.

### 4.1 The block bucket — the change that has to happen first

`Storage/PredicateQuadBlocks.lean` buckets quads by the pair
(predicate, graph) and cuts a bucket at `maxBlockRows` or
`maxBlockWireBytes` (publication rules 1 and 2 after the 2026-09-05
amendment). Rule 3 carries a run below `minBatchRows` (4096) across a batch
end instead of publishing a near-empty block; rule 4 publishes every open run
when the carried rows pass `maxCarriedRows` (1,048,576). Every block
therefore holds ONE graph and its `graphSet` has one member.

With per-concept graphs that bucketing is unusable. 14 million leaves times
the number of distinct predicates a concept uses — say 8 to 12 for SKOS — is
of the order of 10^8 buckets, each holding one or two rows, each becoming a
block with a header, a local dictionary, a Merkle leaf, a manifest `Entry`
and a file in the generation directory. ESTIMATE: at 300 bytes of fixed
overhead per block that is 30 GB of overhead against about 8 GB of payload,
and 10^8 files, which no filesystem in the deployment path will hold.

**Proposal: bucket by (predicate, PARENT), with the leaf graph as a column
value.** The bucket key becomes `(predicate, parentOf(graph))` where
`parentOf` is the declaration's nearest declared ancestor of the row's graph
name, and the row keeps its own leaf graph in the existing IBK graph column.
Consequences:

* Block count is driven by the size cuts, not by the leaf count. MEASURED
  baseline: 1,543,478,120 bytes of skosdex give 3,306 entries. Scaling that
  ratio to 65 GB gives about 140,000 blocks — the same order as today's
  per-scheme graphs, which is the point.
* A block's `graphSet` now has many members again, so §4.3 replaces it.
* `PredicateQuadBlocksTheorems.bucket_one_graph` becomes
  `bucket_one_parent`: every row of a bucket has the same `parentOf`. The
  proof shape is unchanged — it is a property of `keyOf`.
* `GRAPH <parent> { ?s <p> ?o }` still reads exactly the blocks of one
  bucket key, which is the property the (predicate, graph) key was
  introduced for.
* `GRAPH <leaf> { ?s <p> ?o }` reads the parent's blocks and filters rows by
  the graph column. That is a widening, and §4.4 is how it is narrowed back.

Rules 3 and 4 are the reason the leaf key fails rather than merely being
inefficient. With the key (predicate, LEAF), every run holds one or two rows,
so rule 3 retains every run — no run ever reaches `minBatchRows` — and the
carried-row counter climbs to `maxCarriedRows` within a few batches, at which
point rule 4 publishes every open run at whatever size it has reached. The
packer then emits millions of one-row and two-row blocks and holds a million
open runs in memory between flushes, which is the memory curve of
`docs/designissues/2026-09-05-shard-pack-profile-and-memory.md` with a much
worse constant. With the key (predicate, PARENT), a run holds a scheme's rows
for one predicate, reaches `minBatchRows` in the ordinary case, and rules 3
and 4 keep the behaviour they have today: they were written for a source with
hundreds of thousands of PREDICATES, and the parent key keeps the bucket
count in that range instead of moving it to the leaf count. Neither rule
changes; the key does.

The parent level is a declaration choice: with a three-level pattern the
bucket may key on the middle level or the top. The rule to state is that the
bucket key is the SHALLOWEST declared ancestor whose expected block size is
below the cut, which is a packer statistic, not a semantic choice.

### 4.2 The term dictionary and the graph column

The graph column already holds a block-local term ID, so the per-row cost is
already small; the cost is the DICTIONARY entry for each distinct graph IRI
in each block that mentions it.

ESTIMATE, full IRI per dictionary entry: a leaf IRI of about 55 bytes, a
concept appearing in about 10 predicate blocks, 14 million concepts —
14e6 × 10 × 55 ≈ 7.7 GB of dictionary devoted to graph names, against a
42 GB generation.

ESTIMATE, template instantiation: store the graph column value as a template
id plus the variable values, and put the values that are constant across the
block — `{scheme}`, which is constant by construction under §4.1 — in the
block header. The per-entry cost falls to a template byte plus the
`{concept}` value. When `{concept}` is the local name of a subject IRI the
block's dictionary already holds, the value can be a reference to that
dictionary entry: about 5 bytes. 14e6 × 10 × 5 ≈ 700 MB. A saving of about
7 GB on a 42 GB generation, ESTIMATED, not measured.

The cost of the template form is a wire format change: the graph column's
term encoding gains a case, which is a new IBK wire version (11), and the
decoder must reject a template id the manifest's declaration does not
define. The cost of the full-IRI form is zero format change and about 7 GB.
This is open decision 3.

Note that the template form makes the dictionary's graph entries depend on a
declaration stored outside the block. The project rule from
`skills/shardborough-storage/SKILL.md` — encoder admission equals decoder
admission — then requires the declaration to be committed WITH the
generation (§6, slice 1) and its digest to be in the manifest, so a block
cannot be decoded against a different declaration than it was written under.

### 4.3 The manifest: `graphSet` becomes a graph SPAN

`Entry.graphSet : List GraphName` cannot hold a leaf set of millions. Two
candidate replacements:

**(a) A pattern-ordered interval.** Add to `Entry`:

```
graphSpan : Option (Nat × List UInt8 × List UInt8)
```

the template id and the smallest and largest GRAPH KEY in the block, each
truncated to `zoneBytes`, where a graph key is the version-2 wire encoding
of the graph name and the order is `lexLe`. This is the exact shape of
`subjectZone` and `objectZone`, and `zoneKeepsEntry` is the function that
tests it. A constant parent `<p>` resolves to the interval
`[key(<p>), key(<p> ++ 0xFF…)]`, which is a prefix range because level-1
expansion never emits `/` and the template's separator literal orders below
every expansion. An entry is kept when the intervals intersect.

Under §4.1 the block's graph names all lie below one parent, so the interval
is exactly the parent's range and the test is exact for `GRAPH <parent>` and
conservative for `GRAPH <leaf>`.

**(b) A per-block graph presence index**, a sidecar over the block's
distinct graph names, so that `GRAPH <leaf>` is decided without reading
rows. This is the same shape as the literal 3-gram index (LGI1): a candidate
filter, with the planner re-checking the rows. Note that the tag `GBI1` is
already the geometry bounding-box index of SBM9, so a graph index needs its
own tag — `GRI1` is proposed.

**Recommendation: (a) first, (b) later.** (a) costs two fields on `Entry`,
reuses a proved lemma shape, and delivers the parent case, which is the one
the pattern exists for. (b) is what makes the leaf case selective, and it is
only worth its bytes once a workload reads single leaves.

### 4.4 The graph collector

`ShardManifest.queryGraphNames?` today returns `Option (List GraphName)` and
`quadEntriesForQueryWithKeys` keeps an entry when its `graphSet` meets that
list. With millions of leaves the list form cannot be built. The collector
becomes:

```
queryGraphRanges? : Query → Option (List GraphRange)
```

where a `GraphRange` is either an explicit name (today's case, when no
declaration matches the name) or a template id with a key interval (a
constant parent under a declaration). The entry test becomes: the entry's
`graphSpan` intersects some range, or — for a pre-declaration generation
with an explicit `graphSet` — some name is in some range. The conservative
`none` behaviour is unchanged and is what every unproved shape falls back
to.

The soundness obligation is Lemma G of the planner-soundness record with
`restrictGraphs G` replaced by `restrictGraphs (namesIn ranges)`, plus T5:
the query reads the view of the parent, the view is the union of the leaves,
and the leaves are exactly the names in the interval. The interval step is
where the pattern's determinism (T2) is used — an IRI in the interval that
matched a DIFFERENT template would be in the range and not in the view.

### 4.5 The per-triple case: a derivable graph column

Under a per-triple pattern the graph name is a function of the row. So the
graph column can be omitted from the block and computed by the reader. That
is 219 million column values not stored, and it is a theorem obligation, not
a trick: the reader's reconstruction must equal the packer's naming
function, which is T6 plus a `namingRoundTrip` guard in the block codec.
The cost is that the reader must run the canonical form and the hash for
every row it returns a graph name for, so it is worth it only for a store
whose queries mostly do not bind `?g`. Deferred (§6).

### 4.6 Activation and the delta log

* **Activation** (`Harness/ShardActivate.lean`, `verifyQuadEntry`) checks the
  manifest's `graphSet` against the block header's graph set position by
  position. With a span it checks instead that every graph name in the block
  lies inside the span and that the span's bounds are attained. That is a
  scan of the block's distinct graph names, which activation already reads.
* **Delta log.** A per-leaf update is small and frequent, which is what the
  DLOG framing is for. Two additions: a graph-scoped tombstone, so that
  `DROP GRAPH <leaf>` is one record rather than 15 delete records; and,
  under `dropCascade`, a SPAN tombstone for `DROP GRAPH <parent>`, which is
  one record for a subtree of any size. A span tombstone must carry the
  declaration digest, because which leaves it covers depends on the
  declaration.

### 4.7 What a skosdex per-concept instance looks like

ESTIMATES, from the measured baselines above, all to one significant figure:

| Quantity | Per-scheme (today's shape) | Per-concept, full-IRI graph column | Per-concept, template column |
|---|---|---|---|
| Named graphs | 717 | about 14 million | about 14 million |
| Quads | about 219 million | same | same |
| Blocks | about 140,000 | about 140,000 (bucket by (predicate, parent)) | same |
| Generation bytes | about 42 GB | about 50 GB | about 43 GB |
| Manifest entries | about 140,000 | same | same |
| Manifest bytes | about 140,000 × 100 B ≈ 14 MB | plus 2 span fields ≈ +5 MB | same |
| Pack time at 2.47 MB/s | about 7.3 h | about 7.3 h | about 7.3 h |

The row that matters is the block count: it does not move, which is the
whole argument for §4.1. The row that is least trustworthy is the
generation-bytes column, which carries the §4.2 estimate and no measurement.

---

## 5. Interop

### 5.1 Solid and LWS

A Solid storage with one resource per record IS this pattern in another
specification. [Solid Protocol §4.2](https://solidproject.org/TR/protocol#resource-containment),
quoted in `L4Factoidal/Solid/Server/Containment.lean`:

> "There is a 1-1 correspondence between containment triples and relative
> reference within the path name hierarchy."

That is T2 and T1 for the LDP case: `parent?` gives a path at most one
container (`containerOfChildUnique`), and containment is read off the path
hierarchy of [RFC 3986 §5](https://www.rfc-editor.org/rfc/rfc3986#section-5),
which is the same construction as `Template.extendedBy` restricted to one
extra segment.

**Can one declaration serve both?** Yes, with one distinction kept explicit.
Take the leaf template's instantiation to be the resource URI, so graph name
= resource URI. Then:

* the Solid/LWS side answers a container GET with the CONTAINMENT TRIPLES —
  [LDP 1.0 §5.2](https://www.w3.org/TR/ldp/#ldpc) defines a container's
  representation as containment triples plus the container's own triples,
  and NOT as the union of its members;
* the SPARQL/GSP side answers `GRAPH <parent>` with the VIEW, the union.

So one declaration, two exposures, and the parent's OWN triples in the RDF
view are exactly the containment triples the LDP side serves. That is a
tidy identification and it is a proposal, not a landed behaviour:
`containmentTriples` and `view` are different functions today, and making
the first the parent's own graph is the work.

The remaining difference is depth. LDP containment is the DIRECT child
relation; `below` is its reflexive-transitive closure. A container hierarchy
of depth three gives `ldp:contains` two levels and `below` all of them.

### 5.2 Graph Store Protocol

§2.6 covers the operations. The addition here is discovery: a client that
fetches a leaf should be able to find the parent. Use a
[Link header](https://www.rfc-editor.org/rfc/rfc8288) with `rel="up"` on a
leaf response, and `rel="describedby"` to the declaration document. The
Solid host already reads and writes Link fields per RFC 8288, so the
mechanism is in the tree.

### 5.3 Service description

[SPARQL 1.1 Service Description §5](https://www.w3.org/TR/sparql11-service-description/)
has `sd:availableGraphs` and `sd:namedGraph`, which enumerate. Fourteen
million `sd:NamedGraph` nodes is not a description. The declaration is
published INSTEAD, as a small graph naming the templates and the composition
edges, with local vocabulary — `fct:graphTemplate`, `fct:composesInto`,
`fct:enumerates` — declared as an extension in the service description and
marked in `docs/w3c-glossary.md` as local, not specification, vocabulary.
`sd:UnionDefaultGraph` stays available and independent (§2.4).

The `enumerate = leaves` default (§2.2) makes this publication necessary
rather than optional: it is the only way a client learns that `GRAPH
<parent>` will be answered.

---

## 6. Migration and measurement

### Slice 1 — the declaration, and only that

Declaration as a SIDECAR of the generation, not a field of the manifest:
`graphs.gpat`, one template per line plus the composition edges, with its
SHA-256 recorded in the manifest's metadata block. A sidecar avoids a
manifest wire-version bump for a slice that changes no block byte, and the
digest is what §4.2 requires for encoder/decoder agreement.

Gate: `Template.wf` and `Decl.wf` `#guard`s, plus the matcher `#guard`s
already in the sketch. Labelled: "graph-pattern declaration guards: N pass,
0 fail (out of N)".

### Slice 2 — the collector, conservative

`queryGraphRanges?` (§4.4) alongside `queryGraphNames?`, returning `none`
whenever a declaration is absent or a name does not match, so an existing
generation's behaviour does not change. `graphSpan` on `Entry` behind the
next SBM version, written by the packer and checked by activation.

Gate: the existing `l4block-quad-query` suite unchanged, plus new `#guard`s
for the interval test. Labelled with pass/fail out of the suite size.

### Slice 3 — the executable equivalence probe

The theorem that must be executable before any of this is trusted is T5.
Probe: take the W3C SPARQL 1.1 query evaluation test datasets, split each
one by a synthetic per-record key (the subject IRI's local name), run every
test's own query text against (a) the original dataset and (b) the split
dataset viewed through the declaration, and compare the result sets by the
suite's own comparison. Every test whose query names no graph must give the
same answer; a test naming a graph is run with the parent name substituted.

Gate: "graph-pattern equivalence probe: N pass, 0 fail (out of N)", with the
denominator being the tests the split applies to and the rest reported as
not applicable. A failure here is a defect in the design, not in the
implementation, and stops the slice.

### Slice 4 — the scale measurement

A skosdex per-concept pack on the Fly path of `deploy/fly/skosall/`, one
leaf per concept, measuring: block count, manifest bytes, generation bytes,
dictionary bytes attributable to graph names, pack throughput, and the
latency of `GRAPH <scheme>` and `GRAPH <concept>` queries. This replaces
every ESTIMATE in §4.7 with a measurement, and the estimates are written
down here so that the comparison is a check on the reasoning rather than a
new set of numbers.

### Deliberately deferred

* Per-triple patterns in the packer, and the derivable graph column (§4.5).
* The graph presence index sidecar `GRI1` (§4.3 option b).
* `routeInsert` and write cascade (§2.5).
* `enumerate = parents` and `enumerate = all` (§2.2).
* The decision procedure for template overlap (§1.2); the first slice uses
  an admission test over the declared templates and the stored names.
* Making the LDP containment triples the parent's own graph (§5.1).
* Anything about federated composition — a parent whose leaves live in
  another service.

---

## 7. Proposed paragraph for `skills/shardborough-storage/SKILL.md`

Not applied here; the skill is unedited. Proposed for the section after
"Block selection":

> **Named-graph IRI patterns.** A generation may carry a declaration sidecar
> (`graphs.gpat`) of RFC 6570 level-1 templates plus composition edges, which
> says that `https://s.example/g/{scheme}/c/{concept}` composes into
> `https://s.example/g/{scheme}`. It changes what a graph NAME denotes and
> nothing else: `GRAPH <parent>` reads the union of the graphs below the
> parent, `GRAPH ?g` enumerates leaves only by default, and `DROP GRAPH
> <parent>` cascades. Two storage consequences follow and are what the
> declaration is for. The packer buckets quads by (predicate, PARENT) rather
> than (predicate, graph), so a store with fourteen million leaf graphs has
> the same block count as one with seven hundred; and the manifest carries a
> graph SPAN — a template id plus the smallest and largest graph key, in the
> shape of `subjectZone` — instead of a `graphSet` list, so the graph
> collector resolves a constant parent to an interval rather than to a list
> it cannot build. The declaration's digest is in the manifest because the
> graph column may encode a template instantiation, and encoder admission
> equals decoder admission. Design record:
> `docs/designissues/2026-09-07-hierarchical-named-graphs.md`.
