# Virtual named graphs — design notes

Status: **exploration**. Companion to
[`roaring_parquet_notes.md`](roaring_parquet_notes.md), which covers
the broader Roaring/Parquet/COTTAS/ID-encoding landscape; this file
zooms in on virtual named graphs as a feature in their own right.

Date: 2026-05-06.

> **Path note.** Sibling file at `design_issues/virtual_ngs.md` per
> request. Repo convention is `docs/designissues/YYYY-MM-DD-…`; same
> path question as the companion doc, deferred.

---

## 1. Why this is a separable doc

Virtual NGs interact with most of the rest of the architecture
(graph-IRI ID encoding, posting-list scope, ID width, SPARQL
semantics, update / invalidation, federation, …). The interactions
are stronger than any single one of those topics, so the feature
deserves its own page rather than being a footnote inside the
ID-encoding section.

The crisp prompt that triggered this:

> A SPARQL query over arbitrary quads might imply a NG grouping
> policy. As a corpus grows, some of its content might be
> self-referential about its graph structure (e.g. pages on sites
> that are AboutUs pages). If that data is in a graph in the
> corpus, can it be wired into the indices?

The short answer is yes and the rest of this document is "but be
deliberate about how."

---

## 2. The spectrum: declarative ↔ inferred

There are at least four distinct ways a virtual NG's membership can
be specified. They are not mutually exclusive; a real system likely
supports several.

### 2.1 URI-shape based (structural)

Membership is a function of the graph IRI string itself: prefix,
suffix, regex, segment-pattern. Examples:

- `https://acme.com/data/2024-*` → "all of 2024."
- `urn:wikidata:Q*` → "all entity graphs."
- `https://*.acme.com/data/*/about` → "all AboutUs pages across
  subdomains."

Pure structural; no data read needed. Cheap to evaluate, cheap to
build indexes for. Covered in §9 of `roaring_parquet_notes.md`.

### 2.2 Explicitly declared via configuration

A config file or environment variable lists virtual NGs and their
membership rules. Operator-controlled; out-of-band from the data;
requires redeploy / restart to change.

### 2.3 Declared in a metadata graph (corpus-internal)

The corpus contains a designated graph (e.g.
`<urn:factoidal:meta:virtual-ngs>` or some equivalent IRI) that
itself contains RDF describing the virtual NGs. The engine reads
the metadata graph and acts on it. **Updates to the metadata graph
update the virtual NG configuration without restart.**

This is the "data is policy" pattern; see §6.

### 2.4 Data-content inferred

Membership is a function of *triples in the data*. "All graphs `g`
such that `EXISTS { GRAPH ?g { ?s a schema:AboutPage } }`."

This requires the engine to read the data to determine membership,
which is the bootstrap question (§5).

### 2.5 Workload inferred

The query log is analysed to detect frequent groupings; the engine
proposes (or auto-creates) virtual NGs to optimise them. Adaptive,
ML-flavoured, far enough from anything currently in scope that it's
mentioned for completeness only.

### 2.6 The hybrid framing

Real systems mix these. A reasonable target architecture:

| Layer | Source | Cost to evaluate | Cost to maintain |
|---|---|---|---|
| URI-shape | structural | O(log N) range scan | none |
| Config-declared | operator | as below per rule | manual |
| Metadata-graph-declared | data | as below per rule | follows graph updates |
| Data-content-inferred | full SPARQL | full membership query | refresh policy |
| Workload-inferred | analyser | varies | not in scope |

The interesting feature of this framing is that **membership
ultimately resolves to a set of physical graph-IDs**, regardless of
how it was specified. That set is a bitmap. Roaring is the natural
representation; the upstream-source heterogeneity becomes
homogeneous at the bitmap layer.

---

## 3. The "self-describing corpus" pattern

The user's AboutUs example is the canonical case for §2.4 driven by
§2.3: the corpus contains *both* the data and the policy that
defines virtual NGs over the data.

Concretely (vocabulary sketch, not normative):

```turtle
@prefix vng:    <http://factoidal.example/virtual-ng#> .
@prefix schema: <http://schema.org/> .
@prefix :       <http://acme.com/data/> .

# Policy lives in a designated metadata graph
GRAPH <urn:factoidal:meta:virtual-ngs> {

  :about-pages a vng:VirtualNamedGraph ;
    rdfs:label "AboutUs pages across the corpus" ;
    vng:membership-query """
      SELECT ?g WHERE {
        GRAPH ?g { ?s a schema:AboutPage }
      }
    """ ;
    vng:refresh-policy vng:OnUpdate ;
    vng:cache-bitmap true .

  :january-2024 a vng:VirtualNamedGraph ;
    vng:uri-shape-include [
      vng:prefix "https://acme.com/data/" ;
      vng:suffix-pattern "2024-01-*"
    ] ;
    vng:cache-bitmap true .

  :january-2024-about-pages a vng:VirtualNamedGraph ;
    vng:intersect-of ( :about-pages :january-2024 ) .
}

# Data lives in physical graphs
GRAPH <https://acme.com/pages/foo/about> {
  :foo a schema:AboutPage ;
       schema:name "About Foo" .
}

GRAPH <https://acme.com/pages/bar/about> {
  :bar a schema:AboutPage ;
       schema:name "About Bar" .
}
```

The corpus is now describing — *in standard RDF, inside itself* —
how its own indexes should be organised. Adding a new virtual NG is
`INSERT DATA` into the policy graph; no config edits, no restarts.

This pattern interacts well with SHACL: a shape stating "things of
type `schema:AboutPage` should be group-queryable" is a similar
declaration in standard vocabulary, and could in principle be lifted
into a virtual NG automatically.

It also dovetails with VoID
(<https://www.w3.org/TR/void/>) and DCAT — both of which describe
RDF datasets in RDF. A corpus that already has VoID/DCAT metadata
could have its virtual NGs derived partly from existing metadata
without inventing new vocabulary.

---

## 4. The bootstrap problem

Data-driven virtual NGs (§2.4) have a chicken-and-egg in the cold
case:

- To know which graphs match the membership query, the engine must
  evaluate the query.
- Evaluating efficiently needs indexes.
- Building indexes might want to know about virtual NGs (e.g. so
  they can be pre-aggregated).
- Knowing virtual NGs requires evaluating membership queries.

Standard resolution — same as SQL materialized views, Lucene
custom analyzers, RocksDB column families — is **two-phase
startup**:

1. **Phase 0: physical indexes.** S/P/O/G posting lists (and any
   sidecars) per *physical* graph. No virtual NG awareness. This
   is the same work the engine does without the virtual-NG feature.

2. **Phase 1: read declarations.** From config, from the metadata
   graph, or both. Build an in-memory list of declared virtual
   NGs and their membership rules.

3. **Phase 2: evaluate URI-shape declarations.** Cheap range scans
   on graph-IRI dictionaries. Materialise membership bitmaps.

4. **Phase 3: evaluate data-driven declarations.** Run each
   declaration's membership query against the Phase-0 indexes;
   collect the resulting graph-IDs; build a Roaring membership
   bitmap.

5. **Phase 4: derived virtual NGs.** Set-algebra over the bitmaps
   built in Phases 2/3 (`vng:intersect-of`, `vng:union-of`,
   `vng:difference-of`).

6. **Phase 5: optional pre-aggregation.** Per virtual NG with
   `vng:cache-bitmap true` and high enough query frequency,
   compute and cache the union of member graphs' posting lists.

Crucially, **none of this requires special index machinery beyond
what the corpus already needs for normal SPARQL queries**. A
membership query is just SPARQL.

---

## 5. What goes in the indexes per virtual NG

Three layers, each independently cacheable:

### 5.1 Membership bitmap

Roaring over physical graph-IDs. The set of graphs that are
"members of" the virtual NG. Always cheap to maintain
incrementally (one bit flip on a bound change).

**Open question**: 32-bit Roaring (assuming graph-ID universe ≤ 4B)
or 64-bit (if we go QLever-tagged)? See `roaring_parquet_notes.md`
§7. The graph-membership-bitmap case is one of the strongest
arguments for engaging with 64-bit Roaring, because it interacts
with graph-ID encoding (§7.4 and §9.4 of that doc).

### 5.2 Aggregated posting lists (optional)

For virtual NG `V` and term `t`, pre-compute
`union over g ∈ V of g.posting[t]`. Materialised view; speeds up
`GRAPH <virtual:V> { ?s ?p ?o }` at memory cost. Per-virtual-NG
choice — like SQL indexed views.

### 5.3 Aggregated cardinality estimates

For query planning. Per virtual NG, per `(s, p, o)` slot binding,
estimated result size. Cheap to derive from the per-physical-graph
cardinality estimates that an evaluator already maintains
(`Mem5`-style).

---

## 6. SPARQL semantics — questions, not answers

Here be dragons. SPARQL 1.1 doesn't know about virtual NGs;
introducing them affects:

### 6.1 `GRAPH` position

`GRAPH <virtual:about-pages> { ?s ?p ?o }` — what does this mean?

- Option A: union over member physical graphs. Natural. Result
  triples might be duplicated if the same triple appears in multiple
  member graphs; default-graph-style or quad-style?
- Option B: a fresh "virtual graph" with provenance information,
  binding to `<virtual:about-pages>`.

### 6.2 `GRAPH ?g { ... }` enumeration

Does `?g` ever bind to a virtual IRI?

- If yes: the engine returns both physical and virtual graph IRIs
  in the binding. This is a non-standard extension; SPARQL 1.1
  expects `?g` to range over named graphs in the dataset.
- If no: virtual NGs are query-time-only and never observable as
  bindings. Easier to specify; less expressive.

A hybrid: `?g` binds to physical IRIs by default; an extension
function (e.g. `factoidal:virtualGraphsOf(?g)`) lets users opt in.

### 6.3 Non-`GRAPH`-position uses

`<virtual:about-pages>` as a subject or object? Probably should be
an error or returns no rows — virtual NG IRIs aren't terms in the
corpus, they're catalog entries.

### 6.4 Update operations

`INSERT DATA { GRAPH <virtual:about-pages> { ... } }` — where do
the new triples actually land?

- Option A: error. Virtual NGs are read-only.
- Option B: a "default writable target" rule per virtual NG. E.g.
  the virtual NG declaration carries `vng:default-write-target
  <https://acme.com/inbox>`.
- Option C: write to all physical members. Almost never what you
  want.

Option A is the safe default. Option B is the more useful one;
needs vocabulary support.

### 6.5 `FROM NAMED <virtual:...>` in dataset description

If `FROM NAMED` lists a virtual NG, presumably the dataset is the
union of member physical graphs as named graphs. The bindings of
`?g` in subsequent `GRAPH ?g` patterns then range over those
physical IRIs (not the virtual one). Probably the natural
semantics.

---

## 7. Update / invalidation

A virtual NG defined by data needs its membership bitmap kept in
sync as the data changes. Granularity choices:

### 7.1 Refresh policies

- **`vng:OnUpdate`** — eager: every triple update that could affect
  membership triggers re-evaluation. Expensive but always fresh.
- **`vng:Periodic`** — scheduled: re-evaluate every N seconds /
  minutes / on cron. Stale between refreshes.
- **`vng:OnDemand`** — lazy: re-evaluate when a query references
  the virtual NG and the cache is older than some threshold.
- **`vng:Manual`** — operator triggers refresh explicitly via an
  admin endpoint.

### 7.2 Incremental maintenance

Eager refresh doesn't have to mean "re-run the full membership
query." For monotonic membership rules (the common case for the
AboutUs-style example), incremental updates are linear in the
number of changed triples:

- Triple `(<g_id>, schema:AboutPage)` inserted in graph `g`?
  → If `g` was not already a member, set bit `g` in the
  membership bitmap.
- Last `?s a schema:AboutPage` triple removed from graph `g`?
  → Clear bit `g`.

For non-monotonic rules (e.g. "graphs with *exactly one* AboutPage")
incremental maintenance gets harder; full re-evaluation may be
unavoidable.

This is exactly the territory where Roaring shines: bit-flip
updates are O(1) amortised, container conversions only happen at
the cardinality boundary.

### 7.3 Subscription / change-feed

If the engine emits a change feed (some kind of "this triple was
added/removed in graph G" stream), virtual NG maintenance becomes
a stream-processing job. Out of scope as a first step but worth
keeping in mind for the architecture.

---

## 8. Implications for ID encoding

The §9 of `roaring_parquet_notes.md` discussed graph-ID encoding
choices oriented around URI-shape factoring (tagged tuple IDs with
prefix-family + suffix-family in the high bits). That works for
URI-shape virtual NGs but **doesn't help data-driven ones** —
their membership cuts across URI shape arbitrarily.

If we expect a meaningful fraction of virtual NGs to be data-driven
(the AboutUs example suggests yes), graph-ID encoding probably
should not over-commit to URI-shape factoring. Two viable shapes:

### 8.1 Sorted-position graph-IDs + supplementary bitmaps

- IDs allocated by sorted IRI position. URI prefix queries =
  contiguous range scans on the dictionary. Cheap.
- Suffix queries: parallel reverse-IRI dictionary, separate ID
  space, translation table. Cheap if bounded.
- Data-driven virtual NGs: ordinary Roaring membership bitmaps over
  graph-IDs. The bitmaps may be less clustered than URI-shape ones
  (run containers less common), but array/bitmap containers are
  fine.

### 8.2 Tagged tuple graph-IDs (URI-shape factored)

- High bits = prefix family, middle = suffix family, low = unique.
- URI-shape queries are bitmask tests.
- Data-driven virtual NGs: cut across the structure; membership
  bitmaps are typically array containers, possibly bitmap
  containers, rarely run containers.
- Bitmask filtering still works for the URI-shape projection;
  data-driven membership is a *separate* bitmap, not derived from
  the encoding.

Either way, **Roaring is the unifying primitive**: regardless of
how a virtual NG is defined (URI-shape, declared, data-driven,
workload-inferred), its membership ends up as a Roaring bitmap and
downstream consumers see the same interface.

This actually changes the strategic argument slightly: even if
data-driven virtual NGs would be "wasted" on the URI-shape
encoding, they're still cheap to maintain because the bitmap layer
is uniform. So the encoding choice is not as load-bearing as it
initially seemed. The real question is whether *URI-shape virtual
NGs are common enough* to justify the extra encoding complexity, or
whether sorted-position IDs + Roaring everywhere is a simpler and
nearly-as-fast story.

---

## 9. Vocabulary sketch (illustrative, not normative)

Assembling the pieces from the example in §3:

```turtle
@prefix vng:  <http://factoidal.example/virtual-ng#> .
@prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .
@prefix xsd:  <http://www.w3.org/2001/XMLSchema#> .

vng:VirtualNamedGraph a rdfs:Class .

# --- Membership specification ----------------------------------

vng:uri-shape-include    a rdf:Property .   # URI-shape filter
vng:uri-shape-exclude    a rdf:Property .

vng:prefix               a rdf:Property .   # string
vng:suffix               a rdf:Property .   # string
vng:prefix-pattern       a rdf:Property .   # glob
vng:suffix-pattern       a rdf:Property .   # glob
vng:iri-regex            a rdf:Property .   # regex (last resort)

vng:membership-query     a rdf:Property .   # SPARQL SELECT
vng:membership-ask       a rdf:Property .   # SPARQL ASK template

vng:include-explicit     a rdf:Property .   # rdf:List of physical IRIs
vng:exclude-explicit     a rdf:Property .

# --- Composition -----------------------------------------------

vng:union-of             a rdf:Property .   # rdf:List of vng:VirtualNamedGraph
vng:intersect-of         a rdf:Property .
vng:difference-of        a rdf:Property .

# --- Maintenance / caching -------------------------------------

vng:refresh-policy       a rdf:Property .   # vng:OnUpdate | vng:Periodic | vng:OnDemand | vng:Manual
vng:refresh-interval     a rdf:Property .   # xsd:duration

vng:cache-bitmap         a rdf:Property .   # xsd:boolean
vng:cache-aggregate-postings a rdf:Property .   # xsd:boolean

# --- Update routing --------------------------------------------

vng:default-write-target a rdf:Property .   # IRI of physical graph
vng:read-only            a rdf:Property .   # xsd:boolean

# --- Refresh-policy individuals --------------------------------

vng:OnUpdate    a vng:RefreshPolicy .
vng:Periodic    a vng:RefreshPolicy .
vng:OnDemand    a vng:RefreshPolicy .
vng:Manual      a vng:RefreshPolicy .
```

This is sketch level — picking it up would need real RFC-style
discussion, alignment with VoID/DCAT/SHACL where they overlap, and
agreement on extension conventions.

---

## 10. Worked examples

### 10.1 Temporal partition (URI-shape)

```turtle
:january-2024 a vng:VirtualNamedGraph ;
  vng:uri-shape-include [
    vng:prefix-pattern "https://acme.com/data/2024-01-*"
  ] ;
  vng:cache-bitmap true ;
  vng:read-only true .
```

Query:

```sparql
SELECT (COUNT(*) AS ?n)
WHERE { GRAPH <virtual:january-2024> { ?s ?p ?o } }
```

Engine: bitmask test on the graph-ID dictionary; aggregate counts
across matching physical graphs.

### 10.2 Per-entity AboutUs corpus (data-driven)

The example from §3. Engine:

1. Reads the policy from the metadata graph at startup.
2. Runs the membership query to populate the bitmap.
3. Subscribes to data updates that could affect membership
   (`?s rdf:type schema:AboutPage` insert/delete).
4. On a query like
   `SELECT ?name WHERE { GRAPH <virtual:about-pages> { ?s schema:name ?name } }`,
   iterates physical graphs in the bitmap, evaluates the inner
   pattern, unions the results.

### 10.3 Cross-source mirror (URI-shape, suffix-driven)

```turtle
:berlin-data a vng:VirtualNamedGraph ;
  vng:uri-shape-include [
    vng:suffix-pattern "/data/Berlin"
  ] .
```

Catches `http://dbpedia.org/data/Berlin`,
`http://yago.org/data/Berlin`, etc. Useful for federation: "the
union of all source mirrors' Berlin graph."

### 10.4 Composed virtual NG (intersection)

```turtle
:january-about-pages a vng:VirtualNamedGraph ;
  vng:intersect-of ( :january-2024 :about-pages ) .
```

Engine: bitmap intersection of the two cached membership bitmaps.

### 10.5 Per-tenant per-day (2-D)

```turtle
:foo-jan-2024 a vng:VirtualNamedGraph ;
  vng:intersect-of (
    [ a vng:VirtualNamedGraph ;
      vng:uri-shape-include [ vng:prefix "https://acme.com/tenant/foo/" ] ]
    [ a vng:VirtualNamedGraph ;
      vng:uri-shape-include [ vng:suffix-pattern "/day/2024-01-*" ] ]
  ) .
```

Engine: bitmap-intersect a "prefix-foo" set with a "suffix-2024-01"
set. This is the case where 64-bit tagged graph-IDs (with
independent prefix and suffix bitfields) make membership tests
trivial; with sorted-position IDs both sets need range scans on
their respective dictionaries first.

---

## 11. Interaction with federation

Federated SPARQL (`SERVICE`) gets interesting:

- A virtual NG could span graphs hosted at *remote* endpoints.
  Membership bitmap stores only the local-to-this-engine graphs;
  query evaluation does the local part natively and dispatches the
  remote part via `SERVICE`.
- A federated endpoint might publish *its* virtual NG declarations
  in a discovery document (probably VoID-shaped). Other engines
  could consume those declarations and reference them directly.
- Cached SERVICE results ←→ row-set bitmaps ←→ virtual NGs at the
  remote: there's a coherent story here about "every set we ever
  compute is a Roaring bitmap, including remote query results."
  Out of scope as a starting feature.

---

## 12. Comparison — what other systems do

Brief, to show this is well-trodden architectural territory rather
than novel invention:

| System | Equivalent feature | Notes |
|---|---|---|
| SQL (SQL Server, PostgreSQL, Oracle) | Materialized views | Standard pattern; refresh policies; query rewriting |
| Apache Jena Fuseki | Assemblers + dataset descriptions | Configurable but mostly static |
| Stardog | Virtual graphs (over external sources) | Different feature: federation, not corpus-internal grouping |
| Apache Jena TDB | No equivalent | |
| Virtuoso | Quad-store with named graph URIs; some grouping via prefix | No first-class virtual NG concept |
| GraphDB | Repository templates | Static configuration |
| Wikidata Query Service | No equivalent | All in one default graph |
| Apache Solr / Elasticsearch | "Aliases" (collection aliases) | Closest analogue: an alias maps to a set of physical collections; queries against the alias union them |
| Lucene / Tantivy | Index segments + alias | Same shape as Solr/Elasticsearch |
| Snowflake | Materialized views + zero-copy cloning | Different problem, partially relevant |

The Solr/Elasticsearch *alias* pattern is probably the closest
operational analogue: an alias is a logical collection name that
resolves to a set of physical collections; queries to the alias are
unioned. Adding an "alias" RDF semantics means: a virtual NG IRI
that the SPARQL engine resolves to a set of physical NGs.

---

## 13. Open questions

These should be tracked. None are answered here.

### Architecture

- Are virtual NG declarations stored in a designated graph IRI
  (which one?), in config, or both?
- Are virtual NGs first-class IRIs (`?g` can bind to them) or
  query-time-only?
- Do virtual NG IRIs have a prefix/scheme convention
  (`virtual:`, `urn:factoidal:vng:`, …) or are they just regular
  IRIs?

### Membership

- What's the membership-query language? Full SPARQL? A restricted
  subset (no virtual NGs in the query, to avoid recursion)?
- Are rules monotonic by default (allowing incremental maintenance),
  or arbitrary?
- Recursion: can a virtual NG depend on another virtual NG? (`vng:union-of`
  suggests yes, but membership query referencing another virtual
  NG is trickier — risk of cycles.)

### Refresh

- Default refresh policy: lazy (`OnDemand`) or eager (`OnUpdate`)?
- How is refresh expense bounded? (A `vng:OnUpdate` with a heavy
  membership query could regress every write.)
- Can refresh be deferred / coalesced into batches?

### Update

- Is `INSERT INTO GRAPH <virtual:...>` an error, or routed via
  `vng:default-write-target`?
- Does updating the metadata graph (changing a virtual NG
  definition) trigger automatic re-evaluation, or require an
  explicit refresh?

### SPARQL semantics

- `GRAPH ?g`: does `?g` bind to virtual NGs? If so, is that
  standard or via an extension function?
- Can virtual NG IRIs appear as triples' subjects/objects, or only
  in `GRAPH` position?
- `FROM NAMED <virtual:...>`: union of member physical graphs as
  named graphs, yes?

### Storage

- Is the membership bitmap persisted on disk (sidecar to the
  metadata graph?) or rebuilt at startup?
- Is aggregate posting-list pre-computation per-virtual-NG a config
  option, an automatic decision based on usage, or never?

### Vocabulary

- Reuse VoID / DCAT terms where they overlap, or define a fresh
  vocabulary with mappings?
- Alignment with SHACL: can a SHACL shape implicitly define a
  virtual NG?

### Identity / encoding (cross-ref)

- Does adding virtual NGs change the graph-ID encoding decision
  (`roaring_parquet_notes.md` §9)? Probably yes — see §8 above.
- Does the membership-bitmap-over-graph-IDs use case argue for or
  against engaging with Roaring64?

---

## 14. Where this connects to the broader plan

If virtual NGs are ever wired up, they touch:

- **Roaring** as the membership-bitmap representation
  (`roaring_parquet_notes.md` §6.4).
- **Graph-ID encoding** (§8 above; cross-refs §9 of the parent doc).
- **SPARQL evaluator** (`SPARQL11.Algebra.fst`) to handle
  `GRAPH <virtual:...>` patterns.
- **Storage** — metadata graph storage, membership-bitmap
  persistence, optional aggregate posting-list materialisation.
- **Update path** — `apply_insert_data` / `apply_delete_data` need
  to feed into virtual NG maintenance for `vng:OnUpdate` policies.
- **Federation / `SERVICE`** in the long run.
- **Format / community story** (`roaring_parquet_notes.md` §12) —
  if virtual-NG declarations are first-class data, they need a
  documented vocabulary, golden test files, and a conformance
  story like any other format.

---

## 15. Recommended next step (if/when we engage)

A worked end-to-end demo on a corpus small enough to inspect:

1. A synthetic corpus of, say, 5 physical graphs.
2. A metadata graph declaring 2–3 virtual NGs (one URI-shape, one
   data-driven, one composed).
3. A test that queries each via `GRAPH <virtual:...>` and verifies
   the result against ground truth.
4. A test that updates a triple and verifies the membership bitmap
   refreshes correctly.

This forces us to commit to one choice on each open question in §13
*for the demo*, exposing which choices are easy and which are
load-bearing. None of the choices need to be the final ones.

---

## 16. Revision history

- **2026-05-06**: First draft. Spun out of the conversation that
  produced `roaring_parquet_notes.md`. Captures the
  "declarative ↔ inferred" spectrum, the "self-describing corpus"
  pattern, the bootstrap two-phase startup, and the interaction
  with graph-ID encoding. Nothing decided.
