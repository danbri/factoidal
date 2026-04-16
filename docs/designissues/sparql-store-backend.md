# SPARQL Store Backend Notes

This note records the current direction for making SPARQL evaluation stop
assuming that an RDF graph is just a plain in-memory list of triples.

## Problem

Today the algebra layer effectively assumes:

```fstar
let graph_triples (g : rdf_graph) : list triple = g
```

That means:

- a graph is represented as a `list triple`
- triple-pattern evaluation scans that whole list
- BGP evaluation compounds the cost by repeating that scan pattern

This is acceptable for parser validation and small examples, but it does not
scale to larger corpora.

## Direction

Keep the SPARQL algebra and value semantics in F*, but put a storage/query
boundary underneath them.

The first implementation target is:

- keep the current list-backed representation working
- introduce a store-facing API for triple-pattern search
- make `eval_single_tp` call the store API rather than directly scanning the
  graph list

That gives us a seam for later backends such as HDT, HDTQ-style dataset
stores, and COTTAS-style columnar quad stores.

The same seam should also support future SQL-backed storage, especially:

- SQLite for compact local corpora and embedded deployments
- PostgreSQL for larger operational backends

The algebra should target a storage interface, not an HDT-only worldview.
That same interface family should be able to host:

- per-graph HDT stores
- dataset-native HDTQ-style stores
- dataset-native COTTAS-style columnar stores
- Parquet-like quad batch stores
- SQL-backed graph / dataset stores

## Corpus Shape

Factoidal should not be treated as one monolithic always-live SPARQL dataset.

The better model is:

- cold corpus
  - very large collection of separately named graph assets
- hot working set
  - the subset selected for a user, task, workflow, or query
- assembled query dataset
  - the temporary SPARQL-visible dataset formed from that working set

In that model:

- import adds another graph asset to the corpus
- import should not make every future query pay a tax for all prior imports
- HDT is a storage format for graph assets, not the whole corpus architecture
- selection and manifest metadata matter as much as raw triple storage

This means named graphs are not merely SPARQL syntax. They become units of:

- storage
- provenance
- indexing
- relevance selection
- caching
- trust/policy
- composition

## HDT Position

HDT should be treated as a physical storage backend, not as a parser
replacement.

For now the safer dataset design is:

- one manifested graph = one HDT artifact
- named graph identity lives in the corpus TOC / manifest layer
- the algebra asks a dataset backend for a graph handle
- the graph handle answers triple-pattern lookups

This avoids making correctness depend on HDT-native quad support.

For quad-aware storage, the native target should be an F*-defined HDTQ-style
dataset backend, not an opaque external engine. See also:

- [`hdtq-native-backend.md`](/home/danbri/working/sandbox/foaf25/codex/factoidal/docs/designissues/hdtq-native-backend.md)

For the current dataset-storage focus, COTTAS should be treated as a first-class
native target too:

- [`cottas-native-backend.md`](/home/danbri/working/sandbox/foaf25/codex/factoidal/docs/designissues/cottas-native-backend.md)

## Questions To Keep In Scope

### Can Factoidal serialize its own graphs to binary on-disk data?

Yes, in principle, but there are two distinct meanings:

1. Factoidal-specific binary persistence
2. Standard HDT-compatible serialization

The first is easier. We already own the RDF term and triple structures, so an
F*/OCaml backend could serialize:

- a term dictionary
- ID-based triples
- optional auxiliary indexes

The second is harder because it means conforming to HDT container and index
structure, not just inventing our own binary store.

Recommended stance:

- short term: use external HDT tooling for canonical HDT files
- medium term: define an internal binary graph representation that can also act
  as an in-memory or on-disk index
- long term: decide whether full HDT writing belongs inside Factoidal

### Can the HDT structure also serve as an in-memory ephemeral index?

Yes, conceptually.

The useful split is:

- logical SPARQL layer stays in terms/triples/solution mappings
- physical storage layer may use dictionary IDs and indexed triples

That physical layer could be:

- backed by an on-disk HDT
- backed by an in-memory index built from a few parsed FOAF files

So the abstraction should not be named too narrowly around files. It should be
closer to:

- graph store
- dataset store
- term encoding / decoding
- indexed triple-pattern search

This allows one API to cover:

- persisted HDT-backed graphs
- ephemeral in-memory indexed graphs
- future hybrid corpus/dataset handles

### Can one in-memory corpus contain several indexed ephemeral graphs?

Yes. The same store abstraction should support:

- one standalone in-memory graph store
- several named in-memory graph stores in one dataset store
- mixtures of in-memory and on-disk graph stores in one dataset view

That implies that `Corpus` eventually needs a runtime representation as well as
an on-disk layout. The runtime representation should not assume every graph
comes from an HDT file.

## Immediate Refactor Targets

1. Introduce `triple_pattern_bound`, `graph_store`, and `rdf_dataset_store`
   types in the algebra layer.
2. Implement a list-backed default store so current semantics stay unchanged.
3. Rewrite `eval_single_tp` to use `store_search`.
4. Add cardinality-estimate hooks for future BGP reordering.
5. Later, route named graph lookup through dataset stores backed by TOC/HDT
   metadata.

## Constraints

- Do not load HDTs into `list triple` just to keep the types simple.
- Do not make named-graph correctness depend on quad-native HDT support.
- Do not solve all property-path optimization before triple-pattern pushdown.
- Keep the verified algebra as the semantic source of truth.
