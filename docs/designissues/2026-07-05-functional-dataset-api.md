# A strictly functional dataset API for factoidal — design + landed slice

**Date:** 2026-07-05.
**Status:** implemented in this commit
(`npm/factoidal/fn.js`, `fn.d.ts`, `test/fn.test.js`). Not a proposal
for future work — this doc records what shipped and why, in the style
of [`2026-07-05-graphs-api-design.md`](2026-07-05-graphs-api-design.md).
**Owner's goal:** "a variant of the rdfjs api that is more strictly
functional, to exploit our F\* work and set us up for dataflow
applications."

## 0. The premise

Every extracted factoidal operation is a value-to-value function.
`RDF.Graph.Executable.fst`'s `rdf_dataset` is an immutable F\* record;
`parse_to_dataset`, `query`, `canonicalize_to_nquads` all take a value
and return a value — there is no mutation to expose, because F\* has
none to give. `RDF/JS DatasetCore`'s `add(quad)` / `delete(quad)`
methods are wrapper-side skeuomorphism: `rdfjs.js`'s `Dataset` class
implements them by splicing an internal array
([`rdfjs.js:450-458`](../../npm/factoidal/rdfjs.js)) — a correct
implementation of the RDF/JS spec, but one that papers over the fact
that nothing underneath actually mutates. Every `lib/api.js` call that
accepts a `Dataset` immediately calls `toNQuads()` on it
([`lib/api.js:172`](../../npm/factoidal/lib/api.js)) and hands a byte
string to the engine; the `Dataset` object's mutability is never
load-bearing at the engine boundary, only for callers who want the
familiar imperative shape.

`fn.js` makes the JS contract match the verified one: a frozen
snapshot type (`FnDataset`), free functions instead of methods (so
they compose — `filter(union(a, b), pred)` reads left to right), and
RDFC-1.0 canonical hashes promoted to a first-class, memoized value.
That last piece is what "dataflow applications" needs: content-addressed
identity lets a recompute step ask "did anything actually change?" in
O(1) instead of re-running a query to find out.

This is additive. `rdfjs.js` and `lib/api.js` are unchanged; `fn.js`
wraps the already-built `index.js` API (`require('./index.js')`) and
reuses `rdfjs.js`'s quad/term model rather than forking a second
serialization or parsing path — per rule #11, no new engine plumbing
lives here, only a frozen shape and pure composition on top of the JS
engine binding.

## 1. API surface

`FnDataset` — a frozen, de-duplicated snapshot of RDF/JS quads.
`Object.freeze` on the instance; every accessor is read-only
(`size`, iteration, `toArray()`, `toNQuads()`, `match()`); no method
mutates. Quads yielded by iteration are the same frozen `Quad`
instances `rdfjs.js`'s `dataFactory` already produces (`Quad`'s
constructor calls `Object.freeze(this)` —
[`rdfjs.js:107`](../../npm/factoidal/rdfjs.js) — so this is inherited,
not re-implemented).

Every constructor path funnels through one private helper,
`makeFnDataset(quadsIterable)`, which de-duplicates by N-Quads token
(`quadToNQuads`, the exact serializer `rdfjs.js` already uses for
engine interchange) and re-freezes every quad via `dataFactory.fromQuad`.
This is the one invariant the whole module leans on: **an `FnDataset`
is always a proper set of quads**, never a multiset, regardless of
which operation produced it.

Free functions (`fn.js`):

| Function | Shape | Notes |
|---|---|---|
| `fromDataset(dataset)` | `Dataset -> FnDataset` | snapshot a mutable RDF/JS `Dataset` |
| `toDataset(ds)` | `FnDataset -> Dataset` | materialize an independently-mutable copy |
| `parse(text, opts)` | `(string, opts) -> Promise<FnDataset>` | thin wrapper over `index.js`'s `parse` |
| `union(a, b)` | `(FnDataset, FnDataset) -> FnDataset` | set union, first-seen order |
| `difference(a, b)` | `(FnDataset, FnDataset) -> FnDataset` | quads in `a` not in `b` |
| `filter(ds, quadPred)` | `(FnDataset, Quad -> bool) -> FnDataset` | subset |
| `mapQuads(ds, f)` | `(FnDataset, Quad -> Quad) -> FnDataset` | transform + re-dedup |
| `query(ds, sparql, opts)` | `-> Promise<Bindings[] \| boolean \| FnDataset>` | SELECT/ASK/CONSTRUCT, same shape as `index.js`'s `query` |
| `entail(ds, regime)` | `(FnDataset, EntailRegime) -> Promise<FnDataset>` | materialized closure — see §5, this is *not* CONSTRUCT under the hood |
| `canonicalize(ds)` | `FnDataset -> Promise<string>` | RDFC-1.0 canonical N-Quads text |
| `hash(ds)` | `FnDataset -> Promise<string>` | sha256 hex of `canonicalize(ds)`, memoized |
| `equals(a, b)` | `(FnDataset, FnDataset) -> Promise<boolean>` | see §2's cost model |
| `graphs(ds)` | `FnDataset -> Array<[iri, FnDataset]>` | wraps `index.js`'s `graphs()` |
| `builder()` / `fromChunks(chunks)` | streaming seam, §7 |
| `cell(initial)` / `derive(fn, ...cells)` | dataflow primitives, §4 |
| `EMPTY` | constant | identity element for `union`/`difference` |

`capabilities()` is re-exported unchanged from `index.js` — the same
gate (npm-entry bundle present or not) applies, since `fn.js` does not
add or remove engine capability, only reshapes it.

## 2. Identity and equality — the cost model, stated honestly

RDFC-1.0 canonicalization is O(n log n) in the number of blank nodes
(the tie-breaking / hash-mixing pass over the graph — see
[`RDF.Canonical.fst`](../../formal/fstar/RDF.Canonical.fst) and the
HFDQ algorithm it implements). Computing a canonical hash is not free,
and pretending otherwise would violate the project's measurement
discipline (see [`perf-benchmarking`](../../skills/perf-benchmarking/SKILL.md)).
`fn.js`'s answer:

- **Hashes are computed on demand, never eagerly.** `hash(ds)` calls
  `canonicalize(ds)` the first time it's asked and nowhere else. No
  operation in this module (`parse`, `union`, `filter`, ...) triggers
  canonicalization as a side effect of running.
- **Memoized by `FnDataset` identity, not by content**, in a
  module-level `WeakMap` keyed on the frozen object — not a field on
  the object. This matters for the immutability claim: if the cache
  were an object field, "frozen" would be a partial lie (something
  inside the object still changes on first read). A side table lets
  `Object.freeze(ds)` mean what it says for the object's entire
  lifetime, while still avoiding recomputation. Concurrent callers
  before the first result lands share one in-flight `Promise` (the
  cache stores the promise, then overwrites it with the settled
  string), so two dataflow consumers asking for the same hash at the
  same time trigger one `canonicalize()` call, not two.
- **`equals(a, b)` tries the cheapest *conclusive* test first, not the
  cheapest test period** — a cheap but inconclusive test (e.g. "same
  size") can only ever produce a `false` short-circuit, never a `true`
  one:
  1. Different `size` → not equal. O(1).
  2. Both sides already have a memoized hash → compare hashes. O(1),
     no new canonicalization.
  3. Exact quad-set match (same terms and labels, via the same
     `quadToNQuads` tokens `makeFnDataset` uses for dedup) → equal.
     O(n). Never a false positive — identical tokens mean identical
     quads — so this is safe regardless of blank nodes.
  4. A non-match at step 3, **and neither dataset contains a blank
     node** → not equal, authoritatively. Ground quads have no
     relabeling to hide behind, so token inequality is graph
     inequality.
  5. A non-match at step 3 with blank nodes present → inconclusive
     (the graphs could still be isomorphic under relabeling), so this
     is where the module pays for canonicalization: `hash(a)` and
     `hash(b)`, then compare — the same charge `hash()` was already
     going to make for identity, not a second one.

  In short: `equals` falls back to size+quad-set comparison exactly
  when that comparison is cheaper *and correct* (no blank nodes, or an
  exact match at any size); it only pays for canonicalization when
  blank-node relabeling makes the cheap comparison unsound —
  soundness-gated cost minimization, not a heuristic that trades
  correctness for speed.

`toNQuads()` (inherited read accessor, not a free function) is
deliberately *not* identity — it is arrival-order, non-canonical
N-Quads text, useful for cheap debugging output and as `makeFnDataset`'s
own dedup substrate, but two isomorphic graphs with different
blank-node labels will not produce the same string from it. Nothing in
this module treats `toNQuads()` output as a cache key for anything
beyond its own within-instance dedup pass.

## 3. Interop with the mutable RDF/JS layer

`fromDataset(dataset)` snapshots a live `rdfjs.Dataset` — including one
still being mutated elsewhere — into a frozen, de-duplicated
`FnDataset`. `toDataset(ds)` is the inverse: a fresh `Dataset`
constructed from `ds.toArray()`, independently mutable and disconnected
from `ds` (mutating the result cannot reach back into the frozen
snapshot; `test/fn.test.js` asserts this directly). Every function
here that needs to call into the existing engine binding (`query`,
`entail`, `canonicalize`, `graphs`) goes through `toDataset()`
internally, since `lib/api.js`'s `toDocs()` only special-cases
`instanceof Dataset` ([`lib/api.js:171`](../../npm/factoidal/lib/api.js))
— reusing the existing entry point by handing it the type it already
recognizes, rather than duplicating that dispatch.

An application can mix styles: build a document with the mutable
`Dataset` (convenient for incremental construction from a loop),
`fromDataset()` it once construction is done for a stable, shareable,
hashable value, run the functional pipeline, then `toDataset()` the
final result if a downstream consumer expects RDF/JS `add`/`delete`.

## 4. The dataflow pattern: `cell` + `derive`

The owner's stated destination is "dataflow applications" — computation
graphs where a node recomputes only when its inputs actually changed.
Content-addressed identity (§2) is what makes "actually changed"
answerable in O(1) instead of "run the computation and diff the
output." `fn.js` ships the minimal seed for that, deliberately small
and dependency-free (no reactive-programming library, no scheduler):

```js
const { cell, derive, parse, filter, hash } = require('factoidal/fn');

// A dataflow input: something that changes over time (a poll loop, a
// file watcher, a user edit).
const source = cell(await parse(initialTurtle));

// A derived node: recomputes only when source's *content* hash
// differs from last time -- not when a new object is set into the
// cell, and not on every tick of whatever drives .get().
const people = derive(
  (ds) => filter(ds, (q) => q.predicate.value.endsWith('/type')),
  source
);

await people.get();               // computes once
source.set(await parse(initialTurtle));  // same content, new object
await people.get();               // memoized hit -- content unchanged
source.set(await parse(editedTurtle));
await people.get();               // content changed -- recomputes
```

`derive`'s recompute key is `hash(ds)` for `FnDataset` inputs and the
raw value (compared by `===`) for anything else — so a `derive` node
can depend on a mix of dataset cells and plain parameter cells (a
SPARQL string, a numeric threshold) in one call. This is the part
RDF/JS's mutable `DatasetCore` cannot give you at all: two different
`Dataset` objects with identical quads are not `===`, have no cheap
equality test, and mutating one in place invalidates any cached
"unchanged" assumption silently. An `FnDataset`'s hash is a value you
can compare, cache, and use as a map key — which is the whole point of
content addressing for dataflow.

`derive` here is single-slot (one cached result, replaced on
recompute) — a "cell" in the spreadsheet sense, not a general memo
table keyed by an unbounded history of past inputs. That is
deliberately the smallest useful primitive; a multi-entry LRU or a
push-based (rather than pull-based, `.get()`-triggered) scheduler is
future work if a real pipeline needs it, not something to speculate
into this seed.

## 5. `entail()` — reusing an existing capability, not adding one

The natural design for `entail(ds, regime)` is a self-CONSTRUCT under
entailment: `CONSTRUCT { ?s ?p ?o } WHERE { ?s ?p ?o }` with
`entail: regime`. That does not work through the existing API today:
`lib/api.js`'s `query()` explicitly routes non-`'none'` entailment
requests away from the npm-entry ABI ("entailment closure stays on the
CLI path" — [`lib/api.js:251-253`](../../npm/factoidal/lib/api.js)),
and the CLI path throws `pendingError` for `CONSTRUCT`
([`lib/api.js:276-278`](../../npm/factoidal/lib/api.js)). CONSTRUCT +
entailment is not a combination the engine binding supports yet,
npm-entry bundle or not.

`entail()` instead runs `SELECT ?s ?p ?o WHERE { ?s ?p ?o }` with the
entailment option — the combination `test/api.test.js`'s `query:
entail RDFS infers subclass instances` test already exercises — and
repackages each solution row into a quad with `dataFactory.quad`. This
is JS-side reshaping of already-materialized bindings (the same kind
`bindingsFromSrj` already does), not new RDF/SPARQL semantics, so it
stays inside rule #11 and works with the CLI bundle alone — no
npm-entry bundle required, unlike `canonicalize`/`hash`.

Scope limitation, stated rather than hidden: like any bare
`WHERE { ?s ?p ?o }` in SPARQL, this closes over the **default graph
only** — named-graph triples are not restated. A named-graph-aware
version would need `GRAPH ?g { ?s ?p ?o }` per graph and a definition
of "entailment closure of one named graph" that the underlying
`query()` does not have today. Not attempted here.

## 6. Relationship to the graphs API and Blogic component graphs

[`2026-07-05-graphs-api-design.md`](2026-07-05-graphs-api-design.md)
added `graphs()` (named-graph enumeration) and `canonicalHash()`
(per-graph RDFC-1.0 hash) to the mutable API; `fn.js`'s `graphs(ds)`
is a direct wrapper over `index.js`'s `graphs()`, re-wrapping each
result as an `FnDataset`. No new graph semantics.

This connects to the larger *component-graphs* line
([`2026-07-04-blogic-surfaces-graphs-review.md`](2026-07-04-blogic-surfaces-graphs-review.md)):
that review's `urn:rdfc:sha256:<hex>` naming scheme (§2.1 there) —
"a component's name can be derived from its own canonical hash" — is
precisely what `hash(ds)` on one entry of `fn.graphs(ds)` computes. A
pipeline that splits a dataset into components, hashes each with
`fn.hash`, and treats two components with the same hash as the same
value (dedup, cache key, `derive()` recompute key) is the functional
API's version of that naming scheme, without committing to the
`urn:rdfc:` minting step itself — minting/persisting that name stays
the mutable-API/CLI layer's concern (that doc's §1.2-1.3). `fn.js`
supplies the value half only: a hash computable and comparable in
memory.

## 7. Future backends: on-disk quadstores and streaming parsers

This slice's only implementation is in-memory and string-backed
(`parse()` takes a whole document string; the internal representation
is an array of RDF/JS quads). Two directions this needs to serve
without a rewrite — on-disk quadstores (COTTAS) and streaming
parsers — are addressed at the API-shape level now, implemented
trivially, so the shape doesn't foreclose them later.

**On-disk quadstores.** `FnDataset` holds an opaque `_backend`
satisfying a three-member interface (`size`, `quads(): Iterable<Quad>`,
`precomputedHash: string | null`) — the same capabilities-style
pattern `lib/api.js`'s `buildApi(driver)` already uses for the
JS-vs-Wasm engine split. `arrayBackend` (§1) is the only
implementation today; every free function calls only the public
`FnDataset` surface (`size`, iteration, `toArray()`, `match()`), never
`_backend` fields directly, so a `cottasBackend(generation, path)` —
backed by a COTTAS-on-Parquet snapshot
([`docs/cottas-format-v1.md`](../cottas-format-v1.md)) where a
"dataset value" is an immutable store generation rather than a string
— could implement the same interface without any op in this module
changing signature. The concrete hook already wired: `hash()` and
`equals()` check `_backend.precomputedHash` before calling
`canonicalize()` (§2); a COTTAS backend reading a per-component
`.c14n.sha256` sidecar (the E3 experiment in
[`2026-07-03-shapes-canon-storage-strategies.md`](2026-07-03-shapes-canon-storage-strategies.md)
§5, and the `urn:rdfc:` naming scheme in
[`2026-07-05-graphs-api-design.md`](2026-07-05-graphs-api-design.md)
§2.1) would get O(1) identity for free through the same call sites
`hash()`'s callers already use — no new API. What is **not** solved
by this shape alone: `filter()`, `mapQuads()`, and `query()`'s
`toDataset()` call all fully materialize via `toArray()` today. A
COTTAS backend would need `filter()` to push a predicate down into
row-group pruning (the E1 characteristic-set clustering work,
[`2026-07-03-e1-cs-clustering-results.md`](2026-07-03-e1-cs-clustering-results.md))
rather than materializing every quad first — that is real, separate
design work this slice deliberately does not attempt, only avoids
blocking.

**Streaming parsers.** `builder()` / `fromChunks()` are the seam:
`builder()` returns a mutable accumulator (`addChunk(quadOrQuads)`,
`finish()`), and `finish()` is where the mutable world ends — it
de-duplicates once and returns a frozen `FnDataset`, indistinguishable
from one `parse()` produced. A future streaming Turtle/N-Quads reader
(rule #4: still F\*-implemented and extracted, not hand-written JS)
would call `addChunk()` once per parsed batch instead of requiring
`parse()`'s whole-string input; every op downstream of `finish()` only
ever observes the finished, immutable value, never the accumulator.
Today's `builder()` is the trivial case — accumulate an array, dedup
once at `finish()` — because no streaming parser exists yet to feed
it; the call shape is what needed settling now, not a scheduler or
backpressure story for one that isn't built.

Both directions share one design decision: **`FnDataset` never lets a
free function assume "the representation is an N-Quads string" or "the
representation is an in-memory array."** Every op goes through the
`size`/iteration/`toArray()`/`match()` contract, which today happens
to be backed by an array, and tomorrow does not have to be.

## 8. Deferred, on purpose

- **Browser/Wasm entry.** `fn.js` requires `node:crypto` for
  `hash()`'s sha256 digest, matching `index.js`'s existing
  Node-specific `node:fs`/`node:path` use — this is the Node entry.
  A browser-safe `fn` (using `SubtleCrypto` for the digest, wired
  through `browser.js`/`browser-wasm.js`) is future work, not required
  by this slice.
- **Multi-entry memoization / push-based dataflow scheduling.** `derive`
  is single-slot and pull-based (§4) on purpose; a real pipeline's
  scheduling needs should drive what (if anything) grows here next,
  not speculation now.
- **Named-graph-aware `entail()`.** §5.
- **`urn:rdfc:` minting.** §6 — stays with the graphs-API/CLI layer.
- **COTTAS backend, predicate pushdown, real streaming parser.** §7 —
  the interface and seam exist; the implementations behind them do
  not, on purpose.

## 9. Testing

`npm test` (from `npm/factoidal/`) runs `test/fn.test.js` alongside the
existing suites via the package's `test/*.test.js` glob. Covered:
purity (ops leave inputs' hash/size unchanged; `FnDataset` and its
iterated quads are frozen; `toArray()` is an independent copy),
union/difference algebra (`EMPTY` identity, idempotence, a
difference/union round-trip reconstructing the original), hash
stability under blank-node relabeling plus change-sensitivity when
content differs, hash memoization (including concurrent
in-flight-promise sharing), `equals()`'s ground-data and blank-node
paths, `derive()` hit/miss behavior ("same content, different object"
staying a hit proves the key is content, not object identity),
`builder()`/`fromChunks()` (cross-chunk dedup, post-`finish()` misuse
throwing, async-iterable consumption), and an `fromDataset`/`toDataset`
round-trip confirming the two sides don't alias. Tests needing the
npm-entry bundle probe `capabilities()` and
skip with the project's existing `"pending npm-entry build"` reason
when only the CLI bundle is present (matching `test/api.test.js`);
`entail()`'s test does not skip, since per §5 it never needs that
bundle.
