/-
L4Factoidal.Storage.QuadDataset — the RDF dataset an IBK4 quad sequence
denotes.

`IndexedBlockWireV4.QuadRow` is `(Option GraphRef, Triple)`. The default graph
is the rows whose graph column is `none`; each distinct graph name becomes one
named graph, in first-occurrence order over the row sequence. Triple order
inside each graph is the order the rows were read.

This lives in `L4Factoidal/` rather than in a host tool because two hosts read
the same generations and must answer the same dataset: the native
`l4block-quad-query` (`Harness/QuadQuery.lean`) and the WASM store operations
(`Wasm/Ops/Store.lean`). One definition, one meaning.

No `partial`, no `sorry`, no `native_decide`.
-/
import L4Factoidal.Storage.IndexedBlockWireV4
import Std.Data.HashMap

namespace L4Factoidal.Storage.QuadDataset

open L4Factoidal.RDF

/-! ## Set semantics

An RDF graph is a SET of triples (RDF 1.1 Concepts, section 3). `Graph.add` in
`RDF/Core.lean` states it — `if g.mem t then g else g ++ [t]` — and the
reference evaluator answers one solution per distinct triple. A generation may
carry the same quad in the same graph in more than one row: the packer
publishes blocks during the ingest pass and has no whole-graph index, so it
cannot see that a row repeats one it wrote to an earlier block
(`docs/designissues/2026-09-05-pack-publication-every-batch.md`). The reader
is where the set is made. Measured on a 209,715,187-byte skosdex N-Quads
prefix, 2026-09-05: 603 distinct quads repeat, for 1,067 repeated rows.

The membership test is bucketed by `(subject, predicate, object joinKey)` and
compared with `Triple.eqb`, which is `Syntax.FastGraph.add`'s shape and is
what makes it linear rather than quadratic. It is restated here rather than
imported: `Storage` does not depend on `Syntax`. -/

private abbrev TripleKey := Subject × WfIri × Term

private def tripleKey (t : Triple) : TripleKey := (t.s, t.p, t.o.joinKey)

/-- One graph under construction: reverse insertion order plus the buckets
    that make the membership test constant-time in expectation. -/
private structure BucketedGraph where
  rev : List Triple := []
  buckets : Std.HashMap TripleKey (List Triple) := ∅

private def BucketedGraph.add (g : BucketedGraph) (t : Triple) : BucketedGraph :=
  let key := tripleKey t
  let bucket := g.buckets.getD key []
  if bucket.any (fun u => u.eqb t) then g
  else { rev := t :: g.rev, buckets := g.buckets.insert key (t :: bucket) }

private structure GraphBuckets where
  defaultGraph : BucketedGraph := {}
  named : Std.HashMap GraphRef BucketedGraph := ∅
  orderRev : List GraphRef := []

/-- The named case uses `Std.HashMap.modify`, NOT a lookup followed by an
    insert: a lookup hands out a second reference to the graph while the map
    still holds the first, so the insert inside `BucketedGraph.add` cannot
    update in place and copies that graph's whole bucket map. That is the
    measured reason named graphs did not scale in the N-Quads accumulator
    (<https://github.com/danbri/factoidal/issues/650>); the same shape applies
    here. -/
private def addQuad (buckets : GraphBuckets)
    (quad : L4Factoidal.Storage.IndexedBlockWireV4.QuadRow) : GraphBuckets :=
  match quad.1 with
  | none => { buckets with defaultGraph := buckets.defaultGraph.add quad.2 }
  | some name =>
      if buckets.named.contains name then
        { buckets with named := buckets.named.modify name (fun g => g.add quad.2) }
      else
        { buckets with
          named := buckets.named.insert name (BucketedGraph.add {} quad.2),
          orderRev := name :: buckets.orderRev }

/-- The dataset a quad sequence denotes: each graph is the SET of its
    triples, in first-occurrence row order. -/
def datasetOfQuads (quads : List L4Factoidal.Storage.IndexedBlockWireV4.QuadRow) : Dataset :=
  let buckets := quads.foldl addQuad {}
  { default := buckets.defaultGraph.rev.reverse
  , named := buckets.orderRev.reverse.map fun name =>
      { name, graph := (buckets.named.getD name {}).rev.reverse } }

/-- Every graph name of the dataset is a well-formed IRI.

    `SPARQL/StoreDataset.lean`'s `materialiseDatasetBackend` keeps only graphs
    whose name is an IRI, so a dataset carrying a blank-node graph name must
    reach the reference evaluator directly. SBM7 admits a blank-node graph
    name (`ShardManifest.GraphName.bnode`), so every IBK4 reader needs this
    test. -/
def namesAreIris (ds : Dataset) : Bool :=
  ds.named.all fun ng => match ng.name with | .iri _ => true | _ => false

end L4Factoidal.Storage.QuadDataset
