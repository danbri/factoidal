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

private structure GraphBuckets where
  defaultRev : List Triple := []
  named : Std.HashMap GraphRef (List Triple) := ∅
  orderRev : List GraphRef := []

private def addQuad (buckets : GraphBuckets)
    (quad : L4Factoidal.Storage.IndexedBlockWireV4.QuadRow) : GraphBuckets :=
  match quad.1 with
  | none => { buckets with defaultRev := quad.2 :: buckets.defaultRev }
  | some name =>
      let known := buckets.named.contains name
      { buckets with
        named := buckets.named.insert name (quad.2 :: buckets.named.getD name []),
        orderRev := if known then buckets.orderRev else name :: buckets.orderRev }

/-- The dataset a quad sequence denotes. -/
def datasetOfQuads (quads : List L4Factoidal.Storage.IndexedBlockWireV4.QuadRow) : Dataset :=
  let buckets := quads.foldl addQuad {}
  { default := buckets.defaultRev.reverse
  , named := buckets.orderRev.reverse.map fun name =>
      { name, graph := (buckets.named.getD name []).reverse } }

/-- Every graph name of the dataset is a well-formed IRI.

    `SPARQL/StoreDataset.lean`'s `materialiseDatasetBackend` keeps only graphs
    whose name is an IRI, so a dataset carrying a blank-node graph name must
    reach the reference evaluator directly. SBM7 admits a blank-node graph
    name (`ShardManifest.GraphName.bnode`), so every IBK4 reader needs this
    test. -/
def namesAreIris (ds : Dataset) : Bool :=
  ds.named.all fun ng => match ng.name with | .iri _ => true | _ => false

end L4Factoidal.Storage.QuadDataset
