/-
L4Factoidal.Storage.PredicateQuadBlocks — one IBK4 quad block per predicate.

The quad twin of `PredicateBlocks`. That module partitions a graph of triples
into one `IndexedBlock.Block` per predicate; this one partitions the quads of a
DATASET into one `IndexedBlockWireV4.QuadBlock` per predicate, so a predicate's
rows for every graph live in the same artifact and `GRAPH <iri> { ... }` is a
filter inside the block (`docs/designissues/2026-09-02-quad-aware-block-layout.md`,
option B).

Publication order is the first-occurrence order of the predicate in the
flattened quad list, and row order inside a block is the flattened quad order
restricted to that predicate. Both are the orders `PredicateBlocks` already
uses, so an IBK4 generation of a default-graph-only source has the same block
sequence as the IBK3 generation of the same source.

No `partial`, no `unsafe`, no `sorry`.
-/
import L4Factoidal.Storage.IndexedBlockWireV4
import Std.Data.HashMap

namespace L4Factoidal.Storage.PredicateQuadBlocks

open L4Factoidal.RDF
open L4Factoidal.Storage.IndexedBlockWireV4

/-- Flatten a dataset into quads: the default graph first, then each named
    graph in `Dataset.named` order, each graph in its own triple order.

    This is the same list as `RDF.Canonical.datasetQuads`, restated here so the
    storage layer does not depend on the RDFC-1.0 canonicalization module. The
    two definitions must stay in step; the `#guard` at the foot of this file
    pins the shape that matters — the default graph comes first. -/
def quadsOfDataset (ds : Dataset) : List QuadRow :=
  ds.default.map (fun t => ((none : Option GraphRef), t)) ++
    ds.named.flatMap (fun ng => ng.graph.map (fun t => ((some ng.name : Option GraphRef), t)))

/-- Packer-facing construction state. `rows` gives expected constant-time
    predicate lookup; `orderRev` records first-seen predicates in reverse so
    construction stays constant-time per quad. Rows are held in reverse source
    order until `blocksOfBuckets`. -/
structure Buckets where
  rows : Std.HashMap WfIri (List QuadRow) := ∅
  orderRev : List WfIri := []

def addQuad (buckets : Buckets) (quad : QuadRow) : Buckets :=
  let predicate := quad.2.p
  let known := buckets.rows.contains predicate
  { rows := buckets.rows.insert predicate (quad :: buckets.rows.getD predicate [])
  , orderRev := if known then buckets.orderRev else predicate :: buckets.orderRev }

def addQuads (buckets : Buckets) (quads : List QuadRow) : Buckets :=
  quads.foldl addQuad buckets

def blocksOfBuckets (buckets : Buckets) : List (WfIri × QuadBlock) :=
  buckets.orderRev.reverse.map fun predicate =>
    (predicate, fromQuads (buckets.rows.getD predicate []).reverse)

/-- One IBK4 block per predicate, over every graph of the dataset. -/
def blocksOfQuads (quads : List QuadRow) : List (WfIri × QuadBlock) :=
  blocksOfBuckets (addQuads {} quads)

def blocksOfDataset (ds : Dataset) : List (WfIri × QuadBlock) :=
  blocksOfQuads (quadsOfDataset ds)

/-! ## Build-time checks -/

private def pName : WfIri := ⟨"http://example.org/name", by simp [isIri]⟩
private def pKind : WfIri := ⟨"http://example.org/kind", by simp [isIri]⟩
private def alice : Subject := .iri ⟨"http://example.org/alice", by simp [isIri]⟩
private def bob : Subject := .iri ⟨"http://example.org/bob", by simp [isIri]⟩
private def g1 : GraphRef := .iri ⟨"http://example.org/g1", by simp [isIri]⟩

private def sample : Dataset :=
  { default := [{ s := alice, p := pName, o := .literal (Literal.string "A") },
                { s := alice, p := pKind, o := .iri ⟨"http://example.org/Person", by simp [isIri]⟩ }]
    named := [{ name := g1
                graph := [{ s := bob, p := pName, o := .literal (Literal.string "B") }] }] }

private def sampleBlocks := blocksOfDataset sample

-- The default graph is flattened first, so publication order is the
-- first-occurrence order of the predicate over the whole dataset.
#guard sampleBlocks.map Prod.fst == [pName, pKind]
#guard (quadsOfDataset sample).head?.map Prod.fst == some none
#guard (quadsOfDataset sample).length == 3

-- The `name` block holds rows from two graphs; every block is predicate-local
-- and every block encodes.
#guard (sampleBlocks.find? (fun entry => entry.1 == pName)).map
  (fun entry => entry.2.rows.size) == some 2
#guard sampleBlocks.all fun entry => onePredicate entry.2
#guard sampleBlocks.all fun entry => (encode? entry.2).isSome
#guard (sampleBlocks.find? (fun entry => entry.1 == pName)).bind
  (fun entry => graphNames? entry.2) == some [none, some g1]
#guard (sampleBlocks.find? (fun entry => entry.1 == pKind)).bind
  (fun entry => graphNames? entry.2) == some [none]

-- Every quad of the dataset is denoted by exactly one block, in source order.
#guard (sampleBlocks.flatMap fun entry => entry.2.denotes).length == 3

end L4Factoidal.Storage.PredicateQuadBlocks
