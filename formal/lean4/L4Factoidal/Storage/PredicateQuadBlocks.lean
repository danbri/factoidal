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

/-! ## Bounded blocks

A predicate's rows are cut into consecutive runs, and each run becomes its own
block. `docs/designissues/2026-09-04-blocks-per-predicate.md` records the
decision; the rules are:

1. the graph changes — always, so a block holds one predicate in ONE graph and
   its manifest `graphSet` has exactly one member;
2. `maxBlockRows` rows;
3. `maxBlockWireBytes` of estimated wire size.

Cutting NEVER reorders: `quadsOfDataset` is graph-major, so a predicate's rows
already arrive with their graph runs consecutive, and a cut is a partition of
the existing order into consecutive pieces. `PredicateQuadBlocksTheorems`
proves the concatenation of the runs is the row list itself, so the emitted
block set denotes exactly the quads the single-block set denoted.

The two numbers come from the read caps of `Wasm/Ops/Store.lean`, which are
TOTALS over the entries one `storeQuery` selects rather than per-block limits:
8,388,608 bytes and 100,000 rows. A per-block target has to leave room for
several blocks in one query, so the byte target is a quarter of the byte cap
and the row target is a sixth of the row cap, rounded down to a power of two. -/

def maxBlockRows : Nat := 16384
def maxBlockWireBytes : Nat := 2097152

/-- One length-prefixed string of `DeltaLog.serializeLString`: a u32 length and
    the UTF-8 bytes. -/
private def lstringWireBytes (s : String) : Nat := 4 + s.utf8ByteSize

/-- The exact `DeltaLog.serializeTerm` length of a subject term. -/
def subjectWireBytes : Subject → Nat
  | .iri i => 1 + lstringWireBytes i.val
  | .bnode b => 1 + lstringWireBytes b

/-- The exact `DeltaLog.serializeTerm` length, which is what PTD1 writes into
    a block dictionary. A triple term is one tag byte and is refused by
    `IndexedBlockWireV4.supported` anyway. -/
def termWireBytes : Term → Nat
  | .iri i => 1 + lstringWireBytes i.val
  | .bnode b => 1 + lstringWireBytes b
  | .literal l =>
      1 + lstringWireBytes l.val.lexicalForm + lstringWireBytes l.val.datatype.val +
        (match l.val.langTag with
         | none => 1
         | some tag => 1 + lstringWireBytes tag)
  | .tripleTerm _ _ _ => 1

/-- A conservative UPPER BOUND of the bytes one quad adds to its block: the
    fixed-width row, one graph-summary entry, and the dictionary cost of all
    four term positions counted WITHOUT de-duplication. PTD1 stores each
    distinct term once, so the true cost is never larger. -/
def quadWireBytes (quad : QuadRow) : Nat :=
  rowBytes + graphEntryBytes +
    subjectWireBytes quad.2.s + 1 + lstringWireBytes quad.2.p.val +
    termWireBytes quad.2.o +
    (match quad.1 with
     | none => 0
     | some graph => subjectWireBytes graph)

/-- Cut one predicate's rows into consecutive runs. Structural on the input
    list; the accumulator is reversed and flipped back at each cut. -/
def chunkGo : List QuadRow → List QuadRow → Nat → Nat → Option GraphRef →
    List (List QuadRow)
  | [], accRev, _, _, _ => if accRev.isEmpty then [] else [accRev.reverse]
  | quad :: rest, accRev, rows, bytes, graph =>
      let weight := quadWireBytes quad
      if accRev.isEmpty then chunkGo rest [quad] 1 weight quad.1
      else if quad.1 == graph && rows < maxBlockRows &&
          bytes + weight <= maxBlockWireBytes then
        chunkGo rest (quad :: accRev) (rows + 1) (bytes + weight) graph
      else accRev.reverse :: chunkGo rest [quad] 1 weight quad.1

/-- The runs of one predicate's rows, in row order. -/
def chunkQuadRows (quads : List QuadRow) : List (List QuadRow) :=
  chunkGo quads [] 0 0 none

def blocksOfBuckets (buckets : Buckets) : List (WfIri × QuadBlock) :=
  buckets.orderRev.reverse.flatMap fun predicate =>
    (chunkQuadRows (buckets.rows.getD predicate []).reverse).map fun rows =>
      (predicate, fromQuads rows)

/-- The IBK4 blocks of a quad list: one or more per predicate, each holding
    that predicate's rows for ONE graph, bounded by the two targets above. -/
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
-- first-occurrence order of the predicate over the whole dataset. `name` has
-- rows in two graphs, so it now publishes two blocks.
#guard sampleBlocks.map Prod.fst == [pName, pName, pKind]
#guard (quadsOfDataset sample).head?.map Prod.fst == some none
#guard (quadsOfDataset sample).length == 3

-- Every block holds ONE graph, is predicate-local, and encodes.
#guard sampleBlocks.map (fun entry => entry.2.rows.size) == [1, 1, 1]
#guard sampleBlocks.all fun entry => onePredicate entry.2
#guard sampleBlocks.all fun entry => (encode? entry.2).isSome
#guard sampleBlocks.all fun entry =>
  (graphNames? entry.2).map List.length == some 1
#guard sampleBlocks.map (fun entry => graphNames? entry.2) ==
  [some [none], some [some g1], some [none]]

-- Cutting is a partition of the row order: no reordering, nothing lost.
#guard (chunkQuadRows (quadsOfDataset sample)).flatten == quadsOfDataset sample

-- Every quad of the dataset is denoted by exactly one block, in source order.
#guard (sampleBlocks.flatMap fun entry => entry.2.denotes).length == 3

end L4Factoidal.Storage.PredicateQuadBlocks
