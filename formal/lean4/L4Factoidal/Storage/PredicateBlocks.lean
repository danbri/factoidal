/-
L4Factoidal.Storage.PredicateBlocks — independently decodable predicate shards.

`IndexedBlockWireV2` makes predicate rows contiguous, but its one shared
dictionary means that a small predicate still needs the whole dictionary to
decode its rows.  This module defines the next physical boundary: a dataset is
a collection of immutable, predicate-local `IndexedBlock.Block`s.  A future
manifest may store each block as its own canonical IBK2 artifact; until then
the module is deliberately pure and lets the existing backend execute it.

The source graph is retained only for the unbound-predicate case, where it
preserves the established source-order observable behaviour.  A predicate-bound
scan uses exactly one local block, giving the intended access shape without a
second SPARQL evaluator.
-/
import L4Factoidal.Storage.IndexedBlock
import Std.Data.HashMap

namespace L4Factoidal.Storage.PredicateBlocks

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.SPARQL.StoreBackend
open L4Factoidal.Storage.IndexedBlock

/-- A graph represented as one immutable indexed block per predicate. -/
structure Store where
  /-- Authoritative sequence for scans with no predicate bound. -/
  source : Graph
  /-- Predicate identity and its independently decodable local block. -/
  blocks : List (WfIri × Block)

/-- Predicate buckets are a packer-facing construction state. `rows` supplies
    expected constant-time predicate lookup; `orderRev` records first-seen
    predicates in reverse so construction remains constant-time, while
    `blocksOfBuckets` restores the reference encoder's publication order.
    Rows are held in reverse source order until `blocksOfBuckets`. -/
structure Buckets where
  rows : Std.HashMap WfIri Graph := ∅
  orderRev : List WfIri := []

/-- Add one row without a linear search over unrelated predicates. -/
def addTriple (buckets : Buckets) (triple : Triple) : Buckets :=
  let known := buckets.rows.contains triple.p
  { rows := buckets.rows.insert triple.p (triple :: buckets.rows.getD triple.p [])
  , orderRev := if known then buckets.orderRev else triple.p :: buckets.orderRev }

def addTriples (buckets : Buckets) (triples : List Triple) : Buckets :=
  triples.foldl addTriple buckets

def blocksOfBuckets (buckets : Buckets) : List (WfIri × Block) :=
  buckets.orderRev.reverse.map fun predicate =>
    (predicate, IndexedBlock.fromGraph (buckets.rows.getD predicate []).reverse)

/-- Build predicate-local dictionaries from an RDF graph.  This is a compact,
    correctness-first loader; the eventual streaming writer can construct the
    same manifest without the intermediate lists. -/
def fromGraph (graph : Graph) : Store :=
  { source := graph
  , blocks := blocksOfBuckets (addTriples {} graph) }

/-- Find the independently decodable block for a predicate. -/
def blockFor? (predicate : WfIri) (store : Store) : Option Block :=
  (store.blocks.find? fun entry => entry.1 == predicate).map Prod.snd

/-- Predicate-bound reads touch one shard.  Other reads retain the original
    graph semantics until a manifest-level multi-shard merge is introduced. -/
def scanBound (bound : PatternBound) (store : Store) : List Triple :=
  match bound.p with
  | none => tripleMatchesBound bound store.source
  | some predicate =>
      match blockFor? predicate store with
      | none => []
      | some block => IndexedBlock.scanBound bound block

/-- Existing SPARQL evaluation receives this through its single backend
    capability dispatch point. -/
def readOps (store : Store) : BackendReadOps :=
  { search := fun bound => scanBound bound store
  , estimate := fun bound => (scanBound bound store).length
  , predicatePresent := fun predicate => !(scanBound { p := some predicate } store).isEmpty }

/-! ## Executable regression fixture

These guards pin the essential observable contract while the manifest and
on-disk sharded format are still being designed. -/

private def pName : WfIri := ⟨"http://example.org/name", by simp [isIri]⟩
private def pKind : WfIri := ⟨"http://example.org/kind", by simp [isIri]⟩
private def alice : Subject := .iri ⟨"http://example.org/alice", by simp [isIri]⟩
private def bob : Subject := .iri ⟨"http://example.org/bob", by simp [isIri]⟩
private def fixture : Graph :=
  [{ s := alice, p := pName, o := .literal (Literal.langString "Alice" "en") },
   { s := alice, p := pKind, o := .iri ⟨"http://example.org/Person", by simp [isIri]⟩ },
   { s := bob, p := pName, o := .literal (Literal.langString "Bob" "en") }]
private def fixtureStore := fromGraph fixture

#guard fixtureStore.blocks.length == 2
-- Bucket lookup is hashed, but publication retains first-seen order so
-- manifest ordinals remain stable for existing artifacts.
#guard fixtureStore.blocks.map Prod.fst == [pName, pKind]
#guard scanBound { p := some pName } fixtureStore == tripleMatchesBound { p := some pName } fixture
#guard scanBound { p := some pKind } fixtureStore == tripleMatchesBound { p := some pKind } fixture
#guard scanBound {} fixtureStore == fixture

end L4Factoidal.Storage.PredicateBlocks
