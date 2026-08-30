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

/-- Predicate buckets are a packer-facing construction state. Rows are held
    in reverse source order until `blocksOfBuckets`, so extending a frequent
    predicate remains constant-time. -/
abbrev Buckets := List (WfIri × Graph)

/- Predicate buckets are held in reverse source order while building. Appending
   to a `Graph` for every occurrence makes a frequent Wikidata predicate
   quadratic before any IBK2 bytes can be written. -/
private def prependFor (predicate : WfIri) (triple : Triple) :
    Buckets → Buckets
  | [] => [(predicate, [triple])]
  | (current, graph) :: rest =>
      if current == predicate then (current, triple :: graph) :: rest
      else (current, graph) :: prependFor predicate triple rest

def addTriples (buckets : Buckets) (triples : List Triple) : Buckets :=
  triples.foldl (fun groups triple => prependFor triple.p triple groups) buckets

def blocksOfBuckets (buckets : Buckets) : List (WfIri × Block) :=
  let ordered := buckets.map fun (predicate, rowsRev) => (predicate, rowsRev.reverse)
  ordered.map fun (predicate, rows) => (predicate, IndexedBlock.fromGraph rows)

/-- Build predicate-local dictionaries from an RDF graph.  This is a compact,
    correctness-first loader; the eventual streaming writer can construct the
    same manifest without the intermediate lists. -/
def fromGraph (graph : Graph) : Store :=
  { source := graph
  , blocks := blocksOfBuckets (addTriples [] graph) }

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
#guard scanBound { p := some pName } fixtureStore == tripleMatchesBound { p := some pName } fixture
#guard scanBound { p := some pKind } fixtureStore == tripleMatchesBound { p := some pKind } fixture
#guard scanBound {} fixtureStore == fixture

end L4Factoidal.Storage.PredicateBlocks
