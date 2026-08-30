/-
L4Factoidal.Storage.IndexedBlock — dictionary-backed RDF block execution.

This is the first physical successor to `BlockMvp`: triples are held as term-ID
rows and a predicate partition gives a bounded SPARQL triple pattern a smaller
candidate sequence. The dictionary deliberately retains the first source term
for an engine-equality class, so decoded result bindings remain RDF terms.

The representation is in-memory only. Its byte format belongs to the later
canonical-codec gate; this module establishes the executable data layout and
its backend-facing scan shape first.
-/
import Std.Data.HashMap
import L4Factoidal.Storage.BlockMvp
import L4Factoidal.SPARQL.StoreBackend

namespace L4Factoidal.Storage.IndexedBlock

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.SPARQL.StoreBackend

abbrev TermId := Nat

/-- A triple whose three positions refer into one shared block dictionary. -/
structure IdTriple where
  s : TermId
  p : TermId
  o : TermId
  deriving Repr, DecidableEq, Inhabited

/-- An immutable RDF block with source-order ID rows and predicate partitions.
    Partitions accumulate backwards for constant-time load and are reversed
    before a scan, restoring SPARQL sequence order. -/
structure Block where
  dict : Array Term
  idByTerm : Std.HashMap Term TermId
  rows : Array IdTriple
  byPredicate : Std.HashMap TermId (List IdTriple)

private structure BuildState where
  dict : Array Term := #[]
  idByTerm : Std.HashMap Term TermId := ∅
  rows : Array IdTriple := #[]
  byPredicate : Std.HashMap TermId (List IdTriple) := ∅

/-- Add a structurally distinct RDF term to the build dictionary in amortised
    constant time. This preserves original terms exactly; matching semantics
    are still applied by `boundMatches` after decoding. -/
private def intern (state : BuildState) (term : Term) : BuildState × TermId :=
  match state.idByTerm[term]? with
  | some id => (state, id)
  | none =>
      let id := state.dict.size
      ({ state with dict := state.dict.push term, idByTerm := state.idByTerm.insert term id }, id)

private def internTriple (state : BuildState) (triple : Triple) : BuildState :=
  let (state1, s) := intern state triple.s.toTerm
  let (state2, p) := intern state1 (.iri triple.p)
  let (state3, o) := intern state2 triple.o
  let row := { s := s, p := p, o := o }
  { state3 with
    rows := state3.rows.push row
    byPredicate := state3.byPredicate.insert p (row :: state3.byPredicate.getD p []) }

/-- Build the shared dictionary and source-order predicate partitions. -/
def fromGraph (graph : Graph) : Block :=
  let state := graph.foldl internTriple {}
  { dict := state.dict, idByTerm := state.idByTerm, rows := state.rows,
    byPredicate := state.byPredicate }

/-- Decode one ID triple. Invalid references are rejected rather than mapped to
    a fabricated term. -/
def decodeTriple? (dict : Array Term) (row : IdTriple) : Option Triple := do
  let s ← dict[row.s]?
  let p ← dict[row.p]?
  let o ← dict[row.o]?
  let subject ← s.toSubject?
  match p with
  | .iri predicate => some { s := subject, p := predicate, o := o }
  | _ => none

/-- The RDF graph denoted by valid ID rows, in physical row order. -/
def Block.denotes (block : Block) : Graph :=
  block.rows.toList.filterMap (decodeTriple? block.dict)

/-- Select the cheapest currently available physical candidate sequence. A
    predicate bound selects its partition; other bounds are checked after ID
    decoding so all RDF equality details remain in one semantic operation. -/
def candidateRows (bound : PatternBound) (block : Block) : List IdTriple :=
  match bound.p with
  | none => block.rows.toList
  | some predicate =>
      match block.idByTerm[Term.iri predicate]? with
      | none => []
      | some pid => (block.byPredicate.getD pid []).reverse

/-- A predicate-aware candidate scan of the ID block. -/
def scanBound (bound : PatternBound) (block : Block) : List Triple :=
  ((candidateRows bound block).filterMap (decodeTriple? block.dict)).filter (boundMatches bound)

/-- The backend read capability for this block. `estimate` is exact for the
    current representation and lets existing planning choose its predicate
    access path. -/
def readOps (block : Block) : BackendReadOps :=
  { search := fun bound => scanBound bound block
  , estimate := fun bound => (scanBound bound block).length
  , predicatePresent := fun predicate => !(scanBound { p := some predicate } block).isEmpty }

end L4Factoidal.Storage.IndexedBlock
