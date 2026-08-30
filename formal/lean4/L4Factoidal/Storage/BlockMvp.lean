/-
L4Factoidal.Storage.BlockMvp — the first executable RDF block vertical.

This module is intentionally an in-memory MVP. It uses `Term` values directly,
so it does not allocate persistent `TermId` values before the RDF 1.2 term
identity contract is settled. A block preserves the represented graph's row
order. `scan` is an independently recursive physical traversal, and its
theorem connects it to SPARQL `evalTP` for every triple pattern and seed
binding.

This is the first Block seam, not the final storage representation. Later
blocks may use dictionaries, sorted permutations, codecs, and backend reads
only when they preserve `denotes` and refine this semantic result.
-/
import L4Factoidal.SPARQL.Algebra

namespace L4Factoidal.Storage.BlockMvp

open L4Factoidal.RDF
open L4Factoidal.SPARQL

/-- One immutable in-memory block. `rows` is a `Graph`, whose list order is
    observable through SPARQL solution-sequence order. -/
structure Block where
  rows : Graph
  deriving Repr, DecidableEq

/-- The RDF graph denoted by the MVP block. -/
def Block.denotes (block : Block) : Graph := block.rows

/-- Scan one physical row list against a triple pattern and seed binding.

    This deliberately does not call `List.filterMap`; it is the physical scan
    shape that later implementations refine. -/
def scanRows (tp : TriplePattern) (rows : List Triple) (mu : Binding) : SolutionSeq :=
  match rows with
  | [] => []
  | row :: rest =>
      match tpMatch tp row mu with
      | none => scanRows tp rest mu
      | some mu' => mu' :: scanRows tp rest mu

/-- Scan the rows of one immutable block. The triple pattern carries the
    subject, predicate, object, and seed-binding bounds. -/
def scan (tp : TriplePattern) (block : Block) (mu : Binding) : SolutionSeq :=
  scanRows tp block.rows mu

/-- Scan physical rows against the bounds supplied by the storage-planning
    seam. This returns candidate triples, not solution mappings; the SPARQL
    evaluator still applies the complete triple-pattern match afterwards. -/
def scanBoundRows (bound : PatternBound) : List Triple → List Triple
  | [] => []
  | row :: rest =>
      if boundMatches bound row then row :: scanBoundRows bound rest
      else scanBoundRows bound rest

/-- The block's candidate-row scan for one backend pattern bound. -/
def scanBound (bound : PatternBound) (block : Block) : List Triple :=
  scanBoundRows bound block.rows

/-- The independently recursive physical scan returns exactly the SPARQL
    triple-pattern result, preserving order and duplicate rows. -/
theorem scanRows_eq_evalTP (tp : TriplePattern) (rows : List Triple) (mu : Binding) :
    scanRows tp rows mu = evalTP tp rows mu := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
      simp only [scanRows, evalTP, List.filterMap]
      cases h : tpMatch tp row mu with
      | none =>
          simp
          simpa [evalTP] using ih
      | some mu' =>
          simp
          simpa [evalTP] using ih

/-- The MVP block scan refines the existing SPARQL evaluator through the block
    denotation. -/
theorem scan_eq_evalTP (tp : TriplePattern) (block : Block) (mu : Binding) :
    scan tp block mu = evalTP tp block.denotes mu := by
  exact scanRows_eq_evalTP tp block.rows mu

/-- The backend candidate scan has the existing storage-bound meaning and
    preserves the input row order. -/
theorem scanBoundRows_eq_tripleMatchesBound (bound : PatternBound) (rows : List Triple) :
    scanBoundRows bound rows = tripleMatchesBound bound rows := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
      cases h : boundMatches bound row <;>
        simp [scanBoundRows, tripleMatchesBound, h, ih]

/-- The block candidate scan refines the standard backend search relation. -/
theorem scanBound_eq_tripleMatchesBound (bound : PatternBound) (block : Block) :
    scanBound bound block = tripleMatchesBound bound block.denotes := by
  exact scanBoundRows_eq_tripleMatchesBound bound block.rows

end L4Factoidal.Storage.BlockMvp
