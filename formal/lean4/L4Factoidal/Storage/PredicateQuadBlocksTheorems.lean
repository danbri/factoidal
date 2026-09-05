/-
Cutting a bucket's rows into several IBK4 blocks is a PARTITION of the row
order, not a re-grouping of it.

That is the whole correctness argument for
`docs/designissues/2026-09-04-blocks-per-predicate.md`. `chunkGo` walks the
row list once and only ever closes the run it is building, so concatenating
the runs gives the row list back, in order. Every downstream property follows:
the blocks of one bucket denote the same quads in the same order as the one
block they replace, so an SBM7 generation of split blocks materialises the
same dataset as an SBM7 generation of whole ones.

Since 2026-09-05 the bucket key is the pair (predicate, graph) rather than the
predicate alone, and `chunkGo` has no graph rule at all.

No `sorry`, no `axiom`, no `native_decide`.
-/
import L4Factoidal.Storage.PredicateQuadBlocks

namespace L4Factoidal.Storage.PredicateQuadBlocks

open L4Factoidal.RDF
open L4Factoidal.Storage.IndexedBlockWireV4

/-- The general statement, with the accumulator exposed: whatever `chunkGo`
    has already buffered comes out in front of whatever is left to read. -/
theorem chunkGo_flatten (quads : List QuadRow) :
    ∀ (accRev : List QuadRow) (rows bytes : Nat),
      (chunkGo quads accRev rows bytes).flatten = accRev.reverse ++ quads := by
  induction quads with
  | nil =>
      intro accRev rows bytes
      cases accRev with
      | nil => simp [chunkGo]
      | cons a as => simp [chunkGo]
  | cons quad rest ih =>
      intro accRev rows bytes
      rw [chunkGo]
      split
      · rename_i h
        rw [ih]
        simp [List.isEmpty_iff.mp h]
      · split
        · rw [ih]; simp
        · rw [List.flatten_cons, ih]; simp

/-- Cutting a bucket's rows loses nothing, adds nothing and reorders
    nothing. -/
theorem chunkQuadRows_flatten (quads : List QuadRow) :
    (chunkQuadRows quads).flatten = quads := by
  rw [chunkQuadRows]
  simpa using chunkGo_flatten quads [] 0 0

#print axioms chunkQuadRows_flatten

end L4Factoidal.Storage.PredicateQuadBlocks
