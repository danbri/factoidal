/-
Cutting a bucket's rows into several IBK4 blocks is a PARTITION of the row
order, not a re-grouping of it, and every row of a bucket is in the bucket's
graph.

That is the whole correctness argument for
`docs/designissues/2026-09-04-blocks-per-predicate.md`. `chunkGo` walks the
row list once and only ever closes the run it is building, so concatenating
the runs gives the row list back, in order. Every downstream property follows:
the blocks of one bucket denote the same quads in the same order as the one
block they replace, so an SBM7 generation of split blocks materialises the
same dataset as an SBM7 generation of whole ones.

Since 2026-09-05 the bucket key is the pair (predicate, graph) rather than the
predicate alone, and `chunkGo` has no graph rule at all. `bucket_one_graph`
below is what replaces that rule: `addQuad` files a quad under its own key, so
every row of a bucket — and therefore of each of its blocks — carries the
bucket's predicate and the bucket's graph.

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

/-! ## Every row of a bucket carries the bucket's key -/

/-- What `addQuad` does to one bucket: it prepends the quad when the quad's
    key is that bucket's, and leaves the bucket alone otherwise. -/
theorem addQuad_getD (k : BucketKey) (st : Buckets) (quad : QuadRow) :
    (addQuad st quad).rows.getD k []
      = if keyOf quad = k then quad :: st.rows.getD k [] else st.rows.getD k [] := by
  unfold addQuad
  by_cases hk : keyOf quad = k
  · subst hk; simp
  · have hbf : (keyOf quad == k) = false := by
      simp only [beq_eq_false_iff_ne]; exact hk
    simp [hk, Std.HashMap.getD_insert, hbf]

theorem addQuad_key (k : BucketKey) (st : Buckets) (quad : QuadRow)
    (h : ∀ q ∈ st.rows.getD k [], keyOf q = k) :
    ∀ q ∈ (addQuad st quad).rows.getD k [], keyOf q = k := by
  rw [addQuad_getD]
  by_cases hk : keyOf quad = k
  · rw [if_pos hk]
    intro q hq
    rcases List.mem_cons.mp hq with hq' | hq'
    · exact hq' ▸ hk
    · exact h q hq'
  · rw [if_neg hk]; exact h

theorem addQuads_key (k : BucketKey) :
    ∀ (quads : List QuadRow) (st : Buckets),
      (∀ q ∈ st.rows.getD k [], keyOf q = k) →
      ∀ q ∈ (addQuads st quads).rows.getD k [], keyOf q = k
  | [], st, h => h
  | quad :: rest, st, h => by
      show ∀ q ∈ (addQuads (addQuad st quad) rest).rows.getD k [], keyOf q = k
      exact addQuads_key k rest (addQuad st quad) (addQuad_key k st quad h)

/-- Every row of every block of a bucket has the bucket's predicate AND the
    bucket's graph. So a block's `graphSet` has exactly one member and
    `GRAPH <iri>` selects whole blocks, with no row-level filter. -/
theorem bucket_one_graph (k : BucketKey) (quads : List QuadRow)
    (rows : List QuadRow)
    (hrows : rows ∈ chunkQuadRows ((addQuads ({} : Buckets) quads).rows.getD k []).reverse)
    (q : QuadRow) (hq : q ∈ rows) : keyOf q = k := by
  have hbase : ∀ q ∈ ({} : Buckets).rows.getD k [], keyOf q = k := by
    intro q hq
    simp at hq
  have hall := addQuads_key k quads ({} : Buckets) hbase
  have hmem : q ∈ ((addQuads ({} : Buckets) quads).rows.getD k []).reverse := by
    rw [← chunkQuadRows_flatten
      (((addQuads ({} : Buckets) quads).rows.getD k []).reverse)]
    exact List.mem_flatten.mpr ⟨rows, hrows, hq⟩
  exact hall q (List.mem_reverse.mp hmem)

#print axioms chunkQuadRows_flatten
#print axioms bucket_one_graph

end L4Factoidal.Storage.PredicateQuadBlocks
