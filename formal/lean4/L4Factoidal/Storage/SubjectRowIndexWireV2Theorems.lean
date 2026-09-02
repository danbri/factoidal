/-
L4Factoidal.Storage.SubjectRowIndexWireV2Theorems — the round-trip proof for
the SRI2 subject postings codec of
`L4Factoidal.Storage.SubjectRowIndexWireV2`.

SRI2 writes a sixty-one byte prefix (magic, version, the target IBK3 SHA-256
and six u32 counts), a directory of sixteen-byte page references, pages of
eight-byte `(subject, row offset)` pairs, and a CRC32C over every post-version
byte. `decode?` reads all of that back and re-checks the prefix relations, the
directory well-formedness and monotonicity, the per-page framing and ordering,
and the global pair ordering and row-offset permutation. This module proves the
two agree:

    encode? index = some bytes → decode? bytes = some index

on the subset `encode?` admits, with no further hypothesis.

The proof is layered. The byte-array bridge turns each `ByteArray` operation
the decoder performs into the list operation the encoder built. The ordering
lemmas turn `strictlyOrdered` on the whole pair list into the per-page and
per-boundary facts the directory checks need. The pagination lemmas give
`chunks` its four properties: it partitions the pair list, its page count is
the ceiling division the prefix records, its i-th page is the i-th window of
`pagePairs` pairs, and no page is empty. `refsFrom` restates `pageRefs` as a
recursion with a running offset, which is what makes the directory
well-formedness, monotonicity and coverage checks provable by induction.
`decodePairsGo_ok` lifts the eight-byte pair read to a whole page, and
`decodeAllPages_ok` lifts that to the page list under its directory.

`decode?` runs `offsetsPermutation` on the pairs it reads back, and neither
the size conditions nor `strictlyOrdered` imply it: `(1, 0), (2, 0)` is
strictly ordered with in-range row offsets and repeats a row offset. Per the
encoder-boundary policy, `supported` now runs the same check, so `encode?`
refuses exactly the indexes `decode?` would refuse and the theorem below needs
no extra hypothesis.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.SubjectRowIndexWireV2

namespace L4Factoidal.Storage.SubjectRowIndexWireV2

open L4Factoidal.Storage

/-! ## Byte array bridge -/

/-- The byte array built from a list has that list's length. -/
theorem size_bytesOf (xs : List UInt8) : (bytesOf xs).size = xs.length := by
  simp [bytesOf, ByteArray.size]

/-- Reading a built byte array back gives the list it was built from. -/
theorem listOf_bytesOf (xs : List UInt8) : listOf (bytesOf xs) = xs := by
  simp [bytesOf, listOf]

/-- Building from a byte array's own list returns that byte array. -/
theorem bytesOf_listOf (bytes : ByteArray) : bytesOf (listOf bytes) = bytes := by
  simp [bytesOf, listOf]

/-- A byte-range extract is the corresponding list slice. -/
theorem extract_bytesOf (xs : List UInt8) (a b : Nat) :
    (bytesOf xs).extract a b = bytesOf ((xs.drop a).take (b - a)) := by
  simp [bytesOf, ByteArray.extract, ByteArray.copySlice]

/-- Indexed access agrees between the byte array and its list. -/
theorem getElem?_bytesOf (xs : List UInt8) (i : Nat) : (bytesOf xs)[i]? = xs[i]? := by
  by_cases h : i < xs.length
  · rw [getElem?_pos (bytesOf xs) i (by simpa [bytesOf, ByteArray.size] using h),
      getElem?_pos xs i h]
    rfl
  · rw [getElem?_neg (bytesOf xs) i (by simpa [bytesOf, ByteArray.size] using h),
      getElem?_neg xs i h]

/-- The decoder's four-byte read is the little-endian list read. -/
theorem readU32At?_bytesOf (xs : List UInt8) (off : Nat) :
    readU32At? (bytesOf xs) off = readU32LE xs off := by
  simp only [readU32At?, readU32LE, getElem?_bytesOf]
  have h0 : xs[off]? = (xs.drop off)[0]? := by simp [List.getElem?_drop]
  have h1 : xs[off + 1]? = (xs.drop off)[1]? := by simp [List.getElem?_drop]
  have h2 : xs[off + 2]? = (xs.drop off)[2]? := by simp [List.getElem?_drop]
  have h3 : xs[off + 3]? = (xs.drop off)[3]? := by simp [List.getElem?_drop]
  rw [h0, h1, h2, h3]
  generalize xs.drop off = d
  rcases d with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨e, t⟩⟩⟩⟩ <;> simp

/-- A four-byte field is readable at the length of the framing before it. -/
theorem readU32LE_at_prefix (pre : List UInt8) (n : UInt32) (rest : List UInt8) :
    readU32LE (pre ++ (writeU32LE n ++ rest)) pre.length = some n := by
  rw [← List.append_assoc]
  exact readU32LE_append_writeU32LE pre n rest

/-! ## Pair ordering -/

/-- The head of a strictly ordered list has the least subject in it. -/
theorem strictlyOrdered_head_le : ∀ (l : List (Nat × Nat)) (a : Nat × Nat),
    strictlyOrdered (a :: l) = true → ∀ b ∈ l, a.1 ≤ b.1 := by
  intro l
  induction l with
  | nil => intro a _ b hb; simp at hb
  | cons c t ih =>
      intro a hso b hb
      rw [strictlyOrdered, Bool.and_eq_true] at hso
      have hac : a.1 ≤ c.1 := by
        have := hso.1
        simp only [strictlyBefore, before, Bool.or_eq_true, decide_eq_true_eq,
          Bool.and_eq_true, beq_iff_eq] at this
        rcases this with h | ⟨h, -⟩ <;> omega
      rcases List.mem_cons.mp hb with rfl | hb
      · exact hac
      · exact Nat.le_trans hac (ih c hso.2 b hb)

/-- A strictly ordered list stays strictly ordered when a prefix is dropped. -/
theorem strictlyOrdered_drop : ∀ (l : List (Nat × Nat)) (k : Nat),
    strictlyOrdered l = true → strictlyOrdered (l.drop k) = true := by
  intro l
  induction l with
  | nil => intro k _; simp [strictlyOrdered]
  | cons a t ih =>
      intro k hso
      match k with
      | 0 => simpa using hso
      | k + 1 =>
          rw [List.drop_succ_cons]
          match t with
          | [] => simp [strictlyOrdered]
          | c :: t' =>
              rw [strictlyOrdered, Bool.and_eq_true] at hso
              exact ih k hso.2

/-- A strictly ordered list stays strictly ordered when a suffix is dropped. -/
theorem strictlyOrdered_take : ∀ (l : List (Nat × Nat)) (k : Nat),
    strictlyOrdered l = true → strictlyOrdered (l.take k) = true := by
  intro l
  induction l with
  | nil => intro k _; simp [strictlyOrdered]
  | cons a t ih =>
      intro k hso
      match k with
      | 0 => simp [strictlyOrdered]
      | k + 1 =>
          rw [List.take_succ_cons]
          match t with
          | [] => simp [strictlyOrdered]
          | c :: t' =>
              rw [strictlyOrdered, Bool.and_eq_true] at hso
              match k with
              | 0 => simp [strictlyOrdered]
              | k' + 1 =>
                  rw [List.take_succ_cons, strictlyOrdered, Bool.and_eq_true]
                  refine ⟨hso.1, ?_⟩
                  have := ih (k' + 1) hso.2
                  rwa [List.take_succ_cons] at this

/-- A contiguous window of a strictly ordered list is strictly ordered. -/
theorem strictlyOrdered_window (l : List (Nat × Nat)) (i j : Nat)
    (hso : strictlyOrdered l = true) : strictlyOrdered ((l.drop i).take j) = true :=
  strictlyOrdered_take _ j (strictlyOrdered_drop l i hso)

/-- The last subject of a page is at least its first. -/
theorem strictlyOrdered_head_le_getLastD : ∀ (t : List (Nat × Nat)) (a d : Nat × Nat),
    strictlyOrdered (a :: t) = true → a.1 ≤ ((a :: t).getLastD d).1 := by
  intro t a d hso
  have hmem : (a :: t).getLastD d ∈ a :: t := by
    rw [List.getLastD_cons]
    exact List.getLastD_mem_cons
  rcases List.mem_cons.mp hmem with h | h
  · exact Nat.le_of_eq (congrArg Prod.fst h.symm)
  · exact strictlyOrdered_head_le t a hso _ h

/-- Across a page boundary the last subject of the left page is at most the
    first subject of the right page. -/
theorem strictlyOrdered_getLastD_le : ∀ (t : List (Nat × Nat)) (a d b : Nat × Nat)
    (X : List (Nat × Nat)),
    strictlyOrdered ((a :: t) ++ (b :: X)) = true → ((a :: t).getLastD d).1 ≤ b.1 := by
  intro t
  induction t with
  | nil =>
      intro a d b X hso
      rw [List.cons_append, List.nil_append, strictlyOrdered, Bool.and_eq_true] at hso
      have := hso.1
      simp only [strictlyBefore, before, Bool.or_eq_true, decide_eq_true_eq,
        Bool.and_eq_true, beq_iff_eq] at this
      simp only [List.getLastD_cons, List.getLastD_nil]
      rcases this with h | ⟨h, -⟩ <;> omega
  | cons c t' ih =>
      intro a d b X hso
      rw [List.cons_append, List.cons_append, strictlyOrdered, Bool.and_eq_true] at hso
      have hrest : strictlyOrdered ((c :: t') ++ (b :: X)) = true := by
        rw [List.cons_append]; exact hso.2
      rw [List.getLastD_cons]
      exact ih c a b X hrest

/-! ## Pagination -/

/-- The recursive step of `chunks` on a nonempty list. -/
theorem chunks_cons {α : Type} (f : Nat) (a : α) (t : List α) :
    chunks (f + 1) (a :: t)
      = (a :: t).take pagePairs :: chunks f ((a :: t).drop pagePairs) := by
  rw [chunks]
  simp

/-- With enough fuel the pages partition the pair list. -/
theorem chunks_flatten {α : Type} : ∀ (f : Nat) (L : List α), L.length ≤ f →
    (chunks f L).flatten = L := by
  intro f
  induction f with
  | zero =>
      intro L hlen
      have hnil : L = [] := List.length_eq_zero_iff.mp (by omega)
      subst hnil; simp [chunks]
  | succ f ih =>
      intro L hlen
      match L with
      | [] => simp [chunks]
      | a :: t =>
          have hsub : ((a :: t).drop pagePairs).length ≤ f := by
            simp only [List.length_drop, List.length_cons, pagePairs]
            simp only [List.length_cons] at hlen
            omega
          rw [chunks_cons, List.flatten_cons, ih ((a :: t).drop pagePairs) hsub]
          exact List.take_append_drop pagePairs (a :: t)

/-- The page count is the ceiling division the prefix records. -/
theorem chunks_length {α : Type} : ∀ (f : Nat) (L : List α), L.length ≤ f →
    (chunks f L).length = (L.length + pagePairs - 1) / pagePairs := by
  intro f
  induction f with
  | zero =>
      intro L hlen
      have hnil : L = [] := List.length_eq_zero_iff.mp (by omega)
      subst hnil; simp [chunks, pagePairs]
  | succ f ih =>
      intro L hlen
      match L with
      | [] => simp [chunks, pagePairs]
      | a :: t =>
          have hsub : ((a :: t).drop pagePairs).length ≤ f := by
            simp only [List.length_drop, List.length_cons, pagePairs]
            simp only [List.length_cons] at hlen
            omega
          rw [chunks_cons, List.length_cons, ih ((a :: t).drop pagePairs) hsub]
          simp only [List.length_drop, List.length_cons, pagePairs]
          omega

/-- The i-th page is the i-th window of `pagePairs` pairs. -/
theorem chunks_getElem? {α : Type} : ∀ (f : Nat) (L : List α) (j : Nat), L.length ≤ f →
    j < (L.length + pagePairs - 1) / pagePairs →
    (chunks f L)[j]? = some ((L.drop (j * pagePairs)).take pagePairs) := by
  intro f
  induction f with
  | zero =>
      intro L j hlen hj
      have hnil : L = [] := List.length_eq_zero_iff.mp (by omega)
      subst hnil; simp [pagePairs] at hj
  | succ f ih =>
      intro L j hlen hj
      match L with
      | [] => simp [pagePairs] at hj
      | a :: t =>
          have hsub : ((a :: t).drop pagePairs).length ≤ f := by
            simp only [List.length_drop, List.length_cons, pagePairs]
            simp only [List.length_cons] at hlen
            omega
          rw [chunks_cons]
          match j with
          | 0 => simp
          | k + 1 =>
              have hk : k < (((a :: t).drop pagePairs).length + pagePairs - 1) / pagePairs := by
                simp only [List.length_drop, List.length_cons, pagePairs]
                simp only [List.length_cons, pagePairs] at hj
                omega
              rw [List.getElem?_cons_succ, ih ((a :: t).drop pagePairs) k hsub hk,
                List.drop_drop]
              congr 3
              simp only [pagePairs]
              omega

/-- No page is empty, which is what makes the directory contiguous. -/
theorem chunks_ne_nil {α : Type} : ∀ (f : Nat) (L : List α) (pg : List α),
    pg ∈ chunks f L → pg ≠ [] := by
  intro f
  induction f with
  | zero => intro L pg hmem; simp [chunks] at hmem
  | succ f ih =>
      intro L pg hmem
      match L with
      | [] => simp [chunks] at hmem
      | a :: t =>
          rw [chunks_cons, List.mem_cons] at hmem
          rcases hmem with rfl | hmem
          · simp [pagePairs]
          · exact ih _ _ hmem

/-- Every page in a strictly ordered concatenation is strictly ordered. -/
theorem strictlyOrdered_of_mem_flatten : ∀ (PP : List (List (Nat × Nat)))
    (p : List (Nat × Nat)), strictlyOrdered PP.flatten = true → p ∈ PP →
    strictlyOrdered p = true := by
  intro PP
  induction PP with
  | nil => intro p _ hmem; simp at hmem
  | cons q rest ih =>
      intro p hso hmem
      rw [List.flatten_cons] at hso
      rcases List.mem_cons.mp hmem with rfl | hmem
      · have := strictlyOrdered_take _ p.length hso
        rwa [List.take_left] at this
      · have hrest : strictlyOrdered rest.flatten = true := by
          have := strictlyOrdered_drop _ q.length hso
          rwa [List.drop_left] at this
        exact ih p hrest hmem

/-! ## The page directory -/

/-- Each encoded pair occupies eight bytes. -/
theorem flatMap_encodePair_length : ∀ (page : List (Nat × Nat)),
    (page.flatMap encodePair).length = page.length * pairBytes := by
  intro page
  induction page with
  | nil => simp
  | cons x rest ih =>
      simp only [List.flatMap_cons, List.length_append, encodePair, ih,
        List.length_cons, writeU32LE_length, pairBytes]
      omega

/-- The directory fold step, named so the accumulator lemma can be stated. -/
def refStep (state : Nat × List PageRef) (pair : List UInt8 × List (Nat × Nat)) :
    Nat × List PageRef :=
  let (offset, refs) := state
  let (bytes, pairs) := pair
  match pairs with
  | (firstSubject, _) :: _ =>
      let maxSubject := pairs.getLastD (firstSubject, 0) |>.1
      (offset + bytes.length,
        PageRef.mk firstSubject maxSubject offset bytes.length :: refs)
  | [] => (offset, refs)

/-- `pageRefs` is that step folded over the zipped page lists. -/
theorem pageRefs_eq_fold (pages : List (List UInt8)) (pairPages : List (List (Nat × Nat))) :
    pageRefs pages pairPages = ((pages.zip pairPages).foldl refStep (0, [])).2.reverse := rfl

/-- The directory as a recursion over pages with an explicit running offset. -/
def refsFrom : Nat → List (List (Nat × Nat)) → List PageRef
  | _, [] => []
  | base, page :: rest =>
      PageRef.mk (page.headD (0, 0)).1 (page.getLastD (page.headD (0, 0))).1 base
          (page.flatMap encodePair).length ::
        refsFrom (base + (page.flatMap encodePair).length) rest

/-- The directory fold accumulates a running offset and reversed entries. -/
theorem refStep_foldl : ∀ (PP : List (List (Nat × Nat))) (base : Nat) (acc : List PageRef),
    (∀ p ∈ PP, p ≠ []) →
    ((PP.map (fun p => p.flatMap encodePair)).zip PP).foldl refStep (base, acc)
      = (base + (PP.map (fun p => (p.flatMap encodePair).length)).sum,
         (refsFrom base PP).reverse ++ acc) := by
  intro PP
  induction PP with
  | nil => intro base acc _; simp [refsFrom]
  | cons p PP' ih =>
      intro base acc hne
      have hp : p ≠ [] := hne p (by simp)
      match p, hp with
      | (fs, sn) :: t, _ =>
          rw [List.map_cons, List.zip_cons_cons, List.foldl_cons]
          have hstep : refStep (base, acc)
              (((fs, sn) :: t).flatMap encodePair, (fs, sn) :: t)
              = (base + (((fs, sn) :: t).flatMap encodePair).length,
                 PageRef.mk (((fs, sn) :: t).headD (0, 0)).1
                   (((fs, sn) :: t).getLastD (((fs, sn) :: t).headD (0, 0))).1 base
                   (((fs, sn) :: t).flatMap encodePair).length :: acc) := by
            simp only [refStep, List.headD_cons, List.getLastD_cons]
          rw [hstep, ih (base + (((fs, sn) :: t).flatMap encodePair).length) _
            (fun q hq => hne q (by simp [hq]))]
          simp only [refsFrom, List.map_cons, List.sum_cons, List.reverse_cons,
            List.append_assoc, List.cons_append, List.nil_append]
          rw [Nat.add_assoc]

/-- `pageRefs` on the encoder's own page lists is `refsFrom` started at zero. -/
theorem pageRefs_eq (PP : List (List (Nat × Nat))) (hne : ∀ p ∈ PP, p ≠ []) :
    pageRefs (PP.map (fun p => p.flatMap encodePair)) PP = refsFrom 0 PP := by
  rw [pageRefs_eq_fold, refStep_foldl PP 0 [] hne]
  simp

/-- One directory entry per page. -/
theorem refsFrom_length (PP : List (List (Nat × Nat))) (base : Nat) :
    (refsFrom base PP).length = PP.length := by
  induction PP generalizing base with
  | nil => simp [refsFrom]
  | cons p rest ih => simp [refsFrom, ih]

/-- The coverage fold over the directory sums the page byte lengths. -/
theorem refsFrom_sum : ∀ (PP : List (List (Nat × Nat))) (base start : Nat),
    (refsFrom base PP).foldl (fun total ref => total + ref.length) start
      = start + (PP.map (fun p => (p.flatMap encodePair).length)).sum := by
  intro PP
  induction PP with
  | nil => intro base start; simp [refsFrom]
  | cons p rest ih =>
      intro base start
      simp only [refsFrom, List.foldl_cons, List.map_cons, List.sum_cons]
      rw [ih (base + (p.flatMap encodePair).length)
        (start + (p.flatMap encodePair).length)]
      omega

/-- Every directory entry passes the well-formedness check: its subject range
    is ordered, its offset is the running one, and its length is the page's
    declared pair count times the pair width. -/
theorem refsWellFormed_refsFrom (header : Prefix) : ∀ (PP : List (List (Nat × Nat)))
    (ordinal base : Nat),
    (∀ p ∈ PP, p ≠ []) →
    (∀ p ∈ PP, strictlyOrdered p = true) →
    (∀ j page, PP[j]? = some page → pairsInPage header (ordinal + j) = page.length) →
    refsWellFormed header (refsFrom base PP) ordinal base = true := by
  intro PP
  induction PP with
  | nil => intro ordinal base _ _ _; simp [refsFrom, refsWellFormed]
  | cons p PP' ih =>
      intro ordinal base hne hso hcount
      have hp : p ≠ [] := hne p (by simp)
      have hcount0 : pairsInPage header ordinal = p.length := by
        have := hcount 0 p (by simp)
        simpa using this
      have hfm : (p.headD (0, 0)).1 ≤ (p.getLastD (p.headD (0, 0))).1 := by
        match p, hp with
        | a :: t, _ =>
            rw [List.headD_cons]
            exact strictlyOrdered_head_le_getLastD t a a (hso _ (by simp))
      rw [refsFrom, refsWellFormed]
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
      refine ⟨⟨⟨hfm, trivial⟩, ?_⟩, ?_⟩
      · rw [flatMap_encodePair_length, hcount0]
      · exact ih (ordinal + 1) (base + (p.flatMap encodePair).length)
          (fun q hq => hne q (by simp [hq])) (fun q hq => hso q (by simp [hq]))
          (fun j page hj => by
            have := hcount (j + 1) page (by simpa using hj)
            rw [← this]
            congr 1
            omega)

/-- The directory is monotone in both ends of each page's subject range. -/
theorem refsMonotone_refsFrom : ∀ (PP : List (List (Nat × Nat))) (base : Nat),
    (∀ p ∈ PP, p ≠ []) → strictlyOrdered PP.flatten = true →
    refsMonotone (refsFrom base PP) = true := by
  intro PP
  induction PP with
  | nil => intro base _ _; simp [refsFrom, refsMonotone]
  | cons p PP' ih =>
      intro base hne hso
      match PP' with
      | [] => simp [refsFrom, refsMonotone]
      | q :: rest =>
          have hp : p ≠ [] := hne p (by simp)
          have hq : q ≠ [] := hne q (by simp)
          have htail : strictlyOrdered (q :: rest).flatten = true := by
            rw [List.flatten_cons] at hso
            have := strictlyOrdered_drop _ p.length hso
            rwa [List.drop_left] at this
          have hstep : (p.getLastD (p.headD (0, 0))).1 ≤ (q.headD (0, 0)).1 := by
            match p, hp, q, hq with
            | a :: t, _, b :: X, _ =>
                rw [List.headD_cons, List.headD_cons]
                refine strictlyOrdered_getLastD_le t a a b (X ++ rest.flatten) ?_
                rw [List.flatten_cons, List.flatten_cons] at hso
                simpa using hso
          have hpfm : (p.headD (0, 0)).1 ≤ (p.getLastD (p.headD (0, 0))).1 := by
            match p, hp with
            | a :: t, _ =>
                rw [List.headD_cons]
                refine strictlyOrdered_head_le_getLastD t a a ?_
                exact strictlyOrdered_of_mem_flatten _ _ hso (by simp)
          have hqfm : (q.headD (0, 0)).1 ≤ (q.getLastD (q.headD (0, 0))).1 := by
            match q, hq with
            | b :: X, _ =>
                rw [List.headD_cons]
                refine strictlyOrdered_head_le_getLastD X b b ?_
                exact strictlyOrdered_of_mem_flatten _ _ hso (by simp)
          rw [refsFrom, refsFrom, refsMonotone]
          simp only [Bool.and_eq_true, decide_eq_true_eq]
          refine ⟨⟨Nat.le_trans hpfm hstep, Nat.le_trans hstep hqfm⟩, ?_⟩
          have := ih (base + (p.flatMap encodePair).length)
            (fun r hr => hne r (by simp [hr])) htail
          rwa [refsFrom] at this

/-! ## Directory bytes -/

/-- A bounded range copy is the corresponding list slice. -/
theorem copyRange?_bytesOf (xs : List UInt8) (off len : Nat) (h : off + len ≤ xs.length) :
    copyRange? (bytesOf xs) off len = some (bytesOf ((xs.drop off).take len)) := by
  rw [copyRange?, if_pos (by rw [size_bytesOf]; exact h), extract_bytesOf,
    show off + len - off = len from by omega]

/-- Each directory entry occupies sixteen bytes. -/
theorem flatMap_encodeRef_length : ∀ (R : List PageRef),
    (R.flatMap encodeRef).length = R.length * directoryEntryBytes := by
  intro R
  induction R with
  | nil => simp
  | cons r rest ih =>
      simp only [List.flatMap_cons, List.length_append, encodeRef, ih,
        List.length_cons, writeU32LE_length, directoryEntryBytes]
      omega

/-- The directory decoder inverts `encodeRef` entry by entry. -/
theorem decodeRefsGo_ok : ∀ (R : List PageRef) (pre rest : List UInt8) (rev : List PageRef),
    (∀ r ∈ R, r.firstSubject < UInt32.size ∧ r.maxSubject < UInt32.size ∧
      r.offset < UInt32.size ∧ r.length < UInt32.size) →
    decodeRefsGo R.length (bytesOf (pre ++ (R.flatMap encodeRef ++ rest))) pre.length rev
      = some (rev.reverse ++ R) := by
  intro R
  induction R with
  | nil => intro pre rest rev _; simp [decodeRefsGo]
  | cons r R ih =>
      intro pre rest rev hbound
      obtain ⟨hfs, hmx, hoff, hlen⟩ := hbound r (by simp)
      have hbound' : ∀ x ∈ R, x.firstSubject < UInt32.size ∧ x.maxSubject < UInt32.size ∧
          x.offset < UInt32.size ∧ x.length < UInt32.size := fun x hx => hbound x (by simp [hx])
      have e0 : pre ++ ((r :: R).flatMap encodeRef ++ rest)
          = pre ++ (writeU32LE (UInt32.ofNat r.firstSubject) ++
              (writeU32LE (UInt32.ofNat r.maxSubject) ++
                (writeU32LE (UInt32.ofNat r.offset) ++
                  (writeU32LE (UInt32.ofNat r.length) ++ (R.flatMap encodeRef ++ rest))))) := by
        simp [encodeRef, List.append_assoc]
      have e1 : pre ++ ((r :: R).flatMap encodeRef ++ rest)
          = (pre ++ writeU32LE (UInt32.ofNat r.firstSubject)) ++
              (writeU32LE (UInt32.ofNat r.maxSubject) ++
                (writeU32LE (UInt32.ofNat r.offset) ++
                  (writeU32LE (UInt32.ofNat r.length) ++ (R.flatMap encodeRef ++ rest)))) := by
        rw [e0, ← List.append_assoc]
      have e2 : pre ++ ((r :: R).flatMap encodeRef ++ rest)
          = (pre ++ writeU32LE (UInt32.ofNat r.firstSubject) ++
              writeU32LE (UInt32.ofNat r.maxSubject)) ++
              (writeU32LE (UInt32.ofNat r.offset) ++
                (writeU32LE (UInt32.ofNat r.length) ++ (R.flatMap encodeRef ++ rest))) := by
        rw [e1, ← List.append_assoc]
      have e3 : pre ++ ((r :: R).flatMap encodeRef ++ rest)
          = (pre ++ writeU32LE (UInt32.ofNat r.firstSubject) ++
              writeU32LE (UInt32.ofNat r.maxSubject) ++
              writeU32LE (UInt32.ofNat r.offset)) ++
              (writeU32LE (UInt32.ofNat r.length) ++ (R.flatMap encodeRef ++ rest)) := by
        rw [e2, ← List.append_assoc]
      have e4 : pre ++ ((r :: R).flatMap encodeRef ++ rest)
          = (pre ++ encodeRef r) ++ (R.flatMap encodeRef ++ rest) := by
        simp [encodeRef, List.append_assoc]
      have hr0 : readU32At? (bytesOf (pre ++ ((r :: R).flatMap encodeRef ++ rest)))
          pre.length = some (UInt32.ofNat r.firstSubject) := by
        rw [readU32At?_bytesOf, e0]; exact readU32LE_at_prefix _ _ _
      have hr1 : readU32At? (bytesOf (pre ++ ((r :: R).flatMap encodeRef ++ rest)))
          (pre.length + 4) = some (UInt32.ofNat r.maxSubject) := by
        rw [readU32At?_bytesOf, e1,
          show pre.length + 4
            = (pre ++ writeU32LE (UInt32.ofNat r.firstSubject)).length by simp]
        exact readU32LE_at_prefix _ _ _
      have hr2 : readU32At? (bytesOf (pre ++ ((r :: R).flatMap encodeRef ++ rest)))
          (pre.length + 8) = some (UInt32.ofNat r.offset) := by
        rw [readU32At?_bytesOf, e2,
          show pre.length + 8
            = (pre ++ writeU32LE (UInt32.ofNat r.firstSubject) ++
              writeU32LE (UInt32.ofNat r.maxSubject)).length by simp]
        exact readU32LE_at_prefix _ _ _
      have hr3 : readU32At? (bytesOf (pre ++ ((r :: R).flatMap encodeRef ++ rest)))
          (pre.length + 12) = some (UInt32.ofNat r.length) := by
        rw [readU32At?_bytesOf, e3,
          show pre.length + 12
            = (pre ++ writeU32LE (UInt32.ofNat r.firstSubject) ++
              writeU32LE (UInt32.ofNat r.maxSubject) ++
              writeU32LE (UInt32.ofNat r.offset)).length by simp]
        exact readU32LE_at_prefix _ _ _
      have hentry : PageRef.mk (UInt32.ofNat r.firstSubject).toNat
          (UInt32.ofNat r.maxSubject).toNat (UInt32.ofNat r.offset).toNat
          (UInt32.ofNat r.length).toNat = r := by
        rw [u32_toNat_ofNat_of_lt hfs, u32_toNat_ofNat_of_lt hmx,
          u32_toNat_ofNat_of_lt hoff, u32_toNat_ofNat_of_lt hlen]
      have hpre : pre.length + directoryEntryBytes = (pre ++ encodeRef r).length := by
        simp [encodeRef, directoryEntryBytes]
      rw [List.length_cons, decodeRefsGo]
      simp only [hr0, hr1, hr2, hr3, bind, Option.bind]
      rw [hentry, hpre, e4, ih (pre ++ encodeRef r) rest (r :: rev) hbound']
      simp

/-! ## Page bytes -/

/-- The page decoder inverts `encodePair` pair by pair. -/
theorem decodePairsGo_ok : ∀ (page : List (Nat × Nat)) (pre rest : List UInt8)
    (rev : List (Nat × Nat)),
    (∀ x ∈ page, x.1 < UInt32.size ∧ x.2 < UInt32.size) →
    decodePairsGo page.length (bytesOf (pre ++ (page.flatMap encodePair ++ rest)))
        pre.length rev = some (rev.reverse ++ page) := by
  intro page
  induction page with
  | nil => intro pre rest rev _; simp [decodePairsGo]
  | cons x page ih =>
      intro pre rest rev hbound
      obtain ⟨hs, ho⟩ := hbound x (by simp)
      have hbound' : ∀ y ∈ page, y.1 < UInt32.size ∧ y.2 < UInt32.size :=
        fun y hy => hbound y (by simp [hy])
      have e0 : pre ++ ((x :: page).flatMap encodePair ++ rest)
          = pre ++ (writeU32LE (UInt32.ofNat x.1) ++
              (writeU32LE (UInt32.ofNat x.2) ++ (page.flatMap encodePair ++ rest))) := by
        simp [encodePair, List.append_assoc]
      have e1 : pre ++ ((x :: page).flatMap encodePair ++ rest)
          = (pre ++ writeU32LE (UInt32.ofNat x.1)) ++
              (writeU32LE (UInt32.ofNat x.2) ++ (page.flatMap encodePair ++ rest)) := by
        rw [e0, ← List.append_assoc]
      have e2 : pre ++ ((x :: page).flatMap encodePair ++ rest)
          = (pre ++ encodePair x) ++ (page.flatMap encodePair ++ rest) := by
        simp [encodePair, List.append_assoc]
      have hr0 : readU32At? (bytesOf (pre ++ ((x :: page).flatMap encodePair ++ rest)))
          pre.length = some (UInt32.ofNat x.1) := by
        rw [readU32At?_bytesOf, e0]; exact readU32LE_at_prefix _ _ _
      have hr1 : readU32At? (bytesOf (pre ++ ((x :: page).flatMap encodePair ++ rest)))
          (pre.length + 4) = some (UInt32.ofNat x.2) := by
        rw [readU32At?_bytesOf, e1,
          show pre.length + 4 = (pre ++ writeU32LE (UInt32.ofNat x.1)).length by simp]
        exact readU32LE_at_prefix _ _ _
      have hpair : ((UInt32.ofNat x.1).toNat, (UInt32.ofNat x.2).toNat) = x := by
        rw [u32_toNat_ofNat_of_lt hs, u32_toNat_ofNat_of_lt ho]
      have hpre : pre.length + pairBytes = (pre ++ encodePair x).length := by
        simp [encodePair, pairBytes]
      rw [List.length_cons, decodePairsGo]
      simp only [hr0, hr1, bind, Option.bind]
      rw [hpair, hpre, e2, ih (pre ++ encodePair x) rest (x :: rev) hbound']
      simp

/-- One page of encoded pairs decodes back to that page. -/
theorem decodePage?_ok (header : Prefix) (ordinal base : Nat) (p : List (Nat × Nat))
    (hne : p ≠ []) (hord : ordinal < header.pageCount)
    (hcount : pairsInPage header ordinal = p.length)
    (hso : strictlyOrdered p = true)
    (hbound : ∀ x ∈ p, x.1 < UInt32.size ∧ x.2 < UInt32.size ∧ x.2 < header.rowCount) :
    decodePage? header ordinal
        (PageRef.mk (p.headD (0, 0)).1 (p.getLastD (p.headD (0, 0))).1 base
          (p.flatMap encodePair).length)
        (bytesOf (p.flatMap encodePair)) = some p.toArray := by
  have hpairs : decodePairsGo (pairsInPage header ordinal)
      (bytesOf (p.flatMap encodePair)) 0 [] = some p := by
    rw [hcount]
    have := decodePairsGo_ok p [] [] []
      (fun x hx => ⟨(hbound x hx).1, (hbound x hx).2.1⟩)
    simpa using this
  match p, hne with
  | first :: t, _ =>
      have hany : (first :: t).any (fun pair => decide (pair.2 ≥ header.rowCount)) = false := by
        simp only [List.any_eq_false, decide_eq_true_eq, Nat.not_le]
        intro x hx
        exact (hbound x hx).2.2
      rw [decodePage?]
      simp only [size_bytesOf, bne_self_eq_false, Bool.or_false, ge_iff_le,
        decide_eq_true_eq]
      rw [if_neg (by omega)]
      simp only [hpairs, bind, Option.bind, List.headD_cons]
      simp only [bne_self_eq_false, Bool.false_eq_true, hso, Bool.not_true,
        hany, Bool.or_self, if_false]

/-! ## The page walk -/

/-- The page walk decodes every declared page and ends at the last byte. -/
theorem decodeAllPages_ok (header : Prefix) (allList : List UInt8) :
    ∀ (PP : List (List (Nat × Nat))) (i base : Nat) (pre : List UInt8)
      (rev : List (Nat × Nat)),
      allList = pre ++ PP.flatMap (fun p => p.flatMap encodePair) →
      pre.length = base →
      (∀ p ∈ PP, p ≠ []) →
      (∀ p ∈ PP, strictlyOrdered p = true) →
      (∀ p ∈ PP, ∀ x ∈ p, x.1 < UInt32.size ∧ x.2 < UInt32.size ∧ x.2 < header.rowCount) →
      (∀ j page, PP[j]? = some page → pairsInPage header (i + j) = page.length) →
      i + PP.length ≤ header.pageCount →
      decodeAllPages header (refsFrom base PP) (bytesOf allList) base i rev
        = some (rev.reverse ++ PP.flatten) := by
  intro PP
  induction PP with
  | nil =>
      intro i base pre rev hall hbase _ _ _ _ _
      have hsize : (bytesOf allList).size = base := by
        rw [size_bytesOf, hall, ← hbase]; simp
      simp only [refsFrom, decodeAllPages, hsize, beq_self_eq_true, if_true,
        List.flatten_nil, List.append_nil]
  | cons p PP' ih =>
      intro i base pre rev hall hbase hne hso hbound hcount hpc
      have hp : p ≠ [] := hne p (by simp)
      have hcount0 : pairsInPage header i = p.length := by
        have := hcount 0 p (by simp)
        simpa using this
      have hord : i < header.pageCount := by
        simp only [List.length_cons] at hpc
        omega
      have hall' : allList = pre ++ (p.flatMap encodePair ++
          PP'.flatMap (fun q => q.flatMap encodePair)) := by
        rw [hall]; simp
      have hlen : base + (p.flatMap encodePair).length ≤ allList.length := by
        rw [hall', ← hbase]
        simp only [List.length_append]
        omega
      have hdrop : allList.drop base = p.flatMap encodePair ++
          PP'.flatMap (fun q => q.flatMap encodePair) := by
        rw [hall', ← hbase, List.drop_left]
      have hcur : copyRange? (bytesOf allList) base (p.flatMap encodePair).length
          = some (bytesOf (p.flatMap encodePair)) := by
        rw [copyRange?_bytesOf allList base _ hlen, hdrop]
        simp
      rw [refsFrom, decodeAllPages]
      simp only [hcur, bind, Option.bind]
      rw [decodePage?_ok header i base p hp hord hcount0 (hso p (by simp))
        (hbound p (by simp))]
      simp only [List.toList_toArray]
      rw [ih (i + 1) (base + (p.flatMap encodePair).length)
        (pre ++ p.flatMap encodePair) (p.reverse ++ rev)
        (by rw [hall']; simp [List.append_assoc])
        (by rw [← hbase]; simp)
        (fun q hq => hne q (by simp [hq]))
        (fun q hq => hso q (by simp [hq]))
        (fun q hq => hbound q (by simp [hq]))
        (fun j page hj => by
          have := hcount (j + 1) page (by simpa using hj)
          rw [← this]
          congr 1
          omega)
        (by simp only [List.length_cons] at hpc; omega)]
      simp

/-! ## The fixed prefix -/

/-- A byte array's underlying list has its size. -/
theorem length_data_toList (b : ByteArray) : b.data.toList.length = b.size := by
  rw [Array.length_toList]
  rfl

/-- The `ByteArray.toList` loop accumulates the remaining bytes in order.
    Lean core states no relation between `ByteArray.toList` and the underlying
    array, and the encoder writes the SHA-256 field through `toList` while the
    decoder reads it back through `.data`, so the two views must be identified
    here. -/
theorem toList_loop_eq (b : ByteArray) : ∀ (n i : Nat) (r : List UInt8), b.size - i ≤ n →
    ByteArray.toList.loop b i r = r.reverse ++ b.data.toList.drop i := by
  intro n
  induction n with
  | zero =>
      intro i r hle
      have hnot : ¬ i < b.size := by omega
      have hdrop : b.data.toList.drop i = [] :=
        List.drop_eq_nil_of_le (by rw [length_data_toList]; omega)
      rw [ByteArray.toList.loop, if_neg hnot, hdrop, List.append_nil]
  | succ n ih =>
      intro i r hle
      by_cases hi : i < b.size
      · have hlt : i < b.data.toList.length := by rw [length_data_toList]; exact hi
        have hval : b.data.toList[i]'hlt = b.get! i := by
          show b.data[i] = b.data[i]!
          rw [getElem!_pos b.data i hi]
        rw [ByteArray.toList.loop, if_pos hi, ih (i + 1) (b.get! i :: r) (by omega),
          List.drop_eq_getElem_cons hlt, hval]
        simp
      · have hdrop : b.data.toList.drop i = [] :=
          List.drop_eq_nil_of_le (by rw [length_data_toList]; omega)
        rw [ByteArray.toList.loop, if_neg hi, hdrop, List.append_nil]

/-- A byte array's `toList` is the list of its underlying array. -/
theorem toList_eq_data_toList (b : ByteArray) : b.toList = b.data.toList := by
  have := toList_loop_eq b b.size 0 [] (by omega)
  simpa [ByteArray.toList] using this

/-- The codec's list view of a byte array is its `toList`. -/
theorem listOf_eq_toList (b : ByteArray) : listOf b = b.toList := by
  rw [listOf, toList_eq_data_toList]

/-- A byte array's list has its size. -/
theorem length_toList (b : ByteArray) : b.toList.length = b.size := by
  rw [toList_eq_data_toList, length_data_toList]

/-- The sixty-one byte prefix decodes to the header the encoder wrote. -/
theorem decodePrefix?_ok (target : ByteArray) (rows pairsN pageCnt dirLen areaLen : Nat)
    (htarget : target.size = 32) (hrows0 : 0 < rows) (hrows : rows < UInt32.size)
    (hpairs : pairsN < UInt32.size) (hpc : pageCnt < UInt32.size)
    (hdir : dirLen < UInt32.size) (harea : areaLen < UInt32.size)
    (hpr : pairsN = rows) (hpcv : pageCnt = (pairsN + pagePairs - 1) / pagePairs)
    (hdirv : dirLen = pageCnt * directoryEntryBytes) :
    decodePrefix? (bytesOf (writeU32LE magic ++ [version] ++ target.toList ++
        writeU32LE (UInt32.ofNat rows) ++ writeU32LE (UInt32.ofNat pairsN) ++
        writeU32LE (UInt32.ofNat pagePairs) ++ writeU32LE (UInt32.ofNat pageCnt) ++
        writeU32LE (UInt32.ofNat dirLen) ++ writeU32LE (UInt32.ofNat areaLen)))
      = some { targetIBKSha256 := target, rowCount := rows, pairCount := pairsN,
               pageCount := pageCnt, directoryBytes := dirLen, pagesBytes := areaLen } := by
  have htl : target.toList.length = 32 := by rw [length_toList, htarget]
  obtain ⟨L, hL⟩ : ∃ L, L = writeU32LE magic ++ [version] ++ target.toList ++
      writeU32LE (UInt32.ofNat rows) ++ writeU32LE (UInt32.ofNat pairsN) ++
      writeU32LE (UInt32.ofNat pagePairs) ++ writeU32LE (UInt32.ofNat pageCnt) ++
      writeU32LE (UInt32.ofNat dirLen) ++ writeU32LE (UInt32.ofNat areaLen) := ⟨_, rfl⟩
  rw [← hL]
  have hsize : (bytesOf L).size = prefixBytes := by
    rw [size_bytesOf, hL]
    simp only [List.length_append, writeU32LE_length, List.length_cons, List.length_nil, htl,
      prefixBytes]
  have hm : readU32At? (bytesOf L) 0 = some magic := by
    rw [readU32At?_bytesOf, hL,
      show writeU32LE magic ++ [version] ++ target.toList ++
          writeU32LE (UInt32.ofNat rows) ++ writeU32LE (UInt32.ofNat pairsN) ++
          writeU32LE (UInt32.ofNat pagePairs) ++ writeU32LE (UInt32.ofNat pageCnt) ++
          writeU32LE (UInt32.ofNat dirLen) ++ writeU32LE (UInt32.ofNat areaLen)
        = writeU32LE magic ++ ([version] ++ target.toList ++
          writeU32LE (UInt32.ofNat rows) ++ writeU32LE (UInt32.ofNat pairsN) ++
          writeU32LE (UInt32.ofNat pagePairs) ++ writeU32LE (UInt32.ofNat pageCnt) ++
          writeU32LE (UInt32.ofNat dirLen) ++ writeU32LE (UInt32.ofNat areaLen)) by
        simp [List.append_assoc]]
    exact readU32LE_writeU32LE_append _ _
  have hv : (bytesOf L)[4]? = some version := by
    rw [getElem?_bytesOf, hL]
    simp [writeU32LE]
  have hdrop5 : L.drop 5 = target.toList ++ (writeU32LE (UInt32.ofNat rows) ++
      writeU32LE (UInt32.ofNat pairsN) ++ writeU32LE (UInt32.ofNat pagePairs) ++
      writeU32LE (UInt32.ofNat pageCnt) ++ writeU32LE (UInt32.ofNat dirLen) ++
      writeU32LE (UInt32.ofNat areaLen)) := by
    rw [hL,
      show writeU32LE magic ++ [version] ++ target.toList ++
          writeU32LE (UInt32.ofNat rows) ++ writeU32LE (UInt32.ofNat pairsN) ++
          writeU32LE (UInt32.ofNat pagePairs) ++ writeU32LE (UInt32.ofNat pageCnt) ++
          writeU32LE (UInt32.ofNat dirLen) ++ writeU32LE (UInt32.ofNat areaLen)
        = (writeU32LE magic ++ [version]) ++ (target.toList ++
          (writeU32LE (UInt32.ofNat rows) ++ writeU32LE (UInt32.ofNat pairsN) ++
          writeU32LE (UInt32.ofNat pagePairs) ++ writeU32LE (UInt32.ofNat pageCnt) ++
          writeU32LE (UInt32.ofNat dirLen) ++ writeU32LE (UInt32.ofNat areaLen))) by
        simp [List.append_assoc]]
    exact List.drop_left' (by simp)
  have htgt : copyRange? (bytesOf L) 5 32 = some target := by
    rw [copyRange?_bytesOf L 5 32 (by rw [hL]; simp only [List.length_append,
      writeU32LE_length, List.length_cons, List.length_nil, htl]; omega), hdrop5,
      List.take_left' htl, ← listOf_eq_toList]
    exact congrArg some (bytesOf_listOf target)
  have hfield : ∀ (k : Nat) (pre suf : List UInt8) (val : UInt32),
      L = pre ++ (writeU32LE val ++ suf) → pre.length = k →
      readU32At? (bytesOf L) k = some val := by
    intro k pre suf val hsplit hlen
    rw [readU32At?_bytesOf, hsplit, ← hlen]
    exact readU32LE_at_prefix _ _ _
  have hlen37 : (writeU32LE magic ++ [version] ++ target.toList).length = 37 := by
    simp only [List.length_append, writeU32LE_length, List.length_cons, List.length_nil, htl]
  have h37 := hfield 37 (writeU32LE magic ++ [version] ++ target.toList)
    (writeU32LE (UInt32.ofNat pairsN) ++ writeU32LE (UInt32.ofNat pagePairs) ++
      writeU32LE (UInt32.ofNat pageCnt) ++ writeU32LE (UInt32.ofNat dirLen) ++
      writeU32LE (UInt32.ofNat areaLen)) (UInt32.ofNat rows)
    (by rw [hL]; simp [List.append_assoc]) hlen37
  have h41 := hfield 41 (writeU32LE magic ++ [version] ++ target.toList ++
      writeU32LE (UInt32.ofNat rows))
    (writeU32LE (UInt32.ofNat pagePairs) ++ writeU32LE (UInt32.ofNat pageCnt) ++
      writeU32LE (UInt32.ofNat dirLen) ++ writeU32LE (UInt32.ofNat areaLen))
    (UInt32.ofNat pairsN) (by rw [hL]; simp [List.append_assoc])
    (by simp only [List.length_append, writeU32LE_length, hlen37])
  have h45 := hfield 45 (writeU32LE magic ++ [version] ++ target.toList ++
      writeU32LE (UInt32.ofNat rows) ++ writeU32LE (UInt32.ofNat pairsN))
    (writeU32LE (UInt32.ofNat pageCnt) ++ writeU32LE (UInt32.ofNat dirLen) ++
      writeU32LE (UInt32.ofNat areaLen))
    (UInt32.ofNat pagePairs) (by rw [hL]; simp [List.append_assoc])
    (by simp only [List.length_append, writeU32LE_length, hlen37])
  have h49 := hfield 49 (writeU32LE magic ++ [version] ++ target.toList ++
      writeU32LE (UInt32.ofNat rows) ++ writeU32LE (UInt32.ofNat pairsN) ++
      writeU32LE (UInt32.ofNat pagePairs))
    (writeU32LE (UInt32.ofNat dirLen) ++ writeU32LE (UInt32.ofNat areaLen))
    (UInt32.ofNat pageCnt) (by rw [hL]; simp [List.append_assoc])
    (by simp only [List.length_append, writeU32LE_length, hlen37])
  have h53 := hfield 53 (writeU32LE magic ++ [version] ++ target.toList ++
      writeU32LE (UInt32.ofNat rows) ++ writeU32LE (UInt32.ofNat pairsN) ++
      writeU32LE (UInt32.ofNat pagePairs) ++ writeU32LE (UInt32.ofNat pageCnt))
    (writeU32LE (UInt32.ofNat areaLen))
    (UInt32.ofNat dirLen) (by rw [hL]; simp [List.append_assoc])
    (by simp only [List.length_append, writeU32LE_length, hlen37])
  have h57 := hfield 57 (writeU32LE magic ++ [version] ++ target.toList ++
      writeU32LE (UInt32.ofNat rows) ++ writeU32LE (UInt32.ofNat pairsN) ++
      writeU32LE (UInt32.ofNat pagePairs) ++ writeU32LE (UInt32.ofNat pageCnt) ++
      writeU32LE (UInt32.ofNat dirLen)) []
    (UInt32.ofNat areaLen) (by rw [hL]; simp [List.append_assoc])
    (by simp only [List.length_append, writeU32LE_length, hlen37])
  have hpp : (UInt32.ofNat pagePairs).toNat = pagePairs :=
    u32_toNat_ofNat_of_lt (by simp only [pagePairs]; decide)
  rw [decodePrefix?]
  simp only [hsize, bne_self_eq_false, Bool.false_eq_true, if_false, hm, hv, htgt,
    h37, h41, h45, h49, h53, h57, bind, Option.bind,
    u32_toNat_ofNat_of_lt hrows, u32_toNat_ofNat_of_lt hpairs,
    u32_toNat_ofNat_of_lt hpc, u32_toNat_ofNat_of_lt hdir,
    u32_toNat_ofNat_of_lt harea, hpp]
  rw [if_neg (by
      simp only [Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, not_or, Decidable.not_not]
      refine ⟨⟨⟨⟨by omega, hpr⟩, by simp⟩, hpcv⟩, hdirv⟩)]

/-! ## Whole-object round trip -/

/-- `pageBytes` is `chunks` at the default page size, pair-encoded. -/
theorem pageBytes_eq (ps : List (Nat × Nat)) :
    pageBytes ps = (chunks ps.length ps).map (fun p => p.flatMap encodePair) := rfl

/-- Flattening a map is the corresponding `flatMap`. -/
theorem flatten_map_eq_flatMap {α β : Type} (l : List α) (f : α → List β) :
    (l.map f).flatten = l.flatMap f := by
  induction l with
  | nil => simp
  | cons a t ih => simp [ih]

/-- A nonempty page contains its own first pair. -/
theorem headD_mem (p : List (Nat × Nat)) (h : p ≠ []) (d : Nat × Nat) : p.headD d ∈ p := by
  match p, h with
  | a :: t, _ => simp

/-- A nonempty page contains its own last pair. -/
theorem getLastD_headD_mem (p : List (Nat × Nat)) (h : p ≠ []) :
    p.getLastD (p.headD (0, 0)) ∈ p := by
  match p, h with
  | a :: t, _ =>
      rw [List.headD_cons, List.getLastD_cons]
      exact List.getLastD_mem_cons

/-- Every directory entry's subject range comes from one page. -/
theorem refsFrom_mem_subjects : ∀ (PP : List (List (Nat × Nat))) (base : Nat) (r : PageRef),
    r ∈ refsFrom base PP →
    ∃ p ∈ PP, r.firstSubject = (p.headD (0, 0)).1 ∧
      r.maxSubject = (p.getLastD (p.headD (0, 0))).1 := by
  intro PP
  induction PP with
  | nil => intro base r hmem; simp [refsFrom] at hmem
  | cons p rest ih =>
      intro base r hmem
      rw [refsFrom, List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · exact ⟨p, by simp, rfl, rfl⟩
      · obtain ⟨q, hq, h1, h2⟩ := ih _ r hmem
        exact ⟨q, by simp [hq], h1, h2⟩

/-- Every directory entry lies inside the page area it describes. -/
theorem refsFrom_offset_bound : ∀ (PP : List (List (Nat × Nat))) (base : Nat) (r : PageRef),
    r ∈ refsFrom base PP →
    r.offset + r.length ≤ base + (PP.map (fun p => (p.flatMap encodePair).length)).sum := by
  intro PP
  induction PP with
  | nil => intro base r hmem; simp [refsFrom] at hmem
  | cons p rest ih =>
      intro base r hmem
      rw [refsFrom, List.mem_cons] at hmem
      simp only [List.map_cons, List.sum_cons]
      rcases hmem with rfl | hmem
      · simp only []
        omega
      · have := ih (base + (p.flatMap encodePair).length) r hmem
        omega

/-- The decoder inverts the encoder on the byte object the encoder builds. The
    hypotheses are exactly the guards `supported` and `encode?` check. -/
theorem decode?_encoded (target : ByteArray) (rows : Nat) (ps : List (Nat × Nat))
    (htarget : target.size = 32) (hrows0 : 0 < rows) (hrowsfit : rows < UInt32.size)
    (hlenrows : ps.length = rows)
    (hall : ∀ x ∈ ps, x.1 < UInt32.size ∧ x.2 < rows)
    (hperm : offsetsPermutation ps rows = true)
    (hsorted : strictlyOrdered ps = true)
    (hpcfit : (pageRefs (pageBytes ps) (chunks ps.length ps)).length < UInt32.size)
    (hdirfit : ((pageRefs (pageBytes ps) (chunks ps.length ps)).flatMap encodeRef).length
      < UInt32.size)
    (hareafit : (pageBytes ps).flatten.length < UInt32.size) :
    decode? (bytesOf (writeU32LE magic ++ [version] ++
        (target.toList ++ writeU32LE (UInt32.ofNat rows) ++
          writeU32LE (UInt32.ofNat ps.length) ++ writeU32LE (UInt32.ofNat pagePairs) ++
          writeU32LE (UInt32.ofNat (pageRefs (pageBytes ps) (chunks ps.length ps)).length) ++
          writeU32LE (UInt32.ofNat
            ((pageRefs (pageBytes ps) (chunks ps.length ps)).flatMap encodeRef).length) ++
          writeU32LE (UInt32.ofNat (pageBytes ps).flatten.length) ++
          (pageRefs (pageBytes ps) (chunks ps.length ps)).flatMap encodeRef ++
          (pageBytes ps).flatten) ++
        writeU32LE (crc32c (target.toList ++ writeU32LE (UInt32.ofNat rows) ++
          writeU32LE (UInt32.ofNat ps.length) ++ writeU32LE (UInt32.ofNat pagePairs) ++
          writeU32LE (UInt32.ofNat (pageRefs (pageBytes ps) (chunks ps.length ps)).length) ++
          writeU32LE (UInt32.ofNat
            ((pageRefs (pageBytes ps) (chunks ps.length ps)).flatMap encodeRef).length) ++
          writeU32LE (UInt32.ofNat (pageBytes ps).flatten.length) ++
          (pageRefs (pageBytes ps) (chunks ps.length ps)).flatMap encodeRef ++
          (pageBytes ps).flatten))))
      = some { targetIBKSha256 := target, rowCount := rows, pairs := ps.toArray } := by
  -- structural facts about the page list and its directory
  obtain ⟨PP, hPP⟩ : ∃ PP, PP = chunks ps.length ps := ⟨_, rfl⟩
  have hPGeq : pageBytes ps = PP.map (fun p => p.flatMap encodePair) := by
    rw [pageBytes_eq, hPP]
  have hne : ∀ p ∈ PP, p ≠ [] := by rw [hPP]; exact chunks_ne_nil _ _
  have hflat : PP.flatten = ps := by rw [hPP]; exact chunks_flatten ps.length ps (Nat.le_refl _)
  have hPPlen : PP.length = (ps.length + pagePairs - 1) / pagePairs := by
    rw [hPP]; exact chunks_length ps.length ps (Nat.le_refl _)
  have hReq : pageRefs (pageBytes ps) (chunks ps.length ps) = refsFrom 0 PP := by
    rw [hPGeq, ← hPP]; exact pageRefs_eq PP hne
  rw [hReq, hPGeq]
  obtain ⟨R, hR⟩ : ∃ R, R = refsFrom 0 PP := ⟨_, rfl⟩
  rw [← hR]
  obtain ⟨dir, hdir⟩ : ∃ dir, dir = R.flatMap encodeRef := ⟨_, rfl⟩
  rw [← hdir]
  obtain ⟨area, harea⟩ : ∃ area, area = (PP.map (fun p => p.flatMap encodePair)).flatten :=
    ⟨_, rfl⟩
  rw [← harea]
  rw [hReq, ← hR] at hpcfit
  rw [hReq, ← hR, ← hdir] at hdirfit
  rw [hPGeq, ← harea] at hareafit
  obtain ⟨pay, hpay⟩ : ∃ pay, pay = target.toList ++ writeU32LE (UInt32.ofNat rows) ++
    writeU32LE (UInt32.ofNat ps.length) ++ writeU32LE (UInt32.ofNat pagePairs) ++
    writeU32LE (UInt32.ofNat R.length) ++ writeU32LE (UInt32.ofNat dir.length) ++
    writeU32LE (UInt32.ofNat area.length) ++ dir ++ area := ⟨_, rfl⟩
  rw [← hpay]
  obtain ⟨inp, hinp⟩ : ∃ inp, inp = writeU32LE magic ++ [version] ++ pay ++
    writeU32LE (crc32c pay) := ⟨_, rfl⟩
  rw [← hinp]
  obtain ⟨pre61, hpre61⟩ : ∃ q, q = writeU32LE magic ++ [version] ++ target.toList ++
    writeU32LE (UInt32.ofNat rows) ++ writeU32LE (UInt32.ofNat ps.length) ++
    writeU32LE (UInt32.ofNat pagePairs) ++ writeU32LE (UInt32.ofNat R.length) ++
    writeU32LE (UInt32.ofNat dir.length) ++ writeU32LE (UInt32.ofNat area.length) := ⟨_, rfl⟩
  -- derived structure
  have hRlen : R.length = PP.length := by rw [hR, refsFrom_length]
  have hdirlen : dir.length = R.length * directoryEntryBytes := by
    rw [hdir, flatMap_encodeRef_length]
  have hareaflat : area = PP.flatMap (fun p => p.flatMap encodePair) := by
    rw [harea, flatten_map_eq_flatMap]
  have harealen : area.length
      = (PP.map (fun p => (p.flatMap encodePair).length)).sum := by
    rw [harea, List.length_flatten, List.map_map]
    rfl
  have htl : target.toList.length = 32 := by rw [length_toList, htarget]
  have hmemps : ∀ p ∈ PP, ∀ x ∈ p, x ∈ ps := by
    intro p hp x hx
    rw [← hflat]
    exact List.mem_flatten.2 ⟨p, hp, hx⟩
  have hsoPP : ∀ p ∈ PP, strictlyOrdered p = true := by
    intro p hp
    exact strictlyOrdered_of_mem_flatten PP p (by rw [hflat]; exact hsorted) hp
  obtain ⟨header, hheader⟩ : ∃ header : Prefix, header =
    { targetIBKSha256 := target, rowCount := rows, pairCount := ps.length,
      pageCount := R.length, directoryBytes := dir.length, pagesBytes := area.length } := ⟨_, rfl⟩
  have hhtarget : header.targetIBKSha256 = target := by rw [hheader]
  have hhrows : header.rowCount = rows := by rw [hheader]
  have hhpair : header.pairCount = ps.length := by rw [hheader]
  have hhpc : header.pageCount = R.length := by rw [hheader]
  have hhdirb : header.directoryBytes = dir.length := by rw [hheader]
  have hhpages : header.pagesBytes = area.length := by rw [hheader]
  have hcount : ∀ (j : Nat) (page : List (Nat × Nat)), PP[j]? = some page →
      pairsInPage header (0 + j) = page.length := by
    intro j page hj
    have hjlt : j < PP.length := (List.getElem?_eq_some_iff.mp hj).1
    rw [hPPlen] at hjlt
    have hgot := chunks_getElem? ps.length ps j (Nat.le_refl _) hjlt
    rw [← hPP, hj, Option.some.injEq] at hgot
    rw [hgot]
    simp only [pairsInPage, hhpair, List.length_take, List.length_drop, Nat.zero_add]
  have hbound : ∀ p ∈ PP, ∀ x ∈ p, x.1 < UInt32.size ∧ x.2 < UInt32.size ∧
      x.2 < header.rowCount := by
    intro p hp x hx
    obtain ⟨h1, h2⟩ := hall x (hmemps p hp x hx)
    exact ⟨h1, Nat.lt_trans h2 hrowsfit, by rw [hhrows]; exact h2⟩
  have hdirbound : ∀ r ∈ R, r.firstSubject < UInt32.size ∧ r.maxSubject < UInt32.size ∧
      r.offset < UInt32.size ∧ r.length < UInt32.size := by
    intro r hr
    obtain ⟨p, hp, h1, h2⟩ := refsFrom_mem_subjects PP 0 r (hR ▸ hr)
    have hoff := refsFrom_offset_bound PP 0 r (hR ▸ hr)
    rw [← harealen] at hoff
    refine ⟨?_, ?_, by omega, by omega⟩
    · rw [h1]
      exact (hall _ (hmemps p hp _ (headD_mem p (hne p hp) (0, 0)))).1
    · rw [h2]
      exact (hall _ (hmemps p hp _ (getLastD_headD_mem p (hne p hp)))).1
  -- lengths and framings
  have hpaylen : pay.length = 56 + dir.length + area.length := by
    rw [hpay]
    simp only [List.length_append, writeU32LE_length, htl]
  have hinplen : inp.length = 65 + dir.length + area.length := by
    rw [hinp]
    simp only [List.length_append, writeU32LE_length, List.length_cons, List.length_nil, hpaylen]
    omega
  have hpre61len : pre61.length = 61 := by
    rw [hpre61]
    simp only [List.length_append, writeU32LE_length, List.length_cons, List.length_nil, htl]
  have hsplitA : inp = pre61 ++ (dir ++ (area ++ writeU32LE (crc32c pay))) := by
    rw [hinp, hpre61, hpay]; simp [List.append_assoc]
  have hsplitB : inp = (pre61 ++ dir) ++ (area ++ writeU32LE (crc32c pay)) := by
    rw [hsplitA, List.append_assoc]
  have hsplitC : inp = (writeU32LE magic ++ [version]) ++ (pay ++ writeU32LE (crc32c pay)) := by
    rw [hinp]; simp [List.append_assoc]
  have hsplitD : inp = (writeU32LE magic ++ [version] ++ pay) ++
      (writeU32LE (crc32c pay) ++ []) := by rw [hinp]; simp [List.append_assoc]
  -- the fixed prefix decodes to the header the encoder wrote
  have hex0 : (bytesOf inp).extract 0 prefixBytes = bytesOf pre61 := by
    rw [extract_bytesOf]
    congr 1
    rw [List.drop_zero, hsplitA]
    exact List.take_left' (by rw [hpre61len]; simp only [prefixBytes])
  have hprefix : decodePrefix? ((bytesOf inp).extract 0 prefixBytes) = some header := by
    rw [hex0, hpre61, hheader]
    exact decodePrefix?_ok target rows ps.length R.length dir.length area.length htarget
      hrows0 hrowsfit (by omega) hpcfit hdirfit hareafit hlenrows
      (by rw [hRlen, hPPlen]) hdirlen
  -- the payload the decoder hashes is the payload the encoder hashed
  have hpayex : (inp.drop 5).take (inp.length - crcBytes - 5) = pay := by
    rw [hinplen, hsplitC, List.drop_left' (by simp)]
    exact List.take_left' (by rw [hpaylen]; simp only [crcBytes]; omega)
  have hcrcread : readU32LE inp (inp.length - crcBytes) = some (crc32c pay) := by
    rw [hinplen, hsplitD,
      show 65 + dir.length + area.length - crcBytes
        = (writeU32LE magic ++ [version] ++ pay).length by
        simp only [List.length_append, writeU32LE_length, List.length_cons,
          List.length_nil, hpaylen, crcBytes]
        omega]
    exact readU32LE_at_prefix _ _ _
  -- the directory and page areas are the byte ranges the encoder laid out
  have hdirex : (inp.drop prefixBytes).take (prefixBytes + dir.length - prefixBytes) = dir := by
    rw [show prefixBytes + dir.length - prefixBytes = dir.length by omega, hsplitA,
      List.drop_left' (by rw [hpre61len]; simp only [prefixBytes])]
    exact List.take_left' rfl
  have hpagex : (inp.drop (prefixBytes + dir.length)).take
      (prefixBytes + dir.length + area.length - (prefixBytes + dir.length)) = area := by
    rw [show prefixBytes + dir.length + area.length - (prefixBytes + dir.length)
        = area.length by omega, hsplitB,
      List.drop_left' (by
        simp only [List.length_append, hpre61len, prefixBytes])]
    exact List.take_left' rfl
  -- the directory round trips
  have hdecdir : decodeDirectory? header (bytesOf dir) = some R := by
    have hgo : decodeRefsGo R.length (bytesOf dir) 0 [] = some R := by
      have hx := decodeRefsGo_ok R [] [] [] hdirbound
      rw [hdir]
      simpa using hx
    have hwf : refsWellFormed header R 0 0 = true := by
      rw [hR]
      exact refsWellFormed_refsFrom header PP 0 0 hne hsoPP hcount
    have hmono : refsMonotone R = true := by
      rw [hR]
      exact refsMonotone_refsFrom PP 0 hne (by rw [hflat]; exact hsorted)
    have hsum : R.foldl (fun total ref => total + ref.length) 0 = area.length := by
      rw [hR, refsFrom_sum, harealen, Nat.zero_add]
    rw [decodeDirectory?]
    simp only [size_bytesOf, hhdirb, bne_self_eq_false, Bool.false_eq_true, if_false, hhpc,
      hgo, bind, Option.bind, hwf, hmono, hsum, hhpages, Bool.not_true, Bool.or_self]
  -- the pages round trip
  have hdecpages : decodeAllPages header R (bytesOf area) 0 0 [] = some ps := by
    have hkey := decodeAllPages_ok header area PP 0 0 [] [] (by rw [hareaflat]; simp) rfl
      hne hsoPP hbound hcount (by simp [hhpc, hRlen])
    rw [← hR] at hkey
    rw [hkey, List.reverse_nil, List.nil_append, hflat]
  -- assemble
  rw [decode?]
  simp only [size_bytesOf]
  rw [if_neg (by rw [hinplen]; simp only [prefixBytes, crcBytes]; omega)]
  simp only [hprefix, bind, Option.bind, hhdirb, hhpages]
  rw [if_neg (by
      simp only [hinplen, prefixBytes, crcBytes, bne_iff_ne, ne_eq, Decidable.not_not]
      omega)]
  simp only [extract_bytesOf, listOf_bytesOf, hpayex, hcrcread, bne_self_eq_false,
    Bool.false_eq_true, if_false, hdirex, hpagex, hdecdir, hdecpages,
    hhrows, hlenrows, hsorted, hperm, Bool.not_true, Bool.or_self, hhtarget]

/-- The SRI2 codec round trip: whatever `encode?` accepts, `decode?` returns
unchanged. The only hypothesis is that `encode?` accepted the input.

Every condition the decoder needs is a consequence of `encode?`'s own guards.
`supported` fixes the SHA-256 field at thirty-two bytes, the row count in
`0 < rows < 2^32`, the pair count at the row count, every subject below
`2^32` and every row offset below the row count, and — the conjunct added for
this proof — that the row offsets are a permutation of `0 .. rows - 1`, which
is what `decode?` re-checks with `offsetsPermutation`. The pair ordering is
`encode?`'s own second guard, and the three remaining size conditions are its
third. -/
theorem decode?_encode? (index : Index) (bytes : ByteArray) (h : encode? index = some bytes) :
    decode? bytes = some index := by
  simp only [encode?] at h
  split at h
  · exact absurd h (by simp)
  · rename_i hsupp
    split at h
    · exact absurd h (by simp)
    · rename_i hordered
      split at h
      · exact absurd h (by simp)
      · rename_i hguard
        injection h with h
        subst h
        have hs : supported index = true := by simpa using hsupp
        simp only [supported, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, fitsU32,
          List.all_eq_true, gt_iff_lt] at hs
        obtain ⟨⟨⟨⟨⟨htsize, hrows0⟩, hrowsfit⟩, hsize⟩, hall⟩, hperm⟩ := hs
        have hlenrows : index.pairs.toList.length = index.rowCount := by
          rw [Array.length_toList]; exact hsize
        have hall' : ∀ x ∈ index.pairs.toList, x.1 < UInt32.size ∧ x.2 < index.rowCount := hall
        have hsorted : strictlyOrdered index.pairs.toList = true := by
          cases hx : strictlyOrdered index.pairs.toList
          · rw [hx] at hordered; simp at hordered
          · rfl
        simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Nat.not_le] at hguard
        rw [decode?_encoded index.targetIBKSha256 index.rowCount index.pairs.toList
          htsize hrows0 hrowsfit hlenrows hall' hperm hsorted
          (by omega) (by omega) (by omega)]

#print axioms decodePrefix?_ok
#print axioms decodeRefsGo_ok
#print axioms decodeAllPages_ok
#print axioms decode?_encoded
#print axioms decode?_encode?

end L4Factoidal.Storage.SubjectRowIndexWireV2
