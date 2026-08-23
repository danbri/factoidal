/-
L4Factoidal.Cottas.SortByKey — an insertion sort with its sortedness
proof, keyed by a `Nat`.

Not a port of an F\* module. It exists because two COTTAS writers need
the same thing: the reader binary-searches a region, so the writer must
emit that region strictly ascending by a `Nat` key, and the writers are
the place to establish it.

* `CompoundPresenceWriter` keys `(predicate, object)` pairs by
  `pairCode`, so ascending key order is ascending packed-u64 order.
* `OffsetsWriter` keys subject ids by themselves.

The order is STRICT, so `sortedByKey` states ascending order and
duplicate-freedom at once, and `sortByKey` drops repeats.
-/
namespace L4Factoidal.Cottas

variable {α : Type}

/-- Every key in the list is greater than `c`. -/
def allKeysGt (key : α → Nat) (c : Nat) : List α → Bool
  | []      => true
  | y :: ys => c < key y && allKeysGt key c ys

/-- Strictly ascending by key, hence duplicate-free on keys. -/
def sortedByKey (key : α → Nat) : List α → Bool
  | []      => true
  | x :: xs => allKeysGt key (key x) xs && sortedByKey key xs

def insertByKey (key : α → Nat) (x : α) : List α → List α
  | []      => [x]
  | y :: ys =>
      if key x == key y then y :: ys
      else if key x < key y then x :: y :: ys
      else y :: insertByKey key x ys

def sortByKey (key : α → Nat) : List α → List α
  | []      => []
  | x :: xs => insertByKey key x (sortByKey key xs)

theorem allKeysGt_weaken (key : α → Nat) (c d : Nat) (l : List α)
    (hcd : c < d) (h : allKeysGt key d l = true) : allKeysGt key c l = true := by
  induction l with
  | nil => simp [allKeysGt]
  | cons y ys ih =>
      simp only [allKeysGt, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
      exact ⟨by omega, ih h.2⟩

theorem allKeysGt_insertByKey (key : α → Nat) (c : Nat) (x : α) (l : List α)
    (hx : c < key x) (hl : allKeysGt key c l = true) :
    allKeysGt key c (insertByKey key x l) = true := by
  induction l with
  | nil =>
      simp only [insertByKey, allKeysGt, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨hx, trivial⟩
  | cons y ys ih =>
      simp only [allKeysGt, Bool.and_eq_true, decide_eq_true_eq] at hl
      rcases Nat.lt_trichotomy (key x) (key y) with h | h | h
      · have hne : ¬ (key x = key y) := by omega
        simp only [insertByKey, beq_iff_eq, hne, if_false, h, if_pos,
                   allKeysGt, Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨hx, hl.1, hl.2⟩
      · simp only [insertByKey, beq_iff_eq, h, if_pos, allKeysGt,
                   Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨hl.1, hl.2⟩
      · have hne : ¬ (key x = key y) := by omega
        have hnl : ¬ (key x < key y) := by omega
        simp only [insertByKey, beq_iff_eq, hne, hnl, if_false,
                   allKeysGt, Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨hl.1, ih hl.2⟩

theorem insertByKey_sorted (key : α → Nat) (x : α) (l : List α)
    (hl : sortedByKey key l = true) :
    sortedByKey key (insertByKey key x l) = true := by
  induction l with
  | nil =>
      simp only [insertByKey, sortedByKey, allKeysGt, Bool.and_eq_true]
      exact ⟨trivial, trivial⟩
  | cons y ys ih =>
      simp only [sortedByKey, Bool.and_eq_true] at hl
      rcases Nat.lt_trichotomy (key x) (key y) with h | h | h
      · have hne : ¬ (key x = key y) := by omega
        have hgt : allKeysGt key (key x) (y :: ys) = true := by
          simp only [allKeysGt, Bool.and_eq_true, decide_eq_true_eq]
          exact ⟨h, allKeysGt_weaken key _ _ _ h hl.1⟩
        simp only [insertByKey, beq_iff_eq, hne, if_false, h, if_pos,
                   sortedByKey, Bool.and_eq_true]
        exact ⟨hgt, hl.1, hl.2⟩
      · simp only [insertByKey, beq_iff_eq, h, if_pos, sortedByKey,
                   Bool.and_eq_true]
        exact ⟨hl.1, hl.2⟩
      · have hne : ¬ (key x = key y) := by omega
        have hnl : ¬ (key x < key y) := by omega
        simp only [insertByKey, beq_iff_eq, hne, hnl, if_false,
                   sortedByKey, Bool.and_eq_true]
        exact ⟨allKeysGt_insertByKey key _ _ _ h hl.1, ih hl.2⟩

/-- The reader-side precondition, established on the writer side. -/
theorem sortByKey_sorted (key : α → Nat) (l : List α) :
    sortedByKey key (sortByKey key l) = true := by
  induction l with
  | nil => simp [sortByKey, sortedByKey]
  | cons x xs ih => exact insertByKey_sorted key x (sortByKey key xs) ih

/-! ## Build-time checks -/

#guard sortByKey id [3, 1, 2] == [1, 2, 3]
#guard sortByKey id [1, 1, 1] == [1]
#guard sortByKey id ([] : List Nat) == []
#guard sortedByKey id (sortByKey id [9, 0, 4, 4, 7])
#guard (sortByKey id [9, 0, 4, 4, 7]).length == 4
#guard !sortedByKey id [1, 1]
#guard !sortedByKey id [2, 1]
#guard sortByKey (fun x => x.1) [(2, 'b'), (1, 'a')] == [(1, 'a'), (2, 'b')]

#print axioms sortByKey_sorted

end L4Factoidal.Cottas
