/-
L4Factoidal.Regex.RegexTheorems — the correctness theorems of the regex
engine, ported from the `Lemma`s of `Regex.Syntax.fst`,
`Regex.Derivative.fst` and `Regex.Exec.fst`.

Every theorem is proved by structural induction with no `sorry`, no
axiom beyond Lean's standard three, and no `native_decide`
(`#print axioms` lines at the end). Sections follow the F* modules:

  §1 Syntax      — `nullable_correct`, the smart-constructor language
                   lemmas `smartAlt_ok` … `smartStar_ok`, the split
                   enumeration facts they rest on, and the injectivity
                   of the structural order (`reCmp_eq`).
  §2 Derivative  — the split-shift lemmas, `deriv_correct`
                   (`mem (deriv c r) w = mem r (c :: w)` for the FULL
                   AST), `derivWord_correct`, `accepts_correct`.
  §3 Exec        — the ACI flatten preserves the language (`ealt_ok`,
                   `eand_ok`), `nderiv_correct`, `acceptsNorm_correct`,
                   and `acceptsNorm_eq_proven` (the fast path agrees with
                   the reference matcher on every input).

Translation notes. The F* states its lemmas as `<==>` between booleans;
here they are Boolean EQUALITIES, which are stronger and rewrite
directly. The F* shift lemmas exist twice (`cat_shift` on `deriv`,
`cat_shift_gen` on any derivative meeting the spec); the generic form is
the only one needed here and serves both `deriv` and `nderiv`. Because
the Lean `memStar` carries a fuel (see `Syntax.lean`), one lemma with no
F* counterpart is added: `memStar_fuel`, any fuel `≥ |w|` gives the same
answer. `take_zero` / `drop_zero` / `take_cons` / `drop_cons` are the
core lemmas `List.take_zero`, `List.drop_zero`, `List.take_succ_cons`,
`List.drop_succ_cons`.
-/
import L4Factoidal.Regex.Exec

namespace L4Factoidal.Regex

open Re

/-! ## §1 Syntax -/

/-! Equation lemmas for `mem`, stated per constructor so a proof can
unfold ONE application without `simp [mem]` eta-expanding the partial
applications `mem a` that the split enumerators take as arguments. -/
@[simp] theorem mem_empty (w : List Nat) : mem .empty w = false := rfl
@[simp] theorem mem_eps (w : List Nat) : mem .eps w = w.isEmpty := rfl
theorem mem_alt (a b : Re) (w : List Nat) : mem (.alt a b) w = (mem a w || mem b w) := rfl
theorem mem_inter (a b : Re) (w : List Nat) : mem (.inter a b) w = (mem a w && mem b w) := rfl
theorem mem_compl (a : Re) (w : List Nat) : mem (.compl a) w = !(mem a w) := rfl
theorem mem_cat (a b : Re) (w : List Nat) :
    mem (.cat a b) w = catTry (mem a) (mem b) w w.length := rfl
theorem mem_star (a : Re) (w : List Nat) : mem (.star a) w = memStar (mem a) w.length w := rfl

/-- Every regex has size at least 1 (the F* refinement on `size`). -/
theorem size_pos (r : Re) : 1 ≤ r.size := by
  cases r <;> simp [Re.size] <;> omega

/-- F* `nullable_correct`: `nullable r <==> mem r []`. -/
theorem nullable_correct (r : Re) : nullable r = mem r [] := by
  induction r with
  | empty => rfl
  | eps => rfl
  | ranges rs => rfl
  | cat a b iha ihb => simp [nullable, mem, catTry, iha, ihb]
  | alt a b iha ihb => simp [nullable, mem, iha, ihb]
  | inter a b iha ihb => simp [nullable, mem, iha, ihb]
  | compl a iha => simp [nullable, mem, iha]
  | star a _ => rfl

theorem mem_universal (w : List Nat) : mem rUniversal w = true := by
  simp [rUniversal, mem]

/-- F* `smart_alt_ok`. -/
theorem smartAlt_ok (a b : Re) (w : List Nat) :
    mem (smartAlt a b) w = (mem a w || mem b w) := by
  unfold smartAlt
  split
  · subst a; simp [mem]
  · split
    · subst b; simp [mem]
    · split
      · subst b; simp
      · split
        · rename_i h
          rcases Bool.or_eq_true _ _ |>.mp h with h1 | h1
          · rw [decide_eq_true_iff] at h1; subst a; simp [mem_universal]
          · rw [decide_eq_true_iff] at h1; subst b; simp [mem_universal]
        · split
          · rfl
          · simp [mem, Bool.or_comm]

/-- F* `smart_and_ok`. -/
theorem smartAnd_ok (a b : Re) (w : List Nat) :
    mem (smartAnd a b) w = (mem a w && mem b w) := by
  unfold smartAnd
  split
  · rename_i h
    rcases Bool.or_eq_true _ _ |>.mp h with h1 | h1
    · rw [decide_eq_true_iff] at h1; subst a; simp [mem]
    · rw [decide_eq_true_iff] at h1; subst b; simp [mem]
  · split
    · subst a; simp [mem_universal]
    · split
      · subst b; simp [mem_universal]
      · split
        · subst b; simp
        · split
          · rfl
          · simp [mem, Bool.and_comm]

/-- F* `smart_not_ok`. -/
theorem smartNot_ok (a : Re) (w : List Nat) : mem (smartNot a) w = !(mem a w) := by
  cases a <;> simp [smartNot, mem]

/-- F* `cat_empty_left`: no split can match against the empty language. -/
theorem catTry_empty_left (mb : List Nat → Bool) (w : List Nat) (k : Nat) :
    catTry (mem .empty) mb w k = false := by
  induction k with
  | zero => simp [catTry]
  | succ k ih => simp [catTry, ih]

/-- F* `cat_empty_right`. -/
theorem catTry_empty_right (ma : List Nat → Bool) (w : List Nat) (k : Nat) :
    catTry ma (mem .empty) w k = false := by
  induction k with
  | zero => simp [catTry]
  | succ k ih => simp [catTry, ih]

/-- F* `cat_eps_left`: eps matches only the `k = 0` split. -/
theorem catTry_eps_left (mb : List Nat → Bool) (w : List Nat) (k : Nat) :
    catTry (mem .eps) mb w k = mb w := by
  induction k with
  | zero => simp [catTry]
  | succ k ih =>
    cases w with
    | nil => simp [catTry, ih]
    | cons c t => simp [catTry, ih]

/-- F* `cat_eps_right_below`: below the full length the suffix is non-empty. -/
theorem catTry_eps_right_below (ma : List Nat → Bool) (w : List Nat) (k : Nat)
    (hk : k < w.length) : catTry ma (mem .eps) w k = false := by
  induction k with
  | zero =>
    cases w with
    | nil => simp at hk
    | cons c t => simp [catTry]
  | succ k ih =>
    have hne : (w.drop (k + 1)).isEmpty = false := by
      cases h : w.drop (k + 1) with
      | nil => exact absurd (List.drop_eq_nil_iff.mp h) (by omega)
      | cons _ _ => rfl
    simp [catTry, hne, ih (by omega)]

/-- F* `cat_eps_right`: at the full length only the `k = |w|` split contributes. -/
theorem catTry_eps_right (ma : List Nat → Bool) (w : List Nat) :
    catTry ma (mem .eps) w w.length = ma w := by
  cases h : w.length with
  | zero =>
    have : w = [] := List.length_eq_zero_iff.mp h
    subst this; simp [catTry]
  | succ k =>
    have hfull : w.take (k + 1) = w := by rw [← h]; exact List.take_length
    have hdrop : w.drop (k + 1) = [] := by rw [← h]; exact List.drop_length
    simp [catTry, hfull, hdrop, catTry_eps_right_below ma w k (by omega)]

/-- F* `smart_cat_ok`: `smartCat` preserves the language of `cat`. -/
theorem smartCat_ok (a b : Re) (w : List Nat) :
    mem (smartCat a b) w = mem (.cat a b) w := by
  unfold smartCat
  split
  · rename_i h
    rcases Bool.or_eq_true _ _ |>.mp h with h1 | h1
    · rw [decide_eq_true_iff] at h1; subst a; rw [mem_cat, catTry_empty_left]; rfl
    · rw [decide_eq_true_iff] at h1; subst b; rw [mem_cat, catTry_empty_right]; rfl
  · split
    · subst a; rw [mem_cat, catTry_eps_left]
    · split
      · subst b; rw [mem_cat, catTry_eps_right]
      · rfl

/-- F* `star_try_empty`. -/
theorem starTry_empty (ms : List Nat → Bool) (w : List Nat) (k : Nat) :
    starTry (mem .empty) ms w k = false := by
  induction k with
  | zero => rfl
  | succ k ih => simp [starTry, ih]

/-- F* `star_empty_lang`: `empty*` accepts only the empty word. -/
theorem memStar_empty (n : Nat) (w : List Nat) : memStar (mem .empty) n w = w.isEmpty := by
  cases n with
  | zero => rfl
  | succ n =>
    cases w with
    | nil => rfl
    | cons c t => simp [memStar, starTry_empty]

/-- F* `star_try_eps`. -/
theorem starTry_eps (ms : List Nat → Bool) (c : Nat) (t : List Nat) (k : Nat) :
    starTry (mem .eps) ms (c :: t) k = false := by
  induction k with
  | zero => rfl
  | succ k ih => simp [starTry, ih]

/-- F* `star_eps_lang`: `eps*` accepts only the empty word. -/
theorem memStar_eps (n : Nat) (w : List Nat) : memStar (mem .eps) n w = w.isEmpty := by
  cases n with
  | zero => rfl
  | succ n =>
    cases w with
    | nil => rfl
    | cons c t => simp [memStar, starTry_eps]

/-- F* `smart_star_ok`, for non-star arguments (the `star (star x)`
case is star idempotence, deferred in both trees and off the verified
path: `nderiv` never calls `smartStar`). -/
theorem smartStar_ok (a : Re) (h : ∀ x, a ≠ .star x) (w : List Nat) :
    mem (smartStar a) w = mem (.star a) w := by
  cases a with
  | empty => rw [smartStar, mem_star, memStar_empty]; rfl
  | eps => rw [smartStar, mem_star, memStar_eps]; rfl
  | star x => exact absurd rfl (h x)
  | _ => rfl

/-- F* `ranges_cmp_eq`: the range order is injective at `.eq`. -/
theorem rangesCmp_eq (x y : List (Nat × Nat)) (h : rangesCmp x y = .eq) : x = y := by
  induction x generalizing y with
  | nil => cases y with
    | nil => rfl
    | cons _ _ => simp [rangesCmp] at h
  | cons p xs ih =>
    cases y with
    | nil => simp [rangesCmp] at h
    | cons q ys =>
      obtain ⟨a1, b1⟩ := p
      obtain ⟨a2, b2⟩ := q
      simp only [rangesCmp] at h
      split at h
      · split at h <;> simp at h
      · split at h
        · split at h <;> simp at h
        · rename_i h1 h2
          simp at h1 h2; subst h1; subst h2
          rw [ih ys h]

/-- F* `regex_cmp_eq`: the structural order is injective at `.eq`, so the
ACI dedup in `Exec.insertRegex` only ever drops a structurally-equal
(hence language-equal) operand. -/
theorem reCmp_eq (a b : Re) (h : reCmp a b = .eq) : a = b := by
  induction a generalizing b with
  | empty => cases b <;> simp [reCmp, Re.tag] at h ⊢
  | eps => cases b <;> simp [reCmp, Re.tag] at h ⊢
  | ranges x =>
    cases b <;> simp [reCmp, Re.tag] at h ⊢
    exact rangesCmp_eq _ _ h
  | cat a1 a2 ih1 ih2 =>
    cases b <;> simp [reCmp, Re.tag] at h ⊢
    split at h
    · exact ⟨ih1 _ (by assumption), ih2 _ h⟩
    · simp_all
  | alt a1 a2 ih1 ih2 =>
    cases b <;> simp [reCmp, Re.tag] at h ⊢
    split at h
    · exact ⟨ih1 _ (by assumption), ih2 _ h⟩
    · simp_all
  | inter a1 a2 ih1 ih2 =>
    cases b <;> simp [reCmp, Re.tag] at h ⊢
    split at h
    · exact ⟨ih1 _ (by assumption), ih2 _ h⟩
    · simp_all
  | compl a1 ih1 =>
    cases b <;> simp [reCmp, Re.tag] at h ⊢
    exact ih1 _ h
  | star a1 ih1 =>
    cases b <;> simp [reCmp, Re.tag] at h ⊢
    exact ih1 _ h

/-! ## §2 Derivative -/

open Derivative

/-- F* `cat_shift` / `cat_shift_gen`: the split enumeration on `c :: w`
equals the `j = 0` term OR the enumeration of the derivative on `w`,
for ANY `da` that is pointwise the derivative of `ma` by `c`. -/
theorem catTry_shift (ma mb da : List Nat → Bool) (c : Nat) (w : List Nat) (k : Nat)
    (h : ∀ w', da w' = ma (c :: w')) :
    catTry ma mb (c :: w) (k + 1) = ((ma [] && mb (c :: w)) || catTry da mb w k) := by
  induction k with
  | zero => simp [catTry, h, Bool.or_comm]
  | succ k ih =>
    rw [catTry, ih, catTry, List.take_succ_cons, List.drop_succ_cons, h]
    exact Bool.or_left_comm _ _ _

/-- F* `star_shift` / `star_shift_gen`. -/
theorem starTry_shift (ma ms da : List Nat → Bool) (c : Nat) (w : List Nat) (k : Nat)
    (h : ∀ w', da w' = ma (c :: w')) :
    starTry ma ms (c :: w) (k + 1) = catTry da ms w k := by
  induction k with
  | zero => simp [starTry, catTry, h]
  | succ k ih =>
    rw [starTry, ih, catTry, List.take_succ_cons, List.drop_succ_cons, h]

/-- `catTry` only inspects `mb` on the suffixes `w.drop j`, `j ≤ k`. -/
theorem catTry_congr_right (ma mb mb' : List Nat → Bool) (w : List Nat) (k : Nat)
    (h : ∀ j, j ≤ k → mb (w.drop j) = mb' (w.drop j)) :
    catTry ma mb w k = catTry ma mb' w k := by
  induction k with
  | zero =>
    have h0 := h 0 (Nat.le_refl _)
    simp only [List.drop_zero] at h0
    simp [catTry, h0]
  | succ k ih =>
    simp only [catTry]
    rw [h (k + 1) (Nat.le_refl _), ih (fun j hj => h j (Nat.le_succ_of_le hj))]

/-- `starTry` only inspects `ms` on the suffixes `w.drop (j + 1)`, `j < k`. -/
theorem starTry_congr_right (ma ms ms' : List Nat → Bool) (w : List Nat) (k : Nat)
    (h : ∀ j, j < k → ms (w.drop (j + 1)) = ms' (w.drop (j + 1))) :
    starTry ma ms w k = starTry ma ms' w k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [starTry]
    rw [h k (Nat.lt_succ_self _), ih (fun j hj => h j (Nat.lt_succ_of_lt hj))]

/-- No F* counterpart (the F* `mem` needs no fuel): any fuel `≥ |w|` gives
the same star membership. -/
theorem memStar_fuel (ma : List Nat → Bool) (n m : Nat) (w : List Nat)
    (hn : w.length ≤ n) (hm : w.length ≤ m) : memStar ma n w = memStar ma m w := by
  induction n generalizing w m with
  | zero =>
    have : w = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hn)
    subst this
    cases m <;> rfl
  | succ n ih =>
    cases w with
    | nil => cases m <;> rfl
    | cons c t =>
      cases m with
      | zero => simp at hm
      | succ m =>
        simp only [memStar]
        apply starTry_congr_right
        intro j _
        apply ih
        · simp only [List.length_drop, List.length_cons] at hn ⊢; omega
        · simp only [List.length_drop, List.length_cons] at hm ⊢; omega

theorem memStar_length (ma : List Nat → Bool) (n : Nat) (w : List Nat) (hn : w.length ≤ n) :
    memStar ma n w = memStar ma w.length w :=
  memStar_fuel ma n w.length w hn (Nat.le_refl _)

/-- F* `deriv_cat_w` generalised over the derivative function: the cat
case of derivative correctness, given the hypotheses for `a` and `b`. -/
theorem deriv_cat_w (a b da db : Re) (c : Nat) (w : List Nat)
    (ha : ∀ w', mem da w' = mem a (c :: w'))
    (hb : ∀ w', mem db w' = mem b (c :: w')) :
    (if nullable a then (mem (.cat da b) w || mem db w) else mem (.cat da b) w)
      = mem (.cat a b) (c :: w) := by
  have hshift := catTry_shift (mem a) (mem b) (mem da) c w w.length ha
  rw [mem_cat a b, List.length_cons, hshift, mem_cat da b, hb, nullable_correct a]
  cases h : mem a [] <;> simp [Bool.or_comm]

/-- F* `deriv_star_w` generalised over the derivative function. -/
theorem deriv_star_w (a da : Re) (c : Nat) (w : List Nat)
    (ha : ∀ w', mem da w' = mem a (c :: w')) :
    mem (.cat da (.star a)) w = mem (.star a) (c :: w) := by
  have hshift := starTry_shift (mem a) (memStar (mem a) w.length) (mem da) c w w.length ha
  rw [mem_cat, mem_star, List.length_cons]
  simp only [memStar, List.length_cons]
  rw [hshift]
  apply catTry_congr_right
  intro j _
  rw [mem_star]
  exact memStar_fuel _ _ _ _ (Nat.le_refl _) (by rw [List.length_drop]; exact Nat.sub_le _ _)

/-- F* `deriv_correct`, for the FULL AST including `inter` and `compl`. -/
theorem deriv_correct (c : Nat) (r : Re) : ∀ w, mem (deriv c r) w = mem r (c :: w) := by
  induction r with
  | empty => intro w; rfl
  | eps => intro w; rfl
  | ranges rs =>
    intro w
    cases w with
    | nil => cases h : inRanges c rs <;> simp [deriv, mem, h]
    | cons d t => cases h : inRanges c rs <;> simp [deriv, mem, h]
  | alt a b iha ihb => intro w; simp [deriv, mem, smartAlt_ok, iha, ihb]
  | inter a b iha ihb => intro w; simp [deriv, mem, smartAnd_ok, iha, ihb]
  | compl a iha => intro w; simp [deriv, mem, smartNot_ok, iha]
  | cat a b iha ihb =>
    intro w
    have := deriv_cat_w a b (deriv c a) (deriv c b) c w iha ihb
    rw [← this]
    simp only [deriv]
    split <;> simp [smartAlt_ok]
  | star a iha =>
    intro w
    rw [← deriv_star_w a (deriv c a) c w iha]
    rfl

/-- F* `deriv_word_correct`. -/
theorem derivWord_correct (r : Re) (w : List Nat) : mem (derivWord r w) [] = mem r w := by
  induction w generalizing r with
  | nil => rfl
  | cons c rest ih => simp [derivWord, ih, deriv_correct]

/-- F* `matches_correct`: the derivative matcher decides exactly `mem`. -/
theorem accepts_correct (r : Re) (w : List Nat) : Derivative.accepts r w = mem r w := by
  unfold Derivative.accepts
  rw [nullable_correct, derivWord_correct]

/-! ## §3 Exec -/

open Exec

/-- F* `mem_alt_list`: membership against a leaf list = OR over the leaves. -/
def memAltList (xs : List Re) (w : List Nat) : Bool :=
  xs.any (fun x => mem x w)

/-- F* `mem_and_list`. -/
def memAndList (xs : List Re) (w : List Nat) : Bool :=
  xs.all (fun x => mem x w)

/-- F* `insert_regex_ok`: sorted insertion preserves the OR (dedup is
language-safe by `reCmp_eq`). -/
theorem insertRegex_ok (x : Re) (xs : List Re) (w : List Nat) :
    memAltList (insertRegex x xs) w = (mem x w || memAltList xs w) := by
  induction xs with
  | nil => simp [insertRegex, memAltList]
  | cons y ys ih =>
    simp only [insertRegex]
    split
    · rename_i h; have := reCmp_eq x y h; subst this; simp [memAltList]
    · simp [memAltList]
    · simp only [memAltList, List.any_cons] at ih ⊢
      rw [ih]; exact Bool.or_left_comm _ _ _

/-- F* `alt_flatten_ok`. -/
theorem altFlatten_ok (r : Re) (acc : List Re) (w : List Nat) :
    memAltList (altFlatten r acc) w = (mem r w || memAltList acc w) := by
  induction r generalizing acc with
  | alt a b iha ihb => simp [altFlatten, iha, ihb, mem, Bool.or_assoc]
  | empty => simp [altFlatten, mem]
  | _ => simp [altFlatten, insertRegex_ok]

/-- F* `rebuild_alt_ok`. -/
theorem rebuildAlt_ok (xs : List Re) (w : List Nat) :
    mem (rebuildAlt xs) w = memAltList xs w := by
  induction xs with
  | nil => simp [rebuildAlt, memAltList, mem]
  | cons x rest ih =>
    cases rest with
    | nil => simp [rebuildAlt, memAltList]
    | cons y ys => simp [rebuildAlt, mem, memAltList] at ih ⊢; rw [ih]

/-- F* `has_universal_ok`. -/
theorem hasUniversal_ok (xs : List Re) (w : List Nat) (h : hasUniversal xs = true) :
    memAltList xs w = true := by
  induction xs with
  | nil => simp [hasUniversal] at h
  | cons y ys ih =>
    simp only [hasUniversal, Bool.or_eq_true, decide_eq_true_iff] at h
    rcases h with h | h
    · subst h; simp [memAltList, mem_universal]
    · have := ih h
      simp only [memAltList, List.any_cons] at this ⊢
      rw [this]; simp

/-- F* `ealt_ok`: the canonical union denotes the union. -/
theorem ealt_ok (a b : Re) (w : List Nat) : mem (ealt a b) w = (mem a w || mem b w) := by
  unfold ealt
  dsimp only
  split
  · rename_i h
    have h' := hasUniversal_ok _ w h
    rw [altFlatten_ok, altFlatten_ok] at h'
    rw [mem_universal]
    cases ha : mem a w <;> cases hb : mem b w <;> simp_all [memAltList]
  · rw [rebuildAlt_ok, altFlatten_ok, altFlatten_ok]; simp [memAltList]

/-- F* `insert_regex_and_ok`. -/
theorem insertRegex_and_ok (x : Re) (xs : List Re) (w : List Nat) :
    memAndList (insertRegex x xs) w = (mem x w && memAndList xs w) := by
  induction xs with
  | nil => simp [insertRegex, memAndList]
  | cons y ys ih =>
    simp only [insertRegex]
    split
    · rename_i h; have := reCmp_eq x y h; subst this; simp [memAndList]
    · simp [memAndList]
    · simp only [memAndList, List.all_cons] at ih ⊢
      rw [ih]; exact Bool.and_left_comm _ _ _

/-- F* `and_flatten_ok`. -/
theorem andFlatten_ok (r : Re) (acc : List Re) (w : List Nat) :
    memAndList (andFlatten r acc) w = (mem r w && memAndList acc w) := by
  induction r generalizing acc with
  | inter a b iha ihb => simp [andFlatten, iha, ihb, mem, Bool.and_assoc]
  | _ =>
    simp only [andFlatten]
    split
    · rename_i h; rw [h, mem_universal]; simp
    · rw [insertRegex_and_ok]

/-- F* `rebuild_and_ok`. -/
theorem rebuildAnd_ok (xs : List Re) (w : List Nat) :
    mem (rebuildAnd xs) w = memAndList xs w := by
  induction xs with
  | nil => simp [rebuildAnd, memAndList, mem_universal]
  | cons x rest ih =>
    cases rest with
    | nil => simp [rebuildAnd, memAndList]
    | cons y ys => simp [rebuildAnd, mem, memAndList] at ih ⊢; rw [ih]

/-- F* `has_empty_ok`. -/
theorem hasEmpty_ok (xs : List Re) (w : List Nat) (h : hasEmpty xs = true) :
    memAndList xs w = false := by
  induction xs with
  | nil => simp [hasEmpty] at h
  | cons y ys ih =>
    simp only [hasEmpty, Bool.or_eq_true, decide_eq_true_iff] at h
    rcases h with h | h
    · subst h; simp [memAndList]
    · have := ih h
      simp only [memAndList, List.all_cons] at this ⊢
      rw [this]; simp

/-- F* `eand_ok`: the canonical intersection denotes the intersection. -/
theorem eand_ok (a b : Re) (w : List Nat) : mem (eand a b) w = (mem a w && mem b w) := by
  unfold eand
  dsimp only
  split
  · rename_i h
    have h' := hasEmpty_ok _ w h
    rw [andFlatten_ok, andFlatten_ok] at h'
    rw [mem_empty]
    cases ha : mem a w <;> cases hb : mem b w <;> simp_all [memAndList]
  · rw [rebuildAnd_ok, andFlatten_ok, andFlatten_ok]; simp [memAndList]

/-- F* `nderiv_correct`: the ACI-normalised derivative is language-correct
for the FULL AST. Same induction as `deriv_correct`, with `ealt_ok` /
`eand_ok` / `smartCat_ok` in place of the one-node smart constructors. -/
theorem nderiv_correct (c : Nat) (r : Re) : ∀ w, mem (nderiv c r) w = mem r (c :: w) := by
  induction r with
  | empty => intro w; rfl
  | eps => intro w; rfl
  | ranges rs =>
    intro w
    cases w with
    | nil => cases h : inRanges c rs <;> simp [nderiv, mem, h]
    | cons d t => cases h : inRanges c rs <;> simp [nderiv, mem, h]
  | alt a b iha ihb => intro w; simp [nderiv, mem, ealt_ok, iha, ihb]
  | inter a b iha ihb => intro w; simp [nderiv, mem, eand_ok, iha, ihb]
  | compl a iha => intro w; simp [nderiv, mem, smartNot_ok, iha]
  | cat a b iha ihb =>
    intro w
    have := deriv_cat_w a b (nderiv c a) (nderiv c b) c w iha ihb
    rw [← this]
    simp only [nderiv]
    split <;> simp [ealt_ok, smartCat_ok]
  | star a iha =>
    intro w
    rw [← deriv_star_w a (nderiv c a) c w iha]
    simp only [nderiv]
    rw [smartCat_ok]

/-- F* `run_word_norm_correct`. -/
theorem runWordNorm_correct (r : Re) (w : List Nat) : mem (runWordNorm r w) [] = mem r w := by
  induction w generalizing r with
  | nil => rfl
  | cons c rest ih => simp [runWordNorm, ih, nderiv_correct]

/-- F* `matches_norm_correct`: the fast path decides exactly `mem`. -/
theorem acceptsNorm_correct (r : Re) (w : List Nat) : acceptsNorm r w = mem r w := by
  unfold acceptsNorm
  rw [nullable_correct, runWordNorm_correct]

/-- `Exec.runWord` is `Derivative.derivWord` (same fold of the same derivative). -/
theorem runWord_eq_derivWord (r : Re) (w : List Nat) : runWord r w = derivWord r w := by
  induction w generalizing r with
  | nil => rfl
  | cons c rest ih => simp [runWord, derivWord, ih]

/-- The `Exec.accepts` entry inherits F* `matches_correct`. -/
theorem Exec.accepts_correct (r : Re) (w : List Nat) : Exec.accepts r w = mem r w := by
  unfold Exec.accepts
  rw [runWord_eq_derivWord, nullable_correct, derivWord_correct]

/-- F* `matches_norm_eq_proven`: the normalised fast path agrees with the
machine-checked reference matcher on every input. -/
theorem acceptsNorm_eq_proven (r : Re) (w : List Nat) :
    acceptsNorm r w = Derivative.accepts r w := by
  rw [acceptsNorm_correct, accepts_correct]

/-- `search r w` is membership of `w` in `Σ* · L(r) · Σ*`. -/
theorem search_correct (r : Re) (w : List Nat) : search r w = mem (contains r) w :=
  acceptsNorm_correct _ _

/-! ## Axiom audit -/

#print axioms nullable_correct
#print axioms smartCat_ok
#print axioms smartStar_ok
#print axioms reCmp_eq
#print axioms deriv_correct
#print axioms accepts_correct
#print axioms ealt_ok
#print axioms eand_ok
#print axioms nderiv_correct
#print axioms acceptsNorm_correct
#print axioms acceptsNorm_eq_proven

end L4Factoidal.Regex
