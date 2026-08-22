/-
L4Factoidal.Geo.Order — `Scaled.le` is transitive, and the
bounding-box pre-filter is therefore sound.

The obligation `BBox.lean` named. The difficulty: `Scaled.cmp` aligns
ITS TWO arguments at THEIR common scale, so a three-way chain
`a ≤ b ≤ c` involves three different alignment scales. The fix is a
rescaling-invariance lemma — comparing at any scale at least as large
as both operands' gives the same verdict — after which transitivity
is ordinary integer transitivity at one shared scale.
-/
import L4Factoidal.Geo.Types

namespace L4Factoidal.Geo
namespace Scaled

theorem pow10_add (m n : Nat) : pow10 (m + n) = pow10 m * pow10 n := by
  induction m with
  | zero => simp [pow10]
  | succ k ih => simp [pow10, Nat.succ_add, ih, Nat.mul_assoc]

theorem pow10_cast_pos (k : Nat) : (0 : Int) < (pow10 k : Int) := by
  have h := pow10_pos k
  exact_mod_cast h

/-- The mantissa this decimal has when written at scale `s`
    (meaningful when `a.scale ≤ s`). -/
def at' (a : Scaled) (s : Nat) : Int := a.mantissa * (pow10 (s - a.scale) : Int)

/-- Rescaling upward multiplies the mantissa by a power of ten. -/
theorem at'_shift (a : Scaled) (s k : Nat) (h : a.scale ≤ s) :
    a.at' (s + k) = a.at' s * (pow10 k : Int) := by
  have hs : s + k - a.scale = (s - a.scale) + k := by omega
  rw [at', at', hs, pow10_add, Int.natCast_mul, ← Int.mul_assoc]

/-- Comparing at a larger common scale gives the same `≤` verdict. -/
theorem le_at'_shift (a b : Scaled) (s k : Nat)
    (ha : a.scale ≤ s) (hb : b.scale ≤ s) :
    (a.at' (s + k) ≤ b.at' (s + k)) ↔ (a.at' s ≤ b.at' s) := by
  rw [at'_shift a s k ha, at'_shift b s k hb]
  constructor
  · intro h
    exact Int.le_of_mul_le_mul_right h (pow10_cast_pos k)
  · intro h
    exact Int.mul_le_mul_of_nonneg_right h (Int.le_of_lt (pow10_cast_pos k))

/-- `Scaled.le` unfolds to integer `≤` at the operands' common scale. -/
theorem le_iff_at' (a b : Scaled) :
    le a b = true ↔ a.at' (Nat.max a.scale b.scale) ≤ b.at' (Nat.max a.scale b.scale) := by
  unfold le cmp align at'
  simp only [decide_eq_true_eq]
  -- The two aligned mantissas are opaque products; name them so the
  -- remaining reasoning is linear and `omega` applies.
  generalize a.mantissa * ((pow10 (Nat.max a.scale b.scale - a.scale) : Nat) : Int) = x
  generalize b.mantissa * ((pow10 (Nat.max a.scale b.scale - b.scale) : Nat) : Int) = y
  by_cases h1 : x < y
  · simp [h1]; omega
  · by_cases h2 : x = y
    · simp [h1, h2]
    · simp [h1, h2]; omega

/-- `≤` at ANY scale that dominates both operands agrees with `le`. -/
theorem le_iff_at'_of_ge (a b : Scaled) (s : Nat)
    (ha : a.scale ≤ s) (hb : b.scale ≤ s) :
    le a b = true ↔ a.at' s ≤ b.at' s := by
  have hm : Nat.max a.scale b.scale ≤ s := Nat.max_le.mpr ⟨ha, hb⟩
  have hsplit : s = Nat.max a.scale b.scale + (s - Nat.max a.scale b.scale) := by omega
  rw [le_iff_at' a b, hsplit,
      le_at'_shift a b (Nat.max a.scale b.scale) (s - Nat.max a.scale b.scale)
        (Nat.le_max_left _ _) (Nat.le_max_right _ _)]

/-- TRANSITIVITY — the lemma the bounding-box pre-filter waited on. -/
theorem le_trans {a b c : Scaled}
    (hab : le a b = true) (hbc : le b c = true) : le a c = true := by
  let s := Nat.max (Nat.max a.scale b.scale) c.scale
  have ha : a.scale ≤ s := Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)
  have hb : b.scale ≤ s := Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)
  have hc : c.scale ≤ s := Nat.le_max_right _ _
  have h1 : a.at' s ≤ b.at' s := (le_iff_at'_of_ge a b s ha hb).mp hab
  have h2 : b.at' s ≤ c.at' s := (le_iff_at'_of_ge b c s hb hc).mp hbc
  exact (le_iff_at'_of_ge a c s ha hc).mpr (Int.le_trans h1 h2)

end Scaled
end L4Factoidal.Geo
