/-
L4Factoidal.Geo.BBoxSound — a bounding box may EXCLUDE a geometry pair, and
the exclusion is proved.

Design record: `docs/designissues/2026-09-05-geometry-bounding-box-index.md`.

`BBox.lean` proves the first half: two boxes that do not overlap share no
point (`disjoint_bbox_no_shared_point`). That is useless on its own, because
the topology predicates are not stated over points — they are ray casts,
orientation determinants and segment tests over vertex lists. This module
supplies the missing half: when one of those algorithms answers `some true`,
the two geometries have a point that BOTH boxes contain.

Composed, the two halves say a non-overlapping box pair can never be the
answer to `geof:sfIntersects`, `sfWithin`, `sfContains`, `sfTouches` or
`sfEquals`, which is what makes a bounding-box index a sound candidate filter.

## The one difficult step

`polygonClass p poly = .interior` is decided by ray casting: the count of
ring edges the +x ray from `p` crosses is odd. Nothing in that statement
mentions the polygon's box, and the argument that an interior point is inside
the box is the Jordan-curve argument in miniature. It is done here in three
parts.

* An odd count is a non-zero count, so some edge crosses. A crossing edge
  STRADDLES the line `y = p.y`, which puts one endpoint above `p.y` and the
  other at or below it. Both `y` bounds follow from that alone.
* If `p.x` were greater than every vertex `x`, then every straddling edge
  takes the orientation sign the crossing test rejects, so the count would be
  ZERO. Zero is even.
* If `p.x` were less than every vertex `x`, then every straddling edge
  crosses, so the count IS the straddle count. On a closed ring the straddle
  count is even, because the predicate `y > p.y` returns to its starting
  value after one lap.

Both sign steps rest on one regrouping of the orientation determinant,

    orient a b p = (b.x - p.x)*(p.y - a.y) + (a.x - p.x)*(b.y - p.y)

whose two products have known signs once `p` is on one side of the edge and
the edge straddles. `Scaled.at'` carries `sub` and `mul` to integers at a
shared decimal scale, so the signs are ordinary integer arithmetic and no
float or division appears.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Geo.Topology

namespace L4Factoidal.Geo

/-! ## 1. `Scaled` is a total order, and its arithmetic reaches the integers -/

namespace Scaled

/-- Swapping the arguments negates the three-way comparison. Everything below
that relates `le`, `lt`, `gt` and `eq` comes from this one fact. -/
theorem cmp_swap (a b : Scaled) : cmp b a = - cmp a b := by
  unfold cmp align
  rw [Nat.max_comm b.scale a.scale]
  generalize a.mantissa * ((pow10 (Nat.max a.scale b.scale - a.scale) : Nat) : Int) = x
  generalize b.mantissa * ((pow10 (Nat.max a.scale b.scale - b.scale) : Nat) : Int) = y
  by_cases h1 : y < x
  · by_cases h2 : y = x <;> simp [h1, h2] <;> omega
  · by_cases h2 : y = x <;> simp [h1, h2] <;> omega

theorem le_refl (a : Scaled) : le a a = true := by
  unfold le cmp align
  simp only [decide_eq_true_eq]
  generalize a.mantissa * ((pow10 (Nat.max a.scale a.scale - a.scale) : Nat) : Int) = x
  simp

/-- `gt` is the Boolean complement of `le`. -/
theorem gt_eq_not_le (a b : Scaled) : gt a b = !(le a b) := by
  unfold gt le
  generalize cmp a b = c
  by_cases h : c ≤ 0
  · simp only [h, decide_true, Bool.not_true, decide_eq_false_iff_not]; omega
  · simp only [h, decide_false, Bool.not_false, decide_eq_true_eq]; omega

/-- `lt a b` is the complement of `le b a`. -/
theorem lt_eq_not_le (a b : Scaled) : lt a b = !(le b a) := by
  unfold lt le
  rw [cmp_swap a b]
  generalize cmp a b = c
  by_cases h : -c ≤ 0
  · simp only [h, decide_true, Bool.not_true, decide_eq_false_iff_not]; omega
  · simp only [h, decide_false, Bool.not_false, decide_eq_true_eq]; omega

/-- The order is total. -/
theorem le_total (a b : Scaled) (h : le a b = false) : le b a = true := by
  unfold le at h ⊢
  rw [cmp_swap a b]
  simp only [decide_eq_false_iff_not] at h
  simp only [decide_eq_true_eq]
  omega

theorem lt_of_lt_of_le {a b c : Scaled} (hab : lt a b = true) (hbc : le b c = true) :
    lt a c = true := by
  rw [lt_eq_not_le] at hab ⊢
  simp only [Bool.not_eq_true'] at hab ⊢
  refine Classical.byContradiction (fun hc => ?_)
  simp only [Bool.not_eq_false] at hc
  rw [le_trans hbc hc] at hab
  simp at hab

theorem lt_of_le_of_lt {a b c : Scaled} (hab : le a b = true) (hbc : lt b c = true) :
    lt a c = true := by
  rw [lt_eq_not_le] at hbc ⊢
  simp only [Bool.not_eq_true'] at hbc ⊢
  refine Classical.byContradiction (fun hc => ?_)
  simp only [Bool.not_eq_false] at hc
  rw [le_trans hc hab] at hbc
  simp at hbc

/-- `lt` and `le` cannot both hold in opposite directions. -/
theorem not_lt_of_le {a b : Scaled} (h : le a b = true) : lt b a = false := by
  rw [lt_eq_not_le, h]; rfl

theorem eq_le {a b : Scaled} (h : eq a b = true) : le a b = true ∧ le b a = true := by
  unfold eq at h
  simp only [beq_iff_eq] at h
  refine ⟨?_, ?_⟩
  · unfold le; simp only [decide_eq_true_eq]; omega
  · unfold le; rw [cmp_swap a b, h]; simp

/-- Equal decimals compare the same way against any third one. -/
theorem gt_congr_left {a b : Scaled} (h : eq a b = true) (c : Scaled) :
    gt a c = gt b c := by
  obtain ⟨hab, hba⟩ := eq_le h
  rw [gt_eq_not_le, gt_eq_not_le]
  by_cases hac : le a c = true
  · rw [hac, le_trans hba hac]
  · simp only [Bool.not_eq_true] at hac
    rw [hac]
    by_cases hbc : le b c = true
    · rw [le_trans hab hbc] at hac; exact absurd hac (by simp)
    · simp only [Bool.not_eq_true] at hbc; rw [hbc]

theorem min_le_left (a b : Scaled) : le (min a b) a = true := by
  unfold min
  by_cases h : le a b = true
  · rw [if_pos h]; exact le_refl a
  · simp only [Bool.not_eq_true] at h; rw [if_neg (by simp [h])]; exact le_total a b h

theorem min_le_right (a b : Scaled) : le (min a b) b = true := by
  unfold min
  by_cases h : le a b = true
  · rw [if_pos h]; exact h
  · simp only [Bool.not_eq_true] at h; rw [if_neg (by simp [h])]; exact le_refl b

/-- `ge a b` is `le b a`. -/
theorem ge_eq_le_swap (a b : Scaled) : ge a b = le b a := by
  unfold ge le
  rw [cmp_swap a b]
  generalize cmp a b = c
  by_cases h : 0 ≤ c
  · rw [decide_eq_true (by omega : c ≥ 0), decide_eq_true (by omega : -c ≤ 0)]
  · rw [decide_eq_false (by omega : ¬ (c ≥ 0)), decide_eq_false (by omega : ¬ (-c ≤ 0))]

theorem le_max_left (a b : Scaled) : le a (max a b) = true := by
  unfold max
  rw [ge_eq_le_swap]
  by_cases h : le b a = true
  · rw [if_pos h]; exact le_refl a
  · simp only [Bool.not_eq_true] at h; rw [if_neg (by simp [h])]; exact le_total b a h

theorem le_max_right (a b : Scaled) : le b (max a b) = true := by
  unfold max
  rw [ge_eq_le_swap]
  by_cases h : le b a = true
  · rw [if_pos h]; exact h
  · simp only [Bool.not_eq_true] at h; rw [if_neg (by simp [h])]; exact le_refl b

theorem le_min {c a b : Scaled} (ha : le c a = true) (hb : le c b = true) :
    le c (min a b) = true := by
  unfold min
  by_cases h : le a b = true
  · rw [if_pos h]; exact ha
  · simp only [Bool.not_eq_true] at h; rw [if_neg (by simp [h])]; exact hb

theorem max_le {a b c : Scaled} (ha : le a c = true) (hb : le b c = true) :
    le (max a b) c = true := by
  unfold max
  rw [ge_eq_le_swap]
  by_cases h : le b a = true
  · rw [if_pos h]; exact ha
  · simp only [Bool.not_eq_true] at h; rw [if_neg (by simp [h])]; exact hb

/-! ### `sub` and `mul` at a shared scale

`at'` is a ring homomorphism into `Int` once the scale is large enough. These
two lemmas are the whole bridge; the determinant signs below are integer
arithmetic afterwards. -/

theorem sub_scale (x y : Scaled) : (sub x y).scale = Nat.max x.scale y.scale := rfl
theorem mul_scale (x y : Scaled) : (mul x y).scale = x.scale + y.scale := rfl

theorem sub_mantissa (x y : Scaled) :
    (sub x y).mantissa =
      x.at' (Nat.max x.scale y.scale) - y.at' (Nat.max x.scale y.scale) := rfl

theorem zero_at' (s : Nat) : Scaled.zero.at' s = 0 := by
  unfold at' zero ofInt; simp

theorem sub_at' (x y : Scaled) (s : Nat) (hx : x.scale ≤ s) (hy : y.scale ≤ s) :
    (sub x y).at' s = x.at' s - y.at' s := by
  have hm : Nat.max x.scale y.scale ≤ s := Nat.max_le.mpr ⟨hx, hy⟩
  have hk : s = Nat.max x.scale y.scale + (s - Nat.max x.scale y.scale) := by omega
  have hxs : x.at' s = x.at' (Nat.max x.scale y.scale) * (pow10 (s - Nat.max x.scale y.scale) : Int) := by
    conv => lhs; rw [hk]
    exact at'_shift x _ _ (Nat.le_max_left _ _)
  have hys : y.at' s = y.at' (Nat.max x.scale y.scale) * (pow10 (s - Nat.max x.scale y.scale) : Int) := by
    conv => lhs; rw [hk]
    exact at'_shift y _ _ (Nat.le_max_right _ _)
  rw [hxs, hys, ← Int.sub_mul, at', sub_mantissa, sub_scale]

theorem mul_at' (x y : Scaled) (s1 s2 : Nat) (hx : x.scale ≤ s1) (hy : y.scale ≤ s2) :
    (mul x y).at' (s1 + s2) = x.at' s1 * y.at' s2 := by
  have hsplit : s1 + s2 - (x.scale + y.scale) = (s1 - x.scale) + (s2 - y.scale) := by omega
  unfold at' mul
  simp only [hsplit, pow10_add, Int.natCast_mul]
  grind

/-- A sign test against zero is a sign test on the integer value at any
sufficiently large scale. -/
theorem lt_zero_iff (o : Scaled) (s : Nat) (h : o.scale ≤ s) :
    lt o zero = true ↔ o.at' s < 0 := by
  rw [lt_eq_not_le]
  have hz : Scaled.zero.scale ≤ s := Nat.zero_le s
  have hiff := le_iff_at'_of_ge Scaled.zero o s hz h
  rw [zero_at'] at hiff
  constructor
  · intro hlt
    simp only [Bool.not_eq_true'] at hlt
    refine Classical.byContradiction (fun hc => ?_)
    have hnn : (0 : Int) ≤ o.at' s := by omega
    rw [hiff.mpr hnn] at hlt
    simp at hlt
  · intro hlt
    simp only [Bool.not_eq_true']
    refine Classical.byContradiction (fun hc => ?_)
    simp only [Bool.not_eq_false] at hc
    have := (le_iff_at'_of_ge Scaled.zero o s hz h).mp hc
    rw [zero_at'] at this
    omega

theorem eq_zero_iff (o : Scaled) (s : Nat) (h : o.scale ≤ s) :
    eq o zero = true ↔ o.at' s = 0 := by
  have hz : Scaled.zero.scale ≤ s := Nat.zero_le s
  constructor
  · intro he
    obtain ⟨h1, h2⟩ := eq_le he
    have a1 := (le_iff_at'_of_ge o Scaled.zero s h hz).mp h1
    have a2 := (le_iff_at'_of_ge Scaled.zero o s hz h).mp h2
    rw [zero_at'] at a1 a2
    omega
  · intro he
    have a1 : le o Scaled.zero = true :=
      (le_iff_at'_of_ge o Scaled.zero s h hz).mpr (by rw [zero_at', he]; omega)
    have a2 : le Scaled.zero o = true :=
      (le_iff_at'_of_ge Scaled.zero o s hz h).mpr (by rw [zero_at', he]; omega)
    unfold eq
    unfold le at a1 a2
    simp only [decide_eq_true_eq] at a1 a2
    have hs := cmp_swap o Scaled.zero
    simp only [beq_iff_eq]
    omega

end Scaled

/-! ## 2. A box that covers a point list

`BBox.ofPoints` folds a union across the list. `covers` is the property the
whole module consumes: every vertex of the list is inside the box. It is
stated as a hypothesis rather than as `BBox.ofPoints l = some b`, so the same
lemmas apply to a box built over a polygon's exterior ring together with its
holes. -/

/-- Every point of `l` is inside `b`. -/
def BBox.covers (b : BBox) (l : List Point) : Prop := ∀ q ∈ l, b.contains q = true

theorem BBox.contains_union_left {a c : BBox} {q : Point} (h : a.contains q = true) :
    (a.union c).contains q = true := by
  simp only [BBox.contains, BBox.union, Bool.and_eq_true] at h ⊢
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨⟨⟨Scaled.le_trans (Scaled.min_le_left a.xmin c.xmin) h1,
           Scaled.le_trans h2 (Scaled.le_max_left a.xmax c.xmax)⟩,
          Scaled.le_trans (Scaled.min_le_left a.ymin c.ymin) h3⟩,
         Scaled.le_trans h4 (Scaled.le_max_left a.ymax c.ymax)⟩

theorem BBox.contains_union_right {a c : BBox} {q : Point} (h : c.contains q = true) :
    (a.union c).contains q = true := by
  simp only [BBox.contains, BBox.union, Bool.and_eq_true] at h ⊢
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨⟨⟨Scaled.le_trans (Scaled.min_le_right a.xmin c.xmin) h1,
           Scaled.le_trans h2 (Scaled.le_max_right a.xmax c.xmax)⟩,
          Scaled.le_trans (Scaled.min_le_right a.ymin c.ymin) h3⟩,
         Scaled.le_trans h4 (Scaled.le_max_right a.ymax c.ymax)⟩

/-- The accumulator already contains `q`, so the union still does, whatever
the incoming box is. -/
theorem BBox.unionOpt_carry {acc : Option BBox} {x : BBox} {c : Option BBox} {q : Point}
    (hacc : acc = some x) (hx : x.contains q = true) :
    ∃ y, BBox.unionOpt acc c = some y ∧ y.contains q = true := by
  subst hacc
  cases c with
  | none => exact ⟨x, rfl, hx⟩
  | some z => exact ⟨x.union z, rfl, BBox.contains_union_left hx⟩

/-- The incoming box contains `q`, so the union does. -/
theorem BBox.unionOpt_absorb {acc : Option BBox} {z : BBox} {q : Point}
    (hz : z.contains q = true) :
    ∃ y, BBox.unionOpt acc (some z) = some y ∧ y.contains q = true := by
  cases acc with
  | none => exact ⟨z, rfl, hz⟩
  | some x => exact ⟨x.union z, rfl, BBox.contains_union_right hz⟩

/-- A fold that starts from a real box never returns `none`. -/
theorem BBox.foldl_points_ne_none :
    ∀ (l : List Point) (a : BBox),
      l.foldl (fun acc p => BBox.unionOpt acc (some (BBox.ofPoint p))) (some a) ≠ none := by
  intro l
  induction l with
  | nil => intro a; simp
  | cons w ws ih => intro a; simpa [List.foldl_cons, BBox.unionOpt] using ih (a.union (BBox.ofPoint w))

/-- A non-empty point list always has a box. -/
theorem BBox.ofPoints_ne_none {l : List Point} {q : Point} (hq : q ∈ l) :
    BBox.ofPoints l ≠ none := by
  cases l with
  | nil => simp at hq
  | cons w ws =>
      simp only [BBox.ofPoints, List.foldl_cons, BBox.unionOpt]
      exact BBox.foldl_points_ne_none ws (BBox.ofPoint w)

/-- The fold invariant: whatever the accumulator already contains, and every
point still to come, ends up inside the final box. -/
theorem BBox.foldl_covers (q : Point) :
    ∀ (l : List Point) (acc : Option BBox) (b : BBox),
      l.foldl (fun acc p => BBox.unionOpt acc (some (BBox.ofPoint p))) acc = some b →
      (q ∈ l ∨ (∃ x, acc = some x ∧ x.contains q = true)) →
      b.contains q = true := by
  intro l
  induction l with
  | nil =>
      intro acc b hfold h
      simp only [List.foldl_nil] at hfold
      rcases h with hq | ⟨x, hx, hcx⟩
      · simp at hq
      · rw [hfold] at hx; simp only [Option.some.injEq] at hx; subst hx; exact hcx
  | cons p rest ih =>
      intro acc b hfold h
      simp only [List.foldl_cons] at hfold
      refine ih _ b hfold ?_
      rcases h with hq | ⟨x, hx, hcx⟩
      · simp only [List.mem_cons] at hq
        rcases hq with rfl | hq
        · exact Or.inr (BBox.unionOpt_absorb (contains_ofPoint q))
        · exact Or.inl hq
      · exact Or.inr (BBox.unionOpt_carry hx hcx)

/-- The box of a point list covers the list. -/
theorem BBox.ofPoints_covers {l : List Point} {b : BBox} (h : BBox.ofPoints l = some b) :
    b.covers l := by
  intro q hq
  exact BBox.foldl_covers q l none b h (Or.inl hq)

theorem BBox.foldl_rings_covers (q : Point) :
    ∀ (rs : List Ring) (acc : Option BBox) (b : BBox),
      rs.foldl (fun acc r => BBox.unionOpt acc (BBox.ofPoints r)) acc = some b →
      ((∃ r ∈ rs, q ∈ r) ∨ (∃ x, acc = some x ∧ x.contains q = true)) →
      b.contains q = true := by
  intro rs
  induction rs with
  | nil =>
      intro acc b hfold h
      simp only [List.foldl_nil] at hfold
      rcases h with ⟨r, hr, _⟩ | ⟨x, hx, hcx⟩
      · simp at hr
      · rw [hfold] at hx; simp only [Option.some.injEq] at hx; subst hx; exact hcx
  | cons r rest ih =>
      intro acc b hfold h
      simp only [List.foldl_cons] at hfold
      refine ih _ b hfold ?_
      rcases h with ⟨r', hr', hq⟩ | ⟨x, hx, hcx⟩
      · simp only [List.mem_cons] at hr'
        rcases hr' with rfl | hr'
        · refine Or.inr ?_
          cases hb : BBox.ofPoints r' with
          | none => exact absurd hb (BBox.ofPoints_ne_none hq)
          | some rb =>
              exact BBox.unionOpt_absorb (BBox.ofPoints_covers hb q hq)
        · exact Or.inl ⟨r', hr', hq⟩
      · exact Or.inr (BBox.unionOpt_carry hx hcx)

/-- The box of a list of rings covers every point of every ring. -/
theorem BBox.ofRings_covers {rs : List Ring} {b : BBox} (h : BBox.ofRings rs = some b) :
    ∀ r ∈ rs, ∀ q ∈ r, b.contains q = true := by
  intro r hr q hq
  exact BBox.foldl_rings_covers q rs none b h (Or.inl ⟨r, hr, hq⟩)

/-- A point both boxes contain makes them overlap. This is the converse
direction of `disjoint_bbox_no_shared_point` and is what the index consumes:
every proof below produces such a point. -/
theorem BBox.overlaps_of_common_point {a b : BBox} {q : Point}
    (ha : a.contains q = true) (hb : b.contains q = true) : a.overlaps b = true := by
  simp only [BBox.contains, Bool.and_eq_true] at ha hb
  obtain ⟨⟨⟨ha1, ha2⟩, ha3⟩, ha4⟩ := ha
  obtain ⟨⟨⟨hb1, hb2⟩, hb3⟩, hb4⟩ := hb
  simp only [BBox.overlaps, Bool.and_eq_true]
  exact ⟨⟨⟨Scaled.le_trans ha1 hb2, Scaled.le_trans hb1 ha2⟩,
          Scaled.le_trans ha3 hb4⟩, Scaled.le_trans hb3 ha4⟩

/-! ## 3. A point on a path is inside any box covering the path -/

theorem inSegBBox_contains {b : BBox} {p a c : Point}
    (hca : b.contains a = true) (hcc : b.contains c = true)
    (h : inSegBBox p a c = true) : b.contains p = true := by
  simp only [inSegBBox, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  simp only [BBox.contains, Bool.and_eq_true] at hca hcc ⊢
  obtain ⟨⟨⟨a1, a2⟩, a3⟩, a4⟩ := hca
  obtain ⟨⟨⟨c1, c2⟩, c3⟩, c4⟩ := hcc
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · exact Scaled.le_trans (Scaled.le_min a1 c1) h1
  · exact Scaled.le_trans h2 (Scaled.max_le a2 c2)
  · exact Scaled.le_trans (Scaled.le_min a3 c3) h3
  · exact Scaled.le_trans h4 (Scaled.max_le a4 c4)

/-- A point the exact on-segment test accepts is inside any box covering the
path. `pointOnSegment` carries `inSegBBox` as a conjunct, so this needs no
geometry at all. -/
theorem pointOnPath_contains {b : BBox} {p : Point} :
    ∀ (l : List Point), b.covers l → pointOnPath p l = true → b.contains p = true := by
  intro l
  induction l with
  | nil => intro _ h; simp [pointOnPath] at h
  | cons a t ih =>
      intro hcov h
      cases t with
      | nil => simp [pointOnPath] at h
      | cons c rest =>
          simp only [pointOnPath, Bool.or_eq_true] at h
          rcases h with hseg | hrest
          · simp only [pointOnSegment, Bool.and_eq_true] at hseg
            exact inSegBBox_contains (hcov a (by simp)) (hcov c (by simp)) hseg.2
          · exact ih (fun q hq => hcov q (List.mem_cons_of_mem _ hq)) hrest

theorem pointOnAnyRing_contains {b : BBox} {p : Point} :
    ∀ (rs : List Ring), (∀ r ∈ rs, b.covers r) → pointOnAnyRing p rs = true →
      b.contains p = true := by
  intro rs
  induction rs with
  | nil => intro _ h; simp [pointOnAnyRing] at h
  | cons r rest ih =>
      intro hcov h
      simp only [pointOnAnyRing, Bool.or_eq_true] at h
      rcases h with hr | hrest
      · exact pointOnPath_contains r (hcov r (by simp)) hr
      · exact ih (fun r' hr' => hcov r' (by simp [hr'])) hrest

/-! ## 4. The ray cast

`rayCrossCount` inlines its two tests with `let`, so they are restated here
as named functions that are DEFINITIONALLY the same thing; `rayCrossCount_two`
is `rfl`. Nothing is re-decided. -/

/-- The edge `[a,c]` straddles the horizontal line `y = p.y`. -/
def straddlesEdge (p a c : Point) : Bool := Scaled.gt a.y p.y != Scaled.gt c.y p.y

/-- The +x ray from `p` crosses the edge `[a,c]`. -/
def crossesEdge (p a c : Point) : Bool :=
  if !straddlesEdge p a c then false
  else
    let o := orientSign a c p
    (Scaled.lt a.y c.y && o > 0) || (Scaled.gt a.y c.y && o < 0)

theorem rayCrossCount_two (p a c : Point) (rest : List Point) :
    rayCrossCount p (a :: c :: rest)
      = (if crossesEdge p a c then 1 else 0) + rayCrossCount p (c :: rest) := rfl

theorem crossesEdge_straddles {p a c : Point} (h : crossesEdge p a c = true) :
    straddlesEdge p a c = true := by
  unfold crossesEdge at h
  by_cases hs : straddlesEdge p a c = true
  · exact hs
  · simp only [Bool.not_eq_true] at hs; simp [hs] at h

/-- A straddling edge puts `p.y` between its two endpoint ordinates. -/
theorem straddlesEdge_y {p a c : Point} (h : straddlesEdge p a c = true) :
    (Scaled.le a.y p.y = true ∧ Scaled.le p.y c.y = true) ∨
    (Scaled.le c.y p.y = true ∧ Scaled.le p.y a.y = true) := by
  simp only [straddlesEdge, bne_iff_ne, ne_eq] at h
  rw [Scaled.gt_eq_not_le, Scaled.gt_eq_not_le] at h
  by_cases ha : Scaled.le a.y p.y = true
  · rw [ha] at h
    simp only [Bool.not_true] at h
    have hc : Scaled.le c.y p.y = false := by
      refine Classical.byContradiction (fun hcc => ?_)
      simp only [Bool.not_eq_false] at hcc
      rw [hcc] at h; simp at h
    exact Or.inl ⟨ha, Scaled.le_total _ _ hc⟩
  · simp only [Bool.not_eq_true] at ha
    rw [ha] at h
    simp only [Bool.not_false] at h
    have hc : Scaled.le c.y p.y = true := by
      refine Classical.byContradiction (fun hcc => ?_)
      simp only [Bool.not_eq_true] at hcc
      rw [hcc] at h; simp at h
    exact Or.inr ⟨hc, Scaled.le_total _ _ ha⟩

/-- A non-zero crossing count exhibits a straddling edge whose endpoints are
both vertices of the path. -/
theorem exists_straddle (p : Point) :
    ∀ (l : List Point), rayCrossCount p l ≠ 0 →
      ∃ a c, a ∈ l ∧ c ∈ l ∧ straddlesEdge p a c = true := by
  intro l
  induction l with
  | nil => intro h; simp [rayCrossCount] at h
  | cons a t ih =>
      intro h
      cases t with
      | nil => simp [rayCrossCount] at h
      | cons c rest =>
          rw [rayCrossCount_two] at h
          by_cases hx : crossesEdge p a c = true
          · exact ⟨a, c, by simp, by simp, crossesEdge_straddles hx⟩
          · simp only [Bool.not_eq_true] at hx
            rw [hx] at h
            simp only [Bool.false_eq_true, if_false, Nat.zero_add] at h
            obtain ⟨a', c', ha', hc', hs⟩ := ih h
            exact ⟨a', c', by simp [ha'], by simp [hc'], hs⟩

/-! ### The orientation determinant, regrouped

`orient a c p = (c.x - p.x)*(p.y - a.y) + (a.x - p.x)*(c.y - p.y)`. The
regrouping is what makes the two signs readable: with `p` strictly on one side
of the edge, both `(c.x - p.x)` and `(a.x - p.x)` have the same known sign,
and straddling fixes the signs of `(p.y - a.y)` and `(c.y - p.y)`. -/

/-- The product of two non-positive integers is non-negative. Lean core has
the three mixed-sign forms but not this one. -/
theorem mul_nonneg_of_nonpos_nonpos {x y : Int} (hx : x ≤ 0) (hy : y ≤ 0) :
    0 ≤ x * y := by
  have h := Int.mul_nonneg (by omega : (0:Int) ≤ -x) (by omega : (0:Int) ≤ -y)
  grind

/-- A scale large enough for every coordinate of three points. -/
def coordScale (a c p : Point) : Nat :=
  Nat.max (Nat.max (Nat.max a.x.scale a.y.scale) (Nat.max c.x.scale c.y.scale))
          (Nat.max p.x.scale p.y.scale)

theorem coordScale_bounds (a c p : Point) :
    a.x.scale ≤ coordScale a c p ∧ a.y.scale ≤ coordScale a c p ∧
    c.x.scale ≤ coordScale a c p ∧ c.y.scale ≤ coordScale a c p ∧
    p.x.scale ≤ coordScale a c p ∧ p.y.scale ≤ coordScale a c p := by
  unfold coordScale
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _))
      (Nat.le_max_left _ _)
  · exact Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _))
      (Nat.le_max_left _ _)
  · exact Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))
      (Nat.le_max_left _ _)
  · exact Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))
      (Nat.le_max_left _ _)
  · exact Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  · exact Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)

theorem orient_scale_le (a c p : Point) (s : Nat)
    (h1 : a.x.scale ≤ s) (h2 : a.y.scale ≤ s) (h3 : c.x.scale ≤ s)
    (h4 : c.y.scale ≤ s) (h5 : p.x.scale ≤ s) (h6 : p.y.scale ≤ s) :
    (orient a c p).scale ≤ s + s := by
  unfold orient
  rw [Scaled.sub_scale, Scaled.mul_scale, Scaled.mul_scale,
      Scaled.sub_scale, Scaled.sub_scale, Scaled.sub_scale, Scaled.sub_scale]
  refine Nat.max_le.mpr ⟨?_, ?_⟩
  · exact Nat.add_le_add (Nat.max_le.mpr ⟨h3, h1⟩) (Nat.max_le.mpr ⟨h6, h2⟩)
  · exact Nat.add_le_add (Nat.max_le.mpr ⟨h4, h2⟩) (Nat.max_le.mpr ⟨h5, h1⟩)

/-- The regrouped determinant at a shared scale. `grind` discharges the ring
identity; everything before it is the `at'` bridge. -/
theorem orient_at' (a c p : Point) (s : Nat)
    (h1 : a.x.scale ≤ s) (h2 : a.y.scale ≤ s) (h3 : c.x.scale ≤ s)
    (h4 : c.y.scale ≤ s) (h5 : p.x.scale ≤ s) (h6 : p.y.scale ≤ s) :
    (orient a c p).at' (s + s)
      = (c.x.at' s - p.x.at' s) * (p.y.at' s - a.y.at' s)
        + (a.x.at' s - p.x.at' s) * (c.y.at' s - p.y.at' s) := by
  have e1 : (Scaled.sub c.x a.x).scale ≤ s := Nat.max_le.mpr ⟨h3, h1⟩
  have e2 : (Scaled.sub p.y a.y).scale ≤ s := Nat.max_le.mpr ⟨h6, h2⟩
  have e3 : (Scaled.sub c.y a.y).scale ≤ s := Nat.max_le.mpr ⟨h4, h2⟩
  have e4 : (Scaled.sub p.x a.x).scale ≤ s := Nat.max_le.mpr ⟨h5, h1⟩
  have m1 : (Scaled.mul (Scaled.sub c.x a.x) (Scaled.sub p.y a.y)).scale ≤ s + s :=
    Nat.add_le_add e1 e2
  have m2 : (Scaled.mul (Scaled.sub c.y a.y) (Scaled.sub p.x a.x)).scale ≤ s + s :=
    Nat.add_le_add e3 e4
  unfold orient
  rw [Scaled.sub_at' _ _ (s + s) m1 m2,
      Scaled.mul_at' _ _ s s e1 e2, Scaled.mul_at' _ _ s s e3 e4,
      Scaled.sub_at' c.x a.x s h3 h1, Scaled.sub_at' p.y a.y s h6 h2,
      Scaled.sub_at' c.y a.y s h4 h2, Scaled.sub_at' p.x a.x s h5 h1]
  grind

theorem orientSign_pos_iff (a c p : Point) (s : Nat)
    (h1 : a.x.scale ≤ s) (h2 : a.y.scale ≤ s) (h3 : c.x.scale ≤ s)
    (h4 : c.y.scale ≤ s) (h5 : p.x.scale ≤ s) (h6 : p.y.scale ≤ s) :
    (0 < orientSign a c p) ↔ 0 < (orient a c p).at' (s + s) := by
  have hsc := orient_scale_le a c p s h1 h2 h3 h4 h5 h6
  unfold orientSign
  by_cases hlt : Scaled.lt (orient a c p) Scaled.zero = true
  · have := (Scaled.lt_zero_iff _ _ hsc).mp hlt
    simp only [hlt, if_true]
    omega
  · simp only [Bool.not_eq_true] at hlt
    have hnl : ¬ ((orient a c p).at' (s + s) < 0) := by
      intro hc
      rw [(Scaled.lt_zero_iff _ _ hsc).mpr hc] at hlt
      simp at hlt
    simp only [hlt, Bool.false_eq_true, if_false]
    by_cases heq : Scaled.eq (orient a c p) Scaled.zero = true
    · have := (Scaled.eq_zero_iff _ _ hsc).mp heq
      simp only [heq, if_true]
      omega
    · simp only [Bool.not_eq_true] at heq
      have hne : (orient a c p).at' (s + s) ≠ 0 := by
        intro hc
        rw [(Scaled.eq_zero_iff _ _ hsc).mpr hc] at heq
        simp at heq
      simp only [heq, Bool.false_eq_true, if_false]
      omega

theorem orientSign_neg_iff (a c p : Point) (s : Nat)
    (h1 : a.x.scale ≤ s) (h2 : a.y.scale ≤ s) (h3 : c.x.scale ≤ s)
    (h4 : c.y.scale ≤ s) (h5 : p.x.scale ≤ s) (h6 : p.y.scale ≤ s) :
    (orientSign a c p < 0) ↔ (orient a c p).at' (s + s) < 0 := by
  have hsc := orient_scale_le a c p s h1 h2 h3 h4 h5 h6
  unfold orientSign
  by_cases hlt : Scaled.lt (orient a c p) Scaled.zero = true
  · have := (Scaled.lt_zero_iff _ _ hsc).mp hlt
    simp only [hlt, if_true]
    omega
  · simp only [Bool.not_eq_true] at hlt
    have hnl : ¬ ((orient a c p).at' (s + s) < 0) := by
      intro hc
      rw [(Scaled.lt_zero_iff _ _ hsc).mpr hc] at hlt
      simp at hlt
    simp only [hlt, Bool.false_eq_true, if_false]
    by_cases heq : Scaled.eq (orient a c p) Scaled.zero = true
    · simp only [heq, if_true]; omega
    · simp only [Bool.not_eq_true] at heq
      simp only [heq, Bool.false_eq_true, if_false]
      omega

/-- `Scaled.lt` at a shared scale. -/
theorem Scaled.lt_at' (x y : Scaled) (s : Nat) (hx : x.scale ≤ s) (hy : y.scale ≤ s) :
    Scaled.lt x y = true ↔ x.at' s < y.at' s := by
  rw [Scaled.lt_eq_not_le]
  constructor
  · intro h
    simp only [Bool.not_eq_true'] at h
    refine Classical.byContradiction (fun hc => ?_)
    have : Scaled.le y x = true := (Scaled.le_iff_at'_of_ge y x s hy hx).mpr (by omega)
    rw [this] at h; simp at h
  · intro h
    simp only [Bool.not_eq_true']
    refine Classical.byContradiction (fun hc => ?_)
    simp only [Bool.not_eq_false] at hc
    have := (Scaled.le_iff_at'_of_ge y x s hy hx).mp hc
    omega

/-- With `p` strictly LEFT of both endpoints, a straddling edge always
crosses. This is what makes the crossing count equal the straddle count for a
point left of the whole ring. -/
theorem crossesEdge_of_left {p a c : Point}
    (hs : straddlesEdge p a c = true)
    (ha : Scaled.lt p.x a.x = true) (hc : Scaled.lt p.x c.x = true) :
    crossesEdge p a c = true := by
  have key : ∀ s : Nat, a.x.scale ≤ s → a.y.scale ≤ s → c.x.scale ≤ s →
      c.y.scale ≤ s → p.x.scale ≤ s → p.y.scale ≤ s → crossesEdge p a c = true := by
    intro s b1 b2 b3 b4 b5 b6
    have hax : p.x.at' s < a.x.at' s := (Scaled.lt_at' _ _ s b5 b1).mp ha
    have hcx : p.x.at' s < c.x.at' s := (Scaled.lt_at' _ _ s b5 b3).mp hc
    have hval := orient_at' a c p s b1 b2 b3 b4 b5 b6
    unfold crossesEdge
    simp only [hs, Bool.not_true, Bool.false_eq_true, if_false]
    rcases straddlesEdge_y hs with ⟨hay, hyc⟩ | ⟨hcy, hya⟩
    · have hA : 0 ≤ p.y.at' s - a.y.at' s := by
        have := (Scaled.le_iff_at'_of_ge a.y p.y s b2 b6).mp hay; omega
      have hS : 0 < c.y.at' s - p.y.at' s := by
        have hgt : Scaled.gt c.y p.y = true := by
          simp only [straddlesEdge, bne_iff_ne, ne_eq] at hs
          simp only [Scaled.gt_eq_not_le] at hs ⊢
          rw [hay] at hs
          simp only [Bool.not_true] at hs
          refine Classical.byContradiction (fun hcc => ?_)
          simp only [Bool.not_eq_true, Bool.not_eq_false'] at hcc
          rw [hcc] at hs; simp at hs
        rw [Scaled.gt_eq_not_le] at hgt
        simp only [Bool.not_eq_true'] at hgt
        have hnn : ¬ (c.y.at' s ≤ p.y.at' s) := by
          intro hcc
          rw [(Scaled.le_iff_at'_of_ge c.y p.y s b4 b6).mpr hcc] at hgt
          simp at hgt
        omega
      have hpos : 0 < (orient a c p).at' (s + s) := by
        rw [hval]
        have t1 : 0 ≤ (c.x.at' s - p.x.at' s) * (p.y.at' s - a.y.at' s) :=
          Int.mul_nonneg (by omega) hA
        have t2 : 0 < (a.x.at' s - p.x.at' s) * (c.y.at' s - p.y.at' s) :=
          Int.mul_pos (by omega) hS
        omega
      have hlt : Scaled.lt a.y c.y = true := by
        rw [Scaled.lt_at' _ _ s b2 b4]; omega
      have hsign := (orientSign_pos_iff a c p s b1 b2 b3 b4 b5 b6).mpr hpos
      simp [hlt, hsign]
    · have hS : c.y.at' s - p.y.at' s ≤ 0 := by
        have := (Scaled.le_iff_at'_of_ge c.y p.y s b4 b6).mp hcy; omega
      have hA : p.y.at' s - a.y.at' s < 0 := by
        have hgt : Scaled.gt a.y p.y = true := by
          simp only [straddlesEdge, bne_iff_ne, ne_eq] at hs
          simp only [Scaled.gt_eq_not_le] at hs ⊢
          rw [hcy] at hs
          simp only [Bool.not_true] at hs
          refine Classical.byContradiction (fun hcc => ?_)
          simp only [Bool.not_eq_true, Bool.not_eq_false'] at hcc
          rw [hcc] at hs; simp at hs
        rw [Scaled.gt_eq_not_le] at hgt
        simp only [Bool.not_eq_true'] at hgt
        have hnn : ¬ (a.y.at' s ≤ p.y.at' s) := by
          intro hcc
          rw [(Scaled.le_iff_at'_of_ge a.y p.y s b2 b6).mpr hcc] at hgt
          simp at hgt
        omega
      have hneg : (orient a c p).at' (s + s) < 0 := by
        rw [hval]
        have t1 : (c.x.at' s - p.x.at' s) * (p.y.at' s - a.y.at' s) < 0 :=
          Int.mul_neg_of_pos_of_neg (by omega) hA
        have t2 : (a.x.at' s - p.x.at' s) * (c.y.at' s - p.y.at' s) ≤ 0 :=
          Int.mul_nonpos_of_nonneg_of_nonpos (by omega) hS
        omega
      have hgt : Scaled.gt a.y c.y = true := by
        rw [Scaled.gt_eq_not_le]
        simp only [Bool.not_eq_true']
        refine Classical.byContradiction (fun hcc => ?_)
        simp only [Bool.not_eq_false] at hcc
        have := (Scaled.le_iff_at'_of_ge a.y c.y s b2 b4).mp hcc
        omega
      have hsign := (orientSign_neg_iff a c p s b1 b2 b3 b4 b5 b6).mpr hneg
      simp [hgt, hsign]
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := coordScale_bounds a c p
  exact key (coordScale a c p) b1 b2 b3 b4 b5 b6

/-- With `p` strictly RIGHT of both endpoints, a straddling edge never
crosses — the ray goes the other way. -/
theorem not_crossesEdge_of_right {p a c : Point}
    (hs : straddlesEdge p a c = true)
    (ha : Scaled.lt a.x p.x = true) (hc : Scaled.lt c.x p.x = true) :
    crossesEdge p a c = false := by
  have key : ∀ s : Nat, a.x.scale ≤ s → a.y.scale ≤ s → c.x.scale ≤ s →
      c.y.scale ≤ s → p.x.scale ≤ s → p.y.scale ≤ s → crossesEdge p a c = false := by
    intro s b1 b2 b3 b4 b5 b6
    have hax : a.x.at' s < p.x.at' s := (Scaled.lt_at' _ _ s b1 b5).mp ha
    have hcx : c.x.at' s < p.x.at' s := (Scaled.lt_at' _ _ s b3 b5).mp hc
    have hval := orient_at' a c p s b1 b2 b3 b4 b5 b6
    unfold crossesEdge
    simp only [hs, Bool.not_true, Bool.false_eq_true, if_false]
    rcases straddlesEdge_y hs with ⟨hay, hyc⟩ | ⟨hcy, hya⟩
    · have hA : 0 ≤ p.y.at' s - a.y.at' s := by
        have := (Scaled.le_iff_at'_of_ge a.y p.y s b2 b6).mp hay; omega
      have hS : 0 ≤ c.y.at' s - p.y.at' s := by
        have := (Scaled.le_iff_at'_of_ge p.y c.y s b6 b4).mp hyc; omega
      have hnp0 : (orient a c p).at' (s + s) ≤ 0 := by
        rw [hval]
        have t1 : (c.x.at' s - p.x.at' s) * (p.y.at' s - a.y.at' s) ≤ 0 :=
          Int.mul_nonpos_of_nonpos_of_nonneg (by omega) hA
        have t2 : (a.x.at' s - p.x.at' s) * (c.y.at' s - p.y.at' s) ≤ 0 :=
          Int.mul_nonpos_of_nonpos_of_nonneg (by omega) hS
        omega
      have hgt : Scaled.gt a.y c.y = false := by
        rw [Scaled.gt_eq_not_le, Scaled.le_trans hay hyc]; rfl
      have hnp : ¬ (0 < orientSign a c p) := by
        intro hcc
        have := (orientSign_pos_iff a c p s b1 b2 b3 b4 b5 b6).mp hcc
        omega
      simp [hgt, hnp]
    · have hA : p.y.at' s - a.y.at' s ≤ 0 := by
        have := (Scaled.le_iff_at'_of_ge p.y a.y s b6 b2).mp hya; omega
      have hS : c.y.at' s - p.y.at' s ≤ 0 := by
        have := (Scaled.le_iff_at'_of_ge c.y p.y s b4 b6).mp hcy; omega
      have hnn0 : 0 ≤ (orient a c p).at' (s + s) := by
        rw [hval]
        have t1 : 0 ≤ (c.x.at' s - p.x.at' s) * (p.y.at' s - a.y.at' s) :=
          mul_nonneg_of_nonpos_nonpos (by omega) hA
        have t2 : 0 ≤ (a.x.at' s - p.x.at' s) * (c.y.at' s - p.y.at' s) :=
          mul_nonneg_of_nonpos_nonpos (by omega) hS
        omega
      have hlt : Scaled.lt a.y c.y = false := by
        rw [Scaled.lt_eq_not_le, Scaled.le_trans hcy hya]; rfl
      have hnn : ¬ (orientSign a c p < 0) := by
        intro hcc
        have := (orientSign_neg_iff a c p s b1 b2 b3 b4 b5 b6).mp hcc
        omega
      simp [hlt, hnn]
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := coordScale_bounds a c p
  exact key (coordScale a c p) b1 b2 b3 b4 b5 b6

/-! ### The straddle count, and its parity on a closed ring -/

/-- How many edges of the path straddle the line `y = p.y`. -/
def straddleCount (p : Point) : List Point → Nat
  | []          => 0
  | [_]         => 0
  | a :: c :: rest => (if straddlesEdge p a c then 1 else 0) + straddleCount p (c :: rest)

/-- The eight-case Boolean fact behind the parity: one more edge flips the
running answer exactly when that edge straddles. -/
theorem straddleParityStep (ba bc bz : Bool) :
    ((if (ba != bc) = true then 1 else 0) % 2
      + if (bc == bz) = true then 0 else 1) % 2
      = (if (ba == bz) = true then 0 else 1) := by
  cases ba <;> cases bc <;> cases bz <;> rfl

/-- A lap of a path flips the `y > p.y` predicate once per straddling edge, so
the count's parity is decided by the two ENDS alone. -/
theorem straddleCount_parity (p : Point) :
    ∀ (t : List Point) (a z : Point), (a :: t).getLast? = some z →
      straddleCount p (a :: t) % 2 =
        (if Scaled.gt a.y p.y == Scaled.gt z.y p.y then 0 else 1) := by
  intro t
  induction t with
  | nil =>
      intro a z hz
      simp only [List.getLast?_singleton, Option.some.injEq] at hz
      subst hz
      simp [straddleCount]
  | cons c rest ih =>
      intro a z hz
      have hz' : (c :: rest).getLast? = some z := by
        simpa [List.getLast?_cons_cons] using hz
      have hrec := ih c z hz'
      simp only [straddleCount, straddlesEdge]
      rw [Nat.add_mod, hrec]
      exact straddleParityStep (Scaled.gt a.y p.y) (Scaled.gt c.y p.y) (Scaled.gt z.y p.y)

/-- On a closed ring the straddle count is EVEN. This is the fact that rules
out an odd crossing count for a point left of the whole ring. -/
theorem isClosedLine_head_last {l : List Point} (h : isClosedLine l = true) :
    ∃ a t z, l = a :: t ∧ (a :: t).getLast? = some z ∧ Point.eq a z = true := by
  cases hl : l with
  | nil => rw [hl] at h; simp [isClosedLine] at h
  | cons a t =>
      rw [hl] at h
      cases hgl : (a :: t).getLast? with
      | none => simp at hgl
      | some z =>
          refine ⟨a, t, z, rfl, hgl, ?_⟩
          unfold isClosedLine at h
          rw [hgl] at h
          simp only [Bool.and_eq_true, decide_eq_true_eq] at h
          exact h.1

theorem straddleCount_closed (p : Point) (l : List Point) (h : isClosedLine l = true) :
    straddleCount p l % 2 = 0 := by
  obtain ⟨a, t, z, hl, hlast, heq⟩ := isClosedLine_head_last h
  simp only [Point.eq, Bool.and_eq_true] at heq
  have hy : Scaled.gt a.y p.y = Scaled.gt z.y p.y := Scaled.gt_congr_left heq.2 p.y
  rw [hl, straddleCount_parity p t a z hlast, hy]
  simp

/-- Every vertex right of `p`: the count is the straddle count. -/
theorem rayCrossCount_eq_straddleCount_of_left (p : Point) :
    ∀ (l : List Point), (∀ q ∈ l, Scaled.lt p.x q.x = true) →
      rayCrossCount p l = straddleCount p l := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a t ih =>
      intro hall
      cases t with
      | nil => rfl
      | cons c rest =>
          rw [rayCrossCount_two]
          simp only [straddleCount]
          rw [ih (fun q hq => hall q (List.mem_cons_of_mem _ hq))]
          by_cases hs : straddlesEdge p a c = true
          · rw [crossesEdge_of_left hs (hall a (by simp)) (hall c (by simp)), hs]
          · simp only [Bool.not_eq_true] at hs
            have : crossesEdge p a c = false := by
              unfold crossesEdge; simp [hs]
            rw [this, hs]

/-- Every vertex left of `p`: the ray crosses nothing. -/
theorem rayCrossCount_zero_of_right (p : Point) :
    ∀ (l : List Point), (∀ q ∈ l, Scaled.lt q.x p.x = true) → rayCrossCount p l = 0 := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a t ih =>
      intro hall
      cases t with
      | nil => rfl
      | cons c rest =>
          rw [rayCrossCount_two]
          rw [ih (fun q hq => hall q (List.mem_cons_of_mem _ hq))]
          by_cases hs : straddlesEdge p a c = true
          · rw [not_crossesEdge_of_right hs (hall a (by simp)) (hall c (by simp))]
            simp
          · simp only [Bool.not_eq_true] at hs
            have hcf : crossesEdge p a c = false := by unfold crossesEdge; simp [hs]
            rw [hcf]
            simp

/-! ## 5. An interior point is inside the box -/

/-- THE LEMMA THE INDEX WAITED ON. A point the ray-casting test calls interior
lies inside any box that covers the ring, provided the ring is closed — which
every conforming WKT polygon ring is, and which the index checks at plan time
rather than assuming. -/
theorem ringClass_interior_contains {p : Point} {r : Ring} {b : BBox}
    (hcov : b.covers r) (hclosed : isClosedLine r = true)
    (h : ringClass p r = PtClass.interior) : b.contains p = true := by
  have hodd : rayCrossCount p r % 2 = 1 := by
    unfold ringClass at h
    by_cases hon : pointOnPath p r = true
    · rw [if_pos hon] at h; simp at h
    · simp only [Bool.not_eq_true] at hon
      rw [if_neg (by simp [hon])] at h
      by_cases hpar : rayCrossCount p r % 2 == 1
      · simpa using hpar
      · rw [if_neg (by simp [hpar])] at h; simp at h
  have hne : rayCrossCount p r ≠ 0 := by omega
  -- y bounds, from any straddling edge
  obtain ⟨a, c, ha, hc, hstr⟩ := exists_straddle p r hne
  have hba := hcov a ha
  have hbc := hcov c hc
  simp only [BBox.contains, Bool.and_eq_true] at hba hbc
  obtain ⟨⟨⟨ax1, ax2⟩, ay1⟩, ay2⟩ := hba
  obtain ⟨⟨⟨cx1, cx2⟩, cy1⟩, cy2⟩ := hbc
  have hy1 : Scaled.le b.ymin p.y = true ∧ Scaled.le p.y b.ymax = true := by
    rcases straddlesEdge_y hstr with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨Scaled.le_trans ay1 h1, Scaled.le_trans h2 cy2⟩
    · exact ⟨Scaled.le_trans cy1 h1, Scaled.le_trans h2 ay2⟩
  -- x lower bound, by the closed-ring parity argument
  have hx1 : Scaled.le b.xmin p.x = true := by
    refine Classical.byContradiction (fun hcon => ?_)
    simp only [Bool.not_eq_true] at hcon
    have hleft : ∀ q ∈ r, Scaled.lt p.x q.x = true := by
      intro q hq
      have hqb := hcov q hq
      simp only [BBox.contains, Bool.and_eq_true] at hqb
      have hlt : Scaled.lt p.x b.xmin = true := by
        rw [Scaled.lt_eq_not_le, hcon]; rfl
      exact Scaled.lt_of_lt_of_le hlt hqb.1.1.1
    rw [rayCrossCount_eq_straddleCount_of_left p r hleft,
        straddleCount_closed p r hclosed] at hodd
    simp at hodd
  -- x upper bound: a point right of every vertex crosses nothing
  have hx2 : Scaled.le p.x b.xmax = true := by
    refine Classical.byContradiction (fun hcon => ?_)
    simp only [Bool.not_eq_true] at hcon
    have hright : ∀ q ∈ r, Scaled.lt q.x p.x = true := by
      intro q hq
      have hqb := hcov q hq
      simp only [BBox.contains, Bool.and_eq_true] at hqb
      have hlt : Scaled.lt b.xmax p.x = true := by
        rw [Scaled.lt_eq_not_le, hcon]; rfl
      exact Scaled.lt_of_le_of_lt hqb.1.1.2 hlt
    rw [rayCrossCount_zero_of_right p r hright] at hodd
    simp at hodd
  simp only [BBox.contains, Bool.and_eq_true]
  exact ⟨⟨⟨hx1, hx2⟩, hy1.1⟩, hy1.2⟩

/-- A point the polygon test calls anything but EXTERIOR is inside a box that
covers the exterior ring and every hole. Both the interior case (ray cast) and
the boundary case (on a ring) land here. -/
theorem polygonClass_ne_exterior_contains {p : Point} {poly : Polygon} {b : BBox}
    (hcov : ∀ r ∈ poly.ext :: poly.holes, b.covers r)
    (hclosed : isClosedLine poly.ext = true)
    (h : polygonClass p poly ≠ PtClass.exterior) : b.contains p = true := by
  unfold polygonClass at h
  by_cases hon : pointOnPath p poly.ext || pointOnAnyRing p poly.holes
  · simp only [Bool.or_eq_true] at hon
    rcases hon with hext | hholes
    · exact pointOnPath_contains poly.ext (hcov poly.ext (by simp)) hext
    · exact pointOnAnyRing_contains poly.holes
        (fun r hr => hcov r (by simp [hr])) hholes
  · simp only [Bool.not_eq_true, Bool.or_eq_false_iff] at hon
    rw [if_neg (by simp [hon.1, hon.2])] at h
    -- `p` is on no ring, so the ray cast decides: interior when the count is
    -- odd, exterior otherwise, and exterior contradicts the hypothesis.
    by_cases hodd : (rayCrossCount p poly.ext % 2 == 1) = true
    · have hint : ringClass p poly.ext = PtClass.interior := by
        unfold ringClass
        rw [if_neg (by simp [hon.1]), if_pos hodd]
      exact ringClass_interior_contains (hcov poly.ext (by simp)) hclosed hint
    · exfalso
      have hext : ringClass p poly.ext = PtClass.exterior := by
        unfold ringClass
        rw [if_neg (by simp [hon.1]), if_neg (by simp [hodd])]
      rw [hext] at h
      simp at h

/-! ## 6. The trust surface

Only Lean's own three axioms. Nothing here is admitted. -/

#print axioms ringClass_interior_contains
#print axioms polygonClass_ne_exterior_contains
#print axioms pointOnPath_contains
#print axioms BBox.overlaps_of_common_point
#print axioms BBox.ofPoints_covers
#print axioms BBox.ofRings_covers

end L4Factoidal.Geo
