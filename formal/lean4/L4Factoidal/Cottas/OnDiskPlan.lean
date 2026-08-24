/-
L4Factoidal.Cottas.OnDiskPlan — layer 5 of the port of
`RDF.CottasStore`: candidate-row-group planning.

Layers 3 and 4 walk whichever row groups they are handed. This layer
decides which those are, by reading each row group's Parquet DICTIONARY
page — a fraction of the bytes a data page costs — and keeping only the
row groups whose dictionary contains the bound token.

The F\* source states the safety rule in a comment, twice:

> "If a row group is absent from the dict cache (e.g. dict page missing,
> or column has no dict at all), we INCLUDE it in candidates — safe
> fallback that may cost a wasted data-page decode, never wrong
> answers."

"Never wrong answers" is the claim the entire pruning design rests on,
and it is the one a later edit is most likely to break: making the
planner one notch more selective looks like a pure speed win right up
until it drops a row group that held a match. `planCandidateRgs_complete`
is that claim as a theorem — under a dictionary reader that does not LIE
about its column, no row group holding a matching cell is ever pruned.

## The hypothesis, said plainly

`DictReaderSound` is what the proof needs and all it needs: a dictionary
page, when present, LISTS every token its column holds in that row
group. It may list more — a dictionary with spare entries costs a wasted
decode, never a lost row — and it may be absent, which the planner
already treats as "include". What it may not do is omit a token that
appears in the column. That is exactly the Parquet dictionary-page
contract, and stating it as a hypothesis rather than assuming it is what
makes the conclusion checkable.

## The planner is a filter

`compute_candidate_rgs_loop` counts up, prepends, and the caller
reverses — the same shape as `all_rgs`. `computeCandidateRgs_eq_filter`
proves that it IS `(List.range rgCount).filter`, which delivers three
things at once: the result is ascending (so the sorted intersection's
precondition holds), membership is decidable by the keep test alone, and
the no-bounds case reduces to `allRgs` with no separate argument.

## The intersection needs its inputs sorted, and gets them

`list_nat_intersect_sorted` is a merge, so it is only correct on
ascending inputs; feeding it unsorted lists silently drops elements.
Nothing in the F\* source establishes that its inputs are sorted.
`computeCandidateRgs_sorted` supplies it, from the filter form.

No `sorry`, no user `axiom`, no `native_decide`.
-/
import L4Factoidal.Cottas.OnDiskLimit

namespace L4Factoidal.Cottas.OnDiskStore

open L4Factoidal.RDF
open L4Factoidal.Cottas.Ballyhoo

/-! ## 1. The dictionary read, as a parameter -/

/-- Read one row group's dictionary page for one column: the tokens it
lists, or `none` when the column has no dictionary page (the native
writer's `DELTA_LENGTH_BYTE_ARRAY` columns, or a cardinality Parquet
declined to dictionary-encode). -/
abbrev DictReader := Nat → Nat → Option (List String)

/-- The dictionary cache: `(rowGroup, column)` to that page's tokens.
Port of `dict_cache`. -/
abbrev DictCache := List ((Nat × Nat) × List String)

def dictCacheLookup : DictCache → Nat → Nat → Option (List String)
  | [], _, _ => none
  | ((r, k), v) :: rest, rg, col =>
      if r == rg && k == col then some v else dictCacheLookup rest rg col

/-- Linear membership on a dictionary list. Dictionaries are small —
distinct-token cardinality, not row cardinality — which is the F\*
source's stated reason for not indexing them. -/
def listStringMem : List String → String → Bool
  | [], _ => false
  | hd :: rest, s => if hd == s then true else listStringMem rest s

theorem listStringMem_iff : ∀ (xs : List String) (s : String),
    listStringMem xs s = true ↔ s ∈ xs
  | [], s => by simp [listStringMem]
  | hd :: rest, s => by
      simp only [listStringMem, List.mem_cons]
      by_cases h : hd == s
      · have he : hd = s := by simpa using h
        simp [h, he]
      · have hne : ¬ (hd = s) := by simpa using h
        simp [h, listStringMem_iff rest s, hne, Ne.symm hne]

/-! ## 2. Populating the cache

Port of `populate_dict_cache_loop`. A row group whose dictionary page is
missing is left ABSENT from the cache rather than cached as empty — the
F\* source's own note, and the reason the planner's fallback is
"include" rather than "exclude". -/

def populateDictCacheLoop (dr : DictReader) (c : DictCache) (col : Nat)
    (rgIndex rgCount fuel : Nat) : DictCache :=
  match fuel with
  | 0 => c
  | f + 1 =>
      if rgIndex ≥ rgCount then c
      else
        let c' := match dictCacheLookup c rgIndex col with
          | some _ => c
          | none =>
              match dr rgIndex col with
              | none => c
              | some dict => ((rgIndex, col), dict) :: c
        populateDictCacheLoop dr c' col (rgIndex + 1) rgCount f

def populateDictCacheForColumn (dr : DictReader) (c : DictCache)
    (col rgCount : Nat) : DictCache :=
  populateDictCacheLoop dr c col 0 rgCount rgCount

/-! ## 3. Soundness of a dictionary

The hypothesis the safety theorem needs, and all it needs. -/

def DictReaderSound (dr : DictReader) (rd : ColumnReader) : Prop :=
  ∀ (rg col : Nat) (dict : List String) (cl : Column) (i : Nat) (t : String),
    dr rg col = some dict → rd rg col = some cl → cellAt cl i = some t →
    listStringMem dict t = true

def DictCacheSound (c : DictCache) (rd : ColumnReader) : Prop :=
  ∀ (rg col : Nat) (dict : List String) (cl : Column) (i : Nat) (t : String),
    dictCacheLookup c rg col = some dict → rd rg col = some cl →
    cellAt cl i = some t → listStringMem dict t = true

theorem dictCacheSound_nil (rd : ColumnReader) :
    DictCacheSound [] rd := by
  intro rg col dict cl i t h _ _
  simp [dictCacheLookup] at h

theorem dictCacheSound_cons (dr : DictReader) (rd : ColumnReader)
    (hdr : DictReaderSound dr rd) (c : DictCache) (hc : DictCacheSound c rd)
    (rg col : Nat) (dict : List String) (hd : dr rg col = some dict) :
    DictCacheSound (((rg, col), dict) :: c) rd := by
  intro rg' col' dict' cl i t hlk hcl hcell
  simp only [dictCacheLookup] at hlk
  by_cases hk : (rg == rg') && (col == col')
  · rw [if_pos hk] at hlk
    obtain ⟨h1, h2⟩ := Bool.and_eq_true .. |>.mp hk
    have e1 : rg = rg' := by simpa using h1
    have e2 : col = col' := by simpa using h2
    subst e1; subst e2
    have hdd : dict' = dict := by simpa using hlk.symm
    rw [hdd]
    exact hdr rg col dict cl i t hd hcl hcell
  · rw [if_neg hk] at hlk
    exact hc rg' col' dict' cl i t hlk hcl hcell

theorem populateDictCacheLoop_sound (dr : DictReader) (rd : ColumnReader)
    (hdr : DictReaderSound dr rd) (col : Nat) :
    ∀ (fuel rgIndex rgCount : Nat) (c : DictCache), DictCacheSound c rd →
      DictCacheSound (populateDictCacheLoop dr c col rgIndex rgCount fuel) rd
  | 0, _, _, c, hc => hc
  | fuel + 1, i, n, c, hc => by
      rw [populateDictCacheLoop]
      by_cases h : i ≥ n
      · simpa [h] using hc
      · simp only [h, ge_iff_le, if_neg, not_false_eq_true]
        refine populateDictCacheLoop_sound dr rd hdr col fuel (i + 1) n _ ?_
        cases hlk : dictCacheLookup c i col with
        | some _ => simpa [hlk] using hc
        | none =>
            cases hdd : dr i col with
            | none => simpa [hlk, hdd] using hc
            | some dict =>
                simpa [hlk, hdd] using
                  dictCacheSound_cons dr rd hdr c hc i col dict hdd

theorem populateDictCacheForColumn_sound (dr : DictReader) (rd : ColumnReader)
    (hdr : DictReaderSound dr rd) (c : DictCache) (hc : DictCacheSound c rd)
    (col rgCount : Nat) :
    DictCacheSound (populateDictCacheForColumn dr c col rgCount) rd :=
  populateDictCacheLoop_sound dr rd hdr col rgCount 0 rgCount c hc

/-! ## 4. The planner is a filter -/

/-- Keep this row group for this bound? A row group ABSENT from the
cache is kept — the safe fallback. -/
def rgKeeps (c : DictCache) (col : Nat) (tok : String) (rg : Nat) : Bool :=
  match dictCacheLookup c rg col with
  | none => true
  | some dict => listStringMem dict tok

def computeCandidateRgsLoop (c : DictCache) (col : Nat) (tok : String)
    (rgIndex rgCount fuel : Nat) (accRev : List Nat) : List Nat :=
  match fuel with
  | 0 => accRev
  | f + 1 =>
      if rgIndex ≥ rgCount then accRev
      else
        computeCandidateRgsLoop c col tok (rgIndex + 1) rgCount f
          (if rgKeeps c col tok rgIndex then rgIndex :: accRev else accRev)

def computeCandidateRgs (c : DictCache) (col : Nat) (tok : String)
    (rgCount : Nat) : List Nat :=
  (computeCandidateRgsLoop c col tok 0 rgCount rgCount []).reverse

theorem computeCandidateRgsLoop_eq_filter (c : DictCache) (col : Nat)
    (tok : String) :
    ∀ (fuel rgIndex rgCount : Nat) (accRev : List Nat),
      rgCount - rgIndex ≤ fuel →
      computeCandidateRgsLoop c col tok rgIndex rgCount fuel accRev
        = ((List.range' rgIndex (rgCount - rgIndex)).filter
            (rgKeeps c col tok)).reverse ++ accRev
  | 0, i, n, accRev, hf => by
      have h : n - i = 0 := by omega
      simp [computeCandidateRgsLoop, h]
  | fuel + 1, i, n, accRev, hf => by
      rw [computeCandidateRgsLoop]
      by_cases h : i ≥ n
      · have hz : n - i = 0 := by omega
        simp [h, hz]
      · have hk : n - i = (n - (i + 1)) + 1 := by omega
        simp only [h, if_neg, not_false_eq_true]
        rw [computeCandidateRgsLoop_eq_filter c col tok fuel (i + 1) n _
              (by omega), hk, List.range'_succ]
        by_cases hkeep : rgKeeps c col tok i
        · simp [hkeep]
        · simp [hkeep]

theorem computeCandidateRgs_eq_filter (c : DictCache) (col : Nat)
    (tok : String) (rgCount : Nat) :
    computeCandidateRgs c col tok rgCount
      = (List.range rgCount).filter (rgKeeps c col tok) := by
  simp only [computeCandidateRgs,
             computeCandidateRgsLoop_eq_filter c col tok rgCount 0 rgCount []
               (by omega),
             Nat.sub_zero, List.append_nil, List.reverse_reverse]
  rw [List.range_eq_range']

theorem computeCandidateRgs_sorted (c : DictCache) (col : Nat) (tok : String)
    (rgCount : Nat) :
    (computeCandidateRgs c col tok rgCount).Pairwise (· < ·) := by
  rw [computeCandidateRgs_eq_filter]
  exact List.Pairwise.sublist List.filter_sublist List.pairwise_lt_range

theorem mem_computeCandidateRgs (c : DictCache) (col : Nat) (tok : String)
    (rgCount rg : Nat) :
    rg ∈ computeCandidateRgs c col tok rgCount
      ↔ (rg < rgCount ∧ rgKeeps c col tok rg = true) := by
  rw [computeCandidateRgs_eq_filter]
  simp [List.mem_filter]

/-- **A row group whose column holds the bound token is never pruned.**
The per-column half of the safety claim. -/
theorem computeCandidateRgs_complete (c : DictCache) (rd : ColumnReader)
    (hc : DictCacheSound c rd) (col : Nat) (tok : String) (rgCount rg : Nat)
    (hlt : rg < rgCount) (cl : Column) (hcl : rd rg col = some cl)
    (i : Nat) (hcell : cellAt cl i = some tok) :
    rg ∈ computeCandidateRgs c col tok rgCount := by
  rw [mem_computeCandidateRgs]
  refine ⟨hlt, ?_⟩
  simp only [rgKeeps]
  cases hlk : dictCacheLookup c rg col with
  | none => rfl
  | some dict => exact hc rg col dict cl i tok hlk hcl hcell

/-! ## 5. The sorted intersection

A merge, so it is correct only on ascending inputs — feeding it unsorted
lists silently drops elements, and nothing in the F\* source establishes
that its inputs are sorted. `computeCandidateRgs_sorted` supplies it. -/

def listNatIntersectSorted : List Nat → List Nat → List Nat → Nat → List Nat
  | _, _, accRev, 0 => accRev
  | [], _, accRev, _ + 1 => accRev
  | _ :: _, [], accRev, _ + 1 => accRev
  | x :: xrest, y :: yrest, accRev, f + 1 =>
      if x = y then listNatIntersectSorted xrest yrest (x :: accRev) f
      else if x < y then listNatIntersectSorted xrest (y :: yrest) accRev f
      else listNatIntersectSorted (x :: xrest) yrest accRev f

def intersectSortedRgLists (xs ys : List Nat) : List Nat :=
  (listNatIntersectSorted xs ys [] (xs.length + ys.length + 1)).reverse

/-- An ascending list holds nothing below its head. -/
theorem not_mem_of_lt_head {y : Nat} {yrest : List Nat} {a : Nat}
    (hs : (y :: yrest).Pairwise (· < ·)) (hlt : a < y) : a ∉ y :: yrest := by
  intro hmem
  rcases List.mem_cons.mp hmem with rfl | hmem
  · exact Nat.lt_irrefl _ hlt
  · exact Nat.lt_irrefl _ (Nat.lt_trans hlt ((List.pairwise_cons.mp hs).1 a hmem))

/-- **Completeness of the merge intersection.** Everything in both
inputs survives. (Soundness — that nothing else survives — is a
performance property, not a correctness one, and is not what the safety
claim needs.) -/
theorem listNatIntersectSorted_complete :
    ∀ (fuel : Nat) (xs ys : List Nat) (accRev : List Nat) (a : Nat),
      xs.length + ys.length ≤ fuel →
      xs.Pairwise (· < ·) → ys.Pairwise (· < ·) →
      (a ∈ accRev ∨ (a ∈ xs ∧ a ∈ ys)) →
      a ∈ listNatIntersectSorted xs ys accRev fuel
  | 0, xs, ys, accRev, a, hf, _, _, h => by
      have hx : xs = [] := by
        cases xs with
        | nil => rfl
        | cons _ _ => simp at hf
      subst hx
      rw [listNatIntersectSorted]
      rcases h with h | ⟨h, _⟩
      · exact h
      · simp at h
  | fuel + 1, [], ys, accRev, a, hf, _, _, h => by
      rw [listNatIntersectSorted]
      rcases h with h | ⟨h, _⟩
      · exact h
      · simp at h
  | fuel + 1, x :: xrest, [], accRev, a, hf, _, _, h => by
      rw [listNatIntersectSorted]
      rcases h with h | ⟨_, h⟩
      · exact h
      · simp at h
  | fuel + 1, x :: xrest, y :: yrest, accRev, a, hf, hsx, hsy, h => by
      rw [listNatIntersectSorted]
      by_cases hxy : x = y
      · simp only [hxy, if_pos]
        refine listNatIntersectSorted_complete fuel xrest yrest (y :: accRev) a
          (by simp at hf ⊢; omega) (List.pairwise_cons.mp (hxy ▸ hsx)).2
          (List.pairwise_cons.mp hsy).2 ?_
        rcases h with h | ⟨h1, h2⟩
        · exact Or.inl (List.mem_cons_of_mem _ h)
        · rcases List.mem_cons.mp h2 with rfl | h2'
          · exact Or.inl (List.mem_cons_self ..)
          · rcases List.mem_cons.mp h1 with rfl | h1'
            · exact Or.inl (by simp [hxy])
            · exact Or.inr ⟨h1', h2'⟩
      · simp only [hxy, if_neg, not_false_eq_true]
        by_cases hlt : x < y
        · simp only [hlt, if_pos]
          refine listNatIntersectSorted_complete fuel xrest (y :: yrest) accRev a
            (by simp at hf ⊢; omega) (List.pairwise_cons.mp hsx).2 hsy ?_
          rcases h with h | ⟨h1, h2⟩
          · exact Or.inl h
          · rcases List.mem_cons.mp h1 with rfl | h1'
            · exact absurd h2 (not_mem_of_lt_head hsy hlt)
            · exact Or.inr ⟨h1', h2⟩
        · simp only [hlt, if_neg, not_false_eq_true]
          have hgt : y < x := by omega
          refine listNatIntersectSorted_complete fuel (x :: xrest) yrest accRev a
            (by simp at hf ⊢; omega) hsx (List.pairwise_cons.mp hsy).2 ?_
          rcases h with h | ⟨h1, h2⟩
          · exact Or.inl h
          · rcases List.mem_cons.mp h2 with rfl | h2'
            · exact absurd h1 (not_mem_of_lt_head hsx hgt)
            · exact Or.inr ⟨h1, h2'⟩

theorem mem_intersectSortedRgLists (xs ys : List Nat) (a : Nat)
    (hsx : xs.Pairwise (· < ·)) (hsy : ys.Pairwise (· < ·))
    (hx : a ∈ xs) (hy : a ∈ ys) : a ∈ intersectSortedRgLists xs ys := by
  simp only [intersectSortedRgLists, List.mem_reverse]
  exact listNatIntersectSorted_complete (xs.length + ys.length + 1) xs ys [] a
    (by omega) hsx hsy (Or.inr ⟨hx, hy⟩)

/-! ## 6. The intersection is a sublist of its left input

Needed because the planner intersects repeatedly: without this, the
second intersection has no sorted left input and the merge is being fed
something it is only correct on by accident. -/

theorem listNatIntersectSorted_sublist :
    ∀ (fuel : Nat) (xs ys accRev : List Nat),
      ∃ R : List Nat,
        listNatIntersectSorted xs ys accRev fuel = R ++ accRev
          ∧ R.reverse.Sublist xs
  | 0, xs, ys, accRev => ⟨[], by rw [listNatIntersectSorted]; simp, by simp⟩
  | fuel + 1, [], ys, accRev => ⟨[], by rw [listNatIntersectSorted]; simp, by simp⟩
  | fuel + 1, x :: xrest, [], accRev =>
      ⟨[], by rw [listNatIntersectSorted]; simp, by simp⟩
  | fuel + 1, x :: xrest, y :: yrest, accRev => by
      rw [listNatIntersectSorted]
      by_cases hxy : x = y
      · simp only [hxy, if_pos]
        obtain ⟨R, hR, hsub⟩ :=
          listNatIntersectSorted_sublist fuel xrest yrest (y :: accRev)
        refine ⟨R ++ [y], by rw [hR]; simp, ?_⟩
        simp only [List.reverse_append, List.reverse_cons, List.reverse_nil,
                   List.nil_append, List.cons_append]
        exact List.Sublist.cons_cons y hsub
      · simp only [hxy, if_neg, not_false_eq_true]
        by_cases hlt : x < y
        · simp only [hlt, if_pos]
          obtain ⟨R, hR, hsub⟩ :=
            listNatIntersectSorted_sublist fuel xrest (y :: yrest) accRev
          exact ⟨R, hR, List.Sublist.cons x hsub⟩
        · simp only [hlt, if_neg, not_false_eq_true]
          exact listNatIntersectSorted_sublist fuel (x :: xrest) yrest accRev

theorem intersectSortedRgLists_sublist (xs ys : List Nat) :
    (intersectSortedRgLists xs ys).Sublist xs := by
  obtain ⟨R, hR, hsub⟩ :=
    listNatIntersectSorted_sublist (xs.length + ys.length + 1) xs ys []
  simpa [intersectSortedRgLists, hR] using hsub

theorem intersectSortedRgLists_sorted (xs ys : List Nat)
    (hsx : xs.Pairwise (· < ·)) : (intersectSortedRgLists xs ys).Pairwise (· < ·) :=
  hsx.sublist (intersectSortedRgLists_sublist xs ys)

/-! ## 7. Composing the bounds

Port of `plan_candidate_rgs`. Start from every row group and intersect
each present bound's candidate set into it. The graph column (index 3)
prunes too — the F\* source says so and includes it. -/

structure PlanState where
  cands : List Nat
  cache : DictCache

def planStep (dr : DictReader) (rgCount : Nat) (st : PlanState) (col : Nat) :
    Option String → PlanState
  | none => st
  | some tok =>
      let c' := populateDictCacheForColumn dr st.cache col rgCount
      { cands := intersectSortedRgLists st.cands
                   (computeCandidateRgs c' col tok rgCount)
        cache := c' }

def planCandidateRgs (dr : DictReader) (bs bp bo bg : Option String)
    (rgCount : Nat) : PlanState :=
  let st0 : PlanState := { cands := allRgs rgCount, cache := [] }
  let st1 := planStep dr rgCount st0 0 bs
  let st2 := planStep dr rgCount st1 1 bp
  let st3 := planStep dr rgCount st2 2 bo
  planStep dr rgCount st3 3 bg

/-- With no bound on any column the plan is every row group — which
`walkRange_eq_walkCandidates` already showed is the unpruned scan. -/
theorem planCandidateRgs_unbounded (dr : DictReader) (rgCount : Nat) :
    (planCandidateRgs dr none none none none rgCount).cands
      = List.range rgCount := by
  simp [planCandidateRgs, planStep, allRgs_eq_range]

/-! ## 8. The safety claim

"Never wrong answers", as a theorem. -/

/-- What it means for a row group's column to hold a bound's token. An
unbound column imposes nothing. -/
def ColumnHolds (rd : ColumnReader) (rg col : Nat) (b : Option String) : Prop :=
  ∀ tok, b = some tok →
    ∃ (cl : Column) (i : Nat), rd rg col = some cl ∧ cellAt cl i = some tok

theorem planStep_sorted (dr : DictReader) (rgCount : Nat) (st : PlanState)
    (col : Nat) (b : Option String) (hs : st.cands.Pairwise (· < ·)) :
    (planStep dr rgCount st col b).cands.Pairwise (· < ·) := by
  cases b with
  | none => simpa [planStep] using hs
  | some tok => exact intersectSortedRgLists_sorted _ _ hs

theorem planStep_cacheSound (dr : DictReader) (rd : ColumnReader)
    (hdr : DictReaderSound dr rd) (rgCount : Nat) (st : PlanState)
    (hcs : DictCacheSound st.cache rd) (col : Nat) (b : Option String) :
    DictCacheSound (planStep dr rgCount st col b).cache rd := by
  cases b with
  | none => simpa [planStep] using hcs
  | some tok =>
      simpa [planStep] using
        populateDictCacheForColumn_sound dr rd hdr st.cache hcs col rgCount

theorem planStep_complete (dr : DictReader) (rd : ColumnReader)
    (hdr : DictReaderSound dr rd) (rgCount : Nat) (st : PlanState)
    (hcs : DictCacheSound st.cache rd) (hss : st.cands.Pairwise (· < ·))
    (col : Nat) (b : Option String) (rg : Nat) (hlt : rg < rgCount)
    (hin : rg ∈ st.cands) (hholds : ColumnHolds rd rg col b) :
    rg ∈ (planStep dr rgCount st col b).cands := by
  cases hb : b with
  | none => simpa [planStep] using hin
  | some tok =>
      obtain ⟨cl, i, hcl, hcell⟩ := hholds tok (by rw [← hb])
      have hc' := populateDictCacheForColumn_sound dr rd hdr st.cache hcs col
        rgCount
      have hmem := computeCandidateRgs_complete
        (populateDictCacheForColumn dr st.cache col rgCount) rd hc' col tok
        rgCount rg hlt cl hcl i hcell
      simpa [planStep] using
        mem_intersectSortedRgLists st.cands _ rg hss
          (computeCandidateRgs_sorted _ col tok rgCount) hin hmem

/-- **No row group holding a matching cell is ever pruned.** The claim
the F\* source states twice as a comment — "safe fallback that may cost
a wasted data-page decode, never wrong answers" — under the one
hypothesis it needs: a dictionary page, when present, lists every token
its column holds. -/
theorem planCandidateRgs_complete (dr : DictReader) (rd : ColumnReader)
    (hdr : DictReaderSound dr rd) (bs bp bo bg : Option String)
    (rgCount rg : Nat) (hlt : rg < rgCount)
    (h0 : ColumnHolds rd rg 0 bs) (h1 : ColumnHolds rd rg 1 bp)
    (h2 : ColumnHolds rd rg 2 bo) (h3 : ColumnHolds rd rg 3 bg) :
    rg ∈ (planCandidateRgs dr bs bp bo bg rgCount).cands := by
  simp only [planCandidateRgs]
  have hs0 : (allRgs rgCount).Pairwise (· < ·) := by
    rw [allRgs_eq_range]; exact List.pairwise_lt_range
  have hin0 : rg ∈ allRgs rgCount := by
    rw [allRgs_eq_range]; simpa using hlt
  have hc0 : DictCacheSound ([] : DictCache) rd := dictCacheSound_nil rd
  have e1 := planStep_complete dr rd hdr rgCount
    { cands := allRgs rgCount, cache := [] } hc0 hs0 0 bs rg hlt hin0 h0
  have s1 := planStep_sorted dr rgCount
    { cands := allRgs rgCount, cache := [] } 0 bs hs0
  have c1 := planStep_cacheSound dr rd hdr rgCount
    { cands := allRgs rgCount, cache := [] } hc0 0 bs
  have e2 := planStep_complete dr rd hdr rgCount _ c1 s1 1 bp rg hlt e1 h1
  have s2 := planStep_sorted dr rgCount _ 1 bp s1
  have c2 := planStep_cacheSound dr rd hdr rgCount _ c1 1 bp
  have e3 := planStep_complete dr rd hdr rgCount _ c2 s2 2 bo rg hlt e2 h2
  have s3 := planStep_sorted dr rgCount _ 2 bo s2
  have c3 := planStep_cacheSound dr rd hdr rgCount _ c2 2 bo
  exact planStep_complete dr rd hdr rgCount _ c3 s3 3 bg rg hlt e3 h3

/-! ## Build-time checks -/

/-- Two row groups. Row group 0's predicate dictionary lists `<p:1>`;
row group 1's lists `<p:2>`. Row group 2 has no dictionary page. -/
private def drTwo : DictReader := fun rg col =>
  if col == 1 then
    match rg with
    | 0 => some ["<p:1>"]
    | 1 => some ["<p:2>"]
    | _ => none
  else none

private def cTwo : DictCache := populateDictCacheForColumn drTwo [] 1 3

/-! The bound token prunes to the row group whose dictionary lists it —
and the row group with no dictionary page is KEPT. -/
#guard computeCandidateRgs cTwo 1 "<p:1>" 3 == [0, 2]
#guard computeCandidateRgs cTwo 1 "<p:2>" 3 == [1, 2]
#guard computeCandidateRgs cTwo 1 "<p:9>" 3 == [2]

/-! An empty cache prunes nothing. -/
#guard computeCandidateRgs [] 1 "<p:1>" 3 == [0, 1, 2]

/-! Dictionary membership. -/
#guard listStringMem ["<p:1>", "<p:2>"] "<p:2>"
#guard ! listStringMem ["<p:1>"] "<p:2>"
#guard ! listStringMem [] "<p:1>"

/-! The sorted intersection keeps what is in both, and nothing else. -/
#guard intersectSortedRgLists [0, 1, 2, 3] [1, 3, 5] == [1, 3]
#guard intersectSortedRgLists [0, 1] [2, 3] == ([] : List Nat)
#guard intersectSortedRgLists [] [1, 2] == ([] : List Nat)
#guard intersectSortedRgLists [1, 2] [] == ([] : List Nat)

/-! No bound: every row group. -/
#guard (planCandidateRgs drTwo none none none none 3).cands == [0, 1, 2]

/-! One bound on the predicate column. -/
#guard (planCandidateRgs drTwo none (some "<p:1>") none none 3).cands == [0, 2]

/-! ⚠️ A bound on a column with NO dictionary pages prunes nothing —
the safe fallback, not a bug. -/
#guard (planCandidateRgs drTwo (some "<a:1>") none none none 3).cands
        == [0, 1, 2]

/-! Two bounds intersect. The subject column has no dictionaries here,
so its candidate set is everything and the predicate bound decides. -/
#guard (planCandidateRgs drTwo (some "<a:1>") (some "<p:2>") none none 3).cands
        == [1, 2]

/-! ## Axiom audit -/

#print axioms computeCandidateRgs_eq_filter
#print axioms computeCandidateRgs_complete
#print axioms intersectSortedRgLists_sorted
#print axioms mem_intersectSortedRgLists
#print axioms planCandidateRgs_unbounded
#print axioms planCandidateRgs_complete

end L4Factoidal.Cottas.OnDiskStore
