/-
L4Factoidal.Cottas.OnDiskLimit — layer 4 of the port of
`RDF.CottasStore`: LIMIT pushdown.

`RDF/StoreCapabilities.lean` already states the law a backend's LIMIT
path must satisfy — `StoreCapsLawful.limitAgrees`: a limited read
returns the prefix the unbounded read would have returned. The COTTAS
backend has a whole second family of walks for LIMIT
(`filter_zipped_rows_limited_seq`, `walk_row_groups_search_limited`,
`walk_candidate_rgs_search_limited`, and their `_tok` and `_global`
siblings), and nothing in the F\* tree connects them to the unlimited
family at all.

`filterLimitedTok_prefix` and `walkCandidatesLimitedTok_prefix` are that
connection: the limited walk's answer, flipped into row order, is the
unlimited walk's answer flipped and truncated. Early exit is a
refinement of the full scan, so a `LIMIT`-bearing query cannot return a
row the unlimited query would not, nor stop before it has `limit` of
them.

## The count is the length

The F\* limited walks carry `acc_count` alongside `acc_rev` and
increment the two together. `filterLimitedTok_count` proves the
invariant, so the count is not a second source of truth that an edit
can desynchronise from the list.

## A branch that cannot be taken

The F\* source's end-of-row-group arm returns
`(acc_rev, acc_count, acc_count >= limit)` — but that arm is only
reachable when the FIRST guard, `acc_count >= limit`, was false, so the
flag it computes is always `false`. It is transcribed here as written,
and `filterLimitedTok_end_flag_false` states that the computation is
dead. Deleting it would be a change to the F\* source, which this port
does not make; recording that it decides nothing is what the port can
do.

## Ordering, again

Both families accumulate in reverse and leave the flip to the caller, so
every statement here is about `.reverse`. Getting that backwards would
turn "the first `limit` rows" into "the last `limit` rows", which is why
the theorems are stated on the flipped list rather than on the
accumulator.

No `sorry`, no user `axiom`, no `native_decide`.
-/
import L4Factoidal.Cottas.OnDiskWalk

namespace L4Factoidal.Cottas.OnDiskStore

open L4Factoidal.RDF
open L4Factoidal.Cottas.Ballyhoo

/-! ## 1. Two unfolding lemmas

`filterTokSeq` and `filterLimitedTok` both recurse on `n - i`, so their
equation lemmas are `dite`-shaped and rewriting with the definition name
unfolds an unpredictable number of levels. Naming the two branches once
keeps every proof below controllable. -/

theorem filterTokSeq_lt (bs bp bo bg : Option String) (sc pc oc gc : Column)
    (n i : Nat) (accRev : List QpRowTok) (h : i < n) :
    filterTokSeq bs bp bo bg sc pc oc gc n i accRev
      = filterTokSeq bs bp bo bg sc pc oc gc n (i + 1)
          (match rowSelected bs bp bo bg sc pc oc gc i with
           | some r => r :: accRev
           | none => accRev) := by
  rw [filterTokSeq, dif_pos h]
  rfl

theorem filterTokSeq_ge (bs bp bo bg : Option String) (sc pc oc gc : Column)
    (n i : Nat) (accRev : List QpRowTok) (h : ¬ i < n) :
    filterTokSeq bs bp bo bg sc pc oc gc n i accRev = accRev := by
  rw [filterTokSeq, dif_neg h]

/-! ## 2. The unlimited walk accumulates

Everything below rests on this: a walk started from a non-empty
accumulator appends to it and never inspects it. -/

theorem filterTokSeq_append (bs bp bo bg : Option String)
    (sc pc oc gc : Column) :
    ∀ (fuel n i : Nat) (accRev : List QpRowTok), n - i ≤ fuel →
      filterTokSeq bs bp bo bg sc pc oc gc n i accRev
        = filterTokSeq bs bp bo bg sc pc oc gc n i [] ++ accRev
  | 0, n, i, accRev, hf => by
      have h : ¬ i < n := by omega
      rw [filterTokSeq_ge (h := h),
          filterTokSeq_ge (h := h)]
      simp
  | fuel + 1, n, i, accRev, hf => by
      by_cases h : i < n
      · rw [filterTokSeq_lt (h := h),
            filterTokSeq_lt (h := h)]
        cases hsel : rowSelected bs bp bo bg sc pc oc gc i with
        | none =>
            exact filterTokSeq_append bs bp bo bg sc pc oc gc fuel n (i + 1)
              accRev (by omega)
        | some r =>
            rw [filterTokSeq_append bs bp bo bg sc pc oc gc fuel n (i + 1)
                  (r :: accRev) (by omega),
                filterTokSeq_append bs bp bo bg sc pc oc gc fuel n (i + 1)
                  [r] (by omega)]
            simp
      · rw [filterTokSeq_ge (h := h),
            filterTokSeq_ge (h := h)]
        simp

/-! ## 3. The limited filter

Port of `filter_zipped_rows_limited_tok_seq`. The `acc_count >= limit`
guard comes FIRST, before the end-of-row-group check — which is what
makes the third component of the end arm dead. -/

def filterLimitedTok (bs bp bo bg : Option String) (sc pc oc gc : Column)
    (n i : Nat) (accRev : List QpRowTok) (accCount limit : Nat) :
    List QpRowTok × Nat × Bool :=
  if accCount ≥ limit then (accRev, accCount, true)
  else if i ≥ n then (accRev, accCount, decide (accCount ≥ limit))
  else
    match rowSelected bs bp bo bg sc pc oc gc i with
    | some r =>
        filterLimitedTok bs bp bo bg sc pc oc gc n (i + 1) (r :: accRev)
          (accCount + 1) limit
    | none =>
        filterLimitedTok bs bp bo bg sc pc oc gc n (i + 1) accRev accCount limit
termination_by n - i
decreasing_by all_goals omega

theorem filterLimitedTok_full (bs bp bo bg : Option String)
    (sc pc oc gc : Column) (n i : Nat) (accRev : List QpRowTok)
    (accCount limit : Nat) (hc : ¬ accCount ≥ limit) (h : ¬ i ≥ n) :
    filterLimitedTok bs bp bo bg sc pc oc gc n i accRev accCount limit
      = match rowSelected bs bp bo bg sc pc oc gc i with
        | some r =>
            filterLimitedTok bs bp bo bg sc pc oc gc n (i + 1) (r :: accRev)
              (accCount + 1) limit
        | none =>
            filterLimitedTok bs bp bo bg sc pc oc gc n (i + 1) accRev accCount
              limit := by
  rw [filterLimitedTok]; simp [hc, h]

theorem filterLimitedTok_hit (bs bp bo bg : Option String)
    (sc pc oc gc : Column) (n i : Nat) (accRev : List QpRowTok)
    (accCount limit : Nat) (hc : accCount ≥ limit) :
    filterLimitedTok bs bp bo bg sc pc oc gc n i accRev accCount limit
      = (accRev, accCount, true) := by
  rw [filterLimitedTok]; simp [hc]

/-- The end-of-row-group arm. The F\* source computes
`acc_count >= limit` for the flag here, but this arm is only reachable
when that same test already failed, so the flag is always `false`. The
computation is transcribed as written and shown to decide nothing. -/
theorem filterLimitedTok_end (bs bp bo bg : Option String)
    (sc pc oc gc : Column) (n i : Nat) (accRev : List QpRowTok)
    (accCount limit : Nat) (hc : ¬ accCount ≥ limit) (h : i ≥ n) :
    filterLimitedTok bs bp bo bg sc pc oc gc n i accRev accCount limit
      = (accRev, accCount, false) := by
  rw [filterLimitedTok]; simp [hc, h]

/-! ## 4. The count is the length -/

theorem filterLimitedTok_count (bs bp bo bg : Option String)
    (sc pc oc gc : Column) :
    ∀ (fuel n i : Nat) (accRev : List QpRowTok) (limit : Nat), n - i ≤ fuel →
      (filterLimitedTok bs bp bo bg sc pc oc gc n i accRev accRev.length
        limit).2.1
        = (filterLimitedTok bs bp bo bg sc pc oc gc n i accRev accRev.length
            limit).1.length
  | 0, n, i, accRev, limit, hf => by
      by_cases hc : accRev.length ≥ limit
      · rw [filterLimitedTok_hit (hc := hc)]
      · have h : i ≥ n := by omega
        rw [filterLimitedTok_end (hc := hc) (h := h)]
  | fuel + 1, n, i, accRev, limit, hf => by
      by_cases hc : accRev.length ≥ limit
      · rw [filterLimitedTok_hit (hc := hc)]
      · by_cases h : i ≥ n
        · rw [filterLimitedTok_end (hc := hc) (h := h)]
        · rw [filterLimitedTok_full (hc := hc) (h := h)]
          cases hsel : rowSelected bs bp bo bg sc pc oc gc i with
          | none =>
              exact filterLimitedTok_count bs bp bo bg sc pc oc gc fuel n
                (i + 1) accRev limit (by omega)
          | some r =>
              have := filterLimitedTok_count bs bp bo bg sc pc oc gc fuel n
                (i + 1) (r :: accRev) limit (by omega)
              simpa using this

/-! ## 5. The flag says exactly whether the count reached the limit

Needed below because the walk's early-exit branch and its recursive
branch have to be shown to agree, and the flag is the only thing that
distinguishes them. -/

theorem filterLimitedTok_flag (bs bp bo bg : Option String)
    (sc pc oc gc : Column) :
    ∀ (fuel n i : Nat) (accRev : List QpRowTok) (accCount limit : Nat),
      n - i ≤ fuel →
      (((filterLimitedTok bs bp bo bg sc pc oc gc n i accRev accCount
          limit).2.2 = true)
        ↔ ((filterLimitedTok bs bp bo bg sc pc oc gc n i accRev accCount
              limit).2.1 ≥ limit))
  | 0, n, i, accRev, accCount, limit, hf => by
      by_cases hc : accCount ≥ limit
      · rw [filterLimitedTok_hit (hc := hc)]; simp [hc]
      · have h : i ≥ n := by omega
        rw [filterLimitedTok_end (hc := hc) (h := h)]; simp [hc]
  | fuel + 1, n, i, accRev, accCount, limit, hf => by
      by_cases hc : accCount ≥ limit
      · rw [filterLimitedTok_hit (hc := hc)]; simp [hc]
      · by_cases h : i ≥ n
        · rw [filterLimitedTok_end (hc := hc) (h := h)]; simp [hc]
        · rw [filterLimitedTok_full (hc := hc) (h := h)]
          cases hsel : rowSelected bs bp bo bg sc pc oc gc i with
          | none =>
              exact filterLimitedTok_flag bs bp bo bg sc pc oc gc fuel n (i + 1)
                accRev accCount limit (by omega)
          | some r =>
              exact filterLimitedTok_flag bs bp bo bg sc pc oc gc fuel n (i + 1)
                (r :: accRev) (accCount + 1) limit (by omega)

/-! ## 6. Early exit is the unlimited walk, truncated

The COTTAS backend's version of `StoreCapsLawful.limitAgrees`. -/

theorem filterLimitedTok_prefix (bs bp bo bg : Option String)
    (sc pc oc gc : Column) :
    ∀ (fuel n i : Nat) (accRev : List QpRowTok) (limit : Nat), n - i ≤ fuel →
      accRev.length ≤ limit →
      (filterLimitedTok bs bp bo bg sc pc oc gc n i accRev accRev.length
        limit).1.reverse
        = accRev.reverse
            ++ (filterTokSeq bs bp bo bg sc pc oc gc n i []).reverse.take
                 (limit - accRev.length)
  | 0, n, i, accRev, limit, hf, hle => by
      have h : ¬ i < n := by omega
      rw [filterTokSeq_ge (h := h)]
      by_cases hc : accRev.length ≥ limit
      · rw [filterLimitedTok_hit (hc := hc)]; simp
      · rw [filterLimitedTok_end (hc := hc) (h := by omega)]; simp
  | fuel + 1, n, i, accRev, limit, hf, hle => by
      by_cases hc : accRev.length ≥ limit
      · have heq : limit - accRev.length = 0 := by omega
        rw [filterLimitedTok_hit (hc := hc), heq]; simp
      · by_cases h : i ≥ n
        · rw [filterLimitedTok_end (hc := hc) (h := h),
              filterTokSeq_ge (h := (by omega))]
          simp
        · rw [filterLimitedTok_full (hc := hc) (h := h),
              filterTokSeq_lt (h := (by omega))]
          cases hsel : rowSelected bs bp bo bg sc pc oc gc i with
          | none =>
              exact filterLimitedTok_prefix bs bp bo bg sc pc oc gc fuel n
                (i + 1) accRev limit (by omega) hle
          | some r =>
              have hstep := filterLimitedTok_prefix bs bp bo bg sc pc oc gc
                fuel n (i + 1) (r :: accRev) limit (by omega) (by simp; omega)
              rw [show ((r :: accRev).length) = accRev.length + 1 by simp]
                at hstep
              rw [hstep,
                  filterTokSeq_append bs bp bo bg sc pc oc gc fuel n (i + 1)
                    [r] (by omega)]
              have hk : limit - accRev.length
                  = (limit - (accRev.length + 1)) + 1 := by omega
              simp [hk]

/-- The entry-point form: start from nothing, and the limited answer in
row order is the unlimited answer in row order, truncated. -/
theorem filterLimitedTok_prefix_start (bs bp bo bg : Option String)
    (sc pc oc gc : Column) (n limit : Nat) :
    (filterLimitedTok bs bp bo bg sc pc oc gc n 0 [] 0 limit).1.reverse
      = (filterTokSeq bs bp bo bg sc pc oc gc n 0 []).reverse.take limit := by
  have h := filterLimitedTok_prefix bs bp bo bg sc pc oc gc n n 0 [] limit
    (by omega) (by simp)
  simpa using h

/-! ## 7. One row group, then many

`rgCols` splits the four-way column read ONCE, so the lemmas below case
on one `Option` rather than on sixteen combinations. -/

def rgCols (rd : ColumnReader) (rg : Nat) :
    Option (Column × Column × Column × Column) :=
  match rd rg 0, rd rg 1, rd rg 2, rd rg 3 with
  | some sc, some pc, some oc, some gc => some (sc, pc, oc, gc)
  | _, _, _, _ => none

theorem rgStepTok_cols (rd : ColumnReader) (bs bp bo bg : Option String)
    (rg : Nat) (accRev : List QpRowTok) :
    rgStepTok rd bs bp bo bg rg accRev
      = match rgCols rd rg with
        | some c =>
            filterTokSeq bs bp bo bg c.1 c.2.1 c.2.2.1 c.2.2.2
              (rowGroupRowCount c.1 c.2.1 c.2.2.1 c.2.2.2) 0 accRev
        | none => accRev := by
  simp only [rgStepTok, rgCols]
  cases rd rg 0 <;> cases rd rg 1 <;> cases rd rg 2 <;> cases rd rg 3 <;> rfl

def rgStepLimitedTok (rd : ColumnReader) (bs bp bo bg : Option String)
    (rg : Nat) (accRev : List QpRowTok) (accCount limit : Nat) :
    List QpRowTok × Nat × Bool :=
  match rgCols rd rg with
  | some c =>
      filterLimitedTok bs bp bo bg c.1 c.2.1 c.2.2.1 c.2.2.2
        (rowGroupRowCount c.1 c.2.1 c.2.2.1 c.2.2.2) 0 accRev accCount limit
  | none => (accRev, accCount, false)

def walkCandidatesLimitedTok (rd : ColumnReader) (bs bp bo bg : Option String) :
    List Nat → List QpRowTok → Nat → Nat → List QpRowTok
  | [], accRev, _, _ => accRev
  | rg :: rest, accRev, accCount, limit =>
      if accCount ≥ limit then accRev
      else
        let step := rgStepLimitedTok rd bs bp bo bg rg accRev accCount limit
        if step.2.2 then step.1
        else walkCandidatesLimitedTok rd bs bp bo bg rest step.1 step.2.1 limit

theorem rgStepTok_append (rd : ColumnReader) (bs bp bo bg : Option String)
    (rg : Nat) (accRev : List QpRowTok) :
    rgStepTok rd bs bp bo bg rg accRev
      = rgStepTok rd bs bp bo bg rg [] ++ accRev := by
  rw [rgStepTok_cols, rgStepTok_cols]
  cases rgCols rd rg with
  | none => simp
  | some c =>
      exact filterTokSeq_append bs bp bo bg c.1 c.2.1 c.2.2.1 c.2.2.2
        (rowGroupRowCount c.1 c.2.1 c.2.2.1 c.2.2.2)
        (rowGroupRowCount c.1 c.2.1 c.2.2.1 c.2.2.2) 0 accRev (by omega)

theorem walkCandidatesTok_append (rd : ColumnReader)
    (bs bp bo bg : Option String) :
    ∀ (cands : List Nat) (accRev : List QpRowTok),
      walkCandidatesTok rd bs bp bo bg cands accRev
        = walkCandidatesTok rd bs bp bo bg cands [] ++ accRev
  | [], accRev => by simp [walkCandidatesTok]
  | rg :: rest, accRev => by
      rw [walkCandidatesTok, walkCandidatesTok,
          rgStepTok_append rd bs bp bo bg rg accRev,
          walkCandidatesTok_append rd bs bp bo bg rest
            (rgStepTok rd bs bp bo bg rg [] ++ accRev),
          walkCandidatesTok_append rd bs bp bo bg rest
            (rgStepTok rd bs bp bo bg rg [])]
      simp

theorem rgStepLimitedTok_prefix (rd : ColumnReader)
    (bs bp bo bg : Option String) (rg : Nat) (accRev : List QpRowTok)
    (limit : Nat) (hle : accRev.length ≤ limit) :
    (rgStepLimitedTok rd bs bp bo bg rg accRev accRev.length limit).1.reverse
      = accRev.reverse
          ++ (rgStepTok rd bs bp bo bg rg []).reverse.take
               (limit - accRev.length) := by
  rw [rgStepTok_cols]
  simp only [rgStepLimitedTok]
  cases rgCols rd rg with
  | none => simp
  | some c =>
      exact filterLimitedTok_prefix bs bp bo bg c.1 c.2.1 c.2.2.1 c.2.2.2
        (rowGroupRowCount c.1 c.2.1 c.2.2.1 c.2.2.2)
        (rowGroupRowCount c.1 c.2.1 c.2.2.1 c.2.2.2) 0 accRev limit
        (by omega) hle

theorem rgStepLimitedTok_count (rd : ColumnReader)
    (bs bp bo bg : Option String) (rg : Nat) (accRev : List QpRowTok)
    (limit : Nat) :
    (rgStepLimitedTok rd bs bp bo bg rg accRev accRev.length limit).2.1
      = (rgStepLimitedTok rd bs bp bo bg rg accRev accRev.length
          limit).1.length := by
  simp only [rgStepLimitedTok]
  cases rgCols rd rg with
  | none => rfl
  | some c =>
      exact filterLimitedTok_count bs bp bo bg c.1 c.2.1 c.2.2.1 c.2.2.2
        (rowGroupRowCount c.1 c.2.1 c.2.2.1 c.2.2.2)
        (rowGroupRowCount c.1 c.2.1 c.2.2.1 c.2.2.2) 0 accRev limit (by omega)

theorem rgStepLimitedTok_flag (rd : ColumnReader) (bs bp bo bg : Option String)
    (rg : Nat) (accRev : List QpRowTok) (accCount limit : Nat)
    (hc : ¬ accCount ≥ limit) :
    ((rgStepLimitedTok rd bs bp bo bg rg accRev accCount limit).2.2 = true)
      ↔ ((rgStepLimitedTok rd bs bp bo bg rg accRev accCount limit).2.1
            ≥ limit) := by
  simp only [rgStepLimitedTok]
  cases rgCols rd rg with
  | none => simp [hc]
  | some c =>
      exact filterLimitedTok_flag bs bp bo bg c.1 c.2.1 c.2.2.1 c.2.2.2
        (rowGroupRowCount c.1 c.2.1 c.2.2.1 c.2.2.2)
        (rowGroupRowCount c.1 c.2.1 c.2.2.1 c.2.2.2) 0 accRev accCount limit
        (by omega)

/-- **`limitAgrees` for the COTTAS backend.** A `LIMIT`-bearing scan
returns exactly the prefix the unbounded scan would have returned:
never a row the unbounded scan would not return, and never fewer than
`limit` of them when the unbounded scan has that many. -/
theorem walkCandidatesLimitedTok_prefix (rd : ColumnReader)
    (bs bp bo bg : Option String) :
    ∀ (cands : List Nat) (accRev : List QpRowTok) (limit : Nat),
      accRev.length ≤ limit →
      (walkCandidatesLimitedTok rd bs bp bo bg cands accRev accRev.length
        limit).reverse
        = accRev.reverse
            ++ (walkCandidatesTok rd bs bp bo bg cands []).reverse.take
                 (limit - accRev.length)
  | [], accRev, limit, hle => by
      simp [walkCandidatesLimitedTok, walkCandidatesTok]
  | rg :: rest, accRev, limit, hle => by
      rw [walkCandidatesLimitedTok, walkCandidatesTok]
      by_cases hc : accRev.length ≥ limit
      · have heq : limit - accRev.length = 0 := by omega
        simp [hc, heq]
      · simp only [hc, ge_iff_le, if_neg, not_false_eq_true]
        have hstep := rgStepLimitedTok_prefix rd bs bp bo bg rg accRev limit hle
        have hcnt := rgStepLimitedTok_count rd bs bp bo bg rg accRev limit
        have hlen := congrArg List.length hstep
        simp only [List.length_reverse, List.length_append, List.length_take]
          at hlen
        rw [walkCandidatesTok_append rd bs bp bo bg rest
              (rgStepTok rd bs bp bo bg rg []), List.reverse_append,
            List.take_append]
        have hiff := rgStepLimitedTok_flag rd bs bp bo bg rg accRev
          accRev.length limit hc
        by_cases hhit : (rgStepLimitedTok rd bs bp bo bg rg accRev accRev.length
            limit).2.2 = true
        · simp only [hhit, if_pos]
          have hge := hiff.mp hhit
          rw [hcnt] at hge
          have hz : limit - accRev.length
              - (rgStepTok rd bs bp bo bg rg []).reverse.length = 0 := by
            simp; omega
          rw [hstep, hz]
          simp
        · have hfalse : (rgStepLimitedTok rd bs bp bo bg rg accRev
              accRev.length limit).2.2 = false := by
            simpa using hhit
          simp only [hfalse, if_neg, Bool.false_eq_true, not_false_eq_true]
          have hlt : ¬ (rgStepLimitedTok rd bs bp bo bg rg accRev accRev.length
              limit).2.1 ≥ limit := fun hx => hhit (hiff.mpr hx)
          rw [hcnt] at hlt
          have hsmall : (rgStepTok rd bs bp bo bg rg []).length
              < limit - accRev.length := by omega
          rw [hcnt, walkCandidatesLimitedTok_prefix rd bs bp bo bg rest
                _ limit (by omega), hstep,
              List.take_of_length_le (by simp; omega), List.append_assoc]
          congr 2
          simp
          omega

/-! ## Build-time checks -/

private def lS : Column := #[some "<a:1>", some "<a:2>", some "<a:3>"]
private def lP : Column := #[some "<p:1>", some "<p:1>", some "<p:1>"]
private def lO : Column := #[some "<o:1>", some "<o:2>", some "<o:3>"]
private def lG : Column := #[some "DEFAULT", some "DEFAULT", some "DEFAULT"]

private def rdL : ColumnReader := fun rg col =>
  if rg < 2 then
    match col with
    | 0 => some lS
    | 1 => some lP
    | 2 => some lO
    | 3 => some lG
    | _ => none
  else none

/-! A limit below the row-group size stops inside the first row group. -/
#guard (filterLimitedTok none none none none lS lP lO lG 3 0 [] 0 2).1.length == 2
#guard (filterLimitedTok none none none none lS lP lO lG 3 0 [] 0 2).2.1 == 2
#guard (filterLimitedTok none none none none lS lP lO lG 3 0 [] 0 2).2.2 == true

/-! A limit above it takes the whole row group and does NOT set the
flag. -/
#guard (filterLimitedTok none none none none lS lP lO lG 3 0 [] 0 9).1.length == 3
#guard (filterLimitedTok none none none none lS lP lO lG 3 0 [] 0 9).2.2 == false

/-! Zero rows wanted, zero rows read. -/
#guard (filterLimitedTok none none none none lS lP lO lG 3 0 [] 0 0).1
        == ([] : List QpRowTok)

/-! The prefix property, on the flipped list: the FIRST two rows in row
order, not the last two. -/
#guard ((filterLimitedTok none none none none lS lP lO lG 3 0 [] 0 2).1.reverse.map
          (fun r => r.o)) == ["<o:1>", "<o:2>"]

/-! Across row groups: the limit is reached inside the second one. -/
#guard (walkCandidatesLimitedTok rdL none none none none [0, 1] [] 0 5).length == 5
#guard (walkCandidatesLimitedTok rdL none none none none [0, 1] [] 0 9).length == 6
#guard (walkCandidatesLimitedTok rdL none none none none [0, 1] [] 0 5).reverse
        == (walkCandidatesTok rdL none none none none [0, 1] []).reverse.take 5

/-! ## Axiom audit -/

#print axioms filterTokSeq_append
#print axioms filterLimitedTok_count
#print axioms filterLimitedTok_flag
#print axioms filterLimitedTok_end
#print axioms filterLimitedTok_prefix_start
#print axioms walkCandidatesLimitedTok_prefix

end L4Factoidal.Cottas.OnDiskStore
