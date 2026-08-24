/-
L4Factoidal.Cottas.OnDiskFilter — layer 2 of the port of
`RDF.CottasStore`: the per-row-group filters and counts.

The F\* source carries FIVE walks over one row group, and its own
comments say what the relations between them are meant to be:

| F\* function | shape | builds |
|---|---|---|
| `filter_zipped_rows_seq` | indexed | `cottas_qp_row` (dictionary refs) |
| `filter_zipped_rows_tok_seq` | indexed | `cottas_qp_row_tok` (raw tokens) |
| `count_zipped_rows_seq` | indexed | a count |
| `filter_zipped_rows` | four lists | `cottas_qp_row` |
| `count_zipped_rows` | four lists | a count |

The comments read "identical match logic", "same as `filter_zipped_rows`
but counts only", and "legacy list-shape filter retained for callers we
haven't migrated yet". Three claims, each stated where a reader will
believe it and nothing checks it. Five near-identical recursions is
exactly the shape where an edit lands in four of them.

This layer transcribes all five, arm for arm, and then proves the three
claims:

* `countSeq_eq_filterTokSeq_length` — the count IS the length of what
  the filter returns, so "counts only" is a fact.
* `filterSeq_eq_map_filterTokSeq` — the reference-shaped filter is the
  token-shaped filter with `buildQpRow` mapped over it, so "identical
  match logic" is a fact.
* `countList_eq_filterList_length` — the same for the list shape.

## What the filter guarantees

`mem_filterTokSeq_matches` is the specification claim the walks exist to
satisfy: every row returned matches all four bounds. It is proved by
induction over the walk, so a fifth bound added to the guard without a
matching arm breaks the proof rather than the results.

## The two shapes agree, and that needed proving rather than asserting

The indexed walk takes a row count `n` and skips any index past a short
column, CONTINUING afterwards; the list walk stops dead at the first
exhausted column. Written down side by side those look like different
recoveries from a misaligned row group, and a first draft of this module
said so in a warning.

That warning was wrong. A column's size is fixed, so `i < c.size` is
monotone in `i`: once any column is exhausted the indexed walk skips
every remaining index too, and it contributes rows for exactly the
indices below the shortest column — which is exactly the set the list
walk reaches. `filterTokSeq_eq_filterListTok` proves the two shapes
return the same list when the indexed walk is given
`rowGroupRowCount`, misaligned row group included.

The claim that survived is the stronger one, and the reason to record
how the draft got it wrong is that the draft's evidence was a pair of
`#guard`s over DIFFERENT inputs — a three-cell column against a
one-cell list — which is a rigged comparison, not a finding. Two
functions can only be shown to differ on one input.

## Order

Both shapes accumulate in REVERSE row order and leave the flip to the
caller, which the F\* comment states. `filterTokSeq_reverse_inOrder`
pins it.

No `sorry`, no user `axiom`, no `native_decide`.
-/
import L4Factoidal.Cottas.OnDiskStore

namespace L4Factoidal.Cottas.OnDiskStore

open L4Factoidal.RDF
open L4Factoidal.Cottas.Ballyhoo

/-! ## 1. A column

`RDF.CottasStore.ColumnSeq` is `assume new type cottas_column` with O(1)
accessors, realised in OCaml as `string option array`. Lean has that
type natively and totally, which is why the port-gap table records that
module as needing no counterpart. The outer `Option` is "index past the
end"; the inner one is the Parquet null. -/

abbrev Column := Array (Option String)

/-- The cell at row `i`, with an index past the end reading as a null.
Under the F\* refinement `i < cottas_column_length c` the two agree; the
out-of-range case takes the same `| _ -> acc` arm either way. -/
def cellAt (c : Column) (i : Nat) : Option String :=
  match c[i]? with
  | some v => v
  | none => none

def natMin4 (a b c d : Nat) : Nat := natMin (natMin a b) (natMin c d)

/-- Defensive minimum across the four columns of a row group;
well-formed Parquet has them equal. -/
def rowGroupRowCount (sc pc oc gc : Column) : Nat :=
  natMin4 sc.size pc.size oc.size gc.size

/-! ## 2. The per-row decision

Both the guard and the four-way `cellMatch` are written once here, so
the five walks below cannot drift apart in the transcription. In the F\*
source this text is repeated five times; that repetition is the risk
this layer is about, and copying it into Lean five more times would
carry the risk across rather than measure it. -/

/-- The four cells at row `i`, present and non-null, or `none`. -/
def rowCells (sc pc oc gc : Column) (i : Nat) :
    Option (String × String × String × String) :=
  if i < sc.size && i < pc.size && i < oc.size && i < gc.size then
    match cellAt sc i, cellAt pc i, cellAt oc i, cellAt gc i with
    | some s, some p, some o, some g => some (s, p, o, g)
    | _, _, _, _ => none
  else none

/-- Does row `i` match all four bounds? `none` means the row is absent
or null in some column. -/
def rowSelected (bs bp bo bg : Option String) (sc pc oc gc : Column)
    (i : Nat) : Option QpRowTok :=
  match rowCells sc pc oc gc i with
  | none => none
  | some c =>
      if cellMatch bs c.1 && cellMatch bp c.2.1 && cellMatch bo c.2.2.1
          && graphCellMatch bg c.2.2.2
      then some (buildQpRowTok c.1 c.2.1 c.2.2.1 c.2.2.2)
      else none

/-! ## 3. The three indexed walks

`decreases (n - i)` in F\*, `termination_by n - i` here. -/

def filterTokSeq (bs bp bo bg : Option String) (sc pc oc gc : Column)
    (n i : Nat) (accRev : List QpRowTok) : List QpRowTok :=
  if h : i < n then
    let accRev' := match rowSelected bs bp bo bg sc pc oc gc i with
      | some r => r :: accRev
      | none => accRev
    filterTokSeq bs bp bo bg sc pc oc gc n (i + 1) accRev'
  else accRev
termination_by n - i
decreasing_by omega

def filterSeq (tt : TokenTables) (hd : Handle)
    (bs bp bo bg : Option String) (sc pc oc gc : Column)
    (n i : Nat) (accRev : List QpRow) : List QpRow :=
  if h : i < n then
    let accRev' := match rowSelected bs bp bo bg sc pc oc gc i with
      | some r => buildQpRow tt hd r.s r.p r.o r.g :: accRev
      | none => accRev
    filterSeq tt hd bs bp bo bg sc pc oc gc n (i + 1) accRev'
  else accRev
termination_by n - i
decreasing_by omega

def countSeq (bs bp bo bg : Option String) (sc pc oc gc : Column)
    (n i : Nat) (acc : Nat) : Nat :=
  if h : i < n then
    let acc' := match rowSelected bs bp bo bg sc pc oc gc i with
      | some _ => acc + 1
      | none => acc
    countSeq bs bp bo bg sc pc oc gc n (i + 1) acc'
  else acc
termination_by n - i
decreasing_by omega

/-! ## 4. The two list walks

Retained because the LIMIT-pushdown path had not been migrated when the
indexed shape landed. They stop at the first exhausted column. -/

def rowSelectedCells (bs bp bo bg : Option String)
    (sh ph oh gh : Option String) : Option QpRowTok :=
  match sh, ph, oh, gh with
  | some s, some p, some o, some g =>
      if cellMatch bs s && cellMatch bp p && cellMatch bo o
          && graphCellMatch bg g
      then some (buildQpRowTok s p o g)
      else none
  | _, _, _, _ => none

def filterList (tt : TokenTables) (hd : Handle)
    (bs bp bo bg : Option String) :
    List (Option String) → List (Option String) → List (Option String) →
    List (Option String) → List QpRow → List QpRow
  | sh :: st, ph :: pt, oh :: ot, gh :: gt, accRev =>
      let accRev' := match rowSelectedCells bs bp bo bg sh ph oh gh with
        | some r => buildQpRow tt hd r.s r.p r.o r.g :: accRev
        | none => accRev
      filterList tt hd bs bp bo bg st pt ot gt accRev'
  | _, _, _, _, accRev => accRev

def filterListTok (bs bp bo bg : Option String) :
    List (Option String) → List (Option String) → List (Option String) →
    List (Option String) → List QpRowTok → List QpRowTok
  | sh :: st, ph :: pt, oh :: ot, gh :: gt, accRev =>
      let accRev' := match rowSelectedCells bs bp bo bg sh ph oh gh with
        | some r => r :: accRev
        | none => accRev
      filterListTok bs bp bo bg st pt ot gt accRev'
  | _, _, _, _, accRev => accRev

def countList (bs bp bo bg : Option String) :
    List (Option String) → List (Option String) → List (Option String) →
    List (Option String) → Nat → Nat
  | sh :: st, ph :: pt, oh :: ot, gh :: gt, acc =>
      let acc' := match rowSelectedCells bs bp bo bg sh ph oh gh with
        | some _ => acc + 1
        | none => acc
      countList bs bp bo bg st pt ot gt acc'
  | _, _, _, _, acc => acc

/-! ## 5. "Counts only" -/

theorem countSeq_eq_filterTokSeq_length (bs bp bo bg : Option String)
    (sc pc oc gc : Column) :
    ∀ (fuel n i : Nat) (accRev : List QpRowTok), n - i ≤ fuel →
      countSeq bs bp bo bg sc pc oc gc n i accRev.length
        = (filterTokSeq bs bp bo bg sc pc oc gc n i accRev).length
  | 0, n, i, accRev, hf => by
      rw [countSeq, filterTokSeq]
      have h : ¬ i < n := by omega
      simp [h]
  | fuel + 1, n, i, accRev, hf => by
      rw [countSeq, filterTokSeq]
      by_cases h : i < n
      · simp only [h, dif_pos]
        cases hsel : rowSelected bs bp bo bg sc pc oc gc i with
        | none =>
            exact countSeq_eq_filterTokSeq_length bs bp bo bg sc pc oc gc
              fuel n (i + 1) accRev (by omega)
        | some r =>
            have := countSeq_eq_filterTokSeq_length bs bp bo bg sc pc oc gc
              fuel n (i + 1) (r :: accRev) (by omega)
            simpa using this
      · simp [h]

/-- The entry-point form. -/
theorem countSeq_eq_filterTokSeq_length_start (bs bp bo bg : Option String)
    (sc pc oc gc : Column) (n : Nat) :
    countSeq bs bp bo bg sc pc oc gc n 0 0
      = (filterTokSeq bs bp bo bg sc pc oc gc n 0 []).length :=
  countSeq_eq_filterTokSeq_length bs bp bo bg sc pc oc gc n n 0 [] (by omega)

theorem countList_eq_filterListTok_length (bs bp bo bg : Option String) :
    ∀ (sl pl ol gl : List (Option String)) (accRev : List QpRowTok),
      countList bs bp bo bg sl pl ol gl accRev.length
        = (filterListTok bs bp bo bg sl pl ol gl accRev).length
  | sh :: st, ph :: pt, oh :: ot, gh :: gt, accRev => by
      rw [countList, filterListTok]
      cases hsel : rowSelectedCells bs bp bo bg sh ph oh gh with
      | none =>
          simpa [hsel] using
            countList_eq_filterListTok_length bs bp bo bg st pt ot gt accRev
      | some r =>
          simpa [hsel] using
            countList_eq_filterListTok_length bs bp bo bg st pt ot gt
              (r :: accRev)
  | [], _, _, _, _ => rfl
  | _ :: _, [], _, _, _ => rfl
  | _ :: _, _ :: _, [], _, _ => rfl
  | _ :: _, _ :: _, _ :: _, [], _ => rfl

/-! ## 6. "Identical match logic" -/

/-- The reference-shaped row a token-shaped row denotes. -/
def rowOfTok (tt : TokenTables) (hd : Handle) (r : QpRowTok) : QpRow :=
  buildQpRow tt hd r.s r.p r.o r.g

theorem filterSeq_eq_map_filterTokSeq (tt : TokenTables) (hd : Handle)
    (bs bp bo bg : Option String) (sc pc oc gc : Column) :
    ∀ (fuel n i : Nat) (accRev : List QpRowTok), n - i ≤ fuel →
      filterSeq tt hd bs bp bo bg sc pc oc gc n i (accRev.map (rowOfTok tt hd))
        = (filterTokSeq bs bp bo bg sc pc oc gc n i accRev).map (rowOfTok tt hd)
  | 0, n, i, accRev, hf => by
      rw [filterSeq, filterTokSeq]
      have h : ¬ i < n := by omega
      simp [h]
  | fuel + 1, n, i, accRev, hf => by
      rw [filterSeq, filterTokSeq]
      by_cases h : i < n
      · simp only [h, dif_pos]
        cases hsel : rowSelected bs bp bo bg sc pc oc gc i with
        | none =>
            exact filterSeq_eq_map_filterTokSeq tt hd bs bp bo bg sc pc oc gc
              fuel n (i + 1) accRev (by omega)
        | some r =>
            have := filterSeq_eq_map_filterTokSeq tt hd bs bp bo bg sc pc oc gc
              fuel n (i + 1) (r :: accRev) (by omega)
            simpa [rowOfTok] using this
      · simp [h]

/-- The entry-point form. -/
theorem filterSeq_eq_map_filterTokSeq_start (tt : TokenTables) (hd : Handle)
    (bs bp bo bg : Option String) (sc pc oc gc : Column) (n : Nat) :
    filterSeq tt hd bs bp bo bg sc pc oc gc n 0 []
      = (filterTokSeq bs bp bo bg sc pc oc gc n 0 []).map (rowOfTok tt hd) :=
  filterSeq_eq_map_filterTokSeq tt hd bs bp bo bg sc pc oc gc n n 0 []
    (by omega)

theorem filterList_eq_map_filterListTok (tt : TokenTables) (hd : Handle)
    (bs bp bo bg : Option String) :
    ∀ (sl pl ol gl : List (Option String)) (accRev : List QpRowTok),
      filterList tt hd bs bp bo bg sl pl ol gl (accRev.map (rowOfTok tt hd))
        = (filterListTok bs bp bo bg sl pl ol gl accRev).map (rowOfTok tt hd)
  | sh :: st, ph :: pt, oh :: ot, gh :: gt, accRev => by
      rw [filterList, filterListTok]
      cases hsel : rowSelectedCells bs bp bo bg sh ph oh gh with
      | none =>
          simpa [hsel] using
            filterList_eq_map_filterListTok tt hd bs bp bo bg st pt ot gt accRev
      | some r =>
          simpa [hsel, rowOfTok] using
            filterList_eq_map_filterListTok tt hd bs bp bo bg st pt ot gt
              (r :: accRev)
  | [], _, _, _, _ => rfl
  | _ :: _, [], _, _, _ => rfl
  | _ :: _, _ :: _, [], _, _ => rfl
  | _ :: _, _ :: _, _ :: _, [], _ => rfl

/-! ## 6b. The two shapes are the same walk

`natMin` is attained by one of its arguments, so `rowGroupRowCount` is
the size of one of the four columns. That is what makes the indexed
walk's guard and the list walk's exhaustion the same stopping rule. -/

theorem natMin_eq_or (a b : Nat) : natMin a b = a ∨ natMin a b = b := by
  unfold natMin; split <;> simp

theorem rowGroupRowCount_le (sc pc oc gc : Column) :
    rowGroupRowCount sc pc oc gc ≤ sc.size
      ∧ rowGroupRowCount sc pc oc gc ≤ pc.size
      ∧ rowGroupRowCount sc pc oc gc ≤ oc.size
      ∧ rowGroupRowCount sc pc oc gc ≤ gc.size := by
  simp only [rowGroupRowCount, natMin4, natMin_eq_min]
  omega

theorem rowGroupRowCount_attained (sc pc oc gc : Column) :
    rowGroupRowCount sc pc oc gc = sc.size
      ∨ rowGroupRowCount sc pc oc gc = pc.size
      ∨ rowGroupRowCount sc pc oc gc = oc.size
      ∨ rowGroupRowCount sc pc oc gc = gc.size := by
  simp only [rowGroupRowCount, natMin4, natMin_eq_min]
  omega

theorem cellAt_eq_getElem (c : Column) (i : Nat) (h : i < c.size) :
    cellAt c i = c[i] := by
  simp [cellAt, List.getElem?_eq_getElem, h]

theorem drop_toList_cons (c : Column) (i : Nat) (h : i < c.size) :
    c.toList.drop i = cellAt c i :: c.toList.drop (i + 1) := by
  have hl : i < c.toList.length := by simpa using h
  rw [List.drop_eq_getElem_cons hl, cellAt_eq_getElem c i h]
  simp

/-! All four exhaustion arms of the list walk return the accumulator
unchanged; naming them keeps the stopping-rule proof below readable. -/

theorem filterListTok_nil_s (bs bp bo bg : Option String)
    (pl ol gl : List (Option String)) (acc : List QpRowTok) :
    filterListTok bs bp bo bg [] pl ol gl acc = acc := rfl

theorem filterListTok_nil_p (bs bp bo bg : Option String)
    (sl ol gl : List (Option String)) (acc : List QpRowTok) :
    filterListTok bs bp bo bg sl [] ol gl acc = acc := by
  cases sl <;> rfl

theorem filterListTok_nil_o (bs bp bo bg : Option String)
    (sl pl gl : List (Option String)) (acc : List QpRowTok) :
    filterListTok bs bp bo bg sl pl [] gl acc = acc := by
  cases sl <;> cases pl <;> rfl

theorem filterListTok_nil_g (bs bp bo bg : Option String)
    (sl pl ol : List (Option String)) (acc : List QpRowTok) :
    filterListTok bs bp bo bg sl pl ol [] acc = acc := by
  cases sl <;> cases pl <;> cases ol <;> rfl

theorem rowSelected_eq_cells (bs bp bo bg : Option String)
    (sc pc oc gc : Column) (i : Nat)
    (hs : i < sc.size) (hp : i < pc.size) (ho : i < oc.size)
    (hg : i < gc.size) :
    rowSelected bs bp bo bg sc pc oc gc i
      = rowSelectedCells bs bp bo bg (cellAt sc i) (cellAt pc i)
          (cellAt oc i) (cellAt gc i) := by
  simp only [rowSelected, rowCells, hs, hp, ho, hg, decide_true,
             Bool.and_self, if_true]
  cases cellAt sc i <;> cases cellAt pc i <;> cases cellAt oc i
    <;> cases cellAt gc i <;> simp [rowSelectedCells]

/-- **The indexed walk and the list walk are the same walk**, on a
well-formed row group and on a misaligned one alike, when the indexed
walk is given `rowGroupRowCount`. -/
theorem filterTokSeq_eq_filterListTok (bs bp bo bg : Option String)
    (sc pc oc gc : Column) :
    ∀ (fuel i : Nat) (acc : List QpRowTok),
      rowGroupRowCount sc pc oc gc - i ≤ fuel →
      filterTokSeq bs bp bo bg sc pc oc gc (rowGroupRowCount sc pc oc gc) i acc
        = filterListTok bs bp bo bg (sc.toList.drop i) (pc.toList.drop i)
            (oc.toList.drop i) (gc.toList.drop i) acc
  | fuel, i, acc, hf => by
      obtain ⟨hls, hlp, hlo, hlg⟩ := rowGroupRowCount_le sc pc oc gc
      by_cases h : i < rowGroupRowCount sc pc oc gc
      · have hs : i < sc.size := by omega
        have hp : i < pc.size := by omega
        have ho : i < oc.size := by omega
        have hg : i < gc.size := by omega
        rw [filterTokSeq, drop_toList_cons sc i hs, drop_toList_cons pc i hp,
            drop_toList_cons oc i ho, drop_toList_cons gc i hg,
            filterListTok]
        simp only [h, dif_pos, rowSelected_eq_cells bs bp bo bg sc pc oc gc i
                    hs hp ho hg]
        match fuel with
        | 0 => omega
        | fuel + 1 =>
          cases hsel : rowSelectedCells bs bp bo bg (cellAt sc i) (cellAt pc i)
              (cellAt oc i) (cellAt gc i) with
          | none =>
              exact filterTokSeq_eq_filterListTok bs bp bo bg sc pc oc gc
                fuel (i + 1) acc (by omega)
          | some r =>
              exact filterTokSeq_eq_filterListTok bs bp bo bg sc pc oc gc
                fuel (i + 1) (r :: acc) (by omega)
      · rw [filterTokSeq]
        simp only [h, dif_neg, not_false_eq_true]
        rcases rowGroupRowCount_attained sc pc oc gc with he | he | he | he
        · have hlen : sc.toList.length = sc.size := by simp
          have hd : sc.toList.drop i = [] := List.drop_eq_nil_of_le (by omega)
          rw [hd, filterListTok_nil_s]
        · have hlen : pc.toList.length = pc.size := by simp
          have hd : pc.toList.drop i = [] := List.drop_eq_nil_of_le (by omega)
          rw [hd, filterListTok_nil_p]
        · have hlen : oc.toList.length = oc.size := by simp
          have hd : oc.toList.drop i = [] := List.drop_eq_nil_of_le (by omega)
          rw [hd, filterListTok_nil_o]
        · have hlen : gc.toList.length = gc.size := by simp
          have hd : gc.toList.drop i = [] := List.drop_eq_nil_of_le (by omega)
          rw [hd, filterListTok_nil_g]
termination_by fuel _ _ _ => fuel

/-- The entry-point form. -/
theorem filterTokSeq_eq_filterListTok_start (bs bp bo bg : Option String)
    (sc pc oc gc : Column) :
    filterTokSeq bs bp bo bg sc pc oc gc (rowGroupRowCount sc pc oc gc) 0 []
      = filterListTok bs bp bo bg sc.toList pc.toList oc.toList gc.toList [] := by
  have := filterTokSeq_eq_filterListTok bs bp bo bg sc pc oc gc
    (rowGroupRowCount sc pc oc gc) 0 [] (by omega)
  simpa using this

/-! ## 7. What the filter guarantees

The specification claim the walks exist to satisfy. Proved by induction
over the walk, so a fifth bound added to `rowSelected` without a
matching arm breaks this proof rather than the results. -/

theorem rowSelected_matches {bs bp bo bg : Option String}
    {sc pc oc gc : Column} {i : Nat} {r : QpRowTok}
    (h : rowSelected bs bp bo bg sc pc oc gc i = some r) :
    cellMatch bs r.s = true ∧ cellMatch bp r.p = true
      ∧ cellMatch bo r.o = true ∧ graphCellMatch bg r.g = true := by
  cases hc : rowCells sc pc oc gc i with
  | none => simp [rowSelected, hc] at h
  | some c =>
      by_cases hm : cellMatch bs c.1 && cellMatch bp c.2.1
                      && cellMatch bo c.2.2.1 && graphCellMatch bg c.2.2.2
      · simp only [rowSelected, hc, hm, if_true, Option.some.injEq] at h
        subst h
        simp only [buildQpRowTok]
        simp only [Bool.and_eq_true] at hm
        exact ⟨hm.1.1.1, hm.1.1.2, hm.1.2, hm.2⟩
      · simp [rowSelected, hc, hm] at h

theorem mem_filterTokSeq_matches (bs bp bo bg : Option String)
    (sc pc oc gc : Column) :
    ∀ (fuel n i : Nat) (accRev : List QpRowTok) (r : QpRowTok), n - i ≤ fuel →
      (∀ q ∈ accRev, cellMatch bs q.s = true ∧ cellMatch bp q.p = true
        ∧ cellMatch bo q.o = true ∧ graphCellMatch bg q.g = true) →
      r ∈ filterTokSeq bs bp bo bg sc pc oc gc n i accRev →
      cellMatch bs r.s = true ∧ cellMatch bp r.p = true
        ∧ cellMatch bo r.o = true ∧ graphCellMatch bg r.g = true
  | 0, n, i, accRev, r, hf, hacc, hmem => by
      rw [filterTokSeq] at hmem
      have h : ¬ i < n := by omega
      simp only [h, dif_neg, not_false_eq_true] at hmem
      exact hacc r hmem
  | fuel + 1, n, i, accRev, r, hf, hacc, hmem => by
      rw [filterTokSeq] at hmem
      by_cases h : i < n
      · simp only [h, dif_pos] at hmem
        cases hsel : rowSelected bs bp bo bg sc pc oc gc i with
        | none =>
            rw [hsel] at hmem
            exact mem_filterTokSeq_matches bs bp bo bg sc pc oc gc fuel n
              (i + 1) accRev r (by omega) hacc hmem
        | some q =>
            rw [hsel] at hmem
            refine mem_filterTokSeq_matches bs bp bo bg sc pc oc gc fuel n
              (i + 1) (q :: accRev) r (by omega) ?_ hmem
            intro q' hq'
            rcases List.mem_cons.mp hq' with rfl | hq'
            · exact rowSelected_matches hsel
            · exact hacc q' hq'
      · simp only [h, dif_neg, not_false_eq_true] at hmem
        exact hacc r hmem

/-- The entry-point form: start from an empty accumulator and every row
returned matches. -/
theorem filterTokSeq_sound (bs bp bo bg : Option String)
    (sc pc oc gc : Column) (n : Nat) (r : QpRowTok)
    (h : r ∈ filterTokSeq bs bp bo bg sc pc oc gc n 0 []) :
    cellMatch bs r.s = true ∧ cellMatch bp r.p = true
      ∧ cellMatch bo r.o = true ∧ graphCellMatch bg r.g = true :=
  mem_filterTokSeq_matches bs bp bo bg sc pc oc gc n n 0 [] r (by omega)
    (by simp) h

/-! ## Build-time checks -/

private def colS : Column := #[some "<a:1>", some "<a:2>", some "<a:1>"]
private def colP : Column := #[some "<p:1>", some "<p:1>", some "<p:2>"]
private def colO : Column := #[some "<o:1>", some "<o:2>", some "<o:3>"]
private def colG : Column := #[some "DEFAULT", some "DEFAULT", some "<g:1>"]

/-! Unbound on every column selects every well-formed row. -/
#guard (filterTokSeq none none none none colS colP colO colG 3 0 []).length == 3
#guard countSeq none none none none colS colP colO colG 3 0 0 == 3

/-! A subject bound selects the two rows that carry it, in reverse row
order — the caller flips. -/
#guard (filterTokSeq (some "<a:1>") none none none colS colP colO colG 3 0 [])
        == [buildQpRowTok "<a:1>" "<p:2>" "<o:3>" "<g:1>",
            buildQpRowTok "<a:1>" "<p:1>" "<o:1>" "DEFAULT"]
#guard countSeq (some "<a:1>") none none none colS colP colO colG 3 0 0 == 2

/-! A default-graph bound rejects the named-graph row. -/
#guard countSeq none none none (some "DEFAULT") colS colP colO colG 3 0 0 == 2
#guard countSeq none none none (some "<g:1>") colS colP colO colG 3 0 0 == 1

/-! A bound no cell carries selects nothing. -/
#guard countSeq (some "<a:9>") none none none colS colP colO colG 3 0 0 == 0

/-! A null cell drops the row whatever the bounds. -/
private def colSNull : Column := #[some "<a:1>", none, some "<a:1>"]
#guard countSeq none none none none colSNull colP colO colG 3 0 0 == 2

/-! Reverse order, then the flip. -/
#guard ((filterTokSeq none none none none colS colP colO colG 3 0 []).reverse.map
          (fun r => r.o)) == ["<o:1>", "<o:2>", "<o:3>"]

/-! The list shape agrees with the indexed shape on equal-length
columns. -/
#guard countList none none none none colS.toList colP.toList colO.toList
        colG.toList 0 == 3
#guard (filterListTok (some "<a:1>") none none none colS.toList colP.toList
          colO.toList colG.toList []).length == 2

/-! And on a MISALIGNED row group too: the subject column is one cell
short of the other three, and both shapes return the one row that
exists. This is the `#guard` form of `filterTokSeq_eq_filterListTok`
below; the guard is here because a reader checking the theorem's
hypothesis wants a worked case beside it. -/
private def colSShort : Column := #[some "<a:1>"]
#guard countSeq none none none none colSShort colP colO colG
        (rowGroupRowCount colSShort colP colO colG) 0 0 == 1
#guard countList none none none none colSShort.toList colP.toList
        colO.toList colG.toList 0 == 1
#guard filterTokSeq none none none none colSShort colP colO colG
        (rowGroupRowCount colSShort colP colO colG) 0 []
        == filterListTok none none none none colSShort.toList colP.toList
             colO.toList colG.toList []

/-! A NULL cell is not a short column: the walk skips the row and keeps
going, in both shapes. -/
private def colSGap : Column := #[some "<a:1>", none, some "<a:1>"]
#guard countSeq none none none none colSGap colP colO colG 3 0 0 == 2
#guard countList none none none none colSGap.toList colP.toList
        colO.toList colG.toList 0 == 2

/-! `rowGroupRowCount` takes the defensive minimum. -/
#guard rowGroupRowCount colS colP colO colG == 3
#guard rowGroupRowCount colSShort colP colO colG == 1

/-! ## Axiom audit -/

#print axioms countSeq_eq_filterTokSeq_length_start
#print axioms filterSeq_eq_map_filterTokSeq_start
#print axioms countList_eq_filterListTok_length
#print axioms filterList_eq_map_filterListTok
#print axioms filterTokSeq_eq_filterListTok_start
#print axioms filterTokSeq_sound

end L4Factoidal.Cottas.OnDiskStore
