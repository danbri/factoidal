/-
L4Factoidal.Cottas.OnDiskWalk — layer 3 of the port of
`RDF.CottasStore`: the walks over row groups.

Layer 2 filtered ONE row group. This layer visits many, and the F\*
source has two ways of choosing which:

* a contiguous RANGE `[rg_index, rg_count)` driven by fuel — the
  unpruned scan;
* an explicit LIST of candidate row-group indices — the pruned scan,
  whose list comes from `plan_candidate_rgs`.

`plan_candidate_rgs` returns `all_rgs rg_count` when no bound prunes
anything, and the F\* source treats that as obviously equivalent to the
range walk. It is the assumption the whole pruning design rests on: if
the two walks answered differently, turning pruning on would change
results rather than only time. `walkRange_eq_walkCandidates` proves it,
via `allRgs_eq_range`.

## The column read, as a parameter

Reading a row group's four columns is I/O — `pcache_decode_in_row_group`
and its global and table-indexed siblings, all `assume val` underneath.
`ColumnReader` is that read taken as an argument: given a row-group
index and a column index, either the decoded column or `none`. The F\*
source's own comment says a decoder error on a row group is "skipped
(silently empty)", and `rgStepTok` transcribes that: any of the four
columns failing to decode drops the whole row group and the walk
continues.

⚠️ That is a real risk the port carries across rather than fixes: a
corrupt row group and an empty row group produce the same answer, and
no caller can tell them apart. It is stated here so the next reader
meets it in the type rather than in a query that quietly returns too
few rows. Filed as
<https://github.com/danbri/factoidal/issues/571>.

## Fuel

The F\* range walk takes `fuel` alongside `rg_count` and stops when
either runs out, which makes its `decreases` clause trivial. Lean does
not need the fuel to terminate — `termination_by fuel` accepts it, but
so would a measure on `rgCount - rgIndex`. It is transcribed because it
is OBSERVABLE: a caller passing fuel smaller than the row-group count
gets a partial scan with no error. `walkRangeTok_fuel_truncates` pins
that, so the fuel argument cannot be mistaken for decoration.

No `sorry`, no user `axiom`, no `native_decide`.
-/
import L4Factoidal.Cottas.OnDiskFilter

namespace L4Factoidal.Cottas.OnDiskStore

open L4Factoidal.RDF
open L4Factoidal.Cottas.Ballyhoo

/-! ## 1. The reader -/

/-- Decode one column of one row group: `rd rgIndex colIndex`. Columns
are 0 = subject, 1 = predicate, 2 = object, 3 = graph, per
`docs/cottas-format-v1.md`. `none` is a decode failure OR a row group
that does not exist; the walks cannot distinguish them. -/
abbrev ColumnReader := Nat → Nat → Option Column

/-! ## 2. One row group

Written once, so the eight walk variants below cannot drift apart. -/

def rgStepTok (rd : ColumnReader) (bs bp bo bg : Option String)
    (rg : Nat) (accRev : List QpRowTok) : List QpRowTok :=
  match rd rg 0, rd rg 1, rd rg 2, rd rg 3 with
  | some sc, some pc, some oc, some gc =>
      filterTokSeq bs bp bo bg sc pc oc gc (rowGroupRowCount sc pc oc gc) 0
        accRev
  | _, _, _, _ => accRev

def rgStepCount (rd : ColumnReader) (bs bp bo bg : Option String)
    (rg : Nat) (acc : Nat) : Nat :=
  match rd rg 0, rd rg 1, rd rg 2, rd rg 3 with
  | some sc, some pc, some oc, some gc =>
      countSeq bs bp bo bg sc pc oc gc (rowGroupRowCount sc pc oc gc) 0 acc
  | _, _, _, _ => acc

theorem rgStepCount_eq_length (rd : ColumnReader) (bs bp bo bg : Option String)
    (rg : Nat) (accRev : List QpRowTok) :
    rgStepCount rd bs bp bo bg rg accRev.length
      = (rgStepTok rd bs bp bo bg rg accRev).length := by
  simp only [rgStepCount, rgStepTok]
  cases rd rg 0 <;> cases rd rg 1 <;> cases rd rg 2 <;> cases rd rg 3
    <;> try rfl
  rename_i sc pc oc gc
  exact countSeq_eq_filterTokSeq_length bs bp bo bg sc pc oc gc
    (rowGroupRowCount sc pc oc gc) (rowGroupRowCount sc pc oc gc) 0 accRev
    (by omega)

/-! ## 3. The range walk -/

def walkRangeTok (rd : ColumnReader) (bs bp bo bg : Option String)
    (rgIndex rgCount fuel : Nat) (accRev : List QpRowTok) : List QpRowTok :=
  match fuel with
  | 0 => accRev
  | f + 1 =>
      if rgIndex ≥ rgCount then accRev
      else
        walkRangeTok rd bs bp bo bg (rgIndex + 1) rgCount f
          (rgStepTok rd bs bp bo bg rgIndex accRev)

def walkRangeCount (rd : ColumnReader) (bs bp bo bg : Option String)
    (rgIndex rgCount fuel : Nat) (acc : Nat) : Nat :=
  match fuel with
  | 0 => acc
  | f + 1 =>
      if rgIndex ≥ rgCount then acc
      else
        walkRangeCount rd bs bp bo bg (rgIndex + 1) rgCount f
          (rgStepCount rd bs bp bo bg rgIndex acc)

/-! ## 4. The candidate walk -/

def walkCandidatesTok (rd : ColumnReader) (bs bp bo bg : Option String) :
    List Nat → List QpRowTok → List QpRowTok
  | [], accRev => accRev
  | rg :: rest, accRev =>
      walkCandidatesTok rd bs bp bo bg rest (rgStepTok rd bs bp bo bg rg accRev)

def walkCandidatesCount (rd : ColumnReader) (bs bp bo bg : Option String) :
    List Nat → Nat → Nat
  | [], acc => acc
  | rg :: rest, acc =>
      walkCandidatesCount rd bs bp bo bg rest (rgStepCount rd bs bp bo bg rg acc)

/-! ## 5. Every row group

Port of `all_rgs_loop` / `all_rgs`: count up, prepending, then reverse. -/

def allRgsLoop (rgIndex rgCount fuel : Nat) (accRev : List Nat) : List Nat :=
  match fuel with
  | 0 => accRev
  | f + 1 =>
      if rgIndex ≥ rgCount then accRev
      else allRgsLoop (rgIndex + 1) rgCount f (rgIndex :: accRev)

def allRgs (rgCount : Nat) : List Nat :=
  (allRgsLoop 0 rgCount rgCount []).reverse

theorem allRgsLoop_eq_range' :
    ∀ (fuel rgIndex rgCount : Nat) (accRev : List Nat), rgCount - rgIndex ≤ fuel →
      allRgsLoop rgIndex rgCount fuel accRev
        = (List.range' rgIndex (rgCount - rgIndex)).reverse ++ accRev
  | 0, i, n, accRev, hf => by
      have h : n - i = 0 := by omega
      simp [allRgsLoop, h]
  | fuel + 1, i, n, accRev, hf => by
      rw [allRgsLoop]
      by_cases h : i ≥ n
      · have hz : n - i = 0 := by omega
        simp [h, hz]
      · have hk : n - i = (n - (i + 1)) + 1 := by omega
        simp only [h, if_neg, not_false_eq_true]
        rw [allRgsLoop_eq_range' fuel (i + 1) n (i :: accRev) (by omega), hk,
            List.range'_succ]
        simp

theorem allRgs_eq_range (n : Nat) : allRgs n = List.range n := by
  simp only [allRgs, allRgsLoop_eq_range' n 0 n [] (by omega), Nat.sub_zero,
             List.append_nil, List.reverse_reverse]
  exact List.range_eq_range'.symm

/-! ## 6. The unpruned scan and the full candidate list are one walk

The assumption the pruning design rests on. If these two disagreed,
turning pruning on would change RESULTS rather than only time. -/

theorem walkRangeTok_eq_walkCandidatesTok (rd : ColumnReader)
    (bs bp bo bg : Option String) :
    ∀ (fuel rgIndex rgCount : Nat) (accRev : List QpRowTok),
      rgCount - rgIndex ≤ fuel →
      walkRangeTok rd bs bp bo bg rgIndex rgCount fuel accRev
        = walkCandidatesTok rd bs bp bo bg
            (List.range' rgIndex (rgCount - rgIndex)) accRev
  | 0, i, n, accRev, hf => by
      have h : n - i = 0 := by omega
      simp [walkRangeTok, h, walkCandidatesTok]
  | fuel + 1, i, n, accRev, hf => by
      rw [walkRangeTok]
      by_cases h : i ≥ n
      · have hz : n - i = 0 := by omega
        simp [h, hz, walkCandidatesTok]
      · have hk : n - i = (n - (i + 1)) + 1 := by omega
        simp only [h, if_neg, not_false_eq_true]
        rw [walkRangeTok_eq_walkCandidatesTok rd bs bp bo bg fuel (i + 1) n
              (rgStepTok rd bs bp bo bg i accRev) (by omega), hk]
        rw [List.range'_succ, walkCandidatesTok]

theorem walkRange_eq_walkCandidates (rd : ColumnReader)
    (bs bp bo bg : Option String) (rgCount : Nat) (accRev : List QpRowTok) :
    walkRangeTok rd bs bp bo bg 0 rgCount rgCount accRev
      = walkCandidatesTok rd bs bp bo bg (allRgs rgCount) accRev := by
  rw [allRgs_eq_range, List.range_eq_range']
  have h := walkRangeTok_eq_walkCandidatesTok rd bs bp bo bg rgCount 0 rgCount
    accRev (by omega)
  simpa using h

/-! ## 7. "Counts only", one level up -/

theorem walkRangeCount_eq_length (rd : ColumnReader)
    (bs bp bo bg : Option String) :
    ∀ (fuel rgIndex rgCount : Nat) (accRev : List QpRowTok),
      walkRangeCount rd bs bp bo bg rgIndex rgCount fuel accRev.length
        = (walkRangeTok rd bs bp bo bg rgIndex rgCount fuel accRev).length
  | 0, _, _, _ => rfl
  | fuel + 1, i, n, accRev => by
      rw [walkRangeCount, walkRangeTok]
      by_cases h : i ≥ n
      · simp [h]
      · simp only [h, if_neg, not_false_eq_true]
        rw [rgStepCount_eq_length rd bs bp bo bg i accRev]
        exact walkRangeCount_eq_length rd bs bp bo bg fuel (i + 1) n
          (rgStepTok rd bs bp bo bg i accRev)

theorem walkCandidatesCount_eq_length (rd : ColumnReader)
    (bs bp bo bg : Option String) :
    ∀ (cands : List Nat) (accRev : List QpRowTok),
      walkCandidatesCount rd bs bp bo bg cands accRev.length
        = (walkCandidatesTok rd bs bp bo bg cands accRev).length
  | [], _ => rfl
  | rg :: rest, accRev => by
      rw [walkCandidatesCount, walkCandidatesTok,
          rgStepCount_eq_length rd bs bp bo bg rg accRev]
      exact walkCandidatesCount_eq_length rd bs bp bo bg rest
        (rgStepTok rd bs bp bo bg rg accRev)

/-! ## 8. Soundness survives the walk

Every row a full scan returns matches all four bounds — layer 2's
`filterTokSeq_sound`, carried through the row-group loop. -/

theorem mem_rgStepTok_matches (rd : ColumnReader) (bs bp bo bg : Option String)
    (rg : Nat) (accRev : List QpRowTok) (r : QpRowTok)
    (hacc : ∀ q ∈ accRev, cellMatch bs q.s = true ∧ cellMatch bp q.p = true
      ∧ cellMatch bo q.o = true ∧ graphCellMatch bg q.g = true)
    (h : r ∈ rgStepTok rd bs bp bo bg rg accRev) :
    cellMatch bs r.s = true ∧ cellMatch bp r.p = true
      ∧ cellMatch bo r.o = true ∧ graphCellMatch bg r.g = true := by
  simp only [rgStepTok] at h
  cases h0 : rd rg 0 <;> cases h1 : rd rg 1 <;> cases h2 : rd rg 2
    <;> cases h3 : rd rg 3 <;> rw [h0, h1, h2, h3] at h <;> try exact hacc r h
  rename_i sc pc oc gc
  exact mem_filterTokSeq_matches bs bp bo bg sc pc oc gc
    (rowGroupRowCount sc pc oc gc) (rowGroupRowCount sc pc oc gc) 0 accRev r
    (by omega) hacc h

theorem walkCandidatesTok_sound (rd : ColumnReader)
    (bs bp bo bg : Option String) :
    ∀ (cands : List Nat) (accRev : List QpRowTok) (r : QpRowTok),
      (∀ q ∈ accRev, cellMatch bs q.s = true ∧ cellMatch bp q.p = true
        ∧ cellMatch bo q.o = true ∧ graphCellMatch bg q.g = true) →
      r ∈ walkCandidatesTok rd bs bp bo bg cands accRev →
      cellMatch bs r.s = true ∧ cellMatch bp r.p = true
        ∧ cellMatch bo r.o = true ∧ graphCellMatch bg r.g = true
  | [], accRev, r, hacc, h => hacc r h
  | rg :: rest, accRev, r, hacc, h => by
      rw [walkCandidatesTok] at h
      exact walkCandidatesTok_sound rd bs bp bo bg rest _ r
        (fun q hq => mem_rgStepTok_matches rd bs bp bo bg rg accRev q hacc hq) h

/-! ## Build-time checks -/

private def cS : Column := #[some "<a:1>", some "<a:2>"]
private def cP : Column := #[some "<p:1>", some "<p:1>"]
private def cO : Column := #[some "<o:1>", some "<o:2>"]
private def cG : Column := #[some "DEFAULT", some "DEFAULT"]

/-- Two identical row groups, and a third that fails to decode. -/
private def rdTwo : ColumnReader := fun rg col =>
  if rg < 2 then
    match col with
    | 0 => some cS
    | 1 => some cP
    | 2 => some cO
    | 3 => some cG
    | _ => none
  else none

/-! Both row groups are scanned. -/
#guard (walkRangeTok rdTwo none none none none 0 2 2 []).length == 4
#guard walkRangeCount rdTwo none none none none 0 2 2 0 == 4

/-! ⚠️ A row group whose columns do not decode is SKIPPED, and the walk
continues. An empty row group and a corrupt one give the same answer —
issue 571. -/
#guard (walkRangeTok rdTwo none none none none 0 3 3 []).length == 4

/-! Fuel is observable: fuel below the row-group count truncates the
scan, with no error. -/
#guard (walkRangeTok rdTwo none none none none 0 2 1 []).length == 2
#guard (walkRangeTok rdTwo none none none none 0 2 0 []).length == 0

/-! The unpruned range and the full candidate list are one walk. -/
#guard allRgs 3 == [0, 1, 2]
#guard allRgs 0 == ([] : List Nat)
#guard walkRangeTok rdTwo none none none none 0 2 2 []
        == walkCandidatesTok rdTwo none none none none (allRgs 2) []

/-! Pruning to one row group returns half the rows. -/
#guard (walkCandidatesTok rdTwo none none none none [0] []).length == 2
#guard (walkCandidatesTok rdTwo none none none none [] []).length == 0

/-! A bound cuts across both row groups. -/
#guard walkRangeCount rdTwo (some "<a:1>") none none none 0 2 2 0 == 2
#guard walkRangeCount rdTwo (some "<a:9>") none none none 0 2 2 0 == 0

/-! ## Axiom audit -/

#print axioms allRgs_eq_range
#print axioms walkRange_eq_walkCandidates
#print axioms walkRangeCount_eq_length
#print axioms walkCandidatesCount_eq_length
#print axioms walkCandidatesTok_sound

end L4Factoidal.Cottas.OnDiskStore
