/-
L4Factoidal.Cottas.OnDiskCount — layer 7 of the port of
`RDF.CottasStore`: exact counting, distinct predicates, and the
subject-range prune.

Three families that layers 1 to 6 did not reach.

## The selective count, and where it does not agree

`count_selective_matches_seq` exists because `COUNT(*)` over
`{ ?s a ?o }` was decoding the subject and object columns it never
reads: two high-cardinality columns, and on the gene corpus the
dominant cost of a 55-second cold count. The fix decodes only the
columns that carry a bound, plus the graph column.

The F\* source presents it as the same quantity computed cheaper. It is
not quite. The full count (`count_zipped_rows_seq`) requires ALL FOUR
cells to be non-null before it counts a row. The selective count
requires only the GRAPH cell to be non-null, because `bound_col_match`
on an absent bound returns `true` without inspecting anything. So a row
carrying a null in an UNBOUND column is counted by the selective walk
and dropped by the full one.

`countSelective_eq_countSeq` gives the equality under the conditions
that make the two agree — four columns of equal length, every cell
present — and `countSelective_counts_null_row` exhibits the divergence
on one row that violates the second. Whether a COTTAS column can hold a
null at all is a question about the writer, not about these two
functions; what is settled here is that IF one can, the two counts are
different numbers, and only one of them is the answer to `COUNT(*)`.

Raised as <https://github.com/danbri/factoidal/issues/572>.

## Distinct predicates aborts rather than guesses

`collect_distinct_column_tokens_rgs` returns `none` the instant ANY
touched row group's dictionary page is missing. Its banner says why:
"never silently treat 'couldn't read the dictionary' as 'this row group
has zero predicates.'" `collectDistinct_none_of_missing` states that as
a theorem — the failure is total, not per-row-group — which is the
opposite of the row-group walk's recovery in layer 3, and the contrast
is deliberate in the F\* source.

## The subject-range prune is an interval overlap

`subject_range_candidate_rgs_loop` walks cumulative row counts asking
which row groups a global row range touches.
`subjectRangeCandidateRgs_eq_filter` puts it in filter form, which makes
the overlap test visible as the half-open interval test it is
(`start < cumEnd && cumStart < end`) rather than something to re-derive
from an accumulator.

No `sorry`, no user `axiom`, no `native_decide`.
-/
import L4Factoidal.Cottas.OnDiskSearch

namespace L4Factoidal.Cottas.OnDiskStore

open L4Factoidal.RDF
open L4Factoidal.Cottas.Ballyhoo

/-! ## 1. Small predicates -/

/-- The page cache's default capacity. Parliament's 26 row groups times
4 columns is 104 entries; 128 gives headroom without thrash. -/
def pcacheDefaultCapacity : Nat := 128

/-- Port of `cottas_ondisk_version_ok`. A store whose recorded format
version does not match the writer's current stamp was written by a
writer we no longer trust, and is rejected outright rather than read.
Owner decision on <https://github.com/danbri/factoidal/issues/445>: no
migration path, no back-compatible reader. -/
def versionOk (fileVersion : Option Nat) (currentVersion : Nat) : Bool :=
  match fileVersion with
  | some v => v == currentVersion
  | none => false

theorem versionOk_none (cur : Nat) : versionOk none cur = false := rfl

/-- Port of `cottas_ondisk_has_decode_failure`: any of the four columns
failing a whole-file decode condemns the handle. -/
def hasDecodeFailure (decodeAll : Nat → Option Column) : Bool :=
  (decodeAll 0).isNone || (decodeAll 1).isNone || (decodeAll 2).isNone
    || (decodeAll 3).isNone

/-! ## 2. Counting on the graph column alone -/

def countGraphColMatchesSeq (bg : Option String) (gc : Column)
    (n i acc : Nat) : Nat :=
  if h : i < n then
    countGraphColMatchesSeq bg gc n (i + 1)
      (match cellAt gc i with
       | some g => if graphCellMatch bg g then acc + 1 else acc
       | none => acc)
  else acc
termination_by n - i
decreasing_by omega

def walkCountGraph (rd : ColumnReader) (bg : Option String)
    (rgIndex rgCount fuel acc : Nat) : Nat :=
  match fuel with
  | 0 => acc
  | f + 1 =>
      if rgIndex ≥ rgCount then acc
      else
        walkCountGraph rd bg (rgIndex + 1) rgCount f
          (match rd rgIndex 3 with
           | some gc => countGraphColMatchesSeq bg gc gc.size 0 acc
           | none => acc)

/-! ## 3. The selective count

`boundColMatch` mirrors `cellMatch`'s contract on a bound that is
present, and returns `true` WITHOUT inspecting anything on a bound that
is absent — which is the whole point, since the column may not have been
decoded. -/

def boundColMatch (b : Option String) (col : Option Column) (i : Nat) : Bool :=
  match b with
  | none => true
  | some expected =>
      match col with
      | none => false
      | some c =>
          if i < c.size then
            match cellAt c i with
            | some tok => tok == expected
            | none => false
          else false

def countSelectiveMatchesSeq (bs bp bo bg : Option String)
    (sc pc oc : Option Column) (gc : Column) (n i acc : Nat) : Nat :=
  if h : i < n then
    countSelectiveMatchesSeq bs bp bo bg sc pc oc gc n (i + 1)
      (if i < gc.size then
        match cellAt gc i with
        | some gTok =>
            if boundColMatch bs sc i && boundColMatch bp pc i
                && boundColMatch bo oc i && graphCellMatch bg gTok
            then acc + 1 else acc
        | none => acc
       else acc)
  else acc
termination_by n - i
decreasing_by omega

/-- Only decode a column when its bound is present; the graph column is
always decoded, because it is cheap and it sources the row count. A
BOUND column that fails to decode zeroes the row group; an unbound one
that would have failed is never asked. -/
def walkCountExact (rd : ColumnReader) (bs bp bo bg : Option String)
    (rgIndex rgCount fuel acc : Nat) : Nat :=
  match fuel with
  | 0 => acc
  | f + 1 =>
      if rgIndex ≥ rgCount then acc
      else
        walkCountExact rd bs bp bo bg (rgIndex + 1) rgCount f
          (match rd rgIndex 3 with
           | none => acc
           | some gc =>
               let sc := if bs.isSome then rd rgIndex 0 else none
               let pc := if bp.isSome then rd rgIndex 1 else none
               let oc := if bo.isSome then rd rgIndex 2 else none
               let neededOk := (bs.isNone || sc.isSome)
                 && (bp.isNone || pc.isSome) && (bo.isNone || oc.isSome)
               if neededOk then
                 countSelectiveMatchesSeq bs bp bo bg sc pc oc gc gc.size 0 acc
               else acc)

/-! ## 4. Where the two counts agree, and where they do not -/

/-- Every cell below `n` is present. -/
def ColumnDense (c : Column) (n : Nat) : Prop :=
  ∀ i, i < n → (cellAt c i).isSome = true

theorem boundColMatch_eq_cellMatch (b : Option String) (c : Column) (i : Nat)
    (hlt : i < c.size) (t : String) (hcell : cellAt c i = some t) :
    boundColMatch b (some c) i = cellMatch b t := by
  cases b with
  | none => rfl
  | some e => simp [boundColMatch, cellMatch, hlt, hcell, BEq.comm]

/-- **The selective count IS the full count** on a row group whose four
columns have equal length and hold no null, with every bound column
decoded. Those are exactly the conditions the F\* source assumes
silently. -/
theorem countSelective_eq_countSeq (bs bp bo bg : Option String)
    (sc pc oc gc : Column)
    (hs : sc.size = gc.size) (hp : pc.size = gc.size) (ho : oc.size = gc.size)
    (dsc : ColumnDense sc gc.size) (dpc : ColumnDense pc gc.size)
    (doc : ColumnDense oc gc.size) (dgc : ColumnDense gc gc.size) :
    ∀ (fuel i acc : Nat), gc.size - i ≤ fuel →
      countSelectiveMatchesSeq bs bp bo bg (some sc) (some pc) (some oc) gc
        gc.size i acc
        = countSeq bs bp bo bg sc pc oc gc gc.size i acc
  | 0, i, acc, hf => by
      have h : ¬ i < gc.size := by omega
      rw [countSelectiveMatchesSeq, countSeq]; simp [h]
  | fuel + 1, i, acc, hf => by
      rw [countSelectiveMatchesSeq, countSeq]
      by_cases h : i < gc.size
      · have hsi : i < sc.size := by omega
        have hpi : i < pc.size := by omega
        have hoi : i < oc.size := by omega
        obtain ⟨st, hst⟩ := Option.isSome_iff_exists.mp (dsc i h)
        obtain ⟨pt, hpt⟩ := Option.isSome_iff_exists.mp (dpc i h)
        obtain ⟨ot, hot⟩ := Option.isSome_iff_exists.mp (doc i h)
        obtain ⟨gt, hgt⟩ := Option.isSome_iff_exists.mp (dgc i h)
        simp only [h, dif_pos, hgt, if_pos,
                   boundColMatch_eq_cellMatch bs sc i hsi st hst,
                   boundColMatch_eq_cellMatch bp pc i hpi pt hpt,
                   boundColMatch_eq_cellMatch bo oc i hoi ot hot,
                   rowSelected, rowCells, hsi, hpi, hoi, hst, hpt, hot,
                   decide_true, Bool.and_self]
        rw [countSelective_eq_countSeq bs bp bo bg sc pc oc gc hs hp ho dsc dpc
              doc dgc fuel (i + 1) _ (by omega)]
        congr 1
        by_cases hm : (cellMatch bs st && cellMatch bp pt && cellMatch bo ot
            && graphCellMatch bg gt) = true
        · simp [hm]
        · simp [hm]
      · simp [h]

/-! ⚠️ **And where they do not agree.** One row group, two rows. The
object column's second cell is NULL, and there is no object bound. The
full count drops that row because `rowCells` needs all four; the
selective count keeps it, because an absent bound is never asked about
its column. Two different numbers for `COUNT(*)`. -/

private def dS : Column := #[some "<a:1>", some "<a:2>"]
private def dP : Column := #[some "<p:1>", some "<p:1>"]
private def dONull : Column := #[some "<o:1>", none]
private def dG : Column := #[some "DEFAULT", some "DEFAULT"]

#guard countSeq none (some "<p:1>") none none dS dP dONull dG 2 0 0 == 1
#guard countSelectiveMatchesSeq none (some "<p:1>") none none
        none (some dP) none dG 2 0 0 == 2

/-! With no null the two agree, which is `countSelective_eq_countSeq`
worked on one input. -/
private def dO : Column := #[some "<o:1>", some "<o:2>"]
#guard countSeq none (some "<p:1>") none none dS dP dO dG 2 0 0 == 2
#guard countSelectiveMatchesSeq none (some "<p:1>") none none
        (some dS) (some dP) (some dO) dG 2 0 0 == 2

/-! ## 5. Distinct predicates -/

def unionDedupeStringsAcc (acc : List String) : List String → List String
  | [] => acc
  | hd :: tl =>
      if listStringMem acc hd then unionDedupeStringsAcc acc tl
      else unionDedupeStringsAcc (hd :: acc) tl

theorem mem_unionDedupeStringsAcc : ∀ (acc new : List String) (s : String),
    s ∈ unionDedupeStringsAcc acc new ↔ (s ∈ acc ∨ s ∈ new)
  | acc, [], s => by simp [unionDedupeStringsAcc]
  | acc, hd :: tl, s => by
      rw [unionDedupeStringsAcc]
      by_cases h : listStringMem acc hd
      · rw [if_pos h, mem_unionDedupeStringsAcc acc tl s]
        have hm : hd ∈ acc := (listStringMem_iff acc hd).mp h
        constructor
        · rintro (h1 | h1)
          · exact Or.inl h1
          · exact Or.inr (List.mem_cons_of_mem _ h1)
        · rintro (h1 | h1)
          · exact Or.inl h1
          · rcases List.mem_cons.mp h1 with rfl | h1'
            · exact Or.inl hm
            · exact Or.inr h1'
      · rw [if_neg h, mem_unionDedupeStringsAcc (hd :: acc) tl s]
        constructor
        · rintro (h1 | h1)
          · rcases List.mem_cons.mp h1 with rfl | h1'
            · exact Or.inr (List.mem_cons_self ..)
            · exact Or.inl h1'
          · exact Or.inr (List.mem_cons_of_mem _ h1)
        · rintro (h1 | h1)
          · exact Or.inl (List.mem_cons_of_mem _ h1)
          · rcases List.mem_cons.mp h1 with rfl | h1'
            · exact Or.inl (List.mem_cons_self ..)
            · exact Or.inr h1'

/-- Walk row groups reading only dictionary pages. **A missing
dictionary page aborts the WHOLE walk** — never "this row group has zero
predicates". -/
def collectDistinctColumnTokensRgs (dr : DictReader) (col : Nat)
    (rgIndex rgCount fuel : Nat) (acc : List String) : Option (List String) :=
  match fuel with
  | 0 => some acc
  | f + 1 =>
      if rgIndex ≥ rgCount then some acc
      else
        match dr rgIndex col with
        | none => none
        | some entries =>
            collectDistinctColumnTokensRgs dr col (rgIndex + 1) rgCount f
              (unionDedupeStringsAcc acc entries)

/-- The failure is TOTAL, not per-row-group — the opposite of the
row-group walk's recovery in layer 3, and deliberately so. -/
theorem collectDistinct_none_of_missing (dr : DictReader) (col : Nat) :
    ∀ (fuel rgIndex rgCount : Nat) (acc : List String) (bad : Nat),
      rgIndex ≤ bad → bad < rgCount → rgCount - rgIndex ≤ fuel →
      dr bad col = none →
      (∀ rg, rgIndex ≤ rg → rg < bad → (dr rg col).isSome = true) →
      collectDistinctColumnTokensRgs dr col rgIndex rgCount fuel acc = none
  | 0, i, n, acc, bad, hle, hlt, hf, _, _ => by omega
  | fuel + 1, i, n, acc, bad, hle, hlt, hf, hbad, hbefore => by
      rw [collectDistinctColumnTokensRgs]
      have h : ¬ i ≥ n := by omega
      simp only [h, if_neg, not_false_eq_true]
      by_cases heq : i = bad
      · subst heq; rw [hbad]
      · have hib : i < bad := by omega
        obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp (hbefore i (by omega) hib)
        rw [he]
        exact collectDistinct_none_of_missing dr col fuel (i + 1) n _ bad
          (by omega) hlt (by omega) hbad
          (fun rg h1 h2 => hbefore rg (by omega) h2)

/-- The predicate column is Parquet column index 1. Tokens are typed at
DISTINCT cardinality, not row cardinality. -/
def distinctPredicates (dr : DictReader) (rgCount : Option Nat) :
    Option (List WfIri) :=
  match rgCount with
  | none => none
  | some n =>
      (collectDistinctColumnTokensRgs dr 1 0 n n []).map
        (fun toks => toks.map tokenToPredicate)

/-! ## 6. The subject-range prune

Does the global row range `[start, end)` touch row group `rg`'s own
`[cumStart, cumStart + rows)`? A row-count that cannot be read returns
`none` the instant it appears — the caller then keeps its unpruned
candidate set, never a silently empty one. -/

def rangeOverlaps (start' end' cumStart cumEnd : Nat) : Bool :=
  start' < cumEnd && cumStart < end'

def subjectRangeCandidateRgsLoop (rows : Nat → Option Nat)
    (targetStart targetEnd : Nat) (rgIndex rgCount fuel cumStart : Nat)
    (accRev : List Nat) : Option (List Nat) :=
  match fuel with
  | 0 => some accRev.reverse
  | f + 1 =>
      if rgIndex ≥ rgCount then some accRev.reverse
      else
        match rows rgIndex with
        | none => none
        | some rgRows =>
            let cumEnd := cumStart + rgRows
            subjectRangeCandidateRgsLoop rows targetStart targetEnd
              (rgIndex + 1) rgCount f cumEnd
              (if rangeOverlaps targetStart targetEnd cumStart cumEnd
               then rgIndex :: accRev else accRev)

/-- ⚠️ **The overlap test requires a NON-EMPTY range, and does not say
so.** For `[s, s)` it reduces to `s < cumEnd && cumStart < s`, which is
TRUE for any row group that strictly contains `s` — so an empty range
reports an overlap with the row group it sits inside.

This is not a live defect. `cottas_ondisk_subject_candidate_rgs` returns
`Some []` for a subject whose range count is zero, three lines before it
would call this loop, so the loop never sees an empty range. The
precondition lives in the caller and nowhere in the loop's own type,
which is why it is written down here. -/
theorem rangeOverlaps_empty_reports_overlap (s cumStart cumEnd : Nat)
    (h1 : cumStart < s) (h2 : s < cumEnd) :
    rangeOverlaps s s cumStart cumEnd = true := by
  simp [rangeOverlaps]; omega

/-- An empty range outside a row group correctly reports no overlap, so
the defect above is specific to a point strictly inside. -/
theorem rangeOverlaps_empty_outside (s cumStart cumEnd : Nat)
    (h : cumEnd ≤ s) : rangeOverlaps s s cumStart cumEnd = false := by
  simp [rangeOverlaps]; omega

/-- A range inside one row group touches that row group. -/
theorem rangeOverlaps_inside (s e cumStart cumEnd : Nat)
    (h1 : cumStart ≤ s) (h2 : s < e) (h3 : e ≤ cumEnd) :
    rangeOverlaps s e cumStart cumEnd = true := by
  simp [rangeOverlaps]; omega

/-! ## Build-time checks -/

private def rowsOf : Nat → Option Nat := fun rg =>
  if rg < 3 then some 100 else none

/-! Rows 0..99 are row group 0; 150..250 spans row groups 1 and 2. -/
#guard subjectRangeCandidateRgsLoop rowsOf 0 100 0 3 3 0 [] == some [0]
#guard subjectRangeCandidateRgsLoop rowsOf 150 250 0 3 3 0 [] == some [1, 2]
#guard subjectRangeCandidateRgsLoop rowsOf 0 300 0 3 3 0 [] == some [0, 1, 2]

/-! ⚠️ An empty range at a point INSIDE a row group reports that row
group — see `rangeOverlaps_empty_reports_overlap`. The caller never
passes one, because a zero-count subject range short-circuits to `Some
[]` before the loop is reached. -/
#guard subjectRangeCandidateRgsLoop rowsOf 50 50 0 3 3 0 [] == some [0]
#guard subjectRangeCandidateRgsLoop rowsOf 300 300 0 3 3 0 []
        == some ([] : List Nat)

/-! ⚠️ A row count that cannot be read aborts with `none`, so the caller
keeps its unpruned candidate set rather than getting a wrong empty
one. -/
#guard subjectRangeCandidateRgsLoop rowsOf 0 100 0 4 4 0 [] == (none : Option (List Nat))

/-! Distinct predicates: the union across row groups, deduplicated. -/
private def prDict : DictReader := fun rg col =>
  if col == 1 then
    match rg with
    | 0 => some ["<p:1>", "<p:2>"]
    | 1 => some ["<p:2>", "<p:3>"]
    | _ => none
  else none

#guard (collectDistinctColumnTokensRgs prDict 1 0 2 2 []).map List.length == some 3
#guard (distinctPredicates prDict (some 2)).map List.length == some 3

/-! ⚠️ One missing dictionary page aborts the whole answer. -/
#guard collectDistinctColumnTokensRgs prDict 1 0 3 3 []
        == (none : Option (List String))
#guard distinctPredicates prDict (some 3) == (none : Option (List WfIri))
#guard distinctPredicates prDict none == (none : Option (List WfIri))

/-! Union-dedupe keeps one copy. -/
#guard unionDedupeStringsAcc [] ["a", "b", "a"] == ["b", "a"]
#guard unionDedupeStringsAcc ["a"] ["a"] == ["a"]

/-! Version gate and decode-failure gate. -/
#guard versionOk (some 3) 3
#guard ! versionOk (some 2) 3
#guard ! versionOk none 3
#guard ! hasDecodeFailure (fun _ => some dS)
#guard hasDecodeFailure (fun c => if c == 2 then none else some dS)

/-! Counting on the graph column alone. -/
#guard countGraphColMatchesSeq (some "DEFAULT") dG 2 0 0 == 2
#guard countGraphColMatchesSeq (some "<g:1>") dG 2 0 0 == 0
#guard countGraphColMatchesSeq none dG 2 0 0 == 2

#guard pcacheDefaultCapacity == 128

/-! ## Axiom audit -/

#print axioms countSelective_eq_countSeq
#print axioms mem_unionDedupeStringsAcc
#print axioms collectDistinct_none_of_missing
#print axioms boundColMatch_eq_cellMatch
#print axioms rangeOverlaps_empty_reports_overlap

end L4Factoidal.Cottas.OnDiskStore
