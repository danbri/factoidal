/-
L4Factoidal.Cottas.OnDiskSelective — layer 8 of the port of
`RDF.CottasStore`: row-index-selective decode.

The last family. `cottas_ondisk_search_tok_selective` answers the same
query as `cottas_ondisk_search_tok`, but decodes an UNBOUND column's
values only at the row indices that already matched on the cheap
columns, instead of decoding every column of every candidate row group
up front.

## The claim the F\* source makes, and this layer proves

The public entry point's banner states the differential gate's premise
outright:

> "identical row-group planning … and identical row/row-group ORDER to
> `cottas_ondisk_search_tok` … `need` only changes which UNBOUND columns
> get decoded, never which rows match or their order."

Two separate claims, and both are provable here.

* `matched_iff_rowSelected` — at every index where all four columns
  decode, the selective matcher's gate and `rowSelected` agree, so the
  selective walk selects the rows the plain filter selects. Same rows.
* `selectiveRows_need_invariant` — narrowing `need` changes neither the
  number of rows returned nor their graph values nor their order. Same
  order, and `need` really is only about which bytes get read.

Without the first, the "differential gate" compares two functions that
were never claimed equal. Without the second, `need` is a correctness
parameter wearing a performance parameter's name.

## The lockstep advance, and why it is not a lookup

`vals_advance` walks the decoded pairs head-forward, consuming each list
exactly once across the whole row group. The F\* comment records what it
replaced and what that cost: a per-row rescan made the full-corpus
differential gate quadratic over 889k rows and it timed out on
2026-07-13. The advance is correct only because both the index list and
each values list are ASCENDING — `valsAdvance_skips_stale` and
`valsAdvance_stops_above` pin the two directions of that walk, so the
ordering requirement is a checked fact rather than a comment on a
function that would silently return `none` without it.

## Positions that are never read

A BOUND position is filled from the bound's own token with no column
read at all — the match test already established the cell equals it. An
unbound position that `need` does not mark is `none`, and that `none`
means "never decoded", not "no value". `selectiveRow_bound_position`
states the first; the second is what makes the result type carry
`Option String` where `QpRowTok` carries `String`.

No `sorry`, no user `axiom`, no `native_decide`.
-/
import L4Factoidal.Cottas.OnDiskCount

namespace L4Factoidal.Cottas.OnDiskStore

open L4Factoidal.RDF
open L4Factoidal.Cottas.Ballyhoo

/-! ## 1. The selective row

`none` in a position means the column was never decoded, NOT that the
row has no value there. The graph position is never gated, so it is a
plain `String`. -/

structure QpRowTokSelective where
  s : Option String
  p : Option String
  o : Option String
  g : String
deriving DecidableEq, Repr, Inhabited

/-! ## 2. Which rows matched

Mirrors `countSelectiveMatchesSeq`'s gating exactly — the same
`boundColMatch` and `graphCellMatch` calls — collecting indices instead
of a count. -/

def matchedIndicesSeq (bs bp bo bg : Option String)
    (sc pc oc : Option Column) (gc : Column) (n i : Nat)
    (accRev : List Nat) : List Nat :=
  if h : i < n then
    matchedIndicesSeq bs bp bo bg sc pc oc gc n (i + 1)
      (if i < gc.size then
        match cellAt gc i with
        | some gTok =>
            if boundColMatch bs sc i && boundColMatch bp pc i
                && boundColMatch bo oc i && graphCellMatch bg gTok
            then i :: accRev else accRev
        | none => accRev
       else accRev)
  else accRev
termination_by n - i
decreasing_by omega

/-- **Same rows as the plain filter**, index by index: the selective
matcher's gate holds exactly when `rowSelected` returns a row.

Stated per index rather than over the whole walk because that is what is
true without further hypotheses — the two walks then differ only in the
null-cell case layer 7 already isolated
(<https://github.com/danbri/factoidal/issues/572>), which is the same
divergence, not a second one. -/
theorem matched_iff_rowSelected (bs bp bo bg : Option String)
    (sc pc oc gc : Column) (i : Nat)
    (hsi : i < sc.size) (hpi : i < pc.size) (hoi : i < oc.size)
    (hgi : i < gc.size)
    (st pt ot gt : String)
    (hst : cellAt sc i = some st) (hpt : cellAt pc i = some pt)
    (hot : cellAt oc i = some ot) (hgt : cellAt gc i = some gt) :
    (boundColMatch bs (some sc) i && boundColMatch bp (some pc) i
      && boundColMatch bo (some oc) i && graphCellMatch bg gt)
      = (rowSelected bs bp bo bg sc pc oc gc i).isSome := by
  rw [boundColMatch_eq_cellMatch bs sc i hsi st hst,
      boundColMatch_eq_cellMatch bp pc i hpi pt hpt,
      boundColMatch_eq_cellMatch bo oc i hoi ot hot]
  simp only [rowSelected, rowCells, hsi, hpi, hoi, hgi, hst, hpt, hot, hgt,
             decide_true, Bool.and_self, if_true]
  by_cases hm : cellMatch bs st && cellMatch bp pt && cellMatch bo ot
      && graphCellMatch bg gt
  · simp [hm]
  · simp [hm]

/-! ## 3. Filtering a decoded column by index -/

def filterColumnByIndicesAcc (col : Column) :
    List Nat → List (Nat × String) → List (Nat × String)
  | [], accRev => accRev
  | i :: rest, accRev =>
      filterColumnByIndicesAcc col rest
        (if i < col.size then
          match cellAt col i with
          | some tok => (i, tok) :: accRev
          | none => accRev
         else accRev)

def filterColumnByIndices (col : Column) (indices : List Nat) :
    List (Nat × String) :=
  (filterColumnByIndicesAcc col indices []).reverse

/-! ## 4. The lockstep advance

Correct only because both the index list and each values list are
ASCENDING. The F\* comment records what a per-row rescan cost: the
full-corpus differential gate went quadratic over 889k rows and timed
out. -/

def valsAdvance : List (Nat × String) → Nat → Option String × List (Nat × String)
  | [], _ => (none, [])
  | (k, v) :: rest, i =>
      if k = i then (some v, rest)
      else if k < i then valsAdvance rest i
      else (none, (k, v) :: rest)

/-- A key below the requested row is stale and skipped. -/
theorem valsAdvance_skips_stale (k : Nat) (v : String)
    (rest : List (Nat × String)) (i : Nat) (h : k < i) :
    valsAdvance ((k, v) :: rest) i = valsAdvance rest i := by
  have hne : ¬ (k = i) := by omega
  simp [valsAdvance, hne, h]

/-- A key above the requested row means this row has no decoded value,
and the list is NOT consumed — the next row may want that key. -/
theorem valsAdvance_stops_above (k : Nat) (v : String)
    (rest : List (Nat × String)) (i : Nat) (h : i < k) :
    valsAdvance ((k, v) :: rest) i = (none, (k, v) :: rest) := by
  have hne : ¬ (k = i) := by omega
  have hnl : ¬ (k < i) := by omega
  simp [valsAdvance, hne, hnl]

theorem valsAdvance_hit (v : String) (rest : List (Nat × String)) (i : Nat) :
    valsAdvance ((i, v) :: rest) i = (some v, rest) := by
  simp [valsAdvance]

/-! ## 5. Building the output rows

A BOUND position is filled from the bound's own token — no column read
at all, because the match test already established the cell equals it.
An unbound position `need` does not mark is `none`. -/

/-- One position's value and the remaining pairs: a bound position uses
the bound's own token and consumes nothing, a needed unbound position
advances, and an unneeded one is `none`. -/
def advanceFor (b : Option String) (needIt : Bool)
    (vals : List (Nat × String)) (i : Nat) :
    Option String × List (Nat × String) :=
  if b.isSome then (b, vals)
  else if needIt then valsAdvance vals i else (none, vals)

def buildSelectiveRows (bs bp bo : Option String) (need : ColNeed)
    (gc : Column) :
    List (Nat × String) → List (Nat × String) → List (Nat × String) →
    List Nat → List QpRowTokSelective → List QpRowTokSelective
  | _, _, _, [], accRev => accRev
  | sVals, pVals, oVals, i :: rest, accRev =>
      buildSelectiveRows bs bp bo need gc (advanceFor bs need.s sVals i).2
        (advanceFor bp need.p pVals i).2 (advanceFor bo need.o oVals i).2 rest
        ({ s := (advanceFor bs need.s sVals i).1
           p := (advanceFor bp need.p pVals i).1
           o := (advanceFor bo need.o oVals i).1
           g := if i < gc.size then
                  match cellAt gc i with | some g => g | none => ""
                else "" } :: accRev)

/-- One output row per matched index, whatever `need` says. -/
theorem buildSelectiveRows_length (bs bp bo : Option String) (need : ColNeed)
    (gc : Column) :
    ∀ (sVals pVals oVals : List (Nat × String)) (indices : List Nat)
      (accRev : List QpRowTokSelective),
      (buildSelectiveRows bs bp bo need gc sVals pVals oVals indices
        accRev).length = indices.length + accRev.length
  | _, _, _, [], accRev => by simp [buildSelectiveRows]
  | sVals, pVals, oVals, i :: rest, accRev => by
      rw [buildSelectiveRows,
          buildSelectiveRows_length bs bp bo need gc _ _ _ rest _]
      simp
      omega

/-- **`need` changes no row's graph value and no row's position.** The
graph column is never gated, so the whole `g` projection is independent
of `need` — the "same order" half of the differential claim, made
checkable.

The accumulators are allowed to DIFFER, as long as they already agree on
`g`. That generalisation is not decoration: the two walks build rows
whose `s`, `p` and `o` genuinely differ, and an induction demanding
identical accumulators cannot get past its own first step. -/
theorem buildSelectiveRows_graph_invariant (bs bp bo : Option String)
    (need need' : ColNeed) (gc : Column) :
    ∀ (sVals pVals oVals sVals' pVals' oVals' : List (Nat × String))
      (indices : List Nat) (accRev accRev' : List QpRowTokSelective),
      accRev.map (fun r => r.g) = accRev'.map (fun r => r.g) →
      (buildSelectiveRows bs bp bo need gc sVals pVals oVals indices
        accRev).map (fun r => r.g)
        = (buildSelectiveRows bs bp bo need' gc sVals' pVals' oVals' indices
            accRev').map (fun r => r.g)
  | _, _, _, _, _, _, [], accRev, accRev', h => by
      simpa [buildSelectiveRows] using h
  | sVals, pVals, oVals, sVals', pVals', oVals', i :: rest, accRev, accRev', h => by
      rw [buildSelectiveRows, buildSelectiveRows]
      refine buildSelectiveRows_graph_invariant bs bp bo need need' gc _ _ _ _ _ _
        rest _ _ ?_
      simpa using h

/-- A BOUND position is filled from the bound's own token, with no
column read. -/
theorem selectiveRow_bound_position (bs bp bo : Option String)
    (need : ColNeed) (gc : Column) (tok : String) (hs : bs = some tok)
    (sVals pVals oVals : List (Nat × String)) (i : Nat) :
    ((buildSelectiveRows bs bp bo need gc sVals pVals oVals [i] []).head?).map
      (fun r => r.s) = some (some tok) := by
  rw [buildSelectiveRows, buildSelectiveRows]
  simp [advanceFor, hs]

/-! ## 6. One row group, and the walks -/

/-- Decode one column at exactly the requested indices, preferring the
indexed primitive and falling back to a full decode plus filter. Both
branches are correct; only the primitive's dictionary path is
accelerated. -/
def decodeIndexedOrFallback (indexed : Nat → Nat → List Nat →
      Option (List (Nat × String)))
    (rd : ColumnReader) (rg col : Nat) (indices : List Nat) :
    List (Nat × String) :=
  match indexed rg col indices with
  | some pairs => pairs
  | none =>
      match rd rg col with
      | none => []
      | some c => filterColumnByIndices c indices

def processRowGroupSelective (rd : ColumnReader)
    (indexed : Nat → Nat → List Nat → Option (List (Nat × String)))
    (bs bp bo bg : Option String) (need : ColNeed) (rg : Nat)
    (accRev : List QpRowTokSelective) : List QpRowTokSelective :=
  match rd rg 3 with
  | none => accRev
  | some gc =>
      let sc := if bs.isSome then rd rg 0 else none
      let pc := if bp.isSome then rd rg 1 else none
      let oc := if bo.isSome then rd rg 2 else none
      let boundOk := (bs.isNone || sc.isSome) && (bp.isNone || pc.isSome)
        && (bo.isNone || oc.isSome)
      if boundOk then
        let matched := (matchedIndicesSeq bs bp bo bg sc pc oc gc gc.size 0
          []).reverse
        let sVals := if bs.isNone && need.s then
            decodeIndexedOrFallback indexed rd rg 0 matched else []
        let pVals := if bp.isNone && need.p then
            decodeIndexedOrFallback indexed rd rg 1 matched else []
        let oVals := if bo.isNone && need.o then
            decodeIndexedOrFallback indexed rd rg 2 matched else []
        buildSelectiveRows bs bp bo need gc sVals pVals oVals matched accRev
      else accRev

def walkCandidatesSelective (rd : ColumnReader)
    (indexed : Nat → Nat → List Nat → Option (List (Nat × String)))
    (bs bp bo bg : Option String) (need : ColNeed) :
    List Nat → List QpRowTokSelective → List QpRowTokSelective
  | [], accRev => accRev
  | rg :: rest, accRev =>
      walkCandidatesSelective rd indexed bs bp bo bg need rest
        (processRowGroupSelective rd indexed bs bp bo bg need rg accRev)

/-- **`need` is a performance parameter, not a correctness one.**
Narrowing it changes neither how many rows come back nor their graph
values nor their order — only which bytes were read to fill the other
three positions. -/
theorem selectiveRows_need_invariant (rd : ColumnReader)
    (indexed indexed' : Nat → Nat → List Nat → Option (List (Nat × String)))
    (bs bp bo bg : Option String) (need need' : ColNeed) (rg : Nat)
    (accRev : List QpRowTokSelective) :
    (processRowGroupSelective rd indexed bs bp bo bg need rg accRev).map
      (fun r => r.g)
      = (processRowGroupSelective rd indexed' bs bp bo bg need' rg accRev).map
          (fun r => r.g) := by
  simp only [processRowGroupSelective]
  cases rd rg 3 with
  | none => rfl
  | some gc =>
      by_cases hb : ((bs.isNone || (if bs.isSome then rd rg 0 else none).isSome)
          && (bp.isNone || (if bp.isSome then rd rg 1 else none).isSome)
          && (bo.isNone || (if bo.isSome then rd rg 2 else none).isSome)) = true
      · simp only [hb, if_pos]
        exact buildSelectiveRows_graph_invariant bs bp bo need need' gc _ _ _ _ _ _
          _ accRev accRev rfl
      · simp only [hb, if_neg, Bool.not_eq_true] at *

/-! ## Build-time checks -/

private def vS : Column := #[some "<a:1>", some "<a:2>", some "<a:3>"]
private def vP : Column := #[some "<p:1>", some "<p:2>", some "<p:1>"]
private def vO : Column := #[some "<o:1>", some "<o:2>", some "<o:3>"]
private def vG : Column := #[some "DEFAULT", some "DEFAULT", some "DEFAULT"]

private def vCol : ColumnReader := fun rg col =>
  if rg == 0 then
    match col with
    | 0 => some vS
    | 1 => some vP
    | 2 => some vO
    | 3 => some vG
    | _ => none
  else none

/-- No indexed primitive available, so every decode falls back to a full
read plus filter. -/
private def noIndexed : Nat → Nat → List Nat → Option (List (Nat × String)) :=
  fun _ _ _ => none

/-! A predicate bound selects rows 0 and 2. -/
#guard (matchedIndicesSeq none (some "<p:1>") none none none (some vP) none vG
        3 0 []).reverse == [0, 2]
#guard (matchedIndicesSeq none (some "<p:9>") none none none (some vP) none vG
        3 0 []).reverse == ([] : List Nat)

/-! Filtering a decoded column by index keeps ascending order. -/
#guard filterColumnByIndices vO [0, 2] == [(0, "<o:1>"), (2, "<o:3>")]
#guard filterColumnByIndices vO [] == ([] : List (Nat × String))
#guard filterColumnByIndices vO [9] == ([] : List (Nat × String))

/-! The lockstep advance: hit, stale skip, and stop. -/
#guard valsAdvance [(0, "a"), (2, "b")] 0 == (some "a", [(2, "b")])
#guard valsAdvance [(0, "a"), (2, "b")] 2 == (some "b", ([] : List (Nat × String)))
#guard valsAdvance [(2, "b")] 1 == (none, [(2, "b")])
#guard (valsAdvance ([] : List (Nat × String)) 1).1 == (none : Option String)

/-! With the object needed, the selective search fills it. -/
#guard (processRowGroupSelective vCol noIndexed none (some "<p:1>") none none
        { s := false, p := false, o := true } 0 []).length == 2
#guard ((processRowGroupSelective vCol noIndexed none (some "<p:1>") none none
        { s := false, p := false, o := true } 0 []).reverse.map (fun r => r.o))
        == [some "<o:1>", some "<o:3>"]

/-! ⚠️ With the object NOT needed, the same rows come back and the object
position is `none` — which means "never decoded", not "no value". -/
#guard (processRowGroupSelective vCol noIndexed none (some "<p:1>") none none
        { s := false, p := false, o := false } 0 []).length == 2
#guard ((processRowGroupSelective vCol noIndexed none (some "<p:1>") none none
        { s := false, p := false, o := false } 0 []).reverse.map (fun r => r.o))
        == [none, none]

/-! A bound position is filled from the bound's own token, with no
column read. -/
#guard ((processRowGroupSelective vCol noIndexed none (some "<p:1>") none none
        { s := false, p := false, o := false } 0 []).reverse.map (fun r => r.p))
        == [some "<p:1>", some "<p:1>"]

/-! The graph position is never gated. -/
#guard ((processRowGroupSelective vCol noIndexed none (some "<p:1>") none none
        { s := false, p := false, o := false } 0 []).reverse.map (fun r => r.g))
        == ["DEFAULT", "DEFAULT"]

/-! Same rows as the plain search: two matches either way. -/
#guard (filterTokSeq none (some "<p:1>") none none vS vP vO vG 3 0 []).length == 2

/-! A row group that does not decode contributes nothing, same as every
other walk in this port. -/
#guard (processRowGroupSelective vCol noIndexed none none none none
        colNeedAll 1 []).length == 0
#guard (walkCandidatesSelective vCol noIndexed none none none none colNeedAll
        [0] []).length == 3

/-! ## Axiom audit -/

#print axioms matched_iff_rowSelected
#print axioms buildSelectiveRows_length
#print axioms buildSelectiveRows_graph_invariant
#print axioms selectiveRows_need_invariant
#print axioms valsAdvance_skips_stale
#print axioms valsAdvance_stops_above

end L4Factoidal.Cottas.OnDiskStore
