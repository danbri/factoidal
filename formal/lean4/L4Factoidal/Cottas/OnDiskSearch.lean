/-
L4Factoidal.Cottas.OnDiskSearch — layer 6 of the port of
`RDF.CottasStore`: the public entry points.

Layers 1 to 5 built the parts. This layer is `cottas_ondisk_search_tok`,
`cottas_ondisk_search_limited_tok` and `cottas_ondisk_estimate_tok` — the
three functions `SPARQL11.Store` actually calls — plus the row-to-quad
conversions that turn a matched row back into RDF.

## What the whole path has to be worth

Every layer below this one exists to avoid reading bytes: the dictionary
prune, the subject-offset prune, the compound predicate-object bitmap,
the candidate walk, the early exit. All of it is a bet that reading less
gives the same answer. `searchTok_eq_fullScan` is that bet settled: under
prunes that only drop row groups holding no match, the pruned search
returns exactly what an unpruned scan of every row group returns.

That statement is what makes the speed work safe to continue. A future
prune is correct if and only if it satisfies `PruneSound`, and nothing
else about it has to be re-argued.

## The two prunes this layer takes as parameters

`filter_candidates_by_compound_po` and
`cottas_ondisk_subject_candidate_rgs` both read companion sidecar files
(`.po.presence`, `.s.offsets`, `.p.dict`, `.o.dict`). They are I/O, so
they are fields of `StoreIo` here, and the property each must have is
`PruneSound`. The F\* source argues both are sound in prose — the
subject prune's banner runs to twenty lines about why the row range is
graph-independent — and prose is where that argument stays. Here it is a
hypothesis with a name, discharged by whoever supplies the reader.

⚠️ `compound_po_dict_encode` carries a trap the F\* source documents at
length and this port does NOT re-litigate: the compound bitmap's ids
come from the `.p.dict` / `.o.dict` sorted-rank id space, NOT from
`ondisk_lookup_*_id_global`'s first-occurrence-order space. Mixing them
prunes the one row group that holds the pair — a wrong `0`, not a slow
query. Modelling the prune as an opaque `List Nat → List Nat` keeps that
choice outside the port, where it belongs, rather than transcribing an
id-space confusion into a second tree.

## The estimate is an estimate

`estimateTok` multiplies the candidate count by the average rows per row
group. It is NOT the count, and `RDF/StoreCapabilitiesCottas.lean`
already advertises `estimateIsExact := false` for this backend. A
`#guard` shows a case where the estimate and the count differ, so nobody
reads the name as a promise.

No `sorry`, no user `axiom`, no `native_decide`.
-/
import L4Factoidal.Cottas.OnDiskPlan

namespace L4Factoidal.Cottas.OnDiskStore

open L4Factoidal.RDF
open L4Factoidal.Cottas.Ballyhoo

/-! ## 1. Everything the entry points read -/

/-- The store's I/O surface, as one record. Each field is an
`assume val` in the F\* tree. -/
structure StoreIo where
  /-- `probe_parquet_row_group_count`. -/
  rowGroupCount : Option Nat
  /-- `probe_parquet_num_rows`. -/
  numRows : Option Nat
  /-- The four-column decode, per row group. -/
  column : ColumnReader
  /-- The dictionary-page read, per row group and column. -/
  dict : DictReader
  /-- `cottas_ondisk_subject_candidate_rgs`: `none` means not eligible,
  sidecar absent, or footer doubt — the caller keeps its candidate set
  unchanged. -/
  subjectRgs : Option String → Nat → Option (List Nat)
  /-- `filter_candidates_by_compound_po`: takes the candidate list and
  the predicate and object bounds, and returns a possibly shorter list.
  Returns its input unchanged when either bound is absent or the
  companion file is missing. -/
  compoundPo : List Nat → Option String → Option String → List Nat

/-- The token-shaped bound. Port of `cottas_bound_qp_tok`. -/
structure BoundQpTok where
  s : Option String := none
  p : Option String := none
  o : Option String := none
  /-- `some "DEFAULT"` for default-graph scope, `some "<iri>"` for a
  named graph, `none` only on the dead unbound path. -/
  g : Option String := none
deriving DecidableEq, Repr, Inhabited

/-- Build a bound from the query's typed terms and a graph scope. No
dictionary lookup and no "term absent from the corpus" branch:
serialisation always succeeds, and a term genuinely absent still yields
zero matches cheaply through the dictionary-page prune. -/
def buildBoundQpTok (s : Option Subject) (p : Option WfIri) (o : Option Term)
    (scope : GraphScope) : BoundQpTok where
  s := s.map boundSubjectToToken
  p := p.map boundPredicateToToken
  o := o.map boundObjectToToken
  g := match scope with
    | .defaultOnly => some "DEFAULT"
    | .namedGraph gv => some (boundGraphIriToToken gv)

def BoundQpTok.anyPresent (b : BoundQpTok) : Bool :=
  b.s.isSome || b.p.isSome || b.o.isSome || b.g.isSome

/-! ## 2. Planning, with both prunes applied

Port of the candidate chain inside `cottas_ondisk_search_tok`: the
dictionary-page plan, then the subject-offset intersection, then the
compound predicate-object filter. -/

def planWithPrunes (io : StoreIo) (b : BoundQpTok) (rgCount : Nat) :
    List Nat :=
  let cands0 := (planCandidateRgs io.dict b.s b.p b.o b.g rgCount).cands
  let cands1 := match io.subjectRgs b.s rgCount with
    | none => cands0
    | some subjRgs => intersectSortedRgLists cands0 subjRgs
  io.compoundPo cands1 b.p b.o

/-! ## 3. The entry points -/

def searchTok (io : StoreIo) (b : BoundQpTok) : List QpRowTok :=
  match io.rowGroupCount with
  | none => []
  | some rgCount =>
      if b.anyPresent then
        (walkCandidatesTok io.column b.s b.p b.o b.g
          (planWithPrunes io b rgCount) []).reverse
      else
        (walkRangeTok io.column b.s b.p b.o b.g 0 rgCount rgCount []).reverse

def searchLimitedTok (io : StoreIo) (b : BoundQpTok) (limit : Nat) :
    List QpRowTok :=
  match io.rowGroupCount with
  | none => []
  | some rgCount =>
      if b.anyPresent then
        (walkCandidatesLimitedTok io.column b.s b.p b.o b.g
          (planWithPrunes io b rgCount) [] 0 limit).reverse
      else
        (walkCandidatesLimitedTok io.column b.s b.p b.o b.g
          (allRgs rgCount) [] 0 limit).reverse

/-- ⚠️ An ESTIMATE. With no bound it reports the file's row count; with
a bound it multiplies candidate row groups by the average rows per row
group. `RDF/StoreCapabilitiesCottas.lean` advertises
`estimateIsExact := false` for this backend, and `estimate_not_count`
below exhibits a case where the two differ. -/
def estimateTok (io : StoreIo) (b : BoundQpTok) : Nat :=
  if !b.anyPresent then
    match io.numRows with
    | some n => n
    | none =>
        match io.rowGroupCount with
        | none => 0
        | some rgCount =>
            walkRangeCount io.column b.s b.p b.o b.g 0 rgCount rgCount 0
  else
    match io.rowGroupCount with
    | none => 0
    | some rgCount =>
        let cands := planWithPrunes io b rgCount
        if cands.length = 0 then 0
        else if rgCount = 0 then 0
        else
          match io.numRows with
          | none => cands.length
          | some totalRows => cands.length * (totalRows / rgCount)

/-! ## 4. Rows back to RDF -/

def rowTokToQuad (row : QpRowTok) : Triple × Option Iri :=
  ({ s := tokenToSubject row.s
     p := tokenToPredicate row.p
     o := tokenToObject row.o },
   if row.g == "DEFAULT" then none else some (tokenToGraphName row.g))

def rowsTokToQuads (rows : List QpRowTok) : List (Triple × Option Iri) :=
  rows.map rowTokToQuad

def rowsTokToTriples (rows : List QpRowTok) : List Triple :=
  rows.map (fun r => (rowTokToQuad r).1)

theorem rowsTokToTriples_eq_map_quads (rows : List QpRowTok) :
    rowsTokToTriples rows = (rowsTokToQuads rows).map Prod.fst := by
  simp [rowsTokToTriples, rowsTokToQuads, List.map_map, Function.comp_def]

theorem rowTokToQuad_default (row : QpRowTok) (h : row.g = "DEFAULT") :
    (rowTokToQuad row).2 = none := by simp [rowTokToQuad, h]

/-! ## 5. What a sound prune is

The property the whole speed programme has to preserve, named once so a
future prune has something to satisfy. -/

/-- A candidate list is a sound prune of `full` when it is a sublist of
it and every row group it drops contributes no row. -/
def PruneSound (rd : ColumnReader) (bs bp bo bg : Option String)
    (cands full : List Nat) : Prop :=
  cands.Sublist full
    ∧ ∀ rg ∈ full, rg ∉ cands → rgStepTok rd bs bp bo bg rg [] = []

/-- Dropping row groups that contribute nothing does not change the
answer. Proved by induction on the sublist derivation; `Nodup` is what
rules out a skipped index reappearing later in the candidate list. -/
theorem walkCandidatesTok_sublist_eq (rd : ColumnReader)
    (bs bp bo bg : Option String) :
    ∀ {cands full : List Nat}, cands.Sublist full → full.Nodup →
      (∀ rg ∈ full, rg ∉ cands → rgStepTok rd bs bp bo bg rg [] = []) →
      walkCandidatesTok rd bs bp bo bg cands []
        = walkCandidatesTok rd bs bp bo bg full [] := by
  intro cands full hsub
  induction hsub with
  | slnil => intro _ _; rfl
  | cons rg hsub ih =>
      rename_i c t
      intro hnd hdrop
      have hrgt : rg ∉ t := (List.nodup_cons.mp hnd).1
      have hct : c.Sublist t := hsub
      have hrgc : rg ∉ c := fun hx => hrgt (hct.subset hx)
      have hstep : rgStepTok rd bs bp bo bg rg [] = [] :=
        hdrop rg (List.mem_cons_self ..) hrgc
      show walkCandidatesTok rd bs bp bo bg c []
        = walkCandidatesTok rd bs bp bo bg (rg :: t) []
      rw [walkCandidatesTok, hstep]
      exact ih (List.nodup_cons.mp hnd).2
        (fun rg' hm hnc => hdrop rg' (List.mem_cons_of_mem _ hm) hnc)
  | cons_cons rg hsub ih =>
      rename_i c t
      intro hnd hdrop
      have hrgt : rg ∉ t := (List.nodup_cons.mp hnd).1
      show walkCandidatesTok rd bs bp bo bg (rg :: c) []
        = walkCandidatesTok rd bs bp bo bg (rg :: t) []
      rw [walkCandidatesTok, walkCandidatesTok,
          walkCandidatesTok_append rd bs bp bo bg c
            (rgStepTok rd bs bp bo bg rg []),
          walkCandidatesTok_append rd bs bp bo bg t
            (rgStepTok rd bs bp bo bg rg [])]
      rw [ih (List.nodup_cons.mp hnd).2 ?hd]
      case hd =>
        intro rg' hm hnc
        refine hdrop rg' (List.mem_cons_of_mem _ hm) ?_
        intro hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact hrgt hm
        · exact hnc hx'

/-- **The whole pruned path returns what the unpruned scan returns.**
Every layer below exists to read fewer bytes; this is the statement that
reading fewer bytes gives the same answer. -/
theorem searchTok_eq_fullScan (io : StoreIo) (b : BoundQpTok) (rgCount : Nat)
    (hrg : io.rowGroupCount = some rgCount)
    (hprune : PruneSound io.column b.s b.p b.o b.g
      (planWithPrunes io b rgCount) (List.range rgCount)) :
    searchTok io b
      = (walkRangeTok io.column b.s b.p b.o b.g 0 rgCount rgCount []).reverse := by
  obtain ⟨hsub, hdrop⟩ := hprune
  simp only [searchTok, hrg]
  by_cases hb : b.anyPresent
  · simp only [hb, if_pos]
    rw [walkCandidatesTok_sublist_eq io.column b.s b.p b.o b.g hsub
          (List.nodup_range) hdrop,
        ← allRgs_eq_range, ← walkRange_eq_walkCandidates]
  · simp [hb]

/-- Soundness survives the entry point: every row the search returns
matches all four bounds. -/
theorem searchTok_sound (io : StoreIo) (b : BoundQpTok) (r : QpRowTok)
    (h : r ∈ searchTok io b) :
    cellMatch b.s r.s = true ∧ cellMatch b.p r.p = true
      ∧ cellMatch b.o r.o = true ∧ graphCellMatch b.g r.g = true := by
  simp only [searchTok] at h
  cases hrg : io.rowGroupCount with
  | none => rw [hrg] at h; simp at h
  | some rgCount =>
      rw [hrg] at h
      simp only at h
      by_cases hb : b.anyPresent
      · rw [if_pos hb, List.mem_reverse] at h
        exact walkCandidatesTok_sound io.column b.s b.p b.o b.g _ [] r
          (by simp) h
      · rw [if_neg hb, List.mem_reverse,
            walkRange_eq_walkCandidates] at h
        exact walkCandidatesTok_sound io.column b.s b.p b.o b.g _ [] r
          (by simp) h

/-- LIMIT at the entry point: the limited search is the unlimited search
truncated. -/
theorem searchLimitedTok_prefix (io : StoreIo) (b : BoundQpTok)
    (rgCount limit : Nat) (hrg : io.rowGroupCount = some rgCount) :
    searchLimitedTok io b limit
      = (searchTok io b).take limit := by
  simp only [searchLimitedTok, searchTok, hrg]
  by_cases hb : b.anyPresent
  · simp only [hb, if_pos]
    have h := walkCandidatesLimitedTok_prefix io.column b.s b.p b.o b.g
      (planWithPrunes io b rgCount) [] limit (by simp)
    simpa using h
  · simp only [hb, if_neg, Bool.not_eq_true] at *
    rw [walkRange_eq_walkCandidates]
    have h := walkCandidatesLimitedTok_prefix io.column b.s b.p b.o b.g
      (allRgs rgCount) [] limit (by simp)
    simpa using h

/-! ## Build-time checks -/

private def sS : Column := #[some "<a:1>", some "<a:2>"]
private def sP : Column := #[some "<p:1>", some "<p:1>"]
private def sO : Column := #[some "<o:1>", some "<o:2>"]
private def sG : Column := #[some "DEFAULT", some "DEFAULT"]

private def sCol : ColumnReader := fun rg col =>
  if rg < 2 then
    match col with
    | 0 => some sS
    | 1 => some sP
    | 2 => some sO
    | 3 => some sG
    | _ => none
  else none

/-- Row group 0's subject dictionary lists `<a:1>` and `<a:2>`;
row group 1's lists neither. -/
private def sDict : DictReader := fun rg col =>
  if col == 0 then
    match rg with
    | 0 => some ["<a:1>", "<a:2>"]
    | 1 => some ["<a:9>"]
    | _ => none
  else none

private def io0 : StoreIo :=
  { rowGroupCount := some 2, numRows := some 4, column := sCol, dict := sDict,
    subjectRgs := fun _ _ => none,
    compoundPo := fun cands _ _ => cands }

/-! No bound: every row of both row groups. -/
#guard (searchTok io0 {}).length == 4

/-! A subject bound prunes row group 1 by its dictionary, and the rows
returned are the matching ones — in ROW order, the caller's flip
applied. -/
#guard (searchTok io0 { s := some "<a:1>" }).length == 1
#guard ((searchTok io0 { s := some "<a:1>" }).map (fun r => r.o)) == ["<o:1>"]
#guard (searchTok io0 { s := some "<a:2>" }).length == 1

/-! A bound no row carries returns nothing. -/
#guard (searchTok io0 { s := some "<a:9>" }).length == 0

/-! A default-graph bound keeps both rows; a named-graph bound keeps
none, because this store has only default rows. -/
#guard (searchTok io0 { g := some "DEFAULT" }).length == 4
#guard (searchTok io0 { g := some "<g:1>" }).length == 0

/-! A missing footer answers empty rather than failing. -/
#guard (searchTok { io0 with rowGroupCount := none } {}).length == 0

/-! LIMIT truncates, and takes the FIRST rows. -/
#guard (searchLimitedTok io0 {} 3).length == 3
#guard searchLimitedTok io0 {} 3 == (searchTok io0 {}).take 3
#guard (searchLimitedTok io0 {} 99).length == 4

/-! ⚠️ The estimate is not the count. With the subject bound the search
returns 1 row; the estimate reports 2, because it multiplies one
candidate row group by two average rows. -/
#guard (searchTok io0 { s := some "<a:1>" }).length == 1
#guard estimateTok io0 { s := some "<a:1>" } == 2

/-! With no bound the estimate reads the file's row count directly. -/
#guard estimateTok io0 {} == 4

/-! Rows back to RDF: the DEFAULT sentinel becomes "no graph". -/
private def exIri : WfIri := ⟨"http://example.org/a", by decide⟩
private def rowDefault : QpRowTok :=
  { s := "<http://example.org/a>", p := "<http://example.org/a>"
    o := "<http://example.org/a>", g := "DEFAULT" }
private def rowNamed : QpRowTok :=
  { rowDefault with g := "<http://example.org/a>" }

#guard (rowTokToQuad rowDefault).2 == (none : Option Iri)
#guard (rowTokToQuad rowNamed).2 == some "http://example.org/a"
#guard (rowTokToQuad rowDefault).1
        == ({ s := .iri exIri, p := exIri, o := .iri exIri } : Triple)
#guard rowsTokToTriples [] == ([] : List Triple)

/-! A bound built from typed terms round-trips through the decoder. -/
#guard (buildBoundQpTok (some (.iri exIri)) none none .defaultOnly).s
        == some "<http://example.org/a>"
#guard (buildBoundQpTok none none none .defaultOnly).g == some "DEFAULT"
#guard (buildBoundQpTok none none none (.namedGraph "http://example.org/a")).g
        == some "<http://example.org/a>"
#guard ! (buildBoundQpTok none none none .defaultOnly).anyPresent == false

/-! ## Axiom audit -/

#print axioms walkCandidatesTok_sublist_eq
#print axioms searchTok_eq_fullScan
#print axioms searchTok_sound
#print axioms searchLimitedTok_prefix
#print axioms rowsTokToTriples_eq_map_quads

end L4Factoidal.Cottas.OnDiskStore
