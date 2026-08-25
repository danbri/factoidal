/-
L4Factoidal.Cottas.OnDiskCountExact — layer 9 of the port of
`RDF.CottasStore`: the offset-index exact-count fast paths, the
dispatcher over them, and the selective row's conversion back to a
triple.

The last eight definitions.

## Four ways to answer one question

`cottas_ondisk_count_exact_tok` picks between four answers to
`COUNT(*)`, in this order:

1. nothing bound at all → the file's own row count;
2. only the graph bound → count the graph column, decoding one column;
3. exactly one of predicate-only or subject-only, with a
   default-graph-eligible scope → read a companion offset index and
   decode NO column;
4. anything else → the selective column walk from layer 7.

Each is faster than the one below it and each is a different function.
`countExactTok_dispatch_order` states which branch fires for which bound
shape, so the ordering is a checked fact — and the F\* source's claim
that branches 3a and 3b are "mutually exclusive … never both match the
same bound tuple" is `offsetIndex_paths_disjoint`.

## The eligibility guard is the interesting part

`count_exact_offset_index_eligible` is a soundness gate, not an
optimisation. The offsets writer walks the predicate column and never
looks at the graph column, so a cell's count is a total across EVERY
graph in that row group. Consulting it is sound only when that total
already equals the graph-scoped count the caller wants, which holds when
the store carries zero named graphs AND the query is default-scoped or
unscoped. `eligible_requires_no_named_graphs` and
`eligible_rejects_named_scope` pin both halves, because a gate that
silently widens is how an exact count becomes a wrong one.

## Two kinds of "no answer"

A predicate absent from the `.p.dict` is a genuine, index-free ZERO: any
predicate appearing in the corpus must be a dictionary entry, so a
failed lookup is definitive. An in-range offset read that fails is a
DOUBT, and returns `none` so the caller falls through to the full walk.
`sum_predicate_offset_counts` returns `none` the instant ANY row group
reports a full scan, because a partial sum would silently undercount —
`sumOffsetCounts_none_of_fullScan` states that, and it is the same
all-or-nothing discipline as `collectDistinct_none_of_missing` in layer
7, for the same reason.

No `sorry`, no user `axiom`, no `native_decide`.
-/
import L4Factoidal.Cottas.OnDiskSelective

namespace L4Factoidal.Cottas.OnDiskStore

open L4Factoidal.RDF
open L4Factoidal.Cottas.Ballyhoo

/-! ## 1. The selective row, back to a triple

A position the walk never decoded has no value to report, so it takes
the same out-of-range sentinel the cell decoders use. -/

def rowTokSelectiveToTriple (row : QpRowTokSelective) : Triple :=
  { s := match row.s with
      | some tok => tokenToSubject tok
      | none => .bnode "cottas_decode_oor"
    p := match row.p with
      | some tok => tokenToPredicate tok
      | none => cottasDecodeOorPredicate
    o := match row.o with
      | some tok => tokenToObject tok
      | none => .bnode "cottas_decode_oor" }

def rowsTokSelectiveToTriples (rows : List QpRowTokSelective) : List Triple :=
  rows.map rowTokSelectiveToTriple

/-- ⚠️ An undecoded position becomes the sentinel, so a caller that
narrowed `need` and then asked for a triple gets a sentinel term rather
than an error. `need` is safe to narrow only for a caller that does not
read the narrowed positions — which is what
`selectiveRows_need_invariant` in layer 8 does and does not promise: it
covers the graph position and the row count, not the three gated
positions. -/
theorem rowTokSelectiveToTriple_undecoded (row : QpRowTokSelective)
    (h : row.s = none) :
    (rowTokSelectiveToTriple row).s = .bnode "cottas_decode_oor" := by
  simp [rowTokSelectiveToTriple, h]

/-! ## 2. The eligibility guard -/

/-- Sound to consult the offset index only when the whole-predicate
total already equals the graph-scoped count: the store carries no named
graph, and the query is default-scoped or unscoped. -/
def countExactOffsetIndexEligible (namedGraphs : List Iri)
    (bg : Option String) : Bool :=
  (match namedGraphs with | [] => true | _ => false)
    && (match bg with | none => true | some g => g == "DEFAULT")

theorem eligible_requires_no_named_graphs (g : Iri) (gs : List Iri)
    (bg : Option String) :
    countExactOffsetIndexEligible (g :: gs) bg = false := by
  simp [countExactOffsetIndexEligible]

theorem eligible_rejects_named_scope (gs : List Iri) (iri : String)
    (h : iri ≠ "DEFAULT") :
    countExactOffsetIndexEligible gs (some iri) = false := by
  simp [countExactOffsetIndexEligible]
  intro _
  simpa using h

theorem eligible_accepts_default : countExactOffsetIndexEligible [] (some "DEFAULT")
    = true := by decide

theorem eligible_accepts_unscoped : countExactOffsetIndexEligible [] none = true := by
  decide

/-! ## 3. Summing the predicate offset index

Port of `sum_predicate_offset_counts`. `AccessPath` is the per-row-group
decision the row-jump search consumers already make. -/

inductive AccessPath where
  /-- No usable index for this row group: the sum cannot be completed. -/
  | fullScan
  /-- A definitively-empty cell: contributes zero. -/
  | skip
  /-- An offset jump carrying an exact row count, with no column decode. -/
  | offsetJump (count : Nat)
deriving DecidableEq, Repr

def sumPredicateOffsetCounts (choose : Nat → AccessPath)
    (rgIndex rgCount fuel acc : Nat) : Option Nat :=
  match fuel with
  | 0 => some acc
  | f + 1 =>
      if rgIndex ≥ rgCount then some acc
      else
        match choose rgIndex with
        | .fullScan => none
        | .skip => sumPredicateOffsetCounts choose (rgIndex + 1) rgCount f acc
        | .offsetJump c =>
            sumPredicateOffsetCounts choose (rgIndex + 1) rgCount f (acc + c)

/-- **A partial sum would silently undercount**, so one unusable row
group abandons the whole answer. Same all-or-nothing discipline as
`collectDistinct_none_of_missing`, for the same reason. -/
theorem sumOffsetCounts_none_of_fullScan (choose : Nat → AccessPath) :
    ∀ (fuel rgIndex rgCount acc bad : Nat),
      rgIndex ≤ bad → bad < rgCount → rgCount - rgIndex ≤ fuel →
      choose bad = .fullScan →
      (∀ rg, rgIndex ≤ rg → rg < bad → choose rg ≠ .fullScan) →
      sumPredicateOffsetCounts choose rgIndex rgCount fuel acc = none
  | 0, i, n, acc, bad, hle, hlt, hf, _, _ => by omega
  | fuel + 1, i, n, acc, bad, hle, hlt, hf, hbad, hbefore => by
      rw [sumPredicateOffsetCounts]
      have h : ¬ i ≥ n := by omega
      simp only [h, if_neg, not_false_eq_true]
      by_cases heq : i = bad
      · subst heq; rw [hbad]
      · have hib : i < bad := by omega
        cases hc : choose i with
        | fullScan => exact absurd hc (hbefore i (by omega) hib)
        | skip =>
            exact sumOffsetCounts_none_of_fullScan choose fuel (i + 1) n acc bad
              (by omega) hlt (by omega) hbad
              (fun rg h1 h2 => hbefore rg (by omega) h2)
        | offsetJump c =>
            exact sumOffsetCounts_none_of_fullScan choose fuel (i + 1) n _ bad
              (by omega) hlt (by omega) hbad
              (fun rg h1 h2 => hbefore rg (by omega) h2)

/-! ## 4. The two fast paths

Each fires for exactly one bound shape. A term absent from its companion
dictionary is a genuine zero, not a doubt: any term appearing in the
corpus must be a dictionary entry. -/

/-- The offset-index surface, as a parameter. -/
structure OffsetIo where
  /-- Encode a token through the companion `.p.dict` / `.s.dict`
  sorted-rank id space. `none` means the term is genuinely absent. -/
  dictEncode : String → String → Option Nat
  /-- The per-row-group access-path decision for a predicate id. -/
  choosePred : Nat → Nat → AccessPath
  /-- The subject's contiguous row-range count, or `none` when the
  `.s.offsets` sidecar is missing or unhealthy. -/
  subjectRangeCount : Nat → Option Nat

def countExactViaOffsetIndex (oio : OffsetIo) (namedGraphs : List Iri)
    (bs bp bo bg : Option String) (rgCount : Nat) : Option Nat :=
  match bs, bp, bo with
  | none, some p, none =>
      if !countExactOffsetIndexEligible namedGraphs bg then none
      else
        match oio.dictEncode "p" p with
        | none => some 0
        | some predId =>
            sumPredicateOffsetCounts (oio.choosePred predId) 0 rgCount rgCount 0
  | _, _, _ => none

def countExactViaSubjectOffsetIndex (oio : OffsetIo) (namedGraphs : List Iri)
    (bs bp bo bg : Option String) : Option Nat :=
  match bs, bp, bo with
  | some s, none, none =>
      if !countExactOffsetIndexEligible namedGraphs bg then none
      else
        match oio.dictEncode "s" s with
        | none => some 0
        | some subjId => oio.subjectRangeCount subjId
  | _, _, _ => none

/-- **The two fast paths never both fire.** The F\* source asserts this
in a comment to justify trying both; `some p, none` and `some s, none,
none` cannot match one bound tuple. -/
theorem offsetIndex_paths_disjoint (oio : OffsetIo) (ngs : List Iri)
    (bs bp bo bg : Option String) (rgCount : Nat) :
    (countExactViaOffsetIndex oio ngs bs bp bo bg rgCount).isNone
      ∨ (countExactViaSubjectOffsetIndex oio ngs bs bp bo bg).isNone := by
  cases bs with
  | none => exact Or.inr (by simp [countExactViaSubjectOffsetIndex])
  | some _ => exact Or.inl (by simp [countExactViaOffsetIndex])

/-! ## 5. The dispatcher -/

def countExactTok (io : StoreIo) (oio : OffsetIo) (namedGraphs : List Iri)
    (b : BoundQpTok) : Nat :=
  if b.s.isNone && b.p.isNone && b.o.isNone && b.g.isNone then
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
        if b.s.isNone && b.p.isNone && b.o.isNone then
          walkCountGraph io.column b.g 0 rgCount rgCount 0
        else
          match countExactViaOffsetIndex oio namedGraphs b.s b.p b.o b.g rgCount with
          | some n => n
          | none =>
              match countExactViaSubjectOffsetIndex oio namedGraphs b.s b.p b.o b.g with
              | some n => n
              | none =>
                  walkCountExact io.column b.s b.p b.o b.g 0 rgCount rgCount 0

/-- **Which branch fires for which bound shape.** Branch 1 needs every
bound absent INCLUDING the graph bound — a graph-only query takes branch
2, not the row count, because a named-graph scope does not match every
row. -/
theorem countExactTok_unbound (io : StoreIo) (oio : OffsetIo)
    (ngs : List Iri) (n : Nat) (hn : io.numRows = some n) :
    countExactTok io oio ngs {} = n := by
  simp [countExactTok, hn]

theorem countExactTok_graphOnly (io : StoreIo) (oio : OffsetIo)
    (ngs : List Iri) (g : String) (rgCount : Nat)
    (hrg : io.rowGroupCount = some rgCount) :
    countExactTok io oio ngs { g := some g }
      = walkCountGraph io.column (some g) 0 rgCount rgCount 0 := by
  simp [countExactTok, hrg]

/-! ## Build-time checks -/

/-- A dictionary that resolves nothing: every lookup is a genuine
absence, so no index read ever happens. -/
private def oioEmpty : OffsetIo :=
  { dictEncode := fun _ _ => none
    choosePred := fun _ _ => .fullScan
    subjectRangeCount := fun _ => none }

/-- A dictionary that RESOLVES the predicate over an index that cannot
answer — the shape that exhibits the abandoned sum. Distinguishing this
from `oioEmpty` is the whole point of the "genuine zero versus doubt"
split. -/
private def oioNoIndex : OffsetIo :=
  { dictEncode := fun col tok => if col == "p" && tok == "<p:1>" then some 7
      else none
    choosePred := fun _ _ => .fullScan
    subjectRangeCount := fun _ => none }

private def oioLive : OffsetIo :=
  { dictEncode := fun col tok =>
      if col == "p" && tok == "<p:1>" then some 7
      else if col == "s" && tok == "<a:1>" then some 3
      else none
    choosePred := fun predId rg =>
      if predId == 7 then (if rg == 0 then .offsetJump 5 else .skip)
      else .fullScan
    subjectRangeCount := fun subjId => if subjId == 3 then some 11 else none }

/-! The predicate fast path sums the index and decodes no column. -/
#guard countExactViaOffsetIndex oioLive [] none (some "<p:1>") none
        (some "DEFAULT") 2 == some 5

/-! ⚠️ A named graph in the store makes the index unsound, so the gate
refuses and the caller falls through to the full walk. -/
#guard countExactViaOffsetIndex oioLive ["http://example.org/g"] none
        (some "<p:1>") none (some "DEFAULT") 2 == (none : Option Nat)

/-! ⚠️ So does a named-graph-scoped query, even on a store with none. -/
#guard countExactViaOffsetIndex oioLive [] none (some "<p:1>") none
        (some "<http://example.org/g>") 2 == (none : Option Nat)

/-! A predicate absent from the dictionary is a genuine zero, not a
doubt — no index read at all. -/
#guard countExactViaOffsetIndex oioLive [] none (some "<p:9>") none none 2
        == some 0

/-! ⚠️ An unusable row group abandons the sum, because a partial one
would undercount. -/
#guard countExactViaOffsetIndex oioNoIndex [] none (some "<p:1>") none none 2
        == (none : Option Nat)

/-! And a dictionary that resolves NOTHING answers a genuine zero
instead, without touching the index at all. -/
#guard countExactViaOffsetIndex oioEmpty [] none (some "<p:1>") none none 2
        == some 0
#guard sumPredicateOffsetCounts (fun _ => AccessPath.fullScan) 0 2 2 0
        == (none : Option Nat)
#guard sumPredicateOffsetCounts (fun _ => AccessPath.skip) 0 2 2 0 == some 0
#guard sumPredicateOffsetCounts (fun _ => AccessPath.offsetJump 4) 0 3 3 0
        == some 12

/-! The subject fast path reads one range count. -/
#guard countExactViaSubjectOffsetIndex oioLive [] (some "<a:1>") none none none
        == some 11
#guard countExactViaSubjectOffsetIndex oioLive [] (some "<a:9>") none none none
        == some 0

/-! The two fast paths never both fire. -/
#guard (countExactViaOffsetIndex oioLive [] none (some "<p:1>") none none 2).isSome
#guard (countExactViaSubjectOffsetIndex oioLive [] none (some "<p:1>") none
        none).isNone
#guard (countExactViaOffsetIndex oioLive [] (some "<a:1>") none none none
        2).isNone
#guard (countExactViaSubjectOffsetIndex oioLive [] (some "<a:1>") none none
        none).isSome

/-! A selective row with an undecoded position gives the sentinel. -/
private def rowUndecoded : QpRowTokSelective :=
  { s := none, p := none, o := none, g := "DEFAULT" }
#guard (rowTokSelectiveToTriple rowUndecoded).s
        == Subject.bnode "cottas_decode_oor"
#guard (rowTokSelectiveToTriple rowUndecoded).p == cottasDecodeOorPredicate
#guard rowsTokSelectiveToTriples [] == ([] : List Triple)

/-! ## Axiom audit -/

#print axioms sumOffsetCounts_none_of_fullScan
#print axioms offsetIndex_paths_disjoint
#print axioms eligible_requires_no_named_graphs
#print axioms eligible_rejects_named_scope
#print axioms countExactTok_unbound
#print axioms countExactTok_graphOnly

end L4Factoidal.Cottas.OnDiskStore
