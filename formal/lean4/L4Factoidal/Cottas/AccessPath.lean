/-
L4Factoidal.Cottas.AccessPath — the access-path chooser.

Port of `formal/fstar/SPARQL.Plan.AccessPath.fst` (257 lines). Given
what a triple pattern binds and what the `.p.offsets` companion says,
pick the cheapest legal way to read one row group.

## Why it is in F\*, and now in Lean, rather than in a dispatcher

The F\* header records the history: the decision "if the predicate is
bound and the offsets companion is present, jump to the row positions,
otherwise decode the whole predicate column" used to live inside an
OCaml dispatcher that also BUILT the bytes. Iron rule #11 makes the
choice a backend correctness decision, so it belongs in the formal
source and the reader consumes a typed value.

## The three regimes

| Result | Meaning |
|---|---|
| `skip` | this row group cannot match — the decisive answer |
| `offsetJump cv` | read only `cv.count` row positions from `cv.start` |
| `fullScan` | no offset information; decode the predicate column |

`skip` is the one that saves work and the one that must be right;
`fullScan` is the over-include and is always sound.

| bound predicate | handle | index result | path |
|---|---|---|---|
| `none` | any | — | `fullScan` |
| `some _` | `none` | — | `fullScan` |
| `some p` | `some h` | `noInfo` | `fullScan` |
| `some p` | `some h` | `empty` | `skip` |
| `some p` | `some h` | `use cv` | `offsetJump cv` |

## Soundness

`skip` arises only from `rowPositionsForOpt` answering `empty`, which
arises only from a cell count of zero, which
`Cottas/OffsetIndex.lean`'s `rowPositionsFor_count_sound` turns into
"the row group holds no row with that predicate" for a correctly built
file. `chooseAccessPath_skip_sound` below states that chain as one
theorem, where the F\* module leaves it as a comment pointing at the
`OffsetIndex` lemma.
-/
import L4Factoidal.Cottas.OffsetIndex
import L4Factoidal.Cottas.PlanPruning

namespace L4Factoidal.Cottas

inductive AccessPath where
  | skip
  | offsetJump (cv : CellView)
  | fullScan
  deriving DecidableEq, Repr, Inhabited

/-- The per-row-group decision. -/
def chooseAccessPath (ohOffsets : Option OffsetsHandle) (rg : Nat)
    (boundPredId : Option Nat) : AccessPath :=
  match rowPositionsForOpt ohOffsets rg boundPredId with
  | .noInfo => .fullScan
  | .empty  => .skip
  | .use cv => .offsetJump cv

/-- The caller-shaped wrapper. Only the PREDICATE bound is consulted:
    the subject and object bounds belong to the prune decision, made
    before this, and to the post-jump filter at each row position. -/
def chooseAccessPathForPattern (ohOffsets : Option OffsetsHandle) (rg : Nat)
    (bounds : PatternBoundIds) : AccessPath :=
  chooseAccessPath ohOffsets rg bounds.p

/-- Per-row-group decisions over a candidate list, order preserved.
    `skip` results are KEPT: they carry information, namely that the
    row group contributes exactly zero rows to the estimate. -/
def chooseAccessPathsForRgs (ohOffsets : Option OffsetsHandle)
    (candidates : List Nat) (bounds : PatternBoundIds) :
    List (Nat × AccessPath) :=
  candidates.map (fun rg => (rg, chooseAccessPathForPattern ohOffsets rg bounds))

/-- Drop the `skip` entries. The execution layer wants the row groups
    it must actually read; the estimate layer wants the full list. -/
def dropSkips : List (Nat × AccessPath) → List (Nat × AccessPath)
  | [] => []
  | (rg, ap) :: tl => if ap == .skip then dropSkips tl else (rg, ap) :: dropSkips tl

/-! ## Properties -/

/-- With no companion open, every row group is a full scan — the
    baseline behaviour before the offset index existed. -/
theorem chooseAccessPath_no_handle_is_full_scan (rg : Nat)
    (boundPredId : Option Nat) :
    chooseAccessPath none rg boundPredId = .fullScan := by
  simp only [chooseAccessPath, rowPositionsForOpt_noInfo_when_handle_absent]

/-- An unbound predicate is a full scan: the index is keyed by
    predicate, so there is nothing to look up. -/
theorem chooseAccessPath_unbound_pred_is_full_scan
    (ohOffsets : Option OffsetsHandle) (rg : Nat) :
    chooseAccessPath ohOffsets rg none = .fullScan := by
  simp only [chooseAccessPath, rowPositionsForOpt_noInfo_when_pred_unbound]

theorem chooseAccessPathForPattern_unbound_pred_is_full_scan
    (ohOffsets : Option OffsetsHandle) (rg : Nat) (bounds : PatternBoundIds)
    (h : bounds.p = none) :
    chooseAccessPathForPattern ohOffsets rg bounds = .fullScan := by
  simp only [chooseAccessPathForPattern, h,
             chooseAccessPath_unbound_pred_is_full_scan]

/-- `dropSkips` is the identity on a list with no `skip`. -/
theorem dropSkips_identity_when_no_skips (xs : List (Nat × AccessPath))
    (h : ∀ p ∈ xs, p.2 ≠ .skip) : dropSkips xs = xs := by
  induction xs with
  | nil => rfl
  | cons x tl ih =>
      obtain ⟨rg, ap⟩ := x
      have hx : ap ≠ .skip := h (rg, ap) List.mem_cons_self
      have hb : (ap == AccessPath.skip) = false := by
        simp only [beq_eq_false_iff_ne]; exact hx
      simp only [dropSkips, hb, if_false, Bool.false_eq_true]
      exact congrArg _ (ih (fun p hp => h p (List.mem_cons_of_mem _ hp)))

/-- The soundness chain, stated once rather than left as a comment:
    a `skip` on a correctly built file means the row group really holds
    no row with that predicate. -/
theorem chooseAccessPath_skip_sound (h : OffsetsHandle)
    (rowsWithPred : RowsWithPred) (rg p : Nat)
    (hbuilt : OffsetsBuiltCorrectly h rowsWithPred)
    (hrg : rg < h.header.numRgs) (hp : p < h.header.numPreds)
    (hok : h.header.ok = true)
    (hskip : chooseAccessPath (some h) rg (some p) = .skip) :
    rowsWithPred rg p = [] := by
  simp only [chooseAccessPath, rowPositionsForOpt, hok, Bool.not_true] at hskip
  cases hcv : rowPositionsFor h rg p with
  | none => rw [hcv] at hskip; simp at hskip
  | some cv =>
      rw [hcv] at hskip
      by_cases hz : cv.count = 0
      · exact rowPositionsFor_count_sound h rowsWithPred rg p cv hbuilt hrg hp hcv hz
      · have hne : (cv.count == 0) = false := by simp [hz]
        simp only [hne, if_false, Bool.false_eq_true] at hskip
        exact absurd hskip (by simp)

/-! ## Build-time checks

The fixture is the one `Cottas/OffsetIndex.lean` uses: row group 0
holds predicate 0 at rows 1 and 4 and predicate 2 at row 7; row group 1
holds predicate 1 at row 2. Every other cell is empty, and the data
section starts at byte 72. -/

private def apix : OffsetsHandle :=
  (openOffsetsBytes ((buildOffsets 2 3 [[1, 4], [], [7], [], [2], []]).getD
    ByteArray.empty)).getD ⟨ByteArray.empty, default⟩

#guard chooseAccessPath (some apix) 0 (some 0) == .offsetJump ⟨72, 2⟩
#guard chooseAccessPath (some apix) 0 (some 1) == .skip
#guard chooseAccessPath (some apix) 0 (some 2) == .offsetJump ⟨72 + 8, 1⟩
#guard chooseAccessPath (some apix) 1 (some 1) == .offsetJump ⟨72 + 8 + 4, 1⟩

/-! Every path to `fullScan` — no handle, unbound predicate, an
    out-of-range row group, and a truncated file. None of them is
    `skip`, which is the direction that matters: a `skip` on missing
    information would drop rows. -/

#guard chooseAccessPath none 0 (some 0) == .fullScan
#guard chooseAccessPath (some apix) 0 none == .fullScan
#guard chooseAccessPath (some apix) 9 (some 0) == .fullScan
#guard chooseAccessPath
  (some { apix with bytes := apix.bytes.extract 0 offsetsHeaderSize }) 0 (some 0)
  == .fullScan

/-! The pattern-shaped wrapper reads the PREDICATE bound and no other.
    Two bounds records differing only in subject and object give the
    same path. -/

#guard chooseAccessPathForPattern (some apix) 0 (mkBounds none (some 1) none)
       == .skip
#guard chooseAccessPathForPattern (some apix) 0 (mkBounds (some 5) (some 1) (some 9))
       == .skip
#guard chooseAccessPathForPattern (some apix) 0 noBounds == .fullScan

/-! Over a candidate list: order preserved, `skip` kept, and
    `dropSkips` removing exactly those. -/

private def paths : List (Nat × AccessPath) :=
  chooseAccessPathsForRgs (some apix) [0, 1] (mkBounds none (some 1) none)

#guard paths.map (·.1) == [0, 1]
#guard paths.map (·.2) == [.skip, .offsetJump ⟨72 + 8 + 4, 1⟩]
#guard dropSkips paths == [(1, .offsetJump ⟨72 + 8 + 4, 1⟩)]
#guard dropSkips (chooseAccessPathsForRgs none [0, 1] (mkBounds none (some 1) none))
       == [(0, .fullScan), (1, .fullScan)]

#print axioms chooseAccessPath_skip_sound
#print axioms dropSkips_identity_when_no_skips

end L4Factoidal.Cottas
