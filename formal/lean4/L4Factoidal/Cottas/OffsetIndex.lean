/-
L4Factoidal.Cottas.OffsetIndex — the `.p.offsets` reader.

Port of `formal/fstar/RDF.Store.Columnar.OffsetIndex.fst` (408 lines).
The reader for the file `Cottas/OffsetsWriter.lean` writes: per
`(row group, predicate)`, the ascending row positions inside that row
group whose predicate token is that predicate.

## The I/O, at the edge

The F\* reader composes `OnDiskIndex.fst`'s `read_companion_u32_le` /
`read_companion_u64_le` / `mmap_companion_open` `assume val`s. Here the
handle holds a `ByteArray` that `openOffsets` read once, and the header
parser is shared with the writer module, so the two halves cannot drift
apart about the layout.

## Safe-direction defaults

`none` and `noInfo` mean "no information, run the full predicate-column
decode" — an over-include, always sound. `empty` is the decisive answer
that earns the index its place: no row in this row group carries this
predicate, so the caller may skip the row group's subject and object
decode for the pattern.

| Situation | Answer |
|---|---|
| `rg` or `pred` out of range | `none` → `noInfo` |
| an index entry unreadable | `none` → `noInfo` |
| end before start | `none` → `noInfo` |
| predicate unbound in the pattern | `noInfo` |
| companion absent or header invalid | `noInfo` |
| count zero | `empty` — decisive |

## ⚠️ The F\* soundness predicate is weaker than its comment

`offsets_built_correctly`'s comment says the file is built correctly
when "the cell's start_off + count + the count successful u32 reads at
start_off..start_off+4*(count-1) yield exactly that ground-truth list".
The predicate itself says only

```
cv.cv_count = FStar.List.Tot.length (rows_with_pred rg p)
```

— the COUNT matches, and nothing about the positions read. A file whose
counts are right and whose row positions are all wrong satisfies it.

`OffsetsBuiltCorrectly` below is the faithful port of the predicate, so
`rowPositionsFor_count_sound` is the same theorem the F\* module has.
The stronger property is stated separately as
`OffsetsBuiltCorrectlyStrong` — the read positions equal the ground
truth, which is what the comment describes — and the fixture is checked
against it by `#guard`, so the difference is visible rather than
implied.
-/
import L4Factoidal.Cottas.OffsetsWriter

namespace L4Factoidal.Cottas

def offsetIndexEntrySize : Nat := 8       -- u64 each
def offsetRowPositionSize : Nat := 4      -- u32 each

/-- `(data-section start byte offset, count of u32 row positions)`. -/
structure CellView where
  start : Nat
  count : Nat
  deriving Repr, DecidableEq, Inhabited

/-- Defensive against a malformed index: an end before its start is a
    count of zero rather than an underflow. -/
def rowPositionsCountFromBounds (startOff endOff : Nat) : Nat :=
  if endOff < startOff then 0 else (endOff - startOff) / offsetRowPositionSize

def cellIndex (h : OffsetsHandle) (rg predId : Nat) : Nat :=
  rg * h.header.numPreds + predId

def readRowPositionAt (h : OffsetsHandle) (startOff i : Nat) : Option Nat :=
  (readU32Le h.bytes (startOff + offsetRowPositionSize * i)).map UInt32.toNat

/-- `none` on an out-of-range coordinate, an unreadable index entry, or
    an end before its start. -/
def rowPositionsFor (h : OffsetsHandle) (rg predId : Nat) : Option CellView :=
  if rg ≥ h.header.numRgs || predId ≥ h.header.numPreds then none
  else
    let i := cellIndex h rg predId
    match readIndexEntry h i, readIndexEntry h (i + 1) with
    | some startOff, some endOff =>
        if endOff < startOff then none
        else some { start := startOff,
                    count := rowPositionsCountFromBounds startOff endOff }
    | _, _ => none

/-- The cell's row positions, read out. `none` if any read fails. -/
def rowPositionsList (h : OffsetsHandle) (rg predId : Nat) : Option (List Nat) :=
  match rowPositionsFor h rg predId with
  | none    => none
  | some cv => (List.range cv.count).mapM (readRowPositionAt h cv.start)

inductive CellDecision where
  | noInfo                      -- run the full predicate-column decode
  | empty                       -- decisive: skip this row group
  | use (cv : CellView)
  deriving Repr, DecidableEq, Inhabited

def rowPositionsForOpt (oh : Option OffsetsHandle) (rg : Nat)
    (boundPredId : Option Nat) : CellDecision :=
  match boundPredId, oh with
  | none, _ => .noInfo
  | _, none => .noInfo
  | some p, some h =>
      if !h.header.ok then .noInfo
      else match rowPositionsFor h rg p with
           | none    => .noInfo
           | some cv => if cv.count == 0 then .empty else .use cv

def offsetNumRgs (h : OffsetsHandle) : Nat := h.header.numRgs
def offsetNumPreds (h : OffsetsHandle) : Nat := h.header.numPreds

/-- `<corpus>.p.offsets`, sibling of `.p.dict` and `.p.presence`. -/
def offsetsPathOf (corpusPath : String) : String := corpusPath ++ ".p.offsets"

/-! ## Soundness -/

def RowsWithPred := Nat → Nat → List Nat

/-- The faithful port of F\*'s `offsets_built_correctly`: the COUNT
    matches the ground truth. It says nothing about which positions are
    stored. -/
def OffsetsBuiltCorrectly (h : OffsetsHandle) (rowsWithPred : RowsWithPred) :
    Prop :=
  ∀ rg p, rg < h.header.numRgs → p < h.header.numPreds →
    ∃ cv, rowPositionsFor h rg p = some cv ∧
          cv.count = (rowsWithPred rg p).length

/-- What the F\* comment describes: the positions read ARE the ground
    truth. Strictly stronger, and not what the F\* predicate says. -/
def OffsetsBuiltCorrectlyStrong (h : OffsetsHandle)
    (rowsWithPred : RowsWithPred) : Prop :=
  ∀ rg p, rg < h.header.numRgs → p < h.header.numPreds →
    rowPositionsList h rg p = some (rowsWithPred rg p)

/-- A count of zero from a correctly built file means the row group
    really holds no row with that predicate, so skipping it is sound. -/
theorem rowPositionsFor_count_sound (h : OffsetsHandle)
    (rowsWithPred : RowsWithPred) (rg p : Nat) (cv : CellView)
    (hbuilt : OffsetsBuiltCorrectly h rowsWithPred)
    (hrg : rg < h.header.numRgs) (hp : p < h.header.numPreds)
    (hcv : rowPositionsFor h rg p = some cv)
    (hzero : cv.count = 0) :
    rowsWithPred rg p = [] := by
  obtain ⟨cv', hcv', hcount⟩ := hbuilt rg p hrg hp
  rw [hcv] at hcv'
  have : cv' = cv := by injection hcv' with hh; exact hh.symm
  subst this
  rw [hzero] at hcount
  exact List.eq_nil_of_length_eq_zero hcount.symm

theorem rowPositionsForOpt_noInfo_when_handle_absent (rg : Nat)
    (boundPredId : Option Nat) :
    rowPositionsForOpt none rg boundPredId = .noInfo := by
  cases boundPredId <;> rfl

theorem rowPositionsForOpt_noInfo_when_pred_unbound (oh : Option OffsetsHandle)
    (rg : Nat) : rowPositionsForOpt oh rg none = .noInfo := by
  cases oh <;> rfl

/-! ## Build-time checks

The fixture is built by the writer, so these check the two halves
against each other. Row group 0 holds predicate 0 at rows 1 and 4 and
predicate 2 at row 7; row group 1 holds predicate 1 at row 2. Every
other cell is empty. -/

private def pixBytes : ByteArray :=
  (buildOffsets 2 3 [[1, 4], [], [7], [], [2], []]).getD ByteArray.empty

private def pix : OffsetsHandle :=
  (openOffsetsBytes pixBytes).getD ⟨ByteArray.empty, default⟩

#guard offsetNumRgs pix == 2
#guard offsetNumPreds pix == 3

#guard (rowPositionsFor pix 0 0).map (·.count) == some 2
#guard (rowPositionsFor pix 0 1).map (·.count) == some 0
#guard (rowPositionsFor pix 0 2).map (·.count) == some 1
#guard (rowPositionsFor pix 1 1).map (·.count) == some 1
#guard (rowPositionsFor pix 2 0).isNone
#guard (rowPositionsFor pix 0 3).isNone

/-! The positions themselves, at their own coordinates. A reader that
    got the counts right and the offsets wrong would pass the count
    guards above and fail these. -/

#guard rowPositionsList pix 0 0 == some [1, 4]
#guard rowPositionsList pix 0 1 == some []
#guard rowPositionsList pix 0 2 == some [7]
#guard rowPositionsList pix 1 0 == some []
#guard rowPositionsList pix 1 1 == some [2]
#guard rowPositionsList pix 1 2 == some []

/-! ### The decision wrapper: `empty` is decisive, everything else is
    an over-include -/

/-! The data section starts at `16 + 8 * (2 * 3 + 1) = 72`, and cell
    `(0, 0)` is the first, so its view is `⟨72, 2⟩`. Written out rather
    than read back from the function under test. -/

#guard offsetsDataStart 2 3 == 72
#guard rowPositionsForOpt (some pix) 0 (some 0) == .use ⟨72, 2⟩
#guard rowPositionsForOpt (some pix) 0 (some 2) == .use ⟨72 + 8, 1⟩
#guard rowPositionsForOpt (some pix) 0 (some 1) == .empty
#guard rowPositionsForOpt (some pix) 1 (some 1) != .empty
#guard rowPositionsForOpt (some pix) 0 none == .noInfo
#guard rowPositionsForOpt none 0 (some 0) == .noInfo
#guard rowPositionsForOpt (some pix) 9 (some 0) == .noInfo

/-! A truncated file falls to `noInfo`, never to `empty`. Collapsing
    those two would turn a read failure into "skip this row group",
    which drops rows. -/

#guard rowPositionsForOpt
  (some { pix with bytes := pix.bytes.extract 0 offsetsHeaderSize }) 0 (some 0)
  == .noInfo

/-! ### Both soundness predicates are satisfiable, and they differ

`rowPositionsFor_count_sound` assumes `OffsetsBuiltCorrectly`. Here is
a file that satisfies it, checked cell by cell — so the theorem is
about something that exists. -/

private def pground : Nat → Nat → List Nat
  | 0, 0 => [1, 4]
  | 0, 2 => [7]
  | 1, 1 => [2]
  | _, _ => []

#guard (List.range 2).all (fun rg => (List.range 3).all (fun p =>
  match rowPositionsFor pix rg p with
  | some cv => cv.count == (pground rg p).length
  | none    => false))

/-! The fixture also satisfies the STRONGER property, the one the F\*
    comment describes and the F\* predicate does not state. -/

#guard (List.range 2).all (fun rg => (List.range 3).all (fun p =>
  rowPositionsList pix rg p == some (pground rg p)))

/-! And the two are genuinely different: this ground truth has the same
    counts everywhere and different positions, so it satisfies the
    count predicate and fails the strong one. -/

private def pgroundWrongPositions : Nat → Nat → List Nat
  | 0, 0 => [99, 98]
  | 0, 2 => [97]
  | 1, 1 => [96]
  | _, _ => []

#guard (List.range 2).all (fun rg => (List.range 3).all (fun p =>
  match rowPositionsFor pix rg p with
  | some cv => cv.count == (pgroundWrongPositions rg p).length
  | none    => false))
#guard !((List.range 2).all (fun rg => (List.range 3).all (fun p =>
  rowPositionsList pix rg p == some (pgroundWrongPositions rg p))))

/-! ### The path convention -/

#guard offsetsPathOf "/data/gene.cottas" == "/data/gene.cottas.p.offsets"

#print axioms rowPositionsFor_count_sound
#print axioms rowPositionsForOpt_noInfo_when_pred_unbound

end L4Factoidal.Cottas
