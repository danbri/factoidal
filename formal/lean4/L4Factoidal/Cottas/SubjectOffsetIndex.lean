/-
L4Factoidal.Cottas.SubjectOffsetIndex — the `.s.offsets` reader.

Port of `formal/fstar/RDF.Store.Columnar.SubjectOffsetIndex.fst` (260
lines). The reader for the file `Cottas/SubjectOffsetsWriter.lean`
writes.

`BaseWriter` sorts rows by `(s, p, o, g)`, subject primary, so every
row with a given subject occupies one CONTIGUOUS global row range. This
index records `[start, end)` per subject.

## The I/O, at the edge again

The F\* reader reaches bytes through `OnDiskIndex.fst`'s
`read_companion_u32_le` / `read_companion_u64_le` `assume val`s over an
mmap. Here the handle already holds a `ByteArray` — `openSubjectOffsets`
in the writer module reads the file once — so the header parser and the
range lookup are shared with the writer rather than written twice, and
the two halves cannot drift apart in their idea of the layout.

## The decision wrapper, and why three answers collapse to two

`rangeForSubjectOpt` is what callers use. `noInfo` means the caller
must fall through to the dictionary-page probing path
(`plan_candidate_rgs`); `use r` means the range is authoritative. Every
failure — companion absent, header invalid, subject unbound,
out-of-range id, read error — is `noInfo`, which over-includes and is
the safe direction.

The F\* module's comment notes that an out-of-range subject id is kept
distinct from "no info" in principle while today's only caller treats
them the same. It is one constructor here, and the reason is written
down: nothing in the tree consumes the distinction, and a constructor
no caller reads is a claim that the reader can tell two situations
apart when nothing acts on the difference. `rangeForSubject` still
returns `none` for the two cases separately, so a future caller that
wants them can have them without changing this type.
-/
import L4Factoidal.Cottas.SubjectOffsetsWriter

namespace L4Factoidal.Cottas

/-- The contiguous global row range `[start, end)` of one subject. -/
structure SubjectRange where
  start : Nat
  stop  : Nat
  deriving Repr, DecidableEq, Inhabited

/-- An end before its start counts as empty rather than as an
    underflow — the same defensive reading the writer module's
    `subjectRowCount` uses. -/
def subjectRangeCount (r : SubjectRange) : Nat :=
  if r.stop < r.start then 0 else r.stop - r.start

def subjectOffsetEntrySize : Nat := 16

def entryOffset (subjectId : Nat) : Nat :=
  subjectOffsetsHeaderSize + subjectOffsetEntrySize * subjectId

/-- `none` for an out-of-range subject id and for a read failure. -/
def rangeForSubject (h : SubjectOffsetsHandle) (subjectId : Nat) :
    Option SubjectRange :=
  if subjectId ≥ h.header.numSubjects then none
  else do
    let s ← readU64Le h.bytes (entryOffset subjectId)
    let e ← readU64Le h.bytes (entryOffset subjectId + 8)
    some { start := s, stop := e }

inductive SubjectRangeDecision where
  | noInfo                          -- fall through to plan_candidate_rgs
  | use (r : SubjectRange)
  deriving Repr, DecidableEq, Inhabited

def rangeForSubjectOpt (oh : Option SubjectOffsetsHandle)
    (subjectId : Option Nat) : SubjectRangeDecision :=
  match subjectId, oh with
  | none, _ => .noInfo                       -- unbound subject
  | _, none => .noInfo                       -- companion not open
  | some sid, some h =>
      if !h.header.ok then .noInfo
      else match rangeForSubject h sid with
           | none   => .noInfo
           | some r => .use r

def subjectOffsetNumSubjects (h : SubjectOffsetsHandle) : Nat :=
  h.header.numSubjects

/-- `<corpus>.s.offsets`, sibling of `.s.dict` and `.s.presence`. -/
def subjectOffsetsPathOf (corpusPath : String) : String :=
  corpusPath ++ ".s.offsets"

/-! ## Soundness

`rowsWithSubject sid` is the ground truth: the ascending global row
indices whose subject has dictionary rank `sid`. -/

def RowsWithSubject := Nat → List Nat

def SubjectOffsetsBuiltCorrectly (h : SubjectOffsetsHandle)
    (rowsWithSubject : RowsWithSubject) : Prop :=
  ∀ sid, sid < h.header.numSubjects →
    ∃ r, rangeForSubject h sid = some r ∧
         subjectRangeCount r = (rowsWithSubject sid).length

/-- A count of zero from a correctly built file means the subject
    really owns no rows. -/
theorem rangeForSubject_count_sound (h : SubjectOffsetsHandle)
    (rowsWithSubject : RowsWithSubject) (sid : Nat) (r : SubjectRange)
    (hbuilt : SubjectOffsetsBuiltCorrectly h rowsWithSubject)
    (hlt : sid < h.header.numSubjects)
    (hr : rangeForSubject h sid = some r)
    (hzero : subjectRangeCount r = 0) :
    rowsWithSubject sid = [] := by
  obtain ⟨r', hr', hcount⟩ := hbuilt sid hlt
  rw [hr] at hr'
  have : r' = r := by injection hr' with hh; exact hh.symm
  subst this
  rw [hzero] at hcount
  exact List.eq_nil_of_length_eq_zero hcount.symm

theorem rangeForSubjectOpt_noInfo_when_handle_absent (subjectId : Option Nat) :
    rangeForSubjectOpt none subjectId = .noInfo := by
  cases subjectId <;> rfl

theorem rangeForSubjectOpt_noInfo_when_subject_unbound
    (oh : Option SubjectOffsetsHandle) :
    rangeForSubjectOpt oh none = .noInfo := by
  cases oh <;> rfl

/-! ## Build-time checks

### A real file, read back through the index

The fixture is the one the writer builds, so these check the two halves
against each other rather than against a restatement of the format. -/

private def ixBytes : ByteArray :=
  (buildSubjectOffsets 4 12 [(0, 4), (4, 4), (4, 9), (9, 12)]).getD ByteArray.empty

private def ix : SubjectOffsetsHandle :=
  (openSubjectOffsetsBytes ixBytes).getD ⟨ByteArray.empty, default⟩

#guard rangeForSubject ix 0 == some ⟨0, 4⟩
#guard rangeForSubject ix 1 == some ⟨4, 4⟩
#guard rangeForSubject ix 2 == some ⟨4, 9⟩
#guard rangeForSubject ix 3 == some ⟨9, 12⟩
#guard (rangeForSubject ix 4).isNone

#guard subjectRangeCount ⟨0, 4⟩ == 4
#guard subjectRangeCount ⟨4, 4⟩ == 0
#guard subjectRangeCount ⟨9, 4⟩ == 0          -- end before start: empty
#guard subjectOffsetNumSubjects ix == 4

/-! The ranges tile the row space with no gap and no overlap, which is
    what "subject-primary global sort" means and what makes one range
    per subject exact. -/

#guard ((List.range 4).map (fun i => subjectRangeCount
          ((rangeForSubject ix i).getD ⟨0, 0⟩))).foldl (· + ·) 0 == 12
#guard ix.header.numRowsTotal == 12

/-! ### The decision wrapper -/

#guard rangeForSubjectOpt (some ix) (some 0) == .use ⟨0, 4⟩
#guard rangeForSubjectOpt (some ix) (some 4) == .noInfo   -- out of range
#guard rangeForSubjectOpt (some ix) none == .noInfo       -- unbound
#guard rangeForSubjectOpt none (some 0) == .noInfo        -- no companion
#guard rangeForSubjectOpt none none == .noInfo

/-! A truncated file falls the safe way rather than reading short. -/

#guard rangeForSubjectOpt
  (some { ix with bytes := ix.bytes.extract 0 (ix.bytes.size - 4) }) (some 3)
  == .noInfo

/-! ### The soundness lemma's hypotheses are satisfiable

`rangeForSubject_count_sound` assumes `SubjectOffsetsBuiltCorrectly`.
A theorem whose hypotheses no file satisfies proves nothing about any
file, so here is a file that satisfies them: the fixture's ranges
agree with a ground truth at every subject id, including the empty
subject 1 that the lemma is about. -/

private def groundTruth : Nat → List Nat
  | 0 => [0, 1, 2, 3]
  | 1 => []
  | 2 => [4, 5, 6, 7, 8]
  | 3 => [9, 10, 11]
  | _ => []

#guard (List.range 4).all (fun sid =>
  match rangeForSubject ix sid with
  | some r => subjectRangeCount r == (groundTruth sid).length
  | none   => false)

/-! And the conclusion is the one the lemma draws: subject 1's count is
    zero and its ground truth is empty. -/

#guard subjectRangeCount ((rangeForSubject ix 1).getD ⟨1, 1⟩) == 0
#guard groundTruth 1 == []

/-! ### The path convention -/

#guard subjectOffsetsPathOf "/data/gene.cottas" == "/data/gene.cottas.s.offsets"

#print axioms rangeForSubject_count_sound
#print axioms rangeForSubjectOpt_noInfo_when_handle_absent

end L4Factoidal.Cottas
