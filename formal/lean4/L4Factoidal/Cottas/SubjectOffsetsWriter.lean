/-
L4Factoidal.Cottas.SubjectOffsetsWriter — the `.s.offsets` serialiser.

Port of `formal/fstar/RDF.CottasStore.SubjectOffsetsWriter.fst` (272
lines). One contiguous global row range per subject.

## Why this file is simpler than `.p.offsets`

`BaseWriter` sorts every row by `(s, p, o, g)`, subject primary, before
serialisation. A predicate takes a few distinct values scattered
through every row group, so `.p.offsets` records a per-`(row group,
predicate)` list. A subject, sorted primary, occupies ONE contiguous
global row range, so one `(start, end)` pair per subject is exact. The
F\* header gives the measured size: 91,871 distinct subjects in the gene
corpus, 16 bytes each, about 1.4 MB.

```
Header (16 bytes, little-endian throughout):
  [ magic         : u32  'COTS' = 0x53544F43 ]
  [ version       : u32  currently 1 ]
  [ numSubjects   : u32 ]
  [ numRowsTotal  : u32  cross-check against the parquet row count ]

Ranges:
  [ (start : u64, endExclusive : u64) * numSubjects,
    in ascending subject-id order ]
```

## This module does NOT carry the offset-unit fault

`CompoundPresenceWriter` and `OffsetsWriter` both read a payload entry
as an element count where the shipping writer stores a byte offset, so
their parsers return `None` on every real file
(<https://github.com/danbri/factoidal/issues/555>). This module reads
its count from the header field `num_subjects` and never consults the
payload for it, so the question does not arise. Its round-trip lemma
covers the files the project writes, and the F\* header says the byte
assembly of the range array is itself on the shipping path rather than
in OCaml.

## What is proved here

`unflattenRanges_flattenRanges` proves the pair-flattening round trip,
the Lean counterpart of `lemma_unflatten_flatten`. The byte-level round
trip is checked by `#guard` at several shapes and is not proved; that
needs inverse lemmas for `readU32Le` and `readU64Le` over `ByteArray`,
which no module in this tree has yet.

## One change from the F\* module

An endpoint at or above 2^64 fails the whole write. F\*'s shared
`serialize_u64_list` returns `[]` at the first out-of-range entry,
which drops the rest of the payload while the header still declares
the full subject count — a short unparseable file, written with no
error. `buildSubjectOffsets` returns `none`.
-/
import L4Factoidal.Cottas.OffsetsWriter

namespace L4Factoidal.Cottas

def cotsMagicU32 : UInt32 := 0x53544F43
def subjectOffsetsLayoutVersion : UInt32 := 1
def subjectOffsetsHeaderSize : Nat := 16

structure SubjectOffsetsHeader where
  magic        : UInt32
  version      : UInt32
  numSubjects  : Nat
  numRowsTotal : Nat
  deriving Repr, DecidableEq, Inhabited

def SubjectOffsetsHeader.ok (h : SubjectOffsetsHeader) : Bool :=
  h.magic == cotsMagicU32 && h.version == subjectOffsetsLayoutVersion

def buildSubjectOffsetsHeader (numSubjects numRowsTotal : UInt32) : List UInt8 :=
  writeU32Le cotsMagicU32 ++ writeU32Le subjectOffsetsLayoutVersion ++
  writeU32Le numSubjects ++ writeU32Le numRowsTotal

def serializeSubjectOffsetsHeader (numSubjects numRowsTotal : Nat) :
    Option (List UInt8) :=
  if numSubjects ≥ 4294967296 || numRowsTotal ≥ 4294967296 then none
  else some (buildSubjectOffsetsHeader (UInt32.ofNat numSubjects)
               (UInt32.ofNat numRowsTotal))

/-! ## Flattening the pairs -/

def flattenRanges : List (Nat × Nat) → List Nat
  | []           => []
  | (s, e) :: tl => s :: e :: flattenRanges tl

def unflattenRanges : List Nat → Option (List (Nat × Nat))
  | []            => some []
  | [_]           => none                    -- odd length: no matching end
  | s :: e :: tl  => (unflattenRanges tl).map (fun rest => (s, e) :: rest)

theorem unflattenRanges_flattenRanges (rs : List (Nat × Nat)) :
    unflattenRanges (flattenRanges rs) = some rs := by
  induction rs with
  | nil => rfl
  | cons x tl ih =>
      obtain ⟨s, e⟩ := x
      simp [flattenRanges, unflattenRanges, ih]

theorem flattenRanges_length (rs : List (Nat × Nat)) :
    (flattenRanges rs).length = 2 * rs.length := by
  induction rs with
  | nil => rfl
  | cons x tl ih =>
      obtain ⟨s, e⟩ := x
      simp [flattenRanges, ih]
      omega

/-! ## The whole file -/

def rangesAllLt (rs : List (Nat × Nat)) (bound : Nat) : Bool :=
  rs.all (fun r => r.1 < bound && r.2 < bound)

/-- `none` when a header count overflows u32, when the range count does
    not match `numSubjects`, or when an endpoint does not fit in u64. -/
def buildSubjectOffsets (numSubjects numRowsTotal : Nat)
    (ranges : List (Nat × Nat)) : Option ByteArray :=
  if ranges.length != numSubjects then none
  else if !rangesAllLt ranges 18446744073709551616 then none
  else (serializeSubjectOffsetsHeader numSubjects numRowsTotal).map (fun hdr =>
    ⟨(hdr ++ (flattenRanges ranges).flatMap writeU64Le).toArray⟩)

/-! ## Reading it back -/

structure SubjectOffsetsHandle where
  bytes  : ByteArray
  header : SubjectOffsetsHeader

def readSubjectOffsetsHeader (bs : ByteArray) : Option SubjectOffsetsHeader := do
  let magic ← readU32Le bs 0
  let version ← readU32Le bs 4
  let numSubjects ← readU32Le bs 8
  let numRowsTotal ← readU32Le bs 12
  some { magic := magic, version := version,
         numSubjects := numSubjects.toNat, numRowsTotal := numRowsTotal.toNat }

def openSubjectOffsetsBytes (bs : ByteArray) : Option SubjectOffsetsHandle :=
  match readSubjectOffsetsHeader bs with
  | none   => none
  | some h => if h.ok then some { bytes := bs, header := h } else none

def openSubjectOffsets (path : System.FilePath) :
    IO (Option SubjectOffsetsHandle) := do
  if !(← path.pathExists) then return none
  return openSubjectOffsetsBytes (← IO.FS.readBinFile path)

/-- The `(start, endExclusive)` row range of subject `sid`. -/
def subjectRange (h : SubjectOffsetsHandle) (sid : Nat) : Option (Nat × Nat) :=
  if sid ≥ h.header.numSubjects then none
  else do
    let s ← readU64Le h.bytes (subjectOffsetsHeaderSize + 16 * sid)
    let e ← readU64Le h.bytes (subjectOffsetsHeaderSize + 16 * sid + 8)
    some (s, e)

/-- The row count of subject `sid`. An end before its start counts as
    an empty range rather than an error, matching
    `row_positions_count_from_bounds` in
    `RDF.Store.Columnar.OffsetIndex`. A subject id outside the file is
    `none`, which is a different answer from a subject with no rows. -/
def subjectRowCount (h : SubjectOffsetsHandle) (sid : Nat) : Option Nat :=
  (subjectRange h sid).map (fun (s, e) => if e < s then 0 else e - s)

def parseSubjectOffsets (bs : ByteArray) :
    Option (Nat × Nat × List (Nat × Nat)) := do
  let h ← openSubjectOffsetsBytes bs
  let flat ← (List.range (2 * h.header.numSubjects)).mapM
               (fun i => readU64Le bs (subjectOffsetsHeaderSize + 8 * i))
  let ranges ← unflattenRanges flat
  some (h.header.numSubjects, h.header.numRowsTotal, ranges)

/-! ## Build-time checks

### The pair flattening, in both directions -/

#guard flattenRanges [(1, 2), (3, 9)] == [1, 2, 3, 9]
#guard unflattenRanges [1, 2, 3, 9] == some [(1, 2), (3, 9)]
#guard (unflattenRanges [1, 2, 3]).isNone
#guard unflattenRanges ([] : List Nat) == some []

/-! ### The byte-level round trip -/

private def srt (numSubjects numRowsTotal : Nat) (rs : List (Nat × Nat)) : Bool :=
  match buildSubjectOffsets numSubjects numRowsTotal rs with
  | none    => false
  | some bs =>
      match parseSubjectOffsets bs with
      | none => false
      | some (n, r, back) => n == numSubjects && r == numRowsTotal && back == rs

#guard srt 0 0 []
#guard srt 1 5 [(0, 5)]
#guard srt 3 12 [(0, 4), (4, 4), (4, 12)]
#guard srt 2 4294967295 [(0, 4294967295), (4294967295, 4294967295)]

/-! ### Each subject's range at its own id -/

private def sbytes : ByteArray :=
  (buildSubjectOffsets 3 12 [(0, 4), (4, 4), (4, 12)]).getD ByteArray.empty

private def sh : SubjectOffsetsHandle :=
  (openSubjectOffsetsBytes sbytes).getD ⟨ByteArray.empty, default⟩

#guard subjectRange sh 0 == some (0, 4)
#guard subjectRange sh 1 == some (4, 4)
#guard subjectRange sh 2 == some (4, 12)
#guard (subjectRange sh 3).isNone

/-! ### An empty range and an absent subject are different answers

Subject 1 owns no rows; subject 3 is not in the file at all. A reader
that returned `0` for both would lose the distinction. -/

#guard subjectRowCount sh 0 == some 4
#guard subjectRowCount sh 1 == some 0
#guard subjectRowCount sh 2 == some 8
#guard (subjectRowCount sh 3).isNone

/-! An end before its start counts as empty, not as an underflow. -/

#guard (match buildSubjectOffsets 1 4 [(4, 1)] with
        | some bs => match openSubjectOffsetsBytes bs with
                     | some h => subjectRowCount h 0 == some 0
                     | none   => false
        | none    => false)

/-! ### Wrong magic, wrong version, and the other three COTTAS files -/

#guard (openSubjectOffsetsBytes ⟨(writeU32Le 0x44544F43 ++ writeU32Le 1 ++
          writeU32Le 0 ++ writeU32Le 0).toArray⟩).isNone
#guard (openSubjectOffsetsBytes ⟨(writeU32Le cotsMagicU32 ++ writeU32Le 2 ++
          writeU32Le 0 ++ writeU32Le 0).toArray⟩).isNone
#guard (openSubjectOffsetsBytes (mkPresence 2 2 [])).isNone
#guard (openSubjectOffsetsBytes (mkCompound 2 2 [[(1, 1)]])).isNone
#guard cotsMagicU32 != cotoMagicU32
#guard cotsMagicU32 != copoMagicU32
#guard cotsMagicU32 != cotpMagicU32

/-! A `.s.offsets` file must not open as a `.p.offsets` one either. -/

#guard (openOffsetsBytes sbytes).isNone

/-! ### A truncated file is refused rather than read short -/

#guard (parseSubjectOffsets (sbytes.extract 0 (sbytes.size - 8))).isNone

/-! ### The writer refuses rather than truncating -/

#guard (buildSubjectOffsets 1 0 [(0, 18446744073709551616)]).isNone
#guard (buildSubjectOffsets 2 0 [(0, 1)]).isNone            -- count mismatch
#guard (buildSubjectOffsets 4294967296 0 []).isNone

/-! ### The header, byte for byte -/

#guard serializeSubjectOffsetsHeader 91871 250000 ==
  some (writeU32Le 0x53544F43 ++ writeU32Le 1 ++ writeU32Le 91871 ++
        writeU32Le 250000)
#guard (serializeSubjectOffsetsHeader 3 12).map List.length == some 16

/-! ### The file size the F\* header predicts

16 bytes of header plus 16 bytes per subject. -/

#guard sbytes.size == 16 + 16 * 3

#print axioms unflattenRanges_flattenRanges

end L4Factoidal.Cottas
