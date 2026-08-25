/-
L4Factoidal.HDT.Triples — BitmapTriples navigation.

Port of `formal/fstar/HDT.Triples.fst` (316 lines). Stage 3, on top of
the container skeleton (stage 1) and the PFC dictionary (stage 2).
This is the part that turns an HDT file into triples.

## The structure

The Triples section holds four sub-structures, in the order hdt-cpp
writes them: bitmap(Y), bitmap(Z), log-array(Y), log-array(Z).

- **ArrayY** holds one predicate ID per (subject, predicate) pair, in
  subject-major order. **BitmapY[i] = 1** marks the LAST such pair for
  its subject.
- **ArrayZ** holds one object ID per triple, in the same order.
  **BitmapZ[i] = 1** marks the last object of its (subject, predicate)
  pair.
- Subject IDs are exactly the dictionary's subject-role ID space
  (`Role.subject`: shared IDs 1..Nshared, then the subjects section).

So the file is an SPO forest with two levels, and one primitive
decodes a range at either level: `childrenRange` maps a parent index
to the inclusive child-array range its bitmap delimits.

## rank1 / select1, and where they will be replaced

`rank1 a bm i` counts 1-bits in positions `[0, i]` inclusive.
`select1 a bm k` is the position of the (k+1)-th 1-bit, 0-based `k`.
That pairing gives the identity the probe checks over every valid `k`
of both fixture bitmaps: `rank1 a bm (select1 a bm k) = some (k + 1)`.

Both are linear scans with no auxiliary index. Everything above this
line reaches a bitmap ONLY through `rank1`, `select1` and
`childrenRange` — never through `bitAt` or raw byte offsets, except
inside those three definitions. Replacing the scans with superblock
and block popcount counters changes those three and nothing else.

## Differences from the F* module

1. `nat_sub` is absent, as in stage 2: Lean's `Nat` subtraction
   already truncates at zero.
2. `walk_y_positions` and `hdt_enumerate_subjects` accumulate with
   `acc @ new`, which is quadratic in the number of triples. Both
   accumulate reversed here and reverse once.
-/
import L4Factoidal.HDT.Dictionary

namespace L4Factoidal.HDT

open L4Factoidal.RDF

/-! ## The Triples section's four sub-structures -/

structure TriplesInfo where
  bitmapY : BitmapInfo      -- last-predicate-of-subject markers
  bitmapZ : BitmapInfo      -- last-object-of-(subject, predicate) markers
  arrayY  : LogArrayInfo    -- predicate IDs, one per (subject, predicate) pair
  arrayZ  : LogArrayInfo    -- object IDs, one per triple
  deriving Repr, Inhabited

def parseTriplesInfo (a : Bytes) (pos : Nat) : Option TriplesInfo := do
  let bmy ← parseBitmapInfo a pos
  let bmz ← parseBitmapInfo a bmy.end
  let lay ← parseLogArrayInfo a bmz.end
  let laz ← parseLogArrayInfo a lay.end
  some { bitmapY := bmy, bitmapZ := bmz, arrayY := lay, arrayZ := laz }

/-- Stage 1's inventory plus this stage's section decode. The Triples
    control information is already CRC16-checked by `parseInventory`,
    so a truncated file that still has a valid control block but a
    cut-off payload fails HERE, not at the inventory stage. -/
def readTriples (a : Bytes) (inv : Inventory) : Option TriplesInfo :=
  parseTriplesInfo a inv.triplesDataStart

/-! ## CRC validation

Bitmaps need a preamble CRC8 and a payload CRC32C — the two flavours
stage 1 does not check for them. ArrayY and ArrayZ are ordinary
`LogArrayInfo` values, so their CRCs reuse stage 2's checks. -/

def bmPreambleLen (bm : BitmapInfo) : Nat := (bm.dataStart - 1) - bm.start
def bmPreambleCrc8Pos (bm : BitmapInfo) : Nat := bm.dataStart - 1

def bmPreambleCrc8Ok (a : Bytes) (bm : BitmapInfo) : Bool :=
  match crc8Range a bm.start (bmPreambleLen bm) 0, readU8 a (bmPreambleCrc8Pos bm) with
  | some c, some stored => c == stored
  | _, _ => false

def bmDataCrc32Ok (a : Bytes) (bm : BitmapInfo) : Bool :=
  match crc32cOfRange a bm.dataStart bm.dataBytes, readU32LE a (bm.end - 4) with
  | some c, some stored => c == stored
  | _, _ => false

def bitmapCrcOk (a : Bytes) (bm : BitmapInfo) : Bool :=
  bmPreambleCrc8Ok a bm && bmDataCrc32Ok a bm

/-- All six CRCs the Triples section carries: both bitmaps' preamble
    and payload, both log-arrays' preamble and payload. -/
def triplesCrcOk (a : Bytes) (t : TriplesInfo) : Bool :=
  bitmapCrcOk a t.bitmapY && bitmapCrcOk a t.bitmapZ &&
  laPreambleCrc8Ok a t.arrayY && laDataCrc32Ok a t.arrayY &&
  laPreambleCrc8Ok a t.arrayZ && laDataCrc32Ok a t.arrayZ

/-! ## Bit access, rank1 and select1 — the swap seam -/

/-- Bit `i` of a bitmap, read as a 1-bit-wide log-array entry. Bitmaps
    and log-arrays share one bit convention in hdt-cpp, so this reuses
    `laBitsAcc` rather than restating it. -/
def bitAt (a : Bytes) (bm : BitmapInfo) (i : Nat) : Option Bool :=
  if i ≥ bm.numbits then none
  else (laBitsAcc a bm.dataStart i 1 1 0).map (· == 1)

/-- 1-bits among positions `[pos, pos+fuel)`, added to `acc`. -/
def rank1Upto (a : Bytes) (bm : BitmapInfo) (pos : Nat) : Nat → Nat → Option Nat
  | 0,     acc => some acc
  | n + 1, acc =>
      match bitAt a bm pos with
      | none   => none
      | some b => rank1Upto a bm (pos + 1) n (if b then acc + 1 else acc)

/-- 1-bits in positions `[0, i]`, inclusive. -/
def rank1 (a : Bytes) (bm : BitmapInfo) (i : Nat) : Option Nat :=
  if i ≥ bm.numbits then none else rank1Upto a bm 0 (i + 1) 0

/-- Linear scan from `pos` with `fuel` positions left and `seen` ones
    already counted; returns the position of the bit that brings the
    running count to `target`. -/
def select1Scan (a : Bytes) (bm : BitmapInfo) (pos : Nat) :
    Nat → Nat → Nat → Option Nat
  | 0,     _,      _    => none
  | n + 1, target, seen =>
      match bitAt a bm pos with
      | none   => none
      | some b =>
          let seen' := if b then seen + 1 else seen
          if b && seen' == target then some pos
          else select1Scan a bm (pos + 1) n target seen'

/-- Position of the (k+1)-th 1-bit, 0-based `k`. Paired with `rank1`
    so that `rank1 a bm (select1 a bm k) = some (k + 1)`. -/
def select1 (a : Bytes) (bm : BitmapInfo) (k : Nat) : Option Nat :=
  select1Scan a bm 0 bm.numbits (k + 1) 0

/-! ## SPO forest navigation -/

/-- Parent index `idx` (0-based) to the inclusive `[lo, hi]` range of
    its children, delimited by consecutive 1-bits of the level's
    bitmap. The one range primitive both levels use. -/
def childrenRange (a : Bytes) (bm : BitmapInfo) (idx : Nat) : Option (Nat × Nat) := do
  let hi ← select1 a bm idx
  if idx == 0 then some (0, hi)
  else do
    let prev ← select1 a bm (idx - 1)
    some (prev + 1, hi)

/-- `count` consecutive log-array entries from `pos` (0-based), in
    order. Generic over ArrayY and ArrayZ. -/
def collectRange (a : Bytes) (la : LogArrayInfo) (pos : Nat) :
    Nat → List Nat → Option (List Nat)
  | 0,     acc => some acc.reverse
  | n + 1, acc =>
      match laEntry a la pos with
      | none   => none
      | some v => collectRange a la (pos + 1) n (v :: acc)

def rangeCount (lo hi : Nat) : Nat := if hi ≥ lo then hi - lo + 1 else 0

/-- Walk `count` consecutive Y-positions from `y`, emitting one
    (predicate, object) pair per object in each position's Z-range.
    The accumulator is reversed; `trailsForSubject` reverses once. -/
def walkYPositions (a : Bytes) (t : TriplesInfo) (y : Nat) :
    Nat → List (Nat × Nat) → Option (List (Nat × Nat))
  | 0,     acc => some acc
  | n + 1, acc =>
      match laEntry a t.arrayY y with
      | none => none
      | some p =>
          match childrenRange a t.bitmapZ y with
          | none => none
          | some (zlo, zhi) =>
              match collectRange a t.arrayZ zlo (rangeCount zlo zhi) [] with
              | none => none
              | some objs =>
                  walkYPositions a t (y + 1) n
                    ((objs.reverse.map (fun o => (p, o))) ++ acc)

/-- Subject ID to its (predicate, object) ID pairs, in the file's own
    subject-then-predicate-then-object order. `subj` is a 1-based ID in
    the dictionary's `Role.subject` space. -/
def triplesForSubject (a : Bytes) (t : TriplesInfo) (subj : Nat) :
    Option (List (Nat × Nat)) :=
  if subj == 0 then none
  else match childrenRange a t.bitmapY (subj - 1) with
  | none => none
  | some (ylo, yhi) => (walkYPositions a t ylo (rangeCount ylo yhi) []).map List.reverse

/-! ## Whole-container enumeration -/

/-- ArrayZ carries exactly one entry per triple. Its 1-bits mark the
    last object of each (subject, predicate) pair, but EVERY entry —
    1-bit or not — is one object of one triple. -/
def tripleCount (t : TriplesInfo) : Nat := t.arrayZ.numentries

/-- Subjects with data: the 1-bits of BitmapY, since each subject that
    appears ends its Y-range with exactly one. Derived from the bitmap
    alone, so comparing it with `roleMaxId inv .subject` — which comes
    from the dictionary section sizes — is a real cross-check. -/
def numSubjects (a : Bytes) (t : TriplesInfo) : Option Nat :=
  let bm := t.bitmapY
  if bm.numbits == 0 then some 0 else rank1 a bm (bm.numbits - 1)

structure IdTriple where
  s : Nat
  p : Nat
  o : Nat
  deriving Repr, DecidableEq, Inhabited

def enumerateSubjects (a : Bytes) (t : TriplesInfo) (subj : Nat) :
    Nat → List IdTriple → Option (List IdTriple)
  | 0,     acc => some acc
  | n + 1, acc =>
      match triplesForSubject a t subj with
      | none => none
      | some pairs =>
          enumerateSubjects a t (subj + 1) n
            ((pairs.reverse.map (fun (p, o) => ⟨subj, p, o⟩)) ++ acc)

/-- Every triple as IDs, in file order: subject-major, then predicate,
    then object. -/
def enumerateAll (a : Bytes) (t : TriplesInfo) : Option (List IdTriple) :=
  match numSubjects a t with
  | none      => none
  | some 0    => some []
  | some n    => (enumerateSubjects a t 1 n []).map List.reverse

/-- One ID triple resolved through the dictionary. `none` if any of
    the three IDs has no term, which is what the probe counts as an
    unresolved triple rather than silently dropping. -/
def resolveIdTriple (a : Bytes) (inv : Inventory) (it : IdTriple) : Option Triple := do
  let s ← idToTerm a inv .subject it.s
  let p ← idToTerm a inv .predicate it.p
  let o ← idToTerm a inv .object it.o
  match s, p with
  | .iri si,  .iri pi => some (RDF.Triple.mk (.iri si) pi o)
  | .bnode b, .iri pi => some (RDF.Triple.mk (.bnode b) pi o)
  | _, _ => none

end L4Factoidal.HDT
