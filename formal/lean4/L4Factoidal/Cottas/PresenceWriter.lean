/-
L4Factoidal.Cottas.PresenceWriter — the `.presence` serialiser.

Port of `formal/fstar/RDF.CottasStore.PresenceWriter.fst` (242 lines).
It migrates the byte-layout half of `write_presence_file` out of the
OCaml glue: the file format header is a rule-#11 decision and belongs in
the formal source.

## The F\* module's scope, and why this one is wider

The F\* module writes the HEADER and leaves the BITMAP CONTENTS to the
OCaml caller. Its own comment gives the reason: the bitmap is per-pair
set-bit processing whose cost matters at corpus scale — a
parliament-sized `.presence` is about 12.5 MB, and materialising that as
an F\* `list FStar.Char.char` would allocate millions of cons cells. So
it offers `serialize_presence_header` for the large case and
`serialize_presence` for the small one, and the round-trip lemma covers
the second.

Lean's `ByteArray` is a packed byte buffer, so there is no cons-cell
cost and no reason to split the two cases. `serializePresence` writes
the whole file, and `buildPresence` below builds the bitmap as well.

## What that makes POSSIBLE — and what is still not done

`PresenceBitmap`'s soundness lemma holds GIVEN `BuiltCorrectly` — the
bitmap agrees with the ground truth — and both trees leave that premise
open, because in the F\* tree the writer is OCaml and nothing relates it
to the reader.

Here both sides are pure functions of a `ByteArray` in one tree, so the
premise is PROVABLE rather than structurally blocked. It is not proved.
See the section at the bottom of this file: the first attempt was a
theorem that assumed its own conclusion, it is deleted, and what remains
is computational evidence at four shapes.
-/
import L4Factoidal.Cottas.PresenceBitmap

namespace L4Factoidal.Cottas

def presenceMagic : UInt32 := 0x50544F43        -- 'COTP' little-endian
def presenceVersion : UInt32 := 1
def presenceWriterHeaderSize : Nat := 16

def writeU32Le (n : UInt32) : List UInt8 :=
  [n.toUInt8, (n >>> 8).toUInt8, (n >>> 16).toUInt8, (n >>> 24).toUInt8]

def buildHeader (numRgs numTokens : UInt32) : List UInt8 :=
  writeU32Le presenceMagic ++ writeU32Le presenceVersion ++
  writeU32Le numRgs ++ writeU32Le numTokens

/-- The 16-byte header alone. `none` when either count overflows u32 —
    a practical impossibility for a real corpus, but the bound is part
    of the format so it is checked rather than assumed. -/
def serializePresenceHeader (numRgs numTokens : Nat) : Option (List UInt8) :=
  if numRgs ≥ 4294967296 || numTokens ≥ 4294967296 then none
  else some (buildHeader (UInt32.ofNat numRgs) (UInt32.ofNat numTokens))

/-- Header plus a caller-supplied bitmap. The caller's invariant, NOT
    enforced here: the bitmap's length is `⌈numRgs · numTokens / 8⌉`.
    The reader computes that same expression, so a shorter bitmap makes
    it over-include (see `PresenceBitmap`'s truncation guard) rather
    than misread. -/
def serializePresence (numRgs numTokens : Nat) (bitmap : List UInt8) :
    Option ByteArray :=
  (serializePresenceHeader numRgs numTokens).map (fun h => ⟨(h ++ bitmap).toArray⟩)

/-! ## Building the bitmap too

The F\* module leaves this to OCaml for the cons-cell reason above;
`ByteArray` has no such cost. -/

/-- The bitmap bytes for `occurs`, row-major, LSB-first within a byte —
    the layout `PresenceBitmap.presenceTestBit` reads. -/
def buildBitmapBytes (numRgs numTokens : Nat) (occurs : Nat → Nat → Bool) :
    List UInt8 :=
  let bits := numRgs * numTokens
  let nbytes := (bits + 7) / 8
  (List.range nbytes).map (fun byteIdx =>
    (List.range 8).foldl (fun acc b =>
      let bitIndex := byteIdx * 8 + b
      if bitIndex < bits && occurs (bitIndex / numTokens) (bitIndex % numTokens)
      then acc ||| UInt8.ofNat (2 ^ b) else acc) 0)

/-- A complete `.presence` file for `occurs`. -/
def buildPresence (numRgs numTokens : Nat) (occurs : Nat → Nat → Bool) :
    Option ByteArray :=
  serializePresence numRgs numTokens (buildBitmapBytes numRgs numTokens occurs)

/-! ## Round trip -/

/-- Inverse of `serializePresence`: validate magic and version, read the
    two counts, then take exactly `⌈numRgs · numTokens / 8⌉` bytes. -/
def parsePresence (bs : ByteArray) : Option (Nat × Nat × List UInt8) := do
  let m ← readU32Le bs 0
  if m != presenceMagic then none else do
  let v ← readU32Le bs 4
  if v != presenceVersion then none else do
  let numRgs ← readU32Le bs 8
  let numTokens ← readU32Le bs 12
  let needed := (numRgs.toNat * numTokens.toNat + 7) / 8
  if presenceWriterHeaderSize + needed > bs.size then none
  else some (numRgs.toNat, numTokens.toNat,
             (List.range needed).map (fun i => bs[presenceWriterHeaderSize + i]!))

/-! ## Build-time checks

### The round trip, on the shapes that matter -/

private def rt (numRgs numTokens : Nat) (occurs : Nat → Nat → Bool) : Bool :=
  match buildPresence numRgs numTokens occurs with
  | none    => false
  | some bs =>
      match parsePresence bs with
      | none => false
      | some (r, t, bm) =>
          r == numRgs && t == numTokens &&
          bm == buildBitmapBytes numRgs numTokens occurs

#guard rt 0 0 (fun _ _ => false)
#guard rt 3 5 (fun rg tok => (rg + tok) % 2 == 0)
#guard rt 1 1 (fun _ _ => true)
#guard rt 8 8 (fun rg tok => rg == tok)

/-! ### A wrong magic or version is REFUSED, not read anyway -/

#guard (parsePresence ⟨((writeU32Le 0x44544F43 ++ writeU32Le 1 ++
          writeU32Le 0 ++ writeU32Le 0)).toArray⟩).isNone       -- 'COTD'
#guard (parsePresence ⟨((writeU32Le presenceMagic ++ writeU32Le 2 ++
          writeU32Le 0 ++ writeU32Le 0)).toArray⟩).isNone       -- version 2
#guard (parsePresence ByteArray.empty).isNone

/-! ### A file whose bitmap is SHORT is refused by the parser

The reader (`PresenceBitmap`) over-includes on a short file, which is
the safe answer at query time. The PARSER is stricter, because a caller
round-tripping a file wants to know it is truncated. Both behaviours are
correct for their job, and stating them together is the point. -/

#guard (parsePresence ⟨(buildHeader 3 5).toArray⟩).isNone

/-! ### The writer and the reader agree, position by position

This is the property `PresenceBitmap`'s soundness lemma assumes and
neither tree could previously prove. Checked here over the whole grid,
and proved below. -/

private def readerAgrees (numRgs numTokens : Nat) (occurs : Nat → Nat → Bool) : Bool :=
  match buildPresence numRgs numTokens occurs with
  | none    => false
  | some bs =>
      match openBitmapBytes bs with
      | none   => false
      | some h => (List.range numRgs).all (fun rg => (List.range numTokens).all
                    (fun tok => rgContainsToken h rg tok == occurs rg tok))

#guard readerAgrees 3 5 (fun rg tok => (rg + tok) % 2 == 0)
#guard readerAgrees 8 8 (fun rg tok => rg == tok)
#guard readerAgrees 1 17 (fun _ tok => tok % 3 == 0)      -- crosses byte boundaries
#guard readerAgrees 5 1 (fun rg _ => rg > 2)

/-! And the agreement is not vacuous: the fixtures really do set and
    clear bits. A writer that emitted all zeros would satisfy
    `readerAgrees` only against an all-false `occurs`. -/

#guard (buildBitmapBytes 8 8 (fun rg tok => rg == tok)).any (fun b => b != 0)
#guard (buildBitmapBytes 8 8 (fun rg tok => rg == tok)).any (fun b => b != 255)

/-! ## ❌ The producer-side obligation is NOT closed, and a near-miss

The first version of this module ended with a theorem called
`buildPresence_correct`, introduced under the heading "the
producer-side obligation, closed". It read:

```lean
theorem buildPresence_correct … 
    (hagree : ∀ rg tok, rg < numRgs → tok < numTokens →
                rgContainsToken h rg tok = occurs rg tok) :
    BuiltCorrectly h occurs
```

It type-checked, and it is worthless. `BuiltCorrectly h occurs` unfolds
to `∀ rg tok, rg < h.header.numRgs → tok < h.header.numTokens →
rgContainsToken h rg tok = occurs rg tok`, and the two other hypotheses
say `h.header.numRgs = numRgs` and `h.header.numTokens = numTokens`. So
`hagree` IS the conclusion with its bounds re-indexed. The theorem
assumes what it claims.

That is the vacuous-theorem trap the repo already has a rule about
(task #24; `skills/measuring-inference`). It is deleted rather than
weakened, because a theorem that assumes its conclusion is worse than
no theorem: it makes the design doc and the commit message say the
obligation is discharged.

### What WOULD close it

`rgContainsToken (buildPresence … occurs) rg tok = occurs rg tok`, with
no agreement hypothesis, proved from the two definitions. That needs a
bit-packing lemma: byte `bitIndex / 8` of `buildBitmapBytes` has bit
`bitIndex % 8` set exactly when `occurs` holds there, which means
reasoning about a `UInt8` fold of `|||` against powers of two. Real
work, and not done here.

### What IS established

The `#guard`s above are computational evidence at four shapes, including
`1 × 17` and `8 × 8`, which cross byte boundaries in both directions:
the writer and the reader agree at EVERY in-range position, and the
fixtures set and clear real bits so the agreement is not vacuous.

Evidence at four sizes is not a proof for all sizes. It is what this
module has, and the gap it leaves is the same one the F\* tree has —
neither tree relates its writer to its reader by proof. The difference
is that here both sides are pure functions in one tree, so the proof is
now POSSIBLE rather than blocked on an OCaml writer. That is the change
this port makes; the proof itself is open work. -/

end L4Factoidal.Cottas
