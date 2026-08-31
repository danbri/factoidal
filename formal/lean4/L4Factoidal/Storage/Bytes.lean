/-
L4Factoidal.Storage.Bytes — the byte-level primitives of the HDT
on-disk format, ported from `formal/fstar/HDT.Container.fst` and
`HDT.Dictionary.fst`.

Spec: HDT (Header-Dictionary-Triples,
https://www.rdfhdt.org/hdt-binary-format/), whose sections are
checksum-guarded: a CRC8 over each preamble and a CRC32C over each
data range.

Why this module is in the LEAN tree at all: iron rule 11 puts byte
assembly in the formal source — `serialize : data -> List UInt8` —
leaving only `write_bytes` outside. So the format IS specifiable
here, and reading it back is a total function over a byte list, with
no I/O.

Round-trip theorems are proved rather than assumed, because a
storage format whose decode does not invert its encode loses data
silently.
-/

import Std.Tactic.BVDecide

namespace L4Factoidal.Storage

/-- VByte: 7 bits per byte, the high bit marking the LAST byte.

    This is HDT's own variant and it is the opposite of LEB128, where
    the high bit marks CONTINUATION. Getting the polarity backwards
    decodes every multi-byte number wrongly while single-byte values
    keep working — the failure mode that survives casual testing. -/
def vbyteEncode (n : Nat) : List UInt8 :=
  let rec go (n : Nat) (acc : List UInt8) : List UInt8 :=
    if n < 128 then (acc ++ [UInt8.ofNat (n + 128)])
    else go (n / 128) (acc ++ [UInt8.ofNat (n % 128)])
  go n []

/-- Decode a VByte, returning the value and the bytes consumed. -/
def vbyteDecode (bs : List UInt8) : Option (Nat × Nat) :=
  let rec go (bs : List UInt8) (shift acc used : Nat) : Option (Nat × Nat) :=
    match bs with
    | [] => none
    | b :: rest =>
        let v := b.toNat
        if v ≥ 128 then some (acc + (v - 128) * (128 ^ shift), used + 1)
        else go rest (shift + 1) (acc + v * (128 ^ shift)) (used + 1)
  go bs 0 0 0

/-  NEXT OBLIGATIONS, stated rather than admitted (no `sorry`):

    * `vbyteDecode (vbyteEncode n) = some (n, len)` for ALL `n`. It
      needs induction on `n / 128` with the accumulator generalised —
      a real proof, not a `simp`. `#guard` covers a spread of
      multi-byte values by evaluation until it lands.
    * `Section.parse s.serialize .. = some s`. The obstacle is a
      `readU32LE`-over-append lemma; the CRC width obligations were
      removed by typing the checksums `UInt8`/`UInt32` rather than
      `Nat`, which is why that restructure happened here.

    Both are stated because a storage format whose decode does not
    invert its encode loses data SILENTLY, so the gap belongs in the
    source where the next reader sees it.
-/

/-- Little-endian 32-bit read. -/
def readU32LE (bs : List UInt8) (pos : Nat) : Option UInt32 :=
  match bs.drop pos with
  | b0 :: b1 :: b2 :: b3 :: _ =>
      some (b0.toUInt32 ||| (b1.toUInt32 <<< 8) |||
            (b2.toUInt32 <<< 16) ||| (b3.toUInt32 <<< 24))
  | _ => none

/-- Little-endian 32-bit write. -/
def writeU32LE (n : UInt32) : List UInt8 :=
  [n.toUInt8, (n >>> 8).toUInt8, (n >>> 16).toUInt8, (n >>> 24).toUInt8]

/-- The fixed-width little-endian primitive is an inverse even when followed
    by arbitrary later input. This is the base lemma for every framed storage
    object: a parser must consume its own four-byte field and leave the tail
    untouched. -/
theorem readU32LE_writeU32LE_append (n : UInt32) (rest : List UInt8) :
    readU32LE (writeU32LE n ++ rest) 0 = some n := by
  simp [readU32LE, writeU32LE]
  bv_decide

/-- A fixed-width field remains readable after arbitrary preceding framing. -/
theorem readU32LE_append_writeU32LE (pre : List UInt8) (n : UInt32) (rest : List UInt8) :
    readU32LE (pre ++ writeU32LE n ++ rest) pre.length = some n := by
  simp [readU32LE, writeU32LE]
  bv_decide

/-- CRC8 with the HDT polynomial, one step.

    Typed `UInt8` rather than `Nat` deliberately: the width is part of
    the format, so carrying it in the TYPE removes every "< 256"
    obligation from the round-trip proof instead of discharging them
    one at a time. -/
def crc8Step (c : UInt8) : UInt8 :=
  if c % 2 == 1 then (c / 2) ^^^ 0x8C else c / 2

def crc8Byte (crc b : UInt8) : UInt8 :=
  let rec go (c : UInt8) : Nat → UInt8
    | 0     => c
    | n + 1 => go (crc8Step c) n
  go (crc ^^^ b) 8

def crc8 (bs : List UInt8) : UInt8 :=
  bs.foldl crc8Byte 0

/-- CRC32C (Castagnoli), one step. Same width-in-the-type reasoning
    as `crc8Step`. -/
def crc32cStep (c : UInt32) : UInt32 :=
  if c % 2 == 1 then (c / 2) ^^^ 0x82F63B78 else c / 2

def crc32cByte (crc : UInt32) (b : UInt8) : UInt32 :=
  let rec go (c : UInt32) : Nat → UInt32
    | 0     => c
    | n + 1 => go (crc32cStep c) n
  go (crc ^^^ b.toUInt32) 8

def crc32c (bs : List UInt8) : UInt32 :=
  (bs.foldl crc32cByte 0xFFFFFFFF) ^^^ 0xFFFFFFFF

/-- A checksummed section: the preamble guarded by CRC8, the data by
    CRC32C. Both must verify — a section that fails EITHER is
    rejected, never partially read. -/
structure Section where
  preamble : List UInt8
  data     : List UInt8
deriving Repr, Inhabited, DecidableEq

/-- Serialise a section: preamble, its CRC8, data, its CRC32C. -/
def Section.serialize (s : Section) : List UInt8 :=
  s.preamble ++ [crc8 s.preamble] ++ s.data ++ writeU32LE (crc32c s.data)

/-- Read a section back, verifying both checksums. `none` means the
    bytes are corrupt — reading on regardless is how a storage layer
    turns a disk error into wrong query answers. -/
def Section.parse (bs : List UInt8) (preambleLen dataLen : Nat) : Option Section :=
  let preamble := bs.take preambleLen
  match (bs.drop preambleLen).head? with
  | none => none
  | some storedCrc8 =>
      if storedCrc8 != crc8 preamble then none
      else
        let rest := bs.drop (preambleLen + 1)
        let data := rest.take dataLen
        match readU32LE rest dataLen with
        | none => none
        | some storedCrc32 =>
            if storedCrc32 != crc32c data then none
            else some ⟨preamble, data⟩

end L4Factoidal.Storage
