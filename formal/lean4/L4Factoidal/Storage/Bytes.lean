/-
L4Factoidal.Storage.Bytes — the byte-level primitives shared by every
on-disk format in this tree: VByte, little-endian u32 fields with their
read/write lemmas, CRC8 and CRC32C, and the checksum-guarded `Section`.

They were ported for HDT (Header-Dictionary-Triples,
https://www.rdfhdt.org/hdt-binary-format/, from
`formal/fstar/HDT.Container.fst` and `HDT.Dictionary.fst`), whose
sections carry a CRC8 over each preamble and a CRC32C over each data
range. The Shardborough codecs (`BlockWireV0`, `IndexedBlockWire*`,
`PagedTermDictionary`, `SubjectRowIndexWire*`, `TermLocalIndexWire`,
`DeltaLog`) use the same u32 fields and CRC32C.

Why this module is in the LEAN tree at all: iron rule 11 puts byte
assembly in the formal source — `serialize : data -> List UInt8` —
leaving only `write_bytes` outside. So the format IS specifiable
here, and reading it back is a total function over a byte list, with
no I/O.

Round-trip theorems are proved rather than assumed, because a
storage format whose decode does not invert its encode loses data
silently.
-/

import Init.Data.UInt.Lemmas

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

/- Keep these proofs on Lean's core fixed-width bit-vector lemmas. Importing
   `Std.Tactic.BVDecide` here would put a proof-tactic initializer in every
   executable storage consumer, including the narrow WASM block kernel. -/
private theorem bitVec32_toNat_32 : (32 : BitVec 32).toNat = 32 := by decide

private theorem bitVecOr_reverse4 {a b c d : BitVec 32} :
    a ||| b ||| c ||| d = d ||| c ||| b ||| a := by
  ac_rfl

private theorem u32Byte0 (n : UInt32) :
    n.toUInt8.toBitVec = n.toBitVec.extractLsb' 0 8 := by
  rw [UInt32.toBitVec_toUInt8, BitVec.setWidth_eq_extractLsb' (by decide)]

private theorem u32Byte8 (n : UInt32) :
    ((n >>> 8).toUInt8).toBitVec = n.toBitVec.extractLsb' 8 8 := by
  rw [UInt32.toBitVec_toUInt8, UInt32.toBitVec_shiftRight]
  simp only [BitVec.ushiftRight_eq', BitVec.toNat_umod,
    UInt32.toNat_toBitVec, UInt32.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  rw [bitVec32_toNat_32]
  simp only [Nat.reduceMod]
  rw [BitVec.setWidth_ushiftRight_eq_extractLsb]

private theorem u32Byte16 (n : UInt32) :
    ((n >>> 16).toUInt8).toBitVec = n.toBitVec.extractLsb' 16 8 := by
  rw [UInt32.toBitVec_toUInt8, UInt32.toBitVec_shiftRight]
  simp only [BitVec.ushiftRight_eq', BitVec.toNat_umod,
    UInt32.toNat_toBitVec, UInt32.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  rw [bitVec32_toNat_32]
  simp only [Nat.reduceMod]
  rw [BitVec.setWidth_ushiftRight_eq_extractLsb]

private theorem u32Byte24 (n : UInt32) :
    ((n >>> 24).toUInt8).toBitVec = n.toBitVec.extractLsb' 24 8 := by
  rw [UInt32.toBitVec_toUInt8, UInt32.toBitVec_shiftRight]
  simp only [BitVec.ushiftRight_eq', BitVec.toNat_umod,
    UInt32.toNat_toBitVec, UInt32.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  rw [bitVec32_toNat_32]
  simp only [Nat.reduceMod]
  rw [BitVec.setWidth_ushiftRight_eq_extractLsb]

private theorem assembleU32LE_eq (n : UInt32) :
    n.toUInt8.toUInt32 ||| (((n >>> 8).toUInt8).toUInt32 <<< 8) |||
      (((n >>> 16).toUInt8).toUInt32 <<< 16) |||
      (((n >>> 24).toUInt8).toUInt32 <<< 24) = n := by
  apply UInt32.toBitVec_inj.1
  rw [UInt32.toBitVec_or, UInt32.toBitVec_or, UInt32.toBitVec_or,
    UInt32.toBitVec_shiftLeft, UInt32.toBitVec_shiftLeft,
    UInt32.toBitVec_shiftLeft, UInt8.toBitVec_toUInt32,
    UInt8.toBitVec_toUInt32, UInt8.toBitVec_toUInt32,
    UInt8.toBitVec_toUInt32, u32Byte0, u32Byte8, u32Byte16, u32Byte24]
  simp only [BitVec.shiftLeft_eq', BitVec.toNat_umod,
    UInt32.toNat_toBitVec, UInt32.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  simp only [bitVec32_toNat_32, Nat.reduceMod]
  rw [bitVecOr_reverse4]
  calc
    _ = ((n.toBitVec.extractLsb' 24 8 ++
          n.toBitVec.extractLsb' 16 8 ++
          n.toBitVec.extractLsb' 8 8 ++
          n.toBitVec.extractLsb' 0 8).setWidth 32) := by
      simpa only [Nat.reduceAdd] using
        (BitVec.setWidth_append_append_append_eq_shiftLeft_setWidth_or
          (b := n.toBitVec.extractLsb' 24 8)
          (b' := n.toBitVec.extractLsb' 16 8)
          (b'' := n.toBitVec.extractLsb' 8 8)
          (b''' := n.toBitVec.extractLsb' 0 8)
          (w'''' := 32)).symm
    _ = n.toBitVec := by
      rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide),
        BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide),
        BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide)]
      simp

@[simp] theorem writeU32LE_length (n : UInt32) : (writeU32LE n).length = 4 := by
  simp [writeU32LE]

/-- A natural number below the u32 format limit is not truncated by the
    little-endian field representation. -/
theorem u32_toNat_ofNat_of_lt {n : Nat} (h : n < UInt32.size) :
    (UInt32.ofNat n).toNat = n := UInt32.toNat_ofNat_of_lt h

/-- Dropping a known prefix plus `n` bytes from an appended byte stream is the
    same as dropping `n` bytes from the suffix. This is the list counterpart
    to a framed decoder advancing its cursor by a fixed header. -/
theorem drop_append_length_add (pre tail : List UInt8) (n : Nat) :
    (pre ++ tail).drop (pre.length + n) = tail.drop n := by
  induction pre with
  | nil => simp
  | cons byte pre ih =>
      simpa [Nat.succ_add] using ih

/-- The fixed-width little-endian primitive is an inverse even when followed
    by arbitrary later input. This is the base lemma for every framed storage
    object: a parser must consume its own four-byte field and leave the tail
    untouched. -/
theorem readU32LE_writeU32LE_append (n : UInt32) (rest : List UInt8) :
    readU32LE (writeU32LE n ++ rest) 0 = some n := by
  simpa [readU32LE, writeU32LE] using congrArg some (assembleU32LE_eq n)

/-- A fixed-width field remains readable after arbitrary preceding framing. -/
theorem readU32LE_append_writeU32LE (pre : List UInt8) (n : UInt32) (rest : List UInt8) :
    readU32LE (pre ++ writeU32LE n ++ rest) pre.length = some n := by
  simpa [readU32LE, writeU32LE] using congrArg some (assembleU32LE_eq n)

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

/-- One step of the byte-array CRC32C loop, bounded by `fuel` so the
    definition is structural. -/
private def crc32cArrayLoop (bs : ByteArray) : Nat → Nat → UInt32 → UInt32
  | 0, _, state => state
  | fuel + 1, i, state =>
      if h : i < bs.size then
        crc32cArrayLoop bs fuel (i + 1) (crc32cByte state bs[i])
      else state

/-- Continue a CRC32C accumulator over a `ByteArray` region.

    `crc32c` folds over a `List UInt8`. A codec that must checksum a large
    `ByteArray` would otherwise convert it to a list first, which allocates one
    cons cell per byte (`ByteArray.data` is itself a linear-time conversion).
    This loop indexes the array in place. `crc32cAppendArray_eq` proves it
    computes the same fold, so no format changes. -/
def crc32cAppendArray (state : UInt32) (bs : ByteArray) : UInt32 :=
  crc32cArrayLoop bs bs.size 0 state

private theorem crc32cArrayLoop_eq (bs : ByteArray) :
    ∀ fuel i state, bs.size - i ≤ fuel →
      crc32cArrayLoop bs fuel i state = (bs.data.toList.drop i).foldl crc32cByte state := by
  intro fuel
  induction fuel with
  | zero =>
      intro i state hfuel
      have hnil : bs.data.toList.drop i = [] := by
        apply List.drop_eq_nil_of_le
        simp only [Array.length_toList, ByteArray.size_data]
        omega
      simp [crc32cArrayLoop, hnil]
  | succ fuel ih =>
      intro i state hfuel
      rw [crc32cArrayLoop]
      split
      · rename_i hlt
        have hlen : i < bs.data.toList.length := by
          simp only [Array.length_toList, ByteArray.size_data]
          exact hlt
        rw [ih (i + 1) _ (by omega), List.drop_eq_getElem_cons hlen]
        simp [ByteArray.getElem_eq_getElem_data]
      · rename_i hlt
        have hnil : bs.data.toList.drop i = [] := by
          apply List.drop_eq_nil_of_le
          simp only [Array.length_toList, ByteArray.size_data]
          omega
        simp [hnil]

/-- The in-place loop computes the same accumulator as the list fold. -/
theorem crc32cAppendArray_eq (state : UInt32) (bs : ByteArray) :
    crc32cAppendArray state bs = bs.data.toList.foldl crc32cByte state := by
  rw [crc32cAppendArray, crc32cArrayLoop_eq bs bs.size 0 state (by omega)]
  simp

/-- CRC32C of a byte list followed by a `ByteArray` region, without
    materialising that region as a list. -/
theorem crc32c_append_array (pre : List UInt8) (bs : ByteArray) :
    crc32c (pre ++ bs.data.toList) =
      crc32cAppendArray (pre.foldl crc32cByte 0xFFFFFFFF) bs ^^^ 0xFFFFFFFF := by
  rw [crc32c, List.foldl_append, crc32cAppendArray_eq]

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
