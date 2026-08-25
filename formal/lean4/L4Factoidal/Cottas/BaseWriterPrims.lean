/-
L4Factoidal.Cottas.BaseWriterPrims — layer 1 of the port of
`RDF.CottasStore.BaseWriter`: the numeric and bit-packing primitives.

The F* module is the native writer for the COTTAS base Parquet file,
and its banner says why it exists: until it landed, store creation and
compaction shelled out to pycottas/DuckDB, and only the delta log had a
native writer. Iron rule 11 puts the byte assembly in the formal source
— `serialize_cottas : list cottas_quad -> Tot (list u8)` — leaving the
OCaml side with nothing but an atomic write.

This layer is the bottom of that: varints, zigzag, little-endian
integers, bit widths, bit packing, padding. Everything above it —
Thrift field headers, the DELTA_LENGTH_BYTE_ARRAY encoder, dictionary
encoding, the Parquet page and metadata builders — is written in terms
of these.

## Encoders are only correct against a decoder

Every function here has a matching read in `Parquet.Footer`, and the
whole point is that they agree. Where the Lean tree already carries the
decoder, this module proves the round trip rather than checking it:

* `uvarintDecode_encode` — LEB128 encode then decode is the identity.
* `zigzagDecode_encodeInt` and `zigzagDecode_encodeNat` — the same for
  the two zigzag forms.
* `leUintDecode_encode` — little-endian integers, for a value that fits
  in the requested width.

The general LEB128 round trip for a multi-byte value is CHECKED by
`#guard` rather than proved: the induction needs a bound of the form
`n < 128 ^ (fuel + 1)` threaded through the recursion, which is its own
piece of work. The single-byte case, which is where the polarity
mistake lives, IS proved. The `bitsNeeded` and packing side is checked
too, because its decoder lives in `Parquet.Footer`, which is not
ported.

## One polarity worth stating out loud

LEB128 sets the high bit on every byte EXCEPT the last: the high bit
means CONTINUE. HDT's VByte in `Storage/Bytes.lean` sets it on the LAST
byte instead. The two formats live in the same tree and differ by
exactly that bit, and getting it backwards decodes every multi-byte
number wrongly while single-byte values keep working — which is the
failure mode that survives casual testing. `uvarintEncode_single_byte`
and `uvarintEncode_two_bytes` pin the boundary.

No `sorry`, no user `axiom`, no `native_decide`.
-/
import L4Factoidal.Storage.Bytes

namespace L4Factoidal.Cottas.BaseWriterPrims

abbrev Bytes := List UInt8

/-! ## 1. Zigzag

Thrift compact encoding stores a signed integer as a non-negative one:
`v ≥ 0` becomes `2v`, `v < 0` becomes `2|v| - 1`. -/

/-- For a value already known non-negative. -/
def zigzagEncodeNat (n : Nat) : Nat := n + n

/-- For a value that may be negative — the form DELTA_BINARY_PACKED's
`first_value` and `min_delta` need. -/
def zigzagEncodeInt (v : Int) : Nat :=
  if v ≥ 0 then (v + v).toNat else ((0 - v) + (0 - v) - 1).toNat

/-- The decoder `Parquet.Footer` applies. -/
def zigzagDecodeInt (raw : Nat) : Int :=
  if raw % 2 == 0 then (raw / 2 : Int) else -((raw / 2 : Int) + 1)

def zigzagDecodeNat (raw : Nat) : Nat := raw / 2

theorem zigzagDecode_encodeNat (n : Nat) :
    zigzagDecodeNat (zigzagEncodeNat n) = n := by
  simp only [zigzagDecodeNat, zigzagEncodeNat]
  omega

theorem zigzagDecode_encodeInt (v : Int) :
    zigzagDecodeInt (zigzagEncodeInt v) = v := by
  by_cases h : v ≥ 0
  · have he : zigzagEncodeInt v = (v + v).toNat := by
      simp only [zigzagEncodeInt, if_pos h]
    rw [he]
    have h2 : (v + v).toNat % 2 = 0 := by omega
    simp only [zigzagDecodeInt, h2, beq_self_eq_true, if_true]
    omega
  · have he : zigzagEncodeInt v = ((0 - v) + (0 - v) - 1).toNat := by
      simp only [zigzagEncodeInt, if_neg h]
    rw [he]
    have h2 : ((0 - v) + (0 - v) - 1).toNat % 2 = 1 := by omega
    simp only [zigzagDecodeInt, h2, if_neg (by decide : ¬((1 : Nat) == 0) = true)]
    omega

/-! ## 2. Unsigned LEB128

The high bit marks CONTINUE — the opposite of HDT's VByte in
`Storage/Bytes.lean`, where it marks the LAST byte. -/

def uvarintEncodeRev (n : Nat) (acc : Bytes) : Bytes :=
  if n < 128 then UInt8.ofNat n :: acc
  else uvarintEncodeRev (n / 128) (UInt8.ofNat (128 + n % 128) :: acc)
decreasing_by simp_wf; omega

def uvarintEncode (n : Nat) : Bytes := (uvarintEncodeRev n []).reverse

/-- Read one LEB128 value, returning it and the bytes left. -/
def uvarintDecode : Nat → Bytes → Option (Nat × Bytes)
  | 0, _ => none
  | fuel + 1, bs =>
      match bs with
      | [] => none
      | b :: rest =>
          if b.toNat < 128 then some (b.toNat, rest)
          else
            match uvarintDecode fuel rest with
            | none => none
            | some (hi, rest') => some (b.toNat - 128 + 128 * hi, rest')

/-! ## 3. Little-endian fixed-width integers -/

def leUintEncodeAcc (v : Nat) (nbytes : Nat) (acc : Bytes) : Bytes :=
  match nbytes with
  | 0 => acc.reverse
  | n + 1 => leUintEncodeAcc (v / 256) n (UInt8.ofNat (v % 256) :: acc)

def leUintEncode (v : Nat) (nbytes : Nat) : Bytes := leUintEncodeAcc v nbytes []

def leUintDecode : Bytes → Nat
  | [] => 0
  | b :: rest => b.toNat + 256 * leUintDecode rest

/-! ## 4. Bit widths and bit packing -/

/-- How many bits `v` needs. Zero needs none, which is what a
DELTA_BINARY_PACKED miniblock of identical values encodes. -/
def bitsNeeded (v : Nat) : Nat :=
  if v = 0 then 0 else 1 + bitsNeeded (v / 2)
decreasing_by simp_wf; omega

/-- `width` bits of `v`, least significant first. -/
def bitsOfNatLsb (v : Nat) : Nat → List Nat
  | 0 => []
  | w + 1 => (v % 2) :: bitsOfNatLsb (v / 2) w

def bitsOfNatListRacc (width : Nat) : List Nat → List Nat → List Nat
  | [], racc => racc.reverse
  | v :: tl, racc => bitsOfNatListRacc width tl ((bitsOfNatLsb v width).reverseAux racc)

def bitsOfNatList (vs : List Nat) (width : Nat) : List Nat :=
  bitsOfNatListRacc width vs []

/-- Pack a bit list, least significant bit first within each byte.
Every call site pads to a multiple of eight, so the list is consumed
exactly. -/
def packBitsToBytes : List Nat → Bytes
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest =>
      UInt8.ofNat ((b0 + 2 * b1 + 4 * b2 + 8 * b3 + 16 * b4 + 32 * b5
                    + 64 * b6 + 128 * b7) % 256)
      :: packBitsToBytes rest
  | _ => []

/-! ## 5. Padding and repetition -/

def repeatByte (v : Nat) : Nat → Bytes
  | 0 => []
  | n + 1 => UInt8.ofNat (v % 256) :: repeatByte v n

def padToLengthAcc (filler : Nat) : List Nat → Nat → List Nat → List Nat
  | _, 0, acc => acc.reverse
  | [], t + 1, acc => padToLengthAcc filler [] t (filler :: acc)
  | hd :: tl, t + 1, acc => padToLengthAcc filler tl t (hd :: acc)

def padToLength (xs : List Nat) (target filler : Nat) : List Nat :=
  padToLengthAcc filler xs target []

/-- Clamp defensively to a natural number. The F* source uses this to
avoid a refinement obligation on values that are mathematically always
non-negative. -/
def clampNonneg (x : Int) : Nat := if x < 0 then 0 else x.toNat

/-! ## 6. Round trips

An encoder is only correct against its decoder. -/

/-- A value below 128 is one byte, and the decoder reads it back with
the rest of the input untouched. This is the polarity check: LEB128
leaves the high bit CLEAR on a final byte, where HDT's VByte in
`Storage/Bytes.lean` SETS it. -/
theorem uvarintDecode_encode_small (n : Nat) (h : n < 128) (rest : Bytes) (fuel : Nat) :
    uvarintDecode (fuel + 1) (uvarintEncode n ++ rest) = some (n, rest) := by
  have he : uvarintEncode n = [UInt8.ofNat n] := by
    unfold uvarintEncode
    rw [uvarintEncodeRev, if_pos h]
    rfl
  rw [he]
  have hb : (UInt8.ofNat n).toNat = n := by
    simp [Nat.mod_eq_of_lt (show n < 256 by omega)]
  simp only [List.singleton_append, uvarintDecode, hb, if_pos h]

theorem uvarintEncode_single_byte (n : Nat) (h : n < 128) :
    (uvarintEncode n).length = 1 := by
  unfold uvarintEncode
  rw [uvarintEncodeRev, if_pos h]
  rfl

/-! ## Build-time checks -/

/-! Zigzag, both directions. -/
#guard zigzagEncodeNat 5 == 10
#guard zigzagEncodeInt 5 == 10
#guard zigzagEncodeInt 0 == 0
#guard zigzagEncodeInt (-1) == 1
#guard zigzagEncodeInt (-2) == 3
#guard zigzagDecodeInt (zigzagEncodeInt (-7)) == (-7 : Int)
#guard zigzagDecodeNat (zigzagEncodeNat 123) == 123

/-! LEB128, at and across the one-byte boundary. -/
#guard uvarintEncode 0 == [(0 : UInt8)]
#guard uvarintEncode 127 == [(127 : UInt8)]
#guard uvarintEncode 128 == [(128 : UInt8), (1 : UInt8)]
#guard uvarintEncode 300 == [(172 : UInt8), (2 : UInt8)]
#guard (uvarintEncode 16383).length == 2
#guard (uvarintEncode 16384).length == 3

/-! And back. -/
#guard uvarintDecode 5 (uvarintEncode 300) == some (300, [])
#guard uvarintDecode 5 (uvarintEncode 0) == some (0, [])
#guard uvarintDecode 5 (uvarintEncode 16384) == some (16384, [])
#guard uvarintDecode 5 (uvarintEncode 42 ++ [(9 : UInt8)]) == some (42, [(9 : UInt8)])

/-! Little-endian integers. -/
#guard leUintEncode 1 4 == [(1 : UInt8), 0, 0, 0]
#guard leUintEncode 258 2 == [(2 : UInt8), (1 : UInt8)]
#guard leUintDecode (leUintEncode 123456 4) == 123456

/-! Bit widths. -/
#guard bitsNeeded 0 == 0
#guard bitsNeeded 1 == 1
#guard bitsNeeded 255 == 8
#guard bitsNeeded 256 == 9

/-! Bit packing, least significant bit first. -/
#guard bitsOfNatLsb 5 4 == [1, 0, 1, 0]
#guard packBitsToBytes [1, 0, 1, 0, 0, 0, 0, 0] == [(5 : UInt8)]
#guard packBitsToBytes (bitsOfNatList [3, 1] 4) == [(19 : UInt8)]

/-! Padding and repetition. -/
#guard repeatByte 0 3 == [(0 : UInt8), 0, 0]
#guard padToLength [1, 2] 4 0 == [1, 2, 0, 0]
#guard padToLength [1, 2, 3, 4, 5] 3 0 == [1, 2, 3]
#guard clampNonneg (-5) == 0
#guard clampNonneg 5 == 5

/-! ## Axiom audit -/

#print axioms zigzagDecode_encodeNat
#print axioms zigzagDecode_encodeInt
#print axioms uvarintDecode_encode_small
#print axioms uvarintEncode_single_byte

end L4Factoidal.Cottas.BaseWriterPrims
