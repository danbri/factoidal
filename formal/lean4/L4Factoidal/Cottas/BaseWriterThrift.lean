/-
L4Factoidal.Cottas.BaseWriterThrift — layer 2 of the port of
`RDF.CottasStore.BaseWriter`: the Thrift compact-protocol field
writers.

Parquet's file metadata is a Thrift struct in the COMPACT protocol, so
every field the writer emits goes through one of these. Each has a
matching read in `Parquet.Footer`, and the F\* source names the
decoder next to each writer — `decode_compact_binary_hex`,
`decode_compact_list_info_hex`, `nth_field_hex`.

## The two short forms, and where they stop

The compact protocol has a short and a long form for both field headers
and list headers, and the boundary is where an implementation goes
wrong quietly:

* A FIELD header is one byte when the id is 1 to 15 MORE than the
  previous id, packing the delta in the high nibble and the type in the
  low one. Otherwise the type goes alone in the low nibble and the id
  follows as a ZIGZAG varint. `fieldHeader_short` and
  `fieldHeader_long_at_16` pin both sides of that boundary.
* A LIST header is one byte for a count below 15, packing count and
  element type. At 15 and above the count moves to a PLAIN varint after
  a `0xF_` byte. `listHeader_short`, `listHeader_long_at_15` pin it.

Fifteen is the boundary in both cases and it is off by one between
them — a field DELTA of 15 still fits, a list COUNT of 15 does not.
Reading the two rules as the same rule is the mistake these theorems
exist to catch.

## Zigzag or not, per field

`i32` and `i64` values are ZIGZAG varints. A binary field's LENGTH is a
PLAIN varint — no zigzag — and so is a long-form list count. Mixing
them up produces values that are correct only when they are zero.
`i32_is_zigzag` and `binary_length_is_plain` state the difference.

## An issue this module must not reintroduce

<https://github.com/danbri/factoidal/issues/445>: the length prefix of
a binary field is the UTF-8 BYTE length, never the codepoint count. The
two coincide for ASCII, which is why the original bug went unnoticed.
`binaryLength_is_utf8_bytes` and a `#guard` on a multi-byte character
keep it fixed.

No `sorry`, no user `axiom`, no `native_decide`.
-/
import L4Factoidal.Cottas.BaseWriterPrims

namespace L4Factoidal.Cottas.BaseWriterThrift

open L4Factoidal.Cottas.BaseWriterPrims

/-! ## 1. The compact-protocol type codes

Same values as `Parquet.Footer`'s, which is what makes the writer and
the reader agree. -/

def tBoolTrue : Nat := 1
def tBoolFalse : Nat := 2
def tI32 : Nat := 5
def tI64 : Nat := 6
def tBinary : Nat := 8
def tList : Nat := 9
def tStruct : Nat := 12

/-! ## 2. Field headers -/

/-- Short form when the id advances by 1 to 15; long form otherwise. -/
def writeFieldHeader (fieldType fieldId prevId : Nat) : Bytes :=
  if fieldId > prevId && fieldId - prevId ≤ 15 then
    [UInt8.ofNat (((fieldId - prevId) % 16 * 16 + fieldType) % 256)]
  else
    UInt8.ofNat (fieldType % 256) :: uvarintEncode (zigzagEncodeNat fieldId)

def writeFieldI32 (fieldId prevId v : Nat) : Bytes :=
  writeFieldHeader tI32 fieldId prevId ++ uvarintEncode (zigzagEncodeNat v)

def writeFieldI64 (fieldId prevId v : Nat) : Bytes :=
  writeFieldHeader tI64 fieldId prevId ++ uvarintEncode (zigzagEncodeNat v)

/-- A binary field. The length is the UTF-8 BYTE length and a PLAIN
varint — see <https://github.com/danbri/factoidal/issues/445>. -/
def writeFieldBinary (fieldId prevId : Nat) (s : String) : Bytes :=
  let sbytes := s.toUTF8.toList
  writeFieldHeader tBinary fieldId prevId ++ uvarintEncode sbytes.length ++ sbytes

/-! ## 3. List headers -/

/-- Short form below 15; at 15 and above the count moves to a PLAIN
varint after a `0xF_` byte. -/
def writeListHeader (count etype : Nat) : Bytes :=
  if count < 15 then [UInt8.ofNat ((count % 16 * 16 + etype) % 256)]
  else UInt8.ofNat ((240 + etype) % 256) :: uvarintEncode count

def writeFieldListHeader (fieldId prevId count etype : Nat) : Bytes :=
  writeFieldHeader tList fieldId prevId ++ writeListHeader count etype

def writeStop : Bytes := [(0 : UInt8)]

/-! ## 4. Where the short forms stop -/

/-- A field id one to fifteen above the previous one is a single
byte. -/
theorem fieldHeader_short (fieldType fieldId prevId : Nat)
    (h1 : fieldId > prevId) (h2 : fieldId - prevId ≤ 15) :
    (writeFieldHeader fieldType fieldId prevId).length = 1 := by
  simp only [writeFieldHeader, if_pos (by simp [h1, h2] : (decide (fieldId > prevId) &&
    decide (fieldId - prevId ≤ 15)) = true)]
  rfl

/-- A delta of exactly 15 still fits — the boundary a list header does
NOT share. -/
theorem fieldHeader_short_at_15 (fieldType prevId : Nat) :
    (writeFieldHeader fieldType (prevId + 15) prevId).length = 1 :=
  fieldHeader_short fieldType (prevId + 15) prevId (by omega) (by omega)

/-- A delta of 16 does not: the header becomes a type byte plus a
zigzag varint id. -/
theorem fieldHeader_long_at_16 (fieldType prevId : Nat) :
    writeFieldHeader fieldType (prevId + 16) prevId
      = UInt8.ofNat (fieldType % 256)
        :: uvarintEncode (zigzagEncodeNat (prevId + 16)) := by
  simp only [writeFieldHeader,
             if_neg (by simp : ¬((decide (prevId + 16 > prevId) &&
               decide (prevId + 16 - prevId ≤ 15)) = true))]

/-- A count below 15 is a single byte. -/
theorem listHeader_short (count etype : Nat) (h : count < 15) :
    (writeListHeader count etype).length = 1 := by
  simp only [writeListHeader, if_pos h]
  rfl

/-- A count of exactly 15 does NOT fit, unlike a field delta of 15.
This is the off-by-one between the two rules. -/
theorem listHeader_long_at_15 (etype : Nat) :
    writeListHeader 15 etype
      = UInt8.ofNat ((240 + etype) % 256) :: uvarintEncode 15 := by
  simp only [writeListHeader, if_neg (by omega : ¬(15 < 15))]

/-! ## 5. Zigzag or plain, per field -/

/-- An `i32` value is a ZIGZAG varint. -/
theorem i32_is_zigzag (fieldId prevId v : Nat) :
    writeFieldI32 fieldId prevId v
      = writeFieldHeader tI32 fieldId prevId ++ uvarintEncode (zigzagEncodeNat v) := rfl

/-- A binary field's LENGTH is a plain varint, not a zigzag one. -/
theorem binary_length_is_plain (fieldId prevId : Nat) (s : String) :
    writeFieldBinary fieldId prevId s
      = writeFieldHeader tBinary fieldId prevId
        ++ uvarintEncode s.toUTF8.toList.length ++ s.toUTF8.toList := rfl

/-- **The length prefix counts UTF-8 BYTES, never codepoints**
(<https://github.com/danbri/factoidal/issues/445>). The two coincide
for ASCII, which is why the original defect survived. -/
theorem binaryLength_is_utf8_bytes (fieldId prevId : Nat) (s : String) :
    (writeFieldBinary fieldId prevId s).length
      = (writeFieldHeader tBinary fieldId prevId).length
        + (uvarintEncode s.toUTF8.toList.length).length
        + s.toUTF8.toList.length := by
  simp [writeFieldBinary]
  omega

/-! ## Build-time checks -/

/-! Field headers: the short form packs delta and type in one byte. -/
#guard writeFieldHeader tI32 1 0 == [(21 : UInt8)]
#guard writeFieldHeader tI64 2 1 == [(22 : UInt8)]
#guard (writeFieldHeader tI32 16 0).length == 2
#guard (writeFieldHeader tI32 15 0).length == 1

/-! `version = 1` as field 1 of the file metadata — the three bytes the
F* module pins with its own literal lemma. -/
#guard writeFieldI32 1 0 1 == [(21 : UInt8), (2 : UInt8)]
#guard writeFieldI32 1 0 125 == [(21 : UInt8), (250 : UInt8), (1 : UInt8)]

/-! List headers: short below 15, long at 15. -/
#guard writeListHeader 3 tStruct == [(60 : UInt8)]
#guard writeListHeader 14 tStruct == [(236 : UInt8)]
#guard (writeListHeader 15 tStruct).length == 2
#guard writeListHeader 15 tStruct == [(252 : UInt8), (15 : UInt8)]

/-! Fifteen is the boundary in both rules and it lands on opposite
sides: a field DELTA of 15 is short, a list COUNT of 15 is long. -/
#guard (writeFieldHeader tI32 15 0).length == 1
#guard (writeListHeader 15 tI32).length == 2

/-! Binary fields, ASCII and not. `"é"` is one codepoint and TWO UTF-8
bytes, so a codepoint count would write 1 where 2 is correct. -/
#guard writeFieldBinary 1 0 "ab"
        == [(24 : UInt8), (2 : UInt8), (97 : UInt8), (98 : UInt8)]
#guard "é".toUTF8.toList.length == 2
#guard "é".length == 1
#guard (writeFieldBinary 1 0 "é")[1]! == (2 : UInt8)

/-! The stop byte. -/
#guard writeStop == [(0 : UInt8)]

/-! ## Axiom audit -/

#print axioms fieldHeader_short_at_15
#print axioms fieldHeader_long_at_16
#print axioms listHeader_long_at_15
#print axioms binaryLength_is_utf8_bytes

end L4Factoidal.Cottas.BaseWriterThrift
