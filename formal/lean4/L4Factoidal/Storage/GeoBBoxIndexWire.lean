/-
L4Factoidal.Storage.GeoBBoxIndexWire — GBI1 geometry bounding-box index bytes.

Design record: `docs/designissues/2026-09-05-geometry-bounding-box-index.md`,
section 6.

GBI1 is an immutable companion to one IBK3 or IBK4 block. It stores, for every
`geo:wktLiteral` term of the block dictionary whose geometry is inside the
proved fragment, that geometry's exact bounding box and its CRS; and it stores
the local IDs of the parseable geometries OUTSIDE the fragment, which are
always candidates and so may never be dropped.

    magic "GBI1", version 1
    prefix   u32 magic, u8 version, [32] targetIBKSha256,
             u32 dictCount, u32 entryCount, u32 opaqueCount,
             u32 crsCount, u32 crsBytes, u32 entriesBytes
    crs      crsCount entries: u32 byteLength, the CRS IRI in UTF-8.
             Index 0 is NOT stored and always means the default CRS84.
    entries  entryCount, strictly ascending by local ID, 44 bytes each:
             u32 localTermId, u32 crsIndex,
             4 x { u64 mantissa two's complement, u8 scale }
             for xmin, ymin, xmax, ymax
    opaque   opaqueCount strictly ascending u32 local IDs
    u32      crc32c(payload)

Coordinates stay EXACT: a mantissa and a decimal scale, never a float. A float
box would need an outward rounding rule to stay conservative, and the wrong
rounding direction is the silent-row-loss failure this whole index exists to
avoid.

An entry is fixed at 44 bytes because the lookup is a linear pass that compares
four decimals per entry. A variable-length entry would make that pass parse
before it can compare.

## Encoder admission equals decoder admission

`supported` is the encoder gate and `decode?` re-runs every one of its
conditions on what it reads back: both ID lists strictly ascending and below
`dictCount`, every CRS index at most `crsCount`, every scale below 256, every
mantissa inside the signed 64-bit range, `xmin <= xmax` and `ymin <= ymax` in
each box, and the areas covering the payload exactly.

## Two readers, proved equal

`decodeSpec?` reads through `List UInt8`; it states what GBI1 admits.
`decode?` reads the artifact by byte-array index, with no list materialised
per field. `decode_eq_spec` proves the two agree on EVERY input, so the fast
reader cannot admit or reject a byte string the specification does not.

The two share one `decodeUsing`, parameterised by a `Reader`; the theorem is
that the byte-indexed `Reader` equals the list `Reader`, pointwise, and is
therefore about the readers rather than about a restatement of the decoder.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.GeoBBoxIndex
import L4Factoidal.Storage.TermLocalIndexWireTheorems

namespace L4Factoidal.Storage.GeoBBoxIndexWire

open L4Factoidal.RDF
open L4Factoidal.Geo
open L4Factoidal.Storage
open L4Factoidal.Storage.BlockWireV0
open L4Factoidal.Storage.TermLocalIndexWire (readU32LEB byteAtB listOfByteArray
  byteArrayOfList readU32LEB_eq length_listOfByteArray)
open L4Factoidal.Storage.GeoBBoxIndex

def magic : UInt32 := 0x31494247 /-- `GBI1` little endian. -/
def version : UInt8 := 1
def prefixBytes : Nat := 4 + 1 + 32 + 4 + 4 + 4 + 4 + 4 + 4
def crcBytes : Nat := 4
/-- A `Scaled` on the wire: a two's-complement 64-bit mantissa and a scale. -/
def scaledBytes : Nat := 9
/-- `u32 id`, `u32 crsIndex`, four `Scaled`. -/
def entryBytes : Nat := 4 + 4 + 4 * scaledBytes

def two32 : Nat := 4294967296
def two63 : Nat := 9223372036854775808
def two64 : Nat := 18446744073709551616

structure Artifact where
  targetIBKSha256 : ByteArray
  index : Index
  deriving DecidableEq

/-! ## 1. Admission -/

def fitsU32 (n : Nat) : Bool := n < UInt32.size
def fitsI64 (m : Int) : Bool := -(two63 : Int) ≤ m && m < (two63 : Int)
def scaledSupported (s : Scaled) : Bool := fitsI64 s.mantissa && s.scale < 256

def boxSupported (b : BBox) : Bool :=
  scaledSupported b.xmin && scaledSupported b.ymin &&
  scaledSupported b.xmax && scaledSupported b.ymax &&
  Scaled.le b.xmin b.xmax && Scaled.le b.ymin b.ymax

/-- Strictly ascending local IDs. An equal pair is refused: each list is a
set, and a repeated ID would report a candidate twice. -/
def idsAscending : List Nat → Bool
  | [] | [_] => true
  | a :: b :: rest => a < b && idsAscending (b :: rest)

def entriesAscending : List Entry → Bool
  | [] | [_] => true
  | a :: b :: rest => a.id < b.id && entriesAscending (b :: rest)

/-- The encoder gate. `decode?` re-runs every conjunct on what it reads. -/
def supported (artifact : Artifact) : Bool :=
  artifact.targetIBKSha256.size == 32 &&
    fitsU32 artifact.index.dictCount &&
    fitsU32 artifact.index.entries.size &&
    fitsU32 artifact.index.opaqueIds.size &&
    fitsU32 artifact.index.crsTable.size &&
    artifact.index.crsTable.all (fun c => fitsU32 c.toUTF8.size) &&
    artifact.index.entries.toList.all (fun e =>
      e.id < artifact.index.dictCount &&
        e.crsIndex ≤ artifact.index.crsTable.size &&
        boxSupported e.box) &&
    entriesAscending artifact.index.entries.toList &&
    artifact.index.opaqueIds.toList.all (fun i => i < artifact.index.dictCount) &&
    idsAscending artifact.index.opaqueIds.toList

/-! ## 2. Encoding -/

/-- The unsigned 64-bit image of a mantissa inside the signed range. -/
def mantissaWord (m : Int) : Nat :=
  if m < 0 then ((two64 : Int) + m).toNat else m.toNat

def encodeScaled (s : Scaled) : List UInt8 :=
  let w := mantissaWord s.mantissa
  writeU32LE (UInt32.ofNat (w % two32)) ++ writeU32LE (UInt32.ofNat (w / two32)) ++
    [UInt8.ofNat s.scale]

def encodeEntry (e : Entry) : List UInt8 :=
  writeU32LE (UInt32.ofNat e.id) ++ writeU32LE (UInt32.ofNat e.crsIndex) ++
    encodeScaled e.box.xmin ++ encodeScaled e.box.ymin ++
    encodeScaled e.box.xmax ++ encodeScaled e.box.ymax

def encodeCrs (c : String) : List UInt8 :=
  let b := c.toUTF8.data.toList
  writeU32LE (UInt32.ofNat b.length) ++ b

def encode? (artifact : Artifact) : Option ByteArray :=
  if !supported artifact then none else
  let crs := artifact.index.crsTable.toList.flatMap encodeCrs
  let entries := artifact.index.entries.toList.flatMap encodeEntry
  let opaqueArea := artifact.index.opaqueIds.toList.flatMap
    (fun i => writeU32LE (UInt32.ofNat i))
  if !fitsU32 crs.length || !fitsU32 entries.length then none else
  let payload := artifact.targetIBKSha256.data.toList ++
    writeU32LE (UInt32.ofNat artifact.index.dictCount) ++
    writeU32LE (UInt32.ofNat artifact.index.entries.size) ++
    writeU32LE (UInt32.ofNat artifact.index.opaqueIds.size) ++
    writeU32LE (UInt32.ofNat artifact.index.crsTable.size) ++
    writeU32LE (UInt32.ofNat crs.length) ++
    writeU32LE (UInt32.ofNat entries.length) ++ crs ++ entries ++ opaqueArea
  some <| byteArrayOfList
    (writeU32LE magic ++ [version] ++ payload ++ writeU32LE (crc32c payload))

/-! ## 3. The two readers

Only the field reads differ. `listReader` walks `List UInt8`; `idxReader`
indexes the `ByteArray`. `readers_agree` proves them equal. -/

/-- One field access shape, so `decodeUsing` is written once. -/
structure Reader where
  u32 : Nat → Option UInt32
  u8 : Nat → Option UInt8
  size : Nat

def listReader (bytes : ByteArray) : Reader :=
  { u32 := fun off => readU32LE (listOfByteArray bytes) off
    u8 := fun off => (listOfByteArray bytes)[off]?
    size := bytes.size }

def idxReader (bytes : ByteArray) : Reader :=
  { u32 := fun off => readU32LEB bytes off
    u8 := fun off => byteAtB bytes off
    size := bytes.size }

def readScaled (r : Reader) (off : Nat) : Option Scaled := do
  let lo ← r.u32 off
  let hi ← r.u32 (off + 4)
  let sc ← r.u8 (off + 8)
  let w := hi.toNat * two32 + lo.toNat
  let m : Int := if w ≥ two63 then (w : Int) - (two64 : Int) else (w : Int)
  some { mantissa := m, scale := sc.toNat }

def readEntry (r : Reader) (off : Nat) : Option Entry := do
  let id ← r.u32 off
  let crsIndex ← r.u32 (off + 4)
  let xmin ← readScaled r (off + 8)
  let ymin ← readScaled r (off + 8 + scaledBytes)
  let xmax ← readScaled r (off + 8 + 2 * scaledBytes)
  let ymax ← readScaled r (off + 8 + 3 * scaledBytes)
  some { id := id.toNat, crsIndex := crsIndex.toNat,
         box := { xmin := xmin, ymin := ymin, xmax := xmax, ymax := ymax } }

def readEntries (r : Reader) : Nat → Nat → List Entry → Option (List Entry)
  | 0, _, acc => some acc.reverse
  | n + 1, off, acc => do
      let e ← readEntry r off
      readEntries r n (off + entryBytes) (e :: acc)

def readIds (r : Reader) : Nat → Nat → List Nat → Option (List Nat)
  | 0, _, acc => some acc.reverse
  | n + 1, off, acc => do
      let v ← r.u32 off
      readIds r n (off + 4) (v.toNat :: acc)

/-- The CRS table is small and cold, so both readers walk it as a list. -/
def parseCrsTable : Nat → List UInt8 → List String → Option (List String)
  | 0, rest, acc => if rest.isEmpty then some acc.reverse else none
  | n + 1, xs, acc => do
      let len ← readU32LE xs 0
      let raw := (xs.drop 4).take len.toNat
      if raw.length != len.toNat then none else do
      let text ← String.fromUTF8? (ByteArray.mk raw.toArray)
      if text.toUTF8.data.toList != raw then none else
        parseCrsTable n ((xs.drop 4).drop len.toNat) (text :: acc)

/-! ## 4. Decoding -/

/-- The one decoder, parameterised by how a field is read. -/
def decodeUsing (r : Reader) (bytes : ByteArray) : Option Artifact := do
  if r.size < prefixBytes + crcBytes then none else do
  let foundMagic ← r.u32 0
  if foundMagic != magic then none else do
  let foundVersion ← r.u8 4
  if foundVersion != version then none else do
  let dictCount ← r.u32 37
  let entryCount ← r.u32 41
  let opaqueCount ← r.u32 45
  let crsCount ← r.u32 49
  let crsLen ← r.u32 53
  let entriesLen ← r.u32 57
  if entriesLen.toNat != entryBytes * entryCount.toNat then none else do
  let payloadLength := 32 + 24 + crsLen.toNat + entriesLen.toNat + 4 * opaqueCount.toNat
  if r.size != 5 + payloadLength + crcBytes then none else do
  let storedCrc ← r.u32 (r.size - crcBytes)
  if storedCrc !=
      (crc32cAppendArray 0xFFFFFFFF (bytes.extract 5 (5 + payloadLength)) ^^^ 0xFFFFFFFF) then
    none else do
  let crsTable ← parseCrsTable crsCount.toNat
    (listOfByteArray (bytes.extract prefixBytes (prefixBytes + crsLen.toNat))) []
  let entriesStart := prefixBytes + crsLen.toNat
  let opaqueStart := entriesStart + entriesLen.toNat
  let entries ← readEntries r entryCount.toNat entriesStart []
  let opaqueIds ← readIds r opaqueCount.toNat opaqueStart []
  -- Every encoder condition, re-run on what was read.
  if !entries.all (fun e =>
        e.id < dictCount.toNat && e.crsIndex ≤ crsTable.length && boxSupported e.box) ||
      !entriesAscending entries ||
      !opaqueIds.all (fun i => i < dictCount.toNat) ||
      !idsAscending opaqueIds then none else
    some { targetIBKSha256 := bytes.extract 5 37
           index := { dictCount := dictCount.toNat
                      crsTable := crsTable.toArray
                      entries := entries.toArray
                      opaqueIds := opaqueIds.toArray } }

/-- The specification: what GBI1 admits, read through `List UInt8`. -/
def decodeSpec? (bytes : ByteArray) : Option Artifact :=
  decodeUsing (listReader bytes) bytes

/-- The artifact reader: the same admission, read by byte-array index. -/
def decode? (bytes : ByteArray) : Option Artifact :=
  decodeUsing (idxReader bytes) bytes

/-! ## 5. The two readers agree -/

theorem byteAtB_eq (bytes : ByteArray) (off : Nat) :
    byteAtB bytes off = (listOfByteArray bytes)[off]? := by
  have hlen : (listOfByteArray bytes).length = bytes.size := length_listOfByteArray bytes
  unfold TermLocalIndexWire.byteAtB
  split
  · rename_i h
    have h0 : off < (listOfByteArray bytes).length := by omega
    rw [List.getElem?_eq_getElem h0]
    simp [TermLocalIndexWire.listOfByteArray, ByteArray.getElem_eq_getElem_data]
  · rename_i h
    rw [List.getElem?_eq_none (by omega)]

theorem readers_agree (bytes : ByteArray) : idxReader bytes = listReader bytes := by
  unfold idxReader listReader
  congr 1
  · funext off; exact readU32LEB_eq bytes off
  · funext off; exact byteAtB_eq bytes off

/-- The byte-indexed reader admits exactly what the specification admits, on
every input. -/
theorem decode_eq_spec (bytes : ByteArray) : decode? bytes = decodeSpec? bytes := by
  unfold decode? decodeSpec?
  rw [readers_agree]

/-! ## 6. Samples -/

private def wkt (s : String) : Term :=
  .literal ⟨⟨s, ⟨wktLiteralIri, by rfl⟩, none, none⟩, by rfl⟩

private def sampleDict : Array Term :=
  #[wkt "POINT(1 1)", wkt "POINT(-5.25 12.5)",
    wkt "POLYGON((0 0, 10 0, 10 10, 0 10, 0 0))",
    wkt "LINESTRING(0 0, 1 1)",
    wkt "<http://www.opengis.net/def/crs/EPSG/0/27700> POINT(3 4)"]

private def sample : Artifact :=
  { targetIBKSha256 := ByteArray.mk (Array.replicate 32 7), index := build sampleDict }
private def sampleBytes : ByteArray := (encode? sample).getD ByteArray.empty
private def corrupt (b : ByteArray) : ByteArray :=
  if b.size == 0 then b else b.set! (b.size - 1) 0
private def unsortedEntries : Artifact :=
  { sample with index := { sample.index with entries := sample.index.entries.reverse } }
private def outOfRange : Artifact :=
  { sample with index := { sample.index with dictCount := 0 } }

#guard supported sample
#guard sampleBytes.size > prefixBytes + crcBytes
#guard decode? sampleBytes == some sample
#guard decodeSpec? sampleBytes == some sample
#guard decode? sampleBytes == decodeSpec? sampleBytes
#guard (decode? (corrupt sampleBytes)).isNone
#guard (decode? (sampleBytes.extract 0 (sampleBytes.size - 1))).isNone
#guard decode? (corrupt sampleBytes) == decodeSpec? (corrupt sampleBytes)
#guard (encode? unsortedEntries).isNone
#guard (encode? outOfRange).isNone
-- Negative coordinates survive the two's-complement round trip.
#guard ((decode? sampleBytes).map (fun a => a.index.entries.size)) == some 4
#guard ((decode? sampleBytes).map (fun a => a.index.opaqueIds)) == some #[3]
#guard ((decode? sampleBytes).map (fun a => a.index.crsTable.size)) == some 1
-- The decoded index answers the same candidates the built one does.
#guard ((decode? sampleBytes).map (fun a =>
    candidates? a.index GeoOp.within
      ((Wkt.parseLiteral "POLYGON((0 0, 4 0, 4 4, 0 4, 0 0))").getD ⟨none, .empty .polygon⟩)))
  == some (candidatesSpec sampleDict GeoOp.within
      ((Wkt.parseLiteral "POLYGON((0 0, 4 0, 4 4, 0 4, 0 0))").getD ⟨none, .empty .polygon⟩))
-- The MISS, through the decoded artifact.
#guard ((decode? sampleBytes).map (fun a =>
    candidates? a.index GeoOp.within
      ((Wkt.parseLiteral "POLYGON((900 900, 910 900, 910 910, 900 910, 900 900))").getD
        ⟨none, .empty .polygon⟩)))
  == some (some [3])

#print axioms decode_eq_spec

end L4Factoidal.Storage.GeoBBoxIndexWire
