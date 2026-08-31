/-
L4Factoidal.Storage.SubjectRowIndexWire — SRI1 canonical subject postings.

SRI1 is a standalone, checksummed byte object for the subject-to-row mapping
of one predicate-local ID-row array.  It is deliberately separate from IBK3:
the old artifact stays readable while a later version can commit the IBK bytes
and this index together in one immutable manifest generation.

The payload has one `(subjectId, sourceRowOffset)` pair per row, ordered first
by subject ID and then by offset.  The ordering makes encoding canonical and
allows a range reader to binary-search a future directory.  Before a host
uses an offset it must still read the referenced IBK row and check its subject
ID: SRI1 alone cannot establish that cross-object relation.
-/
import L4Factoidal.Storage.SubjectRowIndex
import L4Factoidal.Storage.BlockWireV0

namespace L4Factoidal.Storage.SubjectRowIndexWire

open L4Factoidal.Storage
open L4Factoidal.Storage.IndexedBlock
open L4Factoidal.Storage.SubjectRowIndex

/-- `'SRI1'` in little-endian form. -/
def magic : UInt32 := 0x31495253
def version : UInt8 := 1
def prefixBytes : Nat := 13
def pairBytes : Nat := 8
def crcBytes : Nat := 4

private def byteArrayOfList (xs : List UInt8) : ByteArray := ByteArray.mk xs.toArray
private def listOfByteArray (bs : ByteArray) : List UInt8 := bs.data.toList

private def rawPairsGo : Nat → List IdTriple → List (Nat × Nat) → List (Nat × Nat)
  | _, [], reversed => reversed.reverse
  | offset, row :: rest, reversed => rawPairsGo (offset + 1) rest ((row.s, offset) :: reversed)

private def rawObjectPairsGo : Nat → List IdTriple → List (Nat × Nat) → List (Nat × Nat)
  | _, [], reversed => reversed.reverse
  | offset, row :: rest, reversed => rawObjectPairsGo (offset + 1) rest ((row.o, offset) :: reversed)

private def pairBefore (left right : Nat × Nat) : Bool :=
  left.1 < right.1 || (left.1 == right.1 && left.2 < right.2)

/-- Canonical posting pairs for source-order rows. -/
def pairsOfRows (rows : Array IdTriple) : List (Nat × Nat) :=
  (rawPairsGo 0 rows.toList []).toArray.qsort pairBefore |>.toList

/-- Canonical object-local-ID postings for the same fixed source rows.  The
    wire relation is intentionally generic `(local ID, row offset)`; SBM6
    gives this separately committed value an `objectIndex` role so it cannot
    be substituted for the subject sidecar at generation activation. -/
def pairsOfObjects (rows : Array IdTriple) : List (Nat × Nat) :=
  (rawObjectPairsGo 0 rows.toList []).toArray.qsort pairBefore |>.toList

private def encodePair (pair : Nat × Nat) : List UInt8 :=
  writeU32LE (UInt32.ofNat pair.1) ++ writeU32LE (UInt32.ofNat pair.2)

def supported (rows : Array IdTriple) : Bool :=
  rows.size < UInt32.size && rows.toList.all fun row => row.s < UInt32.size

/-- Canonical SRI1 encoding.  It refuses values which a u32 field would
    truncate; every accepted row produces exactly one payload pair. -/
def encode? (rows : Array IdTriple) : Option ByteArray :=
  if !supported rows then none else
    let pairs := pairsOfRows rows
    let body := writeU32LE magic ++ [version] ++ writeU32LE (UInt32.ofNat rows.size) ++
      writeU32LE (UInt32.ofNat pairs.length) ++ pairs.flatMap encodePair
    some (byteArrayOfList (body ++ writeU32LE (crc32c body)))

private def decodePairsGo : Nat → List UInt8 → List (Nat × Nat) → Option (List (Nat × Nat) × List UInt8)
  | 0, bytes, reversed => some (reversed.reverse, bytes)
  | count + 1, bytes, reversed => do
      let subject ← readU32LE bytes 0
      let offset ← readU32LE bytes 4
      decodePairsGo count (bytes.drop pairBytes) ((subject.toNat, offset.toNat) :: reversed)

private def canonicalPairsGo : Nat → List (Nat × Nat) → Bool
  | _, [] => true
  | _, [_] => true
  | rows, left :: right :: rest =>
      left.2 < rows && pairBefore left right && canonicalPairsGo rows (right :: rest)

private def canonicalPairs (rows : Nat) (pairs : List (Nat × Nat)) : Bool :=
  pairs.length == rows && canonicalPairsGo rows pairs

/-- Decode a complete SRI1 object.  Unknown version, truncated fields,
    checksum mismatch, duplicate offsets, unordered postings, and out-of-row
    offsets are rejected. -/
def decode (bytes : ByteArray) : Option (Nat × List (Nat × Nat)) := do
  let input := listOfByteArray bytes
  if input.length < prefixBytes + crcBytes then none else do
  let foundMagic ← readU32LE input 0
  if foundMagic != magic then none else do
  let (foundVersion, afterVersion) ← parseU8 (input.drop 4)
  if foundVersion != version then none else do
  let rowCount ← readU32LE afterVersion 0
  let pairCount ← readU32LE afterVersion 4
  let expected := prefixBytes + pairCount.toNat * pairBytes + crcBytes
  if input.length != expected then none else do
  let body := input.take (input.length - crcBytes)
  let storedCrc ← readU32LE input (input.length - crcBytes)
  if storedCrc != crc32c body then none else do
  let payload := input.drop prefixBytes |>.take (pairCount.toNat * pairBytes)
  let (pairs, rest) ← decodePairsGo pairCount.toNat payload []
  if !rest.isEmpty then none else do
  if !canonicalPairs rowCount.toNat pairs then none else some (rowCount.toNat, pairs)

/-- Lower-bound search over the canonical subject ordering. The fuel is the
    shrinking interval width, so this stays total even for malformed caller
    arrays; an admitted SRI1 payload supplies the expected ordering. -/
private def lowerBoundGo (pairs : Array (Nat × Nat)) (subject low high : Nat) : Nat → Nat
  | 0 => low
  | fuel + 1 =>
      if low >= high then low
      else
        let middle := low + (high - low) / 2
        match pairs[middle]? with
        | some pair =>
            if pair.1 < subject then lowerBoundGo pairs subject (middle + 1) high fuel
            else lowerBoundGo pairs subject low middle fuel
        | none => low

private def lowerBound (pairs : Array (Nat × Nat)) (subject : Nat) : Nat :=
  lowerBoundGo pairs subject 0 pairs.size (pairs.size + 1)

private def collectOffsetsGo (pairs : Array (Nat × Nat)) (subject index : Nat)
    (reversed : List Nat) : Nat → List Nat
  | 0 => reversed.reverse
  | fuel + 1 =>
      match pairs[index]? with
      | some pair =>
          if pair.1 == subject then
            collectOffsetsGo pairs subject (index + 1) (pair.2 :: reversed) fuel
          else reversed.reverse
      | none => reversed.reverse

/-- Lookup over an admitted canonical payload. It uses binary search to find
    the first subject posting and then reads only that subject's contiguous
    offsets, which remain in original source-row order. -/
def offsetsFor (pairs : List (Nat × Nat)) (subject : Nat) : List Nat :=
  let array := pairs.toArray
  collectOffsetsGo array subject (lowerBound array subject) [] (array.size + 1)

end L4Factoidal.Storage.SubjectRowIndexWire
