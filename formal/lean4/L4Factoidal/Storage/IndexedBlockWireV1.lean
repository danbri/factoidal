/-
L4Factoidal.Storage.IndexedBlockWireV1 — framed bytes for IndexedBlock.

V1 is the first direct byte representation of the shared dictionary plus ID
rows. The wire sequence is deterministic for a supplied IndexedBlock:

  magic, version, dictionary count, row count,
  length-delimited dictionary terms,
  (subjectId, predicateId, objectId)*,
  CRC32C of everything after the version.

The inherited term codec currently refuses RDF-star triple terms and directional
literals. V1 makes that boundary explicit; it is the direct-ID replacement for
BLK0 on the supported RDF subset, not yet the final RDF 1.2 codec.
-/
import L4Factoidal.Storage.IndexedBlock
import L4Factoidal.Storage.BlockWireV0
import L4Factoidal.Storage.DeltaLog

namespace L4Factoidal.Storage.IndexedBlockWireV1

open L4Factoidal.RDF
open L4Factoidal.Storage
open L4Factoidal.Storage.IndexedBlock
open L4Factoidal.Storage.BlockWireV0

/-- `'IBK1'` in little-endian form. -/
def magic : UInt32 := 0x314B4249
def version : UInt8 := 1

def fitsU32 (n : Nat) : Bool := n < 4294967296

def supported (block : Block) : Bool :=
  block.dict.toList.all termSupported && fitsU32 block.dict.size && fitsU32 block.rows.size &&
    block.rows.toList.all (fun row => fitsU32 row.s && fitsU32 row.p && fitsU32 row.o)

private def byteArrayOfList (xs : List UInt8) : ByteArray := ByteArray.mk xs.toArray
private def listOfByteArray (bs : ByteArray) : List UInt8 := bs.data.toList

private def encodeRow (row : IdTriple) : List UInt8 :=
  writeU32LE (UInt32.ofNat row.s) ++ writeU32LE (UInt32.ofNat row.p) ++
    writeU32LE (UInt32.ofNat row.o)

/-- The V1 representation of a supplied ID block. Call `encode?` when data may
    fall outside the current term-codec subset or U32 layout. -/
def encodeList (block : Block) : List UInt8 :=
  let payload := writeU32LE (UInt32.ofNat block.dict.size) ++
    writeU32LE (UInt32.ofNat block.rows.size) ++
    block.dict.toList.flatMap serializeTerm ++ block.rows.toList.flatMap encodeRow
  writeU32LE magic ++ [version] ++ payload ++ writeU32LE (crc32c payload)

def encode? (block : Block) : Option ByteArray :=
  if supported block then some (byteArrayOfList (encodeList block)) else none

private def decodeTerms : Nat → List UInt8 → Option (List Term × List UInt8)
  | 0, bytes => some ([], bytes)
  | n + 1, bytes => do
      let (term, afterTerm) ← parseTerm bytes
      let (terms, rest) ← decodeTerms n afterTerm
      some (term :: terms, rest)

private def decodeRows : Nat → List UInt8 → Option (List IdTriple × List UInt8)
  | 0, bytes => some ([], bytes)
  | n + 1, bytes => do
      let s ← readU32LE bytes 0
      let p ← readU32LE bytes 4
      let o ← readU32LE bytes 8
      let (rows, rest) ← decodeRows n (bytes.drop 12)
      some ({ s := s.toNat, p := p.toNat, o := o.toNat } :: rows, rest)

/-- Decode one complete V1 ID block. Unknown versions, duplicate dictionary
    entries, invalid ID references, malformed terms, and bad CRCs are refused. -/
def decode (bytes : ByteArray) : Option Block := do
  let allBytes := listOfByteArray bytes
  let foundMagic ← readU32LE allBytes 0
  if foundMagic != magic then none
  else do
    let (foundVersion, afterVersion) ← parseU8 (allBytes.drop 4)
    if foundVersion != version then none
    else do
      if afterVersion.length < 12 then none
      else do
        let payloadLen := afterVersion.length - 4
        let payload := afterVersion.take payloadLen
        let storedCrc ← readU32LE afterVersion payloadLen
        if storedCrc != crc32c payload then none
        else do
          let dictCount ← readU32LE payload 0
          let rowCount ← readU32LE payload 4
          let (dict, afterDict) ← decodeTerms dictCount.toNat (payload.drop 8)
          let (rows, rest) ← decodeRows rowCount.toNat afterDict
          if rest.isEmpty then fromParts? dict.toArray rows.toArray else none

end L4Factoidal.Storage.IndexedBlockWireV1
