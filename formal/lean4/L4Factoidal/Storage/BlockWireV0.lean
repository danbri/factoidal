/-
L4Factoidal.Storage.BlockWireV0 — first versioned byte boundary for BlockMvp.

This is deliberately a narrow transition format, not the final TermId block
format. It frames a sequence of direct RDF triples using the established
delta-log triple codec, then decodes the bytes before calling the proved block
scan. The format gives the MVP a real byte boundary without pretending that
direct RDF terms are the persistent cross-position ID model.

The delta triple codec intentionally refuses RDF 1.2 triple terms and
directional literals. `encode?` makes that refusal visible. The future Block
v1 codec replaces this representation after the RDF 1.2 identity and TermId
decisions, and must prove a general denotation round trip.
-/
import L4Factoidal.Storage.BlockMvp
import L4Factoidal.Storage.DeltaLog

namespace L4Factoidal.Storage.BlockWireV0

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.Storage
open L4Factoidal.Storage.BlockMvp

/-- `'BLK0'` in little-endian form. -/
def magic : UInt32 := 0x304B4C42
def version : UInt8 := 0

/-- The direct-term subset accepted by the inherited triple codec. -/
def termSupported : Term → Bool
  | .iri _ => true
  | .bnode _ => true
  | .literal l => l.val.direction.isNone
  | .tripleTerm _ _ _ => false

def tripleSupported (t : Triple) : Bool := termSupported t.o
def blockSupported (block : Block) : Bool := block.rows.all tripleSupported

private def byteArrayOfList (xs : List UInt8) : ByteArray :=
  ByteArray.mk xs.toArray

private def listOfByteArray (bs : ByteArray) : List UInt8 := bs.data.toList

/-- The portable byte sequence. Header: magic, version, row count; body:
    the inherited length-delimited triple encodings in physical row order;
    trailer: CRC32C of that body. -/
def encodeList (block : Block) : List UInt8 :=
  let payload := block.rows.flatMap serializeTriple
  writeU32LE magic ++ [version] ++ writeU32LE (UInt32.ofNat block.rows.length) ++
    payload ++ writeU32LE (crc32c payload)

/-- Encode when every row belongs to the v0 direct-term subset. -/
def encode? (block : Block) : Option ByteArray :=
  if blockSupported block then some (byteArrayOfList (encodeList block)) else none

def decodeRows : Nat → List UInt8 → Option (List Triple × List UInt8)
  | 0, bs => some ([], bs)
  | n + 1, bs => do
      let (row, afterRow) ← parseTriple bs
      let (rows, rest) ← decodeRows n afterRow
      some (row :: rows, rest)

/-- Decode one complete v0 block. Unknown versions, malformed rows, and
    trailing bytes are rejected. -/
def decode (bytes : ByteArray) : Option Block := do
  let allBytes := listOfByteArray bytes
  let foundMagic ← readU32LE allBytes 0
  if foundMagic != magic then none
  else do
    let (foundVersion, afterVersion) ← parseU8 (allBytes.drop 4)
    if foundVersion != version then none
    else do
      let count ← readU32LE afterVersion 0
      let bodyAndCrc := afterVersion.drop 4
      if bodyAndCrc.length < 4 then none
      else do
        let payloadLen := bodyAndCrc.length - 4
        let payload := bodyAndCrc.take payloadLen
        let storedCrc ← readU32LE bodyAndCrc payloadLen
        if storedCrc != crc32c payload then none
        else do
          let (rows, rest) ← decodeRows count.toNat payload
          if rest.isEmpty then some { rows := rows } else none

/-- Run the proved candidate scan only after a complete block decode. A bad
    byte sequence produces no candidates; a production backend reports this
    as a decode failure through its capability record. -/
def scanBoundDecoded (bound : PatternBound) (bytes : ByteArray) : List Triple :=
  match decode bytes with
  | none => []
  | some block => scanBound bound block

def scanDecoded (tp : TriplePattern) (bytes : ByteArray) (mu : Binding) : SolutionSeq :=
  match decode bytes with
  | none => []
  | some block => scan tp block mu

/-- Once a byte sequence has decoded to a block, its scan has the existing
    SPARQL triple-pattern meaning. -/
theorem scanDecoded_eq_evalTP (tp : TriplePattern) (bytes : ByteArray)
    (block : Block) (mu : Binding) (h : decode bytes = some block) :
    scanDecoded tp bytes mu = evalTP tp block.denotes mu := by
  simp only [scanDecoded, h]
  exact scan_eq_evalTP tp block mu

/-- Once a byte sequence has decoded to a block, its bounded candidate scan
    has the standard storage-bound meaning. -/
theorem scanBoundDecoded_eq_tripleMatchesBound (bound : PatternBound)
    (bytes : ByteArray) (block : Block) (h : decode bytes = some block) :
    scanBoundDecoded bound bytes = tripleMatchesBound bound block.denotes := by
  simp only [scanBoundDecoded, h]
  exact scanBound_eq_tripleMatchesBound bound block

end L4Factoidal.Storage.BlockWireV0
