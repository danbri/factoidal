/-
L4Factoidal.Storage.IndexedBlockWireV2 — predicate-segmented bytes for IndexedBlock.

`IBK2` retains V1's one shared term dictionary, but places ID rows in
predicate-local contiguous segments.  Its fixed-width directory makes the
physical segment of a predicate discoverable after only the header, dictionary
and directory have been read.  Each segment row carries its original source
position; full decode reconstructs the V1 source order and a selected scan
keeps the same observable order.

The fixed prefix includes the dictionary byte length.  A host can therefore
find the directory without speculative scanning of variable-length RDF terms.
Offsets below are relative to the start of the segment area.  This makes a
future range reader independent of whether the enclosing artifact is a local
file, `bytea`, object storage, OPFS, or a TiKV value.
-/
import L4Factoidal.Storage.IndexedBlockWireV1

namespace L4Factoidal.Storage.IndexedBlockWireV2

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.SPARQL.StoreBackend
open L4Factoidal.Storage
open L4Factoidal.Storage.IndexedBlock
open L4Factoidal.Storage.IndexedBlockWireV1
open L4Factoidal.Storage.BlockWireV0

/-- `'IBK2'` in little-endian form. -/
def magic : UInt32 := 0x324B4249
def version : UInt8 := 2

structure DirectoryEntry where
  predicate : TermId
  offset : Nat
  length : Nat
  deriving Repr, DecidableEq, Inhabited

/-- The fixed, 16-byte CRC-covered prefix after magic/version. -/
structure Prefix where
  dictCount : Nat
  rowCount : Nat
  segmentCount : Nat
  dictBytes : Nat
  deriving Repr, DecidableEq, Inhabited

def prefixBytes : Nat := 4 + 1 + 16

/-- A byte range in the canonical IBK2 artifact.  Offsets are absolute from
    byte zero, so this is also the narrow storage-backend contract. -/
structure ByteRange where
  offset : Nat
  length : Nat
  deriving Repr, DecidableEq, Inhabited

def dictionaryRange (header : Prefix) : ByteRange :=
  { offset := prefixBytes, length := header.dictBytes }

def directoryRange (header : Prefix) : ByteRange :=
  { offset := prefixBytes + header.dictBytes, length := header.segmentCount * 12 }

def segmentAreaOffset (header : Prefix) : Nat :=
  prefixBytes + header.dictBytes + header.segmentCount * 12

/-- The contiguous prefix a storage provider reads before it can select a
    predicate segment: framing, dictionary and directory. -/
def planningRange (header : Prefix) : ByteRange :=
  { offset := 0, length := segmentAreaOffset header }

private def byteArrayOfList (xs : List UInt8) : ByteArray := ByteArray.mk xs.toArray
private def listOfByteArray (bs : ByteArray) : List UInt8 := bs.data.toList

private def encodePositioned (entry : PositionedIdTriple) : List UInt8 :=
  writeU32LE (UInt32.ofNat entry.position) ++
  writeU32LE (UInt32.ofNat entry.row.s) ++ writeU32LE (UInt32.ofNat entry.row.p) ++
  writeU32LE (UInt32.ofNat entry.row.o)

private def encodeDirectory (entry : DirectoryEntry) : List UInt8 :=
  writeU32LE (UInt32.ofNat entry.predicate) ++ writeU32LE (UInt32.ofNat entry.offset) ++
  writeU32LE (UInt32.ofNat entry.length)

private def predicateIds (rows : List IdTriple) : List TermId :=
  rows.foldl (fun ids row => if ids.contains row.p then ids else ids ++ [row.p]) []

private def segments (block : Block) : List (TermId × List UInt8) :=
  (predicateIds block.rows.toList).map fun predicate =>
    (predicate, (predicateSegment predicate block).flatMap encodePositioned)

private def directoryFor (segments : List (TermId × List UInt8)) : List DirectoryEntry :=
  let (_, reversed) := segments.foldl (fun (state : Nat × List DirectoryEntry) segment =>
    let (offset, entries) := state
    let (predicate, bytes) := segment
    (offset + bytes.length, { predicate := predicate, offset := offset, length := bytes.length } :: entries)) (0, [])
  reversed.reverse

def supported (block : Block) : Bool :=
  IndexedBlockWireV1.supported block &&
    (segments block).all fun segment => fitsU32 segment.1 && fitsU32 segment.2.length

/-- Deterministic V2 bytes for a supported block.  Header: magic + version;
    CRC-covered payload: dictionary count, row count, segment count, terms,
    fixed-width directory, then contiguous segment bytes; trailer: CRC32C. -/
def encodeList (block : Block) : List UInt8 :=
  let segs := segments block
  let directory := directoryFor segs
  let encodedDict := block.dict.toList.flatMap serializeTerm
  let payload := writeU32LE (UInt32.ofNat block.dict.size) ++
    writeU32LE (UInt32.ofNat block.rows.size) ++ writeU32LE (UInt32.ofNat segs.length) ++
    writeU32LE (UInt32.ofNat encodedDict.length) ++ encodedDict ++ directory.flatMap encodeDirectory ++
    segs.flatMap (fun segment => segment.2)
  writeU32LE magic ++ [version] ++ payload ++ writeU32LE (crc32c payload)

def encode? (block : Block) : Option ByteArray :=
  if supported block then some (byteArrayOfList (encodeList block)) else none

private def decodeTerms : Nat → List UInt8 → Option (List Term × List UInt8)
  | 0, bytes => some ([], bytes)
  | n + 1, bytes => do
      let (term, afterTerm) ← parseTerm bytes
      let (terms, rest) ← decodeTerms n afterTerm
      some (term :: terms, rest)

private def decodeDirectory : Nat → List UInt8 → Option (List DirectoryEntry × List UInt8)
  | 0, bytes => some ([], bytes)
  | n + 1, bytes => do
      let predicate ← readU32LE bytes 0
      let offset ← readU32LE bytes 4
      let length ← readU32LE bytes 8
      let (entries, rest) ← decodeDirectory n (bytes.drop 12)
      some ({ predicate := predicate.toNat, offset := offset.toNat, length := length.toNat } :: entries, rest)

/-- Parse only the fixed prefix.  This is deliberately independent of CRC:
    a range reader obtains CRC/integrity evidence from its opened artifact
    manifest and verifies every subsequently supplied range before use. -/
def decodePrefix (bytes : ByteArray) : Option Prefix := do
  let allBytes := listOfByteArray bytes
  let foundMagic ← readU32LE allBytes 0
  if foundMagic != magic then none
  else do
    let (foundVersion, payloadPrefix) ← parseU8 (allBytes.drop 4)
    if foundVersion != version then none
    else do
      let dictCount ← readU32LE payloadPrefix 0
      let rowCount ← readU32LE payloadPrefix 4
      let segmentCount ← readU32LE payloadPrefix 8
      let dictBytes ← readU32LE payloadPrefix 12
      some (Prefix.mk dictCount.toNat rowCount.toNat segmentCount.toNat dictBytes.toNat)

private def distinctPredicates : List DirectoryEntry → Bool
  | [] => true
  | entry :: rest => !((rest.map DirectoryEntry.predicate).contains entry.predicate) && distinctPredicates rest

private def directoryContiguous : List DirectoryEntry → Nat → Bool
  | [], _ => true
  | entry :: rest, expected =>
      entry.length > 0 && entry.length % 16 == 0 && entry.offset == expected &&
        directoryContiguous rest (entry.offset + entry.length)

/-- Directory entries are deliberately required to be an exact partition of
    the segment area in on-disk order.  This rejects holes, overlaps, trailing
    bytes and non-row-aligned ranges before a selected segment is decoded. -/
private def directoryCovers (bytes : List UInt8) : List DirectoryEntry → Nat → Bool
  | [], expected => expected == bytes.length
  | entry :: rest, expected =>
      entry.length > 0 && entry.length % 16 == 0 && entry.offset == expected &&
        entry.offset + entry.length <= bytes.length &&
        directoryCovers bytes rest (entry.offset + entry.length)

private def decodeDictionaryAndDirectory? (header : Prefix) (dictionaryBytes directoryBytes : ByteArray) :
    Option (Array Term × List DirectoryEntry) := do
  if dictionaryBytes.size != header.dictBytes || directoryBytes.size != header.segmentCount * 12 then none
  else do
    let (terms, dictRest) ← decodeTerms header.dictCount (listOfByteArray dictionaryBytes)
    if !dictRest.isEmpty then none
    else do
      let (directory, directoryRest) ← decodeDirectory header.segmentCount (listOfByteArray directoryBytes)
      if !directoryRest.isEmpty || !distinctPredicates directory || !directoryContiguous directory 0 then none
      else some (terms.toArray, directory)

private def decodeSegmentRows (predicate : TermId) : Nat → List UInt8 → Option (List PositionedIdTriple)
  | 0, _ => some []
  | n + 1, bytes => do
      let position ← readU32LE bytes 0
      let s ← readU32LE bytes 4
      let p ← readU32LE bytes 8
      let o ← readU32LE bytes 12
      if p.toNat != predicate then none
      else do
        let rows ← decodeSegmentRows predicate n (bytes.drop 16)
        some ({ position := position.toNat, row := { s := s.toNat, p := p.toNat, o := o.toNat } } :: rows)

private def decodeSegment (segmentBytes : List UInt8) (entry : DirectoryEntry) : Option (List PositionedIdTriple) :=
  if entry.length % 16 != 0 || entry.offset + entry.length > segmentBytes.length then none
  else decodeSegmentRows entry.predicate (entry.length / 16)
    (segmentBytes.drop entry.offset |>.take entry.length)

private def orderedRows? (rowCount : Nat) (rows : List PositionedIdTriple) : Option (Array IdTriple) :=
  let ordered := rows.toArray.qsort (fun left right => left.position < right.position) |>.toList
  if ordered.length != rowCount then none
  else if (ordered.zipIdx.all fun (entry, position) => entry.position == position) then
    some (ordered.map PositionedIdTriple.row |>.toArray)
  else none

private def decodePayload (payload : List UInt8) : Option (Array Term × Array IdTriple) := do
  let dictCount ← readU32LE payload 0
  let rowCount ← readU32LE payload 4
  let segmentCount ← readU32LE payload 8
  let dictBytes ← readU32LE payload 12
  if dictBytes.toNat > (payload.drop 16).length then none
  else do
  let dictSection := (payload.drop 16).take dictBytes.toNat
  let (terms, dictRest) ← decodeTerms dictCount.toNat dictSection
  if !dictRest.isEmpty then none
  else do
  let (directory, segmentBytes) ← decodeDirectory segmentCount.toNat (payload.drop (16 + dictBytes.toNat))
  if !distinctPredicates directory || !directoryCovers segmentBytes directory 0 then none
  else do
    let segments ← directory.mapM (decodeSegment segmentBytes)
    let rows ← orderedRows? rowCount.toNat segments.flatten
    some (terms.toArray, rows)

/-- Decode one complete V2 block.  As well as V1's dictionary/reference and
    CRC checks, V2 rejects an ill-formed directory, mismatched segment
    predicates, non-contiguous segment bytes, duplicate source positions, and
    missing source positions. -/
def decode (bytes : ByteArray) : Option Block := do
  let allBytes := listOfByteArray bytes
  let foundMagic ← readU32LE allBytes 0
  if foundMagic != magic then none
  else do
    let (foundVersion, afterVersion) ← parseU8 (allBytes.drop 4)
    if foundVersion != version || afterVersion.length < 20 then none
    else do
      let payloadLen := afterVersion.length - 4
      let payload := afterVersion.take payloadLen
      let storedCrc ← readU32LE afterVersion payloadLen
      if storedCrc != crc32c payload then none
      else do
        let (dict, rows) ← decodePayload payload
        fromParts? dict rows

private def idForPredicate? (dict : Array Term) (predicate : WfIri) : Option TermId :=
  (dict.toList.zipIdx.find? fun (term, _) => term == .iri predicate).map (fun (_, id) => id)

/-- Plan the one segment required by a predicate-bound triple pattern using
    only the fixed header, dictionary and directory ranges.  It intentionally
    does not read the segment itself. -/
def predicateRange? (header : Prefix) (dictionaryBytes directoryBytes : ByteArray)
    (predicate : WfIri) : Option ByteRange := do
  let (dict, directory) ← decodeDictionaryAndDirectory? header dictionaryBytes directoryBytes
  let predicateId ← idForPredicate? dict predicate
  let entry ← directory.find? fun candidate => candidate.predicate == predicateId
  some { offset := segmentAreaOffset header + entry.offset, length := entry.length }

/-- The exact two-request plan for a predicate-bound IBK2 scan. The first
    range is contiguous framing/dictionary/directory; the second is the one
    selected segment. A provider may coalesce adjacent ranges. -/
def predicateReadRanges? (header : Prefix) (dictionaryBytes directoryBytes : ByteArray)
    (predicate : WfIri) : Option (List ByteRange) := do
  let segment ← predicateRange? header dictionaryBytes directoryBytes predicate
  some [planningRange header, segment]

def rangeBytes (ranges : List ByteRange) : Nat :=
  ranges.foldl (fun total range => total + range.length) 0

/-- Execute a predicate-bound scan from exactly four independently obtained
    IBK2 ranges: fixed header, dictionary, directory and selected segment.
    Integrity of those ranges is supplied by the artifact/manifest layer; this
    function validates their structural relation before decoding RDF values. -/
def scanPredicateRanges (bound : PatternBound) (headerBytes dictionaryBytes directoryBytes segmentBytes : ByteArray) :
    List Triple :=
  match bound.p with
  | none => []
  | some predicate =>
      match decodePrefix headerBytes with
      | none => []
      | some header =>
          match decodeDictionaryAndDirectory? header dictionaryBytes directoryBytes,
              predicateRange? header dictionaryBytes directoryBytes predicate with
          | some (dict, directory), some range =>
              if segmentBytes.size != range.length then []
              else
                match idForPredicate? dict predicate,
                    directory.find? (fun entry => segmentAreaOffset header + entry.offset == range.offset) with
                | some predicateId, some entry =>
                    let localEntry := { predicate := predicateId, offset := 0, length := entry.length }
                    match decodeSegment (listOfByteArray segmentBytes) localEntry with
                    | some rows =>
                        (rows.filterMap (fun positioned => decodeTriple? dict positioned.row)).filter (boundMatches bound)
                    | none => []
                | _, _ => []
          | _, _ => []

/-- Decode a row-aligned prefix of one predicate segment.  Unlike
    `scanPredicateRanges`, this is intentionally not a whole-segment answer:
    it is the range-reader primitive for a future bounded scan which keeps
    fetching prefixes until enough *matching* triples have been found.  The
    decoder refuses a prefix that is not an exact sequence of 16-byte rows or
    that exceeds the committed predicate segment. -/
def scanPredicateSegmentPrefix (bound : PatternBound) (headerBytes dictionaryBytes directoryBytes
    segmentPrefix : ByteArray) : List Triple :=
  match bound.p with
  | none => []
  | some predicate =>
      match decodePrefix headerBytes with
      | none => []
      | some header =>
          match decodeDictionaryAndDirectory? header dictionaryBytes directoryBytes,
              predicateRange? header dictionaryBytes directoryBytes predicate with
          | some (dict, _), some range =>
              if segmentPrefix.size > range.length || segmentPrefix.size % 16 != 0 then []
              else match idForPredicate? dict predicate with
                | none => []
                | some predicateId =>
                    let entry := { predicate := predicateId, offset := 0, length := segmentPrefix.size }
                    match decodeSegment (listOfByteArray segmentPrefix) entry with
                    | some rows =>
                        (rows.filterMap (fun positioned => decodeTriple? dict positioned.row)).filter
                          (boundMatches bound)
                    | none => []
          | _, _ => []

private def decodeForPredicate? (payload : List UInt8) (predicate : WfIri) : Option (Array Term × List PositionedIdTriple) := do
  let dictCount ← readU32LE payload 0
  let _rowCount ← readU32LE payload 4
  let segmentCount ← readU32LE payload 8
  let dictBytes ← readU32LE payload 12
  if dictBytes.toNat > (payload.drop 16).length then none
  else do
  let dictSection := (payload.drop 16).take dictBytes.toNat
  let (terms, dictRest) ← decodeTerms dictCount.toNat dictSection
  if !dictRest.isEmpty then none
  else do
  let (directory, segmentBytes) ← decodeDirectory segmentCount.toNat (payload.drop (16 + dictBytes.toNat))
  if !distinctPredicates directory || !directoryCovers segmentBytes directory 0 then none
  else do
    let dict := terms.toArray
    let predicateId ← idForPredicate? dict predicate
    let entry ← directory.find? fun candidate => candidate.predicate == predicateId
    let rows ← decodeSegment segmentBytes entry
    some (dict, rows)

/-- Decode only the dictionary/directory and the one predicate segment named by
    a bound predicate.  This is the executable selective-read meaning of V2;
    a range-capable host can supply exactly those same byte ranges later. -/
def scanPredicateDecoded (bound : PatternBound) (bytes : ByteArray) : List Triple :=
  match bound.p with
  | none => []
  | some predicate =>
      let allBytes := listOfByteArray bytes
      match readU32LE allBytes 0, parseU8 (allBytes.drop 4) with
      | some foundMagic, some (foundVersion, afterVersion) =>
          if foundMagic != magic || foundVersion != version || afterVersion.length < 20 then []
          else
            let payloadLen := afterVersion.length - 4
            let payload := afterVersion.take payloadLen
            match readU32LE afterVersion payloadLen with
            | some storedCrc =>
                if storedCrc != crc32c payload then []
                else match decodeForPredicate? payload predicate with
                  | some (dict, rows) =>
                      (rows.filterMap (fun entry => decodeTriple? dict entry.row)).filter (boundMatches bound)
                  | none => []
            | none => []
      | _, _ => []

private def sliceBytes (bytes : ByteArray) (range : ByteRange) : ByteArray :=
  bytes.extract range.offset (range.offset + range.length)

/-- An IBK2 artifact that has passed the whole-artifact decoder once at open
    time. Subsequent predicate-bound scans use the fixed header/dictionary/
    directory/segment range layout instead of rebuilding a predicate index. -/
structure OpenBlock where
  bytes : ByteArray
  decoded : Block
  header : Prefix

def open? (bytes : ByteArray) : Option OpenBlock := do
  let decoded ← decode bytes
  let header ← decodePrefix (sliceBytes bytes { offset := 0, length := prefixBytes })
  some { bytes := bytes, decoded := decoded, header := header }

/-- Opening is a checked admission boundary: a caller that received an
    `OpenBlock` also has a complete, CRC-checked IBK2 decode of exactly the
    same bytes.  Range scans must be constructed through this boundary rather
    than from an unchecked header. -/
theorem open?_decode_sound {bytes : ByteArray} {opened : OpenBlock}
    (h : open? bytes = some opened) : decode bytes = some opened.decoded := by
  simp only [open?, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨decoded, hdecode, header, _hheader, hopened⟩ := h
  cases hopened
  simpa using hdecode

/-- The byte identity retained by an opened artifact is the caller-supplied
    artifact, so later range offsets cannot accidentally be applied to a
    different byte sequence. -/
theorem open?_bytes_sound {bytes : ByteArray} {opened : OpenBlock}
    (h : open? bytes = some opened) : opened.bytes = bytes := by
  simp only [open?, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨decoded, _hdecode, header, _hheader, hopened⟩ := h
  cases hopened
  rfl

/-- The header stored by `open?` is parsed from the canonical fixed prefix of
    the very artifact that was fully decoded.  This keeps the later range
    layout tied to the opened bytes, not merely to an equal-looking header. -/
theorem open?_prefix_sound {bytes : ByteArray} {opened : OpenBlock}
    (h : open? bytes = some opened) :
    decodePrefix (sliceBytes bytes { offset := 0, length := prefixBytes }) = some opened.header := by
  simp only [open?, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨decoded, _hdecode, header, hheader, hopened⟩ := h
  cases hopened
  simpa using hheader

/-- The range-layout scan used after `open?` establishes whole-artifact
    integrity. An unbound predicate necessarily falls back to the decoded
    block; a bound predicate obtains exactly its dictionary, directory, and
    one segment from the canonical layout. -/
def scanBoundRange (bound : PatternBound) (opened : OpenBlock) : List Triple :=
  match bound.p with
  | none => IndexedBlock.scanBound bound opened.decoded
  | some predicate =>
      let dictionary := dictionaryRange opened.header
      let directory := directoryRange opened.header
      match predicateRange? opened.header (sliceBytes opened.bytes dictionary)
          (sliceBytes opened.bytes directory) predicate with
      | none => []
      | some segment =>
          scanPredicateRanges bound
            (sliceBytes opened.bytes { offset := 0, length := prefixBytes })
            (sliceBytes opened.bytes dictionary)
            (sliceBytes opened.bytes directory)
            (sliceBytes opened.bytes segment)

/-- The existing SPARQL backend seam for a verified/opened IBK2 artifact.
    This is intentionally the same `BackendReadOps` used by COTTAS/HDT and
    indexed blocks, so algebra and planning do not gain a second execution
    route for the new physical format. -/
def readOpsRange (opened : OpenBlock) : BackendReadOps :=
  { search := fun bound => scanBoundRange bound opened
  , estimate := fun bound => (scanBoundRange bound opened).length
  , predicatePresent := fun predicate => !(scanBoundRange { p := some predicate } opened).isEmpty }

/-- An unbound predicate never takes the range-only fast path: its observable
    candidates are exactly the decoded block's ordinary indexed scan. -/
theorem scanBoundRange_unbound (bound : PatternBound) (opened : OpenBlock)
    (h : bound.p = none) :
    scanBoundRange bound opened = IndexedBlock.scanBound bound opened.decoded := by
  cases bound with
  | mk s p o =>
      simp only at h
      subst p
      rfl

/-- `BackendReadOps.search` is definitionally the checked IBK2 range scan.
    This makes the existing SPARQL backend seam auditable without a separate
    execution implementation. -/
theorem readOpsRange_search (opened : OpenBlock) (bound : PatternBound) :
    (readOpsRange opened).search bound = scanBoundRange bound opened := rfl

end L4Factoidal.Storage.IndexedBlockWireV2
