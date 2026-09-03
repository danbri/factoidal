/-
L4Factoidal.Storage.IndexedBlockWireV3 — predicate-local rows plus a pageable
term dictionary.

`IBK3` is an additive physical successor to IBK2.  It admits one predicate per
immutable artifact, writes its fixed-width ID rows *before* a PTD1 pageable
dictionary, and retains the source-position field used by IBK2.  A range host
can therefore read a row prefix first, identify the small set of referenced
term pages, and then obtain only those PTD1 pages.  The term array and row
denotation remain exactly `IndexedBlock.Block`; no vocabulary interpretation
is encoded in this format.

IBK3 stores triples and has no graph column. The quad-aware successor is
`IndexedBlockWireV4` (IBK4), which adds a per-row graph column and a header
graph-set summary over its own `QuadBlock` type. IBK4 does not replace this
module: IBK3 artifacts stay readable and this file's bytes, denotation and
theorems are unchanged.

The current module establishes the canonical complete-artifact codec and its
range layout.  The range executor is deliberately added separately so its
partial-page admission and Merkle contracts can be tested against this full
decoder rather than guessed from a byte sketch.
-/
import L4Factoidal.Storage.IndexedBlockWireV2
import L4Factoidal.Storage.PagedTermDictionary

namespace L4Factoidal.Storage.IndexedBlockWireV3

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.SPARQL.StoreBackend
open L4Factoidal.Storage
open L4Factoidal.Storage.BlockWireV0
open L4Factoidal.Storage.IndexedBlock
open L4Factoidal.Storage.IndexedBlockWireV1
open L4Factoidal.Storage.PagedTermDictionary

/-- `'IBK3'` in little-endian form. -/
def magic : UInt32 := 0x334B4249
def version : UInt8 := 3
def magicVersionBytes : Nat := 4 + 1
def crcBytes : Nat := 4

/-- Fixed header: magic/version, row count and PTD1 byte length. -/
structure Prefix where
  rowCount : Nat
  dictionaryBytes : Nat
  deriving Repr, DecidableEq, Inhabited

def prefixBytes : Nat := 4 + 1 + 8
def rowBytes : Nat := 16

structure ByteRange where
  offset : Nat
  length : Nat
  deriving Repr, DecidableEq, Inhabited

def rowsRange (header : Prefix) : ByteRange :=
  { offset := prefixBytes, length := header.rowCount * rowBytes }

/-- A checked contiguous subset of fixed-width rows.  Unlike `rowsRange`,
    this is suitable for a resumable physical cursor: the caller receives no
    range at all when its requested start/count would extend beyond the
    declared immutable row extent. -/
def rowRange? (header : Prefix) (start count : Nat) : Option ByteRange :=
  if start > header.rowCount || count > header.rowCount - start then none
  else some
    { offset := (rowsRange header).offset + start * rowBytes
      length := count * rowBytes }

def dictionaryRange (header : Prefix) : ByteRange :=
  { offset := prefixBytes + header.rowCount * rowBytes, length := header.dictionaryBytes }

/-- First dictionary read after the fixed IBK3 header.  It is the fixed PTD1
    prefix, not the whole variable-width dictionary. -/
def dictionaryPrefixRange (header : Prefix) : Option ByteRange :=
  if header.dictionaryBytes < PagedTermDictionary.prefixBytes then none
  else some { offset := (dictionaryRange header).offset, length := PagedTermDictionary.prefixBytes }

/-- The second dictionary planning read, once the supplied PTD1 prefix has
    declared its page count.  Returned offsets are absolute IBK3 offsets. -/
def dictionaryDirectoryRange? (header : Prefix) (ptdPrefix : ByteArray) : Option ByteRange := do
  let ptd ← PagedTermDictionary.decodePrefix ptdPrefix
  if ptd.pageTerms != PagedTermDictionary.defaultPageTerms then none else do
  let relative := PagedTermDictionary.directoryRange ptd
  if relative.offset + relative.length > header.dictionaryBytes then none
  else some { offset := (dictionaryRange header).offset + relative.offset, length := relative.length }

def byteArrayOfList (xs : List UInt8) : ByteArray := ByteArray.mk xs.toArray
def listOfByteArray (bs : ByteArray) : List UInt8 := bs.data.toList

def encodeRow (entry : PositionedIdTriple) : List UInt8 :=
  writeU32LE (UInt32.ofNat entry.position) ++
  writeU32LE (UInt32.ofNat entry.row.s) ++ writeU32LE (UInt32.ofNat entry.row.p) ++
  writeU32LE (UInt32.ofNat entry.row.o)

def positionedRows (block : Block) : List PositionedIdTriple :=
  block.rows.toList.zipIdx.map fun (row, position) => { position, row }

def onePredicate (block : Block) : Bool :=
  match block.rows.toList with
  | [] => false
  | row :: rows => rows.all fun later => later.p == row.p

/-- IBK3 is deliberately predicate-local.  `IndexedBlockWireV1.supported`
    supplies the current term and 32-bit ID admission checks; PTD1 supplies
    its own term-codec admission check.

    The final conjunct is the decoder's own reconstruction admission.  `decode`
    finishes with `IndexedBlock.fromParts? dictionary rows` on exactly the
    dictionary and rows this block carries, and `fromParts?` refuses a
    dictionary with repeated terms (its ID map would not be injective) and rows
    whose IDs do not resolve to an RDF subject, predicate IRI and object.
    Running the same test here makes the encoder refuse precisely the blocks the
    decoder would refuse, so `IndexedBlockWireV3Theorems.decode_encode?` needs
    no hypothesis beyond `encode? block = some bytes`. -/
def supported (block : Block) : Bool :=
  IndexedBlockWireV1.supported block && onePredicate block &&
    PagedTermDictionary.supported block.dict &&
    (IndexedBlock.fromParts? block.dict block.rows).isSome

def encodeList (block : Block) : List UInt8 :=
  let rows := positionedRows block |>.flatMap encodeRow
  let dictionary := (PagedTermDictionary.encode? block.dict).getD ByteArray.empty |>.data.toList
  let payload := writeU32LE (UInt32.ofNat block.rows.size) ++
    writeU32LE (UInt32.ofNat dictionary.length) ++ rows ++ dictionary
  writeU32LE magic ++ [version] ++ payload ++ writeU32LE (crc32c payload)

/-- The IBK3 CRC-covered payload: row count, dictionary byte length, the
    fixed-width row area, then the whole PTD1 dictionary. `rows` is the encoded
    row area and `dictionary` the encoded PTD1 artifact, both supplied by
    `encode?`, so the specification and the assembler share one copy of each. -/
def encodeListPayload (block : Block) (dictionary : ByteArray) (rows : List UInt8) :
    List UInt8 :=
  writeU32LE (UInt32.ofNat block.rows.size) ++
    writeU32LE (UInt32.ofNat dictionary.size) ++ rows ++ dictionary.data.toList

/-- The complete IBK3 artifact as a byte list. This is the SPECIFICATION of the
    encoder output. `encodeBytes` assembles the same bytes without converting
    the dictionary to a list; `IndexedBlockWireV3Theorems.encodeBytes_eq` proves
    the two agree, and the round-trip proof reasons about this form. -/
def encodeListSpec (block : Block) (dictionary : ByteArray) (rows : List UInt8) :
    List UInt8 :=
  writeU32LE magic ++ [version] ++ encodeListPayload block dictionary rows ++
    writeU32LE (crc32c (encodeListPayload block dictionary rows))

/-- `encodeListSpec` assembled as a `ByteArray`.

    The dictionary carries every literal in the block and is the largest region
    of the artifact. Building the specification list would allocate one cons
    cell per dictionary byte, then copy the result back into a `ByteArray`. This
    appends the dictionary bytes directly and runs the CRC32C over them in
    place with `crc32cAppendArray`. `encodeBytes_eq` is the proof that the
    produced bytes are the specification's. -/
def encodeBytes (block : Block) (dictionary : ByteArray) (rows : List UInt8) : ByteArray :=
  let leading := writeU32LE (UInt32.ofNat block.rows.size) ++
    writeU32LE (UInt32.ofNat dictionary.size) ++ rows
  let checksum :=
    crc32cAppendArray (leading.foldl crc32cByte 0xFFFFFFFF) dictionary ^^^ 0xFFFFFFFF
  byteArrayOfList (writeU32LE magic ++ [version] ++ leading) ++ dictionary ++
    byteArrayOfList (writeU32LE checksum)

def encode? (block : Block) : Option ByteArray := do
  if !supported block then none else
  let dictionary ← PagedTermDictionary.encode? block.dict
  let rows := positionedRows block |>.flatMap encodeRow
  if dictionary.size >= UInt32.size || rows.length >= UInt32.size then none else
  some (encodeBytes block dictionary rows)

def decodePrefix (bytes : ByteArray) : Option Prefix := do
  let input := listOfByteArray bytes
  let foundMagic ← readU32LE input 0
  if foundMagic != magic then none else do
  let (foundVersion, rest) ← parseU8 (input.drop 4)
  if foundVersion != version then none else do
  let rowCount ← readU32LE rest 0
  let dictionaryBytes ← readU32LE rest 4
  some { rowCount := rowCount.toNat, dictionaryBytes := dictionaryBytes.toNat }

def readU32At? (bytes : ByteArray) (offset : Nat) : Option UInt32 := do
  let b0 ← bytes[offset]?
  let b1 ← bytes[offset + 1]?
  let b2 ← bytes[offset + 2]?
  let b3 ← bytes[offset + 3]?
  some (b0.toUInt32 ||| (b1.toUInt32 <<< 8) |||
    (b2.toUInt32 <<< 16) ||| (b3.toUInt32 <<< 24))

def decodeRowsGo : Nat → ByteArray → Nat → List PositionedIdTriple →
    Option (List PositionedIdTriple)
  | 0, _, _, reversed => some reversed.reverse
  | count + 1, bytes, offset, reversed => do
      let position ← readU32At? bytes offset
      let s ← readU32At? bytes (offset + 4)
      let p ← readU32At? bytes (offset + 8)
      let o ← readU32At? bytes (offset + 12)
      decodeRowsGo count bytes (offset + rowBytes)
        ({ position := position.toNat, row := { s := s.toNat, p := p.toNat, o := o.toNat } } :: reversed)

/-- Fixed-width row decoding consumes the byte stream with a reverse
    accumulator. The final reversal restores wire order once, without a
    data-sized post-recursion call stack. -/
def decodeRows (count : Nat) (bytes : ByteArray) : Option (List PositionedIdTriple) :=
  if bytes.size != count * rowBytes then none else decodeRowsGo count bytes 0 []

def canonicalOrder (rows : List PositionedIdTriple) : Bool :=
  rows.zipIdx.all fun (entry, position) => entry.position == position

/-- Rows are admitted when their positions are exactly `0, 1, ..., rowCount - 1`
    after sorting.  A canonical artifact (the encoder's output) already has its
    rows in that order, so it is checked directly; sorting is reserved for a
    non-canonical row order and gives the same answer, since sorting a list
    whose positions are already `0, 1, ...` returns that list.  The direct
    path is what the round-trip proof reasons about, as Lean core has no
    theorems about `Array.qsort`. -/
def orderedRows? (rowCount : Nat) (rows : List PositionedIdTriple) : Option (Array IdTriple) :=
  if rows.length != rowCount then none
  else if canonicalOrder rows then
    some (rows.map PositionedIdTriple.row |>.toArray)
  else
    let ordered := rows.toArray.qsort (fun left right => left.position < right.position) |>.toList
    if canonicalOrder ordered then
      some (ordered.map PositionedIdTriple.row |>.toArray)
    else none

def predicateLocal (rows : Array IdTriple) : Bool :=
  match rows.toList with
  | [] => false
  | row :: rest => rest.all fun later => later.p == row.p

/-- Decode an exact row-aligned prefix supplied by a range host.  It does not
    claim whole-block source-order validation; that is the full `decode`
    admission boundary.  It is the intentional first step of a bounded scan:
    row IDs determine which PTD1 term pages to obtain next. -/
def decodeRowPrefix? (bytes : ByteArray) : Option (List IdTriple) := do
  if bytes.size % rowBytes != 0 then none else do
  let rows ← decodeRows (bytes.size / rowBytes) bytes
  some (rows.map PositionedIdTriple.row)

private def validatedRowPredicateGo : Nat → Nat → ByteArray → Nat → Option Nat → Option Nat
  | 0, _, _, _, first => first
  | count + 1, termCount, bytes, offset, first => do
      let subject ← readU32At? bytes (offset + 4)
      let predicate ← readU32At? bytes (offset + 8)
      let object ← readU32At? bytes (offset + 12)
      if subject.toNat >= termCount || predicate.toNat >= termCount || object.toNat >= termCount then none else
      match first with
      | none => validatedRowPredicateGo count termCount bytes (offset + rowBytes) (some predicate.toNat)
      | some expected =>
          if predicate.toNat == expected then
            validatedRowPredicateGo count termCount bytes (offset + rowBytes) first
          else none

/-- Validate a nonempty fixed-width row range for the aggregate/ASK physical
    operators without building an `IdTriple` list. Every term ID must lie in
    the declared dictionary and every row must carry the same predicate ID;
    that ID is returned for one PTD1-page lookup. -/
def validatedRowPredicate? (termCount : Nat) (bytes : ByteArray) : Option Nat :=
  if bytes.isEmpty || bytes.size % rowBytes != 0 then none else
  validatedRowPredicateGo (bytes.size / rowBytes) termCount bytes 0 none

private def termIdsOfRows (rows : List IdTriple) : List Nat :=
  rows.flatMap fun row => [row.s, row.p, row.o]

/-- Plan the distinct PTD1 pages needed to turn a previously fetched IBK3 row
    prefix into RDF terms.  The host supplies only the PTD1 prefix, its fixed
    directory, and the row bytes; all returned page offsets are absolute in
    the enclosing IBK3 artifact. -/
def dictionaryPagesForRowPrefix? (header : Prefix) (ptdPrefix ptdDirectory rowPrefix : ByteArray) :
    Option (List ByteRange) := do
  let ptd ← PagedTermDictionary.decodePrefix ptdPrefix
  if ptd.pageTerms != PagedTermDictionary.defaultPageTerms then none else do
  let directory ← PagedTermDictionary.decodeDirectory? ptd ptdDirectory
  let rows ← decodeRowPrefix? rowPrefix
  let pages ← PagedTermDictionary.pageRangesForTerms? ptd directory (termIdsOfRows rows)
  if (pages.all fun page => page.offset + page.length <= header.dictionaryBytes) then
    some (pages.map fun page => { offset := (dictionaryRange header).offset + page.offset, length := page.length })
  else none

/-- The range counterpart of `dictionaryPagesForRowPrefix?`.  Page planning
    depends only on the decoded local IDs, but accepting the row start here
    keeps the planner's contract tied to the declared IBK3 row extent rather
    than trusting a host-provided byte slice. -/
def dictionaryPagesForRowRange? (header : Prefix) (rowStart : Nat)
    (ptdPrefix ptdDirectory rowBytes : ByteArray) : Option (List ByteRange) := do
  let rows ← decodeRowPrefix? rowBytes
  let _ ← rowRange? header rowStart rows.length
  let ptd ← PagedTermDictionary.decodePrefix ptdPrefix
  if ptd.pageTerms != PagedTermDictionary.defaultPageTerms then none else do
  let directory ← PagedTermDictionary.decodeDirectory? ptd ptdDirectory
  let pages ← PagedTermDictionary.pageRangesForTerms? ptd directory (termIdsOfRows rows)
  if (pages.all fun page => page.offset + page.length <= header.dictionaryBytes) then
    some (pages.map fun page => { offset := (dictionaryRange header).offset + page.offset, length := page.length })
  else none

private def lookupPageBytes? (pages : List (ByteRange × ByteArray)) (wanted : ByteRange) : Option ByteArray :=
  (pages.find? fun supplied => supplied.1 == wanted).map Prod.snd

private def pageIndexForAbsolute? (header : Prefix) (ptdHeader : PagedTermDictionary.Prefix)
    (directory : List PagedTermDictionary.PageEntry) (absolute : ByteRange) : Option Nat :=
  (directory.zipIdx.find? fun (entry, index) =>
    absolute == { offset := (dictionaryRange header).offset + PagedTermDictionary.pageAreaOffset ptdHeader + entry.offset,
                  length := entry.length }).map Prod.snd

private def decodeSuppliedPages? (header : Prefix) (ptdHeader : PagedTermDictionary.Prefix)
    (directory : List PagedTermDictionary.PageEntry) (pages : List (ByteRange × ByteArray)) :
    Option (List (Nat × Array Term)) :=
  pages.mapM fun (absolute, pageBytes) => do
    let page ← pageIndexForAbsolute? header ptdHeader directory absolute
    let terms ← PagedTermDictionary.decodePageArray? ptdHeader directory page pageBytes
    some (page, terms)

private def termFromDecodedPages? (ptdHeader : PagedTermDictionary.Prefix)
    (pages : List (Nat × Array Term)) (termId : TermId) : Option Term := do
  let page ← PagedTermDictionary.pageIndex? ptdHeader termId
  let terms ← (pages.find? fun decoded => decoded.1 == page).map Prod.snd
  terms[termId % ptdHeader.pageTerms]?

private def tripleFromDecodedPages? (ptdHeader : PagedTermDictionary.Prefix)
    (pages : List (Nat × Array Term))
    (row : IdTriple) : Option Triple := do
  let subjectTerm ← termFromDecodedPages? ptdHeader pages row.s
  let predicateTerm ← termFromDecodedPages? ptdHeader pages row.p
  let object ← termFromDecodedPages? ptdHeader pages row.o
  match subjectTerm, predicateTerm with
  | .iri subject, .iri predicate => some { s := .iri subject, p := predicate, o := object }
  | .bnode subject, .iri predicate => some { s := .bnode subject, p := predicate, o := object }
  | _, _ => none

/-- Execute one predicate-bound scan from a row-aligned prefix plus precisely
    the PTD1 pages it references. Every supplied page is identified by its
    absolute canonical IBK3 range. An omitted, mismatched, or malformed page,
    malformed planning input, or overlong row prefix returns `none`: it is
    never reported to a host as an empty query result. -/
def scanRowPrefixPages (bound : PatternBound) (headerBytes rowPrefix ptdPrefix ptdDirectory : ByteArray)
    (pages : List (ByteRange × ByteArray)) : Option (List Triple) :=
  if bound.p.isNone then none else match decodePrefix headerBytes, PagedTermDictionary.decodePrefix ptdPrefix with
  | some header, some ptdHeader =>
      if ptdHeader.pageTerms != PagedTermDictionary.defaultPageTerms then none else
      match PagedTermDictionary.decodeDirectory? ptdHeader ptdDirectory, decodeRowPrefix? rowPrefix with
      | some directory, some rows =>
          if rowPrefix.size > (rowsRange header).length then none
          else
            let decodedPages := decodeSuppliedPages? header ptdHeader directory pages
            decodedPages.bind fun decoded =>
              let triples := rows.mapM (tripleFromDecodedPages? ptdHeader decoded)
              triples.map (fun values => values.filter (boundMatches bound))
      | _, _ => none
  | _, _ => none

/-- Execute a predicate-bound scan over one checked contiguous row range.
    This has the same dictionary-page and term checks as the prefix executor;
    `rowStart` is an additional range-admission check, so a host cannot label
    an arbitrary row byte sequence as an in-bounds cursor page. -/
def scanRowRangePages (bound : PatternBound) (headerBytes : ByteArray) (rowStart : Nat)
    (rowBytes ptdPrefix ptdDirectory : ByteArray)
    (pages : List (ByteRange × ByteArray)) : Option (List Triple) :=
  if bound.p.isNone then none else match decodePrefix headerBytes, PagedTermDictionary.decodePrefix ptdPrefix with
  | some header, some ptdHeader =>
      if ptdHeader.pageTerms != PagedTermDictionary.defaultPageTerms then none else
      match PagedTermDictionary.decodeDirectory? ptdHeader ptdDirectory, decodeRowPrefix? rowBytes with
      | some directory, some rows =>
          match rowRange? header rowStart rows.length with
          | none => none
          | some _ =>
              let decodedPages := decodeSuppliedPages? header ptdHeader directory pages
              decodedPages.bind fun decoded =>
                let triples := rows.mapM (tripleFromDecodedPages? ptdHeader decoded)
                triples.map (fun values => values.filter (boundMatches bound))
      | _, _ => none
  | _, _ => none

/-! ## The admission decoder

`decode` runs on every IBK3 artifact at activation and on every block a query
opens. Reading it through `listOfByteArray` converts the whole artifact to a
`List UInt8`, one cons cell per byte; the payload is then copied again by
`List.drop`/`List.take`, `crc32c` folds over that copy, and the stored CRC read
drops the whole list once more. A sampler run on 2026-09-03 attributed 17 s of
a 66 s activation of a 28-block generation with 345 literals over 100 KB to
this decoder.

`decodeSpec` below keeps that list decoder as the SPECIFICATION of what IBK3
admits. `decode` reads the same fields by byte-array index, and checksums the
payload in place with `Bytes.crc32cAppendArray`.
`IndexedBlockWireV3Theorems.decode_eq_spec` proves

    decode bytes = decodeSpec bytes

for every `bytes`, so the format and the admission decision are unchanged. -/

/-- Complete admission decoder, stated over the byte list.  This is the
    SPECIFICATION; `decode` is proved equal to it.

    PTD1 validates its own canonical page layout and CRC; IBK3 validates its
    enclosing framing, row count/order, and CRC before restoring the
    established indexed-block denotation. -/
def decodeSpec (bytes : ByteArray) : Option Block := do
  let input := listOfByteArray bytes
  let header ← decodePrefix (bytes.extract 0 prefixBytes)
  if input.length < prefixBytes + header.rowCount * rowBytes + header.dictionaryBytes + 4 then none else do
  let payload := input.drop magicVersionBytes |>.take (input.length - magicVersionBytes - crcBytes)
  let storedCrc ← readU32LE input (input.length - crcBytes)
  if storedCrc != crc32c payload then none else do
  let rowsStart := prefixBytes
  let rowEnd := rowsStart + header.rowCount * rowBytes
  let dictionaryEnd := rowEnd + header.dictionaryBytes
  if dictionaryEnd + 4 != input.length then none else do
  let dictionaryBytes := bytes.extract rowEnd dictionaryEnd
  let ptd ← PagedTermDictionary.decodePrefix (dictionaryBytes.extract 0 PagedTermDictionary.prefixBytes)
  if ptd.pageTerms != PagedTermDictionary.defaultPageTerms then none else do
  let positioned ← decodeRows header.rowCount (bytes.extract rowsStart rowEnd)
  let rows ← orderedRows? header.rowCount positioned
  if !predicateLocal rows then none else do
  let dictionary ← PagedTermDictionary.decode? dictionaryBytes
  fromParts? dictionary rows

/-- Complete admission decoder, reading the artifact by byte-array index.

    The bytes admitted, and the block returned, are exactly `decodeSpec`'s;
    `IndexedBlockWireV3Theorems.decode_eq_spec` is that proof. -/
def decode (bytes : ByteArray) : Option Block := do
  let header ← decodePrefix (bytes.extract 0 prefixBytes)
  if bytes.size < prefixBytes + header.rowCount * rowBytes + header.dictionaryBytes + 4 then none else do
  let storedCrc ← readU32At? bytes (bytes.size - crcBytes)
  if storedCrc != (crc32cAppendArray 0xFFFFFFFF
      (bytes.extract magicVersionBytes (bytes.size - crcBytes)) ^^^ 0xFFFFFFFF) then none else do
  let rowsStart := prefixBytes
  let rowEnd := rowsStart + header.rowCount * rowBytes
  let dictionaryEnd := rowEnd + header.dictionaryBytes
  if dictionaryEnd + 4 != bytes.size then none else do
  let dictionaryBytes := bytes.extract rowEnd dictionaryEnd
  let ptd ← PagedTermDictionary.decodePrefix (dictionaryBytes.extract 0 PagedTermDictionary.prefixBytes)
  if ptd.pageTerms != PagedTermDictionary.defaultPageTerms then none else do
  let positioned ← decodeRows header.rowCount (bytes.extract rowsStart rowEnd)
  let rows ← orderedRows? header.rowCount positioned
  if !predicateLocal rows then none else do
  let dictionary ← PagedTermDictionary.decode? dictionaryBytes
  fromParts? dictionary rows

end L4Factoidal.Storage.IndexedBlockWireV3
