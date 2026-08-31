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
  let relative := PagedTermDictionary.directoryRange ptd
  if relative.offset + relative.length > header.dictionaryBytes then none
  else some { offset := (dictionaryRange header).offset + relative.offset, length := relative.length }

private def byteArrayOfList (xs : List UInt8) : ByteArray := ByteArray.mk xs.toArray
private def listOfByteArray (bs : ByteArray) : List UInt8 := bs.data.toList

private def encodeRow (entry : PositionedIdTriple) : List UInt8 :=
  writeU32LE (UInt32.ofNat entry.position) ++
  writeU32LE (UInt32.ofNat entry.row.s) ++ writeU32LE (UInt32.ofNat entry.row.p) ++
  writeU32LE (UInt32.ofNat entry.row.o)

private def positionedRows (block : Block) : List PositionedIdTriple :=
  block.rows.toList.zipIdx.map fun (row, position) => { position, row }

private def onePredicate (block : Block) : Bool :=
  match block.rows.toList with
  | [] => false
  | row :: rows => rows.all fun later => later.p == row.p

/-- IBK3 is deliberately predicate-local.  `IndexedBlockWireV1.supported`
    supplies the current term and 32-bit ID admission checks; PTD1 supplies
    its own term-codec admission check. -/
def supported (block : Block) : Bool :=
  IndexedBlockWireV1.supported block && onePredicate block &&
    PagedTermDictionary.supported block.dict

def encodeList (block : Block) : List UInt8 :=
  let rows := positionedRows block |>.flatMap encodeRow
  let dictionary := (PagedTermDictionary.encode? block.dict).getD ByteArray.empty |>.data.toList
  let payload := writeU32LE (UInt32.ofNat block.rows.size) ++
    writeU32LE (UInt32.ofNat dictionary.length) ++ rows ++ dictionary
  writeU32LE magic ++ [version] ++ payload ++ writeU32LE (crc32c payload)

def encode? (block : Block) : Option ByteArray := do
  if !supported block then none else
  let dictionary ← PagedTermDictionary.encode? block.dict
  let rows := positionedRows block |>.flatMap encodeRow
  if dictionary.size >= UInt32.size || rows.length >= UInt32.size then none else
  let payload := writeU32LE (UInt32.ofNat block.rows.size) ++
    writeU32LE (UInt32.ofNat dictionary.size) ++ rows ++ dictionary.data.toList
  some <| byteArrayOfList (writeU32LE magic ++ [version] ++ payload ++ writeU32LE (crc32c payload))

def decodePrefix (bytes : ByteArray) : Option Prefix := do
  let input := listOfByteArray bytes
  let foundMagic ← readU32LE input 0
  if foundMagic != magic then none else do
  let (foundVersion, rest) ← parseU8 (input.drop 4)
  if foundVersion != version then none else do
  let rowCount ← readU32LE rest 0
  let dictionaryBytes ← readU32LE rest 4
  some { rowCount := rowCount.toNat, dictionaryBytes := dictionaryBytes.toNat }

private def decodeRows : Nat → List UInt8 → Option (List PositionedIdTriple × List UInt8)
  | 0, bytes => some ([], bytes)
  | count + 1, bytes => do
      let position ← readU32LE bytes 0
      let s ← readU32LE bytes 4
      let p ← readU32LE bytes 8
      let o ← readU32LE bytes 12
      let (rows, rest) ← decodeRows count (bytes.drop rowBytes)
      some ({ position := position.toNat, row := { s := s.toNat, p := p.toNat, o := o.toNat } } :: rows, rest)

private def orderedRows? (rowCount : Nat) (rows : List PositionedIdTriple) : Option (Array IdTriple) :=
  let ordered := rows.toArray.qsort (fun left right => left.position < right.position) |>.toList
  if ordered.length != rowCount then none
  else if ordered.zipIdx.all (fun (entry, position) => entry.position == position) then
    some (ordered.map PositionedIdTriple.row |>.toArray)
  else none

private def predicateLocal (rows : Array IdTriple) : Bool :=
  match rows.toList with
  | [] => false
  | row :: rest => rest.all fun later => later.p == row.p

/-- Decode an exact row-aligned prefix supplied by a range host.  It does not
    claim whole-block source-order validation; that is the full `decode`
    admission boundary.  It is the intentional first step of a bounded scan:
    row IDs determine which PTD1 term pages to obtain next. -/
def decodeRowPrefix? (bytes : ByteArray) : Option (List IdTriple) := do
  if bytes.size % rowBytes != 0 then none else do
  let (rows, rest) ← decodeRows (bytes.size / rowBytes) (listOfByteArray bytes)
  if !rest.isEmpty then none else some (rows.map PositionedIdTriple.row)

private def termIdsOfRows (rows : List IdTriple) : List Nat :=
  rows.flatMap fun row => [row.s, row.p, row.o]

/-- Plan the distinct PTD1 pages needed to turn a previously fetched IBK3 row
    prefix into RDF terms.  The host supplies only the PTD1 prefix, its fixed
    directory, and the row bytes; all returned page offsets are absolute in
    the enclosing IBK3 artifact. -/
def dictionaryPagesForRowPrefix? (header : Prefix) (ptdPrefix ptdDirectory rowPrefix : ByteArray) :
    Option (List ByteRange) := do
  let ptd ← PagedTermDictionary.decodePrefix ptdPrefix
  let directory ← PagedTermDictionary.decodeDirectory? ptd ptdDirectory
  let rows ← decodeRowPrefix? rowPrefix
  let pages ← PagedTermDictionary.pageRangesForTerms? ptd directory (termIdsOfRows rows)
  if (pages.all fun page => page.offset + page.length <= header.dictionaryBytes) then
    some (pages.map fun page => { offset := (dictionaryRange header).offset + page.offset, length := page.length })
  else none

private def lookupPageBytes? (pages : List (ByteRange × ByteArray)) (wanted : ByteRange) : Option ByteArray :=
  (pages.find? fun supplied => supplied.1 == wanted).map Prod.snd

private def termFromPages? (header : Prefix) (ptdHeader : PagedTermDictionary.Prefix)
    (directory : List PagedTermDictionary.PageEntry) (pages : List (ByteRange × ByteArray))
    (termId : TermId) : Option Term := do
  let relative ← PagedTermDictionary.pageRange? ptdHeader directory termId
  let absolute : ByteRange :=
    { offset := (dictionaryRange header).offset + relative.offset, length := relative.length }
  let pageBytes ← lookupPageBytes? pages absolute
  PagedTermDictionary.decodeTermFromPage? ptdHeader directory termId pageBytes

private def tripleFromPages? (header : Prefix) (ptdHeader : PagedTermDictionary.Prefix)
    (directory : List PagedTermDictionary.PageEntry) (pages : List (ByteRange × ByteArray))
    (row : IdTriple) : Option Triple := do
  let subjectTerm ← termFromPages? header ptdHeader directory pages row.s
  let predicateTerm ← termFromPages? header ptdHeader directory pages row.p
  let object ← termFromPages? header ptdHeader directory pages row.o
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
  match decodePrefix headerBytes, PagedTermDictionary.decodePrefix ptdPrefix with
  | some header, some ptdHeader =>
      match PagedTermDictionary.decodeDirectory? ptdHeader ptdDirectory, decodeRowPrefix? rowPrefix with
      | some directory, some rows =>
          if rowPrefix.size > (rowsRange header).length then none
          else
            let triples := rows.mapM (tripleFromPages? header ptdHeader directory pages)
            triples.map (fun values => values.filter (boundMatches bound))
      | _, _ => none
  | _, _ => none

/-- Complete admission decoder.  PTD1 validates its own canonical page layout
    and CRC; IBK3 validates its enclosing framing, row count/order, and CRC
    before restoring the established indexed-block denotation. -/
def decode (bytes : ByteArray) : Option Block := do
  let input := listOfByteArray bytes
  let header ← decodePrefix (bytes.extract 0 prefixBytes)
  if input.length < prefixBytes + header.rowCount * rowBytes + header.dictionaryBytes + 4 then none else do
  let payload := input.drop 5 |>.take (input.length - 9)
  let storedCrc ← readU32LE input (input.length - 4)
  if storedCrc != crc32c payload then none else do
  let rowsStart := prefixBytes
  let rowEnd := rowsStart + header.rowCount * rowBytes
  let dictionaryEnd := rowEnd + header.dictionaryBytes
  if dictionaryEnd + 4 != input.length then none else do
  let (positioned, rowRest) ← decodeRows header.rowCount (input.drop rowsStart |>.take (rowEnd - rowsStart))
  if !rowRest.isEmpty then none else do
  let rows ← orderedRows? header.rowCount positioned
  if !predicateLocal rows then none else do
  let dictionary ← PagedTermDictionary.decode? (bytes.extract rowEnd dictionaryEnd)
  fromParts? dictionary rows

end L4Factoidal.Storage.IndexedBlockWireV3
