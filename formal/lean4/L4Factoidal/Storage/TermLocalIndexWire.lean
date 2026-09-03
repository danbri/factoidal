/-
L4Factoidal.Storage.TermLocalIndexWire — TLI1 pageable term-to-local-ID bytes.

TLI1 is an immutable companion to one IBK3 dictionary. Its order is the pure
TermLocalIndex order; a directory identifies small sorted pages so a range
reader can locate the one page which may contain a requested RDF term.
-/
import L4Factoidal.Storage.TermLocalIndex
import L4Factoidal.Storage.BlockWireV0

namespace L4Factoidal.Storage.TermLocalIndexWire

open L4Factoidal.RDF
open L4Factoidal.Storage
open L4Factoidal.Storage.BlockWireV0
open L4Factoidal.Storage.TermLocalIndex

def magic : UInt32 := 0x31494C54 /-- `TLI1` little endian. -/
def version : UInt8 := 1
def pageTerms : Nat := 256
def prefixBytes : Nat := 4 + 1 + 32 + 4 + 4 + 4 + 4 + 4
def crcBytes : Nat := 4

structure PageRef where
  firstKey : List UInt8
  offset : Nat
  length : Nat
  deriving DecidableEq

/-- The fixed TLI1 prefix.  A native range reader can obtain this before it
    fetches the variable-size page directory or any term page. -/
structure Prefix where
  targetIBKSha256 : ByteArray
  termCount : Nat
  pageCount : Nat
  directoryBytes : Nat
  pagesBytes : Nat
  deriving DecidableEq

structure Index where
  targetIBKSha256 : ByteArray
  entries : Array Entry
  deriving DecidableEq

def byteArrayOfList (xs : List UInt8) : ByteArray := ByteArray.mk xs.toArray
def listOfByteArray (xs : ByteArray) : List UInt8 := xs.data.toList
def fitsU32 (n : Nat) : Bool := n < UInt32.size

def lessKey : List UInt8 → List UInt8 → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => if a < b then true else if a == b then lessKey as bs else false

/-- Canonical byte ordering used by the TLI1 directory and pages. -/
def keyBefore (left right : List UInt8) : Bool := lessKey left right

def strictlyIncreasing : List Entry → Bool
  | [] | [_] => true
  | left :: right :: rest => lessKey left.key right.key && strictlyIncreasing (right :: rest)

def takeExact (n : Nat) (xs : List UInt8) : Option (List UInt8 × List UInt8) :=
  let taken := xs.take n
  if taken.length == n then some (taken, xs.drop n) else none

def encodeEntry (entry : Entry) : List UInt8 :=
  writeU32LE (UInt32.ofNat entry.key.length) ++ entry.key ++ writeU32LE (UInt32.ofNat entry.localId)

def chunks : Nat → List α → List (List α)
  | 0, _ => []
  | _ + 1, [] => []
  | fuel + 1, xs => xs.take pageTerms :: chunks fuel (xs.drop pageTerms)

def pageBytes (entries : List Entry) : List (List UInt8) :=
  (chunks entries.length entries).map (fun page => page.flatMap encodeEntry)

def pageRefs (pages : List (List UInt8)) (entries : List (List Entry)) : List PageRef :=
  let (_, reversed) := pages.zip entries |>.foldl (fun (state : Nat × List PageRef) pair =>
    let (offset, refs) := state
    let (bytes, page) := pair
    match page with
    | first :: _ => (offset + bytes.length, { firstKey := first.key, offset, length := bytes.length } :: refs)
    | [] => (offset, refs)) (0, [])
  reversed.reverse

def encodePageRef (ref : PageRef) : List UInt8 :=
  writeU32LE (UInt32.ofNat ref.firstKey.length) ++ ref.firstKey ++
    writeU32LE (UInt32.ofNat ref.offset) ++ writeU32LE (UInt32.ofNat ref.length)

/-- In a list with exactly `termCount` in-range, pairwise-distinct local IDs,
    every local ID is present exactly once.  The seen array replaces the old
    quadratic `eraseDups` pass in full TLI1 activation. -/
def localIdsPermutationGo : List Entry → Array Bool → Bool
  | [], _ => true
  | entry :: rest, seen =>
      match seen[entry.localId]? with
      | some false => localIdsPermutationGo rest (seen.set! entry.localId true)
      | _ => false

def localIdsPermutation (entries : List Entry) (termCount : Nat) : Bool :=
  entries.length == termCount && localIdsPermutationGo entries (Array.replicate termCount false)

/-- The TLI1 encoder admission gate.  Beside the size and key conditions it
    runs three checks `decode?` also runs on what it reads back:
    `localIdsPermutation`, which the decoder's `canonicalEntries` re-runs and
    which distinct-key ordering does not imply; and `termSupported` together
    with `termFitsU32b`, the two admission conditions of the term codec round
    trip `L4Factoidal.Storage.parseTerm_serializeTerm`, which `parseEntry`
    needs to rebuild the RDF term from the stored key.  Without these
    conjuncts the encoder would emit bytes its own decoder rejects. -/
def supported (index : Index) : Bool :=
  index.targetIBKSha256.size == 32 && index.entries.size < UInt32.size &&
    index.entries.toList.all (fun entry =>
      entry.localId < index.entries.size && entry.key == serializeTerm entry.term &&
        entry.key.length < UInt32.size && termSupported entry.term &&
        termFitsU32b entry.term) &&
    localIdsPermutation index.entries.toList index.entries.size

def encode? (index : Index) : Option ByteArray := do
  if !supported index then none else
  let entries := index.entries.toList
  /- Adjacent strict ordering is already the canonical lexical-order test.
     Avoid sorting the whole dictionary merely to confirm that invariant. -/
  if !strictlyIncreasing entries then none else
  let entryPages := chunks entries.length entries
  let pages := pageBytes entries
  let refs := pageRefs pages entryPages
  let directory := refs.flatMap encodePageRef
  let payload := index.targetIBKSha256.data.toList ++
    writeU32LE (UInt32.ofNat entries.length) ++ writeU32LE (UInt32.ofNat pageTerms) ++
    writeU32LE (UInt32.ofNat refs.length) ++ writeU32LE (UInt32.ofNat directory.length) ++
    writeU32LE (UInt32.ofNat pages.flatten.length) ++ directory ++ pages.flatten
  if !fitsU32 refs.length || !fitsU32 directory.length || !fitsU32 pages.flatten.length then none else
  some <| byteArrayOfList (writeU32LE magic ++ [version] ++ payload ++ writeU32LE (crc32c payload))

def parseEntry (xs : List UInt8) : Option (Entry × List UInt8) := do
  let keyLength ← readU32LE xs 0
  let (key, afterKey) ← takeExact keyLength.toNat (xs.drop 4)
  let localId ← readU32LE afterKey 0
  let (term, trailing) ← parseTerm key
  if !trailing.isEmpty || serializeTerm term != key then none else
    some ({ key, term, localId := localId.toNat }, afterKey.drop 4)

def parseEntries : Nat → List UInt8 → List Entry → Option (List Entry × List UInt8)
  | 0, xs, reversed => some (reversed.reverse, xs)
  | count + 1, xs, reversed => do
      let (entry, rest) ← parseEntry xs
      parseEntries count rest (entry :: reversed)

def parseRef (xs : List UInt8) : Option (PageRef × List UInt8) := do
  let firstLength ← readU32LE xs 0
  let (firstKey, afterKey) ← takeExact firstLength.toNat (xs.drop 4)
  let offset ← readU32LE afterKey 0
  let length ← readU32LE afterKey 4
  some ({ firstKey, offset := offset.toNat, length := length.toNat }, afterKey.drop 8)

def parseRefs : Nat → List UInt8 → List PageRef → Option (List PageRef × List UInt8)
  | 0, xs, reversed => some (reversed.reverse, xs)
  | count + 1, xs, reversed => do
      let (ref, rest) ← parseRef xs
      parseRefs count rest (ref :: reversed)

def pageEntryCount (termCount page : Nat) : Nat := min pageTerms (termCount - page * pageTerms)

def decodePages : Nat → List PageRef → List UInt8 → Nat → List Entry → Option (List Entry)
  | _, [], [], _, reversed => some reversed.reverse
  | _, [], _, _, _ => none
  | termCount, ref :: refs, xs, page, reversed => do
      let current := xs.take ref.length
      if current.length != ref.length then none else do
      let (entries, trailing) ← parseEntries (pageEntryCount termCount page) current []
      if !trailing.isEmpty then none else
      match entries with
      | first :: _ =>
          if first.key != ref.firstKey then none else
          decodePages termCount refs (xs.drop ref.length) (page + 1) (entries.reverse ++ reversed)
      | [] => none

def refsContiguous : List PageRef → Nat → Bool
  | [], _ => true
  | ref :: rest, expected => ref.length > 0 && ref.offset == expected && refsContiguous rest (expected + ref.length)

def refsStrictlyIncreasing : List PageRef → Bool
  | [] | [_] => true
  | left :: right :: rest => lessKey left.firstKey right.firstKey && refsStrictlyIncreasing (right :: rest)

def canonicalEntries (entries : List Entry) (termCount : Nat) : Bool :=
  strictlyIncreasing entries && localIdsPermutation entries termCount

/-- Strictly decode just the fixed-length TLI1 header. -/
def decodePrefix? (bytes : ByteArray) : Option Prefix := do
  if bytes.size != prefixBytes then none else do
  let input := listOfByteArray bytes
  let foundMagic ← readU32LE input 0
  if foundMagic != magic then none else do
  let (foundVersion, afterVersion) ← parseU8 (input.drop 4)
  if foundVersion != version then none else do
  let (target, afterTarget) ← takeExact 32 afterVersion
  let termCount ← readU32LE afterTarget 0
  let foundPageTerms ← readU32LE afterTarget 4
  let pageCount ← readU32LE afterTarget 8
  let directoryBytes ← readU32LE afterTarget 12
  let pagesBytes ← readU32LE afterTarget 16
  if foundPageTerms.toNat != pageTerms ||
      pageCount.toNat != (termCount.toNat + pageTerms - 1) / pageTerms then none else
    some { targetIBKSha256 := byteArrayOfList target, termCount := termCount.toNat,
           pageCount := pageCount.toNat, directoryBytes := directoryBytes.toNat,
           pagesBytes := pagesBytes.toNat }

/-- Strictly decode only the variable directory.  Page payloads remain
    unfetched; offsets are relative to the start of that payload. -/
def decodeDirectory? (header : Prefix) (bytes : ByteArray) : Option (List PageRef) := do
  if bytes.size != header.directoryBytes then none else do
  let (refs, trailing) ← parseRefs header.pageCount (listOfByteArray bytes) []
  if !trailing.isEmpty || !refsContiguous refs 0 || !refsStrictlyIncreasing refs ||
      refs.foldl (fun total ref => total + ref.length) 0 != header.pagesBytes then none else
    some refs

/-- The one candidate page for a canonical term key.  If the key precedes the
    first directory key, the first page is returned so the caller can prove
    absence by its ordinary exact lookup. -/
def pageFor? (refs : List PageRef) (wanted : List UInt8) : Option (Nat × PageRef) :=
  let rec go : Nat → List PageRef → Option (Nat × PageRef) → Option (Nat × PageRef)
    | _, [], best => best
    | ordinal, ref :: rest, best =>
        if lessKey wanted ref.firstKey then best.getD (ordinal, ref)
        else go (ordinal + 1) rest (some (ordinal, ref))
  go 0 refs none

/-- Decode one selected page.  The entry count follows from the header and
    page ordinal, while canonical in-page ordering and RDF term decoding are
    checked here.  Cross-page/global permutation checks remain the job of the
    full `decode?` admission decoder. -/
def decodePage? (header : Prefix) (ordinal : Nat) (ref : PageRef) (bytes : ByteArray) : Option (Array Entry) := do
  if ordinal >= header.pageCount || bytes.size != ref.length then none else do
  let (entries, trailing) ← parseEntries (pageEntryCount header.termCount ordinal) (listOfByteArray bytes) []
  match entries with
  | [] => none
  | first :: _ =>
      if !trailing.isEmpty || first.key != ref.firstKey ||
          !strictlyIncreasing entries ||
          !entries.all (fun entry => entry.localId < header.termCount) then none else
        some entries.toArray

/-! ## The byte-indexed admission decoder

`decode?` runs on every TLI1 sidecar at activation. Reading it through
`listOfByteArray` converts the whole artifact to a `List UInt8`, one cons cell
per byte, and then walks that list with `List.take`/`List.drop`: the payload,
the directory and the page area are each copied again, and the page walk drops
the whole remaining page area once per page, which is quadratic in the page
count. Per entry it also rebuilt the canonical term serialization as a list to
compare it with the stored key.

`decodeSpec?` below keeps that list decoder as the SPECIFICATION of what TLI1
admits. `decode?` reads the same fields by byte-array index, checksums the
payload in place with `Bytes.crc32cAppendArray`, extracts one page at a time,
and compares the re-serialized key as packed bytes.
`TermLocalIndexWireTheorems.decode?_eq_spec` proves

    decode? bytes = decodeSpec? bytes

for every `bytes`, so the format and the admission decision are unchanged. -/

/-- `readU32LE` at a byte-array offset, with no list conversion. -/
def readU32LEB (bytes : ByteArray) (off : Nat) : Option UInt32 :=
  if h : off + 4 <= bytes.size then
    some ((bytes[off]'(by omega)).toUInt32 |||
      ((bytes[off + 1]'(by omega)).toUInt32 <<< 8) |||
      ((bytes[off + 2]'(by omega)).toUInt32 <<< 16) |||
      ((bytes[off + 3]'(by omega)).toUInt32 <<< 24))
  else none

/-- `parseU8` at a byte-array offset. -/
def byteAtB (bytes : ByteArray) (off : Nat) : Option UInt8 :=
  if h : off < bytes.size then some (bytes[off]'h) else none

/-- `serializeLString` as packed bytes. -/
def serializeLStringBytes (s : String) : ByteArray :=
  let b := s.toUTF8
  byteArrayOfList (writeU32LE (UInt32.ofNat b.size)) ++ b

/-- `serializeTerm` as packed bytes.

    `parseEntry` confirms that the stored key is the canonical serialization of
    the term it parsed. That check is NOT redundant: `parseTerm` reads each
    length-prefixed field with `String.fromUTF8?`, and nothing in the term
    codec proves that re-encoding the decoded `String` reproduces the stored
    bytes, so the comparison is what rejects a key whose bytes are not the
    canonical spelling of its own term. Building the comparison operand as a
    `List UInt8` allocated one cons cell per key byte for every entry; this
    builds the same bytes packed.
    `TermLocalIndexWireTheorems.serializeTermBytes_eq` proves it equals
    `serializeTerm`. -/
def serializeTermBytes : Term -> ByteArray
  | .iri i => byteArrayOfList [termTagIri] ++ serializeLStringBytes i.val
  | .bnode b => byteArrayOfList [termTagBnode] ++ serializeLStringBytes b
  | .literal l =>
      byteArrayOfList [termTagLiteral] ++
        (serializeLStringBytes l.val.lexicalForm ++
          serializeLStringBytes l.val.datatype.val ++
          (match l.val.langTag with
           | none => byteArrayOfList [(0 : UInt8)]
           | some tag => byteArrayOfList [(1 : UInt8)] ++ serializeLStringBytes tag))
  | .tripleTerm _ _ _ => byteArrayOfList [termTagTripleTerm]

/-- `parseEntry` at a byte-array offset.  Returns the entry and the offset of
    the first byte after it. -/
def parseEntryB (bytes : ByteArray) (off : Nat) : Option (Entry × Nat) := do
  let keyLength <- readU32LEB bytes off
  let keyEnd := off + 4 + keyLength.toNat
  if keyEnd > bytes.size then none else do
  let keySlice := bytes.extract (off + 4) keyEnd
  let localId <- readU32LEB bytes keyEnd
  let key := listOfByteArray keySlice
  let (term, trailing) <- parseTerm key
  if !trailing.isEmpty || serializeTermBytes term != keySlice then none else
    some ({ key, term, localId := localId.toNat }, keyEnd + 4)

/-- `parseEntries` at a byte-array offset. -/
def parseEntriesB (bytes : ByteArray) : Nat -> Nat -> List Entry -> Option (List Entry × Nat)
  | 0, off, reversed => some (reversed.reverse, off)
  | count + 1, off, reversed => do
      let (entry, next) <- parseEntryB bytes off
      parseEntriesB bytes count next (entry :: reversed)

/-- `decodePages` over the packed page area.  One page is extracted at a time,
    so the walk is linear in the page area instead of dropping the remaining
    area once per page. -/
def decodePagesB : Nat -> List PageRef -> ByteArray -> Nat -> Nat -> List Entry -> Option (List Entry)
  | _, [], pages, off, _, reversed => if off == pages.size then some reversed.reverse else none
  | termCount, ref :: refs, pages, off, page, reversed => do
      if off + ref.length > pages.size then none else do
      let current := pages.extract off (off + ref.length)
      let (entries, trailing) <- parseEntriesB current (pageEntryCount termCount page) 0 []
      if trailing != current.size then none else
      match entries with
      | first :: _ =>
          if first.key != ref.firstKey then none else
          decodePagesB termCount refs pages (off + ref.length) (page + 1)
            (entries.reverse ++ reversed)
      | [] => none

/-- The TLI1 admission decoder, stated over the byte list.  This is the
    SPECIFICATION; `decode?` is proved equal to it. -/
def decodeSpec? (bytes : ByteArray) : Option Index := do
  let input := listOfByteArray bytes
  let foundMagic ← readU32LE input 0
  if foundMagic != magic then none else do
  let (foundVersion, afterVersion) ← parseU8 (input.drop 4)
  if foundVersion != version || input.length < prefixBytes + crcBytes then none else do
  let (target, afterTarget) ← takeExact 32 afterVersion
  let termCount ← readU32LE afterTarget 0
  let foundPageTerms ← readU32LE afterTarget 4
  let pageCount ← readU32LE afterTarget 8
  let directoryBytes ← readU32LE afterTarget 12
  let pagesBytes ← readU32LE afterTarget 16
  if foundPageTerms.toNat != pageTerms ||
      pageCount.toNat != (termCount.toNat + pageTerms - 1) / pageTerms then none else do
  let payloadLength := 32 + 20 + directoryBytes.toNat + pagesBytes.toNat
  if input.length != 5 + payloadLength + crcBytes then none else do
  let payload := afterVersion.take payloadLength
  let storedCrc ← readU32LE input (input.length - crcBytes)
  if storedCrc != crc32c payload then none else do
  let directory := payload.drop 52 |>.take directoryBytes.toNat
  let pages := payload.drop (52 + directoryBytes.toNat) |>.take pagesBytes.toNat
  let (refs, trailing) ← parseRefs pageCount.toNat directory []
  if !trailing.isEmpty || !refsContiguous refs 0 ||
      refs.foldl (fun total ref => total + ref.length) 0 != pages.length then none else do
  let entries ← decodePages termCount.toNat refs pages 0 []
  if !canonicalEntries entries termCount.toNat then none else
    some { targetIBKSha256 := byteArrayOfList target, entries := entries.toArray }

/-- The TLI1 admission decoder, reading the artifact by byte-array index. -/
def decode? (bytes : ByteArray) : Option Index := do
  let foundMagic <- readU32LEB bytes 0
  if foundMagic != magic then none else do
  let foundVersion <- byteAtB bytes 4
  if foundVersion != version || bytes.size < prefixBytes + crcBytes then none else do
  let termCount <- readU32LEB bytes 37
  let foundPageTerms <- readU32LEB bytes 41
  let pageCount <- readU32LEB bytes 45
  let directoryBytes <- readU32LEB bytes 49
  let pagesBytes <- readU32LEB bytes 53
  if foundPageTerms.toNat != pageTerms ||
      pageCount.toNat != (termCount.toNat + pageTerms - 1) / pageTerms then none else do
  let payloadLength := 32 + 20 + directoryBytes.toNat + pagesBytes.toNat
  if bytes.size != 5 + payloadLength + crcBytes then none else do
  let storedCrc <- readU32LEB bytes (bytes.size - crcBytes)
  if storedCrc !=
      (crc32cAppendArray 0xFFFFFFFF (bytes.extract 5 (5 + payloadLength)) ^^^ 0xFFFFFFFF) then
    none else do
  let directory := bytes.extract 57 (57 + directoryBytes.toNat)
  let pages := bytes.extract (57 + directoryBytes.toNat)
    (57 + directoryBytes.toNat + pagesBytes.toNat)
  let (refs, trailing) <- parseRefs pageCount.toNat (listOfByteArray directory) []
  if !trailing.isEmpty || !refsContiguous refs 0 ||
      refs.foldl (fun total ref => total + ref.length) 0 != pages.size then none else do
  let entries <- decodePagesB termCount.toNat refs pages 0 0 []
  if !canonicalEntries entries termCount.toNat then none else
    some { targetIBKSha256 := bytes.extract 5 37, entries := entries.toArray }

private def ex : WfIri := ⟨"https://example.test/a", by decide⟩
private def ex2 : WfIri := ⟨"https://example.test/b", by decide⟩
private def sampleTerms : Array Term := #[.iri ex2, .bnode "b", .iri ex]
private def sample : Index := { targetIBKSha256 := ByteArray.mk (Array.replicate 32 7), entries := entriesOf sampleTerms }
private def duplicateLocalIds : List Entry :=
  match sample.entries.toList with
  | first :: second :: rest => first :: { second with localId := first.localId } :: rest
  | entries => entries
private def sampleBytes : ByteArray := (encode? sample).getD ByteArray.empty
private def twoPageTerms : Array Term :=
  (List.range (pageTerms + 1)).map (fun n => Term.bnode s!"term-{n}") |>.toArray
private def twoPage : Index := { targetIBKSha256 := ByteArray.mk (Array.replicate 32 9), entries := entriesOf twoPageTerms }
private def twoPageBytes : ByteArray := (encode? twoPage).getD ByteArray.empty
private def corrupt (bytes : ByteArray) : ByteArray :=
  if bytes.size == 0 then bytes else bytes.set! (bytes.size - 1) 0
private def wrongTarget : Index := { sample with targetIBKSha256 := ByteArray.mk (Array.replicate 32 8) }
private def samplePageLookup : Option (Option Nat) := do
  let header ← decodePrefix? (sampleBytes.extract 0 prefixBytes)
  let refs ← decodeDirectory? header (sampleBytes.extract prefixBytes (prefixBytes + header.directoryBytes))
  let (ordinal, ref) ← pageFor? refs (serializeTerm (.iri ex))
  let page ← decodePage? header ordinal ref
    (sampleBytes.extract (prefixBytes + header.directoryBytes + ref.offset)
      (prefixBytes + header.directoryBytes + ref.offset + ref.length))
  some (lookup? page (.iri ex))

#guard decode? sampleBytes == some sample
#guard decodeSpec? sampleBytes == decode? sampleBytes
#guard decodeSpec? twoPageBytes == decode? twoPageBytes
#guard decodeSpec? (corrupt sampleBytes) == decode? (corrupt sampleBytes)
#guard decodeSpec? (sampleBytes.extract 0 (sampleBytes.size - 1))
  == decode? (sampleBytes.extract 0 (sampleBytes.size - 1))
#guard localIdsPermutation sample.entries.toList sample.entries.size
#guard !localIdsPermutation duplicateLocalIds sample.entries.size
#guard (decodePrefix? (sampleBytes.extract 0 prefixBytes)).map Prefix.termCount == some sample.entries.size
#guard samplePageLookup == some (some 2)
#guard decode? twoPageBytes == some twoPage
#guard (decode? (corrupt sampleBytes)).isNone
#guard decode? ((encode? wrongTarget).getD ByteArray.empty) == some wrongTarget

end L4Factoidal.Storage.TermLocalIndexWire
