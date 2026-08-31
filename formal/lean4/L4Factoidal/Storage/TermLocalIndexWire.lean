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

private def byteArrayOfList (xs : List UInt8) : ByteArray := ByteArray.mk xs.toArray
private def listOfByteArray (xs : ByteArray) : List UInt8 := xs.data.toList
private def fitsU32 (n : Nat) : Bool := n < UInt32.size

private def lessKey : List UInt8 → List UInt8 → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => if a < b then true else if a == b then lessKey as bs else false

/-- Canonical byte ordering used by the TLI1 directory and pages. -/
def keyBefore (left right : List UInt8) : Bool := lessKey left right

private def strictlyIncreasing : List Entry → Bool
  | [] | [_] => true
  | left :: right :: rest => lessKey left.key right.key && strictlyIncreasing (right :: rest)

private def takeExact (n : Nat) (xs : List UInt8) : Option (List UInt8 × List UInt8) :=
  let taken := xs.take n
  if taken.length == n then some (taken, xs.drop n) else none

private def encodeEntry (entry : Entry) : List UInt8 :=
  writeU32LE (UInt32.ofNat entry.key.length) ++ entry.key ++ writeU32LE (UInt32.ofNat entry.localId)

private def chunks : Nat → List α → List (List α)
  | 0, _ => []
  | _ + 1, [] => []
  | fuel + 1, xs => xs.take pageTerms :: chunks fuel (xs.drop pageTerms)

private def pageBytes (entries : List Entry) : List (List UInt8) :=
  (chunks entries.length entries).map (fun page => page.flatMap encodeEntry)

private def pageRefs (pages : List (List UInt8)) (entries : List (List Entry)) : List PageRef :=
  let (_, reversed) := pages.zip entries |>.foldl (fun (state : Nat × List PageRef) pair =>
    let (offset, refs) := state
    let (bytes, page) := pair
    match page with
    | first :: _ => (offset + bytes.length, { firstKey := first.key, offset, length := bytes.length } :: refs)
    | [] => (offset, refs)) (0, [])
  reversed.reverse

private def encodePageRef (ref : PageRef) : List UInt8 :=
  writeU32LE (UInt32.ofNat ref.firstKey.length) ++ ref.firstKey ++
    writeU32LE (UInt32.ofNat ref.offset) ++ writeU32LE (UInt32.ofNat ref.length)

def supported (index : Index) : Bool :=
  index.targetIBKSha256.size == 32 && index.entries.size < UInt32.size &&
    index.entries.toList.all fun entry =>
      entry.localId < index.entries.size && entry.key == serializeTerm entry.term &&
        entry.key.length < UInt32.size

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

private def parseEntry (xs : List UInt8) : Option (Entry × List UInt8) := do
  let keyLength ← readU32LE xs 0
  let (key, afterKey) ← takeExact keyLength.toNat (xs.drop 4)
  let localId ← readU32LE afterKey 0
  let (term, trailing) ← parseTerm key
  if !trailing.isEmpty || serializeTerm term != key then none else
    some ({ key, term, localId := localId.toNat }, afterKey.drop 4)

private def parseEntries : Nat → List UInt8 → List Entry → Option (List Entry × List UInt8)
  | 0, xs, reversed => some (reversed.reverse, xs)
  | count + 1, xs, reversed => do
      let (entry, rest) ← parseEntry xs
      parseEntries count rest (entry :: reversed)

private def parseRef (xs : List UInt8) : Option (PageRef × List UInt8) := do
  let firstLength ← readU32LE xs 0
  let (firstKey, afterKey) ← takeExact firstLength.toNat (xs.drop 4)
  let offset ← readU32LE afterKey 0
  let length ← readU32LE afterKey 4
  some ({ firstKey, offset := offset.toNat, length := length.toNat }, afterKey.drop 8)

private def parseRefs : Nat → List UInt8 → List PageRef → Option (List PageRef × List UInt8)
  | 0, xs, reversed => some (reversed.reverse, xs)
  | count + 1, xs, reversed => do
      let (ref, rest) ← parseRef xs
      parseRefs count rest (ref :: reversed)

private def pageEntryCount (termCount page : Nat) : Nat := min pageTerms (termCount - page * pageTerms)

private def decodePages : Nat → List PageRef → List UInt8 → Nat → List Entry → Option (List Entry)
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

private def refsContiguous : List PageRef → Nat → Bool
  | [], _ => true
  | ref :: rest, expected => ref.length > 0 && ref.offset == expected && refsContiguous rest (expected + ref.length)

private def refsStrictlyIncreasing : List PageRef → Bool
  | [] | [_] => true
  | left :: right :: rest => lessKey left.firstKey right.firstKey && refsStrictlyIncreasing (right :: rest)

/-- In a list with exactly `termCount` in-range, pairwise-distinct local IDs,
    every local ID is present exactly once.  The seen array replaces the old
    quadratic `eraseDups` pass in full TLI1 activation. -/
private def localIdsPermutationGo : List Entry → Array Bool → Bool
  | [], _ => true
  | entry :: rest, seen =>
      match seen[entry.localId]? with
      | some false => localIdsPermutationGo rest (seen.set! entry.localId true)
      | _ => false

private def localIdsPermutation (entries : List Entry) (termCount : Nat) : Bool :=
  entries.length == termCount && localIdsPermutationGo entries (Array.replicate termCount false)

private def canonicalEntries (entries : List Entry) (termCount : Nat) : Bool :=
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

def decode? (bytes : ByteArray) : Option Index := do
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
#guard localIdsPermutation sample.entries.toList sample.entries.size
#guard !localIdsPermutation duplicateLocalIds sample.entries.size
#guard (decodePrefix? (sampleBytes.extract 0 prefixBytes)).map Prefix.termCount == some sample.entries.size
#guard samplePageLookup == some (some 2)
#guard decode? twoPageBytes == some twoPage
#guard (decode? (corrupt sampleBytes)).isNone
#guard decode? ((encode? wrongTarget).getD ByteArray.empty) == some wrongTarget

end L4Factoidal.Storage.TermLocalIndexWire
