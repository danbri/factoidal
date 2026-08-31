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
  deriving DecidableEq, Repr

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

private def entryBefore (left right : Entry) : Bool := lessKey left.key right.key

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
  let sorted := entries.toArray.qsort entryBefore |>.toList
  if sorted != entries then none else
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

private def canonicalEntries (entries : List Entry) (termCount : Nat) : Bool :=
  entries.length == termCount && (entries.toArray.qsort entryBefore).toList == entries &&
  entries.all (fun entry => entry.localId < termCount) &&
  (entries.map Entry.localId).eraseDups.length == termCount

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
private def sampleBytes : ByteArray := (encode? sample).getD ByteArray.empty
private def twoPageTerms : Array Term :=
  (List.range (pageTerms + 1)).map (fun n => Term.bnode s!"term-{n}") |>.toArray
private def twoPage : Index := { targetIBKSha256 := ByteArray.mk (Array.replicate 32 9), entries := entriesOf twoPageTerms }
private def twoPageBytes : ByteArray := (encode? twoPage).getD ByteArray.empty

#guard decode? sampleBytes == some sample
#guard decode? twoPageBytes == some twoPage

end L4Factoidal.Storage.TermLocalIndexWire
