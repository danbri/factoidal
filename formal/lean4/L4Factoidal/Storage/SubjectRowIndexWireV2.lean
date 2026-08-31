/-
L4Factoidal.Storage.SubjectRowIndexWireV2 — SRI2 pageable subject postings.

SRI2 is the page-selective successor to the flat SRI1 object.  It retains the
same canonical `(subject local ID, source row offset)` relation but binds it to
one IBK3 SHA-256 and supplies a compact first-subject directory.
-/
import L4Factoidal.Storage.SubjectRowIndexWire

namespace L4Factoidal.Storage.SubjectRowIndexWireV2

open L4Factoidal.Storage
open L4Factoidal.Storage.IndexedBlock
open L4Factoidal.Storage.SubjectRowIndexWire

def magic : UInt32 := 0x32495253 /-- `SRI2` little-endian. -/
def version : UInt8 := 2
def pagePairs : Nat := 256
def prefixBytes : Nat := 4 + 1 + 32 + 4 + 4 + 4 + 4 + 4 + 4
def pairBytes : Nat := 8
def directoryEntryBytes : Nat := 16
def crcBytes : Nat := 4

structure Prefix where
  targetIBKSha256 : ByteArray
  rowCount : Nat
  pairCount : Nat
  pageCount : Nat
  directoryBytes : Nat
  pagesBytes : Nat
  deriving DecidableEq

structure PageRef where
  firstSubject : Nat
  maxSubject : Nat
  offset : Nat
  length : Nat
  deriving DecidableEq, Repr

structure Index where
  targetIBKSha256 : ByteArray
  rowCount : Nat
  pairs : Array (Nat × Nat)
  deriving DecidableEq

private def bytesOf (xs : List UInt8) : ByteArray := ByteArray.mk xs.toArray
private def listOf (xs : ByteArray) : List UInt8 := xs.data.toList
private def readU32At? (bytes : ByteArray) (offset : Nat) : Option UInt32 := do
  let b0 ← bytes[offset]?
  let b1 ← bytes[offset + 1]?
  let b2 ← bytes[offset + 2]?
  let b3 ← bytes[offset + 3]?
  some (b0.toUInt32 ||| (b1.toUInt32 <<< 8) |||
    (b2.toUInt32 <<< 16) ||| (b3.toUInt32 <<< 24))

private def copyRange? (bytes : ByteArray) (offset length : Nat) : Option ByteArray :=
  if offset + length <= bytes.size then some (bytes.extract offset (offset + length)) else none

private def takeExact (n : Nat) (xs : List UInt8) : Option (List UInt8 × List UInt8) :=
  let taken := xs.take n
  if taken.length == n then some (taken, xs.drop n) else none

private def before (left right : Nat × Nat) : Bool :=
  left.1 < right.1 || (left.1 == right.1 && left.2 < right.2)

private def strictlyBefore (left right : Nat × Nat) : Bool := before left right

private def strictlyOrdered : List (Nat × Nat) → Bool
  | [] => true
  | [_] => true
  | left :: right :: rest => strictlyBefore left right && strictlyOrdered (right :: rest)

private def chunks : Nat → List α → List (List α)
  | 0, _ => []
  | _ + 1, [] => []
  | fuel + 1, xs => xs.take pagePairs :: chunks fuel (xs.drop pagePairs)

private def encodePair (pair : Nat × Nat) : List UInt8 :=
  writeU32LE (UInt32.ofNat pair.1) ++ writeU32LE (UInt32.ofNat pair.2)

private def pageBytes (pairs : List (Nat × Nat)) : List (List UInt8) :=
  (chunks pairs.length pairs).map fun page => page.flatMap encodePair

private def pageRefs (pages : List (List UInt8)) (pairPages : List (List (Nat × Nat))) : List PageRef :=
  let (_, reversed) := pages.zip pairPages |>.foldl (fun (state : Nat × List PageRef) pair =>
    let (offset, refs) := state
    let (bytes, pairs) := pair
    match pairs with
    | (firstSubject, _) :: _ =>
        let maxSubject := pairs.getLastD (firstSubject, 0) |>.1
        (offset + bytes.length,
          PageRef.mk firstSubject maxSubject offset bytes.length :: refs)
    | [] => (offset, refs)) (0, [])
  reversed.reverse

private def encodeRef (ref : PageRef) : List UInt8 :=
  writeU32LE (UInt32.ofNat ref.firstSubject) ++ writeU32LE (UInt32.ofNat ref.maxSubject) ++
    writeU32LE (UInt32.ofNat ref.offset) ++ writeU32LE (UInt32.ofNat ref.length)

def supported (index : Index) : Bool :=
  index.targetIBKSha256.size == 32 && index.rowCount > 0 && index.pairs.size == index.rowCount &&
    index.pairs.toList.all fun pair => pair.1 < UInt32.size && pair.2 < index.rowCount

def encode? (index : Index) : Option ByteArray := do
  if !supported index then none else
  let pairs := index.pairs.toList
  if !(strictlyOrdered pairs) then none else
  let pairPages := chunks pairs.length pairs
  let pages := pageBytes pairs
  let refs := pageRefs pages pairPages
  let directory := refs.flatMap encodeRef
  let pageArea := pages.flatten
  if refs.length >= UInt32.size || directory.length >= UInt32.size || pageArea.length >= UInt32.size then none else
  let payload := index.targetIBKSha256.toList ++ writeU32LE (UInt32.ofNat index.rowCount) ++
    writeU32LE (UInt32.ofNat pairs.length) ++ writeU32LE (UInt32.ofNat pagePairs) ++
    writeU32LE (UInt32.ofNat refs.length) ++ writeU32LE (UInt32.ofNat directory.length) ++
    writeU32LE (UInt32.ofNat pageArea.length) ++ directory ++ pageArea
  some <| bytesOf (writeU32LE magic ++ [version] ++ payload ++ writeU32LE (crc32c payload))

def decodePrefix? (bytes : ByteArray) : Option Prefix := do
  if bytes.size != prefixBytes then none else do
  let foundMagic ← readU32At? bytes 0
  if foundMagic != magic then none else do
  let foundVersion ← bytes[4]?
  if foundVersion != version then none else do
  let target ← copyRange? bytes 5 32
  let rowCount ← readU32At? bytes 37
  let pairCount ← readU32At? bytes 41
  let foundPairs ← readU32At? bytes 45
  let pageCount ← readU32At? bytes 49
  let directoryBytes ← readU32At? bytes 53
  let pagesBytes ← readU32At? bytes 57
  if rowCount.toNat == 0 || pairCount.toNat != rowCount.toNat || foundPairs.toNat != pagePairs ||
      pageCount.toNat != (pairCount.toNat + pagePairs - 1) / pagePairs ||
      directoryBytes.toNat != pageCount.toNat * directoryEntryBytes then none else
    some { targetIBKSha256 := target, rowCount := rowCount.toNat, pairCount := pairCount.toNat,
           pageCount := pageCount.toNat, directoryBytes := directoryBytes.toNat, pagesBytes := pagesBytes.toNat }

private def parseRef (xs : List UInt8) : Option (PageRef × List UInt8) := do
  let subject ← readU32LE xs 0
  let maxSubject ← readU32LE xs 4
  let offset ← readU32LE xs 8
  let length ← readU32LE xs 12
  let ref : PageRef := PageRef.mk subject.toNat maxSubject.toNat offset.toNat length.toNat
  some (ref, xs.drop directoryEntryBytes)

private def parseRefs : Nat → List UInt8 → List PageRef → Option (List PageRef × List UInt8)
  | 0, xs, reversed => some (reversed.reverse, xs)
  | count + 1, xs, reversed => do
      let (ref, rest) ← parseRef xs
      parseRefs count rest (ref :: reversed)

private def decodeRefsGo : Nat → ByteArray → Nat → List PageRef → Option (List PageRef)
  | 0, _, _, reversed => some reversed.reverse
  | count + 1, bytes, offset, reversed => do
      let firstSubject ← readU32At? bytes offset
      let maxSubject ← readU32At? bytes (offset + 4)
      let pageOffset ← readU32At? bytes (offset + 8)
      let length ← readU32At? bytes (offset + 12)
      decodeRefsGo count bytes (offset + directoryEntryBytes)
        (PageRef.mk firstSubject.toNat maxSubject.toNat pageOffset.toNat length.toNat :: reversed)

private def pairsInPage (header : Prefix) (page : Nat) : Nat :=
  min pagePairs (header.pairCount - page * pagePairs)

private def refsWellFormed : Prefix → List PageRef → Nat → Nat → Bool
  | _, [], _, _ => true
  | header, ref :: rest, ordinal, expected =>
      ref.firstSubject <= ref.maxSubject && ref.offset == expected &&
        ref.length == pairsInPage header ordinal * pairBytes &&
        refsWellFormed header rest (ordinal + 1) (expected + ref.length)

/-- A canonical SRI2 page sequence is ordered by both ends of its inclusive
    subject range. Activation later establishes this directory against all
    decoded pairs; retaining the inexpensive local condition here lets a range
    reader use logarithmic directory search without assuming arbitrary
    untrusted metadata is sorted. -/
private def refsMonotone : List PageRef → Bool
  | [] => true
  | [_] => true
  | left :: right :: rest =>
      left.firstSubject <= right.firstSubject && left.maxSubject <= right.maxSubject &&
        refsMonotone (right :: rest)

def decodeDirectory? (header : Prefix) (bytes : ByteArray) : Option (List PageRef) := do
  if bytes.size != header.directoryBytes then none else do
  let refs ← decodeRefsGo header.pageCount bytes 0 []
  if !refsWellFormed header refs 0 0 || !refsMonotone refs ||
      refs.foldl (fun total ref => total + ref.length) 0 != header.pagesBytes then none else some refs

private def parsePairs : Nat → List UInt8 → List (Nat × Nat) → Option (List (Nat × Nat) × List UInt8)
  | 0, xs, reversed => some (reversed.reverse, xs)
  | count + 1, xs, reversed => do
      let subject ← readU32LE xs 0
      let offset ← readU32LE xs 4
      parsePairs count (xs.drop pairBytes) ((subject.toNat, offset.toNat) :: reversed)

private def decodePairsGo : Nat → ByteArray → Nat → List (Nat × Nat) → Option (List (Nat × Nat))
  | 0, _, _, reversed => some reversed.reverse
  | count + 1, bytes, offset, reversed => do
      let subject ← readU32At? bytes offset
      let rowOffset ← readU32At? bytes (offset + 4)
      decodePairsGo count bytes (offset + pairBytes)
        ((subject.toNat, rowOffset.toNat) :: reversed)

def decodePage? (header : Prefix) (page : Nat) (ref : PageRef) (bytes : ByteArray) : Option (Array (Nat × Nat)) := do
  if page >= header.pageCount || bytes.size != ref.length then none else do
  let pairs ← decodePairsGo (pairsInPage header page) bytes 0 []
  match pairs with
  | [] => none
  | first :: _ =>
      let maxSubject := pairs.getLastD first |>.1
      if first.1 != ref.firstSubject || maxSubject != ref.maxSubject ||
          !(strictlyOrdered pairs) || pairs.any (fun pair => pair.2 >= header.rowCount) then none
      else some pairs.toArray

/-- First page with `maxSubject >= subject`, over an admitted monotone
    directory. Its fuel is the shrinking search interval, so malformed caller
    arrays cannot make this partial. -/
private def lowerBoundMaxGo (refs : Array PageRef) (subject low high : Nat) : Nat → Nat
  | 0 => low
  | fuel + 1 =>
      if low >= high then low else
        let middle := low + (high - low) / 2
        match refs[middle]? with
        | some ref =>
            if ref.maxSubject < subject then lowerBoundMaxGo refs subject (middle + 1) high fuel
            else lowerBoundMaxGo refs subject low middle fuel
        | none => low

/-- First page with `firstSubject > subject`, over an admitted monotone
    directory. -/
private def upperBoundFirstGo (refs : Array PageRef) (subject low high : Nat) : Nat → Nat
  | 0 => low
  | fuel + 1 =>
      if low >= high then low else
        let middle := low + (high - low) / 2
        match refs[middle]? with
        | some ref =>
            if ref.firstSubject <= subject then upperBoundFirstGo refs subject (middle + 1) high fuel
            else upperBoundFirstGo refs subject low middle fuel
        | none => low

private def collectCandidateRefs (refs : Array PageRef) (subject index stop : Nat) : Nat → List (Nat × PageRef) → List (Nat × PageRef)
  | 0, reversed => reversed.reverse
  | fuel + 1, reversed =>
      if index >= stop then reversed.reverse else
        match refs[index]? with
        | some ref =>
            let next := if ref.firstSubject <= subject && subject <= ref.maxSubject
              then (index, ref) :: reversed else reversed
            collectCandidateRefs refs subject (index + 1) stop fuel next
        | none => reversed.reverse

/-- All pages whose inclusive subject range can contain `subject`. A posting
    list may straddle more than two pages, so this returns every candidate.
    It binary-searches the monotone directory and scans only the candidate
    interval; ordinary subjects select one page. -/
def pagesFor (refs : List PageRef) (subject : Nat) : List (Nat × PageRef) :=
  let directory := refs.toArray
  let low := lowerBoundMaxGo directory subject 0 directory.size (directory.size + 1)
  let high := upperBoundFirstGo directory subject 0 directory.size (directory.size + 1)
  collectCandidateRefs directory subject low high (high - low + 1) []

def offsetsInPage (pairs : Array (Nat × Nat)) (subject : Nat) : List Nat :=
  pairs.toList.filterMap fun pair => if pair.1 == subject then some pair.2 else none

private def decodeAllPages : Prefix → List PageRef → List UInt8 → Nat → List (Nat × Nat) → Option (List (Nat × Nat))
  | _, [], [], _, reversed => some reversed.reverse
  | _, [], _, _, _ => none
  | header, ref :: refs, xs, page, reversed => do
      let current := xs.take ref.length
      let decoded ← decodePage? header page ref (bytesOf current)
      decodeAllPages header refs (xs.drop ref.length) (page + 1) (decoded.toList.reverse ++ reversed)

private def offsetsPermutation (pairs : List (Nat × Nat)) (rows : Nat) : Bool :=
  (pairs.map Prod.snd).eraseDups.length == rows && pairs.all (fun pair => pair.2 < rows)

def decode? (bytes : ByteArray) : Option Index := do
  if bytes.size < prefixBytes + crcBytes then none else do
  let header ← decodePrefix? (bytes.extract 0 prefixBytes)
  if bytes.size != prefixBytes + header.directoryBytes + header.pagesBytes + crcBytes then none else do
  let payload := listOf (bytes.extract 5 (bytes.size - crcBytes))
  let stored ← readU32LE (listOf bytes) (bytes.size - crcBytes)
  if stored != crc32c payload then none else do
  let directoryBytes := bytes.extract prefixBytes (prefixBytes + header.directoryBytes)
  let refs ← decodeDirectory? header directoryBytes
  let pages := (bytes.extract (prefixBytes + header.directoryBytes)
    (prefixBytes + header.directoryBytes + header.pagesBytes)).toList
  let pairs ← decodeAllPages header refs pages 0 []
  if pairs.length != header.rowCount || !(strictlyOrdered pairs) ||
      !offsetsPermutation pairs header.rowCount then none else
    some { targetIBKSha256 := header.targetIBKSha256, rowCount := header.rowCount, pairs := pairs.toArray }

private def exRows : Array IdTriple := #[{ s := 2, p := 0, o := 1 }, { s := 1, p := 0, o := 2 }, { s := 2, p := 0, o := 3 }]
private def sample : Index := { targetIBKSha256 := ByteArray.mk (Array.replicate 32 7), rowCount := exRows.size, pairs := pairsOfRows exRows |>.toArray }
private def sampleBytes := (encode? sample).getD ByteArray.empty

private def multiPageSample : Index :=
  { targetIBKSha256 := ByteArray.mk (Array.replicate 32 9), rowCount := 257,
    pairs := (List.range 257).map (fun offset => (7, offset)) |>.toArray }
private def multiPageBytes := (encode? multiPageSample).getD ByteArray.empty
private def multiPageHeader := decodePrefix? (multiPageBytes.extract 0 prefixBytes)
private def multiPageRefs := multiPageHeader.bind fun header =>
  decodeDirectory? header (multiPageBytes.extract prefixBytes (prefixBytes + header.directoryBytes))

private def threePageSample : Index :=
  { targetIBKSha256 := ByteArray.mk (Array.replicate 32 11), rowCount := 513,
    pairs := (List.range 513).map (fun subject => (subject, subject)) |>.toArray }
private def threePageBytes := (encode? threePageSample).getD ByteArray.empty
private def threePageRefs := (decodePrefix? (threePageBytes.extract 0 prefixBytes)).bind fun header =>
  decodeDirectory? header (threePageBytes.extract prefixBytes (prefixBytes + header.directoryBytes))

#guard decode? sampleBytes == some sample
#guard (decodePrefix? (sampleBytes.extract 0 prefixBytes)).map Prefix.rowCount == some 3
#guard decode? multiPageBytes == some multiPageSample
#guard multiPageRefs.map (fun refs => (pagesFor refs 7).length) == some 2
#guard threePageRefs.map (fun refs => (pagesFor refs 512).map Prod.fst) == some [2]
#guard threePageRefs.map (fun refs => (pagesFor refs 700).length) == some 0

end L4Factoidal.Storage.SubjectRowIndexWireV2
