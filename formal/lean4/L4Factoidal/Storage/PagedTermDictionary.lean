/-
L4Factoidal.Storage.PagedTermDictionary — a pageable canonical term dictionary.

IBK2 stores one contiguous variable-width term dictionary per block.  That is
simple and canonical, but a cold `LIMIT 5` must read it all before it can turn
the first ID rows back into RDF terms.  This module is the independently
tested inner representation for the next block layout: a fixed directory of
small term pages followed by contiguous canonical term bytes.

The directory is intentionally tiny (one eight-byte entry per 256 terms).
A range host can fetch the prefix + directory, then only the pages containing
the TermIds referenced by a row prefix.  It is a typed byte component, not a
new term identity scheme: its terms and their array indexes have exactly the
same meaning as `IndexedBlock.Block.dict`.
-/
import L4Factoidal.Storage.BlockWireV0

namespace L4Factoidal.Storage.PagedTermDictionary

open L4Factoidal.RDF
open L4Factoidal.Storage
open L4Factoidal.Storage.BlockWireV0

/-- `'PTD1'` in little-endian form. -/
def magic : UInt32 := 0x31445450
def version : UInt8 := 1
def defaultPageTerms : Nat := 256
def prefixBytes : Nat := 4 + 1 + 12

structure Prefix where
  termCount : Nat
  pageTerms : Nat
  pageCount : Nat
  deriving Repr, DecidableEq, Inhabited

structure PageEntry where
  offset : Nat
  length : Nat
  deriving Repr, DecidableEq, Inhabited

structure ByteRange where
  offset : Nat
  length : Nat
  deriving Repr, DecidableEq, Inhabited

private def byteArrayOfList (xs : List UInt8) : ByteArray := ByteArray.mk xs.toArray
private def listOfByteArray (bytes : ByteArray) : List UInt8 := bytes.data.toList
private def fitsU32 (n : Nat) : Bool := n < 4294967296

private def at? : List α → Nat → Option α
  | [], _ => none
  | term :: _, 0 => some term
  | _ :: rest, index + 1 => at? rest index

private def pagesOf (pageTerms : Nat) : Nat → List Term → List (List Term)
  | 0, _ => []
  | _ + 1, [] => []
  | fuel + 1, terms => terms.take pageTerms :: pagesOf pageTerms fuel (terms.drop pageTerms)

private def encodePages (terms : List Term) : List (List UInt8) :=
  (pagesOf defaultPageTerms terms.length terms).map (fun page => page.flatMap serializeTerm)

private def directoryFor (pages : List (List UInt8)) : List PageEntry :=
  let (_, reversed) := pages.foldl (fun (state : Nat × List PageEntry) page =>
    let (offset, entries) := state
    (offset + page.length, { offset := offset, length := page.length } :: entries)) (0, [])
  reversed.reverse

private def encodeDirectory (entry : PageEntry) : List UInt8 :=
  writeU32LE (UInt32.ofNat entry.offset) ++ writeU32LE (UInt32.ofNat entry.length)

def supported (terms : Array Term) : Bool :=
  terms.toList.all termSupported && fitsU32 terms.size

/-- Canonical full bytes.  The CRC covers every post-version byte through the
    final page; a range reader instead relies on the enclosing block's Merkle
    commitment while using the prefix/directory planning functions below. -/
def encode? (terms : Array Term) : Option ByteArray :=
  if !supported terms then none else
  let pages := encodePages terms.toList
  let directory := directoryFor pages
  let pageBytes := pages.flatten
  if !fitsU32 pages.length || !fitsU32 pageBytes.length ||
      !(directory.all fun entry => fitsU32 entry.offset && fitsU32 entry.length) then none
  else
    let payload := writeU32LE (UInt32.ofNat terms.size) ++
      writeU32LE (UInt32.ofNat defaultPageTerms) ++ writeU32LE (UInt32.ofNat pages.length) ++
      directory.flatMap encodeDirectory ++ pageBytes
    some <| byteArrayOfList (writeU32LE magic ++ [version] ++ payload ++ writeU32LE (crc32c payload))

def decodePrefix (bytes : ByteArray) : Option Prefix := do
  let input := listOfByteArray bytes
  let foundMagic ← readU32LE input 0
  if foundMagic != magic then none else do
  let (foundVersion, rest) ← parseU8 (input.drop 4)
  if foundVersion != version then none else do
  let termCount ← readU32LE rest 0
  let pageTerms ← readU32LE rest 4
  let pageCount ← readU32LE rest 8
  if pageTerms.toNat == 0 then none
  else if pageCount.toNat != (termCount.toNat + pageTerms.toNat - 1) / pageTerms.toNat then none
  else some { termCount := termCount.toNat, pageTerms := pageTerms.toNat, pageCount := pageCount.toNat }

def directoryRange (header : Prefix) : ByteRange :=
  { offset := prefixBytes, length := header.pageCount * 8 }

def pageAreaOffset (header : Prefix) : Nat := prefixBytes + header.pageCount * 8

private def decodeDirectory : Nat → List UInt8 → Option (List PageEntry × List UInt8)
  | 0, bytes => some ([], bytes)
  | count + 1, bytes => do
      let offset ← readU32LE bytes 0
      let length ← readU32LE bytes 4
      let (entries, rest) ← decodeDirectory count (bytes.drop 8)
      some ({ offset := offset.toNat, length := length.toNat } :: entries, rest)

private def directoryContiguous : List PageEntry → Nat → Bool
  | [], _ => true
  | entry :: rest, expected =>
      entry.length > 0 && entry.offset == expected && directoryContiguous rest (expected + entry.length)

private def directoryCovers (directory : List PageEntry) (total : Nat) : Bool :=
  directory.foldl (fun expected entry => if entry.length > 0 && entry.offset == expected
    then expected + entry.length else total + 1) 0 == total

def decodeDirectory? (header : Prefix) (bytes : ByteArray) : Option (List PageEntry) := do
  if bytes.size != header.pageCount * 8 then none else do
  let (directory, rest) ← decodeDirectory header.pageCount (listOfByteArray bytes)
  if !rest.isEmpty || !directoryContiguous directory 0 then none else some directory

def pageIndex? (header : Prefix) (termId : Nat) : Option Nat :=
  if termId >= header.termCount then none else some (termId / header.pageTerms)

def pageTermCount (header : Prefix) (page : Nat) : Nat :=
  min header.pageTerms (header.termCount - page * header.pageTerms)

def pageRange? (header : Prefix) (directory : List PageEntry) (termId : Nat) : Option ByteRange := do
  let page ← pageIndex? header termId
  let entry ← at? directory page
  some { offset := pageAreaOffset header + entry.offset, length := entry.length }

private def appendUnique (seen : List Nat) (value : Nat) : List Nat :=
  if seen.contains value then seen else seen ++ [value]

/-- Plan the distinct term pages required by a collection of row IDs. Ordering
    follows first occurrence in `termIds`, which makes the host's read trace
    deterministic and avoids re-fetching a page when a row mentions an ID
    twice. -/
def pageRangesForTerms? (header : Prefix) (directory : List PageEntry)
    (termIds : List Nat) : Option (List ByteRange) := do
  let pageIds ← termIds.foldl (fun pages termId =>
    pages.bind fun current => pageIndex? header termId |>.map (appendUnique current)) (some [])
  pageIds.mapM fun page => do
    let entry ← at? directory page
    some { offset := pageAreaOffset header + entry.offset, length := entry.length }

private def decodeTerms : Nat → List UInt8 → Option (List Term × List UInt8)
  | 0, bytes => some ([], bytes)
  | count + 1, bytes => do
      let (term, afterTerm) ← parseTerm bytes
      let (terms, rest) ← decodeTerms count afterTerm
      some (term :: terms, rest)

/-- Full decoding uses the declared page boundaries too, not merely one
    concatenated term stream. That makes malformed page lengths fail at the
    canonical admission boundary before a range reader can rely on them. -/
private def decodePages? (header : Prefix) : Nat → List PageEntry → List UInt8 → Option (List Term)
  | _, [], [] => some []
  | _, [], _ => none
  | page, entry :: rest, bytes => do
      let current := bytes.take entry.length
      let (terms, trailing) ← decodeTerms (pageTermCount header page) current
      if !trailing.isEmpty then none else do
      let later ← decodePages? header (page + 1) rest (bytes.drop entry.length)
      some (terms ++ later)

/- Decode one declared page. The caller supplies exactly the planned page
   range, normally after a Merkle inclusion check. Exposing the decoded page
   lets an execution host validate it once and reuse its terms for many rows. -/
def decodePage? (header : Prefix) (directory : List PageEntry) (page : Nat)
    (pageBytes : ByteArray) : Option (List Term) := do
  let entry ← at? directory page
  if pageBytes.size != entry.length then none else do
  let (terms, rest) ← decodeTerms (pageTermCount header page) (listOfByteArray pageBytes)
  if !rest.isEmpty then none else some terms

/-- Decode the one page selected by `termId`. -/
def decodeTermFromPage? (header : Prefix) (directory : List PageEntry) (termId : Nat)
    (pageBytes : ByteArray) : Option Term := do
  let page ← pageIndex? header termId
  let terms ← decodePage? header directory page pageBytes
  at? terms (termId % header.pageTerms)

/-- Full validation/decoding for packer and conformance paths. -/
def decode? (bytes : ByteArray) : Option (Array Term) := do
  let input := listOfByteArray bytes
  let header ← decodePrefix (bytes.extract 0 prefixBytes)
  if input.length < prefixBytes + header.pageCount * 8 + 4 then none else
  let payload := input.drop 5 |>.take (input.length - 9)
  let storedCrc ← readU32LE input (input.length - 4)
  if storedCrc != crc32c payload then none else
  let directoryBytes := bytes.extract prefixBytes (prefixBytes + header.pageCount * 8)
  let directory ← decodeDirectory? header directoryBytes
  let pageBytes := input.drop (pageAreaOffset header) |>.take (input.length - pageAreaOffset header - 4)
  if !directoryCovers directory pageBytes.length then none else
  let terms ← decodePages? header 0 directory pageBytes
  if terms.length != header.termCount then none else some terms.toArray

private def ex : WfIri := ⟨"https://example.test/t", by decide⟩
private def ex2 : WfIri := ⟨"https://example.test/u", by decide⟩
private def sample : Array Term := #[.iri ex, .iri ex2]
private def sampleBytes : ByteArray := (encode? sample).getD ByteArray.empty
private def twoPageSample : Array Term :=
  ((List.range (defaultPageTerms + 1)).map (fun index => Term.bnode s!"page-{index}")).toArray
private def twoPageBytes : ByteArray := (encode? twoPageSample).getD ByteArray.empty

#guard decode? sampleBytes == some sample
#guard (decodePrefix (sampleBytes.extract 0 prefixBytes)).map (fun p => p.termCount) == some 2
#guard (decodePrefix (sampleBytes.extract 0 prefixBytes)).bind (fun p =>
  decodeDirectory? p (sampleBytes.extract prefixBytes (prefixBytes + p.pageCount * 8)) |>.bind fun d =>
    pageRange? p d 1 |>.bind fun r => decodeTermFromPage? p d 1 (sampleBytes.extract r.offset (r.offset + r.length)))
  == at? sample.toList 1
#guard decode? twoPageBytes == some twoPageSample
#guard ((decodePrefix (twoPageBytes.extract 0 prefixBytes)).bind (fun p =>
  decodeDirectory? p (twoPageBytes.extract prefixBytes (prefixBytes + p.pageCount * 8)) |>.bind fun d =>
    pageRange? p d 0 |>.bind fun r => decodePage? p d 0 (twoPageBytes.extract r.offset (r.offset + r.length)))
  |>.map List.length) == some defaultPageTerms
#guard (decodePrefix (twoPageBytes.extract 0 prefixBytes)).map (fun p => p.pageCount) == some 2
#guard (decodePrefix (twoPageBytes.extract 0 prefixBytes)).bind (fun p =>
  decodeDirectory? p (twoPageBytes.extract prefixBytes (prefixBytes + p.pageCount * 8)) |>.bind fun d =>
    pageRange? p d defaultPageTerms |>.bind fun r =>
      decodeTermFromPage? p d defaultPageTerms (twoPageBytes.extract r.offset (r.offset + r.length)))
  == at? twoPageSample.toList defaultPageTerms
#guard (((decodePrefix (twoPageBytes.extract 0 prefixBytes)).bind (fun p =>
  decodeDirectory? p (twoPageBytes.extract prefixBytes (prefixBytes + p.pageCount * 8)) |>.bind fun d =>
    pageRangesForTerms? p d [0, defaultPageTerms, 1, defaultPageTerms]) |>.map List.length) == some 2)

end L4Factoidal.Storage.PagedTermDictionary
