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

def byteArrayOfList (xs : List UInt8) : ByteArray := ByteArray.mk xs.toArray
def listOfByteArray (bytes : ByteArray) : List UInt8 := bytes.data.toList
def fitsU32 (n : Nat) : Bool := n < 4294967296

def readU32At? (bytes : ByteArray) (offset : Nat) : Option UInt32 := do
  let b0 ← bytes[offset]?
  let b1 ← bytes[offset + 1]?
  let b2 ← bytes[offset + 2]?
  let b3 ← bytes[offset + 3]?
  some (b0.toUInt32 ||| (b1.toUInt32 <<< 8) |||
    (b2.toUInt32 <<< 16) ||| (b3.toUInt32 <<< 24))

private def at? : List α → Nat → Option α
  | [], _ => none
  | term :: _, 0 => some term
  | _ :: rest, index + 1 => at? rest index

def pagesOf (pageTerms : Nat) : Nat → List Term → List (List Term)
  | 0, _ => []
  | _ + 1, [] => []
  | fuel + 1, terms => terms.take pageTerms :: pagesOf pageTerms fuel (terms.drop pageTerms)

def encodePages (terms : List Term) : List (List UInt8) :=
  (pagesOf defaultPageTerms terms.length terms).map (fun page => page.flatMap serializeTerm)

def directoryFor (pages : List (List UInt8)) : List PageEntry :=
  let (_, reversed) := pages.foldl (fun (state : Nat × List PageEntry) page =>
    let (offset, entries) := state
    (offset + page.length, { offset := offset, length := page.length } :: entries)) (0, [])
  reversed.reverse

def encodeDirectory (entry : PageEntry) : List UInt8 :=
  writeU32LE (UInt32.ofNat entry.offset) ++ writeU32LE (UInt32.ofNat entry.length)

/-- PTD1 admission. `termSupported` is the direct-term subset the inherited
    term codec decodes; `termFitsU32b` is the u32 length-prefix test for the
    TOTAL encoder `serializeTerm` that `encodePages` calls, which would
    otherwise write a truncated length prefix for a string of `2 ^ 32` bytes
    or more. Gating on both makes the decoder's admitted set exactly the
    encoder's, so `PagedTermDictionaryTheorems.decode?_encode?` needs no
    term-level hypothesis. -/
def supported (terms : Array Term) : Bool :=
  terms.toList.all (fun term => termSupported term && termFitsU32b term) && fitsU32 terms.size

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
  if bytes.size != prefixBytes then none else do
  let foundMagic ← readU32At? bytes 0
  if foundMagic != magic then none else do
  let foundVersion ← bytes[4]?
  if foundVersion != version then none else do
  let termCount ← readU32At? bytes 5
  let pageTerms ← readU32At? bytes 9
  let pageCount ← readU32At? bytes 13
  if pageTerms.toNat == 0 then none
  else if pageCount.toNat != (termCount.toNat + pageTerms.toNat - 1) / pageTerms.toNat then none
  else some { termCount := termCount.toNat, pageTerms := pageTerms.toNat, pageCount := pageCount.toNat }

def directoryRange (header : Prefix) : ByteRange :=
  { offset := prefixBytes, length := header.pageCount * 8 }

def pageAreaOffset (header : Prefix) : Nat := prefixBytes + header.pageCount * 8

def decodeDirectoryGo : Nat → ByteArray → Nat → List PageEntry → Option (List PageEntry)
  | 0, _, _, reversed => some reversed.reverse
  | count + 1, bytes, offset, reversed => do
      let pageOffset ← readU32At? bytes offset
      let length ← readU32At? bytes (offset + 4)
      decodeDirectoryGo count bytes (offset + 8)
        ({ offset := pageOffset.toNat, length := length.toNat } :: reversed)

def directoryContiguous : List PageEntry → Nat → Bool
  | [], _ => true
  | entry :: rest, expected =>
      entry.length > 0 && entry.offset == expected && directoryContiguous rest (expected + entry.length)

def directoryCovers (directory : List PageEntry) (total : Nat) : Bool :=
  directory.foldl (fun expected entry => if entry.length > 0 && entry.offset == expected
    then expected + entry.length else total + 1) 0 == total

def decodeDirectory? (header : Prefix) (bytes : ByteArray) : Option (List PageEntry) := do
  if bytes.size != header.pageCount * 8 then none else do
  let directory ← decodeDirectoryGo header.pageCount bytes 0 []
  if !directoryContiguous directory 0 then none else some directory

def pageIndex? (header : Prefix) (termId : Nat) : Option Nat :=
  if termId >= header.termCount then none else some (termId / header.pageTerms)

def pageTermCount (header : Prefix) (page : Nat) : Nat :=
  min header.pageTerms (header.termCount - page * header.pageTerms)

def pageRange? (header : Prefix) (directory : List PageEntry) (termId : Nat) : Option ByteRange := do
  let page ← pageIndex? header termId
  let entry ← at? directory page
  some { offset := pageAreaOffset header + entry.offset, length := entry.length }

private def distinctPageIdsGo (header : Prefix) : List Nat → Array Bool → List Nat → Option (List Nat)
  | [], _, reversed => some reversed.reverse
  | termId :: rest, seen, reversed => do
      let page ← pageIndex? header termId
      match seen[page]? with
      | none => none
      | some true => distinctPageIdsGo header rest seen reversed
      | some false => distinctPageIdsGo header rest (seen.set! page true) (page :: reversed)

/-- Page identity is bounded by the dictionary header, so use an indexed
    seen-set rather than repeatedly scanning the growing output list. The
    reverse accumulator restores first-term occurrence order exactly. -/
private def distinctPageIds? (header : Prefix) (termIds : List Nat) : Option (List Nat) :=
  distinctPageIdsGo header termIds (Array.replicate header.pageCount false) []

/-- Plan the distinct term pages required by a collection of row IDs. Ordering
    follows first occurrence in `termIds`, which makes the host's read trace
    deterministic and avoids re-fetching a page when a row mentions an ID
    twice. -/
def pageRangesForTerms? (header : Prefix) (directory : List PageEntry)
    (termIds : List Nat) : Option (List ByteRange) := do
  let pageIds ← distinctPageIds? header termIds
  pageIds.mapM fun page => do
    let entry ← at? directory page
    some { offset := pageAreaOffset header + entry.offset, length := entry.length }

def decodeTermsGo : Nat → List UInt8 → List Term → Option (List Term × List UInt8)
  | 0, bytes, reversed => some (reversed.reverse, bytes)
  | count + 1, bytes, reversed => do
      let (term, afterTerm) ← parseTerm bytes
      decodeTermsGo count afterTerm (term :: reversed)

def decodeTerms (count : Nat) (bytes : List UInt8) : Option (List Term × List UInt8) :=
  decodeTermsGo count bytes []

/-- Full decoding uses the declared page boundaries too, not merely one
    concatenated term stream. That makes malformed page lengths fail at the
    canonical admission boundary before a range reader can rely on them. -/
def decodePagesGo (header : Prefix) : Nat → List PageEntry → ByteArray → Nat → List Term → Option (List Term)
  | _, [], bytes, offset, reversed => if offset == bytes.size then some reversed.reverse else none
  | page, entry :: rest, bytes, offset, reversed => do
      let current := bytes.extract offset (offset + entry.length)
      if current.size != entry.length then none else do
      let (terms, trailing) ← decodeTerms (pageTermCount header page) (listOfByteArray current)
      if !trailing.isEmpty then none else do
      let next := terms.foldl (fun acc term => term :: acc) reversed
      decodePagesGo header (page + 1) rest bytes (offset + entry.length) next

def decodePages? (header : Prefix) (page : Nat) (directory : List PageEntry)
    (bytes : ByteArray) : Option (List Term) :=
  decodePagesGo header page directory bytes 0 []

/- Decode one declared page. The caller supplies exactly the planned page
   range, normally after a Merkle inclusion check. Exposing the decoded page
   lets an execution host validate it once and reuse its terms for many rows. -/
def decodePage? (header : Prefix) (directory : List PageEntry) (page : Nat)
    (pageBytes : ByteArray) : Option (List Term) := do
  let entry ← at? directory page
  if pageBytes.size != entry.length then none else do
  let (terms, rest) ← decodeTerms (pageTermCount header page) (listOfByteArray pageBytes)
  if !rest.isEmpty then none else some terms

/-- Range execution resolves each page's local IDs many times. Decode once to
    an array so those local lookups are constant-time. The list decoder remains
    the canonical public semantic representation. -/
def decodePageArray? (header : Prefix) (directory : List PageEntry) (page : Nat)
    (pageBytes : ByteArray) : Option (Array Term) :=
  (decodePage? header directory page pageBytes).map List.toArray

/-- Decode the one page selected by `termId`. -/
def decodeTermFromPage? (header : Prefix) (directory : List PageEntry) (termId : Nat)
    (pageBytes : ByteArray) : Option Term := do
  let page ← pageIndex? header termId
  let terms ← decodePage? header directory page pageBytes
  at? terms (termId % header.pageTerms)

/-- Reference mapping from an RDF term to this dictionary's local ID. The
    comparison is complete RDF-term structural equality, not a hash shortcut.
    A later persistent term lookup index must return the same answer before it
    is allowed to drive Subject Row Index postings. -/
private def findTermIdGo (terms : Array Term) (wanted : Term) (index fuel : Nat) : Option Nat :=
  match fuel with
  | 0 => none
  | remaining + 1 =>
      match terms[index]? with
      | none => none
      | some term =>
          if term == wanted then some index
          else findTermIdGo terms wanted (index + 1) remaining

def findTermId? (terms : Array Term) (wanted : Term) : Option Nat :=
  findTermIdGo terms wanted 0 terms.size

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
  let pageBytes := bytes.extract (pageAreaOffset header) (bytes.size - 4)
  if !directoryCovers directory pageBytes.size then none else
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
#guard findTermId? sample (.iri ex2) == some 1
#guard (findTermId? sample (.bnode "missing")).isNone
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
