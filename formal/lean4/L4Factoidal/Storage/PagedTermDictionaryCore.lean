/-
L4Factoidal.Storage.PagedTermDictionaryCore — the paged term dictionary,
over any term codec.

`PagedTermDictionary` (PTD1) writes a block's terms as a fixed
seventeen-byte prefix, a directory of eight-byte page entries, and the
canonical term bytes of the pages, with a CRC32C over every post-version
byte. Wire version 10 needs the same page layout over a different term
codec (PTD2, term codec v2). Only the codec and the two identifying
bytes change, so the layout, the decoder and the round-trip proof are
written once here and instantiated twice.

`TermCodec` is what the layout needs of a codec: a total encoder, an
admission test, a decoder, the fact that an encoding is never empty (the
page framing needs it), and the round trip with trailing bytes present.
`PagedFormat` adds the magic number and the version byte.

The instantiations are `L4Factoidal.Storage.PagedTermDictionary`
(magic `PTD1`, version 1, the `DeltaLog` term codec over `RDF.Term`) and
`L4Factoidal.Storage.PagedTermDictionaryV2` (magic `PTD2`, version 2,
term codec v2 over `TermWireV2.WireTerm`).

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.Bytes

namespace L4Factoidal.Storage.PTD

open L4Factoidal.Storage

/-- What the paged layout needs of a term codec. `encode` is TOTAL: like
`DeltaLog.serializeTerm` it writes bytes for every value, and `admits` is
the test that says whether those bytes read back. -/
structure TermCodec (τ : Type) where
  encode : τ → List UInt8
  admits : τ → Bool
  decode : List UInt8 → Option (τ × List UInt8)
  encode_ne_nil : ∀ a, encode a ≠ []
  roundTrip : ∀ a rest, admits a = true →
    decode (encode a ++ rest) = some (a, rest)

/-- A codec plus the two bytes that identify the artifact it writes. -/
structure PagedFormat (τ : Type) where
  magic : UInt32
  version : UInt8
  codec : TermCodec τ

variable {τ : Type} (F : PagedFormat τ)

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

def at? : List α → Nat → Option α
  | [], _ => none
  | term :: _, 0 => some term
  | _ :: rest, index + 1 => at? rest index

def pagesOf (pageTerms : Nat) : Nat → List τ → List (List τ)
  | 0, _ => []
  | _ + 1, [] => []
  | fuel + 1, terms => terms.take pageTerms :: pagesOf pageTerms fuel (terms.drop pageTerms)

def encodePages (terms : List τ) : List (List UInt8) :=
  (pagesOf defaultPageTerms terms.length terms).map (fun page => page.flatMap F.codec.encode)

def directoryFor (pages : List (List UInt8)) : List PageEntry :=
  let (_, reversed) := pages.foldl (fun (state : Nat × List PageEntry) page =>
    let (offset, entries) := state
    (offset + page.length, { offset := offset, length := page.length } :: entries)) (0, [])
  reversed.reverse

def encodeDirectory (entry : PageEntry) : List UInt8 :=
  writeU32LE (UInt32.ofNat entry.offset) ++ writeU32LE (UInt32.ofNat entry.length)

/-- PTD1 admission. `termSupported` is the direct-term subset the inherited
    term codec decodes; `termFitsU32b` is the u32 length-prefix test for the
    TOTAL encoder `F.codec.encode` that `encodePages` calls, which would
    otherwise write a truncated length prefix for a string of `2 ^ 32` bytes
    or more. Gating on both makes the decoder's admitted set exactly the
    encoder's, so `PagedTermDictionaryTheorems.decode?_encode?` needs no
    term-level hypothesis. -/
def supported (terms : Array τ) : Bool :=
  terms.toList.all (fun term => F.codec.admits term) && fitsU32 terms.size

/-- Canonical full bytes.  The CRC covers every post-F.version byte through the
    final page; a range reader instead relies on the enclosing block's Merkle
    commitment while using the prefix/directory planning functions below. -/
def encode? (terms : Array τ) : Option ByteArray :=
  if !supported F terms then none else
  let pages := encodePages F terms.toList
  let directory := directoryFor pages
  let pageBytes := pages.flatten
  if !fitsU32 pages.length || !fitsU32 pageBytes.length ||
      !(directory.all fun entry => fitsU32 entry.offset && fitsU32 entry.length) then none
  else
    let payload := writeU32LE (UInt32.ofNat terms.size) ++
      writeU32LE (UInt32.ofNat defaultPageTerms) ++ writeU32LE (UInt32.ofNat pages.length) ++
      directory.flatMap encodeDirectory ++ pageBytes
    some <| byteArrayOfList (writeU32LE F.magic ++ [F.version] ++ payload ++ writeU32LE (crc32c payload))

def decodePrefix (bytes : ByteArray) : Option Prefix := do
  if bytes.size != prefixBytes then none else do
  let foundMagic ← readU32At? bytes 0
  if foundMagic != F.magic then none else do
  let foundVersion ← bytes[4]?
  if foundVersion != F.version then none else do
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

def distinctPageIdsGo (header : Prefix) : List Nat → Array Bool → List Nat → Option (List Nat)
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
def distinctPageIds? (header : Prefix) (termIds : List Nat) : Option (List Nat) :=
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

def decodeTermsGo : Nat → List UInt8 → List τ → Option (List τ × List UInt8)
  | 0, bytes, reversed => some (reversed.reverse, bytes)
  | count + 1, bytes, reversed => do
      let (term, afterTerm) ← F.codec.decode bytes
      decodeTermsGo count afterTerm (term :: reversed)

def decodeTerms (count : Nat) (bytes : List UInt8) : Option (List τ × List UInt8) :=
  decodeTermsGo F count bytes []

/-- Full decoding uses the declared page boundaries too, not merely one
    concatenated term stream. That makes malformed page lengths fail at the
    canonical admission boundary before a range reader can rely on them. -/
def decodePagesGo (header : Prefix) : Nat → List PageEntry → ByteArray → Nat → List τ → Option (List τ)
  | _, [], bytes, offset, reversed => if offset == bytes.size then some reversed.reverse else none
  | page, entry :: rest, bytes, offset, reversed => do
      let current := bytes.extract offset (offset + entry.length)
      if current.size != entry.length then none else do
      let (terms, trailing) ← decodeTerms F (pageTermCount header page) (listOfByteArray current)
      if !trailing.isEmpty then none else do
      let next := terms.foldl (fun acc term => term :: acc) reversed
      decodePagesGo header (page + 1) rest bytes (offset + entry.length) next

def decodePages? (header : Prefix) (page : Nat) (directory : List PageEntry)
    (bytes : ByteArray) : Option (List τ) :=
  decodePagesGo F header page directory bytes 0 []

/- Decode one declared page. The caller supplies exactly the planned page
   range, normally after a Merkle inclusion check. Exposing the decoded page
   lets an execution host validate it once and reuse its terms for many rows. -/
def decodePage? (header : Prefix) (directory : List PageEntry) (page : Nat)
    (pageBytes : ByteArray) : Option (List τ) := do
  let entry ← at? directory page
  if pageBytes.size != entry.length then none else do
  let (terms, rest) ← decodeTerms F (pageTermCount header page) (listOfByteArray pageBytes)
  if !rest.isEmpty then none else some terms

/-- Range execution resolves each page's local IDs many times. Decode once to
    an array so those local lookups are constant-time. The list decoder remains
    the canonical public semantic representation. -/
def decodePageArray? (header : Prefix) (directory : List PageEntry) (page : Nat)
    (pageBytes : ByteArray) : Option (Array τ) :=
  (decodePage? F header directory page pageBytes).map List.toArray

/-- Decode the one page selected by `termId`. -/
def decodeTermFromPage? (header : Prefix) (directory : List PageEntry) (termId : Nat)
    (pageBytes : ByteArray) : Option τ := do
  let page ← pageIndex? header termId
  let terms ← decodePage? F header directory page pageBytes
  at? terms (termId % header.pageTerms)

/-- Reference mapping from an RDF term to this dictionary's local ID. The
    comparison is complete RDF-term structural equality, not a hash shortcut.
    A later persistent term lookup index must return the same answer before it
    is allowed to drive Subject Row Index postings. -/
def findTermIdGo [BEq τ] (terms : Array τ) (wanted : τ) (index fuel : Nat) : Option Nat :=
  match fuel with
  | 0 => none
  | remaining + 1 =>
      match terms[index]? with
      | none => none
      | some term =>
          if term == wanted then some index
          else findTermIdGo terms wanted (index + 1) remaining

def findTermId? [BEq τ] (terms : Array τ) (wanted : τ) : Option Nat :=
  findTermIdGo terms wanted 0 terms.size

/-! ## The admission decoder

PTD1 carries every term of a block and is the largest region of an IBK3 or IBK4
artifact, so this decoder runs over almost the whole file at activation and
whenever a query opens a block. Reading it through `listOfByteArray` converts
that region to a `List UInt8`, one cons cell per byte; the payload is then
copied again by `List.drop`/`List.take`, `crc32c` folds over the copy, and the
stored-checksum read drops the list once more.

`decodeSpec?` keeps that list decoder as the SPECIFICATION of what PTD1 admits.
`decode?` reads the same fields by byte-array index and checksums the payload in
place with `Bytes.crc32cAppendArray`.
`PagedTermDictionaryTheorems.decode?_eq_spec` proves

    decode? F bytes = decodeSpec? F bytes

for every `bytes`, so the format and the admission decision are unchanged. -/

/-- Full validation/decoding for packer and conformance paths, stated over the
    byte list.  This is the SPECIFICATION; `decode?` is proved equal to it. -/
def decodeSpec? (bytes : ByteArray) : Option (Array τ) := do
  let input := listOfByteArray bytes
  let header ← decodePrefix F (bytes.extract 0 prefixBytes)
  if input.length < prefixBytes + header.pageCount * 8 + 4 then none else
  let payload := input.drop 5 |>.take (input.length - 9)
  let storedCrc ← readU32LE input (input.length - 4)
  if storedCrc != crc32c payload then none else
  let directoryBytes := bytes.extract prefixBytes (prefixBytes + header.pageCount * 8)
  let directory ← decodeDirectory? header directoryBytes
  let pageBytes := bytes.extract (pageAreaOffset header) (bytes.size - 4)
  if !directoryCovers directory pageBytes.size then none else
  let terms ← decodePages? F header 0 directory pageBytes
  if terms.length != header.termCount then none else some terms.toArray

/-- Full validation/decoding for packer and conformance paths, reading the
    artifact by byte-array index.  The bytes admitted, and the term array
    returned, are exactly `decodeSpec?`'s;
    `PagedTermDictionaryTheorems.decode?_eq_spec` is that proof. -/
def decode? (bytes : ByteArray) : Option (Array τ) := do
  let header ← decodePrefix F (bytes.extract 0 prefixBytes)
  if bytes.size < prefixBytes + header.pageCount * 8 + 4 then none else
  let storedCrc ← readU32At? bytes (bytes.size - 4)
  if storedCrc != (crc32cAppendArray 0xFFFFFFFF (bytes.extract 5 (bytes.size - 4))
      ^^^ 0xFFFFFFFF) then none else
  let directoryBytes := bytes.extract prefixBytes (prefixBytes + header.pageCount * 8)
  let directory ← decodeDirectory? header directoryBytes
  let pageBytes := bytes.extract (pageAreaOffset header) (bytes.size - 4)
  if !directoryCovers directory pageBytes.size then none else
  let terms ← decodePages? F header 0 directory pageBytes
  if terms.length != header.termCount then none else some terms.toArray


end L4Factoidal.Storage.PTD
