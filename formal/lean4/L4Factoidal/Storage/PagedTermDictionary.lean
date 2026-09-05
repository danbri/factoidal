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
import L4Factoidal.Storage.PagedTermDictionaryCore
import L4Factoidal.Storage.TermCodecTheorems

namespace L4Factoidal.Storage.PagedTermDictionary

open L4Factoidal.RDF
open L4Factoidal.Storage
open L4Factoidal.Storage.BlockWireV0

/-- `'PTD1'` in little-endian form. -/
def magic : UInt32 := 0x31445450
def version : UInt8 := 1

/-! The three record types, the page-planning functions and the whole page
layout are shared with PTD2 through
`L4Factoidal.Storage.PagedTermDictionaryCore`. PTD1's own definitions below
keep their bodies, so every existing caller and proof is unchanged; the
`PagedTermDictionaryTheorems` corollaries then show each of them is the
generic definition at the v1 codec, and the round-trip proof is the generic
one. -/

abbrev Prefix := PTD.Prefix
abbrev PageEntry := PTD.PageEntry
abbrev ByteRange := PTD.ByteRange

/-- The v1 term codec as a `PTD.TermCodec`: the total `DeltaLog` encoder,
its two-part admission test, and the round trip
`L4Factoidal.Storage.parseTerm_serializeTerm` proves on that subset. -/
def v1Codec : PTD.TermCodec Term where
  encode := serializeTerm
  admits := fun t => BlockWireV0.termSupported t && termFitsU32b t
  decode := parseTerm
  encode_ne_nil := fun t => by cases t <;> simp [serializeTerm]
  roundTrip := fun t rest h => by
    rw [Bool.and_eq_true] at h
    exact parseTerm_serializeTerm t rest h.1 ((termFitsU32b_iff t).mp h.2)

/-- PTD1: the shared paged layout at the v1 codec. -/
def v1Format : PTD.PagedFormat Term :=
  { magic := magic, version := version, codec := v1Codec }

/-! The page layout, the planning functions and the decoders below are the
generic ones of `PagedTermDictionaryCore` at `v1Format`. The four
definitions that keep their own bodies — `supported`, `encodePages`,
`encode?`, `decodeSpec?` and `decode?` — are the generic bodies written
out, and `PagedTermDictionaryTheorems` proves each equal to the generic
definition by `rfl`. -/

abbrev byteArrayOfList := PTD.byteArrayOfList
abbrev listOfByteArray := PTD.listOfByteArray
abbrev fitsU32 := PTD.fitsU32
abbrev readU32At? := PTD.readU32At?
abbrev defaultPageTerms := PTD.defaultPageTerms
abbrev prefixBytes := PTD.prefixBytes
private abbrev at? := @PTD.at? Term
abbrev pagesOf := @PTD.pagesOf Term
abbrev directoryFor := PTD.directoryFor
abbrev encodeDirectory := PTD.encodeDirectory
abbrev decodePrefix := PTD.decodePrefix v1Format
abbrev directoryRange := PTD.directoryRange
abbrev pageAreaOffset := PTD.pageAreaOffset
abbrev decodeDirectoryGo := PTD.decodeDirectoryGo
abbrev directoryContiguous := PTD.directoryContiguous
abbrev directoryCovers := PTD.directoryCovers
abbrev decodeDirectory? := PTD.decodeDirectory?
abbrev pageIndex? := PTD.pageIndex?
abbrev pageTermCount := PTD.pageTermCount
abbrev pageRange? := PTD.pageRange?
abbrev pageRangesForTerms? := PTD.pageRangesForTerms?
abbrev decodeTermsGo := PTD.decodeTermsGo v1Format
abbrev decodeTerms := PTD.decodeTerms v1Format
abbrev decodePagesGo := PTD.decodePagesGo v1Format
abbrev decodePages? := PTD.decodePages? v1Format
abbrev decodePage? := PTD.decodePage? v1Format
abbrev decodePageArray? := PTD.decodePageArray? v1Format
abbrev decodeTermFromPage? := PTD.decodeTermFromPage? v1Format
abbrev findTermId? := @PTD.findTermId? Term _

/-- PTD1 admission. `termSupported` is the direct-term subset the inherited
    term codec decodes; `termFitsU32b` is the u32 length-prefix test for the
    TOTAL encoder `serializeTerm` that `encodePages` calls, which would
    otherwise write a truncated length prefix for a string of `2 ^ 32` bytes
    or more. Gating on both makes the decoder's admitted set exactly the
    encoder's, so `PagedTermDictionaryTheorems.decode?_encode?` needs no
    term-level hypothesis. -/
def supported (terms : Array Term) : Bool :=
  terms.toList.all (fun term => termSupported term && termFitsU32b term) && fitsU32 terms.size

def encodePages (terms : List Term) : List (List UInt8) :=
  (pagesOf defaultPageTerms terms.length terms).map (fun page => page.flatMap serializeTerm)

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

    decode? bytes = decodeSpec? bytes

for every `bytes`, so the format and the admission decision are unchanged. -/

/-- Full validation/decoding for packer and conformance paths, stated over the
    byte list.  This is the SPECIFICATION; `decode?` is proved equal to it. -/
def decodeSpec? (bytes : ByteArray) : Option (Array Term) := do
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

/-- Full validation/decoding for packer and conformance paths, reading the
    artifact by byte-array index.  The bytes admitted, and the term array
    returned, are exactly `decodeSpec?`'s;
    `PagedTermDictionaryTheorems.decode?_eq_spec` is that proof. -/
def decode? (bytes : ByteArray) : Option (Array Term) := do
  let header ← decodePrefix (bytes.extract 0 prefixBytes)
  if bytes.size < prefixBytes + header.pageCount * 8 + 4 then none else
  let storedCrc ← readU32At? bytes (bytes.size - 4)
  if storedCrc != (crc32cAppendArray 0xFFFFFFFF (bytes.extract 5 (bytes.size - 4))
      ^^^ 0xFFFFFFFF) then none else
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
