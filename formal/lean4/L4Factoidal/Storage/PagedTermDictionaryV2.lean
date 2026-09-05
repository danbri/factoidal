/-
L4Factoidal.Storage.PagedTermDictionaryV2 — PTD2, the paged term
dictionary at term codec v2.

Magic `PTD2`, version byte 2, and otherwise exactly the PTD1 page
layout: a seventeen-byte prefix, a directory of eight-byte page entries,
the canonical term bytes of the pages, and a CRC32C over every
post-version byte. Only the term codec and the two identifying bytes
differ from PTD1, so both are instantiations of
`L4Factoidal.Storage.PagedTermDictionaryCore` and share its round-trip
proof.

The dictionary holds `TermWireV2.WireTerm`, so a block may name an
out-of-line literal without holding its bytes.

## Admission

`PTD.TermCodec.encode` is total. The v2 encoder is not: it refuses a
term outside the admitted set of
`docs/designissues/2026-09-05-wire-version-10-scale.md` section 4. The
total encoder here writes the single byte `0xFF` for such a term, which
is an unassigned tag that `TermWireV2.parseTerm` refuses, and `admits`
is exactly `(serializeTerm? w).isSome`. This is the same arrangement as
PTD1, whose total encoder writes a truncated length prefix for a string
of `2 ^ 32` bytes or more and gates on `termFitsU32b`.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.PagedTermDictionaryCore
import L4Factoidal.Storage.TermWireV2Theorems

namespace L4Factoidal.Storage.PagedTermDictionaryV2

open L4Factoidal.RDF
open L4Factoidal.Storage.TermWireV2

/-- `'PTD2'` in little-endian form. -/
def magic : UInt32 := 0x32445450
def version : UInt8 := 2

/-- The tag byte the total encoder writes for a term the v2 encoder
refuses. `TermWireV2.parseTerm` assigns no meaning to it. -/
def refusedTag : UInt8 := 0xFF

/-- The total v2 encoder the paged layout calls. -/
def totalEncode (w : WireTerm) : List UInt8 := (TermWireV2.serializeTerm? w).getD [refusedTag]

def v2Codec : PTD.TermCodec WireTerm where
  encode := totalEncode
  admits := fun w => (TermWireV2.serializeTerm? w).isSome
  decode := TermWireV2.parseTerm
  encode_ne_nil := by
    intro w
    cases hs : TermWireV2.serializeTerm? w with
    | none => simp [totalEncode, hs]
    | some bs =>
        simp only [totalEncode, hs, Option.getD_some]
        exact TermWireV2.serializeTerm?_ne_nil w bs hs
  roundTrip := by
    intro w rest h
    cases hs : TermWireV2.serializeTerm? w with
    | none => rw [hs] at h; simp at h
    | some bs =>
        show TermWireV2.parseTerm (totalEncode w ++ rest) = some (w, rest)
        simp only [totalEncode, hs, Option.getD_some]
        exact TermWireV2.parseTerm_serializeTerm? w bs rest hs

/-- PTD2: the shared paged layout at term codec v2. -/
def v2Format : PTD.PagedFormat WireTerm :=
  { magic := magic, version := version, codec := v2Codec }

/-! The whole public surface is the generic one at `v2Format`. -/

abbrev Prefix := PTD.Prefix
abbrev PageEntry := PTD.PageEntry
abbrev ByteRange := PTD.ByteRange
abbrev defaultPageTerms := PTD.defaultPageTerms
abbrev prefixBytes := PTD.prefixBytes
abbrev byteArrayOfList := PTD.byteArrayOfList
abbrev listOfByteArray := PTD.listOfByteArray
abbrev fitsU32 := PTD.fitsU32
abbrev readU32At? := PTD.readU32At?
abbrev pagesOf := @PTD.pagesOf WireTerm
abbrev directoryFor := PTD.directoryFor
abbrev encodeDirectory := PTD.encodeDirectory
abbrev directoryRange := PTD.directoryRange
abbrev pageAreaOffset := PTD.pageAreaOffset
abbrev decodeDirectory? := PTD.decodeDirectory?
abbrev directoryContiguous := PTD.directoryContiguous
abbrev directoryCovers := PTD.directoryCovers
abbrev pageIndex? := PTD.pageIndex?
abbrev pageTermCount := PTD.pageTermCount
abbrev pageRange? := PTD.pageRange?
abbrev pageRangesForTerms? := PTD.pageRangesForTerms?
abbrev encodePages := PTD.encodePages v2Format
abbrev supported := PTD.supported v2Format
abbrev encode? := PTD.encode? v2Format
abbrev decodePrefix := PTD.decodePrefix v2Format
abbrev decodeTerms := PTD.decodeTerms v2Format
abbrev decodePages? := PTD.decodePages? v2Format
abbrev decodePage? := PTD.decodePage? v2Format
abbrev decodePageArray? := PTD.decodePageArray? v2Format
abbrev decodeTermFromPage? := PTD.decodeTermFromPage? v2Format
abbrev decodeSpec? := PTD.decodeSpec? v2Format
abbrev decode? := PTD.decode? v2Format
abbrev findTermId? := @PTD.findTermId? WireTerm _

private def ex : WfIri := ⟨"https://example.test/t", by decide⟩
private def ex2 : WfIri := ⟨"https://example.test/u", by decide⟩
private def dirLit : WfLiteral :=
  ⟨{ lexicalForm := "שלום", datatype := rdfDirLangString,
     langTag := some "he", direction := some .rtl }, by decide⟩
private def bigLexical : String := String.ofList (List.replicate 70000 'a')

private def sample : Array WireTerm :=
  #[.inline (.iri ex), .inline (.iri ex2), .inline (.literal dirLit),
    .inline (.tripleTerm (.iri ex) ex2 (.literal dirLit)),
    toWire specHash (.literal (Literal.string bigLexical))]
private def sampleBytes : ByteArray := (encode? sample).getD ByteArray.empty

private def twoPageSample : Array WireTerm :=
  ((List.range (defaultPageTerms + 1)).map
    (fun index => WireTerm.inline (.bnode s!"page-{index}"))).toArray
private def twoPageBytes : ByteArray := (encode? twoPageSample).getD ByteArray.empty

#guard decode? sampleBytes == some sample
#guard (decodePrefix (sampleBytes.extract 0 prefixBytes)).map (fun p => p.termCount) == some 5
#guard (sampleBytes.extract 0 4).toList == [0x50, 0x54, 0x44, 0x32]
#guard sampleBytes[4]! == 2
#guard findTermId? sample (.inline (.iri ex2)) == some 1
#guard decode? twoPageBytes == some twoPageSample
#guard (decodePrefix (twoPageBytes.extract 0 prefixBytes)).map (fun p => p.pageCount) == some 2

end L4Factoidal.Storage.PagedTermDictionaryV2
