/-
L4Factoidal.Storage.TermWireV2 — term codec v2, the wire-version-10 term
encoding.

The v1 codec (`L4Factoidal.Storage.DeltaLog.serializeTerm?`) refuses an
RDF 1.2 triple term and refuses a literal that carries a base direction,
and it has no representation for a literal too large to sit inside a
block. This module is the replacement decided in
`docs/designissues/2026-09-05-wire-version-10-scale.md` section 4.

Every integer is little-endian. `lstring` is the v1 length-prefixed
UTF-8 string of `DeltaLog`: a u32 byte length, then the bytes.

| Tag | Term | Body |
|---|---|---|
| 0 | IRI | `lstring` |
| 1 | blank node | `lstring` label |
| 2 | literal, inline | `lstring` lexical form; `lstring` datatype IRI; u8 flag; if flag >= 1, `lstring` language tag |
| 3 | triple term | subject: u8 (0 IRI, 1 blank node) + `lstring`; predicate `lstring`; object: one v2 term, recursively |
| 4 | literal, out-of-line | `lstring` datatype IRI; u8 flag; if flag >= 1, `lstring` language tag; u64 byte length of the UTF-8 lexical form; 32 bytes SHA-256 of that lexical form |

The flag is 0 for no language tag, 1 for a language tag with no
direction (`rdf:langString`), 2 for a language tag with direction `ltr`
and 3 for a language tag with direction `rtl` (both
`rdf:dirLangString`). The decoder rebuilds the literal through
`RDF.literalWf`, so a flag that disagrees with the datatype IRI is
refused, as in v1.

## Admission

Encoder admission equals decoder admission.

1. Every length-prefixed string has a UTF-8 byte length below `2 ^ 32`
   (`DeltaLog.serializeLString?` refuses the rest).
2. An inline literal (tag 2) has a lexical form of at most
   `maxInlineLexicalBytes` = 65,536 UTF-8 bytes.
3. An out-of-line literal (tag 4) has `byteLength` above
   `maxInlineLexicalBytes` and at most `maxBlobBytes` = 2 ^ 32 - 1, and
   a 32-byte SHA-256 digest.
4. The language tag and the direction agree with the datatype IRI under
   `RDF.literalWf`. For an inline literal that holds by construction of
   `RDF.WfLiteral`; for an out-of-line literal it is the decoder's own
   check `blobWf`, because a `BlobLiteral` is a plain structure.

Rules 2 and 3 together are the canonical choice of section 4.1: a
literal at or below the inline ceiling MUST be written with tag 2, a
longer one MUST be written with tag 4, and the decoder refuses the other
choice. One term has one encoding, which is what dictionary
de-duplication and byte-order key comparison depend on.

## Nesting

`WireTerm` is `inline (t : Term)` or `blob (b : BlobLiteral)`, so the
object of a triple term is an `RDF.Term` and cannot itself be
out-of-line. A triple term whose object literal is above the inline
ceiling therefore has no v2 encoding and the encoder refuses it. Tag 3's
recursive object is parsed by `parseInline`, which refuses tag 4.

## Resolution

`resolve` turns a `WireTerm` back into an `RDF.Term` given a way to
fetch blob bytes. It refuses missing bytes, a byte count that disagrees
with `byteLength`, bytes that hash to a different digest, and bytes that
are not valid UTF-8.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.DeltaLog
import L4Factoidal.Crypto.SHA2

namespace L4Factoidal.Storage.TermWireV2

open L4Factoidal.RDF
open L4Factoidal.Storage

/-! ## Constants -/

/-- The inline ceiling of section 2: a literal whose UTF-8 lexical form
is at most this many bytes is written inline (tag 2), a longer one
out-of-line (tag 4). -/
def maxInlineLexicalBytes : Nat := 65536

/-- The out-of-line ceiling of section 2: `2 ^ 32 - 1` bytes. Above it
the packer refuses the literal. -/
def maxBlobBytes : Nat := 4294967295

def tagIri : UInt8 := 0
def tagBnode : UInt8 := 1
def tagLiteralInline : UInt8 := 2
def tagTripleTerm : UInt8 := 3
def tagLiteralBlob : UInt8 := 4

/-! ## The decoded type -/

/-- An out-of-line literal: everything about the literal except its
lexical form, plus the byte extent and SHA-256 digest that name the
artifact holding that lexical form. -/
structure BlobLiteral where
  datatype   : WfIri
  langTag    : Option String
  direction  : Option TextDirection
  byteLength : Nat
  sha256     : ByteArray
  deriving DecidableEq

instance : Repr BlobLiteral :=
  ⟨fun b n => reprPrec (b.datatype.val, b.langTag, b.byteLength) n⟩

/-- What one dictionary slot holds: an RDF term, or an out-of-line
literal that needs its bytes before it becomes one. -/
inductive WireTerm where
  | inline (t : Term)
  | blob   (b : BlobLiteral)
  deriving DecidableEq, Repr

/-- The well-formedness rule an out-of-line literal must satisfy. The
lexical form plays no part in `RDF.literalWf`, so the empty string is a
faithful stand-in for the bytes the decoder does not have. -/
def blobWf (dt : WfIri) (langTag : Option String)
    (direction : Option TextDirection) : Bool :=
  literalWf { lexicalForm := "", datatype := dt,
              langTag := langTag, direction := direction }

/-- Blob-literal admission: the byte extent is inside the two ceilings
and the digest is a SHA-256 digest. -/
def blobSupported (b : BlobLiteral) : Bool :=
  maxInlineLexicalBytes < b.byteLength && b.byteLength ≤ maxBlobBytes &&
    b.sha256.size == 32 && blobWf b.datatype b.langTag b.direction

/-! ## The language-tag and direction field -/

def serializeLangField? (langTag : Option String)
    (direction : Option TextDirection) : Option (List UInt8) :=
  match langTag, direction with
  | none,     none      => some [(0 : UInt8)]
  | none,     some _    => none
  | some t,   none      => (serializeLString? t).map (fun b => (1 : UInt8) :: b)
  | some t,   some .ltr => (serializeLString? t).map (fun b => (2 : UInt8) :: b)
  | some t,   some .rtl => (serializeLString? t).map (fun b => (3 : UInt8) :: b)

def parseLangField (bs : List UInt8) :
    Option ((Option String × Option TextDirection) × List UInt8) := do
  let (flag, afterFlag) ← parseU8 bs
  if flag == 0 then some ((none, none), afterFlag)
  else if flag == 1 then do
    let (t, rest) ← parseLString afterFlag
    some ((some t, none), rest)
  else if flag == 2 then do
    let (t, rest) ← parseLString afterFlag
    some ((some t, some TextDirection.ltr), rest)
  else if flag == 3 then do
    let (t, rest) ← parseLString afterFlag
    some ((some t, some TextDirection.rtl), rest)
  else none

/-! ## Encoding -/

/-- A literal is inline exactly when its UTF-8 lexical form is at most
`maxInlineLexicalBytes` bytes. -/
def lexicalFitsInline (l : WfLiteral) : Bool :=
  l.val.lexicalForm.utf8ByteSize ≤ maxInlineLexicalBytes

/-- Encoding of the four inline tags. Recursion is on the object slot of
a triple term, which is the only recursive position of `RDF.Term`. -/
def serializeInline? : Term → Option (List UInt8)
  | .iri i => (serializeLString? i.val).map (tagIri :: ·)
  | .bnode b => (serializeLString? b).map (tagBnode :: ·)
  | .literal l =>
      if !lexicalFitsInline l then none else do
        let lexical ← serializeLString? l.val.lexicalForm
        let datatype ← serializeLString? l.val.datatype.val
        let lang ← serializeLangField? l.val.langTag l.val.direction
        some (tagLiteralInline :: (lexical ++ datatype ++ lang))
  | .tripleTerm s p o => do
      let subject ← serializeSubject? s
      let predicate ← serializeLString? p.val
      let object ← serializeInline? o
      some (tagTripleTerm :: (subject ++ predicate ++ object))

def serializeBlob? (b : BlobLiteral) : Option (List UInt8) :=
  if !blobSupported b then none else do
    let datatype ← serializeLString? b.datatype.val
    let lang ← serializeLangField? b.langTag b.direction
    some (tagLiteralBlob :: (datatype ++ lang ++
      writeU64LE (UInt64.ofNat b.byteLength) ++ b.sha256.toList))

def serializeTerm? : WireTerm → Option (List UInt8)
  | .inline t => serializeInline? t
  | .blob b => serializeBlob? b

/-- The canonical byte key of a term, for a zone map or a sort. Order is
lexicographic on these bytes, which is the TLI1 key order restated over
v2. -/
def keyBytes (w : WireTerm) : Option (List UInt8) := serializeTerm? w

/-! ## Decoding

`parseInlineGo` carries a fuel argument because Lean cannot see that the
remainder returned by `parseLString` is structurally smaller than its
input. The fuel is the input's byte length, and every nesting level of a
triple term consumes at least its tag byte, so the fuel is never the
reason a well-formed encoding is refused;
`TermWireV2Theorems.parseTerm_serializeTerm?` states the round trip with
no fuel in sight. -/

private def mkLiteral? (lex dt : String) (langTag : Option String)
    (direction : Option TextDirection) : Option Term :=
  if h : isIri dt then
    let l : Literal := { lexicalForm := lex, datatype := ⟨dt, h⟩,
                         langTag := langTag, direction := direction }
    if hw : literalWf l then some (.literal ⟨l, hw⟩) else none
  else none

def parseInlineGo : Nat → List UInt8 → Option (Term × List UInt8)
  | 0, _ => none
  | fuel + 1, bs => do
      let (tag, afterTag) ← parseU8 bs
      if tag == tagIri then do
        let (i, rest) ← parseLString afterTag
        if h : isIri i then some (.iri ⟨i, h⟩, rest) else none
      else if tag == tagBnode then do
        let (b, rest) ← parseLString afterTag
        some (.bnode b, rest)
      else if tag == tagLiteralInline then do
        let (lex, afterLex) ← parseLString afterTag
        if maxInlineLexicalBytes < (bytesOfString lex).length then none else do
        let (dt, afterDt) ← parseLString afterLex
        let ((langTag, direction), rest) ← parseLangField afterDt
        (mkLiteral? lex dt langTag direction).map (fun t => (t, rest))
      else if tag == tagTripleTerm then do
        let (s, afterSubject) ← parseSubject afterTag
        let (p, afterPredicate) ← parseLString afterSubject
        if hp : isIri p then do
          let (o, rest) ← parseInlineGo fuel afterPredicate
          some (.tripleTerm s ⟨p, hp⟩ o, rest)
        else none
      else none

def parseInline (bs : List UInt8) : Option (Term × List UInt8) :=
  parseInlineGo bs.length bs

def parseBlob (bs : List UInt8) : Option (BlobLiteral × List UInt8) := do
  let (tag, afterTag) ← parseU8 bs
  if tag != tagLiteralBlob then none else do
  let (dt, afterDt) ← parseLString afterTag
  let ((langTag, direction), afterLang) ← parseLangField afterDt
  let rawLength ← readU64LE afterLang 0
  let afterLength := afterLang.drop 8
  let digest := afterLength.take 32
  if digest.length != 32 then none else
  if h : isIri dt then
    let b : BlobLiteral :=
      { datatype := ⟨dt, h⟩, langTag := langTag, direction := direction,
        byteLength := rawLength.toNat,
        sha256 := ByteArray.mk digest.toArray }
    if blobSupported b then some (b, afterLength.drop 32) else none
  else none

def parseTerm (bs : List UInt8) : Option (WireTerm × List UInt8) :=
  match bs with
  | [] => none
  | tag :: _ =>
      if tag == tagLiteralBlob then
        (parseBlob bs).map (fun p => (.blob p.1, p.2))
      else
        (parseInline bs).map (fun p => (.inline p.1, p.2))

/-! ## The packer's choice and the reader's resolution

`h` is the SHA-256 of the UTF-8 lexical form. `L4Factoidal.Crypto.sha256`
is the specification; `h` is taken as a parameter the way
`Storage.BlockMerkle.Hasher` is taken, so a native packer can pass
HACL*'s implementation and get the same digests. -/

/-- The pure specification hash. -/
def specHash : ByteArray → ByteArray := L4Factoidal.Crypto.sha256

/-- Choose the tag by lexical byte length, per section 4.1. -/
def toWire (h : ByteArray → ByteArray) : Term → WireTerm
  | .literal l =>
      if lexicalFitsInline l then .inline (.literal l)
      else .blob { datatype := l.val.datatype, langTag := l.val.langTag,
                   direction := l.val.direction,
                   byteLength := (bytesOfString l.val.lexicalForm).length,
                   sha256 := h l.val.lexicalForm.toUTF8 }
  | t => .inline t

/-- Resolve a wire term to an RDF term. `lookup` fetches the bytes named
by a digest. Missing bytes, a byte count that disagrees with
`byteLength`, a digest mismatch and invalid UTF-8 are all refusals. -/
def resolve (h : ByteArray → ByteArray) (lookup : ByteArray → Option ByteArray) :
    WireTerm → Option Term
  | .inline t => some t
  | .blob b => do
      let bytes ← lookup b.sha256
      if bytes.size != b.byteLength then none else
      if h bytes ≠ b.sha256 then none else do
      let lex ← String.fromUTF8? bytes
      let l : Literal := { lexicalForm := lex, datatype := b.datatype,
                           langTag := b.langTag, direction := b.direction }
      if hw : literalWf l then some (.literal ⟨l, hw⟩) else none

/-- The lookup a packer's own term supplies: the literal's lexical form,
returned when the digest asked for is the digest of that lexical form. -/
def lookupOf (h : ByteArray → ByteArray) (t : Term) :
    ByteArray → Option ByteArray :=
  fun digest =>
    match t with
    | .literal l =>
        if h l.val.lexicalForm.toUTF8 = digest then
          some l.val.lexicalForm.toUTF8
        else none
    | _ => none

/-! ## Samples -/

private def ex : WfIri := ⟨"https://example.test/s", by decide⟩
private def exp : WfIri := ⟨"https://example.test/p", by decide⟩

private def plain : WireTerm := .inline (.literal (Literal.string "hello"))

private def dirLit : WfLiteral :=
  ⟨{ lexicalForm := "שלום", datatype := rdfDirLangString,
     langTag := some "he", direction := some .rtl }, by decide⟩

private def ltrLit : WfLiteral :=
  ⟨{ lexicalForm := "bonjour", datatype := rdfDirLangString,
     langTag := some "fr", direction := some .ltr }, by decide⟩

private def nested : WireTerm :=
  .inline (.tripleTerm (.iri ex) exp (.tripleTerm (.bnode "b0") exp (.literal dirLit)))

private def bigLexical : String := String.ofList (List.replicate 70000 'a')

private def blobTerm : WireTerm := toWire specHash (.literal (Literal.string bigLexical))

private def roundTrip (w : WireTerm) : Option WireTerm :=
  (serializeTerm? w).bind (fun bs => (parseTerm bs).map Prod.fst)

#guard roundTrip (.inline (.iri ex)) == some (.inline (.iri ex))
#guard roundTrip (.inline (.bnode "b1")) == some (.inline (.bnode "b1"))
#guard roundTrip plain == some plain
#guard roundTrip (.inline (.literal dirLit)) == some (.inline (.literal dirLit))
#guard roundTrip (.inline (.literal ltrLit)) == some (.inline (.literal ltrLit))
#guard roundTrip nested == some nested
#guard roundTrip blobTerm == some blobTerm
#guard (match blobTerm with | .blob b => b.byteLength == 70000 | _ => false)
#guard (match blobTerm with | .blob b => b.sha256.size == 32 | _ => false)
#guard toWire specHash (.literal (Literal.string "hello")) == plain
#guard resolve specHash (lookupOf specHash (.literal (Literal.string bigLexical))) blobTerm
  == some (.literal (Literal.string bigLexical))
#guard (resolve specHash (fun _ => none) blobTerm).isNone
#guard (keyBytes (.inline (.iri ex))).isSome

end L4Factoidal.Storage.TermWireV2
