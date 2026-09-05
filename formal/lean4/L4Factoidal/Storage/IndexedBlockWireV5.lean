/-
L4Factoidal.Storage.IndexedBlockWireV5 — the IBK4 quad-block layout with a
PTD2 dictionary of `TermWireV2.WireTerm`.

`IBK5` is the wire-version-10 block, decided in
`docs/designissues/2026-09-05-wire-version-10-scale.md` section 3. The byte
layout is IBK4's, field for field: a seventeen-byte header, the fixed-width
graph-set summary, twenty-byte quad rows, a complete paged term dictionary,
and a CRC32C over every post-version byte. Two things change:

* the dictionary is PTD2, so its terms are `WireTerm` — an RDF term, or an
  out-of-line literal named by its byte length and SHA-256 digest;
* the magic is `IBK5` and the version byte is 5, because a byte change is a
  new wire version (specification section 10).

IBK3 and IBK4 stay readable and are untouched.

## What a blob may be

A `WireTerm.blob` is a literal, so it can only be an object. `fromParts?`
refuses a block whose subject, predicate or graph-name position holds a blob,
exactly as it refuses a subject position holding a literal.

## Admission

Encoder admission equals decoder admission. Every conjunct of `supported` is a
test `decode` re-runs on what it read back.

1. `fieldsSupported` — every dictionary term is one the v2 codec admits
   (`PagedTermDictionaryV2.v2Codec.admits`, which is
   `(TermWireV2.serializeTerm? w).isSome`), and the 32-bit fields fit:
   dictionary size, row count, and each row's subject, predicate, object and
   biased graph column, and each graph-set summary entry.
2. `onePredicate` — the block is nonempty and predicate-local.
3. `PagedTermDictionaryV2.supported` — PTD2's own admission for the whole
   dictionary array.
4. `(fromParts? block.dict block.rows).isSome` — the decoder's own
   reconstruction step, which refuses a dictionary with repeated terms, a row
   whose subject, predicate, object or graph ID does not resolve, and a blob
   in a subject, predicate or graph position.

## What the manifest and the zone maps read

`blobDigests` is the ascending, repeat-free list of SHA-256 digests the
dictionary names, which is the per-entry blob reference list of SBM10 section
6.2. `subjectKeys` and `objectKeys` are the v2 canonical key bytes of every
row's subject and object, which is what an SBM10 zone map takes its bounds
from.

The round trip is proved in `IndexedBlockWireV5Theorems`.

No `partial`, no `unsafe`, no `sorry`.
-/
import L4Factoidal.Storage.IndexedBlockWireV4
import L4Factoidal.Storage.PagedTermDictionaryV2

namespace L4Factoidal.Storage.IndexedBlockWireV5

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.Storage
open L4Factoidal.Storage.TermWireV2
open L4Factoidal.Storage.IndexedBlock (TermId)
open L4Factoidal.Storage.IndexedBlockWireV3 (byteArrayOfList listOfByteArray readU32At?)
open L4Factoidal.Storage.IndexedBlockWireV4 (IdQuad PositionedIdQuad graphField graphOfField
  distinctGraphs encodeRow encodeGraphEntry canonicalOrder predicateLocal
  graphEntryBytes rowBytes prefixBytes magicVersionBytes crcBytes
  decodeGraphsGo decodeGraphSummary decodeRowsGo decodeRows orderedRows?)

/-! ## Hashing a wire term

`Std.HashMap` needs `BEq` and `Hashable`. `WireTerm` derives `DecidableEq`;
the digest of a blob literal is a `ByteArray`, which has neither a `Hashable`
nor a `Repr` instance in core, so both are given here over its byte list. -/

instance : Hashable BlobLiteral :=
  ⟨fun b => hash (b.datatype.val, b.langTag,
    b.direction.map (fun | .ltr => (0 : Nat) | .rtl => 1), b.byteLength, b.sha256.toList)⟩

instance : Hashable WireTerm :=
  ⟨fun w => match w with
    | .inline t => hash (0, hash t)
    | .blob b => hash (1, hash b)⟩

/-- A wire term in a subject, predicate or graph-name position. A blob is a
literal, so it never is one. -/
def wireSubject? : WireTerm → Option Subject
  | .inline t => t.toSubject?
  | .blob _ => none

/-! ## Wire-level quads

The denoted object of an IBK5 row is a triple whose object is a `WireTerm`.
`resolveBlock` turns those into `RDF.Triple`s once the blob bytes are
available. -/

/-- A triple whose object may be an out-of-line literal. -/
structure WireTriple where
  s : Subject
  p : WfIri
  o : WireTerm
  deriving Repr, DecidableEq

/-- The wire-level quad an `IdQuad` denotes once its IDs are resolved. -/
abbrev QuadRow := Option GraphRef × WireTriple

/-! ## The in-memory quad block -/

def addPartition (partitions : Std.HashMap TermId (List IdQuad))
    (row : IdQuad) : Std.HashMap TermId (List IdQuad) :=
  partitions.insert row.p (row :: partitions.getD row.p [])

/-- An immutable RDF quad block over wire terms: one shared PTD2 dictionary,
    source-order ID rows carrying a graph column, and the predicate partition
    cache. -/
structure QuadBlock where
  dict : Array WireTerm
  idByTerm : Std.HashMap WireTerm TermId
  rows : Array IdQuad
  byPredicate : Std.HashMap TermId (List IdQuad)

/-- IBK3's duplicate-refusing identity map, over wire terms. -/
def buildIdMap : List WireTerm → TermId → Std.HashMap WireTerm TermId →
    Option (Std.HashMap WireTerm TermId)
  | [], _, ids => some ids
  | term :: rest, next, ids =>
      if ids[term]?.isSome then none
      else buildIdMap rest (next + 1) (ids.insert term next)

private structure BuildState where
  dict : Array WireTerm := #[]
  idByTerm : Std.HashMap WireTerm TermId := ∅
  rows : Array IdQuad := #[]
  byPredicate : Std.HashMap TermId (List IdQuad) := ∅

private def intern (state : BuildState) (term : WireTerm) : BuildState × TermId :=
  match state.idByTerm[term]? with
  | some id => (state, id)
  | none =>
      let id := state.dict.size
      ({ state with dict := state.dict.push term,
                    idByTerm := state.idByTerm.insert term id }, id)

private def internQuad (state : BuildState) (quad : QuadRow) : BuildState :=
  let (state0, g) :=
    match quad.1 with
    | none => (state, (none : Option TermId))
    | some name =>
        let (next, id) := intern state (.inline name.toTerm)
        (next, some id)
  let (state1, s) := intern state0 (.inline quad.2.s.toTerm)
  let (state2, p) := intern state1 (.inline (.iri quad.2.p))
  let (state3, o) := intern state2 quad.2.o
  let row : IdQuad := { g := g, s := s, p := p, o := o }
  { state3 with
    rows := state3.rows.push row
    byPredicate := addPartition state3.byPredicate row }

/-- Build a quad block from a list of wire-level quads. -/
def fromQuads (quads : List QuadRow) : QuadBlock :=
  let state := quads.foldl internQuad {}
  { dict := state.dict, idByTerm := state.idByTerm, rows := state.rows,
    byPredicate := state.byPredicate }

/-- A row is well formed when its subject, predicate and object IDs resolve,
    the subject resolves to an RDF subject, the predicate to an IRI, and — for
    a named graph — the graph ID to an IRI or a blank node. A blob in any of
    those three positions is refused, because `wireSubject?` gives it no
    subject and an inline IRI is the only accepted predicate. -/
def rowWellFormed (dict : Array WireTerm) (row : IdQuad) : Bool :=
  match dict[row.s]?, dict[row.p]?, dict[row.o]? with
  | some s, some (.inline (.iri _)), some _ =>
      (wireSubject? s).isSome &&
        (match row.g with
         | none => true
         | some gid =>
             match dict[gid]? with
             | some name => (wireSubject? name).isSome
             | none => false)
  | _, _, _ => false

/-- Reconstruct a quad block from a decoded dictionary and decoded ID rows. -/
def fromParts? (dict : Array WireTerm) (rows : Array IdQuad) : Option QuadBlock := do
  let ids ← buildIdMap dict.toList 0 ∅
  if rows.toList.all (rowWellFormed dict) then
    some { dict := dict, idByTerm := ids, rows := rows,
           byPredicate := rows.foldl addPartition ∅ }
  else none

/-- Decode one ID quad. An unresolvable reference is refused rather than
    mapped to a fabricated term. -/
def decodeQuad? (dict : Array WireTerm) (row : IdQuad) : Option QuadRow := do
  let s ← dict[row.s]?
  let p ← dict[row.p]?
  let o ← dict[row.o]?
  let subject ← wireSubject? s
  let graph : Option GraphRef ←
    match row.g with
    | none => some none
    | some gid => do
        let name ← dict[gid]?
        let named ← wireSubject? name
        some (some named)
  match p with
  | .inline (.iri predicate) => some (graph, { s := subject, p := predicate, o := o })
  | _ => none

/-- The wire-level dataset content the rows denote, in physical row order. -/
def QuadBlock.denotes (block : QuadBlock) : List QuadRow :=
  block.rows.toList.filterMap (decodeQuad? block.dict)

/-- The header graph-set summary resolved to RDF graph names, in the block's
    first-occurrence row order. -/
def graphNames? (block : QuadBlock) : Option (List (Option GraphRef)) :=
  (distinctGraphs block.rows.toList).mapM fun g =>
    match g with
    | none => some none
    | some gid => do
        let term ← block.dict[gid]?
        let named ← wireSubject? term
        some (some named)

/-! ## Blob references and zone-map keys -/

private def insertDigest : List (List UInt8) → List UInt8 → List (List UInt8)
  | [], d => [d]
  | head :: rest, d =>
      if d == head then head :: rest
      else if List.lt d head then d :: head :: rest
      else head :: insertDigest rest d

/-- The SHA-256 digests of every out-of-line literal in the dictionary,
    ascending by digest bytes and with no repeats. This is the per-entry blob
    reference list of SBM10 section 6.2. -/
def blobDigests (block : QuadBlock) : List ByteArray :=
  (block.dict.toList.foldl (fun acc w =>
      match w with
      | .inline _ => acc
      | .blob b => insertDigest acc b.sha256.toList) []).map
    (fun d => ByteArray.mk d.toArray)

/-- The v2 canonical key bytes of each row's subject, in row order. `none` for
    a row whose subject ID is not assigned, which `supported` refuses. -/
def subjectKeys (block : QuadBlock) : Option (List (List UInt8)) :=
  block.rows.toList.mapM fun row => do
    let term ← block.dict[row.s]?
    keyBytes term

/-- The v2 canonical key bytes of each row's object, in row order. -/
def objectKeys (block : QuadBlock) : Option (List (List UInt8)) :=
  block.rows.toList.mapM fun row => do
    let term ← block.dict[row.o]?
    keyBytes term

/-! ## Resolution -/

/-- Turn the block's wire-level denotation into RDF quads, fetching every
    out-of-line literal's bytes through `lookup` and checking them against
    `h`. One missing, wrong-length, wrong-digest or invalid-UTF-8 blob refuses
    the whole block. -/
def resolveBlock (h : ByteArray → ByteArray) (lookup : ByteArray → Option ByteArray)
    (block : QuadBlock) : Option (List (Option GraphRef × Triple)) :=
  block.denotes.mapM fun quad => do
    let o ← resolve h lookup quad.2.o
    some (quad.1, ({ s := quad.2.s, p := quad.2.p, o := o } : Triple))

/-- The packer's direction: an RDF quad becomes a wire quad by choosing each
    object's tag with `TermWireV2.toWire`. -/
def toWireQuad (h : ByteArray → ByteArray) (quad : Option GraphRef × Triple) : QuadRow :=
  (quad.1, { s := quad.2.s, p := quad.2.p, o := toWire h quad.2.o })

/-- A block built from RDF quads. -/
def fromRdfQuads (h : ByteArray → ByteArray)
    (quads : List (Option GraphRef × Triple)) : QuadBlock :=
  fromQuads (quads.map (toWireQuad h))

/-! ## The IBK5 byte format -/

/-- `'IBK5'` in little-endian form. -/
def magic : UInt32 := 0x354B4249
def version : UInt8 := 5

/-- Fixed header: magic/version, row count, PTD2 byte length, and the number
    of distinct graphs in the graph-set summary that follows it. -/
structure Prefix where
  rowCount : Nat
  dictionaryBytes : Nat
  graphCount : Nat
  deriving Repr, DecidableEq, Inhabited

structure ByteRange where
  offset : Nat
  length : Nat
  deriving Repr, DecidableEq, Inhabited

def graphSummaryRange (header : Prefix) : ByteRange :=
  { offset := prefixBytes, length := header.graphCount * graphEntryBytes }

def rowsRange (header : Prefix) : ByteRange :=
  { offset := prefixBytes + header.graphCount * graphEntryBytes
  , length := header.rowCount * rowBytes }

def rowRange? (header : Prefix) (start count : Nat) : Option ByteRange :=
  if start > header.rowCount || count > header.rowCount - start then none
  else some
    { offset := (rowsRange header).offset + start * rowBytes
      length := count * rowBytes }

def dictionaryRange (header : Prefix) : ByteRange :=
  { offset := prefixBytes + header.graphCount * graphEntryBytes +
      header.rowCount * rowBytes
    length := header.dictionaryBytes }

def positionedRows (block : QuadBlock) : List PositionedIdQuad :=
  block.rows.toList.zipIdx.map fun (row, position) => { position, row }

def onePredicate (block : QuadBlock) : Bool :=
  match block.rows.toList with
  | [] => false
  | row :: rows => rows.all fun later => later.p == row.p

/-- The 32-bit wire-field admission for a quad block, plus the v2 term-codec
    admission for every dictionary term. -/
def fieldsSupported (block : QuadBlock) : Bool :=
  block.dict.toList.all PagedTermDictionaryV2.v2Codec.admits &&
  IndexedBlockWireV1.fitsU32 block.dict.size &&
  IndexedBlockWireV1.fitsU32 block.rows.size &&
  block.rows.toList.all (fun row =>
    IndexedBlockWireV1.fitsU32 row.s && IndexedBlockWireV1.fitsU32 row.p &&
    IndexedBlockWireV1.fitsU32 row.o &&
    IndexedBlockWireV1.fitsU32 (graphField row.g)) &&
  (distinctGraphs block.rows.toList).all
    (fun g => IndexedBlockWireV1.fitsU32 (graphField g))

/-- IBK5 admission; see the module header for the four conjuncts. -/
def supported (block : QuadBlock) : Bool :=
  fieldsSupported block && onePredicate block &&
    PagedTermDictionaryV2.supported block.dict &&
    (fromParts? block.dict block.rows).isSome

/-- The unchecked byte assembly, for negative tests that must produce a
    well-framed artifact the encoder itself refuses. -/
def encodeList (block : QuadBlock) : List UInt8 :=
  let graphs := distinctGraphs block.rows.toList
  let graphBytes := graphs.flatMap encodeGraphEntry
  let rows := positionedRows block |>.flatMap encodeRow
  let dictionary :=
    (PagedTermDictionaryV2.encode? block.dict).getD ByteArray.empty |>.data.toList
  let payload := writeU32LE (UInt32.ofNat block.rows.size) ++
    writeU32LE (UInt32.ofNat dictionary.length) ++ writeU32LE (UInt32.ofNat graphs.length) ++
    graphBytes ++ rows ++ dictionary
  writeU32LE magic ++ [version] ++ payload ++ writeU32LE (crc32c payload)

def encode? (block : QuadBlock) : Option ByteArray := do
  if !supported block then none else
  let dictionary ← PagedTermDictionaryV2.encode? block.dict
  let graphs := distinctGraphs block.rows.toList
  let graphBytes := graphs.flatMap encodeGraphEntry
  let rows := positionedRows block |>.flatMap encodeRow
  if dictionary.size >= UInt32.size || rows.length >= UInt32.size ||
      graphs.length >= UInt32.size then none else
  let payload := writeU32LE (UInt32.ofNat block.rows.size) ++
    writeU32LE (UInt32.ofNat dictionary.size) ++ writeU32LE (UInt32.ofNat graphs.length) ++
    graphBytes ++ rows ++ dictionary.data.toList
  some <| byteArrayOfList (writeU32LE magic ++ [version] ++ payload ++ writeU32LE (crc32c payload))

def decodePrefix (bytes : ByteArray) : Option Prefix := do
  let input := listOfByteArray bytes
  let foundMagic ← readU32LE input 0
  if foundMagic != magic then none else do
  let (foundVersion, rest) ← parseU8 (input.drop 4)
  if foundVersion != version then none else do
  let rowCount ← readU32LE rest 0
  let dictionaryBytes ← readU32LE rest 4
  let graphCount ← readU32LE rest 8
  some { rowCount := rowCount.toNat, dictionaryBytes := dictionaryBytes.toNat,
         graphCount := graphCount.toNat }

/-! The graph-summary and row decoders are IBK4's. Those fields are identical
in the two versions and hold no term, so IBK5 reuses the definitions rather
than restating them, and inherits their proofs. -/

/-- Read only the header and the graph-set summary: the planner entry point. -/
def decodeGraphSet? (headerBytes summaryBytes : ByteArray) :
    Option (Prefix × List (Option TermId)) := do
  let header ← decodePrefix headerBytes
  let summary ← decodeGraphSummary header.graphCount summaryBytes
  some (header, summary)

/-! ## The admission decoder

`decodeSpec` keeps the list decoder as the SPECIFICATION of what IBK5 admits.
`decode` reads the same fields by byte-array index and checksums the payload in
place. `IndexedBlockWireV5Theorems.decode_eq_spec` proves the two equal. -/

def decodeSpec (bytes : ByteArray) : Option QuadBlock := do
  let input := listOfByteArray bytes
  let header ← decodePrefix (bytes.extract 0 prefixBytes)
  if input.length < prefixBytes + header.graphCount * graphEntryBytes +
      header.rowCount * rowBytes + header.dictionaryBytes + 4 then none else do
  let payload := input.drop magicVersionBytes |>.take (input.length - magicVersionBytes - crcBytes)
  let storedCrc ← readU32LE input (input.length - crcBytes)
  if storedCrc != crc32c payload then none else do
  let graphStart := prefixBytes
  let graphEnd := graphStart + header.graphCount * graphEntryBytes
  let rowEnd := graphEnd + header.rowCount * rowBytes
  let dictionaryEnd := rowEnd + header.dictionaryBytes
  if dictionaryEnd + 4 != input.length then none else do
  let dictionaryBytes := bytes.extract rowEnd dictionaryEnd
  let ptd ← PagedTermDictionaryV2.decodePrefix
    (dictionaryBytes.extract 0 PagedTermDictionaryV2.prefixBytes)
  if ptd.pageTerms != PagedTermDictionaryV2.defaultPageTerms then none else do
  let summary ← decodeGraphSummary header.graphCount (bytes.extract graphStart graphEnd)
  let positioned ← decodeRows header.rowCount (bytes.extract graphEnd rowEnd)
  let rows ← orderedRows? header.rowCount positioned
  if !predicateLocal rows then none else do
  if summary != distinctGraphs rows.toList then none else do
  let dictionary ← PagedTermDictionaryV2.decode? dictionaryBytes
  fromParts? dictionary rows

def decode (bytes : ByteArray) : Option QuadBlock := do
  let header ← decodePrefix (bytes.extract 0 prefixBytes)
  if bytes.size < prefixBytes + header.graphCount * graphEntryBytes +
      header.rowCount * rowBytes + header.dictionaryBytes + 4 then none else do
  let storedCrc ← readU32At? bytes (bytes.size - crcBytes)
  if storedCrc != (crc32cAppendArray 0xFFFFFFFF
      (bytes.extract magicVersionBytes (bytes.size - crcBytes)) ^^^ 0xFFFFFFFF) then none else do
  let graphStart := prefixBytes
  let graphEnd := graphStart + header.graphCount * graphEntryBytes
  let rowEnd := graphEnd + header.rowCount * rowBytes
  let dictionaryEnd := rowEnd + header.dictionaryBytes
  if dictionaryEnd + 4 != bytes.size then none else do
  let dictionaryBytes := bytes.extract rowEnd dictionaryEnd
  let ptd ← PagedTermDictionaryV2.decodePrefix
    (dictionaryBytes.extract 0 PagedTermDictionaryV2.prefixBytes)
  if ptd.pageTerms != PagedTermDictionaryV2.defaultPageTerms then none else do
  let summary ← decodeGraphSummary header.graphCount (bytes.extract graphStart graphEnd)
  let positioned ← decodeRows header.rowCount (bytes.extract graphEnd rowEnd)
  let rows ← orderedRows? header.rowCount positioned
  if !predicateLocal rows then none else do
  if summary != distinctGraphs rows.toList then none else do
  let dictionary ← PagedTermDictionaryV2.decode? dictionaryBytes
  fromParts? dictionary rows

/-! ## Build-time checks -/

private def pName : WfIri := ⟨"http://example.org/name", by simp [isIri]⟩
private def alice : Subject := .iri ⟨"http://example.org/alice", by simp [isIri]⟩
private def bob : Subject := .iri ⟨"http://example.org/bob", by simp [isIri]⟩
private def g1 : GraphRef := .iri ⟨"http://example.org/g1", by simp [isIri]⟩

private def rtlLit : WfLiteral :=
  ⟨{ lexicalForm := "שלום", datatype := rdfDirLangString,
     langTag := some "he", direction := some .rtl }, by decide⟩

private def bigLexical : String := String.ofList (List.replicate 70000 'a')

/-- Three RDF 1.2 objects the v1 codec refuses and IBK5 stores: a triple
    term, a directional language literal, and a 70,000-byte literal that goes
    out of line. -/
private def rdfQuads : List (Option GraphRef × Triple) :=
  [(none, { s := alice, p := pName,
            o := .tripleTerm bob pName (.literal (Literal.string "nested")) }),
   (some g1, { s := bob, p := pName, o := .literal rtlLit }),
   (some g1, { s := alice, p := pName, o := .literal (Literal.string bigLexical) })]

private def sampleBlock : QuadBlock := fromRdfQuads specHash rdfQuads
private def sampleBytes : ByteArray := (encode? sampleBlock).getD ByteArray.empty

/-- The lookup a packer holds: every literal of the source quads, by digest. -/
private def sampleLookup : ByteArray → Option ByteArray :=
  fun d => rdfQuads.findSome? (fun quad => lookupOf specHash quad.2.o d)

#guard (encode? sampleBlock).isSome
#guard sampleBlock.rows.size == 3
#guard (sampleBytes.extract 0 4).toList == [0x49, 0x42, 0x4B, 0x35]
#guard sampleBytes[4]! == 5

-- The block round-trips at the wire-term level.
#guard ((decode sampleBytes).map (·.dict)) == some sampleBlock.dict
#guard ((decode sampleBytes).map (·.rows)) == some sampleBlock.rows
#guard ((decode sampleBytes).map QuadBlock.denotes) == some sampleBlock.denotes

-- The 70,000-byte literal is the block's one out-of-line literal.
#guard (blobDigests sampleBlock).length == 1
#guard ((blobDigests sampleBlock).head?.map (·.size)) == some 32

-- Resolving the decoded block gives the original RDF quads back.
#guard ((decode sampleBytes).bind (resolveBlock specHash sampleLookup)) == some rdfQuads

-- Without the blob bytes the object cannot be resolved, and the block is not
-- silently returned with a fabricated literal.
#guard ((decode sampleBytes).bind (resolveBlock specHash (fun _ => none))).isNone

-- Zone-map keys exist for every row.
#guard (subjectKeys sampleBlock).map List.length == some 3
#guard (objectKeys sampleBlock).map List.length == some 3

-- The planner reads the graph set from the header plus the summary array
-- alone, with no row or dictionary byte.
#guard (decodeGraphSet? (sampleBytes.extract 0 prefixBytes)
    (sampleBytes.extract prefixBytes (prefixBytes + 2 * graphEntryBytes))).map Prod.snd
  == some (distinctGraphs sampleBlock.rows.toList)

/-- A blob may not be a subject. -/
private def blobTerm : WireTerm := toWire specHash (.literal (Literal.string bigLexical))

private def blobSubjectBlock : QuadBlock :=
  { dict := #[blobTerm, .inline (.iri pName), .inline (.literal (Literal.string "A"))]
    idByTerm := ∅
    rows := #[{ g := none, s := 0, p := 1, o := 2 }]
    byPredicate := ∅ }

#guard (encode? blobSubjectBlock).isNone
#guard (decode (byteArrayOfList (encodeList blobSubjectBlock))).isNone

/-- A row whose graph ID the dictionary never assigned. -/
private def oneQuadBlock : QuadBlock :=
  fromQuads [(none, { s := alice, p := pName,
                      o := .inline (.literal (Literal.string "A")) })]

#guard oneQuadBlock.dict.size == 3

private def badGraphBlock : QuadBlock :=
  { oneQuadBlock with rows := #[{ g := some 3, s := 0, p := 1, o := 2 }] }

private def goodGraphBlock : QuadBlock :=
  { oneQuadBlock with rows := #[{ g := none, s := 0, p := 1, o := 2 }] }

#guard (encode? badGraphBlock).isNone
#guard (decode (byteArrayOfList (encodeList badGraphBlock))).isNone
#guard (encode? goodGraphBlock).isSome
#guard (decode (byteArrayOfList (encodeList goodGraphBlock))).isSome

end L4Factoidal.Storage.IndexedBlockWireV5
