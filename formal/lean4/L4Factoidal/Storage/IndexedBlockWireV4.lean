/-
L4Factoidal.Storage.IndexedBlockWireV4 — quad rows with an in-block graph
column, a header graph-set summary, and the same PTD1 embedded dictionary.

`IBK4` is the quad-aware block layout decided by the owner on 2026-09-02
(`docs/designissues/2026-09-02-quad-aware-block-layout.md`, option B). One
block still holds one predicate, now across all graphs of a dataset. Each row
carries a graph column, so `GRAPH <iri> { ... }` is a bounded filter inside the
block instead of an entry selection in the manifest.

Three points of the byte design, stated here and in section 6.1 of
`docs/shardborough-storage-spec.md`:

* The graph column is a BIASED u32 field: wire value `0` is the default graph
  and wire value `k + 1` is block-local term ID `k`. Specification section 5
  requires that "a normal term ID is not reserved as a default-graph
  sentinel", so IBK4 does not reserve dictionary slot 0; the bias lives in the
  field, and PTD1 keeps assigning IDs from 0 exactly as IBK3 does.
* The header carries the distinct graph set (a count and one biased u32 per
  distinct graph, in first-occurrence row order). A planner can refuse a block
  for `GRAPH <iri>` after reading the header plus that fixed array, without
  reading any row. `decode` recomputes the set from the decoded rows and
  refuses a block whose stored summary differs, so the summary is never an
  independent source of truth.
* IBK3 is unchanged and stays readable. `IndexedBlock.Block` and every IBK3
  theorem are untouched: this module introduces its own `QuadBlock`, because
  adding a graph column to `IndexedBlock.Block` would change the type that
  `IndexedBlockWireV1/V2/V3` and their landed round-trip proofs are stated
  over. A byte change is a new wire version (specification section 10).

The round trip is proved in `IndexedBlockWireV4Theorems`.

No `partial`, no `unsafe`, no `sorry`.
-/
import L4Factoidal.Storage.IndexedBlockWireV3
import L4Factoidal.RDF.DatasetGraphs

namespace L4Factoidal.Storage.IndexedBlockWireV4

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.Storage
open L4Factoidal.Storage.IndexedBlock (TermId buildIdMap)
open L4Factoidal.Storage.IndexedBlockWireV3 (byteArrayOfList listOfByteArray readU32At?)

/-! ## Graph identity in a row

`GraphId` is `Option GraphRef` at the RDF level: `none` is the default graph
and `some name` is a named graph, where `GraphRef = Subject` is an IRI or a
blank node (`RDF/DatasetGraphs.lean`). Inside a block the name is a term ID,
so the row-level type is `Option TermId`.

The denoted object is `Option GraphRef × Triple`, the same shape as
`RDF.Canonical.QQuad`. It is written out here rather than imported, so the
storage layer does not depend on the RDFC-1.0 canonicalization module. -/

/-- A quad whose graph, subject, predicate and object refer into one shared
    block dictionary. `g = none` is the default graph. -/
structure IdQuad where
  g : Option TermId
  s : TermId
  p : TermId
  o : TermId
  deriving Repr, DecidableEq, Inhabited

/-- One row in a contiguous predicate segment. `position` preserves the source
    sequence when segments are decoded independently, exactly as in IBK3. -/
structure PositionedIdQuad where
  position : Nat
  row : IdQuad
  deriving Repr, DecidableEq, Inhabited

/-- The RDF-level quad an `IdQuad` denotes once its IDs are resolved. -/
abbrev QuadRow := Option GraphRef × Triple

/-- The wire value of the graph column. `0` is the default graph; a named
    graph with block-local term ID `k` is written as `k + 1`. -/
def graphField : Option TermId → Nat
  | none => 0
  | some id => id + 1

/-- The inverse of `graphField` on wire values. -/
def graphOfField (value : Nat) : Option TermId :=
  if value == 0 then none else some (value - 1)

@[simp] theorem graphOfField_graphField (g : Option TermId) :
    graphOfField (graphField g) = g := by
  cases g <;> simp [graphField, graphOfField]

/-- The distinct graph column values, in first-occurrence row order. This is
    the header summary the encoder writes and the decoder recomputes. -/
def distinctGraphs (rows : List IdQuad) : List (Option TermId) :=
  rows.foldl (fun acc row => if acc.contains row.g then acc else acc ++ [row.g]) []

/-! ## The in-memory quad block -/

def addPartition (partitions : Std.HashMap TermId (List IdQuad))
    (row : IdQuad) : Std.HashMap TermId (List IdQuad) :=
  partitions.insert row.p (row :: partitions.getD row.p [])

/-- An immutable RDF quad block: one shared term dictionary, source-order ID
    rows carrying a graph column, and the predicate partition cache. -/
structure QuadBlock where
  dict : Array Term
  idByTerm : Std.HashMap Term TermId
  rows : Array IdQuad
  byPredicate : Std.HashMap TermId (List IdQuad)

private structure BuildState where
  dict : Array Term := #[]
  idByTerm : Std.HashMap Term TermId := ∅
  rows : Array IdQuad := #[]
  byPredicate : Std.HashMap TermId (List IdQuad) := ∅

private def intern (state : BuildState) (term : Term) : BuildState × TermId :=
  match state.idByTerm[term]? with
  | some id => (state, id)
  | none =>
      let id := state.dict.size
      ({ state with dict := state.dict.push term, idByTerm := state.idByTerm.insert term id }, id)

private def internQuad (state : BuildState) (quad : QuadRow) : BuildState :=
  let (state0, g) :=
    match quad.1 with
    | none => (state, (none : Option TermId))
    | some name =>
        let (next, id) := intern state name.toTerm
        (next, some id)
  let (state1, s) := intern state0 quad.2.s.toTerm
  let (state2, p) := intern state1 (.iri quad.2.p)
  let (state3, o) := intern state2 quad.2.o
  let row : IdQuad := { g := g, s := s, p := p, o := o }
  { state3 with
    rows := state3.rows.push row
    byPredicate := addPartition state3.byPredicate row }

/-- Build a quad block from a list of quads, interning every graph name,
    subject, predicate and object into one dictionary. -/
def fromQuads (quads : List QuadRow) : QuadBlock :=
  let state := quads.foldl internQuad {}
  { dict := state.dict, idByTerm := state.idByTerm, rows := state.rows,
    byPredicate := state.byPredicate }

/-- A row is well formed when its subject, predicate and object IDs resolve to
    an RDF subject, a predicate IRI and an object, and — for a named graph —
    its graph ID resolves to an IRI or a blank node (`GraphRef`). A graph ID
    that the dictionary does not assign is refused here. -/
def rowWellFormed (dict : Array Term) (row : IdQuad) : Bool :=
  match dict[row.s]?, dict[row.p]?, dict[row.o]? with
  | some s, some (.iri _), some _ =>
      s.toSubject?.isSome &&
        (match row.g with
         | none => true
         | some gid =>
             match dict[gid]? with
             | some name => name.toSubject?.isSome
             | none => false)
  | _, _, _ => false

/-- Reconstruct a quad block from a decoded dictionary and decoded ID rows.
    `buildIdMap` is IBK3's: it refuses a dictionary with repeated terms, whose
    ID map would not be injective. -/
def fromParts? (dict : Array Term) (rows : Array IdQuad) : Option QuadBlock := do
  let ids ← buildIdMap dict.toList 0 ∅
  if rows.toList.all (rowWellFormed dict) then
    some { dict := dict, idByTerm := ids, rows := rows,
           byPredicate := rows.foldl addPartition ∅ }
  else none

/-- Decode one ID quad. An unresolvable reference is refused rather than
    mapped to a fabricated term. -/
def decodeQuad? (dict : Array Term) (row : IdQuad) : Option QuadRow := do
  let s ← dict[row.s]?
  let p ← dict[row.p]?
  let o ← dict[row.o]?
  let subject ← s.toSubject?
  let graph : Option GraphRef ←
    match row.g with
    | none => some none
    | some gid => do
        let name ← dict[gid]?
        let named ← name.toSubject?
        some (some named)
  match p with
  | .iri predicate => some (graph, { s := subject, p := predicate, o := o })
  | _ => none

/-- The RDF dataset content the rows denote, in physical row order: the quads
    `(g, s, p, o)` with `g = none` for the default graph. -/
def QuadBlock.denotes (block : QuadBlock) : List QuadRow :=
  block.rows.toList.filterMap (decodeQuad? block.dict)

/-- The header graph-set summary resolved to RDF graph names, in the block's
    first-occurrence row order. This is what a manifest copies: the summary on
    the wire holds block-local term IDs, so resolving one to a name needs a
    PTD1 page of this block, which is the read a planner must not have to do.
    `none` when a summary entry's ID is not assigned by the dictionary, which
    `supported` and `decode` both refuse. -/
def graphNames? (block : QuadBlock) : Option (List (Option GraphRef)) :=
  (distinctGraphs block.rows.toList).mapM fun g =>
    match g with
    | none => some none
    | some gid => do
        let term ← block.dict[gid]?
        let named ← term.toSubject?
        some (some named)

/-! ## The IBK4 byte format -/

/-- `'IBK4'` in little-endian form. -/
def magic : UInt32 := 0x344B4249
def version : UInt8 := 4
def magicVersionBytes : Nat := 4 + 1
def crcBytes : Nat := 4

/-- Fixed header: magic/version, row count, PTD1 byte length, and the number
    of distinct graphs in the graph-set summary that follows it. -/
structure Prefix where
  rowCount : Nat
  dictionaryBytes : Nat
  graphCount : Nat
  deriving Repr, DecidableEq, Inhabited

def prefixBytes : Nat := 4 + 1 + 12
def graphEntryBytes : Nat := 4
def rowBytes : Nat := 20

structure ByteRange where
  offset : Nat
  length : Nat
  deriving Repr, DecidableEq, Inhabited

/-- The graph-set summary: `graphCount` biased u32 values immediately after
    the fixed header. A planner reads this range and the header alone to
    decide whether a block can contain a wanted graph. -/
def graphSummaryRange (header : Prefix) : ByteRange :=
  { offset := prefixBytes, length := header.graphCount * graphEntryBytes }

def rowsRange (header : Prefix) : ByteRange :=
  { offset := prefixBytes + header.graphCount * graphEntryBytes
  , length := header.rowCount * rowBytes }

/-- A checked contiguous subset of fixed-width rows, for a resumable cursor.
    The caller receives no range when its start/count leaves the declared row
    extent. -/
def rowRange? (header : Prefix) (start count : Nat) : Option ByteRange :=
  if start > header.rowCount || count > header.rowCount - start then none
  else some
    { offset := (rowsRange header).offset + start * rowBytes
      length := count * rowBytes }

def dictionaryRange (header : Prefix) : ByteRange :=
  { offset := prefixBytes + header.graphCount * graphEntryBytes +
      header.rowCount * rowBytes
    length := header.dictionaryBytes }

/-- One row: position, graph column, subject, predicate, object. -/
def encodeRow (entry : PositionedIdQuad) : List UInt8 :=
  writeU32LE (UInt32.ofNat entry.position) ++
  writeU32LE (UInt32.ofNat (graphField entry.row.g)) ++
  writeU32LE (UInt32.ofNat entry.row.s) ++ writeU32LE (UInt32.ofNat entry.row.p) ++
  writeU32LE (UInt32.ofNat entry.row.o)

def encodeGraphEntry (g : Option TermId) : List UInt8 :=
  writeU32LE (UInt32.ofNat (graphField g))

def positionedRows (block : QuadBlock) : List PositionedIdQuad :=
  block.rows.toList.zipIdx.map fun (row, position) => { position, row }

def onePredicate (block : QuadBlock) : Bool :=
  match block.rows.toList with
  | [] => false
  | row :: rows => rows.all fun later => later.p == row.p

/-- The 32-bit wire-field admission for a quad block. It is IBK1's, plus the
    graph column of every row and of every graph-set summary entry. -/
def fieldsSupported (block : QuadBlock) : Bool :=
  block.dict.toList.all BlockWireV0.termSupported &&
  IndexedBlockWireV1.fitsU32 block.dict.size &&
  IndexedBlockWireV1.fitsU32 block.rows.size &&
  block.rows.toList.all (fun row =>
    IndexedBlockWireV1.fitsU32 row.s && IndexedBlockWireV1.fitsU32 row.p &&
    IndexedBlockWireV1.fitsU32 row.o &&
    IndexedBlockWireV1.fitsU32 (graphField row.g)) &&
  (distinctGraphs block.rows.toList).all
    (fun g => IndexedBlockWireV1.fitsU32 (graphField g))

/-- IBK4 admission. Encoder admission equals decoder admission: every
    conjunct is a test `decode` re-runs on what it read back.

    1. `fieldsSupported` — the wire-supported term subset, and the 32-bit
       fields: dictionary size, row count, and each row's subject, predicate,
       object and biased graph column, and each summary entry.
    2. `onePredicate` — the block is nonempty and predicate-local.
    3. `PagedTermDictionary.supported` — PTD1's own term-codec admission,
       including the u32 length-prefix condition of the total term encoder.
    4. `(fromParts? block.dict block.rows).isSome` — the decoder's own
       reconstruction step, which refuses a dictionary with repeated terms and
       rows whose subject, predicate, object or graph ID does not resolve. -/
def supported (block : QuadBlock) : Bool :=
  fieldsSupported block && onePredicate block &&
    PagedTermDictionary.supported block.dict &&
    (fromParts? block.dict block.rows).isSome

/-- The unchecked byte assembly, for negative tests that must produce a
    well-framed artifact the encoder itself refuses. Production writers call
    `encode?`. -/
def encodeList (block : QuadBlock) : List UInt8 :=
  let graphs := distinctGraphs block.rows.toList
  let graphBytes := graphs.flatMap encodeGraphEntry
  let rows := positionedRows block |>.flatMap encodeRow
  let dictionary := (PagedTermDictionary.encode? block.dict).getD ByteArray.empty |>.data.toList
  let payload := writeU32LE (UInt32.ofNat block.rows.size) ++
    writeU32LE (UInt32.ofNat dictionary.length) ++ writeU32LE (UInt32.ofNat graphs.length) ++
    graphBytes ++ rows ++ dictionary
  writeU32LE magic ++ [version] ++ payload ++ writeU32LE (crc32c payload)

def encode? (block : QuadBlock) : Option ByteArray := do
  if !supported block then none else
  let dictionary ← PagedTermDictionary.encode? block.dict
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

def decodeGraphsGo : Nat → ByteArray → Nat → List (Option TermId) →
    Option (List (Option TermId))
  | 0, _, _, reversed => some reversed.reverse
  | count + 1, bytes, offset, reversed => do
      let field ← readU32At? bytes offset
      decodeGraphsGo count bytes (offset + graphEntryBytes)
        (graphOfField field.toNat :: reversed)

/-- Decode the fixed-width graph-set summary. -/
def decodeGraphSummary (count : Nat) (bytes : ByteArray) : Option (List (Option TermId)) :=
  if bytes.size != count * graphEntryBytes then none
  else decodeGraphsGo count bytes 0 []

def decodeRowsGo : Nat → ByteArray → Nat → List PositionedIdQuad →
    Option (List PositionedIdQuad)
  | 0, _, _, reversed => some reversed.reverse
  | count + 1, bytes, offset, reversed => do
      let position ← readU32At? bytes offset
      let g ← readU32At? bytes (offset + 4)
      let s ← readU32At? bytes (offset + 8)
      let p ← readU32At? bytes (offset + 12)
      let o ← readU32At? bytes (offset + 16)
      decodeRowsGo count bytes (offset + rowBytes)
        ({ position := position.toNat,
           row := { g := graphOfField g.toNat, s := s.toNat, p := p.toNat, o := o.toNat } }
          :: reversed)

/-- Fixed-width row decoding with a reverse accumulator, as in IBK3: the final
    reversal restores wire order once, without a data-sized call stack. -/
def decodeRows (count : Nat) (bytes : ByteArray) : Option (List PositionedIdQuad) :=
  if bytes.size != count * rowBytes then none else decodeRowsGo count bytes 0 []

def canonicalOrder (rows : List PositionedIdQuad) : Bool :=
  rows.zipIdx.all fun (entry, position) => entry.position == position

/-- Rows are admitted when their positions are exactly `0, 1, ..., rowCount-1`.
    The encoder's output already is in that order, so it is checked directly;
    sorting is reserved for a non-canonical order and gives the same answer.
    The direct path is what the round-trip proof reasons about, since Lean core
    has no theorems about `Array.qsort`. -/
def orderedRows? (rowCount : Nat) (rows : List PositionedIdQuad) : Option (Array IdQuad) :=
  if rows.length != rowCount then none
  else if canonicalOrder rows then
    some (rows.map PositionedIdQuad.row |>.toArray)
  else
    let ordered := rows.toArray.qsort (fun left right => left.position < right.position) |>.toList
    if canonicalOrder ordered then
      some (ordered.map PositionedIdQuad.row |>.toArray)
    else none

def predicateLocal (rows : Array IdQuad) : Bool :=
  match rows.toList with
  | [] => false
  | row :: rest => rest.all fun later => later.p == row.p

/-- Read only the header and the graph-set summary. This is the planner entry
    point: a block whose summary does not contain a wanted graph cannot
    contribute a row to `GRAPH <iri> { ... }`, and no row or dictionary byte is
    read to establish that. The summary is authoritative only for a block that
    `decode` admits, since `decode` re-derives it from the rows. -/
def decodeGraphSet? (headerBytes summaryBytes : ByteArray) :
    Option (Prefix × List (Option TermId)) := do
  let header ← decodePrefix headerBytes
  let summary ← decodeGraphSummary header.graphCount summaryBytes
  some (header, summary)

/-! ## The admission decoder

An IBK4 artifact is the largest object a quad query reads: one predicate block
of the SKOS store measured for
<https://github.com/danbri/factoidal/issues/653> is 5,571,302 bytes. Reading it
through `listOfByteArray` converts every byte to a cons cell, the payload is
copied again by `List.drop`/`List.take`, `crc32c` folds over that copy, and the
stored-checksum read drops the list once more — four data-sized allocations per
artifact. `PagedTermDictionary` and `IndexedBlockWireV3` were both moved off
that shape; IBK4, the quad codec, was not, and it is what the WebAssembly query
path spends most of its time in.

`decodeSpec` keeps the list decoder as the SPECIFICATION of what IBK4 admits.
`decode` reads the same fields by byte-array index and checksums the payload in
place with `Bytes.crc32cAppendArray`.
`IndexedBlockWireV4Theorems.decode_eq_spec` proves

    decode bytes = decodeSpec bytes

for every `bytes`, so the format and the admission decision are unchanged. -/

/-- Complete admission decoder, stated over the byte list. This is the
    SPECIFICATION; `decode` is proved equal to it.

    PTD1 validates its own page layout and CRC; IBK4 validates its framing, row
    count and order, predicate locality, the graph-set summary against the
    decoded rows, and its CRC, before rebuilding the quad-block denotation. -/
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
  let ptd ← PagedTermDictionary.decodePrefix (dictionaryBytes.extract 0 PagedTermDictionary.prefixBytes)
  if ptd.pageTerms != PagedTermDictionary.defaultPageTerms then none else do
  let summary ← decodeGraphSummary header.graphCount (bytes.extract graphStart graphEnd)
  let positioned ← decodeRows header.rowCount (bytes.extract graphEnd rowEnd)
  let rows ← orderedRows? header.rowCount positioned
  if !predicateLocal rows then none else do
  if summary != distinctGraphs rows.toList then none else do
  let dictionary ← PagedTermDictionary.decode? dictionaryBytes
  fromParts? dictionary rows

/-- Complete admission decoder, reading the artifact by byte-array index.

    The bytes admitted, and the quad block returned, are exactly
    `decodeSpec`'s; `IndexedBlockWireV4Theorems.decode_eq_spec` is that
    proof. -/
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
  let ptd ← PagedTermDictionary.decodePrefix (dictionaryBytes.extract 0 PagedTermDictionary.prefixBytes)
  if ptd.pageTerms != PagedTermDictionary.defaultPageTerms then none else do
  let summary ← decodeGraphSummary header.graphCount (bytes.extract graphStart graphEnd)
  let positioned ← decodeRows header.rowCount (bytes.extract graphEnd rowEnd)
  let rows ← orderedRows? header.rowCount positioned
  if !predicateLocal rows then none else do
  if summary != distinctGraphs rows.toList then none else do
  let dictionary ← PagedTermDictionary.decode? dictionaryBytes
  fromParts? dictionary rows

/-! ## Build-time checks -/

private def pName : WfIri := ⟨"http://example.org/name", by simp [isIri]⟩
private def alice : Subject := .iri ⟨"http://example.org/alice", by simp [isIri]⟩
private def bob : Subject := .iri ⟨"http://example.org/bob", by simp [isIri]⟩
private def g1 : GraphRef := .iri ⟨"http://example.org/g1", by simp [isIri]⟩

/-- One predicate, two graphs: one default-graph quad and two quads in `g1`. -/
private def twoGraphQuads : List QuadRow :=
  [(none, { s := alice, p := pName, o := .literal (Literal.langString "Alice" "en") }),
   (some g1, { s := bob, p := pName, o := .literal (Literal.langString "Bob" "en") }),
   (some g1, { s := alice, p := pName, o := .literal (Literal.string "A") })]

private def twoGraphBlock : QuadBlock := fromQuads twoGraphQuads
private def twoGraphBytes : ByteArray := (encode? twoGraphBlock).getD ByteArray.empty

#guard (encode? twoGraphBlock).isSome
#guard twoGraphBlock.rows.size == 3
#guard twoGraphBlock.denotes == twoGraphQuads

-- The summary holds the default graph and `g1`, in first-occurrence order.
#guard (distinctGraphs twoGraphBlock.rows.toList).length == 2
#guard (distinctGraphs twoGraphBlock.rows.toList).head? == some none

-- The two-graph block round-trips.
#guard ((decode twoGraphBytes).map (·.dict)) == some twoGraphBlock.dict
#guard ((decode twoGraphBytes).map (·.rows)) == some twoGraphBlock.rows
#guard ((decode twoGraphBytes).map QuadBlock.denotes) == some twoGraphBlock.denotes

-- The planner reads the graph set from the header plus the summary array
-- alone, with no row or dictionary byte.
#guard (decodeGraphSet? (twoGraphBytes.extract 0 prefixBytes)
    (twoGraphBytes.extract prefixBytes (prefixBytes + 2 * graphEntryBytes))).map Prod.snd
  == some (distinctGraphs twoGraphBlock.rows.toList)

/-- `fromQuads` on a single default-graph quad interns subject, predicate and
    object as local IDs 0, 1 and 2, so `3` is not an assigned ID. -/
private def oneQuadBlock : QuadBlock :=
  fromQuads [(none, { s := alice, p := pName, o := .literal (Literal.string "A") })]

#guard oneQuadBlock.dict.size == 3

/-- A row whose graph ID the dictionary never assigned. -/
private def badGraphBlock : QuadBlock :=
  { oneQuadBlock with rows := #[{ g := some 3, s := 0, p := 1, o := 2 }] }

/-- The positive control: the same row with the default graph. -/
private def goodGraphBlock : QuadBlock :=
  { oneQuadBlock with rows := #[{ g := none, s := 0, p := 1, o := 2 }] }

#guard (encode? badGraphBlock).isNone
#guard (decode (byteArrayOfList (encodeList badGraphBlock))).isNone
#guard (encode? goodGraphBlock).isSome
#guard (decode (byteArrayOfList (encodeList goodGraphBlock))).isSome

end L4Factoidal.Storage.IndexedBlockWireV4
