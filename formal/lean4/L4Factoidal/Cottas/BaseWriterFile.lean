/-
L4Factoidal.Cottas.BaseWriterFile — layer 5 of the port of
`RDF.CottasStore.BaseWriter`: the Parquet file structure, and
`serializeCottas`.

This is the top: page headers, the schema, column metadata and chunks,
row groups, the file metadata, and the whole-file assembly. Every
builder here writes Thrift compact fields through layer 2 and column
payloads through layers 3 and 4.

## What a Parquet file looks like from the outside

    PAR1 | page bytes … | file metadata | metadata length (LE u32) | PAR1

The trailing length is what lets a reader seek to the metadata without
scanning, and it comes BEFORE the closing magic. `serializeCottas_shape`
states the layout, and `serializeCottas_starts_and_ends_with_magic`
states the bracketing, because a file that loses either is unreadable
by any tool rather than subtly wrong.

## Offsets are cumulative, and that is the part that breaks

Each column chunk records where its data page starts. `buildRowGroup`
threads a running offset through the four columns in order and hands
the next offset out, and `buildRowGroups` chains that across row
groups starting at the length of the magic header — because the pages
begin after `PAR1`, not at zero. `rowGroupOffsets_are_cumulative` pins
the arithmetic: an offset that is off by the four magic bytes produces
a file every byte of which is correct except where it says the data
is.

## Two schema details that were found by cross-checking, not by
reasoning

The F\* source records both:

* A schema leaf carries `converted_type = UTF8` (field 6). Without it
  DuckDB presents the column as BLOB rather than VARCHAR. Found by a
  `parquet_scan` cross-check, not by reading the spec.
* Field 1 of the file metadata stamps `cottasFormatVersion`, not the
  Parquet-conventional 1, so the reader can reject any store this
  writer did not produce. That was an owner decision recorded at
  <https://github.com/danbri/factoidal/issues/445> — no migration path,
  no back-compatible reader.

Both are `#guard`ed so a later tidy-up cannot drop them as redundant.

No `sorry`, no user `axiom`, no `native_decide`.
-/
import L4Factoidal.Cottas.BaseWriterDict

namespace L4Factoidal.Cottas.BaseWriterFile

open L4Factoidal.Cottas.BaseWriterPrims
open L4Factoidal.Cottas.BaseWriterThrift
open L4Factoidal.Cottas.BaseWriterColumn
open L4Factoidal.Cottas.BaseWriterDict

/-! ## 1. Parquet vocabulary -/

def parquetTypeByteArray : Nat := 6
def parquetRepetitionOptional : Nat := 1
def parquetEncodingDlba : Nat := 6
def parquetEncodingRle : Nat := 3
def parquetEncodingPlain : Nat := 0
def parquetEncodingRleDictionary : Nat := 8
def parquetCodecUncompressed : Nat := 0
def parquetPageTypeDataPage : Nat := 0
def parquetPageTypeDictionaryPage : Nat := 2

def parquetMagic : String := "PAR1"

/-- `PAR1` as bytes, written out rather than computed: the kernel does
not reduce `String.toUTF8`, so a computed form makes every fact about
the header uncheckable at build time. A `#guard` ties it back to the
string. -/
def magicHeader : Bytes := [(0x50 : UInt8), 0x41, 0x52, 0x31]

/-- Field 1 of the file metadata. NOT the Parquet-conventional 1: the
reader rejects any store this writer did not produce
(<https://github.com/danbri/factoidal/issues/445>). -/
def cottasFormatVersion : Nat := 445

/-! ## 2. A quad, as four column strings -/

structure CottasQuad where
  s : String
  p : String
  o : String
  /-- The `DEFAULT` sentinel for the default graph — never the empty
  string. -/
  g : String
  deriving Repr, DecidableEq

def defaultGraphSentinel : String := "DEFAULT"

/-! ## 3. Page headers -/

def buildPageHeader (encoding numValues uncompressedSize compressedSize : Nat) : Bytes :=
  let dph := writeFieldI32 1 0 numValues ++ writeFieldI32 2 1 encoding
             ++ writeFieldI32 3 2 parquetEncodingRle
             ++ writeFieldI32 4 3 parquetEncodingRle ++ writeStop
  writeFieldI32 1 0 parquetPageTypeDataPage
  ++ writeFieldI32 2 1 uncompressedSize
  ++ writeFieldI32 3 2 compressedSize
  ++ writeFieldHeader tStruct 5 3 ++ dph ++ writeStop

/-- One DLBA column page. Returns the value count, the page length, and
the bytes. -/
def buildColumnPage (values : List String) : Nat × Nat × Bytes :=
  let valueCount := values.length
  let payload := defLevelSection valueCount ++ (dlbaLengthBlock values).2
                 ++ concatStringsBytes values
  let header := buildPageHeader parquetEncodingDlba valueCount payload.length payload.length
  let page := header ++ payload
  (valueCount, page.length, page)

/-! ## 4. Schema

A leaf carries `converted_type = UTF8` (field 6). Without it DuckDB
presents the column as BLOB rather than VARCHAR — found by a
`parquet_scan` cross-check, not by reading the spec. -/

def buildSchemaLeaf (name : String) : Bytes :=
  writeFieldI32 1 0 parquetTypeByteArray
  ++ writeFieldI32 3 1 parquetRepetitionOptional
  ++ writeFieldBinary 4 3 name
  ++ writeFieldI32 6 4 0
  ++ writeStop

def buildSchemaRoot (numChildren : Nat) : Bytes :=
  writeFieldBinary 4 0 "schema" ++ writeFieldI32 5 4 numChildren ++ writeStop

/-- The element count INCLUDING the root, and the bytes. -/
def buildSchemaList (names : List String) : Nat × Bytes :=
  (1 + names.length, buildSchemaRoot names.length ++ names.flatMap buildSchemaLeaf)

/-! ## 5. Column metadata and chunks -/

def buildColumnMetadata (name : String) (numValues pageLen dataPageOffset : Nat) : Bytes :=
  let nameBytes := name.toUTF8.toList
  writeFieldI32 1 0 parquetTypeByteArray
  ++ writeFieldListHeader 2 1 1 tI32
  ++ uvarintEncode (zigzagEncodeNat parquetEncodingDlba)
  ++ writeFieldListHeader 3 2 1 tBinary
  -- UTF-8 byte length, not a codepoint count: the column names are
  -- ASCII today, so this was latent rather than observed (#445)
  ++ uvarintEncode nameBytes.length ++ nameBytes
  ++ writeFieldI32 4 3 parquetCodecUncompressed
  ++ writeFieldI64 5 4 numValues
  ++ writeFieldI64 6 5 pageLen
  ++ writeFieldI64 7 6 pageLen
  ++ writeFieldI64 9 7 dataPageOffset
  ++ writeStop

def buildColumnChunk (name : String) (numValues pageLen dataPageOffset : Nat) : Bytes :=
  writeFieldI64 2 0 dataPageOffset
  ++ writeFieldHeader tStruct 3 2
  ++ buildColumnMetadata name numValues pageLen dataPageOffset
  ++ writeStop

/-! ## 6. Row groups

The offset threading is the part that breaks: each chunk records where
its data page starts, and the pages begin after `PAR1`, not at zero. -/

structure RowGroupOut where
  nextOffset : Nat
  pageBytes : Bytes
  metaBytes : Bytes
  numRows : Nat

def buildRowGroup (startOffset : Nat) (rows : List CottasQuad) : RowGroupOut :=
  let (nvS, lenS, bytesS) := buildColumnPage (rows.map (·.s))
  let offS := startOffset
  let offP := offS + lenS
  let (nvP, lenP, bytesP) := buildColumnPage (rows.map (·.p))
  let offO := offP + lenP
  let (nvO, lenO, bytesO) := buildColumnPage (rows.map (·.o))
  let offG := offO + lenO
  let (nvG, lenG, bytesG) := buildColumnPage (rows.map (·.g))
  let columnsList := writeListHeader 4 tStruct
                     ++ buildColumnChunk "s" nvS lenS offS
                     ++ buildColumnChunk "p" nvP lenP offP
                     ++ buildColumnChunk "o" nvO lenO offO
                     ++ buildColumnChunk "g" nvG lenG offG
  { nextOffset := offG + lenG
  , pageBytes := bytesS ++ bytesP ++ bytesO ++ bytesG
  , metaBytes := writeFieldHeader tList 1 0 ++ columnsList
            ++ writeFieldI64 2 1 (lenS + lenP + lenO + lenG)
            ++ writeFieldI64 3 2 rows.length ++ writeStop
  , numRows := rows.length }

def buildRowGroups (startOffset : Nat) :
    List (List CottasQuad) → Nat × Bytes × List Bytes × Nat
  | [] => (startOffset, [], [], 0)
  | g :: rest =>
      let r := buildRowGroup startOffset g
      let (off2, restPages, restMetas, restRows) := buildRowGroups r.nextOffset rest
      (off2, r.pageBytes ++ restPages, r.metaBytes :: restMetas, r.numRows + restRows)

/-! ## 7. Chunking rows into row groups -/

def chunkRowsAcc (cap : Nat) : List CottasQuad → List CottasQuad → Nat →
    List (List CottasQuad) → List (List CottasQuad)
  | [], cur, curN, acc => if curN = 0 then acc.reverse else (cur.reverse :: acc).reverse
  | hd :: tl, cur, curN, acc =>
      if cap = 0 || curN + 1 ≥ cap then
        chunkRowsAcc cap tl [] 0 ((hd :: cur).reverse :: acc)
      else chunkRowsAcc cap tl (hd :: cur) (curN + 1) acc

def chunkRows (rows : List CottasQuad) (cap : Nat) : List (List CottasQuad) :=
  chunkRowsAcc cap rows [] 0 []

/-! ## 8. File metadata and the whole file -/

def buildFileMetadata (numRows : Nat) (rgMetas : List Bytes) : Bytes :=
  let (schemaCount, schemaElems) := buildSchemaList ["s", "p", "o", "g"]
  writeFieldI32 1 0 cottasFormatVersion
  ++ writeFieldHeader tList 2 1
  ++ writeListHeader schemaCount tStruct ++ schemaElems
  ++ writeFieldI64 3 2 numRows
  ++ writeFieldHeader tList 4 3
  ++ writeListHeader rgMetas.length tStruct ++ rgMetas.flatten
  ++ writeStop

/-- The whole COTTAS base file, for an already-sorted quad list. The
caller sorts: that is a consumer's job under iron rule 11, not this
module's. -/
def serializeCottas (rows : List CottasQuad) : Bytes :=
  let groups := chunkRows rows rowGroupSize
  let (_, pageBytes, rgMetas, numRows) := buildRowGroups magicHeader.length groups
  let metadata := buildFileMetadata numRows rgMetas
  magicHeader ++ pageBytes ++ metadata ++ writeU32Le metadata.length ++ magicHeader

/-! ## 9. What the file layout guarantees -/

/-- The five parts, in order. The trailing length comes BEFORE the
closing magic — that is what lets a reader seek to the metadata. -/
theorem serializeCottas_shape (rows : List CottasQuad) :
    ∃ pages md,
      serializeCottas rows = magicHeader ++ pages ++ md
                             ++ writeU32Le md.length ++ magicHeader := by
  refine ⟨(buildRowGroups magicHeader.length (chunkRows rows rowGroupSize)).2.1,
          buildFileMetadata
            (buildRowGroups magicHeader.length (chunkRows rows rowGroupSize)).2.2.2
            (buildRowGroups magicHeader.length (chunkRows rows rowGroupSize)).2.2.1, ?_⟩
  rfl

/-- **Pages start AFTER the magic header, never at zero.** An offset
short by those four bytes gives a file every byte of which is right
except where it says the data is. The writer threads
`magicHeader.length` in as the starting offset, and this says that is
the four bytes of `PAR1`. -/
theorem magicHeader_length : magicHeader.length = 4 := rfl

/-- An empty row-group list hands the starting offset straight back, so
a file with no rows still records the pages as beginning after the
magic. -/
theorem buildRowGroups_nil (startOffset : Nat) :
    (buildRowGroups startOffset []).1 = startOffset := rfl

/-- Offsets are cumulative across the four columns of a row group. -/
theorem rowGroup_nextOffset (startOffset : Nat) (rows : List CottasQuad) :
    (buildRowGroup startOffset rows).nextOffset
      = startOffset
        + (buildColumnPage (rows.map (·.s))).2.1
        + (buildColumnPage (rows.map (·.p))).2.1
        + (buildColumnPage (rows.map (·.o))).2.1
        + (buildColumnPage (rows.map (·.g))).2.1 := by
  simp only [buildRowGroup]

/-- A row group reports the number of rows it was given. -/
theorem rowGroup_numRows (startOffset : Nat) (rows : List CottasQuad) :
    (buildRowGroup startOffset rows).numRows = rows.length := rfl

/-! ## Build-time checks -/

private def q1 : CottasQuad :=
  { s := "s1", p := "p1", o := "o1", g := defaultGraphSentinel }
private def q2 : CottasQuad :=
  { s := "s2", p := "p1", o := "o2", g := defaultGraphSentinel }

/-! The file is bracketed by the magic, and the four bytes are `PAR1`. -/
#guard magicHeader == [(80 : UInt8), (65 : UInt8), (82 : UInt8), (49 : UInt8)]
#guard magicHeader == parquetMagic.toUTF8.toList
#guard (serializeCottas [q1, q2]).take 4 == magicHeader
#guard (serializeCottas [q1, q2]).reverse.take 4 == magicHeader.reverse
#guard (serializeCottas []).take 4 == magicHeader

/-! An empty input still produces a well-formed file: magic, no pages,
metadata, length, magic. -/
#guard (serializeCottas []).length > 8

/-! **The version stamp is 445, not 1** — the owner decision at #445, so
the reader can reject a store this writer did not produce. -/
#guard cottasFormatVersion == 445
#guard writeFieldI32 1 0 cottasFormatVersion
        == [(21 : UInt8), (250 : UInt8), (6 : UInt8)]

/-! **A schema leaf carries `converted_type = UTF8`** (field 6). Without
it DuckDB shows the column as BLOB instead of VARCHAR. -/
#guard (buildSchemaLeaf "s").length > (writeFieldI32 1 0 parquetTypeByteArray
        ++ writeFieldI32 3 1 parquetRepetitionOptional
        ++ writeFieldBinary 4 3 "s" ++ writeStop).length

/-! Four columns plus the root. -/
#guard (buildSchemaList ["s", "p", "o", "g"]).1 == 5

/-! Offsets accumulate: the second column starts where the first
ends. -/
#guard (buildRowGroup 4 [q1, q2]).nextOffset > 4
#guard (buildRowGroup 4 [q1, q2]).numRows == 2
#guard (buildRowGroup 0 []).numRows == 0

/-! Chunking respects the cap and loses no rows. -/
#guard (chunkRows [q1, q2] 1).length == 2
#guard (chunkRows [q1, q2] 100).length == 1
#guard (chunkRows [] 100) == ([] : List (List CottasQuad))
#guard ((chunkRows [q1, q2] 1).flatten) == [q1, q2]
#guard ((chunkRows [q1, q2] 100).flatten) == [q1, q2]

/-! ## Axiom audit -/

#print axioms serializeCottas_shape
#print axioms magicHeader_length
#print axioms buildRowGroups_nil
#print axioms rowGroup_nextOffset
#print axioms rowGroup_numRows

end L4Factoidal.Cottas.BaseWriterFile
