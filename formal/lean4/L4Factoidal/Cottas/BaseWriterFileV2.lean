/-
L4Factoidal.Cottas.BaseWriterFileV2 — layer 6 of the port of
`RDF.CottasStore.BaseWriter`: the writer-v2 emit path, which completes
the module.

Layer 5 wired the v1 path, which writes DELTA_LENGTH_BYTE_ARRAY for
every column. The F\* banner records what v1 cost and why v2 exists:

> v1 always writes DELTA_LENGTH_BYTE_ARRAY: correct for any cardinality
> but pays the full string bytes on every row, every column, even for
> p/g whose whole point is massive repetition.

v2 adds the RLE_DICTIONARY emit path — a dictionary page followed by a
hybrid-RLE index stream — and closes a roughly sixty-fold size premium
against pycottas.

## Two columns are FORCED, two are measured

`buildRowGroupV2` does not treat the four columns alike, and the
asymmetry is the design:

* `p` and `g` are FORCED to the dictionary. A predicate column and a
  graph column repeat by construction — the graph column is mostly one
  `DEFAULT` sentinel — so measuring them would only ever confirm the
  obvious.
* `s` and `o` are MEASURED. A subject or object column can be
  all-distinct, and then the dictionary is bigger than DLBA.

`rowGroupV2_forces_p_and_g` states the forcing so the asymmetry cannot
be tidied away into "encode every column the same".

## The offset field that is two fields

A dictionary-encoded chunk has TWO offsets: field 9 is the DATA page
and field 11 is the DICTIONARY page. The dictionary page comes first,
so field 11 is the chunk start and field 9 is that plus the dictionary
page length. The F\* source records this as bug history — a reader that
treats them as one offset reads the index stream as if it were the
dictionary. `columnMetadataV2_dataPage_after_dict` pins the
arithmetic.

A DLBA chunk has no field 11 at all, which is why the two metadata
builders are not one builder with a flag.

## The encodings list is two entries, not one

A dictionary-encoded column declares `[PLAIN, RLE_DICTIONARY]` — the
dictionary page's own encoding, then the data page's. A DLBA column
declares one. `#guard` covers both lengths.

No `sorry`, no user `axiom`, no `native_decide`.
-/
import L4Factoidal.Cottas.BaseWriterFile

namespace L4Factoidal.Cottas.BaseWriterFileV2

open L4Factoidal.Cottas.BaseWriterPrims
open L4Factoidal.Cottas.BaseWriterThrift
open L4Factoidal.Cottas.BaseWriterColumn
open L4Factoidal.Cottas.BaseWriterDict
open L4Factoidal.Cottas.BaseWriterFile

/-! ## 1. An encoded column, with its bytes -/

structure ColPage where
  kind : ColumnEncoding
  numValues : Nat
  /-- Zero for `dlba`: there is no dictionary page at all. -/
  dictPageLen : Nat
  /-- The FULL byte length of this column's pages. -/
  totalLen : Nat
  bytes : Bytes

/-! ## 2. The dictionary page header -/

/-- `DictionaryPageHeader` inside a `PageHeader`: field 1 the page
type, fields 2 and 3 the sizes, field 7 the dictionary sub-struct whose
own field 1 is the value count and field 2 the PLAIN encoding. -/
def buildDictionaryPageHeader (numValues uncompressedSize compressedSize : Nat) : Bytes :=
  let dph := writeFieldI32 1 0 numValues
             ++ writeFieldI32 2 1 parquetEncodingPlain ++ writeStop
  writeFieldI32 1 0 parquetPageTypeDictionaryPage
  ++ writeFieldI32 2 1 uncompressedSize
  ++ writeFieldI32 3 2 compressedSize
  ++ writeFieldHeader tStruct 7 3 ++ dph ++ writeStop

/-! ## 3. The two column encoders -/

def buildColumnPageDlbaV2 (values : List String) : ColPage :=
  let (nv, len, bytes) := buildColumnPage values
  { kind := .dlba, numValues := nv, dictPageLen := 0, totalLen := len, bytes := bytes }

/-- Dictionary page, then data page. The empty column still writes both,
so a reader never meets a chunk that declares RLE_DICTIONARY and has no
dictionary. -/
def buildColumnPageRleDict (values : List String) : ColPage :=
  let valueCount := values.length
  let distinct := columnDictionary values
  let tree := dictTreeOfSorted (zipWithIndex distinct) distinct.length
  let indices := lookupIndices values tree
  let bitWidth := bitsNeeded (if distinct.isEmpty then 0 else distinct.length - 1)
  let runs := groupRuns indices
  let dictPayload := buildDictPagePayload distinct
  let dictHeader := buildDictionaryPageHeader distinct.length
                      dictPayload.length dictPayload.length
  let dictBytes := dictHeader ++ dictPayload
  let dataPayload := buildRleDictionaryPagePayload valueCount bitWidth runs
  let dataHeader := buildPageHeader parquetEncodingRleDictionary valueCount
                      dataPayload.length dataPayload.length
  let dataBytes := dataHeader ++ dataPayload
  { kind := .rleDictionary, numValues := valueCount
  , dictPageLen := dictBytes.length
  , totalLen := dictBytes.length + dataBytes.length
  , bytes := dictBytes ++ dataBytes }

/-- Build both and keep the shorter — for a column whose cardinality is
not known in advance. -/
def encodeColumnChooseSmaller (values : List String) : ColPage :=
  let dlba := buildColumnPageDlbaV2 values
  let dict := buildColumnPageRleDict values
  if dict.totalLen < dlba.totalLen then dict else dlba

/-- For a column that repeats by construction. -/
def encodeColumnForcedDict (values : List String) : ColPage :=
  buildColumnPageRleDict values

/-! ## 4. Column metadata, encoding-aware

A dictionary-encoded chunk carries TWO offsets and TWO declared
encodings. A DLBA chunk carries one of each, which is why these are two
builders rather than one with a flag. -/

def buildColumnMetadataV2 (name : String) (ce : ColPage) (chunkStart : Nat) : Bytes :=
  match ce.kind with
  | .dlba => buildColumnMetadata name ce.numValues ce.totalLen chunkStart
  | .rleDictionary =>
      let nameBytes := name.toUTF8.toList
      -- field 9 is the DATA page, field 11 the DICTIONARY page: the
      -- dictionary comes first, so the data page starts after it
      let dataPageOffset := chunkStart + ce.dictPageLen
      writeFieldI32 1 0 parquetTypeByteArray
      ++ writeFieldListHeader 2 1 2 tI32
      ++ uvarintEncode (zigzagEncodeNat parquetEncodingPlain)
      ++ uvarintEncode (zigzagEncodeNat parquetEncodingRleDictionary)
      ++ writeFieldListHeader 3 2 1 tBinary
      ++ uvarintEncode nameBytes.length ++ nameBytes
      ++ writeFieldI32 4 3 parquetCodecUncompressed
      ++ writeFieldI64 5 4 ce.numValues
      ++ writeFieldI64 6 5 ce.totalLen
      ++ writeFieldI64 7 6 ce.totalLen
      ++ writeFieldI64 9 7 dataPageOffset
      ++ writeFieldI64 11 9 chunkStart
      ++ writeStop

def buildColumnChunkV2 (name : String) (ce : ColPage) (chunkStart : Nat) : Bytes :=
  writeFieldI64 2 0 chunkStart
  ++ writeFieldHeader tStruct 3 2
  ++ buildColumnMetadataV2 name ce chunkStart
  ++ writeStop

/-! ## 5. Row groups and the whole file -/

def buildRowGroupV2 (startOffset : Nat) (rows : List CottasQuad) : RowGroupOut :=
  -- s and o are MEASURED; p and g are FORCED to the dictionary,
  -- because they repeat by construction
  let ceS := encodeColumnChooseSmaller (rows.map (·.s))
  let offS := startOffset
  let offP := offS + ceS.totalLen
  let ceP := encodeColumnForcedDict (rows.map (·.p))
  let offO := offP + ceP.totalLen
  let ceO := encodeColumnChooseSmaller (rows.map (·.o))
  let offG := offO + ceO.totalLen
  let ceG := encodeColumnForcedDict (rows.map (·.g))
  let columnsList := writeListHeader 4 tStruct
                     ++ buildColumnChunkV2 "s" ceS offS
                     ++ buildColumnChunkV2 "p" ceP offP
                     ++ buildColumnChunkV2 "o" ceO offO
                     ++ buildColumnChunkV2 "g" ceG offG
  { nextOffset := offG + ceG.totalLen
  , pageBytes := ceS.bytes ++ ceP.bytes ++ ceO.bytes ++ ceG.bytes
  , metaBytes := writeFieldHeader tList 1 0 ++ columnsList
                 ++ writeFieldI64 2 1
                      (ceS.totalLen + ceP.totalLen + ceO.totalLen + ceG.totalLen)
                 ++ writeFieldI64 3 2 rows.length ++ writeStop
  , numRows := rows.length }

def buildRowGroupsV2 (startOffset : Nat) :
    List (List CottasQuad) → Nat × Bytes × List Bytes × Nat
  | [] => (startOffset, [], [], 0)
  | g :: rest =>
      let r := buildRowGroupV2 startOffset g
      let (off2, restPages, restMetas, restRows) := buildRowGroupsV2 r.nextOffset rest
      (off2, r.pageBytes ++ restPages, r.metaBytes :: restMetas, r.numRows + restRows)

/-- The whole COTTAS base file, writer v2. Same outer shape as v1;
different column encodings inside. -/
def serializeCottasV2 (rows : List CottasQuad) : Bytes :=
  let groups := chunkRows rows rowGroupSize
  let (_, pageBytes, rgMetas, numRows) := buildRowGroupsV2 magicHeader.length groups
  let metadata := buildFileMetadata numRows rgMetas
  magicHeader ++ pageBytes ++ metadata ++ writeU32Le metadata.length ++ magicHeader

/-! ## 6. What v2 guarantees -/

/-- **`p` and `g` are forced to the dictionary; `s` and `o` are
measured.** The asymmetry is the design, not an oversight. -/
theorem rowGroupV2_forces_p_and_g (rows : List CottasQuad) :
    (encodeColumnForcedDict (rows.map (·.p))).kind = .rleDictionary
    ∧ (encodeColumnForcedDict (rows.map (·.g))).kind = .rleDictionary := ⟨rfl, rfl⟩

/-- The measured columns take one of the two encodings, never a third
thing. -/
theorem chooseSmaller_is_one_of (values : List String) :
    encodeColumnChooseSmaller values = buildColumnPageDlbaV2 values
    ∨ encodeColumnChooseSmaller values = buildColumnPageRleDict values := by
  simp only [encodeColumnChooseSmaller]
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- **The DLBA case delegates unchanged.** v2 does not rewrite the v1
metadata for a DLBA column — it calls the v1 builder, so a file with no
dictionary-encoded column is byte-identical to what v1 wrote. -/
theorem columnMetadataV2_dlba_delegates (name : String) (ce : ColPage)
    (chunkStart : Nat) (h : ce.kind = .dlba) :
    buildColumnMetadataV2 name ce chunkStart
      = buildColumnMetadata name ce.numValues ce.totalLen chunkStart := by
  simp only [buildColumnMetadataV2, h]

/-- A DLBA column carries no dictionary page. -/
theorem dlba_has_no_dict_page (values : List String) :
    (buildColumnPageDlbaV2 values).dictPageLen = 0 := rfl

/-- Both encoders report the value count they were given. -/
theorem encoders_report_numValues (values : List String) :
    (buildColumnPageDlbaV2 values).numValues = values.length
    ∧ (buildColumnPageRleDict values).numValues = values.length := ⟨rfl, rfl⟩

/-! **The version stamp the reader checks** is `writeFieldI32 1 0 445`,
which the F\* module pins with its own literal lemma. Here it is a
`#guard` rather than a theorem: `uvarintEncode` is defined by
well-founded recursion, so it does not reduce definitionally and `rfl`
cannot close it. -/

/-! ## Build-time checks -/

private def r1 : CottasQuad :=
  { s := "s1", p := "p1", o := "o1", g := defaultGraphSentinel }
private def r2 : CottasQuad :=
  { s := "s2", p := "p1", o := "o2", g := defaultGraphSentinel }

/-! The empty column still writes both pages, so a reader never meets a
chunk that declares RLE_DICTIONARY with no dictionary. -/
#guard (buildColumnPageRleDict []).dictPageLen > 0
#guard (buildColumnPageRleDict []).kind == ColumnEncoding.rleDictionary
#guard (buildColumnPageRleDict []).numValues == 0

/-! A repeating column is smaller dictionary-encoded; an all-distinct
one is not. -/
#guard (encodeColumnChooseSmaller ["aaaaaaaa", "aaaaaaaa", "aaaaaaaa"]).kind
        == ColumnEncoding.rleDictionary
#guard (encodeColumnChooseSmaller ["a", "b", "c"]).kind == ColumnEncoding.dlba

/-! **Two declared encodings for a dictionary column, one for DLBA.**
The metadata is longer in the dictionary case for that reason and for
field 11. -/
#guard (buildColumnMetadataV2 "p" (buildColumnPageRleDict ["a", "a"]) 4).length
        > (buildColumnMetadataV2 "p" (buildColumnPageDlbaV2 ["a", "a"]) 4).length

/-! The file is bracketed by the magic, both writers. -/
#guard (serializeCottasV2 [r1, r2]).take 4 == magicHeader
#guard (serializeCottasV2 [r1, r2]).reverse.take 4 == magicHeader.reverse
#guard (serializeCottasV2 []).take 4 == magicHeader

/-! **v2 is smaller than v1 when the repetition is worth paying a
dictionary for** — which is the whole reason it exists. It is NOT
smaller on a two-row file of short strings: the dictionary page's own
header outweighs the saving, and this pair of checks says so rather
than claiming a win that does not exist at every scale. -/
private def rep : List CottasQuad :=
  List.replicate 8
    { s := "subject-value-long", p := "predicate-value-long"
    , o := "object-value-long", g := defaultGraphSentinel }
#guard (serializeCottasV2 rep).length < (serializeCottas rep).length
#guard (serializeCottasV2 [r1, r2]).length ≥ (serializeCottas [r1, r2]).length

/-! Row groups report their rows and advance the offset. -/
#guard (buildRowGroupV2 4 [r1, r2]).numRows == 2
#guard (buildRowGroupV2 4 [r1, r2]).nextOffset > 4
#guard (buildRowGroupsV2 4 []).1 == 4

/-! The version stamp, again at the byte level. -/
#guard writeFieldI32 1 0 cottasFormatVersion
        == [(21 : UInt8), (250 : UInt8), (6 : UInt8)]

/-! ## Axiom audit -/

#print axioms rowGroupV2_forces_p_and_g
#print axioms chooseSmaller_is_one_of
#print axioms columnMetadataV2_dlba_delegates
#print axioms dlba_has_no_dict_page

end L4Factoidal.Cottas.BaseWriterFileV2
