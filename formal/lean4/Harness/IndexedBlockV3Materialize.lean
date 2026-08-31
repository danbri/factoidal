/- Importable native physical reader for IBK3 predicate-local manifest entries.
   Host I/O is here; the byte layout and range executor remain pure Lean in
   L4Factoidal.Storage.IndexedBlockWireV3. -/
import Harness.PosixRangeIO
import L4Factoidal.Storage.IndexedBlockWireV3
import L4Factoidal.Storage.SubjectRowIndexWire
import L4Factoidal.Storage.ShardManifest

namespace Harness.IndexedBlockV3Materialize

open Harness.PosixRangeIO
open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.Storage.ChunkedArtifact
open L4Factoidal.Storage.ShardManifest
open L4Factoidal.Storage.BlockMerkle
open L4Factoidal.Storage.IndexedBlock

structure Counters where
  requestedBytes : Nat := 0
  fetchedBytes : Nat := 0
  chunks : Nat := 0
  requests : Nat := 0

def addCounters (left right : Counters) : Counters :=
  { requestedBytes := left.requestedBytes + right.requestedBytes
    fetchedBytes := left.fetchedBytes + right.fetchedBytes
    chunks := left.chunks + right.chunks
    requests := left.requests + right.requests }

private def addRead (total : Counters) (read : VerifiedReadFootprint) : Counters :=
  { requestedBytes := total.requestedBytes + read.requestedBytes
    fetchedBytes := total.fetchedBytes + read.fetchedBytes
    chunks := total.chunks + read.chunks
    requests := total.requests + 1 }

structure ScanResult where
  triples : List Triple
  counters : Counters
  artifactBytes : Nat

/-- Manifest artifact keys denote leaf files, never paths supplied by a query.
    Keep the same admission rule as the earlier IBK2 range materializer. -/
def safeLeafKey (key : ArtifactKey) : Bool :=
  !key.value.isEmpty && !(key.value.contains '/') && !(key.value.contains '\\')

private def ioRange (range : L4Factoidal.Storage.IndexedBlockWireV3.ByteRange) :
    L4Factoidal.Storage.IndexedBlockWireV2.ByteRange :=
  { offset := range.offset, length := range.length }

/-- Open a subject-posting sidecar only after all its independent integrity
    boundaries agree: SBM3 extent/SHA-256, fixed-chunk Merkle proof, SRI1
    framing/checksum, and the IBK entry's declared row count. `none` means no
    postings are exposed; a future subject-bound scan must then fail closed or
    use a separately established fallback plan. -/
def subjectPostings? (directory : System.FilePath) (entry : Entry) :
    IO (Option (List (Nat × Nat))) := do
  match entry.subjectIndex with
  | none => pure none
  | some index =>
      if !safeLeafKey index.key then return none
      match index.chunked with
      | none => pure none
      | some ref =>
          let path := (directory / index.key.value).toString
          let leafBytes ← IO.FS.readBinFile (path ++ ".merkle")
          match leaves? ref.chunkCount leafBytes with
          | none => pure none
          | some leaves =>
              let cache ← newVerifiedChunkCache
              let fullRange : L4Factoidal.Storage.IndexedBlockWireV3.ByteRange :=
                { offset := 0, length := index.bytes }
              match ← readVerifiedRangeCached? path ref leaves cache (ioRange fullRange) with
              | none => pure none
              | some (bytes, _) =>
                  if bytes.size != index.bytes ||
                      !L4Factoidal.Storage.BlockArtifact.verify index.sha256 bytes then pure none else
                  match L4Factoidal.Storage.SubjectRowIndexWire.decode bytes with
                  | some (rows, pairs) => if rows == entry.rows then pure (some pairs) else pure none
                  | none => pure none

/-- Restore one ID row through an already admitted complete PTD1 dictionary.
    This is deliberately small and explicit because the SRI1 sidecar names
    row offsets, not RDF values: both the local subject ID and the
    predicate-local invariant are checked before a result reaches SPARQL. -/
private def tripleOfIdRow? (terms : Array Term) (predicate : WfIri) (row : IdTriple) : Option Triple := do
  let subject ← terms[row.s]?
  let actualPredicate ← terms[row.p]?
  let object ← terms[row.o]?
  match subject, actualPredicate with
  | .iri iri, .iri actual =>
      if actual == predicate then some { s := .iri iri, p := actual, o := object } else none
  | .bnode bnode, .iri actual =>
      if actual == predicate then some { s := .bnode bnode, p := actual, o := object } else none
  | _, _ => none

private def appendSubjectOffsets (pairs : List (Nat × Nat)) : List Nat → List (Nat × Nat)
  | [] => []
  | subject :: rest =>
      let current := L4Factoidal.Storage.SubjectRowIndexWire.offsetsFor pairs subject |>.map fun offset => (subject, offset)
      current ++ appendSubjectOffsets pairs rest

private def scanSubjectRows (path : String) (ref : Ref) (leaves : List Digest)
    (cache : IO.Ref (List VerifiedChunk)) (header : L4Factoidal.Storage.IndexedBlockWireV3.Prefix)
    (terms : Array Term) (predicate : WfIri) : List (Nat × Nat) → Counters → IO (Option (List Triple × Counters))
  | [], counters => pure (some ([], counters))
  | (expectedSubject, offset) :: rest, counters => do
      if offset >= header.rowCount then pure none else
      let range : L4Factoidal.Storage.IndexedBlockWireV3.ByteRange :=
        { offset := (L4Factoidal.Storage.IndexedBlockWireV3.rowsRange header).offset +
            offset * L4Factoidal.Storage.IndexedBlockWireV3.rowBytes,
          length := L4Factoidal.Storage.IndexedBlockWireV3.rowBytes }
      match ← readVerifiedRangeCached? path ref leaves cache (ioRange range) with
      | none => pure none
      | some (rowBytes, footprint) =>
          match L4Factoidal.Storage.IndexedBlockWireV3.decodeRowPrefix? rowBytes with
          | some [row] => do
              if row.s != expectedSubject then pure none else
              let later ← scanSubjectRows path ref leaves cache header terms predicate rest (addRead counters footprint)
              match tripleOfIdRow? terms predicate row, later with
              | some triple, some (later, next) => pure (some (triple :: later, next))
              | _, _ => pure none
          | _ => pure none

/-- Select rows for RDF subjects through an admitted SRI1 companion.  The
    current compatibility bridge reads the complete target PTD1 dictionary to
    resolve RDF subjects to the target block's local IDs; it does *not* read
    the block's full row area. A later TLI1 term-to-local-ID companion replaces
    that dictionary read without changing this row-selection contract. -/
def scanEntryForSubjects (directory : System.FilePath) (predicate : WfIri)
    (subjects : List Term) (entry : Entry) : IO (Option ScanResult) := do
  if !safeLeafKey entry.artifact.key then return none
  match entry.artifact.chunked with
  | none => pure none
  | some ref =>
      let path := (directory / entry.artifact.key.value).toString
      let leafBytes ← IO.FS.readBinFile (path ++ ".merkle")
      match leaves? ref.chunkCount leafBytes, ← subjectPostings? directory entry with
      | some leaves, some pairs =>
          let cache ← newVerifiedChunkCache
          let headerRange : L4Factoidal.Storage.IndexedBlockWireV3.ByteRange :=
            { offset := 0, length := L4Factoidal.Storage.IndexedBlockWireV3.prefixBytes }
          match ← readVerifiedRangeCached? path ref leaves cache (ioRange headerRange) with
          | none => pure none
          | some (headerBytes, headerFootprint) =>
              match L4Factoidal.Storage.IndexedBlockWireV3.decodePrefix headerBytes with
              | none => pure none
              | some header =>
                  if header.rowCount != entry.rows then pure none else
                  let dictionaryRange := L4Factoidal.Storage.IndexedBlockWireV3.dictionaryRange header
                  match ← readVerifiedRangeCached? path ref leaves cache (ioRange dictionaryRange) with
                  | none => pure none
                  | some (dictionaryBytes, dictionaryFootprint) =>
                      match L4Factoidal.Storage.PagedTermDictionary.decode? dictionaryBytes with
                      | none => pure none
                      | some terms =>
                          let ids := subjects.filterMap (L4Factoidal.Storage.PagedTermDictionary.findTermId? terms) |>.eraseDups
                          let selected := appendSubjectOffsets pairs ids
                          match ← scanSubjectRows path ref leaves cache header terms predicate selected
                              (addRead (addRead {} headerFootprint) dictionaryFootprint) with
                          | none => pure none
                          | some (triples, counters) =>
                              pure (some { triples, counters, artifactBytes := entry.artifact.bytes })
      | _, _ => pure none

def scanEntriesForSubjects (directory : System.FilePath) (predicate : WfIri) (subjects : List Term) :
    List Entry → List Triple → Counters → Nat → IO (Option (List Triple × Counters × Nat))
  | [], triples, counters, opened => pure (some (triples, counters, opened))
  | entry :: rest, triples, counters, opened => do
      match ← scanEntryForSubjects directory predicate subjects entry with
      | none => pure none
      | some current =>
          scanEntriesForSubjects directory predicate subjects rest (triples ++ current.triples)
            (addCounters counters current.counters) (opened + 1)

private def readPages (path : String) (ref : Ref) (leaves : List Digest)
    (cache : IO.Ref (List VerifiedChunk)) : List L4Factoidal.Storage.IndexedBlockWireV3.ByteRange → Counters →
    IO (Option (List (L4Factoidal.Storage.IndexedBlockWireV3.ByteRange × ByteArray) × Counters))
  | [], total => pure (some ([], total))
  | range :: rest, total => do
      match ← readVerifiedRangeCached? path ref leaves cache (ioRange range) with
      | none => pure none
      | some (bytes, footprint) =>
          match ← readPages path ref leaves cache rest (addRead total footprint) with
          | none => pure none
          | some (tail, counters) => pure (some ((range, bytes) :: tail, counters))

def scanEntry (directory : System.FilePath) (predicate : WfIri) (rowLimit : Nat)
    (entry : Entry) : IO (Option ScanResult) := do
  if !safeLeafKey entry.artifact.key then return none
  match entry.artifact.chunked with
  | none => pure none
  | some ref =>
      let path := (directory / entry.artifact.key.value).toString
      let leafBytes ← IO.FS.readBinFile (path ++ ".merkle")
      match leaves? ref.chunkCount leafBytes with
      | none => pure none
      | some leaves =>
          let cache ← newVerifiedChunkCache
          let headerRange : L4Factoidal.Storage.IndexedBlockWireV3.ByteRange :=
            { offset := 0, length := L4Factoidal.Storage.IndexedBlockWireV3.prefixBytes }
          match ← readVerifiedRangeCached? path ref leaves cache (ioRange headerRange) with
          | some (headerBytes, headerFootprint) =>
              match L4Factoidal.Storage.IndexedBlockWireV3.decodePrefix headerBytes with
              | some header =>
                  if header.rowCount != entry.rows then pure none else
                  match L4Factoidal.Storage.IndexedBlockWireV3.dictionaryPrefixRange header with
                  | some ptdRange =>
                      match ← readVerifiedRangeCached? path ref leaves cache (ioRange ptdRange) with
                      | some (ptdPrefix, ptdFootprint) =>
                          match L4Factoidal.Storage.IndexedBlockWireV3.dictionaryDirectoryRange? header ptdPrefix with
                          | some directoryRange =>
                              match ← readVerifiedRangeCached? path ref leaves cache (ioRange directoryRange) with
                              | some (directoryBytes, directoryFootprint) =>
                                  let wantedRows := min header.rowCount rowLimit
                                  let rowRange := L4Factoidal.Storage.IndexedBlockWireV3.rowsRange header
                                  let rowPrefix : L4Factoidal.Storage.IndexedBlockWireV3.ByteRange :=
                                    { offset := rowRange.offset, length := wantedRows * L4Factoidal.Storage.IndexedBlockWireV3.rowBytes }
                                  match ← readVerifiedRangeCached? path ref leaves cache (ioRange rowPrefix) with
                                  | some (rowBytes, rowFootprint) =>
                                      let initial := addRead (addRead (addRead (addRead {} headerFootprint) ptdFootprint) directoryFootprint) rowFootprint
                                      match L4Factoidal.Storage.IndexedBlockWireV3.dictionaryPagesForRowPrefix? header ptdPrefix directoryBytes rowBytes with
                                      | some ranges =>
                                          match ← readPages path ref leaves cache ranges initial with
                                          | some (pages, counters) =>
                                              match L4Factoidal.Storage.IndexedBlockWireV3.scanRowPrefixPages { p := some predicate }
                                                  headerBytes rowBytes ptdPrefix directoryBytes pages with
                                              | some triples =>
                                                  if triples.length == wantedRows then
                                                    pure (some { triples, counters, artifactBytes := entry.artifact.bytes })
                                                  else pure none
                                              | none => pure none
                                          | none => pure none
                                      | none => pure none
                                  | none => pure none
                              | none => pure none
                          | none => pure none
                      | none => pure none
                  | none => pure none
              | none => pure none
          | none => pure none

def scanEntries (directory : System.FilePath) (predicate : WfIri) (limit : Nat) :
    List Entry → List Triple → Counters → Nat → IO (Option (List Triple × Counters × Nat))
  | [], triples, counters, opened => pure (some (triples, counters, opened))
  | entry :: rest, triples, counters, opened =>
      if triples.length >= limit then pure (some (triples.take limit, counters, opened)) else do
        match ← scanEntry directory predicate (limit - triples.length) entry with
        | none => pure none
        | some result =>
            scanEntries directory predicate limit rest (triples ++ result.triples)
              (addCounters counters result.counters) (opened + 1)

/-- Exact predicate-local cardinality without RDF-row materialisation. It
    verifies all fixed-width rows, confirms that their one shared predicate ID
    denotes the requested IRI through its PTD1 page, and verifies every read
    range against the manifest Merkle commitment. Subject/object pages are not
    needed for this SPARQL `COUNT(*)` physical operator. -/
def countEntry (directory : System.FilePath) (predicate : WfIri) (entry : Entry) :
    IO (Option (Nat × Counters)) := do
  if !safeLeafKey entry.artifact.key then return none
  match entry.artifact.chunked with
  | none => pure none
  | some ref =>
      let path := (directory / entry.artifact.key.value).toString
      let leafBytes ← IO.FS.readBinFile (path ++ ".merkle")
      match leaves? ref.chunkCount leafBytes with
      | none => pure none
      | some leaves =>
          let cache ← newVerifiedChunkCache
          let headerRange : L4Factoidal.Storage.IndexedBlockWireV3.ByteRange :=
            { offset := 0, length := L4Factoidal.Storage.IndexedBlockWireV3.prefixBytes }
          match ← readVerifiedRangeCached? path ref leaves cache (ioRange headerRange) with
          | none => pure none
          | some (headerBytes, headerFootprint) =>
              match L4Factoidal.Storage.IndexedBlockWireV3.decodePrefix headerBytes with
              | none => pure none
              | some header =>
                  if header.rowCount != entry.rows then pure none else
                  match L4Factoidal.Storage.IndexedBlockWireV3.dictionaryPrefixRange header with
                  | none => pure none
                  | some ptdRange =>
                      match ← readVerifiedRangeCached? path ref leaves cache (ioRange ptdRange) with
                      | none => pure none
                      | some (ptdPrefix, ptdFootprint) =>
                          match L4Factoidal.Storage.PagedTermDictionary.decodePrefix ptdPrefix with
                          | none => pure none
                          | some ptdHeader =>
                              if ptdHeader.pageTerms != L4Factoidal.Storage.PagedTermDictionary.defaultPageTerms then pure none else
                              match L4Factoidal.Storage.IndexedBlockWireV3.dictionaryDirectoryRange? header ptdPrefix with
                              | none => pure none
                              | some directoryRange =>
                                  match ← readVerifiedRangeCached? path ref leaves cache (ioRange directoryRange) with
                                  | none => pure none
                                  | some (directoryBytes, directoryFootprint) =>
                                      match L4Factoidal.Storage.PagedTermDictionary.decodeDirectory? ptdHeader directoryBytes with
                                      | none => pure none
                                      | some directory =>
                                          let rowRange := L4Factoidal.Storage.IndexedBlockWireV3.rowsRange header
                                          match ← readVerifiedRangeCached? path ref leaves cache (ioRange rowRange) with
                                          | none => pure none
                                          | some (rowBytes, rowFootprint) =>
                                              match L4Factoidal.Storage.IndexedBlockWireV3.validatedRowPredicate? ptdHeader.termCount rowBytes with
                                              | none => pure none
                                              | some predicateId =>
                                                  match L4Factoidal.Storage.PagedTermDictionary.pageIndex? ptdHeader predicateId,
                                                        L4Factoidal.Storage.PagedTermDictionary.pageRange? ptdHeader directory predicateId with
                                                  | some page, some relative =>
                                                      let absolute : L4Factoidal.Storage.IndexedBlockWireV3.ByteRange :=
                                                        { offset := (L4Factoidal.Storage.IndexedBlockWireV3.dictionaryRange header).offset + relative.offset,
                                                          length := relative.length }
                                                      match ← readVerifiedRangeCached? path ref leaves cache (ioRange absolute) with
                                                      | none => pure none
                                                      | some (pageBytes, pageFootprint) =>
                                                          match L4Factoidal.Storage.PagedTermDictionary.decodePageArray? ptdHeader directory page pageBytes with
                                                          | none => pure none
                                                          | some terms =>
                                                              match terms[predicateId % ptdHeader.pageTerms]? with
                                                              | some (.iri actual) =>
                                                                  if actual == predicate then
                                                                    let initial := addRead (addRead (addRead (addRead {} headerFootprint) ptdFootprint) directoryFootprint) rowFootprint
                                                                    pure (some (header.rowCount, addRead initial pageFootprint))
                                                                  else pure none
                                                              | _ => pure none
                                                  | _, _ => pure none

def countEntries (directory : System.FilePath) (predicate : WfIri) : List Entry → Nat → Counters →
    IO (Option (Nat × Counters))
  | [], count, counters => pure (some (count, counters))
  | entry :: rest, count, counters => do
      match ← countEntry directory predicate entry with
      | none => pure none
      | some (next, current) => countEntries directory predicate rest (count + next) (addCounters counters current)

/-- Materialise every row from the entries selected by a constant-predicate
    physical plan. This is the conservative bridge for the general SPARQL
    evaluator; bounded predicate scans use `scanEntries` directly. -/
def materializeEntries (directory : System.FilePath) : List Entry → IO (Option (List Triple × Counters))
  | [] => pure (some ([], {}))
  | entry :: rest => do
      match ← scanEntry directory entry.predicate entry.rows entry,
          ← materializeEntries directory rest with
      | some current, some (later, counters) =>
          pure (some (current.triples ++ later, addCounters current.counters counters))
      | _, _ => pure none

end Harness.IndexedBlockV3Materialize
