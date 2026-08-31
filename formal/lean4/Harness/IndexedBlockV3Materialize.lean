/- Importable native physical reader for IBK3 predicate-local manifest entries.
   Host I/O is here; the byte layout and range executor remain pure Lean in
   L4Factoidal.Storage.IndexedBlockWireV3. -/
import Harness.PosixRangeIO
import L4Factoidal.Storage.IndexedBlockWireV3
import L4Factoidal.Storage.SubjectRowIndexWire
import L4Factoidal.Storage.SubjectRowIndexWireV2
import L4Factoidal.Storage.TermLocalIndex
import L4Factoidal.Storage.TermLocalIndexWire
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

private def tliRange (offset length : Nat) : L4Factoidal.Storage.IndexedBlockWireV3.ByteRange :=
  { offset, length }

/-- Resolve RDF subjects through one TLI1 directory and one checked page per
    distinct term. The result still has to be checked against the target PTD1
    dictionary before a row scan uses it: this makes direct file queries safe
    even if they bypass a prior generation activation. -/
private def decodedTliPage? : List (Nat × Array L4Factoidal.Storage.TermLocalIndex.Entry) → Nat →
    Option (Array L4Factoidal.Storage.TermLocalIndex.Entry)
  | [], _ => none
  | (ordinal, entries) :: rest, wanted =>
      if ordinal == wanted then some entries else decodedTliPage? rest wanted

private def termIdsViaIndex (path : String) (ref : Ref) (leaves : List Digest)
    (cache : IO.Ref (List VerifiedChunk)) (header : L4Factoidal.Storage.TermLocalIndexWire.Prefix)
    (directory : List L4Factoidal.Storage.TermLocalIndexWire.PageRef) : List Term →
    List (Nat × Array L4Factoidal.Storage.TermLocalIndex.Entry) → Counters →
    IO (Option (List (Term × Nat) × Counters))
  | [], _, counters => pure (some ([], counters))
  | subject :: rest, decoded, counters => do
      let key := L4Factoidal.Storage.serializeTerm subject
      match L4Factoidal.Storage.TermLocalIndexWire.pageFor? directory key with
      | none => pure none
      | some (ordinal, page) =>
          let continueWith := fun entries decodedPages nextCounters => do
            let found := L4Factoidal.Storage.TermLocalIndex.lookup? entries subject
            match ← termIdsViaIndex path ref leaves cache header directory rest decodedPages nextCounters with
            | none => pure none
            | some (later, next) =>
                match found with
                | some localId => pure (some ((subject, localId) :: later, next))
                | none => pure (some (later, next))
          match decodedTliPage? decoded ordinal with
          | some entries => continueWith entries decoded counters
          | none =>
              let range := tliRange
                (L4Factoidal.Storage.TermLocalIndexWire.prefixBytes + header.directoryBytes + page.offset) page.length
              match ← readVerifiedRangeCached? path ref leaves cache (ioRange range) with
              | none => pure none
              | some (pageBytes, footprint) =>
                  match L4Factoidal.Storage.TermLocalIndexWire.decodePage? header ordinal page pageBytes with
                  | none => pure none
                  | some entries => continueWith entries ((ordinal, entries) :: decoded) (addRead counters footprint)

private def subjectIdsViaTli? (directory : System.FilePath) (entry : Entry) (subjects : List Term) :
    IO (Option (List (Term × Nat) × Counters)) := do
  match entry.termIndex with
  | none => pure none
  | some index =>
      if !safeLeafKey index.key then pure none else
      match index.chunked with
      | none => pure none
      | some ref =>
          let path := (directory / index.key.value).toString
          let leafBytes ← IO.FS.readBinFile (path ++ ".merkle")
          match leaves? ref.chunkCount leafBytes with
          | none => pure none
          | some leaves =>
              let cache ← newVerifiedChunkCache
              match ← readVerifiedRangeCached? path ref leaves cache
                  (ioRange (tliRange 0 L4Factoidal.Storage.TermLocalIndexWire.prefixBytes)) with
              | none => pure none
              | some (prefixBytes, prefixFootprint) =>
                  match L4Factoidal.Storage.TermLocalIndexWire.decodePrefix? prefixBytes with
                  | none => pure none
                  | some header =>
                      if header.targetIBKSha256 != entry.artifact.sha256 then pure none else
                      match ← readVerifiedRangeCached? path ref leaves cache
                          (ioRange (tliRange L4Factoidal.Storage.TermLocalIndexWire.prefixBytes header.directoryBytes)) with
                      | none => pure none
                      | some (directoryBytes, directoryFootprint) =>
                          match L4Factoidal.Storage.TermLocalIndexWire.decodeDirectory? header directoryBytes with
                          | none => pure none
                          | some refs =>
                              termIdsViaIndex path ref leaves cache header refs subjects []
                                (addRead (addRead {} prefixFootprint) directoryFootprint)

/-- Open a subject-posting sidecar only after all its independent integrity
    boundaries agree: SBM3 extent/SHA-256, fixed-chunk Merkle proof, SRI1
    framing/checksum, and the IBK entry's declared row count. `none` means no
    postings are exposed; a future subject-bound scan must then fail closed or
    use a separately established fallback plan. -/
private def subjectPostingsWithCounters? (directory : System.FilePath) (entry : Entry) :
    IO (Option (List (Nat × Nat) × Counters)) := do
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
              | some (bytes, footprint) =>
                  if bytes.size != index.bytes ||
                      !L4Factoidal.Storage.BlockArtifact.verify index.sha256 bytes then pure none else
                  match L4Factoidal.Storage.SubjectRowIndexWire.decode bytes with
                  | some (rows, pairs) =>
                      if rows == entry.rows then pure (some (pairs, addRead {} footprint)) else pure none
                  | none => pure none

/-- Compatibility opener for activation's full SRI1 admission. Query paths
    use the counted variant above so an SRI1 sidecar's full verified read is
    never omitted from benchmark counters. -/
def subjectPostings? (directory : System.FilePath) (entry : Entry) :
    IO (Option (List (Nat × Nat))) := do
  match ← subjectPostingsWithCounters? directory entry with
  | some (pairs, _) => pure (some pairs)
  | none => pure none

/-- Distinct SRI2 page references potentially containing any requested local
    subject ID. `SRI2.pagesFor` intentionally returns more than one page when
    a posting list crosses a page boundary; deduplication stops repeated query
    bindings from rereading a page. -/
private def sri2CandidatePages : List L4Factoidal.Storage.SubjectRowIndexWireV2.PageRef →
    List Nat → List (Nat × L4Factoidal.Storage.SubjectRowIndexWireV2.PageRef)
  | refs, ids => ids.flatMap (L4Factoidal.Storage.SubjectRowIndexWireV2.pagesFor refs) |>.eraseDups

private def readSRI2Pages (path : String) (ref : Ref) (leaves : List Digest)
    (cache : IO.Ref (List VerifiedChunk)) (header : L4Factoidal.Storage.SubjectRowIndexWireV2.Prefix) :
    List (Nat × L4Factoidal.Storage.SubjectRowIndexWireV2.PageRef) → Counters →
    IO (Option (List (Nat × Array (Nat × Nat)) × Counters))
  | [], counters => pure (some ([], counters))
  | (ordinal, page) :: rest, counters => do
      let range := tliRange
        (L4Factoidal.Storage.SubjectRowIndexWireV2.prefixBytes + header.directoryBytes + page.offset) page.length
      match ← readVerifiedRangeCached? path ref leaves cache (ioRange range) with
      | none => pure none
      | some (bytes, footprint) =>
          match L4Factoidal.Storage.SubjectRowIndexWireV2.decodePage? header ordinal page bytes,
              ← readSRI2Pages path ref leaves cache header rest (addRead counters footprint) with
          | some pairs, some (later, next) => pure (some ((ordinal, pairs) :: later, next))
          | _, _ => pure none

private def sri2SelectedPostings (wanted : List Nat) :
    List (Nat × Array (Nat × Nat)) → List (Nat × Nat)
  | [] => []
  | (_, pairs) :: rest =>
      pairs.toList.filter (fun pair => wanted.contains pair.1) ++ sri2SelectedPostings wanted rest

/-- Read SRI2 as a verified range object: prefix, directory and only pages
    whose inclusive subject range can contain a requested local ID.  This is
    deliberately a separate interface until SBM5 commits an SRI2 artifact in
    `Entry`; callers supply that prospective sidecar explicitly. Its Merkle
    root authenticates the fetched ranges, while the header binds them to the
    exact IBK3 artifact whose rows will be read next. -/
def subjectPostingsV2For? (directory : System.FilePath) (entry : Entry)
    (index : ArtifactRef) (subjects : List Nat) : IO (Option (List (Nat × Nat) × Counters)) := do
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
          match ← readVerifiedRangeCached? path ref leaves cache
              (ioRange (tliRange 0 L4Factoidal.Storage.SubjectRowIndexWireV2.prefixBytes)) with
          | none => pure none
          | some (prefixBytes, prefixFootprint) =>
              match L4Factoidal.Storage.SubjectRowIndexWireV2.decodePrefix? prefixBytes with
              | none => pure none
              | some header =>
                  if header.targetIBKSha256 != entry.artifact.sha256 || header.rowCount != entry.rows then pure none else
                  match ← readVerifiedRangeCached? path ref leaves cache
                      (ioRange (tliRange L4Factoidal.Storage.SubjectRowIndexWireV2.prefixBytes header.directoryBytes)) with
                  | none => pure none
                  | some (directoryBytes, directoryFootprint) =>
                      match L4Factoidal.Storage.SubjectRowIndexWireV2.decodeDirectory? header directoryBytes with
                      | none => pure none
                      | some directory =>
                          let wanted := subjects.eraseDups
                          let pages := sri2CandidatePages directory wanted
                          let initial := addRead (addRead {} prefixFootprint) directoryFootprint
                          match ← readSRI2Pages path ref leaves cache header pages initial with
                          | none => pure none
                          | some (decoded, counters) =>
                              pure (some (sri2SelectedPostings wanted decoded, counters))

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

private def indexedTermsAgree (terms : Array Term) : List (Term × Nat) → Bool
  | [] => true
  | (term, localId) :: rest => terms[localId]? == some term && indexedTermsAgree terms rest

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

/-- Fetch exactly the SRI1-selected fixed-width rows before deciding which
    PTD1 term pages are required to render them as RDF. -/
private def scanSubjectIdRows (path : String) (ref : Ref) (leaves : List Digest)
    (cache : IO.Ref (List VerifiedChunk)) (header : L4Factoidal.Storage.IndexedBlockWireV3.Prefix) :
    List (Nat × Nat) → Counters → IO (Option (List L4Factoidal.Storage.IndexedBlock.IdTriple × Counters))
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
          | some [row] =>
              if row.s != expectedSubject then pure none else
              match ← scanSubjectIdRows path ref leaves cache header rest (addRead counters footprint) with
              | some (later, next) => pure (some (row :: later, next))
              | none => pure none
          | _ => pure none

private def rowTermIds (rows : List L4Factoidal.Storage.IndexedBlock.IdTriple) : List Nat :=
  rows.flatMap fun row => [row.s, row.p, row.o]

private def distinctPtdPages (header : L4Factoidal.Storage.PagedTermDictionary.Prefix) :
    List Nat → List Nat → Option (List Nat)
  | [], seen => some seen.reverse
  | termId :: rest, seen =>
      match L4Factoidal.Storage.PagedTermDictionary.pageIndex? header termId with
      | none => none
      | some page =>
          if seen.contains page then distinctPtdPages header rest seen
          else distinctPtdPages header rest (page :: seen)

private def readSparsePtdPages (path : String) (ref : Ref) (leaves : List Digest)
    (cache : IO.Ref (List VerifiedChunk)) (ibkHeader : L4Factoidal.Storage.IndexedBlockWireV3.Prefix)
    (ptdHeader : L4Factoidal.Storage.PagedTermDictionary.Prefix)
    (directory : List L4Factoidal.Storage.PagedTermDictionary.PageEntry) : List Nat → Counters →
    IO (Option (List (Nat × Array Term) × Counters))
  | [], counters => pure (some ([], counters))
  | page :: rest, counters => do
      let firstTerm := page * ptdHeader.pageTerms
      match L4Factoidal.Storage.PagedTermDictionary.pageRange? ptdHeader directory firstTerm with
      | none => pure none
      | some relative =>
          let range : L4Factoidal.Storage.IndexedBlockWireV3.ByteRange :=
            { offset := (L4Factoidal.Storage.IndexedBlockWireV3.dictionaryRange ibkHeader).offset + relative.offset,
              length := relative.length }
          match ← readVerifiedRangeCached? path ref leaves cache (ioRange range) with
          | none => pure none
          | some (bytes, footprint) =>
              match L4Factoidal.Storage.PagedTermDictionary.decodePageArray? ptdHeader directory page bytes,
                  ← readSparsePtdPages path ref leaves cache ibkHeader ptdHeader directory rest (addRead counters footprint) with
              | some terms, some (later, next) => pure (some ((page, terms) :: later, next))
              | _, _ => pure none

private def sparseTerm? (ptdHeader : L4Factoidal.Storage.PagedTermDictionary.Prefix) :
    List (Nat × Array Term) → Nat → Option Term
  | [], _ => none
  | (page, terms) :: rest, termId =>
      if termId / ptdHeader.pageTerms == page then terms[termId % ptdHeader.pageTerms]?
      else sparseTerm? ptdHeader rest termId

private def sparseRowsToTriples? (ptdHeader : L4Factoidal.Storage.PagedTermDictionary.Prefix)
    (pages : List (Nat × Array Term)) (predicate : WfIri) :
    List L4Factoidal.Storage.IndexedBlock.IdTriple → Option (List Triple)
  | [] => some []
  | row :: rest => do
      let subject ← sparseTerm? ptdHeader pages row.s
      let actualPredicate ← sparseTerm? ptdHeader pages row.p
      let object ← sparseTerm? ptdHeader pages row.o
      let later ← sparseRowsToTriples? ptdHeader pages predicate rest
      match subject, actualPredicate with
      | .iri iri, .iri actual => if actual == predicate then some ({ s := .iri iri, p := actual, o := object } :: later) else none
      | .bnode bnode, .iri actual => if actual == predicate then some ({ s := .bnode bnode, p := actual, o := object } :: later) else none
      | _, _ => none

private def sparseIndexedTermsAgree (ptdHeader : L4Factoidal.Storage.PagedTermDictionary.Prefix)
    (pages : List (Nat × Array Term)) : List (Term × Nat) → Bool
  | [] => true
  | (term, localId) :: rest => sparseTerm? ptdHeader pages localId == some term &&
      sparseIndexedTermsAgree ptdHeader pages rest

/-- Select rows for RDF subjects through an admitted SRI1 companion. SBM4
    uses TLI1's prefix, directory and selected pages to obtain local subject
    IDs; PTD1 is still opened to reconstruct RDF output terms and it verifies
    every TLI1 local-ID mapping before any row offsets are trusted. Older
    SBM3 stores retain the complete-PTD1 compatibility bridge. -/
def scanEntryForSubjects (directory : System.FilePath) (predicate : WfIri)
    (subjects : List Term) (entry : Entry) : IO (Option ScanResult) := do
  if !safeLeafKey entry.artifact.key then return none
  match entry.artifact.chunked with
  | none => pure none
  | some ref =>
      let path := (directory / entry.artifact.key.value).toString
      let leafBytes ← IO.FS.readBinFile (path ++ ".merkle")
      match leaves? ref.chunkCount leafBytes, ← subjectPostingsWithCounters? directory entry with
      | some leaves, some (pairs, sriCounters) =>
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
                  match entry.termIndex with
                  | none =>
                      match ← readVerifiedRangeCached? path ref leaves cache (ioRange dictionaryRange) with
                      | none => pure none
                      | some (dictionaryBytes, dictionaryFootprint) =>
                          match L4Factoidal.Storage.PagedTermDictionary.decode? dictionaryBytes with
                          | none => pure none
                          | some terms =>
                              let ids := subjects.filterMap (L4Factoidal.Storage.PagedTermDictionary.findTermId? terms) |>.eraseDups
                              let selected := appendSubjectOffsets pairs ids
                              match ← scanSubjectRows path ref leaves cache header terms predicate selected
                                  (addRead (addRead sriCounters headerFootprint) dictionaryFootprint) with
                              | none => pure none
                              | some (triples, counters) =>
                                  pure (some { triples, counters, artifactBytes := entry.artifact.bytes })
                  | some _ =>
                      match ← subjectIdsViaTli? directory entry subjects with
                      | none => pure none
                      | some (indexed, indexCounters) =>
                          if indexed.isEmpty then
                            pure (some { triples := [], counters := addCounters (addRead {} headerFootprint) indexCounters,
                                         artifactBytes := entry.artifact.bytes })
                          else
                            let ids := indexed.map Prod.snd |>.eraseDups
                            let selected := appendSubjectOffsets pairs ids
                            let initial := addRead (addCounters sriCounters indexCounters) headerFootprint
                            match ← scanSubjectIdRows path ref leaves cache header selected initial with
                            | none => pure none
                            | some (rows, rowCounters) =>
                                match L4Factoidal.Storage.IndexedBlockWireV3.dictionaryPrefixRange header with
                                | none => pure none
                                | some ptdPrefixRange =>
                                    match ← readVerifiedRangeCached? path ref leaves cache (ioRange ptdPrefixRange) with
                                    | none => pure none
                                    | some (ptdPrefixBytes, ptdPrefixFootprint) =>
                                        match L4Factoidal.Storage.PagedTermDictionary.decodePrefix ptdPrefixBytes,
                                            L4Factoidal.Storage.IndexedBlockWireV3.dictionaryDirectoryRange? header ptdPrefixBytes with
                                        | some ptdHeader, some directoryRange =>
                                            match ← readVerifiedRangeCached? path ref leaves cache (ioRange directoryRange) with
                                            | none => pure none
                                            | some (directoryBytes, directoryFootprint) =>
                                                match L4Factoidal.Storage.PagedTermDictionary.decodeDirectory? ptdHeader directoryBytes with
                                                | none => pure none
                                                | some ptdDirectory =>
                                                    let requiredIds := rowTermIds rows ++ indexed.map Prod.snd
                                                    match distinctPtdPages ptdHeader requiredIds [] with
                                                    | none => pure none
                                                    | some pages =>
                                                        let beforePages := addRead (addRead rowCounters ptdPrefixFootprint) directoryFootprint
                                                        match ← readSparsePtdPages path ref leaves cache header ptdHeader ptdDirectory pages beforePages with
                                                        | none => pure none
                                                        | some (decodedPages, counters) =>
                                                            if !sparseIndexedTermsAgree ptdHeader decodedPages indexed then pure none else
                                                            match sparseRowsToTriples? ptdHeader decodedPages predicate rows with
                                                            | some triples => pure (some { triples, counters, artifactBytes := entry.artifact.bytes })
                                                            | none => pure none
                                        | _, _ => pure none
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

/-- SBM5 SRI2 counterpart to `scanEntryForSubjects`.  The only planner change
    is the subject-posting source: terms are first resolved with the committed
    TLI1, then SRI2 provides verified pages for those local IDs. The fixed-row
    and sparse PTD1 checks remain exactly the same as the established SBM4
    path. -/
def scanEntryForSubjectsV2 (directory : System.FilePath) (predicate : WfIri)
    (subjects : List Term) (entry : Entry) : IO (Option ScanResult) := do
  if !safeLeafKey entry.artifact.key then return none
  match entry.artifact.chunked, entry.termIndex, entry.subjectIndex with
  | some ref, some _, some subjectIndex =>
      let path := (directory / entry.artifact.key.value).toString
      let leafBytes ← IO.FS.readBinFile (path ++ ".merkle")
      match leaves? ref.chunkCount leafBytes, ← subjectIdsViaTli? directory entry subjects with
      | some leaves, some (indexed, termCounters) =>
          if indexed.isEmpty then
            pure (some { triples := [], counters := termCounters, artifactBytes := entry.artifact.bytes })
          else
            let ids := indexed.map Prod.snd |>.eraseDups
            match ← subjectPostingsV2For? directory entry subjectIndex ids with
            | none => pure none
            | some (selected, sriCounters) =>
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
                        let initial := addCounters (addCounters termCounters sriCounters) (addRead {} headerFootprint)
                        match ← scanSubjectIdRows path ref leaves cache header selected initial with
                        | none => pure none
                        | some (rows, rowCounters) =>
                            match L4Factoidal.Storage.IndexedBlockWireV3.dictionaryPrefixRange header with
                            | none => pure none
                            | some ptdPrefixRange =>
                                match ← readVerifiedRangeCached? path ref leaves cache (ioRange ptdPrefixRange) with
                                | none => pure none
                                | some (ptdPrefixBytes, ptdPrefixFootprint) =>
                                    match L4Factoidal.Storage.PagedTermDictionary.decodePrefix ptdPrefixBytes,
                                        L4Factoidal.Storage.IndexedBlockWireV3.dictionaryDirectoryRange? header ptdPrefixBytes with
                                    | some ptdHeader, some directoryRange =>
                                        match ← readVerifiedRangeCached? path ref leaves cache (ioRange directoryRange) with
                                        | none => pure none
                                        | some (directoryBytes, directoryFootprint) =>
                                            match L4Factoidal.Storage.PagedTermDictionary.decodeDirectory? ptdHeader directoryBytes with
                                            | none => pure none
                                            | some ptdDirectory =>
                                                let requiredIds := rowTermIds rows ++ indexed.map Prod.snd
                                                match distinctPtdPages ptdHeader requiredIds [] with
                                                | none => pure none
                                                | some pages =>
                                                    let beforePages := addRead (addRead rowCounters ptdPrefixFootprint) directoryFootprint
                                                    match ← readSparsePtdPages path ref leaves cache header ptdHeader ptdDirectory pages beforePages with
                                                    | none => pure none
                                                    | some (decodedPages, counters) =>
                                                        if !sparseIndexedTermsAgree ptdHeader decodedPages indexed then pure none else
                                                        match sparseRowsToTriples? ptdHeader decodedPages predicate rows with
                                                        | some triples => pure (some { triples, counters, artifactBytes := entry.artifact.bytes })
                                                        | none => pure none
                                    | _, _ => pure none
      | _, _ => pure none
  | _, _, _ => pure none

def scanEntriesForSubjectsV2 (directory : System.FilePath) (predicate : WfIri) (subjects : List Term) :
    List Entry → List Triple → Counters → Nat → IO (Option (List Triple × Counters × Nat))
  | [], triples, counters, opened => pure (some (triples, counters, opened))
  | entry :: rest, triples, counters, opened => do
      match ← scanEntryForSubjectsV2 directory predicate subjects entry with
      | none => pure none
      | some current =>
          scanEntriesForSubjectsV2 directory predicate subjects rest (triples ++ current.triples)
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
