/- Versioned logical manifest for a Shardborough collection of independently
   decodable block artifacts.  This is deliberately separate from host I/O. -/
import L4Factoidal.Crypto.SHA2
import L4Factoidal.Storage.BlockArtifact
import L4Factoidal.Storage.ChunkedArtifact
import L4Factoidal.Storage.IndexedBlockWireV2
import L4Factoidal.SPARQL.Query

namespace L4Factoidal.Storage.ShardManifest

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.SPARQL.StoreBackend

/-- `'SBM0'` in little-endian form: Shardborough Manifest, layout zero. -/
def magic : UInt32 := 0x304D4253
def wireVersion0 : UInt8 := 0
def wireVersion1 : UInt8 := 1
def wireVersion2 : UInt8 := 2
def wireVersion3 : UInt8 := 3
def wireVersion4 : UInt8 := 4

private def byteArrayOfList (xs : List UInt8) : ByteArray := ByteArray.mk xs.toArray
private def listOfByteArray (bs : ByteArray) : List UInt8 := bs.data.toList

/-- Length-prefixed UTF-8.  Lengths in this first portable format are u32
    byte counts, never Lean character counts. -/
private def encodeString (s : String) : List UInt8 :=
  let bytes := s.toUTF8.toList
  writeU32LE (UInt32.ofNat bytes.length) ++ bytes

private def decodeString (bytes : List UInt8) : Option (String × List UInt8) := do
  let length ← readU32LE bytes 0
  let body := (bytes.drop 4).take length.toNat
  if body.length != length.toNat then none
  else do
    let value ← String.fromUTF8? ⟨body.toArray⟩
    some (value, (bytes.drop 4).drop length.toNat)

private def takeExact (n : Nat) (bytes : List UInt8) : Option (List UInt8 × List UInt8) :=
  let value := bytes.take n
  if value.length == n then some (value, bytes.drop n) else none

/-- A relative artifact key.  Host integrations decide whether this denotes a
    file, `bytea`, TiKV value, OPFS entry, or mapped byte range. -/
structure ArtifactKey where
  value : String
  deriving DecidableEq

/-- Identity and required byte extent of one immutable local block. -/
structure ArtifactRef where
  key : ArtifactKey
  bytes : Nat
  sha256 : ByteArray
  /-- Present and mandatory for SBM1. SBM0 deliberately has no range-proof
      claim, so this remains absent in its byte-compatible layout. -/
  chunked : Option ChunkedArtifact.Ref := none
  deriving DecidableEq

/-- One predicate-local IBK2 block. SBM0/SBM1 admit one entry per predicate;
    SBM2 permits several bounded immutable blocks for one predicate. -/
structure Entry where
  predicate : WfIri
  artifact : ArtifactRef
  /-- Present and mandatory for SBM3. This independently committed SRI1
      object maps this artifact's local subject IDs to source-row offsets. -/
  subjectIndex : Option ArtifactRef := none
  /-- Present and mandatory for SBM4. This independently committed TLI1
      object maps canonical RDF-term bytes to this IBK3 artifact's local
      dictionary IDs. -/
  termIndex : Option ArtifactRef := none
  rows : Nat
  ordinal : Nat
  deriving DecidableEq

/-- Metadata that makes a derived collection reproducible rather than an
    anonymous cache. -/
structure Manifest where
  version : Nat
  sourceIdentity : ByteArray
  termRegistryVersion : String
  layout : String
  entries : List Entry
  deriving DecidableEq

def uniquePredicates : List Entry → Bool
  | [] => true
  | entry :: rest => !(rest.map Entry.predicate).contains entry.predicate && uniquePredicates rest

def contiguousOrdinals : List Entry → Nat → Bool
  | [], _ => true
  | entry :: rest, expected => entry.ordinal == expected && contiguousOrdinals rest (expected + 1)

/-- No immutable artifact key may play two manifest roles.  In particular an
    SBM3 subject-index sidecar cannot alias another block or sidecar. -/
def uniqueArtifactKeys (entries : List Entry) : Bool :=
  let keys := entries.flatMap fun entry =>
    entry.artifact.key :: (entry.subjectIndex.map ArtifactRef.key).toList ++
      (entry.termIndex.map ArtifactRef.key).toList
  keys.length == keys.eraseDups.length

/-- Structural acceptance before any host artifact is opened. -/
private def artifactValidFor (version : Nat) (artifact : ArtifactRef) : Bool :=
  artifact.bytes > 0 && artifact.sha256.size == 32 &&
    match version, artifact.chunked with
    | 0, none => true
    | 1, some chunked => ChunkedArtifact.valid chunked && chunked.totalBytes == artifact.bytes
    | 2, some chunked => ChunkedArtifact.valid chunked && chunked.totalBytes == artifact.bytes
    | 3, some chunked => ChunkedArtifact.valid chunked && chunked.totalBytes == artifact.bytes
    | 4, some chunked => ChunkedArtifact.valid chunked && chunked.totalBytes == artifact.bytes
    | _, _ => false

def valid (manifest : Manifest) : Bool :=
  (manifest.version == 0 || manifest.version == 1 || manifest.version == 2 || manifest.version == 3 || manifest.version == 4) &&
    (if manifest.version < 2 then uniquePredicates manifest.entries else true) &&
    uniqueArtifactKeys manifest.entries &&
    contiguousOrdinals manifest.entries 0 &&
    manifest.entries.all fun entry => entry.rows > 0 && artifactValidFor manifest.version entry.artifact &&
      match manifest.version, entry.subjectIndex with
      | 3, some index => artifactValidFor 3 index && index.key != entry.artifact.key
      | 4, some index => artifactValidFor 4 index && index.key != entry.artifact.key
      | 0, none | 1, none | 2, none => true
      | _, _ => false
    && match manifest.version, entry.termIndex with
      | 4, some index => artifactValidFor 4 index && index.key != entry.artifact.key
      | 0, none | 1, none | 2, none | 3, none => true
      | _, _ => false

/-- SBM1 and later retain the fixed-chunk Merkle commitment required by the
range-backed local-file and remote readers. -/
def rangeCommitted (manifest : Manifest) : Bool :=
  manifest.version == 1 || manifest.version == 2 || manifest.version == 3 || manifest.version == 4

/-- Predicate selection is total and deterministic; a missing key means no
    candidate artifact, never a fallback that could hide an index error. -/
def select? (manifest : Manifest) (predicate : WfIri) : Option Entry :=
  if valid manifest then manifest.entries.find? fun entry => entry.predicate == predicate else none

/-- All committed blocks for a predicate, in manifest order. -/
def selectAll (manifest : Manifest) (predicate : WfIri) : List Entry :=
  if valid manifest then manifest.entries.filter fun entry => entry.predicate == predicate else []

/-- A host supplies bytes by relative artifact key.  Keeping this interface
    pure is what lets files, mmap, `bytea`, TiKV values, OPFS and WASM buffers
    share the same integrity-before-decode contract. -/
abbrev Reader := ArtifactKey → Option ByteArray

/-- Check the manifest's immutable child-artifact commitment before allowing
    any IBK2 parser to inspect those bytes. -/
def verifyEntry (entry : Entry) (bytes : ByteArray) : Bool :=
  bytes.size == entry.artifact.bytes &&
    L4Factoidal.Storage.BlockArtifact.verify entry.artifact.sha256 bytes

/-- Open a manifest child only after its declared extent and SHA-256 match.
    `none` deliberately conflates unavailable, substituted and malformed
    artifacts at this low-level boundary; hosts can attach richer diagnostics
    without weakening the acceptance rule. -/
def openVerified? (reader : Reader) (entry : Entry) : Option IndexedBlockWireV2.OpenBlock := do
  let bytes ← reader entry.artifact.key
  if verifyEntry entry bytes then do
    let block ← IndexedBlockWireV2.open? bytes
    /- `rows` is executable planning metadata only after it agrees with both
       the decoded row count and the declared predicate-local segment. This
       prevents a well-formed but incorrectly labelled manifest from feeding
       an unsound "exact" cardinality to the SPARQL join planner. -/
    if block.decoded.rows.size == entry.rows &&
        (IndexedBlockWireV2.scanBoundRange { p := some entry.predicate } block).length == entry.rows
    then some block else none
  else none

/-- The first executable Shardborough read: choose exactly the committed
    predicate-local artifact, verify it, then run the established IBK2
    selective scan.  No unlisted artifact and no full-manifest fallback is
    consulted. -/
def scanPredicate? (reader : Reader) (manifest : Manifest) (predicate : WfIri) : Option (List Triple) := do
  let entries := selectAll manifest predicate
  if entries.isEmpty then none else do
  let blocks ← entries.mapM fun entry => do
    let block ← openVerified? reader entry
    some (entry, block)
  some (blocks.flatMap fun (_, block) => IndexedBlockWireV2.scanBoundRange { p := some predicate } block)

/-- A Shardborough collection whose manifest and every child artifact have
    been accepted.  This eager opener is the correctness-first reference;
    later range/lazy variants must preserve its observable `readOps` results. -/
structure OpenStore where
  manifest : Manifest
  blocks : List (Entry × IndexedBlockWireV2.OpenBlock)

private def openEntries? (reader : Reader) : List Entry → Option (List (Entry × IndexedBlockWireV2.OpenBlock))
  | [] => some []
  | entry :: rest => do
      let block ← openVerified? reader entry
      let opened ← openEntries? reader rest
      some ((entry, block) :: opened)

/-- Verify and open every manifest child.  Failure is atomic at the API level:
    callers receive no partially trusted store. -/
def openStore? (reader : Reader) (manifest : Manifest) : Option OpenStore := do
  if !valid manifest then none else do
  let blocks ← openEntries? reader manifest.entries
  some { manifest, blocks }

/-- The manifest entries needed for a set of predicate-bound scans.  The order
    remains manifest order rather than query order, and duplicate predicates
    do not cause a block to be opened twice.  A predicate missing from the
    manifest deliberately contributes no entry: its backend search is empty,
    which is the same result as searching the complete store. -/
def entriesForPredicates (manifest : Manifest) (predicates : List WfIri) : List Entry :=
  manifest.entries.filter fun entry => predicates.contains entry.predicate

/-- Open only the manifest children selected by an already-established
    predicate-bound plan.  This is not a general replacement for `openStore?`:
    an unbound backend search over this store would be incomplete.  The query
    planner guard below exposes it only for native pattern shapes where every
    backend request has a syntactically constant predicate. -/
def openStoreForPredicates? (reader : Reader) (manifest : Manifest)
    (predicates : List WfIri) : Option OpenStore := do
  if !valid manifest then none else do
  let blocks ← openEntries? reader (entriesForPredicates manifest predicates)
  some { manifest, blocks }

/-- The total physical scan behind the existing SPARQL backend seam.  A
    predicate-bound request touches exactly its committed child; unbound scans
    are the reference concatenation over manifest order until a source-order
    / graph-aware layout is introduced. -/
def scanBound (bound : PatternBound) (store : OpenStore) : List Triple :=
  match bound.p with
  | some predicate =>
      store.blocks.filter (fun pair => pair.1.predicate == predicate) |>.flatMap
        fun (_, block) => IndexedBlockWireV2.scanBoundRange bound block
  | none => store.blocks.flatMap fun (_, block) => IndexedBlockWireV2.scanBoundRange bound block

/-- A predicate-local SBM0 entry has an exact admitted row count for an
    otherwise unbound triple pattern. More selective bounds still scan, so the
    planner never mistakes an upper bound for an exact estimate. -/
def estimateBound (bound : PatternBound) (store : OpenStore) : Nat :=
  match bound.s, bound.p, bound.o with
  | none, some predicate, none =>
      store.blocks.foldl (fun total pair =>
        if pair.1.predicate == predicate then total + pair.1.rows else total) 0
  | _, _, _ => (scanBound bound store).length

/-- Ordinary parsed SPARQL reaches the manifested physical collection through
    precisely the same `BackendReadOps` interface as Cottas, HDT and IBK2. -/
def readOps (store : OpenStore) : BackendReadOps :=
  { search := fun bound => scanBound bound store
  , estimate := fun bound => estimateBound bound store
  , predicatePresent := fun predicate => !(scanBound { p := some predicate } store).isEmpty }

/-- Conservative syntactic admission test for the selective manifest opener.
    It accepts only evaluator-native pattern forms whose triple patterns all
    carry a constant IRI predicate.  Filter, OPTIONAL, property paths, graph
    clauses, SERVICE and sub-SELECT deliberately return `none`: those forms
    can materialise the active backend or introduce a nested pattern, so the
    complete-store opener remains the sound default until they receive their
    own planning proof. -/
def nativeConstantPredicates? : QueryPattern → Option (List WfIri)
  | .bgp patterns =>
      patterns.foldr (fun pattern rest => do
        let predicates ← rest
        match pattern.p with
        | .iri predicate => some (predicate :: predicates)
        | _ => none) (some [])
  | .join left right
  | .union left right
  | .minus left right => do
      let l ← nativeConstantPredicates? left
      let r ← nativeConstantPredicates? right
      some (l ++ r)
  | .filter condition pattern =>
      if condition.backendLocal then nativeConstantPredicates? pattern else none
  | .empty => some []
  | _ => none

/-- The query-level form of `nativeConstantPredicates?`.  It is a planner
    capability, not a semantic shortcut: `none` means "open the full
    manifest", never "return no answers". -/
def queryNativeConstantPredicates? (query : Query) : Option (List WfIri) :=
  nativeConstantPredicates? query.pattern

/-- The field widths in SBM0.  Oversized manifests are refused rather than
    being truncated into an ambiguous byte stream. -/
private def fitsU32 (n : Nat) : Bool := n < 4294967296

private def encodableEntry (version : Nat) (entry : Entry) : Bool :=
  fitsU32 entry.predicate.val.toUTF8.size && fitsU32 entry.artifact.key.value.toUTF8.size &&
    fitsU32 entry.artifact.bytes && fitsU32 entry.rows && fitsU32 entry.ordinal &&
    entry.artifact.sha256.size == 32 &&
    match version, entry.artifact.chunked with
    | 0, none => true
    | 1, some chunked => fitsU32 chunked.chunkBytes && fitsU32 chunked.chunkCount && chunked.root.size == 32
    | 2, some chunked => fitsU32 chunked.chunkBytes && fitsU32 chunked.chunkCount && chunked.root.size == 32
    | 3, some chunked => fitsU32 chunked.chunkBytes && fitsU32 chunked.chunkCount && chunked.root.size == 32
    | 4, some chunked => fitsU32 chunked.chunkBytes && fitsU32 chunked.chunkCount && chunked.root.size == 32
    | _, _ => false
  && match version, entry.subjectIndex with
    | 3, some index | 4, some index => fitsU32 index.key.value.toUTF8.size && fitsU32 index.bytes && index.sha256.size == 32 &&
        match index.chunked with
        | some chunked => fitsU32 chunked.chunkBytes && fitsU32 chunked.chunkCount && chunked.root.size == 32
        | none => false
    | 0, none | 1, none | 2, none => true
    | _, _ => false
  && match version, entry.termIndex with
    | 4, some index => fitsU32 index.key.value.toUTF8.size && fitsU32 index.bytes && index.sha256.size == 32 &&
        match index.chunked with
        | some chunked => fitsU32 chunked.chunkBytes && fitsU32 chunked.chunkCount && chunked.root.size == 32
        | none => false
    | 0, none | 1, none | 2, none | 3, none => true
    | _, _ => false

private def encodable (manifest : Manifest) : Bool :=
  fitsU32 manifest.sourceIdentity.size && fitsU32 manifest.termRegistryVersion.toUTF8.size &&
    fitsU32 manifest.layout.toUTF8.size && fitsU32 manifest.entries.length &&
    manifest.entries.all (encodableEntry manifest.version)

private def encodeEntry (version : Nat) (entry : Entry) : List UInt8 :=
  let common := encodeString entry.predicate.val ++ encodeString entry.artifact.key.value ++
    writeU32LE (UInt32.ofNat entry.artifact.bytes) ++ entry.artifact.sha256.toList ++
    writeU32LE (UInt32.ofNat entry.rows) ++ writeU32LE (UInt32.ofNat entry.ordinal)
  match version, entry.artifact.chunked with
  | 0, none => common
  | 1, some chunked => common ++ writeU32LE (UInt32.ofNat chunked.chunkBytes) ++
      writeU32LE (UInt32.ofNat chunked.chunkCount) ++ chunked.root.toList
  | 2, some chunked => common ++ writeU32LE (UInt32.ofNat chunked.chunkBytes) ++
      writeU32LE (UInt32.ofNat chunked.chunkCount) ++ chunked.root.toList
  | 3, some chunked | 4, some chunked =>
      let primary := common ++ writeU32LE (UInt32.ofNat chunked.chunkBytes) ++
        writeU32LE (UInt32.ofNat chunked.chunkCount) ++ chunked.root.toList
      let encodeSidecar := fun index => match index.chunked with
        | some indexChunks => encodeString index.key.value ++ writeU32LE (UInt32.ofNat index.bytes) ++
            index.sha256.toList ++ writeU32LE (UInt32.ofNat indexChunks.chunkBytes) ++
            writeU32LE (UInt32.ofNat indexChunks.chunkCount) ++ indexChunks.root.toList
        | none => []
      match version, entry.subjectIndex, entry.termIndex with
      | 3, some subject, none => primary ++ encodeSidecar subject
      | 4, some subject, some term => primary ++ encodeSidecar subject ++ encodeSidecar term
      | _, _, _ => []
  | _, _ => []

/-- Canonical SBM0/SBM1/SBM2 bytes. SBM1 and SBM2 retain every SBM0 field and
    append a fixed chunk-policy/root commitment to each artifact entry. -/
def encode? (manifest : Manifest) : Option ByteArray :=
  if valid manifest && encodable manifest then
    some <| byteArrayOfList <|
      writeU32LE magic ++ [UInt8.ofNat manifest.version] ++
      writeU32LE (UInt32.ofNat manifest.sourceIdentity.size) ++ manifest.sourceIdentity.toList ++
      encodeString manifest.termRegistryVersion ++ encodeString manifest.layout ++
      writeU32LE (UInt32.ofNat manifest.entries.length) ++ manifest.entries.flatMap (encodeEntry manifest.version)
  else none

private def decodeEntry (version : Nat) (bytes : List UInt8) : Option (Entry × List UInt8) := do
  let (predicateText, afterPredicate) ← decodeString bytes
  let (keyText, afterKey) ← decodeString afterPredicate
  let artifactBytes ← readU32LE afterKey 0
  let (digest, afterDigest) ← takeExact 32 (afterKey.drop 4)
  let rows ← readU32LE afterDigest 0
  let ordinal ← readU32LE afterDigest 4
  let afterCommon := afterDigest.drop 8
  let chunked ← match version with
    | 0 => some none
    | 1 => do
      let chunkBytes ← readU32LE afterCommon 0
      let chunkCount ← readU32LE afterCommon 4
      let (root, _) ← takeExact 32 (afterCommon.drop 8)
      some (some { totalBytes := artifactBytes.toNat, chunkBytes := chunkBytes.toNat,
                   chunkCount := chunkCount.toNat, root := byteArrayOfList root })
    | 2 => do
      let chunkBytes ← readU32LE afterCommon 0
      let chunkCount ← readU32LE afterCommon 4
      let (root, _) ← takeExact 32 (afterCommon.drop 8)
      some (some { totalBytes := artifactBytes.toNat, chunkBytes := chunkBytes.toNat,
                   chunkCount := chunkCount.toNat, root := byteArrayOfList root })
    | 3 | 4 => do
      let chunkBytes ← readU32LE afterCommon 0
      let chunkCount ← readU32LE afterCommon 4
      let (root, _) ← takeExact 32 (afterCommon.drop 8)
      some (some { totalBytes := artifactBytes.toNat, chunkBytes := chunkBytes.toNat,
                   chunkCount := chunkCount.toNat, root := byteArrayOfList root })
    | _ => none
  let rest := match version with
    | 0 => afterCommon
    | 1 => afterCommon.drop 40
    | 2 => afterCommon.drop 40
    | 3 | 4 => afterCommon.drop 40
    | _ => afterCommon
  if h : isIri predicateText then
    let subjectIndex ← match version with
      | 3 | 4 => do
          let (indexKey, afterKey) ← decodeString rest
          let indexBytes ← readU32LE afterKey 0
          let (indexDigest, afterDigest) ← takeExact 32 (afterKey.drop 4)
          let indexChunkBytes ← readU32LE afterDigest 0
          let indexChunkCount ← readU32LE afterDigest 4
          let (indexRoot, afterRoot) ← takeExact 32 (afterDigest.drop 8)
          let indexChunked : ChunkedArtifact.Ref :=
            { totalBytes := indexBytes.toNat, chunkBytes := indexChunkBytes.toNat,
              chunkCount := indexChunkCount.toNat, root := byteArrayOfList indexRoot }
          let indexRef : ArtifactRef :=
            { key := { value := indexKey }, bytes := indexBytes.toNat,
              sha256 := byteArrayOfList indexDigest,
              chunked := some indexChunked }
          some (some indexRef, afterRoot)
      | _ => some (none, rest)
    let termIndex ← match version with
      | 4 => do
          let (indexKey, afterKey) ← decodeString subjectIndex.2
          let indexBytes ← readU32LE afterKey 0
          let (indexDigest, afterDigest) ← takeExact 32 (afterKey.drop 4)
          let indexChunkBytes ← readU32LE afterDigest 0
          let indexChunkCount ← readU32LE afterDigest 4
          let (indexRoot, afterRoot) ← takeExact 32 (afterDigest.drop 8)
          some (some { key := { value := indexKey }, bytes := indexBytes.toNat,
                       sha256 := byteArrayOfList indexDigest,
                       chunked := some { totalBytes := indexBytes.toNat, chunkBytes := indexChunkBytes.toNat,
                                         chunkCount := indexChunkCount.toNat, root := byteArrayOfList indexRoot } }, afterRoot)
      | _ => some (none, subjectIndex.2)
    some
      ({ predicate := ⟨predicateText, h⟩
         artifact := { key := { value := keyText }, bytes := artifactBytes.toNat,
                       sha256 := byteArrayOfList digest, chunked }
         subjectIndex := subjectIndex.1
         termIndex := termIndex.1
         rows := rows.toNat
         ordinal := ordinal.toNat }, termIndex.2)
  else none

private def decodeEntries (version : Nat) : Nat → List UInt8 → Option (List Entry × List UInt8)
  | 0, bytes => some ([], bytes)
  | n + 1, bytes => do
      let (entry, afterEntry) ← decodeEntry version bytes
      let (entries, rest) ← decodeEntries version n afterEntry
      some (entry :: entries, rest)

/-- Strict SBM0/SBM1/SBM2 decoding. A decoder refuses bad framing, unknown versions,
    invalid UTF-8/IRIs, trailing bytes and structurally invalid manifests. -/
def decode? (bytes : ByteArray) : Option Manifest := do
  let allBytes := listOfByteArray bytes
  let foundMagic ← readU32LE allBytes 0
  if foundMagic != magic then none else do
  let (foundVersion, afterVersion) ← parseU8 (allBytes.drop 4)
  if foundVersion != wireVersion0 && foundVersion != wireVersion1 && foundVersion != wireVersion2 && foundVersion != wireVersion3 && foundVersion != wireVersion4 then none else do
  let sourceLength ← readU32LE afterVersion 0
  let (sourceIdentity, afterSource) ← takeExact sourceLength.toNat (afterVersion.drop 4)
  let (termRegistryVersion, afterRegistry) ← decodeString afterSource
  let (layout, afterLayout) ← decodeString afterRegistry
  let entryCount ← readU32LE afterLayout 0
  let (entries, rest) ← decodeEntries foundVersion.toNat entryCount.toNat (afterLayout.drop 4)
  let manifest := { version := foundVersion.toNat, sourceIdentity := byteArrayOfList sourceIdentity,
                    termRegistryVersion, layout, entries }
  if rest.isEmpty && valid manifest then some manifest else none

private def samplePredicate : WfIri := ⟨"https://example.test/p", by decide⟩
private def sampleSubject : Subject := .iri ⟨"https://example.test/s", by decide⟩
private def sampleObject : Term := .iri ⟨"https://example.test/o", by decide⟩
private def sampleBlock : IndexedBlock.Block :=
  IndexedBlock.fromGraph [{ s := sampleSubject, p := samplePredicate, o := sampleObject }]
private def sampleBlockBytes : ByteArray :=
  (IndexedBlockWireV2.encode? sampleBlock).getD ByteArray.empty
private def sampleDigest : ByteArray := L4Factoidal.Crypto.sha256 sampleBlockBytes
private def sampleManifest : Manifest :=
  { version := 0, sourceIdentity := ByteArray.mk #[1, 2, 3], termRegistryVersion := "terms-v0",
    layout := "predicate-ibk2-v0",
    entries := [{ predicate := samplePredicate,
                  artifact := { key := { value := "blocks/p.ibk2" }, bytes := sampleBlockBytes.size,
                                sha256 := sampleDigest }, rows := 1, ordinal := 0 }] }
private def sampleReader (key : ArtifactKey) : Option ByteArray :=
  if key.value == "blocks/p.ibk2" then some sampleBlockBytes else none

private def sampleChunked : ChunkedArtifact.Ref :=
  match ChunkedArtifact.fromChunks? 64 (ChunkedArtifact.chunksOf 64 sampleBlockBytes) with
  | some ref => ref
  | none => { totalBytes := 1, chunkBytes := 1, chunkCount := 1, root := ByteArray.empty }

private def sampleManifestV1 : Manifest :=
  match sampleManifest.entries with
  | entry :: _ =>
      { { sampleManifest with version := 1 } with
        entries := [{ entry with artifact := { entry.artifact with chunked := some sampleChunked } }] }
  | [] => sampleManifest

/-- SBM2 keeps SBM1's range commitment but permits several committed blocks
for one predicate, which is the bounded-publication shape a spooler needs. -/
private def sampleManifestV2 : Manifest :=
  match sampleManifestV1.entries with
  | entry :: _ =>
      { { sampleManifestV1 with version := 2, layout := "predicate-ibk2-merkle-v2" } with
        entries := [entry, { entry with artifact := { entry.artifact with key := { value := "blocks/p-1.ibk2" } }, ordinal := 1 }] }
  | [] => sampleManifestV1

private def sampleManifestV3 : Manifest :=
  match sampleManifestV1.entries with
  | entry :: _ =>
      let index : ArtifactRef :=
        { key := { value := "blocks/p.sri1" }, bytes := sampleBlockBytes.size,
          sha256 := sampleDigest, chunked := some sampleChunked }
      { { sampleManifestV1 with version := 3, layout := "predicate-ibk3-sri1-merkle-v0" } with
        entries := [{ entry with subjectIndex := some index }] }
  | [] => sampleManifestV1

private def sampleManifestV3MissingIndex : Manifest :=
  { sampleManifestV3 with entries := sampleManifestV3.entries.map fun entry =>
    { entry with subjectIndex := none } }

private def sampleManifestV4 : Manifest :=
  match sampleManifestV3.entries with
  | entry :: _ =>
      let index : ArtifactRef :=
        { key := { value := "blocks/p.tli1" }, bytes := sampleBlockBytes.size,
          sha256 := sampleDigest, chunked := some sampleChunked }
      { { sampleManifestV3 with version := 4, layout := "predicate-ibk3-ptd1-sri1-tli1-merkle-v0" } with
        entries := [{ entry with termIndex := some index }] }
  | [] => sampleManifestV3

private def sampleReaderV2 (key : ArtifactKey) : Option ByteArray :=
  if key.value == "blocks/p.ibk2" || key.value == "blocks/p-1.ibk2" then some sampleBlockBytes else none

/-- This remains structurally valid and carries the right artifact digest, but
    its planning cardinality is a lie. Admission must reject it rather than
    allowing an exact-estimate shortcut to influence join ordering. -/
private def sampleManifestWrongRows : Manifest :=
  match sampleManifest.entries with
  | entry :: _ => { sampleManifest with entries := [{ entry with rows := 2 }] }
  | [] => sampleManifest

#guard decode? (encode? sampleManifest |>.getD ByteArray.empty) == some sampleManifest
#guard decode? (encode? sampleManifestV1 |>.getD ByteArray.empty) == some sampleManifestV1
#guard decode? (encode? sampleManifestV2 |>.getD ByteArray.empty) == some sampleManifestV2
#guard decode? (encode? sampleManifestV3 |>.getD ByteArray.empty) == some sampleManifestV3
#guard decode? (encode? sampleManifestV4 |>.getD ByteArray.empty) == some sampleManifestV4
#guard !(valid sampleManifestV3MissingIndex)
#guard (encode? sampleManifestV3MissingIndex).isNone
#guard (decode? (ByteArray.mk #[83, 66, 77, 48, 1])).isNone
#guard (scanPredicate? sampleReader sampleManifest samplePredicate).map List.length == some 1
#guard (scanPredicate? sampleReaderV2 sampleManifestV2 samplePredicate).map List.length == some 2
#guard (openStore? sampleReader sampleManifest).map
  (fun store => estimateBound { p := some samplePredicate } store) == some 1
#guard (openStore? sampleReaderV2 sampleManifestV2).map
  (fun store => estimateBound { p := some samplePredicate } store) == some 2
#guard (openStore? sampleReader sampleManifestWrongRows).isNone
#guard (scanPredicate? (fun _ => some ByteArray.empty) sampleManifest samplePredicate).isNone
#guard (openStore? sampleReader sampleManifest).map (fun store =>
  (readOps store).search { p := some samplePredicate } |>.length) == some 1
#guard (openStore? sampleReaderV2 sampleManifestV2).map (fun store =>
  (readOps store).search { p := some samplePredicate } |>.length) == some 2
#guard (openStoreForPredicates? sampleReader sampleManifest [samplePredicate]).map
  (fun store => store.blocks.length) == some 1
#guard queryNativeConstantPredicates?
  (mkQuery (.select .all) (.bgp [{ s := .var "s", p := .iri samplePredicate, o := .var "o" }]))
  == some [samplePredicate]
#guard (nativeConstantPredicates? (.filter (.boolLit true)
  (.bgp [{ s := .var "s", p := .iri samplePredicate, o := .var "o" }]))
  == some [samplePredicate])
#guard (nativeConstantPredicates? (.filter (.existsPat .empty)
  (.bgp [{ s := .var "s", p := .iri samplePredicate, o := .var "o" }]))).isNone

end L4Factoidal.Storage.ShardManifest
