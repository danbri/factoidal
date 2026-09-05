/- What a Shardborough generation must satisfy before it is made visible.

   `Harness/ShardActivate.lean` held these checks and read every artifact
   from a directory. The WebAssembly module has no file system, so the
   `activateVerify` operation of `Wasm/Ops/Pack.lean` must reach the same
   verdict over bytes a JavaScript host supplies. Iron rule 7 of CLAUDE.md
   forbids a second implementation, so the checks live here, once, with no
   `IO` in any signature.

   ## How the bytes arrive

   Every function takes a `Reader m` — a lookup from an artifact name to its
   bytes, in whatever monad the caller has. The native activator passes a
   reader that reads the candidate directory; the wasm operation passes a
   reader over the byte region the host wrote into the module's heap. A
   `none` is a missing, unreadable or refused artifact, and it fails the
   same check whichever caller produced it.

   ## What is checked here, and what is not

   Checked: each artifact's declared byte length, its declared SHA-256, its
   fixed-chunk Merkle leaves and the root over them, and the agreement of
   each index sidecar (SRI2, TLI1, OLI2) with the block it names; for an
   IBK4 generation, each block's row count, its predicate locality and the
   graph set its manifest entry publishes.

   Not checked here: the paged RANGE read of an IBK3 generation, which
   `Harness/IndexedBlockV3Materialize.lean` performs with positioned reads.
   That path re-reads selected byte ranges through the operating system and
   is a property of the native reader, not of the bytes; the leaves and the
   root over the same bytes are checked above, so the commitment itself is
   covered. `Harness/ShardActivate.lean` still runs it.

   No `partial`, no `sorry`, no `native_decide`. -/
import L4Factoidal.Storage.ShardManifest
import L4Factoidal.Storage.ChunkedArtifact
import L4Factoidal.Storage.BlockArtifact
import L4Factoidal.Storage.IndexedBlockWireV3
import L4Factoidal.Storage.IndexedBlockWireV4
import L4Factoidal.Storage.IndexedBlockWireV5
import L4Factoidal.Storage.BlockV5Plan
import L4Factoidal.Storage.SubjectRowIndexWire
import L4Factoidal.Storage.SubjectRowIndexWireV2
import L4Factoidal.Storage.TermLocalIndex
import L4Factoidal.Storage.TermLocalIndexWire
import L4Factoidal.Storage.LiteralGramIndexWire
import L4Factoidal.Storage.GeoBBoxIndexWire

namespace L4Factoidal.Storage.GenerationVerify

open L4Factoidal.RDF
open L4Factoidal.Storage.ShardManifest
open L4Factoidal.Storage.BlockMerkle (Hasher Digest)

/-- The bytes of one named artifact of the generation, or `none` when it is
    missing, unreadable, or refused by the caller. -/
abbrev Reader (m : Type → Type) := String → m (Option ByteArray)

/-- An artifact name must be one child of the generation directory. A native
    reader would otherwise follow a path a manifest chose. -/
def safeLeafKey (key : ArtifactKey) : Bool :=
  !key.value.isEmpty && !(key.value.contains '/') && !(key.value.contains '\\')

/-- Decode raw 32-byte leaf hashes from a packer's `.merkle` sidecar. Their
    authority comes only from a successful root comparison, never from the
    sidecar bytes themselves. -/
def leaves? (expected : Nat) (bytes : ByteArray) : Option (List Digest) :=
  if bytes.size != expected * 32 then none
  else some <| (List.range expected).map fun index =>
    bytes.extract (index * 32) (index * 32 + 32)

/-! ## The full-artifact commitment

Before a generation becomes visible, every child satisfies BOTH independently
recorded commitments over the same observed bytes: the full-file SHA-256 the
manifest declares, and the fixed-chunk Merkle root its `.merkle` sidecar
rebuilds. A hand-crafted manifest whose digest and root describe different
artifacts is refused here rather than at a later query. -/

def verifyFullArtifact [Monad m] (h : Hasher) (read : Reader m) (artifact : ArtifactRef) :
    m Bool := do
  if !safeLeafKey artifact.key then return false
  match artifact.chunked with
  | none => return false
  | some chunks =>
      match ← read artifact.key.value with
      | none => return false
      | some bytes =>
          match ← read (artifact.key.value ++ ".merkle") with
          | none => return false
          | some leafBytes =>
              let rebuilt := L4Factoidal.Storage.ChunkedArtifact.chunksOf chunks.chunkBytes bytes
                |>.map (L4Factoidal.Storage.BlockMerkle.leafWith h)
              match leaves? chunks.chunkCount leafBytes with
              | none => return false
              | some observed =>
                  return bytes.size == artifact.bytes &&
                    L4Factoidal.Storage.BlockArtifact.verifyWith h artifact.sha256 bytes &&
                    observed == rebuilt &&
                    L4Factoidal.Storage.BlockMerkle.rootWith h observed == chunks.root &&
                    L4Factoidal.Storage.ChunkedArtifact.fromChunksWith? h chunks.chunkBytes
                      (L4Factoidal.Storage.ChunkedArtifact.chunksOf chunks.chunkBytes bytes)
                        == some chunks

def verifyFullEntries [Monad m] (h : Hasher) (read : Reader m) : List Entry → m Bool
  | [] => pure true
  | entry :: rest => do
      if !(← verifyFullArtifact h read entry.artifact) then return false
      match entry.literalIndex with
      | some literal => if !(← verifyFullArtifact h read literal) then return false
      | none => pure ()
      match entry.geoIndex with
      | some geo => if !(← verifyFullArtifact h read geo) then return false
      | none => pure ()
      match entry.subjectIndex with
      | none => verifyFullEntries h read rest
      | some index =>
          if !(← verifyFullArtifact h read index) then return false
          else match entry.termIndex with
            | none => verifyFullEntries h read rest
            | some term =>
                if !(← verifyFullArtifact h read term) then return false
                else match entry.objectIndex with
                  | none => verifyFullEntries h read rest
                  | some object =>
                      if !(← verifyFullArtifact h read object) then return false
                      else verifyFullEntries h read rest

/-! ## The index sidecars

Each of the three is part of the generation, not optional query advice. Each
must decode under its own framing and checksum, must be bound by digest to
the exact block of the same manifest entry, and must equal the canonical
relation that block denotes. -/

def subjectIndexFailure : String :=
  "candidate subject-index sidecar is missing, changed, or malformed"
def termIndexFailure : String :=
  "candidate term-index sidecar is missing, changed, malformed, or bound to another block"
def objectIndexFailure : String :=
  "candidate object-index sidecar is missing, changed, malformed, or inconsistent with its block"
def literalIndexFailure : String :=
  "candidate literal-index sidecar is missing, changed, malformed, or bound to another block"
def geoIndexFailure : String :=
  "candidate geometry-index sidecar is missing, changed, malformed, or bound to another block"
def quadEntryFailure : String :=
  "candidate IBK4 artifact is missing, changed, malformed, mislabelled by predicate, or its graph set differs from the manifest entry"

/-- Read and decode one entry's IBK3 artifact. `none` on any read or decode
    failure; the caller turns that into the message of the first sidecar
    check which needed the block. -/
def decodePrimary? [Monad m] (read : Reader m) (entry : Entry) :
    m (Option L4Factoidal.Storage.IndexedBlock.Block) := do
  match ← read entry.artifact.key.value with
  | none => pure none
  | some bytes => pure (L4Factoidal.Storage.IndexedBlockWireV3.decode bytes)

def subjectIndexAgrees [Monad m] (read : Reader m) (entry : Entry) (index : ArtifactRef)
    (block? : Option L4Factoidal.Storage.IndexedBlock.Block) : m Bool := do
  if !safeLeafKey index.key then return false
  match block? with
  | none => return false
  | some block =>
      match ← read index.key.value with
      | none => return false
      | some indexBytes =>
          match L4Factoidal.Storage.SubjectRowIndexWireV2.decode? indexBytes with
          | none => return false
          | some decoded =>
              return decoded.targetIBKSha256 == entry.artifact.sha256 &&
                decoded.rowCount == entry.rows &&
                decoded.pairs.toList ==
                  L4Factoidal.Storage.SubjectRowIndexWire.pairsOfRows block.rows

def termIndexAgrees [Monad m] (read : Reader m) (entry : Entry) (index : ArtifactRef)
    (block? : Option L4Factoidal.Storage.IndexedBlock.Block) : m Bool := do
  if !safeLeafKey index.key then return false
  match block? with
  | none => return false
  | some block =>
      match ← read index.key.value with
      | none => return false
      | some bytes =>
          match L4Factoidal.Storage.TermLocalIndexWire.decode? bytes with
          | none => return false
          | some decoded =>
              return decoded.targetIBKSha256 == entry.artifact.sha256 &&
                decoded.entries == L4Factoidal.Storage.TermLocalIndex.entriesOf block.dict

/-- OLI2 uses SRI2's pageable local-ID/row-offset framing but is separately
    manifest-typed, and must equal the object-to-row relation of its block. -/
def objectIndexAgrees [Monad m] (read : Reader m) (version : Nat) (entry : Entry)
    (index : ArtifactRef) (block? : Option L4Factoidal.Storage.IndexedBlock.Block) : m Bool := do
  if version != 6 || !safeLeafKey index.key then return false
  match block? with
  | none => return false
  | some block =>
      match ← read index.key.value with
      | none => return false
      | some indexBytes =>
          match L4Factoidal.Storage.SubjectRowIndexWireV2.decode? indexBytes with
          | none => return false
          | some decoded =>
              return decoded.targetIBKSha256 == entry.artifact.sha256 &&
                decoded.rowCount == entry.rows &&
                decoded.pairs.toList ==
                  L4Factoidal.Storage.SubjectRowIndexWire.pairsOfObjects block.rows

/-- LGI1, the SBM8 literal search index. What is checked here is that the
    sidecar decodes under its own framing and CRC, that it names THIS block by
    digest, and that it is sized for this block's dictionary.

    The posting lists are NOT recomputed. Building the index of the SKOS
    `skos:prefLabel` block costs 5.6 s, and an activation that rebuilt every
    block's index would pay that per block for a value the manifest already
    commits by SHA-256 and by Merkle root. What that leaves uncaught is a
    PACKER fault which wrote a self-consistent index of the wrong content;
    tampering after the pack is caught by the digest. The consequence of such
    a fault is bounded: the index is a candidate filter and the planner
    re-evaluates the original expression on the candidates, so a wrong index
    can only DROP rows, never add them. Recomputing the postings is open work,
    recorded in `docs/designissues/2026-09-04-literal-token-index.md`. -/
def literalIndexAgrees [Monad m] (read : Reader m) (version : Nat) (entry : Entry)
    (index : ArtifactRef) : m Bool := do
  if (version != 8 && version != 9) || !safeLeafKey index.key then return false
  match ← read entry.artifact.key.value with
  | none => return false
  | some blockBytes =>
      match L4Factoidal.Storage.IndexedBlockWireV4.decode blockBytes with
      | none => return false
      | some block =>
          match ← read index.key.value with
          | none => return false
          | some indexBytes =>
              match L4Factoidal.Storage.LiteralGramIndexWire.decode? indexBytes with
              | none => return false
              | some decoded =>
                  return decoded.targetIBKSha256 == entry.artifact.sha256 &&
                    decoded.index.dictCount == block.dict.size &&
                    decoded.index.literalCount ==
                      block.dict.toList.countP (fun t =>
                        match t with | .literal _ => true | _ => false)

/-- GBI1, the SBM9 geometry bounding-box index. What is checked is what
    `literalIndexAgrees` checks, for the same reason and with the same limit:
    the sidecar decodes under its own framing and CRC, it names THIS block by
    digest, and it is sized for this block's dictionary.

    The boxes are NOT recomputed. Rebuilding the index parses every
    `geo:wktLiteral` in the dictionary again, which is the whole cost the
    index exists to remove, and an activation that paid it per block would
    pay it for a value the manifest already commits by SHA-256 and by Merkle
    root. What that leaves uncaught is a PACKER fault which wrote a
    self-consistent index of the wrong content; tampering after the pack is
    caught by the digest. The consequence is bounded in the same way: the
    index is a candidate filter and the planner re-evaluates the original
    expression on the candidates, so a wrong index can only DROP rows, never
    add them. Recomputing the boxes is open work, recorded in
    `docs/designissues/2026-09-05-geometry-bounding-box-index.md`. -/
def geoIndexAgrees [Monad m] (read : Reader m) (version : Nat) (entry : Entry)
    (index : ArtifactRef) : m Bool := do
  if version != 9 || !safeLeafKey index.key then return false
  match ← read entry.artifact.key.value with
  | none => return false
  | some blockBytes =>
      match L4Factoidal.Storage.IndexedBlockWireV4.decode blockBytes with
      | none => return false
      | some block =>
          match ← read index.key.value with
          | none => return false
          | some indexBytes =>
              match L4Factoidal.Storage.GeoBBoxIndexWire.decode? indexBytes with
              | none => return false
              | some decoded =>
                  return decoded.targetIBKSha256 == entry.artifact.sha256 &&
                    decoded.index.dictCount == block.dict.size

/-- One entry's sidecars, checked in the order subject, term, object, literal,
    geometry
    against ONE read and ONE decode of its IBK3 artifact.

    `legacySubject` decides the SBM4-and-earlier subject index, whose SRI1
    postings the native activator reads through the paged materializer. A
    caller with no such reader passes `fun _ _ => pure false`, which refuses
    a pre-SBM5 generation rather than admitting one it did not check. -/
def verifyEntryIndexes [Monad m] (read : Reader m) (version : Nat)
    (legacySubject : Entry → ArtifactRef → m Bool) (entry : Entry) : m (Option String) := do
  let needsBlock := (entry.subjectIndex.isSome && version >= 5) ||
    entry.termIndex.isSome || entry.objectIndex.isSome
  let block? ← if needsBlock then decodePrimary? read entry else pure none
  let subjectOk ← match entry.subjectIndex with
    | none => pure true
    | some index =>
        if version >= 5 then subjectIndexAgrees read entry index block?
        else legacySubject entry index
  if !subjectOk then return some subjectIndexFailure
  let termOk ← match entry.termIndex with
    | none => pure true
    | some index => termIndexAgrees read entry index block?
  if !termOk then return some termIndexFailure
  let objectOk ← match entry.objectIndex with
    | none => pure true
    | some index => objectIndexAgrees read version entry index block?
  if !objectOk then return some objectIndexFailure
  /- At version 10 the two candidate-filter sidecars are LGI2 and GBI1 over an
     IBK5 block, and both are checked by `verifyQuadV5Entry` against ONE decode
     of that block. Checking them here as well would decode it twice. -/
  let literalOk ← match entry.literalIndex with
    | none => pure true
    | some index =>
        if version == 10 then pure true else literalIndexAgrees read version entry index
  if !literalOk then return some literalIndexFailure
  let geoOk ← match entry.geoIndex with
    | none => pure true
    | some index => if version == 10 then pure true else geoIndexAgrees read version entry index
  if !geoOk then return some geoIndexFailure
  pure none

def verifyIndexSidecars [Monad m] (read : Reader m) (version : Nat)
    (legacySubject : Entry → ArtifactRef → m Bool) : List Entry → m (Option String)
  | [] => pure none
  | entry :: rest => do
      match ← verifyEntryIndexes read version legacySubject entry with
      | some failure => pure (some failure)
      | none => verifyIndexSidecars read version legacySubject rest

/-! ## IBK4 entries

`IndexedBlockWireV4.decode` re-checks the framing, the CRC, the row order,
the predicate locality and the stored header graph-set summary against the
rows it decoded. Three checks are left to the manifest, because only the
manifest makes those claims: the committed row count, the predicate the entry
names, and the entry's copy of the graph set. The third is what keeps
`GRAPH <iri>` entry selection sound — a planner which reads the manifest
summary and never opens the block must not see a graph set the block does
not have. -/

def verifyQuadEntry [Monad m] (read : Reader m) (entry : Entry) : m (Option Nat) := do
  if !safeLeafKey entry.artifact.key then return none
  match ← read entry.artifact.key.value with
  | none => return none
  | some bytes =>
      match L4Factoidal.Storage.IndexedBlockWireV4.decode bytes with
      | none => return none
      | some block =>
          if block.rows.size != entry.rows then return none
          let predicateOk := block.rows.toList.all fun row =>
            match block.dict[row.p]? with
            | some (.iri value) => value == entry.predicate
            | _ => false
          if !predicateOk then return none
          match L4Factoidal.Storage.IndexedBlockWireV4.graphNames? block with
          | none => return none
          | some names =>
              if names.map GraphName.ofGraphRef == entry.graphSet then return some bytes.size
              else return none

def verifyQuadEntries [Monad m] (read : Reader m) : List Entry → Nat → m (Option Nat)
  | [], total => pure (some total)
  | entry :: rest, total => do
      match ← verifyQuadEntry read entry with
      | none => pure none
      | some bytes => verifyQuadEntries read rest (total + bytes)

/-! ## IBK5 entries and the SBM10 blob table

An SBM10 generation is checked by ONE decode of each block, against which every
manifest claim about that block is re-run: the three IBK4-era claims (row
count, predicate, graph set), the two candidate-filter sidecars, the two zone
maps and the blob reference list. Encoder admission equals decoder admission,
so activation recomputes what the packer computed and compares rather than
trusting the sidecar's self-consistency.

The LGI2 and GBI1 postings ARE recomputed here, unlike LGI1 and GBI1 at SBM8
and SBM9, where the note in `literalIndexAgrees` explains what recomputing
would have cost when one block held a whole predicate. Blocks are now cut at
16,384 rows and 2,097,152 estimated bytes
(`docs/designissues/2026-09-04-blocks-per-predicate.md`), so rebuilding one
block's index costs what packing that block cost, and a packer fault that
wrote a self-consistent index of the wrong content is caught rather than
bounded. -/

def blobFailure : String :=
  "candidate blob artifact is missing, changed, misnamed, or of a byte extent no version-2 term states"
def quadV5EntryFailure : String :=
  "candidate IBK5 artifact is missing, changed, malformed, mislabelled by predicate, or its graph set, zone maps, blob references or index sidecars differ from the manifest entry"

/-- Every blob artifact of the manifest: the full-file SHA-256 and the
    fixed-chunk Merkle commitment `verifyFullArtifact` checks for every other
    child, plus the SBM10 naming rule that the hexadecimal in the key is the
    artifact's own digest. -/
def verifyBlobArtifacts [Monad m] (h : Hasher) (read : Reader m) : List ArtifactRef → m Bool
  | [] => pure true
  | blob :: rest => do
      if blob.key.value != blobKeyOf blob.sha256 then return false
      if !(← verifyFullArtifact h read blob) then return false
      verifyBlobArtifacts h read rest

/-- The blob-table members one entry names, in the entry's own order. -/
def resolvedBlobRefs (manifest : Manifest) (entry : Entry) : Option (List ArtifactRef) :=
  entry.blobRefs.mapM fun index => manifest.blobs[index]?

/-- Every out-of-line literal of a decoded dictionary states a byte extent.
    It must equal the extent of the artifact its digest names, so a reader
    that fetches the blob by digest gets the bytes the term describes. -/
def blobExtentsAgree (refs : List ArtifactRef)
    (dict : Array L4Factoidal.Storage.TermWireV2.WireTerm) : Bool :=
  dict.toList.all fun term =>
    match term with
    | .inline _ => true
    | .blob b =>
        match refs.find? (fun ref => ref.sha256.toList == b.sha256.toList) with
        | none => false
        | some ref => ref.bytes == b.byteLength

/-- One SBM10 entry, against one decode of its IBK5 block. -/
def verifyQuadV5Entry [Monad m] (h : Hasher) (read : Reader m) (manifest : Manifest)
    (entry : Entry) : m (Option Nat) := do
  if !safeLeafKey entry.artifact.key then return none
  match ← read entry.artifact.key.value with
  | none => return none
  | some bytes =>
      match L4Factoidal.Storage.IndexedBlockWireV5.decode bytes with
      | none => return none
      | some block =>
          if block.rows.size != entry.rows then return none
          let predicateOk := block.rows.toList.all fun row =>
            match block.dict[row.p]? with
            | some (.inline (.iri value)) => value == entry.predicate
            | _ => false
          if !predicateOk then return none
          match L4Factoidal.Storage.IndexedBlockWireV5.graphNames? block with
          | none => return none
          | some names =>
              if names.map GraphName.ofGraphRef != entry.graphSet then return none
              -- The zone maps: recomputed from the block, compared to the entry.
              match L4Factoidal.Storage.BlockV5Plan.zones? block with
              | none => return none
              | some (subjectZone, objectZone) =>
              if entry.subjectZone != some subjectZone then return none
              if entry.objectZone != some objectZone then return none
              -- The blob reference list: exactly the digests the dictionary names.
              match resolvedBlobRefs manifest entry with
              | none => return none
              | some refs =>
                  if refs.map (fun ref => ref.sha256.toList) !=
                      (L4Factoidal.Storage.IndexedBlockWireV5.blobDigests block).map
                        ByteArray.toList then return none
                  if !blobExtentsAgree refs block.dict then return none
                  -- LGI2 and GBI1, rebuilt from this dictionary.
                  match entry.literalIndex, entry.geoIndex with
                  | some literalRef, some geoRef =>
                      if !safeLeafKey literalRef.key || !safeLeafKey geoRef.key then
                        return none
                      match ← read literalRef.key.value with
                      | none => return none
                      | some literalBytes =>
                          match L4Factoidal.Storage.LiteralGramIndexWire.decode2? literalBytes with
                          | none => return none
                          | some literal =>
                              if literal.targetIBKSha256 != entry.artifact.sha256 then
                                return none
                              if literal.index !=
                                  L4Factoidal.Storage.BlockV5Plan.literalIndexOf block then
                                return none
                              match ← read geoRef.key.value with
                              | none => return none
                              | some geoBytes =>
                                  match L4Factoidal.Storage.GeoBBoxIndexWire.decode? geoBytes with
                                  | none => return none
                                  | some geo =>
                                      if geo.targetIBKSha256 != entry.artifact.sha256 then
                                        return none
                                      if geo.index !=
                                          L4Factoidal.Storage.BlockV5Plan.geoIndexOf block then
                                        return none
                                      return some bytes.size
                  | _, _ => return none

def verifyQuadV5Entries [Monad m] (h : Hasher) (read : Reader m) (manifest : Manifest) :
    List Entry → Nat → m (Option Nat)
  | [], total => pure (some total)
  | entry :: rest, total => do
      match ← verifyQuadV5Entry h read manifest entry with
      | none => pure none
      | some bytes => verifyQuadV5Entries h read manifest rest (total + bytes)

/-! ## IBK3 entries, without positioned reads

The native activator materialises an IBK3 generation through the paged reader,
which re-checks each selected byte range against the committed Merkle leaves.
A caller with no positioned-read facility decodes each block whole — the
leaves and the root over exactly those bytes were already checked by
`verifyFullArtifact` — and holds the manifest to its declared row count. -/

def verifyIbk3Entry [Monad m] (read : Reader m) (entry : Entry) : m (Option Nat) := do
  if !safeLeafKey entry.artifact.key then return none
  match ← read entry.artifact.key.value with
  | none => return none
  | some bytes =>
      match L4Factoidal.Storage.IndexedBlockWireV3.decode bytes with
      | none => return none
      | some block =>
          let rows := L4Factoidal.Storage.IndexedBlock.scanBound
            { p := some entry.predicate } block
          if rows.length == entry.rows then return some bytes.size else return none

def verifyIbk3Entries [Monad m] (read : Reader m) : List Entry → Nat → m (Option Nat)
  | [], total => pure (some total)
  | entry :: rest, total => do
      match ← verifyIbk3Entry read entry with
      | none => pure none
      | some bytes => verifyIbk3Entries read rest (total + bytes)

end L4Factoidal.Storage.GenerationVerify
