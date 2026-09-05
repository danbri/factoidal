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
import L4Factoidal.Storage.SubjectRowIndexWire
import L4Factoidal.Storage.SubjectRowIndexWireV2
import L4Factoidal.Storage.TermLocalIndex
import L4Factoidal.Storage.TermLocalIndexWire
import L4Factoidal.Storage.LiteralGramIndexWire

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
  if version != 8 || !safeLeafKey index.key then return false
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

/-- One entry's sidecars, checked in the order subject, term, object, literal
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
  let literalOk ← match entry.literalIndex with
    | none => pure true
    | some index => literalIndexAgrees read version entry index
  if !literalOk then return some literalIndexFailure
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
