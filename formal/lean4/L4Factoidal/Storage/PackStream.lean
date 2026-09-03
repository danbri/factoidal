/- The Shardborough packer as a pure fold.

   `Harness/PredicateShardPack.lean` used to interleave the two bounded
   passes with `IO.FS.writeBinFile`. Nothing in the packer needs a file
   system: the fold state is small and bounded, and every output is a name
   and a byte string. This module holds that fold with no `IO` in any
   signature, so the same code runs behind the native CLI and inside the
   WebAssembly module, where there is no file I/O by build decision
   (`Wasm/build-wasm.sh` omits libuv).

   ## The hash is a parameter

   Leaves and artifact digests are taken with a `BlockMerkle.Hasher` passed
   in by the caller. The native harness passes `Harness.nativeHasher`
   (HACL* extracted C); a wasm or interpreter caller passes
   `BlockMerkle.pureHasher`. The committed bytes are identical either way —
   the two hashers agree on every input, which `lake exe l4vc-probe`
   measures in its `sha256 differential` section. This module must NOT
   import `Harness.*`: the verified library does not depend on an extern
   for its own semantics.

   The source-file identity below is separate and always the pure
   incremental `Sha256Stream`, which has no streaming HACL* counterpart. -/
import L4Factoidal.Storage.PredicateBlocks
import L4Factoidal.Storage.IndexedBlockWireV2
import L4Factoidal.Storage.IndexedBlockWireV3
import L4Factoidal.Storage.SubjectRowIndexWire
import L4Factoidal.Storage.SubjectRowIndexWireV2
import L4Factoidal.Storage.TermLocalIndex
import L4Factoidal.Storage.TermLocalIndexWire
import L4Factoidal.Storage.ShardManifest
import L4Factoidal.Storage.ChunkedArtifact
import L4Factoidal.Syntax.Turtle
import L4Factoidal.Syntax.Utf8Stream
import L4Factoidal.Syntax.TurtleChunkFold
import L4Factoidal.Crypto.SHA2

namespace L4Factoidal.Storage.PackStream

open L4Factoidal.Syntax
open L4Factoidal.Storage.PredicateBlocks
open L4Factoidal.Storage.ShardManifest
open L4Factoidal.Storage.ChunkedArtifact
open L4Factoidal.Storage.BlockMerkle (Hasher)
open L4Factoidal.Crypto

/-- One immutable output of the packer: the name it takes inside the
    generation directory, and its bytes. A host writes it to a file; the
    wasm entry layer hands it back through the blob region. -/
structure Artifact where
  name : String
  bytes : ByteArray

def chunkBytes : Nat := 65536

/-- Keep decoding latency small while publishing roughly four MiB batches.
    This is a bounded first block-sizing policy; later compaction may use
    measured encoded-byte targets rather than source-byte batches. -/
def publicationChunkCount : Nat := 64

inductive PackFormat where
  | ibk2
  | ibk3
  | ibk4
  deriving Repr, DecidableEq

def artifactName : PackFormat → Nat → String
  | .ibk2, ordinal => s!"predicate-{ordinal}.ibk2"
  | .ibk3, ordinal => s!"predicate-{ordinal}.ibk3"
  | .ibk4, ordinal => s!"predicate-{ordinal}.ibk4"

def layoutName : PackFormat → String
  | .ibk2 => "predicate-ibk2-merkle-v2-streaming"
  | .ibk3 => "predicate-ibk3-ptd1-sri2-tli1-oli2-merkle-v0"
  | .ibk4 => "quad-ibk4-ptd1-merkle-v0"

def registryVersion : PackFormat → String
  | .ibk2 => "local-ibk2-dict-v0"
  | .ibk3 => "local-ibk3-ptd1-v0"
  | .ibk4 => "local-ibk4-ptd1-v0"

def manifestVersion : PackFormat → Nat
  | .ibk2 => 2
  | .ibk3 => 6
  | .ibk4 => 7

def encodeBlock? : PackFormat → L4Factoidal.Storage.IndexedBlock.Block → Option ByteArray
  | .ibk2, block => L4Factoidal.Storage.IndexedBlockWireV2.encode? block
  | .ibk3, block => L4Factoidal.Storage.IndexedBlockWireV3.encode? block
  | .ibk4, _ => none

/-- The fixed-chunk Merkle leaves of one artifact, as its `.merkle`
    sidecar. This was `writeMerkle`; it returns the bytes instead of
    writing them. -/
def merkleArtifact (h : Hasher) (name : String) (bytes : ByteArray) : Artifact :=
  let leaves := (chunksOf chunkBytes bytes).map (L4Factoidal.Storage.BlockMerkle.leafWith h)
  { name := name ++ ".merkle"
    bytes := ByteArray.mk (leaves.flatMap (fun value => value.data.toList) |>.toArray) }

def artifactRef? (h : Hasher) (name : String) (bytes : ByteArray) : Option ArtifactRef := do
  let chunked ← fromChunksWith? h chunkBytes (chunksOf chunkBytes bytes)
  some { key := { value := name }, bytes := bytes.size, sha256 := h.digest bytes,
         chunked := some chunked }

/-- Bounded first-pass information needed to preserve the reference packer's
    generated-blank-node and source-identity contracts. -/
structure SourcePrepass where
  bnodePrefix : String
  sourceIdentity : ByteArray

/-! ## First pass -/

structure PrepassState where
  utf8 : Utf8Stream := Utf8Stream.init
  underscores : UnderscoreRun := {}
  digest : Sha256Stream := Sha256Stream.init

def prepassInit : PrepassState := {}

def prepassFeed (state : PrepassState) (bytes : ByteArray) : Except String PrepassState :=
  match state.utf8.feed bytes with
  | .error message => .error s!"l4block-shard-pack UTF-8 error: {message}"
  | .ok (text, nextUtf8) =>
      .ok { utf8 := nextUtf8
            underscores := state.underscores.feedChars text.toList
            digest := state.digest.update bytes }

def prepassFinish (state : PrepassState) : Except String SourcePrepass :=
  match state.utf8.finish with
  | .error message => .error s!"l4block-shard-pack UTF-8 error: {message}"
  | .ok _ =>
      .ok { bnodePrefix := freshBnodePrefixOfLongest state.underscores.longest
            sourceIdentity := state.digest.finish }

/-! ## Second pass -/

/- The fold accumulator is deliberately a reverse list of triples completed
   since the current decoded input chunk.  It is reset after publication, so
   the packer never builds a graph-wide predicate map in memory. -/
def ingestStep (accRev : List L4Factoidal.RDF.Triple)
    (triples : List L4Factoidal.RDF.Triple) : List L4Factoidal.RDF.Triple :=
  triples.reverse ++ accRev

/-- Publication metadata is small even for a large source: one manifest row
    and one TSV row per immutable output block, never the source triples. -/
structure PackState where
  tripleCount : Nat := 0
  nextOrdinal : Nat := 0
  entriesRev : List Entry := []
  linesRev : List String := []

private def sidecar (h : Hasher) (indexName : String) (bytes : ByteArray)
    (commitError : String) : Except String (ArtifactRef × List Artifact) :=
  match artifactRef? h indexName bytes with
  | none => .error commitError
  | some ref => .ok (ref, [{ name := indexName, bytes := bytes }, merkleArtifact h indexName bytes])

/-- The encoded block plus its sidecars, as artifacts and one manifest row.
    Artifacts are accumulated in reverse and reversed once at the end. -/
def publishBlocks (h : Hasher) (format : PackFormat) :
    PackState → List Artifact →
    List (L4Factoidal.RDF.WfIri × L4Factoidal.Storage.IndexedBlock.Block) →
    Except String (PackState × List Artifact)
  | state, outRev, [] => .ok (state, outRev.reverse)
  | state, outRev, (predicate, block) :: rest => do
      let bytes ← match encodeBlock? format block with
        | none => .error s!"unsupported block for {predicate.val}"
        | some bytes => pure bytes
      let ordinal := state.nextOrdinal
      let name := artifactName format ordinal
      let artifact ← match artifactRef? h name bytes with
        | some value => pure value
        | none => .error s!"could not commit fixed chunks for {predicate.val}"
      let outRev := merkleArtifact h name bytes :: { name := name, bytes := bytes } :: outRev
      let (subjectIndex, outRev) ← match format with
        | .ibk2 | .ibk4 => pure (none, outRev)
        | .ibk3 =>
            let index : L4Factoidal.Storage.SubjectRowIndexWireV2.Index :=
              { targetIBKSha256 := artifact.sha256
                rowCount := block.rows.size
                pairs := L4Factoidal.Storage.SubjectRowIndexWire.pairsOfRows block.rows |>.toArray }
            match L4Factoidal.Storage.SubjectRowIndexWireV2.encode? index with
            | none => .error s!"could not encode SRI2 index for {predicate.val}"
            | some indexBytes => do
                let (ref, made) ← sidecar h (name ++ ".sri2") indexBytes
                  s!"could not commit SRI2 chunks for {predicate.val}"
                pure (some ref, made.reverse ++ outRev)
      let (termIndex, outRev) ← match format with
        | .ibk2 | .ibk4 => pure (none, outRev)
        | .ibk3 =>
            let index : L4Factoidal.Storage.TermLocalIndexWire.Index :=
              { targetIBKSha256 := artifact.sha256
                entries := L4Factoidal.Storage.TermLocalIndex.entriesOf block.dict }
            match L4Factoidal.Storage.TermLocalIndexWire.encode? index with
            | none => .error s!"could not encode TLI1 index for {predicate.val}"
            | some indexBytes => do
                let (ref, made) ← sidecar h (name ++ ".tli1") indexBytes
                  s!"could not commit TLI1 chunks for {predicate.val}"
                pure (some ref, made.reverse ++ outRev)
      /- OLI2 uses the same canonical pageable `(local ID, row offset)`
         framing as SRI2, but is published in SBM6's distinct
         `objectIndex` role and recomputed against row.o at activation. -/
      let (objectIndex, outRev) ← match format with
        | .ibk2 | .ibk4 => pure (none, outRev)
        | .ibk3 =>
            let index : L4Factoidal.Storage.SubjectRowIndexWireV2.Index :=
              { targetIBKSha256 := artifact.sha256
                rowCount := block.rows.size
                pairs := L4Factoidal.Storage.SubjectRowIndexWire.pairsOfObjects block.rows |>.toArray }
            match L4Factoidal.Storage.SubjectRowIndexWireV2.encode? index with
            | none => .error s!"could not encode OLI2 index for {predicate.val}"
            | some indexBytes => do
                let (ref, made) ← sidecar h (name ++ ".oli2") indexBytes
                  s!"could not commit OLI2 chunks for {predicate.val}"
                pure (some ref, made.reverse ++ outRev)
      let entry : Entry :=
        { predicate
          artifact
          subjectIndex
          termIndex
          objectIndex
          rows := block.rows.size
          ordinal }
      let indexName := subjectIndex.map (fun index => index.key.value) |>.getD ""
      let termIndexName := termIndex.map (fun index => index.key.value) |>.getD ""
      let objectIndexName := objectIndex.map (fun index => index.key.value) |>.getD ""
      publishBlocks h format
        { tripleCount := state.tripleCount + block.rows.size
          nextOrdinal := ordinal + 1
          entriesRev := entry :: state.entriesRev
          linesRev := s!"{ordinal}\t{predicate.val}\t{name}\t{block.rows.size}\t{bytes.size}\t{bytesToHex artifact.sha256}\t{name}.merkle\t{indexName}\t{termIndexName}\t{objectIndexName}" :: state.linesRev }
        outRev rest

/-- Commit all complete statements seen since the prior decoded input chunk.
    A single very large Turtle statement remains an intentional bounded-input
    exception: its grammar requires retaining the unfinished statement. -/
def publishBatch (h : Hasher) (format : PackFormat) (state : PackState)
    (triples : List L4Factoidal.RDF.Triple) : Except String (PackState × List Artifact) :=
  publishBlocks h format state [] (blocksOfBuckets (addTriples {} triples))

/-- The whole second pass: UTF-8 carry, the grammar-validated Turtle fold,
    the independently streamed source digest, and the published metadata.
    Every field is bounded; nothing here grows with the input length except
    one manifest row per output block. -/
structure IngestState where
  hasher : Hasher
  format : PackFormat
  expected : ByteArray
  utf8 : Utf8Stream
  fold : TurtleChunkFoldState (List L4Factoidal.RDF.Triple)
  digest : Sha256Stream
  packed : PackState
  chunksSincePublish : Nat

def ingestInit (h : Hasher) (format : PackFormat) (prepass : SourcePrepass)
    (baseIri : Option String) : IngestState :=
  { hasher := h
    format
    expected := prepass.sourceIdentity
    utf8 := Utf8Stream.init
    fold := TurtleChunkFoldState.init prepass.bnodePrefix ingestStep [] baseIri
    digest := Sha256Stream.init
    packed := {}
    chunksSincePublish := 0 }

/-- Feed one input chunk. Artifacts that complete during a feed are returned
    at once, so a host never holds more than one publication batch. -/
def ingestFeed (state : IngestState) (bytes : ByteArray) :
    Except String (IngestState × List Artifact) :=
  match state.utf8.feed bytes with
  | .error message => .error s!"l4block-shard-pack UTF-8 error: {message}"
  | .ok (text, nextUtf8) =>
      match state.fold.feed ingestStep text with
      | .error error =>
          .error s!"l4block-shard-pack Turtle parse error at {error.pos}: {error.msg}"
      | .ok nextFold =>
          let nextCount := state.chunksSincePublish + 1
          if nextCount < publicationChunkCount then
            .ok ({ state with utf8 := nextUtf8, fold := nextFold,
                              digest := state.digest.update bytes,
                              chunksSincePublish := nextCount }, [])
          else
            match publishBatch state.hasher state.format state.packed nextFold.acc.reverse with
            | .error message => .error message
            | .ok (packed, made) =>
                .ok ({ state with utf8 := nextUtf8, fold := { nextFold with acc := [] },
                                  digest := state.digest.update bytes,
                                  packed := packed, chunksSincePublish := 0 }, made)

/-- End of input: the streamed source digest must equal the first-pass
    commitment before the manifest commits any artifact into a readable
    store. -/
def ingestFinish (state : IngestState) : Except String (PackState × List Artifact) :=
  match state.utf8.finish with
  | .error message => .error s!"l4block-shard-pack UTF-8 error: {message}"
  | .ok _ =>
      if state.digest.finish != state.expected then
        .error "l4block-shard-pack input changed between pre-pass and parse pass"
      else
        match state.fold.finish ingestStep with
        | .error error =>
            .error s!"l4block-shard-pack Turtle parse error at {error.pos}: {error.msg}"
        | .ok triples =>
            publishBatch state.hasher state.format state.packed triples.reverse

/-! ## The manifest -/

def manifestTsvHeader : String :=
  "# index\tpredicate\tfile\trows\tbytes\tsha256\tmerkle-leaves\tsubject-index\tterm-index\tobject-index\n"

def manifestTsv (header : String) (linesRev : List String) : String :=
  header ++ String.intercalate "\n" linesRev.reverse ++ "\n"

/-- The SBM manifest and the human-inspectable TSV, from a finished
    `PackState`. Published only after `ingestFinish` has agreed the source
    digest. -/
def manifestArtifacts (format : PackFormat) (prepass : SourcePrepass) (state : PackState) :
    Except String (List Artifact) :=
  let manifest : Manifest :=
    { version := manifestVersion format
      sourceIdentity := prepass.sourceIdentity
      termRegistryVersion := registryVersion format
      layout := layoutName format
      entries := state.entriesRev.reverse }
  match L4Factoidal.Storage.ShardManifest.encode? manifest with
  | none => .error "could not encode structurally valid SBM2 manifest"
  | some manifestBytes =>
      .ok [{ name := "manifest.sbm2", bytes := manifestBytes },
           { name := "manifest.tsv",
             bytes := (manifestTsv manifestTsvHeader state.linesRev).toUTF8 }]

end L4Factoidal.Storage.PackStream
