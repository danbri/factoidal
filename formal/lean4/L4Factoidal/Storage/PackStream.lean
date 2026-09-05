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
import L4Factoidal.Storage.PredicateQuadBlocks
import L4Factoidal.Storage.IndexedBlockWireV4
import L4Factoidal.Storage.LiteralGramIndexWire
import L4Factoidal.Storage.GeoBBoxIndexWire
import L4Factoidal.Syntax.Turtle
import L4Factoidal.Syntax.TriG
import L4Factoidal.Syntax.NQuadsFast
import L4Factoidal.Syntax.NQuadsFold
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
  | .ibk4 => "quad-ibk4-ptd1-lgi1-gbi1-merkle-v0"

def registryVersion : PackFormat → String
  | .ibk2 => "local-ibk2-dict-v0"
  | .ibk3 => "local-ibk3-ptd1-v0"
  | .ibk4 => "local-ibk4-ptd1-v0"

def manifestVersion : PackFormat → Nat
  | .ibk2 => 2
  | .ibk3 => 6
  | .ibk4 => 9

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

/-- The pre-pass carries its SHA-256 block fold the way the ingest carries
    its `Hasher`: as an injected operation, so the executable edge can pass
    the HACL* C walk (`Harness.nativeBlockFold256`) while every `#guard`,
    every theorem and every WebAssembly operation keeps the pure Lean
    specification walk. The two are extensionally equal; the agreement is a
    measured gate, not an assumption (`Crypto/SHA2Native.lean`). -/
structure PrepassState where
  blocks : Crypto.BlockFold256 := Crypto.pureBlockFold256
  utf8 : Utf8Stream := Utf8Stream.init
  underscores : UnderscoreRun := {}
  digest : Sha256Stream := Sha256Stream.init

def prepassInit (blocks : Crypto.BlockFold256 := Crypto.pureBlockFold256) :
    PrepassState := { blocks }

def prepassFeed (state : PrepassState) (bytes : ByteArray) : Except String PrepassState :=
  match state.utf8.feed bytes with
  | .error message => .error s!"l4block-shard-pack UTF-8 error: {message}"
  | .ok (text, nextUtf8) =>
      .ok { state with
              utf8 := nextUtf8
              underscores := state.underscores.feedChars text.toList
              digest := state.digest.updateWith state.blocks bytes }

def prepassFinish (state : PrepassState) : Except String SourcePrepass :=
  match state.utf8.finish with
  | .error message => .error s!"l4block-shard-pack UTF-8 error: {message}"
  | .ok _ =>
      .ok { bnodePrefix := freshBnodePrefixOfLongest state.underscores.longest
            sourceIdentity := state.digest.finishWith state.blocks }

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
  blocks : Crypto.BlockFold256
  format : PackFormat
  expected : ByteArray
  utf8 : Utf8Stream
  fold : TurtleChunkFoldState (List L4Factoidal.RDF.Triple)
  digest : Sha256Stream
  packed : PackState
  chunksSincePublish : Nat

def ingestInit (h : Hasher) (format : PackFormat) (prepass : SourcePrepass)
    (baseIri : Option String)
    (blocks : Crypto.BlockFold256 := Crypto.pureBlockFold256) : IngestState :=
  { hasher := h
    blocks := blocks
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
                              digest := state.digest.updateWith state.blocks bytes,
                              chunksSincePublish := nextCount }, [])
          else
            match publishBatch state.hasher state.format state.packed nextFold.acc.reverse with
            | .error message => .error message
            | .ok (packed, made) =>
                .ok ({ state with utf8 := nextUtf8, fold := { nextFold with acc := [] },
                                  digest := state.digest.updateWith state.blocks bytes,
                                  packed := packed, chunksSincePublish := 0 }, made)

/-- End of input: the streamed source digest must equal the first-pass
    commitment before the manifest commits any artifact into a readable
    store. -/
def ingestFinish (state : IngestState) : Except String (PackState × List Artifact) :=
  match state.utf8.finish with
  | .error message => .error s!"l4block-shard-pack UTF-8 error: {message}"
  | .ok _ =>
      if state.digest.finishWith state.blocks != state.expected then
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

/-! ## The IBK4 path

An IBK3 block holds one predicate of one graph, so the streaming fold above
may open a new block for the same predicate in a later batch. An IBK4 block
now also holds one predicate of one graph: `PredicateQuadBlocks` cuts a
predicate's rows at every graph change and at two size targets, and the
manifest carries the union (`docs/designissues/2026-09-04-blocks-per-predicate.md`).
The IBK4 packer is still bounded by the input size for a different reason: it
partitions the block set at CONSTRUCTION and publishes every block at the end
of the pass, so the dataset and the encoded generation are live together.
Publishing a graph's blocks when the graph closes is the next step and is not
this change.

This is the shape `Harness/PredicateShardPack.lean` ran natively before
2026-09-03. It is here, with no `IO` in any signature, so the WebAssembly
entry layer runs the identical code and commits identical bytes. The one
difference from the streaming path is that a caller must hold the source
text, which is why `Wasm/Ops/Pack.lean` carries a buffered-input cap for
this layout and not for IBK3.
-/

/-- Which grammar reads the source. The native packer chose this from the
    file-name suffix; the wasm entry has no file name, so a caller states
    it. `ntriples` reads with the Turtle grammar, of which N-Triples is a
    subset — which is what the suffix rule did. -/
inductive PackSyntax where
  | turtle
  | trig
  | nquads
  | ntriples
  deriving Repr, DecidableEq

def syntaxName : PackSyntax → String
  | .turtle => "turtle"
  | .trig => "trig"
  | .nquads => "nquads"
  | .ntriples => "ntriples"

def syntaxOfTag? (tag : String) : Option PackSyntax :=
  match tag.toLower with
  | "turtle" | "ttl" => some .turtle
  | "trig" => some .trig
  | "nquads" | "nq" | "n-quads" => some .nquads
  | "ntriples" | "nt" | "n-triples" => some .ntriples
  | _ => none

def formatOfTag? (tag : String) : Option PackFormat :=
  match tag.toLower with
  | "ibk2" => some .ibk2
  | "ibk3" => some .ibk3
  | "ibk4" => some .ibk4
  | _ => none

def formatName : PackFormat → String
  | .ibk2 => "ibk2"
  | .ibk3 => "ibk3"
  | .ibk4 => "ibk4"

/-- The whole source, as a dataset. `trig` and `nquads` carry named graphs;
    `turtle` and `ntriples` put every triple in the default graph. -/
def parseSource (grammar : PackSyntax) (text : String) (baseIri : Option String) :
    Except String L4Factoidal.RDF.Dataset :=
  match grammar with
  | .trig =>
      match L4Factoidal.Syntax.parseTriG text baseIri with
      | .error e => .error s!"l4block-shard-pack TriG parse error at {e.pos}: {e.msg}"
      | .ok ds => .ok ds
  | .nquads =>
      match L4Factoidal.Syntax.parseNQuadsFast text with
      | .error e => .error s!"l4block-shard-pack N-Quads parse error at {e.pos}: {e.msg}"
      | .ok ds => .ok ds
  | .turtle | .ntriples =>
      match L4Factoidal.Syntax.parseTurtle text baseIri with
      | .error e => .error s!"l4block-shard-pack Turtle parse error at {e.pos}: {e.msg}"
      | .ok graph => .ok { default := graph, named := [] }

private def graphSetText (names : List GraphName) : String :=
  String.intercalate "," (names.map fun name =>
    match name with
    | .defaultGraph => "default"
    | .iri value => value.val
    | .bnode label => "_:" ++ label)

/-- One IBK4 block, its Merkle sidecar and its manifest row. The artifact
    order is the block bytes and then the sidecar, which is the order the
    native packer wrote them in. -/
def publishQuadBlocks (h : Hasher) (scope : String) :
    PackState → List Artifact →
    List (L4Factoidal.RDF.WfIri × L4Factoidal.Storage.IndexedBlockWireV4.QuadBlock) →
    Except String (PackState × List Artifact)
  | state, outRev, [] => .ok (state, outRev.reverse)
  | state, outRev, (predicate, block) :: rest => do
      let bytes ← match L4Factoidal.Storage.IndexedBlockWireV4.encode? block with
        | none => .error s!"unsupported quad block for {predicate.val}"
        | some bytes => pure bytes
      let ordinal := state.nextOrdinal
      let name := artifactName .ibk4 ordinal
      let artifact ← match artifactRef? h name bytes with
        | some value => pure value
        | none => .error s!"could not commit fixed chunks for {predicate.val}"
      let graphSet ← match L4Factoidal.Storage.IndexedBlockWireV4.graphNames? block with
        | none => .error s!"unresolvable graph name in block for {predicate.val}"
        | some names => pure (names.map GraphName.ofGraphRef)
      let outRev := merkleArtifact h name bytes :: { name := name, bytes := bytes } :: outRev
      /- SBM8's LGI1 literal search index. It is written for EVERY block: a
         block whose dictionary holds no literal carries an index with no
         gram, so an SBM8 reader never asks whether the role is present.
         `LiteralGramIndex.build` decides the grams and the posting order and
         `LiteralGramIndexWire.encode?` decides the bytes; nothing is restated
         here. -/
      let literal : L4Factoidal.Storage.LiteralGramIndexWire.Artifact :=
        { targetIBKSha256 := artifact.sha256
          index := L4Factoidal.Storage.LiteralGramIndex.build block.dict }
      let (literalIndex, outRev) ←
        match L4Factoidal.Storage.LiteralGramIndexWire.encode? literal with
        | none => .error s!"could not encode LGI1 index for {predicate.val}"
        | some indexBytes => do
            let (ref, made) ← sidecar h (name ++ ".lgi1") indexBytes
              s!"could not commit LGI1 chunks for {predicate.val}"
            pure (some ref, made.reverse ++ outRev)
      /- SBM9's GBI1 geometry bounding-box index, written for EVERY block on
         the same rule: a block whose dictionary holds no geometry carries an
         index with no entry, so an SBM9 reader never asks whether the role is
         present. `GeoBBoxIndex.build` decides the boxes, the CRS table and
         the entry order, and `GeoBBoxIndexWire.encode?` decides the bytes;
         nothing is restated here. -/
      let geo : L4Factoidal.Storage.GeoBBoxIndexWire.Artifact :=
        { targetIBKSha256 := artifact.sha256
          index := L4Factoidal.Storage.GeoBBoxIndex.build block.dict }
      let (geoIndex, outRev) ←
        match L4Factoidal.Storage.GeoBBoxIndexWire.encode? geo with
        | none => .error s!"could not encode GBI1 index for {predicate.val}"
        | some indexBytes => do
            let (ref, made) ← sidecar h (name ++ ".gbi1") indexBytes
              s!"could not commit GBI1 chunks for {predicate.val}"
            pure (some ref, made.reverse ++ outRev)
      let entry : Entry :=
        { predicate
          artifact
          literalIndex
          geoIndex
          blockLayout := some BlockLayout.ibk4
          blankNodeScope := scope
          graphSet
          rows := block.rows.size
          ordinal }
      let literalIndexName := literalIndex.map (fun index => index.key.value) |>.getD ""
      let geoIndexName := geoIndex.map (fun index => index.key.value) |>.getD ""
      publishQuadBlocks h scope
        { tripleCount := state.tripleCount + block.rows.size
          nextOrdinal := ordinal + 1
          entriesRev := entry :: state.entriesRev
          linesRev := s!"{ordinal}\t{predicate.val}\t{name}\t{block.rows.size}\t{bytes.size}\t{bytesToHex artifact.sha256}\t{name}.merkle\t{graphSet.length}\t{graphSetText graphSet}\t{literalIndexName}\t{geoIndexName}" :: state.linesRev }
        outRev rest

/-- Every IBK4 block of one source. The blank-node scope is the SOURCE
    file's SHA-256, the same digest the manifest commits as its source
    identity: specification section 2.4.1 admits a content digest only under
    a publication profile which states that repeated imports of those bytes
    share one blank-node allocation, and `content-digest-shared` states it. -/
structure QuadPack where
  /-- The named graphs of the source plus its default graph. Reported by the
      native packer's summary line; not a committed value. -/
  graphs : Nat
  packed : PackState
  artifacts : List Artifact

def quadArtifacts (h : Hasher) (grammar : PackSyntax) (prepass : SourcePrepass)
    (text : String) (baseIri : Option String) : Except String QuadPack := do
  let dataset ← parseSource grammar text baseIri
  let (packed, artifacts) ←
    publishQuadBlocks h (bytesToHex prepass.sourceIdentity) {}
      [] (L4Factoidal.Storage.PredicateQuadBlocks.blocksOfDataset dataset)
  .ok { graphs := dataset.named.length + 1, packed, artifacts }

/-! ### The streaming N-Quads route to IBK4

`quadArtifacts` above takes the WHOLE source as a `String`, and
`parseNQuadsFast` starts with `s.toList`. A `List Char` cons cell is three
machine words, so that one list is about twenty-four times the input size and
it is live at the same time as the dataset it produces. Measured on a
104,017,780-byte N-Quads source over 50 named graphs: 2,531,999,744 bytes of
peak memory footprint, of which the character list is the largest part. A
553,021,327-byte source was killed by the operating system after 1 h 57 min
with an empty output directory
(<https://github.com/danbri/factoidal/issues/650>).

The fold below removes both. `Syntax/NQuadsFold.lean` proves
`streamConsume11_eq_batch`: for EVERY consumer, the chunked fold and the
whole-document fold reach the same accumulator. Instantiated at the
`FastDataset` accumulator which `parseNQuadsFast` itself uses, the dataset a
chunked run builds IS the dataset `parseSource .nquads` builds, so every
committed byte is unchanged. Only 65,536 bytes of source, plus at most one
partial line, are decoded at a time.

What this does NOT make bounded: the IBK4 block set is partitioned at
construction but published at the end of the pass, so the dataset, the blocks
and their encoded bytes are all live when the last block is published, so
nothing the pass builds is released before the end, and the character list
twenty-four times the source is no longer among it. What the rest costs was
MEASURED on skosdex prefixes, 2026-09-05: peak footprint 390,318,656 bytes
for 52,428,626 of source, 599,870,336 for 104,857,577, 933,809,856 for
209,715,187 and 5,951,730,560 for 1,543,478,120 — LINEAR in the source, at
3.76 bytes of peak footprint per source byte plus a constant of about
145 MB. The RATIO to the source falls with size (7.44x, 5.72x, 4.45x,
3.86x) because that constant amortises; do not read a trend out of it. The
first three points alone fit a sublinear power law and that reading was
wrong (`docs/designissues/2026-09-05-shard-pack-profile-and-memory.md`,
section 3). A memory footprint independent of the input needs the
publication point to move to the graph boundary, which
`docs/designissues/2026-09-04-blocks-per-predicate.md` records as the next
step. The other three grammars keep the buffered route: TriG has no
chunk fold yet, and Turtle would need its own agreement theorem against
`parseTurtle`. -/

/-- The state of a streaming IBK4 pass over an N-Quads source. Every field is
    bounded except the `FastDataset` accumulator. -/
structure QuadIngestState where
  hasher : Hasher
  blocks : Crypto.BlockFold256
  scope : String
  expected : ByteArray
  utf8 : Utf8Stream
  stream : L4Factoidal.Syntax.NQuadsStreaming.StreamStateC L4Factoidal.Syntax.FastDataset
  digest : Sha256Stream

def quadIngestInit (h : Hasher) (prepass : SourcePrepass)
    (blocks : Crypto.BlockFold256 := Crypto.pureBlockFold256) : QuadIngestState :=
  { hasher := h
    blocks := blocks
    scope := bytesToHex prepass.sourceIdentity
    expected := prepass.sourceIdentity
    utf8 := Utf8Stream.init
    stream := L4Factoidal.Syntax.NQuadsStreaming.initialStateC {}
    digest := Sha256Stream.init }

/-- Feed one input chunk. A parse error is sticky in `StreamStateC` and is
    reported by `quadIngestFinish`, which is where the batch route reports it
    too. -/
def quadIngestFeed (state : QuadIngestState) (bytes : ByteArray) :
    Except String QuadIngestState :=
  match state.utf8.feed bytes with
  | .error message => .error s!"l4block-shard-pack UTF-8 error: {message}"
  | .ok (text, nextUtf8) =>
      .ok { state with
              utf8 := nextUtf8
              stream := L4Factoidal.Syntax.NQuadsStreaming.feedChunkC .rdf11
                          L4Factoidal.Syntax.addQuadFast state.stream text.toList
              digest := state.digest.updateWith state.blocks bytes }

/-- End of input: the streamed source digest must equal the first-pass
    commitment, as `ingestFinish` requires on the IBK3 path. The buffered
    IBK4 route had no such check on the native packer. -/
def quadIngestFinish (state : QuadIngestState) : Except String QuadPack :=
  match state.utf8.finish with
  | .error message => .error s!"l4block-shard-pack UTF-8 error: {message}"
  | .ok _ =>
      if state.digest.finishWith state.blocks != state.expected then
        .error "l4block-shard-pack input changed between pre-pass and parse pass"
      else
        match L4Factoidal.Syntax.NQuadsStreaming.finishC .rdf11
                L4Factoidal.Syntax.addQuadFast state.stream with
        | .error e => .error s!"l4block-shard-pack N-Quads parse error at {e.pos}: {e.msg}"
        | .ok fast =>
            let dataset := fast.toDataset
            let graphs := dataset.named.length + 1
            match publishQuadBlocks state.hasher state.scope {} []
                (L4Factoidal.Storage.PredicateQuadBlocks.blocksOfDataset dataset) with
            | .error message => .error message
            | .ok (packed, artifacts) => .ok { graphs, packed, artifacts }

/-- Which grammars the streaming IBK4 route reads. -/
def quadStreams : PackSyntax → Bool
  | .nquads => true
  | .turtle | .trig | .ntriples => false

def quadManifestTsvHeader : String :=
  "# index\tpredicate\tfile\trows\tbytes\tsha256\tmerkle-leaves\tgraphs\tgraph-set\tliteral-index\tgeo-index\n"

/-- The SBM7 manifest and the TSV of a finished IBK4 `PackState`. -/
def quadManifestArtifacts (prepass : SourcePrepass) (state : PackState) :
    Except String (List Artifact) :=
  let manifest : Manifest :=
    { version := manifestVersion .ibk4
      sourceIdentity := prepass.sourceIdentity
      termRegistryVersion := registryVersion .ibk4
      layout := layoutName .ibk4
      blankNodeProfile := "content-digest-shared"
      entries := state.entriesRev.reverse }
  match L4Factoidal.Storage.ShardManifest.encode? manifest with
  | none => .error "could not encode structurally valid SBM8 manifest"
  | some manifestBytes =>
      .ok [{ name := "manifest.sbm2", bytes := manifestBytes },
           { name := "manifest.tsv",
             bytes := (manifestTsv quadManifestTsvHeader state.linesRev).toUTF8 }]

end L4Factoidal.Storage.PackStream
