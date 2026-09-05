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
import L4Factoidal.Storage.IndexedBlockWireV5
import L4Factoidal.Storage.BlockV5Plan
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
  /-- Wire version 10: IBK5 blocks over a PTD2 dictionary of version-2 terms,
      an LGI2 literal index, the GBI1 geometry index unchanged, and an SBM10
      manifest with a blob table and per-entry zone maps
      (`docs/designissues/2026-09-05-wire-version-10-scale.md`). -/
  | ibk5
  deriving Repr, DecidableEq

/-- The two quad formats. They share the whole ingest fold and differ only in
    the block codec, the sidecar version and the manifest version. -/
def isQuadFormat : PackFormat → Bool
  | .ibk4 | .ibk5 => true
  | .ibk2 | .ibk3 => false

def artifactName : PackFormat → Nat → String
  | .ibk2, ordinal => s!"predicate-{ordinal}.ibk2"
  | .ibk3, ordinal => s!"predicate-{ordinal}.ibk3"
  | .ibk4, ordinal => s!"predicate-{ordinal}.ibk4"
  | .ibk5, ordinal => s!"predicate-{ordinal}.ibk5"

def layoutName : PackFormat → String
  | .ibk2 => "predicate-ibk2-merkle-v2-streaming"
  | .ibk3 => "predicate-ibk3-ptd1-sri2-tli1-oli2-merkle-v0"
  | .ibk4 => "quad-ibk4-ptd1-lgi1-gbi1-merkle-v0"
  | .ibk5 => "quad-ibk5-ptd2-lgi2-gbi1-merkle-v0"

def registryVersion : PackFormat → String
  | .ibk2 => "local-ibk2-dict-v0"
  | .ibk3 => "local-ibk3-ptd1-v0"
  | .ibk4 => "local-ibk4-ptd1-v0"
  | .ibk5 => "local-ibk5-ptd2-v0"

def manifestVersion : PackFormat → Nat
  | .ibk2 => 2
  | .ibk3 => 6
  | .ibk4 => 9
  | .ibk5 => 10

def encodeBlock? : PackFormat → L4Factoidal.Storage.IndexedBlock.Block → Option ByteArray
  | .ibk2, block => L4Factoidal.Storage.IndexedBlockWireV2.encode? block
  | .ibk3, block => L4Factoidal.Storage.IndexedBlockWireV3.encode? block
  | .ibk4, _ => none
  | .ibk5, _ => none

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

/-- The packer's fold step IS the accumulator `parseStatements` uses, which
    is what lets `Syntax.parseTurtle_eq_fold` speak about this packer: the
    reversed accumulator this fold ends with, reversed once, is exactly the
    `Graph` `parseTurtle` returns. -/
theorem ingestStep_eq_prependReverse : ingestStep = L4Factoidal.Syntax.prependReverse := rfl

/-- Publication metadata is small even for a large source: one manifest row
    and one TSV row per immutable output block, never the source triples. -/
structure PackState where
  tripleCount : Nat := 0
  nextOrdinal : Nat := 0
  entriesRev : List Entry := []
  linesRev : List String := []
  /-- SBM10 only: the manifest blob table under construction, ascending and
      distinct by SHA-256. Every out-of-line literal the pass has seen is one
      member, whichever block first named it; content addressing is what makes
      a literal shared by several blocks one artifact. Empty on every other
      path. -/
  blobs : List ArtifactRef := []
  /-- SBM10 only: the digests of the out-of-line literals of each entry, in
      the same reverse order as `entriesRev`. They become positions in the
      final blob table at `quadManifestArtifacts`, which is the first point
      the table is complete. -/
  entryBlobsRev : List (List ByteArray) := []

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
        | .ibk2 | .ibk4 | .ibk5 => pure (none, outRev)
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
        | .ibk2 | .ibk4 | .ibk5 => pure (none, outRev)
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
        | .ibk2 | .ibk4 | .ibk5 => pure (none, outRev)
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
also holds one predicate of one graph: `PredicateQuadBlocks` buckets the quads
by the pair (predicate, graph) and cuts a bucket's rows at two size targets,
and the manifest carries the union
(`docs/designissues/2026-09-04-blocks-per-predicate.md`).
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
  | "ibk5" => some .ibk5
  | _ => none

def formatName : PackFormat → String
  | .ibk2 => "ibk2"
  | .ibk3 => "ibk3"
  | .ibk4 => "ibk4"
  | .ibk5 => "ibk5"

/-- Which RDF version the source is read as. Wire version 10 is the first
    format that can STORE an RDF 1.2 triple term or a directional literal, so
    it is the first that may accept one from a source: an IBK4 block refuses a
    triple term at encoding, and reading one only to refuse it later would
    turn a clean parse error into a block-encoding failure. Every earlier
    format therefore keeps reading RDF 1.1 exactly as before. -/
def sourceMode : PackFormat → L4Factoidal.Syntax.Mode
  | .ibk5 => .rdf12
  | _ => .rdf11

/-- The whole source, as a dataset. `trig` and `nquads` carry named graphs;
    `turtle` and `ntriples` put every triple in the default graph. -/
def parseSource (format : PackFormat) (grammar : PackSyntax) (text : String)
    (baseIri : Option String) : Except String L4Factoidal.RDF.Dataset :=
  let mode := sourceMode format
  match grammar with
  | .trig =>
      match L4Factoidal.Syntax.parseTriG text baseIri mode with
      | .error e => .error s!"l4block-shard-pack TriG parse error at {e.pos}: {e.msg}"
      | .ok ds => .ok ds
  | .nquads =>
      match L4Factoidal.Syntax.parseNQuadsFast text mode with
      | .error e => .error s!"l4block-shard-pack N-Quads parse error at {e.pos}: {e.msg}"
      | .ok ds => .ok ds
  | .turtle | .ntriples =>
      match L4Factoidal.Syntax.parseTurtle text baseIri mode with
      | .error e => .error s!"l4block-shard-pack Turtle parse error at {e.pos}: {e.msg}"
      | .ok graph => .ok { default := graph, named := [] }

private def graphSetText (names : List GraphName) : String :=
  String.intercalate "," (names.map fun name =>
    match name with
    | .defaultGraph => "default"
    | .iri value => value.val
    | .bnode label => "_:" ++ label)

/-! ## SBM10 blob artifacts

An out-of-line literal's lexical form is one artifact, `blob-<sha256 hex>.lit`,
holding exactly its UTF-8 bytes. The digest is the artifact identity, so the
same literal in two blocks or two graphs is one file, and a reader that holds
a version-2 tag-4 term can name the file from the term alone. -/

/-- Insert one blob reference into the table, keeping it ascending by SHA-256.
    A digest already present is not inserted twice. -/
def insertBlobRef : List ArtifactRef → ArtifactRef → List ArtifactRef
  | [], ref => [ref]
  | head :: rest, ref =>
      if head.sha256.toList == ref.sha256.toList then head :: rest
      else if L4Factoidal.Storage.ShardManifest.lexLt ref.sha256.toList head.sha256.toList then
        ref :: head :: rest
      else head :: insertBlobRef rest ref

def blobTableHas (table : List ArtifactRef) (digest : ByteArray) : Bool :=
  table.any fun ref => ref.sha256.toList == digest.toList

/-- The out-of-line literals one block's rows carry, as digest and bytes. The
    packer has the lexical form here and nowhere later, so this is where the
    blob file is made. -/
def blobLiteralsOfRows (h : Hasher)
    (rows : List L4Factoidal.Storage.IndexedBlockWireV4.QuadRow) :
    List (ByteArray × ByteArray) :=
  rows.filterMap fun quad =>
    match quad.2.o with
    | .literal l =>
        if L4Factoidal.Storage.TermWireV2.lexicalFitsInline l then none
        else
          let bytes := l.val.lexicalForm.toUTF8
          some (h.digest bytes, bytes)
    | _ => none

/-- The first row whose object literal is above `maxBlobBytes`. Section 2 of
    the wire-version-10 record: the packer refuses it, naming the literal's
    subject and predicate. -/
def oversizeLiteral? (rows : List L4Factoidal.Storage.IndexedBlockWireV4.QuadRow) :
    Option (L4Factoidal.Storage.IndexedBlockWireV4.QuadRow × Nat) :=
  rows.findSome? fun quad =>
    match quad.2.o with
    | .literal l =>
        let size := l.val.lexicalForm.utf8ByteSize
        if size > L4Factoidal.Storage.TermWireV2.maxBlobBytes then some (quad, size) else none
    | _ => none

private def subjectText (s : L4Factoidal.RDF.Subject) : String :=
  match s with
  | .iri value => "<" ++ value.val ++ ">"
  | .bnode label => "_:" ++ label

/-- The blob artifacts one block adds to the pass, and the table after them.
    A digest already in the table adds nothing: the bytes are already
    committed under exactly this name. -/
def addBlobArtifacts (h : Hasher) (table : List ArtifactRef) (outRev : List Artifact) :
    List (ByteArray × ByteArray) → Except String (List ArtifactRef × List Artifact)
  | [] => .ok (table, outRev)
  | (digest, bytes) :: rest =>
      if blobTableHas table digest then addBlobArtifacts h table outRev rest
      else
        let name := L4Factoidal.Storage.ShardManifest.blobKeyOf digest
        match artifactRef? h name bytes with
        | none => .error s!"could not commit fixed chunks for {name}"
        | some ref =>
            addBlobArtifacts h (insertBlobRef table ref)
              (merkleArtifact h name bytes :: { name := name, bytes := bytes } :: outRev) rest

/-- The first eight bytes of one zone bound, as lowercase hexadecimal. The TSV
    is for a human reading a generation, so it carries the short prefix that
    tells two blocks apart, not the whole 64-byte bound. -/
def zoneText (zone : Option (List UInt8 × List UInt8)) : String :=
  match zone with
  | none => ""
  | some (lo, hi) =>
      bytesToHex (ByteArray.mk (lo.take 8).toArray) ++ ".." ++
        bytesToHex (ByteArray.mk (hi.take 8).toArray)

/-- One IBK4 block, its Merkle sidecar and its manifest row. The artifact
    order is the block bytes and then the sidecar, which is the order the
    native packer wrote them in.

    The argument is the ROWS of each block, not the blocks: the `QuadBlock` is
    built here, one at a time, so a caller publishing a batch never holds more
    than one encoded block beside the rows it has not reached yet. -/
def publishQuadBlocks (h : Hasher) (format : PackFormat) (scope : String) :
    PackState → List Artifact →
    List (L4Factoidal.Storage.PredicateQuadBlocks.BucketKey ×
      List L4Factoidal.Storage.IndexedBlockWireV4.QuadRow) →
    Except String (PackState × List Artifact)
  | state, outRev, [] => .ok (state, outRev.reverse)
  | state, outRev, ((predicate, _graph), rows) :: rest =>
    if format == .ibk5 then do
      /- Section 2 of the wire-version-10 record: a literal above
         `maxBlobBytes` is refused, naming its subject and predicate. -/
      match oversizeLiteral? rows with
      | some (quad, size) =>
          .error s!"l4block-shard-pack refuses a literal of {size} bytes, above maxBlobBytes={L4Factoidal.Storage.TermWireV2.maxBlobBytes}: subject {subjectText quad.2.s} predicate <{quad.2.p.val}>"
      | none => pure ()
      let block := L4Factoidal.Storage.IndexedBlockWireV5.fromRdfQuads h.digest rows
      let bytes ← match L4Factoidal.Storage.IndexedBlockWireV5.encode? block with
        | none => .error s!"unsupported IBK5 quad block for {predicate.val}"
        | some bytes => pure bytes
      let ordinal := state.nextOrdinal
      let name := artifactName .ibk5 ordinal
      let artifact ← match artifactRef? h name bytes with
        | some value => pure value
        | none => .error s!"could not commit fixed chunks for {predicate.val}"
      let graphSet ← match L4Factoidal.Storage.IndexedBlockWireV5.graphNames? block with
        | none => .error s!"unresolvable graph name in block for {predicate.val}"
        | some names => pure (names.map GraphName.ofGraphRef)
      let outRev := merkleArtifact h name bytes :: { name := name, bytes := bytes } :: outRev
      /- The out-of-line literals of this block, as artifacts. Their digests
         are the entry's blob references; the POSITIONS in the manifest blob
         table are resolved at `quadManifestArtifacts`, which is where the
         table is complete and sorted. -/
      let (blobs, outRev) ← addBlobArtifacts h state.blobs outRev (blobLiteralsOfRows h rows)
      let entryDigests := L4Factoidal.Storage.IndexedBlockWireV5.blobDigests block
      /- SBM10's LGI2 literal search index, built over the dictionary's inline
         literals and carrying the positions of the out-of-line ones as its
         opaque list. `BlockV5Plan` decides both, and the activation check
         rebuilds them the same way. -/
      let literal : L4Factoidal.Storage.LiteralGramIndexWire.Artifact :=
        { targetIBKSha256 := artifact.sha256
          index := L4Factoidal.Storage.BlockV5Plan.literalIndexOf block }
      let (literalIndex, outRev) ←
        match L4Factoidal.Storage.LiteralGramIndexWire.encode2? literal with
        | none => .error s!"could not encode LGI2 index for {predicate.val}"
        | some indexBytes => do
            let (ref, made) ← sidecar h (name ++ ".lgi2") indexBytes
              s!"could not commit LGI2 chunks for {predicate.val}"
            pure (some ref, made.reverse ++ outRev)
      /- GBI1, unchanged from SBM9. A blob geometry is NOT in it: its WKT is
         not in the block, so no box can be computed. Every caller that turns
         a GBI1 candidate set into rows must union the block's opaque
         positions into the candidates first, which is what keeps the filter a
         superset (`docs/designissues/2026-09-05-geometry-bounding-box-index.md`). -/
      let geo : L4Factoidal.Storage.GeoBBoxIndexWire.Artifact :=
        { targetIBKSha256 := artifact.sha256
          index := L4Factoidal.Storage.BlockV5Plan.geoIndexOf block }
      let (geoIndex, outRev) ←
        match L4Factoidal.Storage.GeoBBoxIndexWire.encode? geo with
        | none => .error s!"could not encode GBI1 index for {predicate.val}"
        | some indexBytes => do
            let (ref, made) ← sidecar h (name ++ ".gbi1") indexBytes
              s!"could not commit GBI1 chunks for {predicate.val}"
            pure (some ref, made.reverse ++ outRev)
      /- Both zone maps over ONE pass of the dictionary: a key depends only on
         the term, so the key prefixes are computed per dictionary slot rather
         than per row. -/
      let (subjectZone, objectZone) ← match L4Factoidal.Storage.BlockV5Plan.zones? block with
        | none => .error s!"could not compute the zone maps for {predicate.val}"
        | some zones => pure zones
      let entry : Entry :=
        { predicate
          artifact
          literalIndex
          geoIndex
          blockLayout := some BlockLayout.ibk5
          blankNodeScope := scope
          graphSet
          subjectZone := some subjectZone
          objectZone := some objectZone
          rows := block.rows.size
          ordinal }
      let literalIndexName := literalIndex.map (fun index => index.key.value) |>.getD ""
      let geoIndexName := geoIndex.map (fun index => index.key.value) |>.getD ""
      publishQuadBlocks h format scope
        { tripleCount := state.tripleCount + block.rows.size
          nextOrdinal := ordinal + 1
          entriesRev := entry :: state.entriesRev
          blobs := blobs
          entryBlobsRev := entryDigests :: state.entryBlobsRev
          linesRev := s!"{ordinal}\t{predicate.val}\t{name}\t{block.rows.size}\t{bytes.size}\t{bytesToHex artifact.sha256}\t{name}.merkle\t{graphSet.length}\t{graphSetText graphSet}\t{literalIndexName}\t{geoIndexName}\t{zoneText (some subjectZone)}\t{zoneText (some objectZone)}\t{entryDigests.length}" :: state.linesRev }
        outRev rest
    else do
      let block := L4Factoidal.Storage.IndexedBlockWireV4.fromQuads rows
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
      publishQuadBlocks h format scope
        { tripleCount := state.tripleCount + block.rows.size
          nextOrdinal := ordinal + 1
          entriesRev := entry :: state.entriesRev
          blobs := state.blobs
          entryBlobsRev := state.entryBlobsRev
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
  /-- How many publication batches the pass ran. The buffered route is one
      batch by definition. Reported by the summary line; not a committed
      value. -/
  batches : Nat := 1
  packed : PackState
  artifacts : List Artifact

def quadArtifacts (h : Hasher) (format : PackFormat) (grammar : PackSyntax)
    (prepass : SourcePrepass) (text : String) (baseIri : Option String) :
    Except String QuadPack := do
  let dataset ← parseSource format grammar text baseIri
  let (packed, artifacts) ←
    publishQuadBlocks h format (bytesToHex prepass.sourceIdentity) {}
      [] (L4Factoidal.Storage.PredicateQuadBlocks.runsOfDataset dataset)
  .ok { graphs := dataset.named.length + 1, batches := 1, packed, artifacts }

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

What this ALSO makes bounded, since 2026-09-05: the publication point. The
packer publishes a block as soon as the per-block cut rule closes its rows,
and every open run of at least `minBatchRows` rows at each `batchBytes` of
source (`docs/designissues/2026-09-05-pack-publication-every-batch.md`). The
dataset is never built at all; what stays live is one open run per predicate,
the carried rows below `maxCarriedRows`, and one manifest row per block.
MEASURED on skosdex N-Quads prefixes at the 268,435,456-byte default,
2026-09-05: peak footprint 222,955,392 bytes for 52,428,626 of source,
328,272,128 for 104,857,577 and 331,581,824 for 209,715,187 — against
390,318,656, 599,870,336 and 933,809,856 before, which were linear in the
source at 3.76 bytes per source byte. The block SET is larger: 1,018, 1,135
and 1,252 blocks against 964, 1,053 and 1,148.

Turtle, and with it N-Triples, now takes the same route through
`Syntax/TurtleChunkFold.lean` — the fold the IBK3 packer has always used.
Its agreement with `parseTurtle` has two halves. The accumulator half is
PROVED: `Syntax.parseTurtle_eq_fold` states that folding statements with
`ingestStep` and reversing once gives exactly `parseTurtle`'s `Graph`, and
`ingestStep_eq_prependReverse` ties the packer's step to it. The
chunk-boundary half — that the fold reaches the same accumulator whatever
the chunking — is NOT proved. It rests on `TurtleStatementScan` never
offering a candidate that `readStatement` would read past, which is a
lexical property of the scanner that no theorem here states. Byte identity
against the buffered route is therefore MEASURED for Turtle and PROVED for
N-Quads.

TriG keeps the buffered route: it has no chunk fold at all. -/

/-! ### The publication accumulator

The fold no longer builds a `Dataset`. It builds
`PredicateQuadBlocks.Pub` — one OPEN RUN per (predicate, graph) key, each at most
`maxBlockRows` rows and `maxBlockWireBytes` estimated bytes — plus the runs
the cut rule has closed since the last time the caller drained it. The
caller (`quadIngestFeed`) encodes those runs into artifacts and releases
their rows. What stays live is the open runs, the carried rows below the
batch rule, and the manifest rows.

`addQuadPub` has exactly the consumer signature
`NQuadsFold.foldQuadLinesAcc` takes, so `NQuadsFold.streamConsume11_eq_batch`
— stated for EVERY consumer — applies to it unchanged, and
`PackStreamTheorems` uses it. -/

/-- The packer's fold accumulator: the publication state, the runs closed
    since the last drain (in reverse), and the named graphs seen. -/
structure QuadPub where
  pub : L4Factoidal.Storage.PredicateQuadBlocks.Pub := {}
  readyRev : List (L4Factoidal.Storage.PredicateQuadBlocks.BucketKey ×
    List L4Factoidal.Storage.IndexedBlockWireV4.QuadRow) := []
  /-- The distinct named graphs seen. Only its size is reported. -/
  graphs : Std.HashMap L4Factoidal.RDF.GraphRef Unit := ∅

/-- The N-Quads consumer. One quad enters its predicate's open run; whatever
    the cut rule closes is held for the next drain. -/
def addQuadPub (state : QuadPub) (triple : L4Factoidal.RDF.Triple)
    (graph : Option L4Factoidal.RDF.Subject) : QuadPub :=
  let (pub, made) := L4Factoidal.Storage.PredicateQuadBlocks.pubAdd state.pub (graph, triple)
  { pub := pub
    readyRev := made.reverse ++ state.readyRev
    graphs := match graph with
      | none => state.graphs
      | some name => state.graphs.insert name () }

/-- The Turtle consumer: the statements one chunk completed, all in the
    default graph, in source order. -/
def quadPubStep (state : QuadPub) (triples : List L4Factoidal.RDF.Triple) : QuadPub :=
  triples.foldl (fun acc triple => addQuadPub acc triple none) state

/-- The per-grammar part of a streaming IBK4 pass. Both alternatives hold the
    publication accumulator plus one unfinished lexical unit: a partial
    N-Quads line, or a partial Turtle statement. -/
inductive QuadStream where
  | nquads (stream : L4Factoidal.Syntax.NQuadsStreaming.StreamStateC QuadPub)
  | turtle (fold : TurtleChunkFoldState QuadPub)

/-- Take the runs the fold has closed, and reset the ready list. `flushMin`
    is the batch rule: `none` publishes only what the per-block cut rule
    closed, `some n` also publishes every open run of at least `n` rows. -/
def quadStreamDrain (stream : QuadStream) (flushMin : Option Nat) :
    QuadStream × List (L4Factoidal.Storage.PredicateQuadBlocks.BucketKey ×
      List L4Factoidal.Storage.IndexedBlockWireV4.QuadRow) :=
  let take := fun (acc : QuadPub) =>
    let ready := acc.readyRev.reverse
    match flushMin with
    | none => ({ acc with readyRev := [] }, ready)
    | some rows =>
        let (pub, more) := L4Factoidal.Storage.PredicateQuadBlocks.pubFlush acc.pub rows
        ({ acc with pub := pub, readyRev := [] }, ready ++ more)
  match stream with
  | .nquads s =>
      let (acc, out) := take s.acc
      (.nquads { s with acc := acc }, out)
  | .turtle fold =>
      let (acc, out) := take fold.acc
      (.turtle { fold with acc := acc }, out)

/-- The accumulator a finished stream ends with. An N-Quads parse error is
    sticky in `StreamStateC` and surfaces here; the Turtle fold has already
    reported at the chunk that carried the offending statement. -/
def quadStreamFinish (mode : L4Factoidal.Syntax.Mode) (stream : QuadStream) :
    Except ParseError QuadPub :=
  match stream with
  | .nquads s => L4Factoidal.Syntax.NQuadsStreaming.finishC mode addQuadPub s
  | .turtle fold => fold.finish quadPubStep

/-- The state of a streaming IBK4 pass. Every field is bounded: the open runs
    by the per-block cut rule and `maxCarriedRows`, the manifest rows by the
    block count, the rest by construction. -/
structure QuadIngestState where
  hasher : Hasher
  /-- Which quad wire version this pass writes: `.ibk4` is version 9 and
      `.ibk5` version 10. Nothing else about the fold depends on it. -/
  format : PackFormat
  blocks : Crypto.BlockFold256
  scope : String
  expected : ByteArray
  /-- Source bytes per publication batch; `--batch-bytes` on the native CLI,
      the fourth argument of `packBegin` in the WebAssembly module. -/
  batchBytes : Nat
  utf8 : Utf8Stream
  stream : QuadStream
  digest : Sha256Stream
  packed : PackState
  bytesSinceBatch : Nat
  batches : Nat

/-- Start a streaming IBK4 pass. `grammar` selects the fold; a grammar for
    which `quadStreams` is false must not reach here, and reads with the
    Turtle fold if it does, which is what the file-suffix rule did for
    `.nt`. `blocks` is the SHA-256 block fold: the pure Lean walk is the
    specification and the HACL* one is what a host passes, the two being
    extensionally equal. -/
def quadIngestInit (h : Hasher) (format : PackFormat) (grammar : PackSyntax)
    (prepass : SourcePrepass) (baseIri : Option String)
    (batchBytes : Nat := L4Factoidal.Storage.PredicateQuadBlocks.batchSourceBytesDefault)
    (blocks : Crypto.BlockFold256 := Crypto.pureBlockFold256) : QuadIngestState :=
  { hasher := h
    format := format
    blocks := blocks
    scope := bytesToHex prepass.sourceIdentity
    expected := prepass.sourceIdentity
    batchBytes := batchBytes
    utf8 := Utf8Stream.init
    stream :=
      match grammar with
      | .nquads => .nquads (L4Factoidal.Syntax.NQuadsStreaming.initialStateC {})
      | .turtle | .ntriples | .trig =>
          .turtle (TurtleChunkFoldState.init prepass.bnodePrefix quadPubStep {} baseIri
            (sourceMode format))
    digest := Sha256Stream.init
    packed := {}
    bytesSinceBatch := 0
    batches := 0 }

/-- Feed one input chunk and publish. The artifacts a feed returns are the
    ones the host must write, in that order; nothing is held for later. A
    feed publishes the runs the per-block cut rule closed, and at a batch end
    also every open run of at least `minBatchRows` rows. -/
def quadIngestFeed (state : QuadIngestState) (bytes : ByteArray) :
    Except String (QuadIngestState × List Artifact) :=
  match state.utf8.feed bytes with
  | .error message => .error s!"l4block-shard-pack UTF-8 error: {message}"
  | .ok (text, nextUtf8) => do
      let fed ← match state.stream with
        | .nquads stream =>
            .ok (QuadStream.nquads
              (L4Factoidal.Syntax.NQuadsStreaming.feedChunkC (sourceMode state.format)
                  addQuadPub stream text.toList))
        | .turtle fold =>
            match fold.feed quadPubStep text with
            | .error error =>
                .error s!"l4block-shard-pack Turtle parse error at {error.pos}: {error.msg}"
            | .ok next => .ok (QuadStream.turtle next)
      let since := state.bytesSinceBatch + bytes.size
      let batchEnds := since >= state.batchBytes
      let (stream, runs) := quadStreamDrain fed
        (if batchEnds then some L4Factoidal.Storage.PredicateQuadBlocks.minBatchRows else none)
      let (packed, made) ←
        publishQuadBlocks state.hasher state.format state.scope state.packed [] runs
      .ok ({ state with
               utf8 := nextUtf8
               stream := stream
               digest := state.digest.updateWith state.blocks bytes
               packed := packed
               bytesSinceBatch := if batchEnds then 0 else since
               batches := if batchEnds then state.batches + 1 else state.batches }, made)

/-- End of input: the streamed source digest must equal the first-pass
    commitment, as `ingestFinish` requires on the IBK3 path. Then every open
    run is published, whatever its size (rule 5). -/
def quadIngestFinish (state : QuadIngestState) : Except String QuadPack :=
  match state.utf8.finish with
  | .error message => .error s!"l4block-shard-pack UTF-8 error: {message}"
  | .ok _ =>
      if state.digest.finishWith state.blocks != state.expected then
        .error "l4block-shard-pack input changed between pre-pass and parse pass"
      else
        match quadStreamFinish (sourceMode state.format) state.stream with
        | .error e => .error s!"l4block-shard-pack parse error at {e.pos}: {e.msg}"
        | .ok acc =>
            let runs := acc.readyRev.reverse ++
              (L4Factoidal.Storage.PredicateQuadBlocks.pubFlush acc.pub 0).2
            match publishQuadBlocks state.hasher state.format state.scope state.packed []
                runs with
            | .error message => .error message
            | .ok (packed, artifacts) =>
                .ok { graphs := acc.graphs.size + 1
                      batches := state.batches + 1
                      packed := packed
                      artifacts := artifacts }


/-- Which grammars the streaming IBK4 route reads. TriG stays buffered: it
    has no chunk fold at all, so there is nothing to stream it with. -/
def quadStreams : PackSyntax → Bool
  | .nquads | .turtle | .ntriples => true
  | .trig => false

/-- The TSV header. SBM10 adds three columns: the first eight bytes of each
    zone-map bound, and how many out-of-line literals the block names. An SBM9
    generation keeps exactly the eleven columns it had, so a version-9
    generation packed after this change is byte-identical to one packed
    before it. -/
def quadManifestTsvHeader : PackFormat → String
  | .ibk5 =>
      "# index\tpredicate\tfile\trows\tbytes\tsha256\tmerkle-leaves\tgraphs\tgraph-set\tliteral-index\tgeo-index\tsubject-zone\tobject-zone\tblobs\n"
  | _ =>
      "# index\tpredicate\tfile\trows\tbytes\tsha256\tmerkle-leaves\tgraphs\tgraph-set\tliteral-index\tgeo-index\n"

/-! ## Blob references become blob-table positions

An entry holds the DIGESTS of its out-of-line literals while the pass runs,
because the manifest blob table is not complete until the pass ends and a
position in it is not defined before then. SBM10 stores positions rather than
digests so one entry costs four bytes per blob instead of thirty-two. -/

/-- The positions of one entry's digests in the final blob table. `none` when
    a digest is not in the table, which is a packer fault rather than an
    admissible generation. The result is ascending because the table is
    ascending by digest and `blobDigests` is too. -/
def blobPositions? (table : List ArtifactRef) (digests : List ByteArray) : Option (List Nat) :=
  digests.mapM fun digest =>
    table.findIdx? fun ref => ref.sha256.toList == digest.toList

/-- Attach each entry's blob positions. The two lists are parallel: the packer
    pushes one digest list per entry it pushes. -/
def withBlobRefs (table : List ArtifactRef) :
    List Entry → List (List ByteArray) → Option (List Entry)
  | [], [] => some []
  | entry :: entries, digests :: rest => do
      let refs ← blobPositions? table digests
      let tail ← withBlobRefs table entries rest
      some ({ entry with blobRefs := refs } :: tail)
  | _, _ => none

/-- The manifest and the TSV of a finished quad `PackState`: SBM9 for the
    IBK4 format, SBM10 for IBK5, where the blob table is published and each
    entry's digest list becomes positions in it. -/
def quadManifestArtifacts (format : PackFormat) (prepass : SourcePrepass) (state : PackState) :
    Except String (List Artifact) :=
  let entries := state.entriesRev.reverse
  match (if format == .ibk5 then
           withBlobRefs state.blobs entries state.entryBlobsRev.reverse
         else some entries) with
  | none => .error "a block named an out-of-line literal that is not in the blob table"
  | some entries =>
      let manifest : Manifest :=
        { version := manifestVersion format
          sourceIdentity := prepass.sourceIdentity
          termRegistryVersion := registryVersion format
          layout := layoutName format
          blankNodeProfile := "content-digest-shared"
          entries := entries
          blobs := if format == .ibk5 then state.blobs else [] }
      match L4Factoidal.Storage.ShardManifest.encode? manifest with
      | none =>
          .error s!"could not encode structurally valid SBM{manifestVersion format} manifest"
      | some manifestBytes =>
          .ok [{ name := "manifest.sbm2", bytes := manifestBytes },
               { name := "manifest.tsv",
                 bytes := (manifestTsv (quadManifestTsvHeader format) state.linesRev).toUTF8 }]

end L4Factoidal.Storage.PackStream
