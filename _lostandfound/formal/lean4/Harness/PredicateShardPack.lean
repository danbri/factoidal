/- Persist one independently decodable IBK2 artifact per predicate, with both
   a human-inspectable TSV and a strict host-neutral SBM0 Shardborough
   manifest. -/
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
import L4Factoidal.Syntax.Turtle
import L4Factoidal.Syntax.TriG
import L4Factoidal.Syntax.NQuadsFast
import L4Factoidal.Syntax.Utf8Stream
import L4Factoidal.Syntax.TurtleChunkFold
import L4Factoidal.Crypto.SHA2
import Harness.NativeHasher

namespace Harness.PredicateShardPack

open L4Factoidal.Syntax
open L4Factoidal.Storage.PredicateBlocks
open L4Factoidal.Storage.IndexedBlockWireV2
open L4Factoidal.Storage.ShardManifest
open L4Factoidal.Storage.ChunkedArtifact
open L4Factoidal.Crypto

private def chunkBytes : Nat := 65536
private def inputChunkBytes : USize := 65536
/-- Keep decoding latency small while publishing roughly four MiB batches.
    This is a bounded first block-sizing policy; later compaction may use
    measured encoded-byte targets rather than source-byte batches. -/
private def publicationChunkCount : Nat := 64

private inductive PackFormat where
  | ibk2
  | ibk3
  | ibk4

private def artifactName : PackFormat → Nat → String
  | .ibk2, ordinal => s!"predicate-{ordinal}.ibk2"
  | .ibk3, ordinal => s!"predicate-{ordinal}.ibk3"
  | .ibk4, ordinal => s!"predicate-{ordinal}.ibk4"

private def layoutName : PackFormat → String
  | .ibk2 => "predicate-ibk2-merkle-v2-streaming"
  | .ibk3 => "predicate-ibk3-ptd1-sri2-tli1-oli2-merkle-v0"
  | .ibk4 => "quad-ibk4-ptd1-merkle-v0"

private def registryVersion : PackFormat → String
  | .ibk2 => "local-ibk2-dict-v0"
  | .ibk3 => "local-ibk3-ptd1-v0"
  | .ibk4 => "local-ibk4-ptd1-v0"

private def encodeBlock? : PackFormat → L4Factoidal.Storage.IndexedBlock.Block → Option ByteArray
  | .ibk2, block => L4Factoidal.Storage.IndexedBlockWireV2.encode? block
  | .ibk3, block => L4Factoidal.Storage.IndexedBlockWireV3.encode? block
  | .ibk4, _ => none

/-- The published leaves and artifact digests are hashed with
    `Harness.nativeHasher` (HACL* C). The committed bytes are identical to
    the pure Lean specification hasher's output; the source-file identity a
    few lines below still uses the pure incremental `Sha256Stream`, which
    has no streaming HACL* counterpart bound here. -/
private def writeMerkle (path : String) (bytes : ByteArray) : IO Unit := do
  let leaves := (chunksOf chunkBytes bytes).map
    (L4Factoidal.Storage.BlockMerkle.leafWith nativeHasher)
  let proofBytes := ByteArray.mk (leaves.flatMap (fun value => value.data.toList) |>.toArray)
  IO.FS.writeBinFile (path ++ ".merkle") proofBytes

private def artifactRef? (name : String) (bytes : ByteArray) : Option ArtifactRef := do
  let chunked ← fromChunksWith? nativeHasher chunkBytes (chunksOf chunkBytes bytes)
  some { key := { value := name }, bytes := bytes.size, sha256 := nativeSha256 bytes, chunked := some chunked }

/-- Bounded first-pass information needed to preserve the reference packer's
    generated-blank-node and source-identity contracts. -/
private structure SourcePrepass where
  bnodePrefix : String
  sourceIdentity : ByteArray

/-- Host I/O is deliberately tail-recursive/`partial`; it is not semantic
    parser recursion. Each iteration retains only UTF-8 carry, underscore-run
    state and SHA-256 state. -/
private partial def prepassHandle (handle : IO.FS.Handle) (utf8 : Utf8Stream)
    (underscores : UnderscoreRun) (digest : Sha256Stream) : IO SourcePrepass := do
  let bytes ← handle.read inputChunkBytes
  if bytes.isEmpty then
    match utf8.finish with
    | .error message => throw <| IO.userError s!"l4block-shard-pack UTF-8 error: {message}"
    | .ok _ =>
        pure { bnodePrefix := freshBnodePrefixOfLongest underscores.longest
               sourceIdentity := digest.finish }
  else
    match utf8.feed bytes with
    | .error message => throw <| IO.userError s!"l4block-shard-pack UTF-8 error: {message}"
    | .ok (text, nextUtf8) =>
        prepassHandle handle nextUtf8 (underscores.feedChars text.toList) (digest.update bytes)

private def prepassFile (input : System.FilePath) : IO SourcePrepass :=
  IO.FS.withFile input .read fun handle => prepassHandle handle Utf8Stream.init {} Sha256Stream.init

/- The fold accumulator is deliberately a reverse list of triples completed
   since the current decoded input chunk.  It is reset after publication, so
   the packer never builds a graph-wide predicate map in memory. -/
private def ingestStep (accRev : List L4Factoidal.RDF.Triple)
    (triples : List L4Factoidal.RDF.Triple) : List L4Factoidal.RDF.Triple :=
  triples.reverse ++ accRev

/-- Publication metadata is small even for a large source: one manifest row
    and one TSV row per immutable output block, never the source triples. -/
private structure PackState where
  tripleCount : Nat := 0
  nextOrdinal : Nat := 0
  entriesRev : List Entry := []
  linesRev : List String := []

private def publishBlocks (format : PackFormat) (output : String) : PackState → List (L4Factoidal.RDF.WfIri × L4Factoidal.Storage.IndexedBlock.Block) → IO PackState
  | state, [] => pure state
  | state, (predicate, block) :: rest => do
      match encodeBlock? format block with
      | none => throw <| IO.userError s!"unsupported block for {predicate.val}"
      | some bytes =>
          let ordinal := state.nextOrdinal
          let name := artifactName format ordinal
          IO.FS.writeBinFile (output ++ "/" ++ name) bytes
          let artifact ← match artifactRef? name bytes with
            | some value => pure value
            | none => throw <| IO.userError s!"could not commit fixed chunks for {predicate.val}"
          writeMerkle (output ++ "/" ++ name) bytes
          let subjectIndex ← match format with
            | .ibk2 | .ibk4 => pure none
            | .ibk3 =>
                let index : L4Factoidal.Storage.SubjectRowIndexWireV2.Index :=
                  { targetIBKSha256 := artifact.sha256
                    rowCount := block.rows.size
                    pairs := L4Factoidal.Storage.SubjectRowIndexWire.pairsOfRows block.rows |>.toArray }
                match L4Factoidal.Storage.SubjectRowIndexWireV2.encode? index with
                | none => throw <| IO.userError s!"could not encode SRI2 index for {predicate.val}"
                | some indexBytes =>
                    let indexName := name ++ ".sri2"
                    IO.FS.writeBinFile (output ++ "/" ++ indexName) indexBytes
                    writeMerkle (output ++ "/" ++ indexName) indexBytes
                    match artifactRef? indexName indexBytes with
                    | some value => pure (some value)
                    | none => throw <| IO.userError s!"could not commit SRI2 chunks for {predicate.val}"
          let termIndex ← match format with
            | .ibk2 | .ibk4 => pure none
            | .ibk3 =>
                let index : L4Factoidal.Storage.TermLocalIndexWire.Index :=
                  { targetIBKSha256 := artifact.sha256
                    entries := L4Factoidal.Storage.TermLocalIndex.entriesOf block.dict }
                match L4Factoidal.Storage.TermLocalIndexWire.encode? index with
                | none => throw <| IO.userError s!"could not encode TLI1 index for {predicate.val}"
                | some indexBytes =>
                    let indexName := name ++ ".tli1"
                    IO.FS.writeBinFile (output ++ "/" ++ indexName) indexBytes
                    writeMerkle (output ++ "/" ++ indexName) indexBytes
                    match artifactRef? indexName indexBytes with
                    | some value => pure (some value)
                    | none => throw <| IO.userError s!"could not commit TLI1 chunks for {predicate.val}"
          /- OLI2 uses the same canonical pageable `(local ID, row offset)`
             framing as SRI2, but is published in SBM6's distinct
             `objectIndex` role and recomputed against row.o at activation. -/
          let objectIndex ← match format with
            | .ibk2 | .ibk4 => pure none
            | .ibk3 =>
                let index : L4Factoidal.Storage.SubjectRowIndexWireV2.Index :=
                  { targetIBKSha256 := artifact.sha256
                    rowCount := block.rows.size
                    pairs := L4Factoidal.Storage.SubjectRowIndexWire.pairsOfObjects block.rows |>.toArray }
                match L4Factoidal.Storage.SubjectRowIndexWireV2.encode? index with
                | none => throw <| IO.userError s!"could not encode OLI2 index for {predicate.val}"
                | some indexBytes =>
                    let indexName := name ++ ".oli2"
                    IO.FS.writeBinFile (output ++ "/" ++ indexName) indexBytes
                    writeMerkle (output ++ "/" ++ indexName) indexBytes
                    match artifactRef? indexName indexBytes with
                    | some value => pure (some value)
                    | none => throw <| IO.userError s!"could not commit OLI2 chunks for {predicate.val}"
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
          publishBlocks format output
            { tripleCount := state.tripleCount + block.rows.size
              nextOrdinal := ordinal + 1
              entriesRev := entry :: state.entriesRev
              linesRev := s!"{ordinal}\t{predicate.val}\t{name}\t{block.rows.size}\t{bytes.size}\t{bytesToHex artifact.sha256}\t{name}.merkle\t{indexName}\t{termIndexName}\t{objectIndexName}" :: state.linesRev }
            rest

/-- Commit all complete statements seen since the prior decoded input chunk.
    A single very large Turtle statement remains an intentional bounded-input
    exception: its grammar requires retaining the unfinished statement. -/
private def publishBatch (format : PackFormat) (output : String) (state : PackState)
    (triples : List L4Factoidal.RDF.Triple) : IO PackState :=
  publishBlocks format output state (blocksOfBuckets (addTriples {} triples))

/-- Second bounded pass: decoded chunks are handed to the grammar-validated
    fold and their completed batches are published immediately. Its
    independently streamed source digest must equal the first-pass commitment
    before the manifest commits any such artifacts into a readable store. -/
private partial def ingestHandle (format : PackFormat) (output : String) (handle : IO.FS.Handle) (expected : ByteArray) (utf8 : Utf8Stream)
    (fold : TurtleChunkFoldState (List L4Factoidal.RDF.Triple)) (digest : Sha256Stream)
    (published : PackState) (chunksSincePublish : Nat) : IO PackState := do
  let bytes ← handle.read inputChunkBytes
  if bytes.isEmpty then
    match utf8.finish with
    | .error message => throw <| IO.userError s!"l4block-shard-pack UTF-8 error: {message}"
    | .ok _ =>
        if digest.finish != expected then
          throw <| IO.userError "l4block-shard-pack input changed between pre-pass and parse pass"
        match fold.finish ingestStep with
        | .error error => throw <| IO.userError s!"l4block-shard-pack Turtle parse error at {error.pos}: {error.msg}"
        | .ok triples => publishBatch format output published triples.reverse
  else
    match utf8.feed bytes with
    | .error message => throw <| IO.userError s!"l4block-shard-pack UTF-8 error: {message}"
    | .ok (text, nextUtf8) =>
        match fold.feed ingestStep text with
        | .error error => throw <| IO.userError s!"l4block-shard-pack Turtle parse error at {error.pos}: {error.msg}"
        | .ok nextFold =>
            let nextCount := chunksSincePublish + 1
            if nextCount < publicationChunkCount then
              ingestHandle format output handle expected nextUtf8 nextFold (digest.update bytes) published nextCount
            else
              let published ← publishBatch format output published nextFold.acc.reverse
              ingestHandle format output handle expected nextUtf8 { nextFold with acc := [] }
                (digest.update bytes) published 0

private def ingestFile (format : PackFormat) (input output : System.FilePath) (prepass : SourcePrepass) : IO PackState :=
  IO.FS.withFile input .read fun handle =>
    let fold := TurtleChunkFoldState.init prepass.bnodePrefix ingestStep []
      (some ("file://" ++ input.toString))
    ingestHandle format output.toString handle prepass.sourceIdentity Utf8Stream.init fold Sha256Stream.init {} 0

private def pack (format : PackFormat) (input output : String) : IO UInt32 := do
  try
    let prepass ← prepassFile input
    let outputPath := System.FilePath.mk output
    if ← (outputPath / "manifest.sbm2").pathExists then
      throw <| IO.userError s!"refusing to replace committed collection at {output}; choose a fresh output directory"
    if ← (outputPath / "manifest.sbm1").pathExists then
      throw <| IO.userError s!"refusing to replace committed legacy collection at {output}; choose a fresh output directory"
    IO.FS.createDirAll outputPath
    let published ← ingestFile format input output prepass
    /- The streaming ingest already wrote its bounded blocks.  Its manifest
       must be published only after the second-pass source digest agrees. -/
    let entries := published.entriesRev.reverse
    let lines := published.linesRev.reverse
    let manifest : Manifest :=
      { version := (match format with | .ibk2 => 2 | .ibk3 => 6 | .ibk4 => 7), sourceIdentity := prepass.sourceIdentity,
        termRegistryVersion := registryVersion format,
        layout := layoutName format, entries }
    match L4Factoidal.Storage.ShardManifest.encode? manifest with
    | none => throw <| IO.userError "could not encode structurally valid SBM2 manifest"
    | some manifestBytes => IO.FS.writeBinFile (output ++ "/manifest.sbm2") manifestBytes
    IO.FS.writeFile (output ++ "/manifest.tsv")
      ("# index\tpredicate\tfile\trows\tbytes\tsha256\tmerkle-leaves\tsubject-index\tterm-index\tobject-index\n" ++ String.intercalate "\n" lines ++ "\n")
    let manifestVersion := match format with | .ibk2 => 2 | .ibk3 => 6 | .ibk4 => 7
    IO.println s!"l4block-shard-pack format={layoutName format} input={input} triples={published.tripleCount} blocks={entries.length} output={output} manifest=manifest.sbm2 wire-version={manifestVersion} chunk-bytes={chunkBytes}"
    return 0
  catch error =>
    IO.eprintln s!"l4block-shard-pack failure: {error}"
    return 1

/-! ## The IBK4 path

The IBK4 packer parses the WHOLE input file before it writes a block. The
streaming Turtle fold of the IBK3 path publishes bounded batches, which works
because an IBK3 block holds one predicate of one graph and a later batch can
open a new block for the same predicate (SBM2 permits several blocks per
predicate). An IBK4 block holds one predicate across ALL graphs and commits its
graph-set summary in the header, so a batch boundary would either split a
predicate across blocks with partial graph sets or need a second pass to
recompute them. The streaming TriG path is the next step; until it lands the
IBK4 packer is bounded by the input size.

The input syntax is chosen by file extension: `.trig` is TriG, `.nq` and
`.nquads` are N-Quads, and anything else is Turtle, whose triples all land in
the default graph. -/

private inductive InputSyntax where
  | turtle
  | trig
  | nquads

private def syntaxOf (input : String) : InputSyntax :=
  if input.endsWith ".trig" then .trig
  else if input.endsWith ".nq" || input.endsWith ".nquads" then .nquads
  else .turtle

private def syntaxName : InputSyntax → String
  | .turtle => "turtle"
  | .trig => "trig"
  | .nquads => "nquads"

private def parseDataset (input : String) (text : String) :
    IO L4Factoidal.RDF.Dataset := do
  let base := some ("file://" ++ input)
  match syntaxOf input with
  | .trig =>
      match L4Factoidal.Syntax.parseTriG text base with
      | .error e => throw <| IO.userError s!"l4block-shard-pack TriG parse error at {e.pos}: {e.msg}"
      | .ok ds => pure ds
  | .nquads =>
      match L4Factoidal.Syntax.parseNQuadsFast text with
      | .error e => throw <| IO.userError s!"l4block-shard-pack N-Quads parse error at {e.pos}: {e.msg}"
      | .ok ds => pure ds
  | .turtle =>
      match L4Factoidal.Syntax.parseTurtle text base with
      | .error e => throw <| IO.userError s!"l4block-shard-pack Turtle parse error at {e.pos}: {e.msg}"
      | .ok graph => pure { default := graph, named := [] }

private def graphSetOf (predicate : L4Factoidal.RDF.WfIri)
    (block : L4Factoidal.Storage.IndexedBlockWireV4.QuadBlock) : IO (List GraphName) := do
  match L4Factoidal.Storage.IndexedBlockWireV4.graphNames? block with
  | none => throw <| IO.userError s!"unresolvable graph name in block for {predicate.val}"
  | some names => pure (names.map GraphName.ofGraphRef)

private def graphSetText (names : List GraphName) : String :=
  String.intercalate "," (names.map fun name =>
    match name with
    | .defaultGraph => "default"
    | .iri value => value.val
    | .bnode label => "_:" ++ label)

private def publishQuadBlocks (output : String) (scope : String) :
    PackState → List (L4Factoidal.RDF.WfIri × L4Factoidal.Storage.IndexedBlockWireV4.QuadBlock) →
    IO PackState
  | state, [] => pure state
  | state, (predicate, block) :: rest => do
      match L4Factoidal.Storage.IndexedBlockWireV4.encode? block with
      | none => throw <| IO.userError s!"unsupported quad block for {predicate.val}"
      | some bytes =>
          let ordinal := state.nextOrdinal
          let name := artifactName .ibk4 ordinal
          IO.FS.writeBinFile (output ++ "/" ++ name) bytes
          let artifact ← match artifactRef? name bytes with
            | some value => pure value
            | none => throw <| IO.userError s!"could not commit fixed chunks for {predicate.val}"
          writeMerkle (output ++ "/" ++ name) bytes
          let graphSet ← graphSetOf predicate block
          let entry : Entry :=
            { predicate
              artifact
              blockLayout := some BlockLayout.ibk4
              blankNodeScope := scope
              graphSet
              rows := block.rows.size
              ordinal }
          publishQuadBlocks output scope
            { tripleCount := state.tripleCount + block.rows.size
              nextOrdinal := ordinal + 1
              entriesRev := entry :: state.entriesRev
              linesRev := s!"{ordinal}\t{predicate.val}\t{name}\t{block.rows.size}\t{bytes.size}\t{bytesToHex artifact.sha256}\t{name}.merkle\t{graphSet.length}\t{graphSetText graphSet}" :: state.linesRev }
            rest

private def packQuads (input output : String) : IO UInt32 := do
  try
    let prepass ← prepassFile input
    let outputPath := System.FilePath.mk output
    if ← (outputPath / "manifest.sbm2").pathExists then
      throw <| IO.userError s!"refusing to replace committed collection at {output}; choose a fresh output directory"
    IO.FS.createDirAll outputPath
    let text ← IO.FS.readFile input
    let dataset ← parseDataset input text
    /- The blank-node scope is the SOURCE FILE's SHA-256, the same digest the
       manifest commits as its source identity. Specification section 2.4.1
       admits a content digest only under a publication profile that says
       repeated imports of those bytes share one blank-node allocation, which
       is what `content-digest-shared` states. -/
    let scope := bytesToHex prepass.sourceIdentity
    let blocks := L4Factoidal.Storage.PredicateQuadBlocks.blocksOfDataset dataset
    let published ← publishQuadBlocks output scope {} blocks
    let entries := published.entriesRev.reverse
    let lines := published.linesRev.reverse
    let manifest : Manifest :=
      { version := 7, sourceIdentity := prepass.sourceIdentity,
        termRegistryVersion := registryVersion .ibk4,
        layout := layoutName .ibk4,
        blankNodeProfile := "content-digest-shared",
        entries }
    match L4Factoidal.Storage.ShardManifest.encode? manifest with
    | none => throw <| IO.userError "could not encode structurally valid SBM7 manifest"
    | some manifestBytes => IO.FS.writeBinFile (output ++ "/manifest.sbm2") manifestBytes
    IO.FS.writeFile (output ++ "/manifest.tsv")
      ("# index\tpredicate\tfile\trows\tbytes\tsha256\tmerkle-leaves\tgraphs\tgraph-set\n" ++
        String.intercalate "\n" lines ++ "\n")
    let graphCount := (dataset.named.length) + 1
    IO.println s!"l4block-shard-pack format={layoutName .ibk4} syntax={syntaxName (syntaxOf input)} input={input} quads={published.tripleCount} blocks={entries.length} graphs={graphCount} output={output} manifest=manifest.sbm2 wire-version=7 blank-node-scope={scope} chunk-bytes={chunkBytes}"
    return 0
  catch error =>
    IO.eprintln s!"l4block-shard-pack failure: {error}"
    return 1

def main (args : List String) : IO UInt32 := do
  match args with
  | [input, output] => try pack .ibk2 input output catch e => IO.eprintln s!"l4block-shard-pack failure: {e}"; return 1
  | [input, output, "ibk3"] => try pack .ibk3 input output catch e => IO.eprintln s!"l4block-shard-pack failure: {e}"; return 1
  | [input, output, "ibk4"] => try packQuads input output catch e => IO.eprintln s!"l4block-shard-pack failure: {e}"; return 1
  | _ => IO.eprintln "usage: l4block-shard-pack INPUT OUTPUT-DIR [ibk3|ibk4]  (ibk4 accepts .ttl, .trig, .nq)"; return 2

end Harness.PredicateShardPack
def main (args : List String) : IO UInt32 := Harness.PredicateShardPack.main args
