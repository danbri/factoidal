/- Persist one independently decodable IBK2/IBK3 artifact per predicate, with
   both a human-inspectable TSV and a strict host-neutral SBM manifest.

   The packer itself is pure and lives in
   `L4Factoidal/Storage/PackStream.lean`. This file is the native host: it
   opens the input, hands chunks to the fold, and writes every artifact the
   fold gives back. It decides no name, no digest and no byte layout, so the
   same fold runs unchanged inside the WebAssembly module, which has no file
   I/O.

   The IBK4 path below still reads the whole input with `IO.FS.readFile`,
   because an IBK4 block commits a graph-set summary over the whole source;
   lifting it needs the streaming TriG fold and is separate work. Its blocks,
   sidecars and manifest are decided by `PackStream.quadArtifacts` and
   `PackStream.quadManifestArtifacts` like everything else here. -/
import L4Factoidal.Storage.PackStream
import L4Factoidal.Storage.PredicateQuadBlocks
import L4Factoidal.Storage.IndexedBlockWireV4
import L4Factoidal.Syntax.Turtle
import L4Factoidal.Syntax.TriG
import L4Factoidal.Syntax.NQuadsFast
import Harness.NativeHasher

namespace Harness.PredicateShardPack

open L4Factoidal.Syntax
open L4Factoidal.Storage.ShardManifest
open L4Factoidal.Storage.PackStream
open L4Factoidal.Crypto

private def inputChunkBytes : USize := 65536

/-- The published leaves and artifact digests are hashed with
    `Harness.nativeHasher` (HACL* C). The committed bytes are identical to
    the pure Lean specification hasher's output; the source-file identity
    the pure fold streams still uses the pure incremental `Sha256Stream`,
    which has no streaming HACL* counterpart bound here. -/
private def hasher : L4Factoidal.Storage.BlockMerkle.Hasher := nativeHasher

private def ofExcept (result : Except String α) : IO α :=
  match result with
  | .error message => throw <| IO.userError message
  | .ok value => pure value

private def writeArtifacts (output : String) (artifacts : List Artifact) : IO Unit :=
  artifacts.forM fun artifact =>
    IO.FS.writeBinFile (output ++ "/" ++ artifact.name) artifact.bytes

/-- Host I/O is deliberately tail-recursive/`partial`; it is not semantic
    parser recursion. Every decision is in `PackStream.prepass*`. -/
private partial def prepassHandle (handle : IO.FS.Handle) (state : PrepassState) :
    IO SourcePrepass := do
  let bytes ← handle.read inputChunkBytes
  if bytes.isEmpty then ofExcept (prepassFinish state)
  else prepassHandle handle (← ofExcept (prepassFeed state bytes))

private def prepassFile (input : System.FilePath) : IO SourcePrepass :=
  IO.FS.withFile input .read fun handle => prepassHandle handle prepassInit

/-- The second pass: read a chunk, feed it, write whatever completed. -/
private partial def ingestHandle (handle : IO.FS.Handle) (output : String)
    (state : IngestState) : IO PackState := do
  let bytes ← handle.read inputChunkBytes
  if bytes.isEmpty then do
    let (packed, artifacts) ← ofExcept (ingestFinish state)
    writeArtifacts output artifacts
    pure packed
  else do
    let (next, artifacts) ← ofExcept (ingestFeed state bytes)
    writeArtifacts output artifacts
    ingestHandle handle output next

private def ingestFile (format : PackFormat) (input output : System.FilePath)
    (prepass : SourcePrepass) : IO PackState :=
  IO.FS.withFile input .read fun handle =>
    ingestHandle handle output.toString
      (ingestInit hasher format prepass (some ("file://" ++ input.toString)))

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
       is published only after the second-pass source digest agreed, which
       `ingestFinish` checked. -/
    let manifest ← ofExcept (manifestArtifacts format prepass published)
    writeArtifacts output manifest
    IO.println s!"l4block-shard-pack format={layoutName format} input={input} triples={published.tripleCount} blocks={published.entriesRev.length} output={output} manifest=manifest.sbm2 wire-version={manifestVersion format} chunk-bytes={chunkBytes}"
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

Every block, sidecar and manifest byte is decided by
`PackStream.quadArtifacts` and `PackStream.quadManifestArtifacts`, which are
pure and are what the WebAssembly pack operations run. This file only reads
the input and writes what it is given.

The input grammar is chosen by file extension: `.trig` is TriG, `.nq` and
`.nquads` are N-Quads, `.nt` is N-Triples, and anything else is Turtle, whose
triples all land in the default graph. -/

private def syntaxOf (input : String) : PackSyntax :=
  if input.endsWith ".trig" then .trig
  else if input.endsWith ".nq" || input.endsWith ".nquads" then .nquads
  else if input.endsWith ".nt" then .ntriples
  else .turtle

private def packQuads (input output : String) : IO UInt32 := do
  try
    let prepass ← prepassFile input
    let outputPath := System.FilePath.mk output
    if ← (outputPath / "manifest.sbm2").pathExists then
      throw <| IO.userError s!"refusing to replace committed collection at {output}; choose a fresh output directory"
    IO.FS.createDirAll outputPath
    let text ← IO.FS.readFile input
    let grammar := syntaxOf input
    let result ← ofExcept
      (quadArtifacts hasher grammar prepass text (some ("file://" ++ input)))
    writeArtifacts output result.artifacts
    let manifest ← ofExcept (quadManifestArtifacts prepass result.packed)
    writeArtifacts output manifest
    IO.println s!"l4block-shard-pack format={layoutName .ibk4} syntax={syntaxName grammar} input={input} quads={result.packed.tripleCount} blocks={result.packed.entriesRev.length} graphs={result.graphs} output={output} manifest=manifest.sbm2 wire-version=7 blank-node-scope={bytesToHex prepass.sourceIdentity} chunk-bytes={chunkBytes}"
    return 0
  catch error =>
    IO.eprintln s!"l4block-shard-pack failure: {error}"
    return 1

def main (args : List String) : IO UInt32 := do
  match args with
  | [input, output] => try pack .ibk2 input output catch e => IO.eprintln s!"l4block-shard-pack failure: {e}"; return 1
  | [input, output, "ibk3"] => try pack .ibk3 input output catch e => IO.eprintln s!"l4block-shard-pack failure: {e}"; return 1
  | [input, output, "ibk4"] => try packQuads input output catch e => IO.eprintln s!"l4block-shard-pack failure: {e}"; return 1
  | _ => IO.eprintln "usage: l4block-shard-pack INPUT OUTPUT-DIR [ibk3|ibk4]  (ibk4 accepts .ttl, .trig, .nq, .nt)"; return 2

end Harness.PredicateShardPack
def main (args : List String) : IO UInt32 := Harness.PredicateShardPack.main args
