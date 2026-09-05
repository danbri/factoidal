/- Persist one independently decodable IBK2/IBK3 artifact per predicate, with
   both a human-inspectable TSV and a strict host-neutral SBM manifest.

   The packer itself is pure and lives in
   `L4Factoidal/Storage/PackStream.lean`. This file is the native host: it
   opens the input, hands chunks to the fold, and writes every artifact the
   fold gives back. It decides no name, no digest and no byte layout, so the
   same fold runs unchanged inside the WebAssembly module, which has no file
   I/O.

   The IBK4 path below streams the N-Quads grammar through
   `PackStream.quadIngestFeed` and reads the whole input with `IO.FS.readFile`
   only for TriG, Turtle and N-Triples, which have no chunk fold yet. Its
   blocks, sidecars and manifest are decided by `PackStream.quadArtifacts`,
   `PackStream.quadIngestFinish` and `PackStream.quadManifestArtifacts` like
   everything else here. -/
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
    the pure Lean specification hasher's output. The source-file identity
    the pure fold streams runs `Sha256Stream` over `blockFold` below, which
    is the same HACL* C compression walk; before 2026-09-05 it ran the pure
    Lean walk and that was the single largest cost in a pack. -/
private def hasher : L4Factoidal.Storage.BlockMerkle.Hasher := nativeHasher

/-- The SHA-256 compression walk of the source-identity digest. The pure Lean
    walk is the specification and is what the WebAssembly packer runs; this
    native host passes HACL* C, which is the same fold at C speed. The
    pre-pass and the ingest pass each stream every input byte through it, so
    on a 104,857,577-byte N-Quads source it was the single largest cost in
    the pack: 14,162 of the pre-pass's 21,806 leaf samples
    (`/usr/bin/sample`, 2026-09-05). -/
private def blockFold : L4Factoidal.Crypto.BlockFold256 := nativeBlockFold256

private def ofExcept (result : Except String α) : IO α :=
  match result with
  | .error message => throw <| IO.userError message
  | .ok value => pure value

private def writeArtifacts (output : String) (artifacts : List Artifact) : IO Unit :=
  artifacts.forM fun artifact =>
    IO.FS.writeBinFile (output ++ "/" ++ artifact.name) artifact.bytes

/-- Read the input in `inputChunkBytes` chunks and fold. Host I/O is
    deliberately tail-recursive/`partial`; it is not semantic parser
    recursion. Every decision is in `PackStream`, whose folds this drives:
    the pre-pass, the IBK2/IBK3 ingest and the IBK4 N-Quads ingest all read
    the file the same way and differ only in `feed`. -/
private partial def foldHandle {α : Type} (handle : IO.FS.Handle)
    (feed : α → ByteArray → IO α) (state : α) : IO α := do
  let bytes ← handle.read inputChunkBytes
  if bytes.isEmpty then pure state
  else foldHandle handle feed (← feed state bytes)

private def prepassFile (input : System.FilePath) : IO SourcePrepass :=
  IO.FS.withFile input .read fun handle => do
    let state ← foldHandle handle (fun state bytes => ofExcept (prepassFeed state bytes))
      (prepassInit blockFold)
    ofExcept (prepassFinish state)

/-- The second pass: read a chunk, feed it, write whatever completed. -/
private def ingestFile (format : PackFormat) (input output : System.FilePath)
    (prepass : SourcePrepass) : IO PackState :=
  IO.FS.withFile input .read fun handle => do
    let state ← foldHandle handle
      (fun state bytes => do
        let (next, artifacts) ← ofExcept (ingestFeed state bytes)
        writeArtifacts output.toString artifacts
        pure next)
      (ingestInit hasher format prepass (some ("file://" ++ input.toString)) blockFold)
    let (packed, artifacts) ← ofExcept (ingestFinish state)
    writeArtifacts output.toString artifacts
    pure packed

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

The IBK4 packer publishes blocks DURING the ingest pass
(`docs/designissues/2026-09-05-pack-publication-every-batch.md`). A block is
written as soon as the per-block cut rule closes its rows, every open run of
at least `minBatchRows` rows is written at each `--batch-bytes` of source, and
every open run is written at the end. `quadIngestFeed` returns the artifacts
of one feed in the order they must be written, and `quadIngestFile` below
writes them before it reads the next chunk, so the generation is never live
all at once. Several blocks per predicate is what SBM2 has always admitted: a
reader takes the union of the entries for a predicate.

What the input no longer decides is the CHARACTER LIST. For the N-Quads
grammar `quadIngestFile` below feeds 65,536-byte chunks to
`PackStream.quadIngestFeed`, so neither the source `String` nor its
`String.toList` — about twenty-four bytes per source byte — is ever built.
Measured on 104,017,780 bytes of N-Quads over 50 named graphs: peak memory
footprint 2,531,999,744 bytes before, 1,127,907,328 bytes after, with a
byte-identical generation
(<https://github.com/danbri/factoidal/issues/650>). Turtle and N-Triples
take the same route through the Turtle chunk fold; only TriG still buffers,
because it has no chunk fold. Publication every batch then took the same
104,857,577-byte prefix of skosdex from 599,870,336 bytes of peak footprint
to 328,272,128. What is proved and what is only measured for each route is
stated at `PackStream`'s streaming section.

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

/-- The streaming IBK4 second pass. The source `String` and its `List Char`
    never exist; only one 65,536-byte chunk is decoded at a time, and each
    feed's artifacts are written before the next chunk is read, so the
    generation is never live all at once. -/
private def quadIngestFile (input : System.FilePath) (output : System.FilePath)
    (grammar : PackSyntax) (prepass : SourcePrepass) (baseIri : Option String)
    (batchBytes : Nat) : IO QuadPack :=
  IO.FS.withFile input .read fun handle => do
    let state ← foldHandle handle
      (fun state bytes => do
        let (next, artifacts) ← ofExcept (quadIngestFeed state bytes)
        writeArtifacts output.toString artifacts
        pure next)
      (quadIngestInit hasher grammar prepass baseIri batchBytes blockFold)
    let result ← ofExcept (quadIngestFinish state)
    writeArtifacts output.toString result.artifacts
    pure { result with artifacts := [] }

private def packQuads (input output : String) (batchBytes : Nat) : IO UInt32 := do
  try
    let prepass ← prepassFile input
    let outputPath := System.FilePath.mk output
    if ← (outputPath / "manifest.sbm2").pathExists then
      throw <| IO.userError s!"refusing to replace committed collection at {output}; choose a fresh output directory"
    IO.FS.createDirAll outputPath
    let grammar := syntaxOf input
    let baseIri := some ("file://" ++ input)
    let result ←
      if quadStreams grammar then
        quadIngestFile input outputPath grammar prepass baseIri batchBytes
      else do
        let text ← IO.FS.readFile input
        let buffered ← ofExcept (quadArtifacts hasher grammar prepass text baseIri)
        writeArtifacts output buffered.artifacts
        pure { buffered with artifacts := [] }
    let manifest ← ofExcept (quadManifestArtifacts prepass result.packed)
    writeArtifacts output manifest
    IO.println s!"l4block-shard-pack format={layoutName .ibk4} syntax={syntaxName grammar} input={input} quads={result.packed.tripleCount} blocks={result.packed.entriesRev.length} graphs={result.graphs} batches={result.batches} batch-bytes={batchBytes} output={output} manifest=manifest.sbm2 wire-version={manifestVersion .ibk4} blank-node-scope={bytesToHex prepass.sourceIdentity} chunk-bytes={chunkBytes}"
    return 0
  catch error =>
    IO.eprintln s!"l4block-shard-pack failure: {error}"
    return 1

/-- Read `--batch-bytes N` out of the tail arguments. `none` is a malformed
    or missing value; the caller then reports the usage line rather than
    packing with a number nobody asked for. -/
private def batchBytesOf : List String → Option Nat
  | [] => some L4Factoidal.Storage.PredicateQuadBlocks.batchSourceBytesDefault
  | ["--batch-bytes", value] => value.toNat?.filter (· > 0)
  | _ => none

def main (args : List String) : IO UInt32 := do
  match args with
  | [input, output] => try pack .ibk2 input output catch e => IO.eprintln s!"l4block-shard-pack failure: {e}"; return 1
  | [input, output, "ibk3"] => try pack .ibk3 input output catch e => IO.eprintln s!"l4block-shard-pack failure: {e}"; return 1
  | input :: output :: "ibk4" :: rest =>
      match batchBytesOf rest with
      | none =>
          IO.eprintln "l4block-shard-pack: --batch-bytes needs one positive decimal argument"
          return 2
      | some batchBytes =>
          try packQuads input output batchBytes
          catch e => IO.eprintln s!"l4block-shard-pack failure: {e}"; return 1
  | _ => IO.eprintln "usage: l4block-shard-pack INPUT OUTPUT-DIR [ibk3|ibk4] [--batch-bytes N]  (ibk4 accepts .ttl, .trig, .nq, .nt)"; return 2

end Harness.PredicateShardPack
def main (args : List String) : IO UInt32 := Harness.PredicateShardPack.main args
