/-
Wasm.Main — a native command-line driver for the same ABI the wasm
module exposes.

Purpose: it lets the ABI be exercised and diffed WITHOUT a working wasm
toolchain, so an ABI bug and a toolchain bug can never be confused for
one another. The wasm build and this executable call exactly the same
`L4Wasm.bgpQuery`.

  lake exe l4wasm-cli version
  lake exe l4wasm-cli bgp <data.json> <bgp.json>
  lake exe l4wasm-cli call <op> <argsJsonFile>
  lake exe l4wasm-cli callblob <op> <argsJsonFile> <blobFile>
  lake exe l4wasm-cli callseq <seqJsonFile>

`call` drives the dispatch ABI (`Wasm/Dispatch.lean`): `<op>` is the
method name and `<argsJsonFile>` holds a JSON array of strings — the
same two strings `l4_call_c` carries across the wasm boundary. It
routes through `L4Wasm.callIO`, exactly as the shim does, so the
dataset-handle ops answer their envelopes here too — but handle state
dies with the process, so a DEPENDENT sequence (open → query → close)
needs `callseq`: `<seqJsonFile>` holds a JSON array of `[op, [arg, …]]`
pairs, run in order in this one process, one envelope printed per line.

`callblob` is the native form of the wasm module's `l4_call_blob_c`: the
same op name and args document, plus ONE contiguous byte region, read here
from `<blobFile>` and written by a browser host straight into the wasm heap.
It serves the ops of `L4Wasm.blobOpNames` (`storeQuery`, `activateVerify`),
whose block bytes are too large for the string ABI, and delegates every other
op to the pure `call`.

  lake exe l4wasm-cli pack <input> <output-dir> <syntaxTag> <layoutTag>

`pack` is the byte-identity driver for the pack operations
(`Wasm/Ops/Pack.lean`). It reaches the packer ONLY through
`L4Wasm.callBlobIO` and `L4Wasm.callIO` — the same two entries the wasm shim
serves — so a generation it writes is a generation the module would write.
Its purpose is the gate: the directory it fills must be byte for byte what
`lake exe l4block-shard-pack` writes for the same input.

    lake exe l4wasm-cli pack corpus.ttl /tmp/w /tmp/g turtle ibk3
    lake exe l4block-shard-pack corpus.ttl /tmp/n ibk3
    diff -r /tmp/g /tmp/n

Every loop here is fuel-bounded rather than `partial`: a source above the
fuel is an error naming it, never a silent stop.
-/
import Wasm.Exports

open L4Factoidal.JSON

/-- One chunk per feed. The native packer reads 65,536 bytes at a time and
    the JavaScript host feeds the same, which is what keeps the two folds in
    step and the byte-identity gate meaningful. -/
private def packChunkBytes : USize := 65536

/-- Fuel for the feed loop: 65,536 chunks of 65,536 bytes is 4 GiB, above
    what a 32-bit module addresses. -/
private def packFeedFuel : Nat := 65536

/-- Fuel for the artifact drain: a generation with more artifacts than this
    is an error naming the fuel. -/
private def packDrainFuel : Nat := 1000000

private def argsOf (values : List String) : String :=
  (Json.array (values.map Json.string)).toString

private def field? (envelope field : String) : Option Json :=
  match parseJson envelope with
  | .ok (.object members) => (members.find? (fun m => m.1 == field)).map Prod.snd
  | _ => none

private def expectOk (op envelope : String) : IO Unit :=
  match field? envelope "ok" with
  | some (.bool true) => pure ()
  | _ => throw <| IO.userError s!"l4wasm-cli pack: {op} answered {envelope}"

/-- Take every artifact the module has ready and write it under the name the
    module gave it. This decides no name, no digest and no byte. -/
private def drainArtifacts (handle output : String) : Nat → Nat → IO Nat
  | 0, _ => throw <| IO.userError s!"l4wasm-cli pack: more than {packDrainFuel} artifacts"
  | Nat.succ fuel, written => do
      let (envelope, bytes) ← L4Wasm.callBlobIO "packNext" (argsOf [handle]) ByteArray.empty
      expectOk "packNext" envelope
      match field? envelope "done" with
      | some (.bool true) => pure written
      | _ =>
          match field? envelope "name" with
          | some (.string name) => do
              IO.FS.writeBinFile (output ++ "/" ++ name) bytes
              drainArtifacts handle output fuel (written + 1)
          | _ =>
              throw <| IO.userError s!"l4wasm-cli pack: packNext answered {envelope}"

private def feedPass (input : IO.FS.Handle) (handle output : String) :
    Nat → Nat → IO Nat
  | 0, _ => throw <| IO.userError s!"l4wasm-cli pack: source above {packFeedFuel} chunks"
  | Nat.succ fuel, written => do
      let chunk ← input.read packChunkBytes
      if chunk.isEmpty then pure written
      else do
        let (envelope, _) ← L4Wasm.callBlobIO "packFeed" (argsOf [handle]) chunk
        expectOk "packFeed" envelope
        let more ← drainArtifacts handle output packDrainFuel 0
        feedPass input handle output fuel (written + more)

private def packThroughOps (input output syntaxTag layoutTag : String) : IO UInt32 := do
  IO.FS.createDirAll (System.FilePath.mk output)
  let begun ← L4Wasm.callIO "packBegin" (argsOf [syntaxTag, layoutTag])
  expectOk "packBegin" begun
  let handle ← match field? begun "handle" with
    | some (.string h) => pure h
    | _ => throw <| IO.userError s!"l4wasm-cli pack: packBegin answered {begun}"
  let mut written := 0
  for _pass in [0, 1] do
    written := written + (← IO.FS.withFile input .read fun file =>
      feedPass file handle output packFeedFuel 0)
    let ended ← L4Wasm.callIO "packEndPass" (argsOf [handle])
    expectOk "packEndPass" ended
    written := written + (← drainArtifacts handle output packDrainFuel 0)
  let finished ← L4Wasm.callIO "packFinish" (argsOf [handle])
  expectOk "packFinish" finished
  written := written + (← drainArtifacts handle output packDrainFuel 0)
  let closed ← L4Wasm.callIO "packClose" (argsOf [handle])
  expectOk "packClose" closed
  IO.println s!"l4wasm-cli pack input={input} output={output} syntax={syntaxTag} layout={layoutTag} artifacts={written} finish={finished}"
  return 0

def main (args : List String) : IO UInt32 := do
  match args with
  | ["version"] =>
      IO.println (L4Wasm.version)
      return 0
  | ["bgp", dataFile, bgpFile] =>
      let data ← IO.FS.readFile dataFile
      let bgp ← IO.FS.readFile bgpFile
      IO.println (L4Wasm.bgpQuery data bgp)
      return 0
  | ["call", op, argsFile] =>
      let argsJson ← IO.FS.readFile argsFile
      IO.println (← L4Wasm.callIO op argsJson)
      return 0
  | ["callblob", op, argsFile, blobFile] =>
      let argsJson ← IO.FS.readFile argsFile
      let blob ← IO.FS.readBinFile blobFile
      IO.println (L4Wasm.callBlob op argsJson blob)
      return 0
  | ["pack", input, output, syntaxTag, layoutTag] =>
      try packThroughOps input output syntaxTag layoutTag
      catch e => IO.eprintln s!"l4wasm-cli pack failure: {e}"; return 1
  | ["callseq", seqFile] =>
      let seqJson ← IO.FS.readFile seqFile
      match L4Wasm.decodeCallSeq seqJson with
      | .error e =>
          IO.eprintln s!"callseq: {e}"
          return 1
      | .ok pairs =>
          for (op, argsJson) in pairs do
            IO.println (← L4Wasm.callIO op argsJson)
          return 0
  | _ =>
      IO.eprintln "usage: l4wasm-cli (version | bgp <data.json> <bgp.json> | call <op> <argsJsonFile> | callblob <op> <argsJsonFile> <blobFile> | callseq <seqJsonFile> | pack <input> <outputDir> <syntaxTag> <layoutTag>)"
      return 1
