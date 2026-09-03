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
It serves the ops of `L4Wasm.blobOpNames` (`storeQuery`), whose block bytes
are too large for the string ABI, and delegates every other op to the pure
`call`.
-/
import Wasm.Exports

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
      IO.eprintln "usage: l4wasm-cli (version | bgp <data.json> <bgp.json> | call <op> <argsJsonFile> | callblob <op> <argsJsonFile> <blobFile> | callseq <seqJsonFile>)"
      return 1
