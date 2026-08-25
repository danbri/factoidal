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

`call` drives the dispatch ABI (`Wasm/Dispatch.lean`): `<op>` is the
method name and `<argsJsonFile>` holds a JSON array of strings — the
same two strings `l4_call_c` carries across the wasm boundary.
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
      IO.println (L4Wasm.call op argsJson)
      return 0
  | _ =>
      IO.eprintln "usage: l4wasm-cli (version | bgp <data.json> <bgp.json> | call <op> <argsJsonFile>)"
      return 1
