/-
Wasm.Main — a native command-line driver for the same ABI the wasm
module exposes.

Purpose: it lets the ABI be exercised and diffed WITHOUT a working wasm
toolchain, so an ABI bug and a toolchain bug can never be confused for
one another. The wasm build and this executable call exactly the same
`L4Wasm.bgpQuery`.

  lake exe l4wasm-cli version
  lake exe l4wasm-cli bgp <data.json> <bgp.json>
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
  | _ =>
      IO.eprintln "usage: l4wasm-cli (version | bgp <data.json> <bgp.json>)"
      return 1
