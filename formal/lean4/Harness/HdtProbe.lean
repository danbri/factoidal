/-
Harness.HdtProbe — the HDT container reader over the vendored fixtures.

Not part of the verified library: it reads files and prints scores, per
the spec/pragmatics split in PORT_NOTES.md.

The two fixtures in `third_party/testing/hdt/` were written by hdt-cpp
1.3.3 and carry published SHA-256 digests (see the README there). They
were vendored before the Lean tree had a reader, so nothing measured
them. This probe is what turns them into a number.

Run from the REPOSITORY ROOT:
    lake exe l4hdt
or give directories or files as arguments.
-/
import L4Factoidal.HDT.Container

open L4Factoidal.HDT

namespace Harness.HdtProbe

/-- What the reader got out of one file. -/
structure Report where
  path     : String
  ok       : Bool
  detail   : String

def describe (a : Bytes) (inv : Inventory) : String :=
  let hdr := match headerTriples a inv with
    | some (.ok g)    => s!"{g.length} header triples"
    | some (.error e) => s!"header parse error: {e}"
    | none            => "header text not decodable"
  let order := match triplesOrder inv with
    | some n => toString n
    | none   => "absent"
  s!"format={inv.global.format} bytes={a.size} {hdr} order={order} " ++
  s!"dict(shared={inv.dictShared.numstrings} subj={inv.dictSubjects.numstrings} " ++
  s!"pred={inv.dictPredicates.numstrings} obj={inv.dictObjects.numstrings})"

/-- The full skeleton, in the same field order `bin/hdt-probe/hdt_probe.ml`
    prints it, so the two trees' output can be compared field by field
    rather than by eye. `--verbose` selects it. -/
def hex4 (n : UInt16) : String :=
  let d := "0123456789ABCDEF".toList
  let nib (k : Nat) : Char := d.getD ((n.toNat / (16 ^ k)) % 16) '0'
  s!"0x{nib 3}{nib 2}{nib 1}{nib 0}"

def showCi (label : String) (ci : ControlInfo) : List String :=
  [ s!"{label} control information",
    s!"  offset      : {ci.start} .. {ci.end}",
    s!"  format      : {ci.format}",
    s!"  properties  : " ++ (if ci.propsRaw.isEmpty then "(none)" else ci.propsRaw),
    s!"  crc16       : stored {hex4 ci.crcStored} computed {hex4 ci.crcComputed} " ++
      (if ci.crcOk then "OK" else "MISMATCH") ]

def showPfc (label : String) (p : PfcSection) : String :=
  s!"  {label} : bytes {p.start} .. {p.end}  type=2(PFC)  strings={p.numstrings}  " ++
  s!"packed={p.packedBytes}B  blocksize={p.blocksize}"

def skeleton (a : Bytes) (inv : Inventory) : List String :=
  showCi "global" inv.global ++
  showCi "header" inv.headerCi ++
  [ s!"header data : bytes {inv.headerDataStart} .. {inv.headerDataStart + inv.headerDataLen} " ++
    s!"({inv.headerDataLen} bytes of N-Triples)" ] ++
  showCi "dictionary" inv.dictCi ++
  [ showPfc "shared    " inv.dictShared,
    showPfc "subjects  " inv.dictSubjects,
    showPfc "predicates" inv.dictPredicates,
    showPfc "objects   " inv.dictObjects ] ++
  showCi "triples" inv.triplesCi ++
  (let ord := match triplesOrder inv with | some n => toString n | none => "absent"
   [ s!"triples data: starts at byte {inv.triplesDataStart} (order={ord})",
    match headerTriples a inv with
    | some (.ok g)    => s!"header RDF  : {g.length} triples (via the verified N-Triples parser)"
    | some (.error e) => s!"header RDF  : parse error: {e}"
    | none            => "header RDF  : text not decodable" ])

def runOne (path : System.FilePath) : IO Report := do
  match ← readInventory path with
  | none => return { path := path.toString, ok := false,
                     detail := "container skeleton not parsed" }
  | some (a, inv) =>
      return { path := path.toString, ok := true, detail := describe a inv }

/-- Every `.hdt` under a directory, one level deep. -/
def hdtFilesIn (dir : System.FilePath) : IO (Array System.FilePath) := do
  if !(← dir.isDir) then return #[]
  let entries ← dir.readDir
  return entries.filterMap (fun e =>
    if e.fileName.endsWith ".hdt" then some e.path else none)

def defaultDir : System.FilePath := "third_party/testing/hdt"

def main (argv : List String) : IO UInt32 := do
  let verbose := argv.contains "--verbose"
  let args := argv.filter (fun a => a != "--verbose")
  let targets ← if args.isEmpty then hdtFilesIn defaultDir else do
    let mut acc : Array System.FilePath := #[]
    for a in args do
      let p : System.FilePath := a
      if ← p.isDir then acc := acc ++ (← hdtFilesIn p) else acc := acc.push p
    pure acc
  if targets.isEmpty then
    IO.println s!"no .hdt files found (looked in {defaultDir})"
    return 1
  let sorted := targets.qsort (fun a b => a.toString < b.toString)
  let mut pass := 0
  let mut fail := 0
  for p in sorted do
    if verbose then
      IO.println s!"file        : {p} ({(← IO.FS.readBinFile p).size} bytes)"
      match ← readInventory p with
      | none          => IO.println "  container skeleton not parsed"
      | some (a, inv) => for line in skeleton a inv do IO.println line
    let r ← runOne p
    if r.ok then
      pass := pass + 1
      IO.println s!"PASS {r.path}: {r.detail}"
    else
      fail := fail + 1
      IO.println s!"FAIL {r.path}: {r.detail}"
  IO.println ""
  IO.println s!"HDT container: {pass} pass, {fail} fail (out of {pass + fail})"
  return (if fail == 0 then 0 else 1)

end Harness.HdtProbe

def main (args : List String) : IO UInt32 := Harness.HdtProbe.main args
