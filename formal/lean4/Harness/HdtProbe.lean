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
import L4Factoidal.HDT.Dictionary
import L4Factoidal.HDT.Triples

open L4Factoidal.HDT
open L4Factoidal.RDF

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

/-! ## Stage 2 — the PFC dictionary

The line shapes below match `bin/hdt-probe/hdt_probe.ml` character for
character so `tools/hdt-tree-differential.sh` can diff the two trees'
stage-2 output the same way it diffs the container skeleton. The
`M/N ok` form is the F* probe's; the summary lines this probe prints
for the user are worded (CLAUDE.md anti-pattern 25). -/

/-- Decode a section, then report: how many strings came out, how many
    the preamble declared, whether all four CRCs check, and how many
    decoded strings map to an RDF term. -/
def sectionDecodeLine (label : String) (a : Bytes) (sec : PfcSection) : String :=
  match decodeSection a sec with
  | none => s!"  {label} : DECODE FAILED (expected {sec.numstrings})"
  | some strs =>
      let parsed := strs.countP (fun x => (termOfString x).isSome)
      let crc := if pfcSectionCrcOk a sec then "crc OK" else "crc MISMATCH"
      s!"  {label} : decoded {strs.length} strings (expected {sec.numstrings}), " ++
      s!"{crc}, term-parse {parsed}/{strs.length} ok"

/-- `pfcLocate (pfcExtract id) = id` for every ID in the section. -/
def sectionRoundTrip (a : Bytes) (sec : PfcSection) : Nat × Nat :=
  let ids := (List.range sec.numstrings).map (· + 1)
  let good := ids.countP (fun id =>
    match pfcExtract a sec id with
    | none     => false
    | some str => pfcLocate a sec str == some id)
  (good, sec.numstrings - good)

def sectionRoundTripLine (label : String) (a : Bytes) (sec : PfcSection) : String :=
  let (p, f) := sectionRoundTrip a sec
  s!"  {label} : round-trip {p} pass, {f} fail (out of {sec.numstrings})"

/-- `termToId (idToTerm id) = id` across a whole role space, which is
    where the shared-section ID arithmetic is exercised. -/
def roleRoundTrip (a : Bytes) (inv : Inventory) (role : Role) : Nat × Nat × Nat :=
  let n := roleMaxId inv role
  let ids := (List.range n).map (· + 1)
  let good := ids.countP (fun id =>
    match idToTerm a inv role id with
    | none   => false
    | some t => termToId a inv role t == some id)
  (good, n - good, n)

def roleRoundTripLine (label : String) (a : Bytes) (inv : Inventory) (role : Role) : String :=
  let (p, f, n) := roleRoundTrip a inv role
  s!"  {label} : round-trip {p} pass, {f} fail (out of {n})"

def stage2 (a : Bytes) (inv : Inventory) : List String :=
  [ "", "--- stage 2: PFC dictionary decode ---",
    sectionDecodeLine "shared    " a inv.dictShared,
    sectionDecodeLine "subjects  " a inv.dictSubjects,
    sectionDecodeLine "predicates" a inv.dictPredicates,
    sectionDecodeLine "objects   " a inv.dictObjects,
    "", "--- stage 2: per-section round-trip (pfc_locate (pfc_extract id) = id) ---",
    sectionRoundTripLine "shared    " a inv.dictShared,
    sectionRoundTripLine "subjects  " a inv.dictSubjects,
    sectionRoundTripLine "predicates" a inv.dictPredicates,
    sectionRoundTripLine "objects   " a inv.dictObjects,
    "", "--- stage 2: role-level round-trip (hdt_term_to_id (hdt_id_to_term id) = id) ---",
    roleRoundTripLine "subject   " a inv .subject,
    roleRoundTripLine "predicate " a inv .predicate,
    roleRoundTripLine "object    " a inv .object ]

/-- Every stage-2 obligation on one file, as (pass, fail). Used for
    the probe's own summary rather than for the differential. -/
def stage2Score (a : Bytes) (inv : Inventory) : Nat × Nat :=
  let secs := [inv.dictShared, inv.dictSubjects, inv.dictPredicates, inv.dictObjects]
  let crcPass := secs.countP (fun sec => pfcSectionCrcOk a sec)
  let decodePass := secs.countP (fun sec =>
    match decodeSection a sec with
    | none      => false
    | some strs => strs.length == sec.numstrings &&
                   strs.all (fun x => (termOfString x).isSome))
  let secRt := secs.map (sectionRoundTrip a)
  let roleRt := [Role.subject, .predicate, .object].map (roleRoundTrip a inv)
  let pass := crcPass + decodePass + (secRt.map (·.1)).sum + (roleRt.map (·.2.1 == 0)).countP id
  let fail := (4 - crcPass) + (4 - decodePass) + (secRt.map (·.2)).sum +
              (roleRt.map (·.2.1 != 0)).countP id
  (pass, fail)

/-! ## Stage 3 — BitmapTriples

Same rule as stage 2: the line shapes match `hdt_probe.ml` so the
differential can diff them. -/

/-- `rank1 (select1 k) = k + 1` over every valid `k` of a bitmap. -/
def rankSelectScore (a : Bytes) (bm : BitmapInfo) : Nat × Nat × Nat :=
  let ones := if bm.numbits == 0 then 0
              else match rank1 a bm (bm.numbits - 1) with | some n => n | none => 0
  let ks := List.range ones
  let good := ks.countP (fun k =>
    match select1 a bm k with
    | none   => false
    | some p => rank1 a bm p == some (k + 1))
  (good, ones - good, ones)

def stage3 (a : Bytes) (inv : Inventory) : List String :=
  match readTriples a inv with
  | none => ["", "--- stage 3: BitmapTriples navigation ---",
             "triples crc  : SECTION NOT PARSED"]
  | some t =>
      let nsub := match numSubjects a t with | some n => n | none => 0
      let roleMax := roleMaxId inv .subject
      let (yp, yf, yn) := rankSelectScore a t.bitmapY
      let (zp, zf, zn) := rankSelectScore a t.bitmapZ
      [ "", "--- stage 3: BitmapTriples navigation ---",
        s!"triples crc  : " ++ (if triplesCrcOk a t then "OK" else "MISMATCH"),
        s!"triple count : {tripleCount t} (ArrayZ entries)",
        s!"(s,p) pairs  : {t.arrayY.numentries} (ArrayY entries)",
        s!"num subjects : {nsub} (BitmapY ones-count; dictionary role max = " ++
          s!"{roleMax}, match={nsub == roleMax})",
        "", "--- stage 3: rank1/select1 regression (naive scan, stage-5 swap seam) ---",
        s!"  bitmapY  : rank1(select1 k) = k+1 for {yp} pass, {yf} fail (out of {yn})",
        s!"  bitmapZ  : rank1(select1 k) = k+1 for {zp} pass, {zf} fail (out of {zn})",
      ]

/-! ### Enumeration against the source document

The strongest check either tree makes: enumerate every triple out of
the HDT file, serialise both it and the `.nt` the file was built from
as canonical N-Triples, sort, and compare. It fails if a single term,
ID or bit is decoded wrongly. -/

def canonLines (g : Graph) : List String :=
  ((g.map L4Factoidal.Syntax.Triple.toCanonicalNTriples).eraseDups).mergeSort (fun x y => decide (x ≤ y))

def stage3GroundTruth (a : Bytes) (inv : Inventory) (ntPath : System.FilePath)
    (ntText : String) : List String :=
  let header := s!"--- stage 3: enumeration vs ground truth ({ntPath}) ---"
  match readTriples a inv with
  | none => ["", header, "  triples section not parsed"]
  | some t =>
      let ids := (enumerateAll a t).getD []
      let unresolved := ids.countP (fun it => (resolveIdTriple a inv it).isNone)
      let hdtGraph := ids.filterMap (resolveIdTriple a inv)
      let hdtLines := canonLines hdtGraph
      match L4Factoidal.Syntax.parseNTriples ntText with
      | .error _ =>
          ["", header,
           s!"  id-triples decoded : {ids.length} (unresolved: {unresolved})",
           "  ground truth did not parse"]
      | .ok src =>
          let srcLines := canonLines src
          ["", header,
           s!"  id-triples decoded : {ids.length} (unresolved: {unresolved})",
           s!"  hdt lines (unique) : {hdtLines.length}, " ++
             s!"ground truth lines (unique): {srcLines.length}",
           "  enumeration vs source (sorted N-Triples compare) -> " ++
             (if hdtLines == srcLines then "MATCH" else "DIFFER")]

/-- Every stage-3 obligation on one file, as (pass, fail). -/
def stage3Score (a : Bytes) (inv : Inventory) : Nat × Nat :=
  match readTriples a inv with
  | none => (0, 1)
  | some t =>
      let nsub := match numSubjects a t with | some n => n | none => 0
      let (yp, yf, _) := rankSelectScore a t.bitmapY
      let (zp, zf, _) := rankSelectScore a t.bitmapZ
      let ts := (enumerateAll a t).getD []
      let resolved := ts.countP (fun it => (resolveIdTriple a inv it).isSome)
      let crc := if triplesCrcOk a t then 1 else 0
      let subjMatch := if nsub == roleMaxId inv .subject then 1 else 0
      let countMatch := if ts.length == tripleCount t then 1 else 0
      (crc + subjMatch + countMatch + yp + zp + resolved,
       (1 - crc) + (1 - subjMatch) + (1 - countMatch) + yf + zf + (ts.length - resolved))

def runOne (path : System.FilePath) : IO Report := do
  match ← readInventory path with
  | none => return { path := path.toString, ok := false,
                     detail := "container skeleton not parsed" }
  | some (a, inv) =>
      let (p2, f2) := stage2Score a inv
      let (p3, f3) := stage3Score a inv
      return { path := path.toString, ok := f2 == 0 && f3 == 0,
               detail := describe a inv ++
                 s!" | stage 2: {p2} pass, {f2} fail | stage 3: {p3} pass, {f3} fail" }

/-- Every `.hdt` under a directory, one level deep. -/
def hdtFilesIn (dir : System.FilePath) : IO (Array System.FilePath) := do
  if !(← dir.isDir) then return #[]
  let entries ← dir.readDir
  return entries.filterMap (fun e =>
    if e.fileName.endsWith ".hdt" then some e.path else none)

def defaultDir : System.FilePath := "third_party/testing/hdt"

def main (argv : List String) : IO UInt32 := do
  let verbose := argv.contains "--verbose"
  let rest := argv.filter (fun a => a != "--verbose")
  -- An `.nt` path after an `.hdt` path is that file's ground truth.
  let args := rest.filter (fun a => !a.endsWith ".nt")
  let groundTruth := rest.filter (fun a => a.endsWith ".nt")
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
      | some (a, inv) =>
          for line in skeleton a inv do IO.println line
          for line in stage2 a inv do IO.println line
          for line in stage3 a inv do IO.println line
          match groundTruth with
          | []      => pure ()
          | nt :: _ =>
              let ntText ← IO.FS.readFile nt
              for line in stage3GroundTruth a inv nt ntText do IO.println line
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
