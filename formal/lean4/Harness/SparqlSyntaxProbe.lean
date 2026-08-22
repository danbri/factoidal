/-
Harness.SparqlSyntaxProbe — run the Lean SPARQL query parser over the
real W3C sparql11 `.rq` files on disk.

Iron rule #6 ("run the real W3C test files") applied to the SPARQL
query stage. The task brief asked for a probe that works WITHOUT a
manifest, by the `bad`-in-the-name convention. That convention turned
out to be WRONG for this corpus, and the first run said so loudly:
`syntax-BINDscope6.rq`, `syntax-SELECTscope2.rq`, `syntax-bindings-09.rq`,
`aggregates/agg08.rq`, `grouping/group06.rq` and
`construct/constructwhere05.rq` are all `mf:NegativeSyntaxTest11`
entries whose names contain no `bad`, so a name-only probe scores six
CORRECT rejections as failures. Unlike the Turtle stage — where a
manifest cannot be read until a Turtle parser exists — the Turtle
parser IS landed here, so this probe reads each suite's `manifest.ttl`
with `L4Factoidal.Syntax.Turtle` and classifies by
`rdf:type mf:PositiveSyntaxTest11` / `mf:NegativeSyntaxTest11` and
`mf:action`. The naming convention is kept only as the fallback for a
directory with no manifest.

Classification, in order:
  * a file the manifest types as `mf:NegativeSyntaxTest*` — the
    parser MUST reject it; accepting it is a failure.
  * any other file the manifest lists under `mf:action` — must parse.
  * a `.rq` present on disk but named by no manifest — reported in a
    separate "not in any manifest" bucket and NOT scored. These are
    corpus leftovers (`property-path/path-2-1.rq` and friends use the
    `{n,m}` path quantifiers that were dropped before SPARQL 1.1
    became a Recommendation), so scoring them either way would be
    wrong.

BASE. Each file is parsed with its own `file:` URI as the BASE IRI,
which is what SPARQL 1.1 §4.1.1.1 lets a service do with the request
URI and what the F* tree's runner supplies. Without it a fixture like
`syntax-query/syntax-oneof-03.rq` (`FILTER(?o IN(1,<x>))`) or a
relative `FROM <data.ttl>` cannot resolve.

SKIPPED, and reported as such rather than silently: `syntax-update-1/`
and `syntax-update-2/` hold SPARQL 1.1 UPDATE requests ([29]-[52]),
which `parseSparql` does not parse — `SPARQL/Parser.lean` is a QUERY
parser and says so in its header.

Every count is printed with its DENOMINATOR and every failure is named,
per the project's score-reporting rule (anti-pattern #25). This probe
reports what it MEASURED. It is not a conformance claim: that waits
for a Lean runner that reads the same manifests `bin/w3c-runner` does,
end to end.
-/

import L4Factoidal.SPARQL.Parser
import L4Factoidal.Syntax.Turtle

open L4Factoidal.SPARQL
open L4Factoidal.Syntax
open L4Factoidal.RDF

/-- Counters for one directory sweep. -/
structure SynTally where
  posOk        : Nat := 0
  posTotal     : Nat := 0
  negOk        : Nat := 0
  negTotal     : Nat := 0
  /-- `.rq` files on disk that no manifest names — not scored. -/
  unlisted     : Nat := 0
  unlistedNames : List String := []
  failures     : List String := []

/-- Record a named failure. -/
def SynTally.note (t : SynTally) (msg : String) : SynTally :=
  { t with failures := t.failures ++ [msg] }

/-- Merge two sweeps. -/
def SynTally.add (a b : SynTally) : SynTally :=
  { posOk := a.posOk + b.posOk, posTotal := a.posTotal + b.posTotal,
    negOk := a.negOk + b.negOk, negTotal := a.negTotal + b.negTotal,
    unlisted := a.unlisted + b.unlisted,
    unlistedNames := a.unlistedNames ++ b.unlistedNames,
    failures := a.failures ++ b.failures }

/-- The fallback convention when a directory has no manifest. -/
def isBadQueryName (name : String) : Bool := (name.splitOn "bad").length > 1

/-- Read a file, `none` when it cannot be read or decoded. -/
def readOpt (p : System.FilePath) : IO (Option String) := do
  try return some (← IO.FS.readFile p) catch _ => return none

/-- The last path segment of an IRI — how a manifest's `mf:action`
IRI maps back to a file name on disk. -/
def lastSeg (iri : String) : String :=
  match (iri.splitOn "/").getLast? with
  | some s => s
  | none   => iri

/-- What a directory's `manifest.ttl` says: the file names it lists at
all, and the subset it types as a negative syntax test. -/
structure ManifestInfo where
  listed   : List String := []
  negative : List String := []
  triples  : Nat := 0
  parsed   : Bool := false

/-- The test-manifest vocabulary terms this probe reads. -/
def mfNS : String := "http://www.w3.org/2001/sw/DataAccess/tests/test-manifest#"
/-- `rdf:type`. -/
def rdfTypeIriStr : String := "http://www.w3.org/1999/02/22-rdf-syntax-ns#type"
/-- The query-test vocabulary. An EVALUATION test's `mf:action` is a
blank node carrying `qt:query <file.rq>` and `qt:data <file.ttl>`, so
`mf:action` alone finds only the syntax tests' direct file IRIs. -/
def qtQueryP : String := "http://www.w3.org/2001/sw/DataAccess/tests/test-query#query"

/-- Read a suite's `manifest.ttl` with the Lean Turtle parser. -/
def readManifest (dir : System.FilePath) : IO ManifestInfo := do
  match ← readOpt (dir / "manifest.ttl") with
  | none => return {}
  | some text =>
    match parseTurtle text (some "http://example.org/manifest") with
    | .error _ => return {}
    | .ok g =>
      let actionP := mfNS ++ "action"
      -- subject → action file name
      let actions : List (String × String) :=
        (g.filter (fun t => t.p.val == actionP)).filterMap (fun t =>
          match t.s, t.o with
          | .iri s, .iri o => some (s.val, lastSeg o.val)
          | _, _           => none)
      -- subjects typed as a negative syntax test
      let negSubjects : List String :=
        (g.filter (fun t =>
          t.p.val == rdfTypeIriStr &&
          (match t.o with
           | .iri o => (o.val.splitOn "NegativeSyntaxTest").length > 1
           | _      => false))).filterMap (fun t =>
             match t.s with | .iri s => some s.val | _ => none)
      -- Evaluation tests point at their query through a blank-node action.
      let qtNames : List String :=
        (g.filter (fun t => t.p.val == qtQueryP)).filterMap (fun t =>
          match t.o with | .iri o => some (lastSeg o.val) | _ => none)
      return { listed := actions.map Prod.snd ++ qtNames,
               negative := (actions.filter (fun a => negSubjects.contains a.1)).map Prod.snd,
               triples := g.length, parsed := true }

/-- Every `.rq` directly in a directory, sorted. -/
def rqFiles (dir : System.FilePath) : IO (List String) := do
  if !(← dir.isDir) then return []
  let entries ← dir.readDir
  let names := entries.toList.map (fun e => e.fileName)
  return (((names.filter (fun n => n.endsWith ".rq")).toArray).qsort (· < ·)).toList

/-- Every `.ru` (UPDATE request) directly in a directory. -/
def ruFiles (dir : System.FilePath) : IO (List String) := do
  if !(← dir.isDir) then return []
  let entries ← dir.readDir
  let names := entries.toList.map (fun e => e.fileName)
  return (((names.filter (fun n => n.endsWith ".ru")).toArray).qsort (· < ·)).toList

/-- Sweep one suite directory. `scoreUnlisted` makes an unlisted file
count as a positive test (used when a directory has no manifest). -/
def probeDir (dir : System.FilePath) : IO SynTally := do
  let names ← rqFiles dir
  if names.isEmpty then return {}
  let mi ← readManifest dir
  let mut t : SynTally := {}
  for name in names do
    let path := dir / name
    let some text ← readOpt path | do
      t := t.note s!"  UNREADABLE: {path}"
      continue
    -- SPARQL 1.1 §4.1.1.1: the request URI may serve as BASE.
    let base := "file://" ++ (← IO.FS.realPath path).toString
    let res := parseSparql text (some base)
    let isNeg :=
      if mi.parsed then mi.negative.contains name else isBadQueryName name
    let isListed := !mi.parsed || mi.listed.contains name
    if !isListed then
      t := { t with unlisted := t.unlisted + 1,
                    unlistedNames := t.unlistedNames ++ [s!"{dir}/{name}"] }
    else if isNeg then
      match res with
      | .error _ => t := { t with negOk := t.negOk + 1, negTotal := t.negTotal + 1 }
      | .ok _    => t := { t with negTotal := t.negTotal + 1 }.note
                      s!"  ACCEPTED a negative-syntax test: {path}"
    else
      match res with
      | .ok _    => t := { t with posOk := t.posOk + 1, posTotal := t.posTotal + 1 }
      | .error e => t := { t with posTotal := t.posTotal + 1 }.note
                      s!"  REJECTED at char {e.pos}: {path} — {e.msg}"
  return t

/-- Print one tally block. -/
def report (label : String) (t : SynTally) : IO Unit := do
  IO.println s!"--- {label} ---"
  IO.println s!"positive: {t.posOk} pass, {t.posTotal - t.posOk} fail (out of {t.posTotal})"
  IO.println s!"negative: {t.negOk} pass, {t.negTotal - t.negOk} fail (out of {t.negTotal})"
  if t.unlisted > 0 then
    IO.println s!"not in any manifest (NOT scored): {t.unlisted}"
    for n in t.unlistedNames do IO.println s!"    {n}"
  for m in t.failures do IO.println m
  IO.println ""

/-- The probe. Argument 1 is the sparql11 suite root. -/
def main (args : List String) : IO UInt32 := do
  let root : System.FilePath :=
    match args with
    | a :: _ => a
    | []     => "third_party/testing/w3c/sparql/sparql11"
  if !(← root.isDir) then
    IO.eprintln s!"l4sparql-probe: suite root not found: {root}"
    IO.eprintln "run tools/ensure-test-env.sh first"
    return 1

  IO.println "=== SPARQL 1.1 query-syntax probe (Lean parser) ==="
  IO.println s!"root: {root}"
  IO.println ""

  let synQ ← probeDir (root / "syntax-query")
  report "syntax-query" synQ

  let synF ← probeDir (root / "syntax-fed")
  report "syntax-fed" synF

  -- UPDATE requests are `.ru`, not `.rq`.
  let up1 ← ruFiles (root / "syntax-update-1")
  let up2 ← ruFiles (root / "syntax-update-2")
  IO.println "--- syntax-update-1 / syntax-update-2 (SKIPPED: UPDATE, not query) ---"
  IO.println s!"skipped: {up1.length + up2.length} files ({up1.length} + {up2.length})"
  IO.println ""

  -- Every other subdirectory: the evaluation suites' queries.
  let entries ← root.readDir
  let skip := ["syntax-query", "syntax-fed", "syntax-update-1", "syntax-update-2"]
  let mut dirs : List System.FilePath := []
  for e in entries do
    if ← e.path.isDir then
      if !(skip.contains (e.path.fileName.getD "")) then dirs := dirs ++ [e.path]
  let sorted := (dirs.toArray.qsort (fun a b => a.toString < b.toString)).toList
  let mut allT : SynTally := {}
  for d in sorted do
    allT := allT.add (← probeDir d)
  IO.println "--- all other sparql11 subdirectories (query-eval suites) ---"
  IO.println s!"parsed {allT.posOk} of {allT.posTotal}"
  IO.println s!"negative-syntax entries rejected: {allT.negOk} of {allT.negTotal}"
  if allT.unlisted > 0 then
    IO.println s!"not in any manifest (NOT scored): {allT.unlisted}"
    for n in allT.unlistedNames do IO.println s!"    {n}"
  for m in allT.failures do IO.println m
  IO.println ""

  let ok  := synQ.posOk + synQ.negOk + synF.posOk + synF.negOk + allT.posOk + allT.negOk
  let tot := synQ.posTotal + synQ.negTotal + synF.posTotal + synF.negTotal +
             allT.posTotal + allT.negTotal
  IO.println s!"TOTAL (manifest-listed query files): {ok} pass, {tot - ok} fail (out of {tot})"
  let unl := synQ.unlisted + synF.unlisted + allT.unlisted
  IO.println s!"unscored (present on disk, in no manifest): {unl}"
  IO.println s!"unscored (UPDATE suites, out of scope for a query parser): {up1.length + up2.length}"
  return 0
