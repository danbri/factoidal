/-
Harness/JsonLdProbe — run `L4Factoidal.JSONLD` against the real W3C
JSON-LD 1.1 `toRdf` manifest vendored at
`third_party/testing/json-ld/tests/toRdf-manifest.jsonld`.

This is a HARNESS, not part of the verified library: it does file I/O
and prints. It reads the suite the way the F* tree's
`bin/jsonld-runner` does — the real manifest, the real `-in.jsonld`
inputs, the real `-out.nq` expected outputs — never synthetic inputs
"inspired by" the suite (CLAUDE.md iron rule #6).

Usage: `lake exe l4jsonld-probe [path-to-tests-dir] [path-to-cache-dir]`
Defaults are the vendored corpus and context cache, relative to the
repository root.

## What each manifest `@type` means here

  * `jld:PositiveEvaluationTest` — expand + toRdf must succeed and the
    dataset must equal the `expect` file's.
  * `jld:PositiveSyntaxTest` — expand + toRdf must merely succeed.
  * `jld:NegativeEvaluationTest` — expand + toRdf must FAIL. The
    manifest's `expectErrorCode` is additionally compared against the
    `JsonLdError.code` this port produces, and reported separately: a
    code mismatch is NOT counted as a failure (the F* source returns a
    bare `option`, so it has no code to compare at all — counting code
    mismatches as failures would report a WORSE score for strictly more
    information).

## Base IRI

Every test's document base is `baseIri ++ input` (the manifest's own
convention, declared by its `baseIri` field) unless `option.base`
overrides it. `option.expandContext` is manifest-relative and is
resolved the same way, so the loader can fetch it.

## The loader

Built from two sources, in this order:
  1. `prefixLoader baseIri <files>` — the suite's own "remote" contexts
     are ordinary files shipped beside the manifest, addressed by the
     `baseIri` prefix. Every `.jsonld`/`.json` file under the tests
     directory is read once at start-up and keyed by its path relative
     to that directory.
  2. `tableLoader <cache>` — the vendored
     `third_party/jsonld-context-cache/` snapshot store, read through
     `cacheTableOfIndex` (see `JSONLD/Loader.lean` for the index's
     shape). Genuinely remote contexts (`https://www.w3.org/ns/did/v1`
     and friends) resolve from there.
An IRI in neither becomes `loading remote context failed`. There is no
empty-context fallback.

## Two comparison routes, both reported

The primary comparison is `Dataset.isomorphic?` (RDF 1.1 Concepts
§3.6). It has a hard 16-blank-node search budget and compares named
graphs by NAME, so it cannot decide a dataset with more blank nodes or
with blank-node-named graphs. Where it says no, the probe also tries
RDFC-1.0 canonical N-Quads equality (`Dataset.canonicalNQuads`) — the
same comparison the F* runner uses, which relabels blank-node graph
names too. Both are sound dataset-equality tests; the count that needed
the second route is printed separately rather than hidden.

## Expected-file parsing

`Syntax.parseNQuads` is STRICT (any malformed line aborts the whole
parse), while the F* `Parser.NQuads.parse_nquads` skips a malformed
line and continues. The suite relies on that leniency: `0118-out.nq`'s
blank-node-PREDICATE lines are unparseable under either grammar, and
this engine likewise never emits them (see `JSONLD/ToRdf.lean` on
generalized RDF). So the probe parses the expected file LINE BY LINE
and drops the lines that do not parse — reproducing the F* runner's
behaviour exactly, and counting the dropped lines so the leniency is
visible rather than silent.
-/
import L4Factoidal.JSONLD.ToRdf
import L4Factoidal.Syntax.NQuads
import L4Factoidal.RDF.Isomorphism
import L4Factoidal.RDF.Canonical

open L4Factoidal.JSON
open L4Factoidal.JSONLD
open L4Factoidal.RDF
open L4Factoidal.Syntax

namespace JsonLdProbe

/-! ## Manifest entries -/

inductive Kind where
  | positive | positiveSyntax | negative | unknown
  deriving DecidableEq, Repr

def Kind.label : Kind → String
  | .positive       => "PositiveEvaluationTest"
  | .positiveSyntax => "PositiveSyntaxTest"
  | .negative       => "NegativeEvaluationTest"
  | .unknown        => "unrecognized @type"

structure Entry where
  id             : String
  name           : String
  kind           : Kind
  input          : String
  expect         : Option String
  errorCode      : Option String
  base           : Option String
  processingMode : Option String
  rdfDirection   : Option String
  expandContext  : Option String
  deriving Repr

/-- The `@type` array to a `Kind`. -/
def kindOf (j : Json) : Kind :=
  let types : List String :=
    match j.field? "@type" with
    | some (.array items) => items.filterMap Json.asString?
    | some (.string s)    => [s]
    | _ => []
  if types.contains "jld:NegativeEvaluationTest" then .negative
  else if types.contains "jld:PositiveSyntaxTest" then .positiveSyntax
  else if types.contains "jld:PositiveEvaluationTest" then .positive
  else .unknown

def entryOf (j : Json) : Option Entry :=
  match j.getString? "input" with
  | none => none
  | some input =>
    let opt := j.field? "option"
    let optStr (k : String) : Option String := opt.bind (fun o => o.getString? k)
    -- `option.processingMode` and `option.specVersion` are two manifest
    -- spellings of the same thing; forward whichever is present, with
    -- `processingMode` winning if both are.
    let pm := match optStr "processingMode" with
              | some s => some s
              | none   => optStr "specVersion"
    some { id := (j.getString? "@id").getD "?",
           name := (j.getString? "name").getD "",
           kind := kindOf j,
           input := input,
           expect := j.getString? "expect",
           errorCode := j.getString? "expectErrorCode",
           base := optStr "base",
           processingMode := pm,
           rdfDirection := optStr "rdfDirection",
           expandContext := optStr "expandContext" }

/-! ## File-system helpers -/

/-- Recursively list the files under `root`, to a bounded depth (the
suite's tree is two levels deep; the bound keeps this total). Returns
paths RELATIVE to `root`, using `/` separators. -/
def walkDir : Nat → System.FilePath → String → IO (List String)
  | 0, _, _ => pure []
  | depth + 1, root, rel => do
    let dir := if rel.isEmpty then root else root / rel
    let entries ← try dir.readDir catch _ => pure #[]
    let mut out : List String := []
    for e in entries do
      let childRel := if rel.isEmpty then e.fileName else rel ++ "/" ++ e.fileName
      if ← (dir / e.fileName).isDir then
        out := out ++ (← walkDir depth root childRel)
      else
        out := childRel :: out
    pure out

def readFileOpt (p : System.FilePath) : IO (Option String) := do
  try pure (some (← IO.FS.readFile p)) catch _ => pure none

/-! ## Expected-file parsing (line by line, lenient) -/

/-- Parse an N-Quads document one line at a time, dropping lines that do
not parse. Returns the dataset and the number of dropped lines. See this
module's header for why the leniency is needed and what it costs. -/
def parseNQuadsLenient (txt : String) : Dataset × Nat := Id.run do
  let mut ds : Dataset := Dataset.empty
  let mut dropped : Nat := 0
  for line in txt.splitOn "\n" do
    let t := line.trim
    if t.isEmpty || t.startsWith "#" then continue
    match parseNQuads t .rdf11 with
    | .error _ => dropped := dropped + 1
    | .ok one =>
      ds := { default := ds.default ++ one.default,
              named := one.named.foldl (fun acc ng =>
                match acc.find? (fun x => x.name == ng.name) with
                | some existing =>
                  acc.map (fun x => if x.name == ng.name
                                    then { name := x.name, graph := existing.graph ++ ng.graph }
                                    else x)
                | none => acc ++ [ng]) ds.named }
  pure (ds, dropped)

/-! ## Comparison -/

inductive CompareResult where
  /-- Equal by `Dataset.isomorphic?`. -/
  | isomorphic
  /-- Equal by RDFC-1.0 canonical N-Quads, where the bounded
  isomorphism search could not decide (too many blank nodes, or a
  blank-node graph name). -/
  | canonical
  | different
  deriving DecidableEq, Repr

def compareDatasets (got exp : Dataset) : CompareResult :=
  if got.isomorphic? exp then .isomorphic
  else if got.canonicalNQuads == exp.canonicalNQuads then .canonical
  else .different

/-! ## Running one entry -/

inductive Outcome where
  | pass (viaCanonical : Bool)
  | fail (reason : String)
  | skip (reason : String)
  deriving Repr

structure RunResult where
  outcome      : Outcome
  /-- For a negative test that failed as expected: whether the error
  code this port produced matches the manifest's `expectErrorCode`. -/
  codeMatch    : Option Bool
  producedCode : Option String
  /-- Quads produced, and quads expected, for a positive evaluation
  test. Reported in aggregate so a suite that "passes" by comparing
  nothing to nothing is visible rather than silent (CLAUDE.md
  anti-pattern #3 / `skills/measuring-inference` — a green test that
  measured nothing is the failure mode to guard against). -/
  gotQuads     : Nat := 0
  expQuads     : Nat := 0
  /-- Expected-file lines that did not parse and were dropped. -/
  droppedLines : Nat := 0

def datasetQuads (ds : Dataset) : Nat :=
  ds.default.length + (ds.named.map (fun ng => ng.graph.length)).foldl (· + ·) 0

def truncate (n : Nat) (s : String) : String :=
  if s.length ≤ n then s else String.ofList (s.toList.take n) ++ " …"

def runEntry (loader : Loader) (baseIri : String) (dir : System.FilePath) (e : Entry)
    : IO RunResult := do
  if e.kind == .unknown then
    return { outcome := .skip "unrecognized @type for a toRdf test entry",
             codeMatch := none, producedCode := none }
  match ← readFileOpt (dir / e.input) with
  | none => return { outcome := .fail s!"input file not found: {e.input}",
                     codeMatch := none, producedCode := none }
  | some content =>
    let base := match e.base with | some b => some b | none => some (baseIri ++ e.input)
    let expCtx := e.expandContext.map (fun rel => baseIri ++ rel)
    let got := parseJsonLd loader content base e.rdfDirection expCtx e.processingMode
    match e.kind with
    | .unknown => return { outcome := .skip "unreachable", codeMatch := none, producedCode := none }
    | .negative =>
      match got with
      | .error err =>
        let cm := e.errorCode.map (fun c => c == err.code)
        return { outcome := .pass false, codeMatch := cm, producedCode := some err.code }
      | .ok _ =>
        return { outcome := .fail s!"succeeded, but the manifest expects the error \"{e.errorCode.getD "?"}\"",
                 codeMatch := none, producedCode := none }
    | .positiveSyntax =>
      match got with
      | .ok _ => return { outcome := .pass false, codeMatch := none, producedCode := none }
      | .error err =>
        return { outcome := .fail s!"failed with \"{err.code}\", but the input must parse",
                 codeMatch := none, producedCode := none }
    | .positive =>
      match e.expect with
      | none => return { outcome := .fail "manifest entry has no `expect` file",
                         codeMatch := none, producedCode := none }
      | some expectRel =>
        match ← readFileOpt (dir / expectRel) with
        | none => return { outcome := .fail s!"expected .nq file not found: {expectRel}",
                           codeMatch := none, producedCode := none }
        | some expectTxt =>
          match got with
          | .error err =>
            return { outcome := .fail s!"failed with \"{err.code}\" (expected a dataset)",
                     codeMatch := none, producedCode := none }
          | .ok gotDs =>
            let (expDs, dropped) := parseNQuadsLenient expectTxt
            let gq := datasetQuads gotDs
            let xq := datasetQuads expDs
            match compareDatasets gotDs expDs with
            | .isomorphic => return { outcome := .pass false, codeMatch := none, producedCode := none,
                                      gotQuads := gq, expQuads := xq, droppedLines := dropped }
            | .canonical  => return { outcome := .pass true, codeMatch := none, producedCode := none,
                                      gotQuads := gq, expQuads := xq, droppedLines := dropped }
            | .different =>
              let g := truncate 240 gotDs.canonicalNQuads
              let x := truncate 240 expDs.canonicalNQuads
              let note := if dropped > 0 then s!" [{dropped} unparseable expected line(s) dropped]" else ""
              return { outcome := .fail s!"dataset mismatch{note}\n      expected:\n{x}\n      got:\n{g}",
                       codeMatch := none, producedCode := none,
                       gotQuads := gq, expQuads := xq, droppedLines := dropped }

/-! ## Main -/

def defaultTestsDir : System.FilePath := "third_party/testing/json-ld/tests"
def defaultCacheDir : System.FilePath := "third_party/jsonld-context-cache"

/-- Build the loader: suite files under the manifest's `baseIri`
prefix, then the vendored context cache. -/
def buildLoader (dir cacheDir : System.FilePath) (baseIri : String) : IO Loader := do
  -- 1. Every .jsonld/.json file under the tests directory.
  let rels ← walkDir 4 dir ""
  let jsonRels := rels.filter (fun r => r.endsWith ".jsonld" || r.endsWith ".json")
  let mut files : List (String × String) := []
  for r in jsonRels do
    match ← readFileOpt (dir / r) with
    | some body => files := (r, body) :: files
    | none => pure ()
  -- 2. The vendored context cache, via its index.
  let mut cache : List (String × String) := []
  match ← readFileOpt (cacheDir / "index.json") with
  | some idxTxt =>
    match parseJson idxTxt with
    | .ok idx =>
      for ce in cacheTableOfIndex idx do
        match ← readFileOpt (cacheDir / ce.path) with
        | some body => cache := (ce.url, body) :: cache
        | none => pure ()
    | .error _ => pure ()
  | none => pure ()
  IO.println s!"loader: {files.length} suite document(s) under {baseIri}, {cache.length} cached remote context(s)"
  pure (Loader.orElse (prefixLoader baseIri files) (tableLoader cache))

def main (args : List String) : IO UInt32 := do
  let dir : System.FilePath := match args with
    | d :: _ => d
    | []     => defaultTestsDir
  let cacheDir : System.FilePath := match args with
    | _ :: c :: _ => c
    | _           => defaultCacheDir
  let manifestPath := dir / "toRdf-manifest.jsonld"
  if !(← manifestPath.pathExists) then
    IO.eprintln s!"jsonld probe: manifest not found: {manifestPath}"
    IO.eprintln "run tools/ensure-test-env.sh from the repository root first"
    return 1
  let raw ← IO.FS.readFile manifestPath
  match parseJson raw with
  | .error e =>
    IO.eprintln s!"jsonld probe: manifest is not valid JSON: {e}"
    return 2
  | .ok root =>
    let baseIri := (root.getString? "baseIri").getD "https://w3c.github.io/json-ld-api/tests/"
    let seq := (root.getArray? "sequence").getD []
    let entries := seq.filterMap entryOf
    let loader ← buildLoader dir cacheDir baseIri
    IO.println s!"manifest: {manifestPath}"
    IO.println s!"entries:  {entries.length} (of {seq.length} sequence members)"
    IO.println ""
    let mut pass := 0
    let mut failN := 0
    let mut skipN := 0
    let mut viaCanon := 0
    let mut codeOk := 0
    let mut codeSeen := 0
    let mut byKind : List (Kind × Nat × Nat × Nat) :=
      [(.positive, 0, 0, 0), (.positiveSyntax, 0, 0, 0), (.negative, 0, 0, 0), (.unknown, 0, 0, 0)]
    let mut failures : List String := []
    let mut codeMismatches : List String := []
    let mut totalGotQuads := 0
    let mut totalExpQuads := 0
    let mut emptyBoth := 0
    let mut totalDropped := 0
    let mut posRun := 0
    for e in entries do
      let r ← runEntry loader baseIri dir e
      if e.kind == .positive then
        posRun := posRun + 1
        totalGotQuads := totalGotQuads + r.gotQuads
        totalExpQuads := totalExpQuads + r.expQuads
        totalDropped := totalDropped + r.droppedLines
        if r.gotQuads == 0 && r.expQuads == 0 then emptyBoth := emptyBoth + 1
      match r.outcome with
      | .pass viaC =>
        pass := pass + 1
        if viaC then viaCanon := viaCanon + 1
        byKind := byKind.map (fun (k, p, f, s) => if k == e.kind then (k, p + 1, f, s) else (k, p, f, s))
      | .fail msg =>
        failN := failN + 1
        byKind := byKind.map (fun (k, p, f, s) => if k == e.kind then (k, p, f + 1, s) else (k, p, f, s))
        failures := s!"{e.id} [{e.kind.label}] {e.name}: {msg}" :: failures
      | .skip msg =>
        skipN := skipN + 1
        byKind := byKind.map (fun (k, p, f, s) => if k == e.kind then (k, p, f, s + 1) else (k, p, f, s))
        failures := s!"{e.id} SKIP: {msg}" :: failures
      match r.codeMatch with
      | some ok =>
        codeSeen := codeSeen + 1
        if ok then codeOk := codeOk + 1
        else codeMismatches := s!"{e.id}: manifest \"{e.errorCode.getD "?"}\" vs produced \"{r.producedCode.getD "?"}\"" :: codeMismatches
      | none => pure ()
    let total := entries.length
    IO.println s!"toRdf: {pass} pass, {failN} fail, {skipN} skip (out of {total})"
    for (k, p, f, s) in byKind do
      if p + f + s > 0 then
        IO.println s!"  {k.label}: {p} pass, {f} fail, {s} skip (out of {p + f + s})"
    IO.println s!"  of the passes, {viaCanon} needed RDFC-1.0 canonical comparison (bounded isomorphism search could not decide)"
    IO.println s!"  negative-test error codes: {codeOk} of {codeSeen} match the manifest's expectErrorCode"
    IO.println ""
    IO.println "measurement check (a suite that passes by comparing nothing to nothing is not a pass):"
    IO.println s!"  positive tests run: {posRun}; quads produced: {totalGotQuads}; quads expected: {totalExpQuads}"
    IO.println s!"  positive tests where BOTH sides are empty: {emptyBoth}"
    IO.println s!"  expected-file lines dropped as unparseable, all tests: {totalDropped}"
    IO.println ""
    IO.println "side by side, same manifest:"
    IO.println s!"  Lean (this port, measured now): {pass} pass, {failN} fail, {skipN} skip (out of {total})"
    IO.println   "  F*  (bin/darwin-arm64/jsonld_runner, measured 2026-08-22):"
    IO.println   "                                  467 pass, 0 fail, 0 skip (out of 467)"
    IO.println   "  The F* number above is a recorded measurement, not a live run. To"
    IO.println   "  re-measure: bin/<platform>/jsonld_runner third_party/testing/json-ld/tests/toRdf-manifest.jsonld"
    IO.println ""
    if !failures.isEmpty then
      IO.println "failures:"
      for f in failures.reverse do IO.println s!"  {f}"
    if !codeMismatches.isEmpty then
      IO.println ""
      IO.println "negative tests that failed for a DIFFERENT reason than the manifest names"
      IO.println "(still counted as passes — the F* source has no error code to compare at all):"
      for c in codeMismatches.reverse do IO.println s!"  {c}"
    return 0

end JsonLdProbe

def main (args : List String) : IO UInt32 := JsonLdProbe.main args
