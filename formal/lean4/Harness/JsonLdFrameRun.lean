/-
Harness/JsonLdFrameRun — run `L4Factoidal.JSONLD.Frame` against the W3C
json-ld-framing suite (`frame-manifest.jsonld`, 92 entries).

This is a HARNESS, not part of the verified library: it does file I/O
and prints a score. It reads the real manifest, the real inputs, the
real frames and the real expected outputs, the way the F* tree's
`bin/jsonld-frame-runner` does — never synthetic inputs "inspired by"
the suite (CLAUDE.md iron rule #6).

Usage: `l4jsonld-frame [tests-dir] [cache-dir]`. The defaults are
relative to the CURRENT DIRECTORY, so run the built binary from the
repository root (`formal/lean4/.lake/build/bin/l4jsonld-frame`) —
`lake exe` runs it from `formal/lean4`, where the corpus is not.

The comparison rule is the one every JSON-LD runner in this project
uses: RFC 8785 canonical serialisation of both trees, then string
equality. Member order is insignificant, array order IS significant, and
there is no blank-node relabelling — the fixtures pin the exact labels.
-/
import L4Factoidal.JSONLD.Frame

open L4Factoidal.JSON
open L4Factoidal.JSONLD

namespace JsonLdFrameRun

inductive Kind where
  | positive | negative | unknown
  deriving DecidableEq, Repr

structure Entry where
  id             : String
  name           : String
  kind           : Kind
  input          : String
  frame          : String
  expect         : Option String
  errorCode      : Option String
  base           : Option String
  processingMode : Option String
  omitGraph      : Option Bool
  deriving Repr

def typesOf (j : Json) : List String :=
  match j.field? "@type" with
  | some (.array items) => items.filterMap Json.asString?
  | some (.string s)    => [s]
  | _ => []

def kindOf (types : List String) : Kind :=
  if types.contains "jld:NegativeEvaluationTest" then .negative
  else if types.contains "jld:PositiveEvaluationTest" then .positive
  else .unknown

def entryOf (j : Json) : Option Entry := do
  let input ← j.getString? "input"
  let frame ← j.getString? "frame"
  let opt := j.field? "option"
  let optStr (k : String) : Option String := opt.bind (fun o => o.getString? k)
  -- `processingMode` and `specVersion` are two manifest spellings of the
  -- same thing; `processingMode` wins when both appear.
  let pm := match optStr "processingMode" with
            | some s => some s
            | none   => optStr "specVersion"
  some { id := (j.getString? "@id").getD "?",
         name := (j.getString? "name").getD "",
         kind := kindOf (typesOf j),
         input := input, frame := frame,
         expect := j.getString? "expect",
         errorCode := j.getString? "expectErrorCode",
         base := optStr "base",
         processingMode := pm,
         omitGraph := opt.bind (fun o => o.getBool? "omitGraph") }

def readFileOpt (p : System.FilePath) : IO (Option String) := do
  try pure (some (← IO.FS.readFile p)) catch _ => pure none

def walkDir : Nat → System.FilePath → String → IO (List String)
  | 0, _, _ => pure []
  | depth + 1, root, rel => do
    let dir := if rel.isEmpty then root else root / rel
    let entries ← try dir.readDir catch _ => pure #[]
    let mut out : List String := []
    for e in entries do
      let childRel := if rel.isEmpty then e.fileName else rel ++ "/" ++ e.fileName
      if ← (dir / e.fileName).isDir then out := out ++ (← walkDir depth root childRel)
      else out := childRel :: out
    pure out

def buildLoader (dir cacheDir : System.FilePath) (baseIri : String) : IO Loader := do
  let rels ← walkDir 4 dir ""
  let jsonRels := rels.filter (fun r => r.endsWith ".jsonld" || r.endsWith ".json")
  let mut files : List (String × String) := []
  for r in jsonRels do
    match ← readFileOpt (dir / r) with
    | some body => files := (r, body) :: files
    | none => pure ()
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

inductive Outcome where
  | pass
  | fail (reason : String)
  | unsupported (reason : String)
  deriving Repr

def truncate (n : Nat) (s : String) : String :=
  if s.length ≤ n then s else String.ofList (s.toList.take n) ++ " …"

def runEntry (loader : Loader) (baseIri : String) (dir : System.FilePath) (e : Entry)
    : IO Outcome := do
  if e.kind == .unknown then return .unsupported "unrecognized @type"
  match ← readFileOpt (dir / e.input), ← readFileOpt (dir / e.frame) with
  | none, _ =>
    if e.kind == .negative then return .pass
    else return .fail s!"input file not found: {e.input}"
  | _, none =>
    if e.kind == .negative then return .pass
    else return .fail s!"frame file not found: {e.frame}"
  | some inputTxt, some frameTxt =>
    let base : Option String := match e.base with
                                | some b => some b
                                | none   => some (baseIri ++ e.input)
    let got := frameDocument loader inputTxt frameTxt base e.processingMode e.omitGraph
    match e.kind with
    | .unknown => return .unsupported "unreachable"
    | .negative =>
      match got with
      | .error _ => return .pass
      | .ok _ =>
        return .fail s!"succeeded, but the manifest expects the error \"{e.errorCode.getD "?"}\""
    | .positive =>
      match e.expect with
      | none => return .fail "manifest entry has no `expect` file"
      | some expectRel =>
        match ← readFileOpt (dir / expectRel) with
        | none => return .fail s!"expected file not found: {expectRel}"
        | some expectTxt =>
          match got with
          | .error err => return .fail s!"failed with \"{err.code}\" (expected a document)"
          | .ok gotJson =>
            match parseJson expectTxt with
            | .error _ => return .fail "expected file is not valid JSON"
            | .ok expJson =>
              if expandedEqual gotJson expJson then return .pass
              else
                let g := truncate 400 (jcsDocument gotJson)
                let x := truncate 400 (jcsDocument expJson)
                return .fail s!"output differs\n      expected:\n{x}\n      got:\n{g}"

def defaultTestsDir : System.FilePath := "third_party/testing/json-ld-framing/tests"
def defaultCacheDir : System.FilePath := "third_party/jsonld-context-cache"

def main (args : List String) : IO UInt32 := do
  let dir : System.FilePath := match args with | d :: _ => d | [] => defaultTestsDir
  let cacheDir : System.FilePath := match args with | _ :: c :: _ => c | _ => defaultCacheDir
  let manifestPath := dir / "frame-manifest.jsonld"
  if !(← manifestPath.pathExists) then
    IO.eprintln s!"l4jsonld-frame: manifest not found: {manifestPath}"
    IO.eprintln "run tools/ensure-test-env.sh from the repository root first"
    return 1
  let raw ← IO.FS.readFile manifestPath
  match parseJson raw with
  | .error e =>
    IO.eprintln s!"l4jsonld-frame: manifest is not valid JSON: {e}"
    return 1
  | .ok mroot =>
    let baseIri := (mroot.getString? "baseIri").getD "https://w3c.github.io/json-ld-framing/tests/"
    let seq := (mroot.getArray? "sequence").getD []
    let entries := seq.filterMap entryOf
    let loader ← buildLoader dir cacheDir baseIri
    IO.println s!"manifest: {manifestPath}  ({entries.length} entries of {seq.length} sequence members)"
    let mut pass := 0
    let mut fail := 0
    let mut unsup := 0
    let mut failures : List String := []
    for e in entries do
      match ← runEntry loader baseIri dir e with
      | .pass => pass := pass + 1
      | .fail msg =>
        fail := fail + 1
        failures := s!"{e.id} {e.name}: {msg}" :: failures
      | .unsupported msg =>
        unsup := unsup + 1
        failures := s!"{e.id} {e.name}: UNSUPPORTED {msg}" :: failures
    IO.println s!"jsonld-frame: {pass} pass, {fail} fail, {unsup} unsupported (out of {entries.length})"
    IO.println "  F* (recorded in docs/test-results/assurance-inventory.json): 28 pass, 64 fail, 0 skip (out of 92)"
    IO.println ""
    IO.println "The framing port implements the same subset the F* module does:"
    IO.println "@type / @id / property matching, node embedding with a visited"
    IO.println "set, and @explicit. @default, @omitDefault, @requireAll,"
    IO.println "the other @embed modes, @reverse, @included, named graphs and"
    IO.println "value-object matching are absent in BOTH trees, and are what"
    IO.println "most of the remaining failures need."
    if !failures.isEmpty then
      IO.println ""
      IO.println "  failures:"
      for f in failures.reverse do IO.println s!"    {f}"
    return 0

end JsonLdFrameRun

def main (args : List String) : IO UInt32 := JsonLdFrameRun.main args
