/-
Harness/JsonLdApiProbe — run `L4Factoidal.JSONLD` against the W3C
json-ld-api manifests OTHER than `toRdf` (which
`Harness/JsonLdProbe.lean` already covers and this file leaves alone):

  * `expand-manifest.jsonld`   — API §5.1 Expansion
  * `compact-manifest.jsonld`  — API §6 Compaction
  * `flatten-manifest.jsonld`  — API §7 Flattening
  * `fromRdf-manifest.jsonld`  — API §8.5 Serialize RDF as JSON-LD
  * `html-manifest.jsonld`     — API §"HTML Content Algorithms"

This is a HARNESS, not part of the verified library: it does file I/O
and prints scores. It reads the suites the way the F* tree's
`bin/jsonld-{expand,compact,flatten,fromrdf,html}-runner` do — the real
manifests, the real inputs, the real expected outputs — never synthetic
inputs "inspired by" the suite (CLAUDE.md iron rule #6).

Usage: `l4jsonld-api [path-to-tests-dir] [path-to-cache-dir]`
Defaults are the vendored corpus and context cache, RELATIVE TO THE
CURRENT DIRECTORY, so run the built binary from the repository root
(`formal/lean4/.lake/build/bin/l4jsonld-api`) — `lake exe` runs it from
`formal/lean4`, where the corpus is not (skill pitfall #11).

## The comparison rule, reproduced not invented

Every one of the five F* runners compares two JSON trees with
`Parser_JSONLD.jsonld_expanded_equal`: RFC 8785 (JCS) canonical
serialisation of both sides, then string equality. Object member order
is therefore insignificant, array element order IS significant, and
numbers compare by canonical value rather than by lexeme. There is NO
blank-node relabelling in that rule — the fixtures pin the exact
`_:b0`, `_:b1` … labels the algorithms' own blank-node issuers produce.
This port calls the same comparison through
`L4Factoidal.JSONLD.expandedEqual`.

## Negative tests

A `jld:NegativeEvaluationTest` PASSES when the algorithm fails. The
manifest's `expectErrorCode` is additionally compared against the
`JsonLdError.code` this port produces and reported SEPARATELY per
manifest: a code mismatch is not counted as a failure, because the F*
source returns a bare `option` and so has no code to compare at all —
counting mismatches as failures would report a worse score for strictly
more information. This is the same accounting `Harness/JsonLdProbe.lean`
uses for toRdf.

## Local overrides

`tests/local-overrides/*.json` is the F* tree's layer for a fixture the
project has examined and disputes. An id listed there is reported as a
distinctly-counted `local-override`, never folded into `pass`
(anti-pattern #25). The same files are read here so the two trees'
score lines are comparable line for line.
-/
import L4Factoidal.JSONLD.FromRdf
import L4Factoidal.JSONLD.Compact
import L4Factoidal.JSONLD.Flatten
import L4Factoidal.JSONLD.Html
import L4Factoidal.Syntax.NQuads
import L4Factoidal.RDF.Isomorphism
import L4Factoidal.RDF.Canonical

open L4Factoidal.JSON
open L4Factoidal.JSONLD
open L4Factoidal.RDF
open L4Factoidal.Syntax

namespace JsonLdApiProbe

/-! ## Manifest entries -/

inductive Kind where
  | positive | positiveSyntax | negative | unknown
  deriving DecidableEq, Repr

def Kind.label : Kind → String
  | .positive       => "PositiveEvaluationTest"
  | .positiveSyntax => "PositiveSyntaxTest"
  | .negative       => "NegativeEvaluationTest"
  | .unknown        => "unrecognized @type"

/-- Which algorithm an html-manifest entry drives (the html suite mixes
`jld:ExpandTest`, `jld:CompactTest`, `jld:FlattenTest`,
`jld:ToRDFTest`). For the four single-algorithm manifests it is fixed. -/
inductive Algo where
  | expand | compact | flatten | fromRdf | toRdf
  deriving DecidableEq, Repr

def Algo.label : Algo → String
  | .expand => "expand" | .compact => "compact" | .flatten => "flatten"
  | .fromRdf => "fromRdf" | .toRdf => "toRdf"

structure Entry where
  id                : String
  name              : String
  kind              : Kind
  algo              : Algo
  input             : String
  expect            : Option String
  context           : Option String
  errorCode         : Option String
  base              : Option String
  processingMode    : Option String
  rdfDirection      : Option String
  expandContext     : Option String
  compactArrays     : Bool
  compactToRelative : Bool
  useNativeTypes    : Bool
  useRdfType        : Bool
  extractAllScripts : Bool
  processorFeature  : Option String
  deriving Repr

def typesOf (j : Json) : List String :=
  match j.field? "@type" with
  | some (.array items) => items.filterMap Json.asString?
  | some (.string s)    => [s]
  | _ => []

def kindOf (types : List String) : Kind :=
  if types.contains "jld:NegativeEvaluationTest" then .negative
  else if types.contains "jld:PositiveSyntaxTest" then .positiveSyntax
  else if types.contains "jld:PositiveEvaluationTest" then .positive
  else .unknown

def algoOf (types : List String) (dflt : Algo) : Algo :=
  if types.contains "jld:ExpandTest" then .expand
  else if types.contains "jld:CompactTest" then .compact
  else if types.contains "jld:FlattenTest" then .flatten
  else if types.contains "jld:FromRDFTest" then .fromRdf
  else if types.contains "jld:ToRDFTest" then .toRdf
  else dflt

def entryOf (dflt : Algo) (j : Json) : Option Entry :=
  match j.getString? "input" with
  | none => none
  | some input =>
    let opt := j.field? "option"
    let optStr (k : String) : Option String := opt.bind (fun o => o.getString? k)
    let optBool (k : String) (d : Bool) : Bool :=
      (opt.bind (fun o => o.getBool? k)).getD d
    -- `option.processingMode` and `option.specVersion` are two manifest
    -- spellings of the same thing; `processingMode` wins if both appear.
    let pm := match optStr "processingMode" with
              | some s => some s
              | none   => optStr "specVersion"
    let types := typesOf j
    some { id := (j.getString? "@id").getD "?",
           name := (j.getString? "name").getD "",
           kind := kindOf types,
           algo := algoOf types dflt,
           input := input,
           expect := j.getString? "expect",
           context := j.getString? "context",
           errorCode := j.getString? "expectErrorCode",
           base := optStr "base",
           processingMode := pm,
           rdfDirection := optStr "rdfDirection",
           expandContext := optStr "expandContext",
           compactArrays := optBool "compactArrays" true,
           compactToRelative := optBool "compactToRelative" true,
           useNativeTypes := optBool "useNativeTypes" false,
           useRdfType := optBool "useRdfType" false,
           extractAllScripts := optBool "extractAllScripts" false,
           processorFeature := optStr "processorFeature" }

/-! ## File-system helpers -/

/-- Recursively list the files under `root`, to a bounded depth (the
suite's tree is two levels deep; the bound keeps this total). -/
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

/-! ## N-Quads input parsing (fromRdf)

`Syntax.parseNQuads` is STRICT (any malformed line aborts the whole
parse) while F*'s `Parser.NQuads.parse_nquads` skips a malformed line
and continues; the fromRdf runner relies on that leniency. Parse line by
line, drop what does not parse, and COUNT the drops so the leniency is
visible rather than silent. -/
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

/-! ## Running one entry -/

inductive Outcome where
  | pass
  | fail (reason : String)
  | unsupported (reason : String)
  deriving Repr

structure RunResult where
  outcome      : Outcome
  codeMatch    : Option Bool := none
  producedCode : Option String := none
  droppedLines : Nat := 0
  deriving Repr

def truncate (n : Nat) (s : String) : String :=
  if s.length ≤ n then s else String.ofList (s.toList.take n) ++ " …"

/-- Produce the algorithm's output for one entry, or a `JsonLdError`.
`base` is already resolved by the caller (an HTML `<base href>` may move
it). -/
def runAlgo (loader : Loader) (baseIri : String) (dir : System.FilePath) (e : Entry)
    (base : Option String) (content : String) : IO (Res Json × Nat) := do
  let expCtx := e.expandContext.map (fun rel => baseIri ++ rel)
  match e.algo with
  | .expand => pure (expandDocument loader content base expCtx e.processingMode, 0)
  | .toRdf =>
    -- handled by `runToRdfEntry`; never reached through this path
    pure (.error .notJsonLd, 0)
  | .fromRdf =>
    let (ds, dropped) := parseNQuadsLenient content
    let opts : FromRdf.Options :=
      { useNativeTypes := e.useNativeTypes, useRdfType := e.useRdfType,
        rdfDirection := e.rdfDirection }
    match FromRdf.fromRdf ds opts with
    | some j => pure (.ok j, dropped)
    | none   => pure (.error .invalidJsonLiteral, dropped)
  | .compact =>
    match e.context with
    | none => pure (.error .loadingDocumentFailed, 0)
    | some ctxRel =>
      match ← readFileOpt (dir / ctxRel) with
      | none => pure (.error .loadingDocumentFailed, 0)
      | some ctxTxt =>
        pure (compactDocument loader content ctxTxt base (some (baseIri ++ ctxRel))
                e.compactArrays e.compactToRelative e.processingMode, 0)
  | .flatten =>
    match e.context with
    | none =>
      pure (flattenDocument loader content none base none e.compactArrays e.processingMode, 0)
    | some ctxRel =>
      match ← readFileOpt (dir / ctxRel) with
      | none => pure (.error .loadingDocumentFailed, 0)
      | some ctxTxt =>
        pure (flattenDocument loader content (some ctxTxt) base (some (baseIri ++ ctxRel))
                e.compactArrays e.processingMode, 0)

/-- A `jld:ToRDFTest` entry (html manifest only): produce a dataset and
compare it against the expected N-Quads, the way `Harness/JsonLdProbe`
compares toRdf — `Dataset.isomorphic?` first, RDFC-1.0 canonical N-Quads
where the bounded isomorphism search cannot decide. -/
def runToRdfEntry (loader : Loader) (baseIri : String) (dir : System.FilePath) (e : Entry)
    (base : Option String) (content : String) : IO RunResult := do
  let expCtx := e.expandContext.map (fun rel => baseIri ++ rel)
  let got := parseJsonLd loader content base none expCtx e.processingMode
  match e.kind with
  | .negative =>
    match got with
    | .error err => return { outcome := .pass, codeMatch := e.errorCode.map (fun c => c == err.code),
                             producedCode := some err.code }
    | .ok _ => return { outcome := .fail
                          s!"succeeded, but the manifest expects the error \"{e.errorCode.getD "?"}\"" }
  | _ =>
    match e.expect with
    | none => return { outcome := .fail "manifest entry has no `expect` file" }
    | some expectRel =>
      match ← readFileOpt (dir / expectRel) with
      | none => return { outcome := .fail s!"expected .nq file not found: {expectRel}" }
      | some expectTxt =>
        match got with
        | .error err => return { outcome := .fail s!"failed with \"{err.code}\" (expected a dataset)" }
        | .ok gotDs =>
          let (expDs, dropped) := parseNQuadsLenient expectTxt
          if gotDs.isomorphic? expDs || gotDs.canonicalNQuads == expDs.canonicalNQuads then
            return { outcome := .pass, droppedLines := dropped }
          else
            let g := truncate 400 gotDs.canonicalNQuads
            let x := truncate 400 expDs.canonicalNQuads
            return { outcome := .fail s!"dataset mismatch\n      expected:\n{x}\n      got:\n{g}",
                     droppedLines := dropped }

def runEntry (loader : Loader) (baseIri : String) (dir : System.FilePath) (e : Entry)
    : IO RunResult := do
  if e.kind == .unknown then
    return { outcome := .unsupported "unrecognized @type" }
  -- The html manifest's `input` may carry a fragment identifier naming
  -- the script element to select (`html/e003-in.html#second`).
  let isHtml := (Html.pathOf e.input).endsWith ".html"
  let inputPath := if isHtml then Html.pathOf e.input else e.input
  match ← readFileOpt (dir / inputPath) with
  | none =>
    if e.kind == .negative then return { outcome := .pass }
    else return { outcome := .fail s!"input file not found: {inputPath}" }
  | some content0 =>
    -- Effective document base. An HTML `<base href>` element always
    -- applies, resolved against the fallback (option.base if the test
    -- sets one, else the document URL).
    let fallback := match e.base with
                    | some b => b
                    | none   => baseIri ++ inputPath
    let base : Option String :=
      if isHtml then
        match Html.extractHtmlBase content0 with
        | some hb => some (resolveIri fallback hb)
        | none    => some fallback
      else some fallback
    -- Extract the embedded JSON-LD script(s) (API "HTML Content
    -- Algorithms"), with its two named error conditions.
    let loaded : Res (Option String) :=
      if isHtml then
        Html.loadHtmlJsonLd content0 (Html.fragmentOf e.input) e.extractAllScripts
      else .ok (some content0)
    let content ←
      match loaded with
      | .error err =>
        if e.kind == .negative then
          return { outcome := .pass, codeMatch := e.errorCode.map (fun c => c == err.code),
                   producedCode := some err.code }
        else
          return { outcome := .fail s!"HTML script extraction failed with \"{err.code}\"" }
      | .ok none =>
        -- No script extracted. For a negative test that IS the expected
        -- outcome (`loading document failed`); for a positive one the
        -- document is simply empty, so feed `[]` to the algorithm
        -- (matching bin/jsonld-html-runner).
        if e.kind == .negative then
          return { outcome := .pass,
                   codeMatch := e.errorCode.map (fun c => c == JsonLdError.loadingDocumentFailed.code),
                   producedCode := some JsonLdError.loadingDocumentFailed.code }
        else pure "[]"
      | .ok (some c) => pure c
    if e.algo == .toRdf then
      return ← runToRdfEntry loader baseIri dir e base content
    else
      let (got, dropped) ← runAlgo loader baseIri dir e base content
      match e.kind with
      | .unknown => return { outcome := .unsupported "unreachable" }
      | .negative =>
        match got with
        | .error err =>
          return { outcome := .pass, codeMatch := e.errorCode.map (fun c => c == err.code),
                   producedCode := some err.code, droppedLines := dropped }
        | .ok _ =>
          return { outcome := .fail
                     s!"succeeded, but the manifest expects the error \"{e.errorCode.getD "?"}\"",
                   droppedLines := dropped }
      | .positiveSyntax =>
        match got with
        | .ok _ => return { outcome := .pass, droppedLines := dropped }
        | .error err =>
          return { outcome := .fail s!"failed with \"{err.code}\", but the input must parse",
                   droppedLines := dropped }
      | .positive =>
        match e.expect with
        | none => return { outcome := .fail "manifest entry has no `expect` file" }
        | some expectRel =>
          match ← readFileOpt (dir / expectRel) with
          | none => return { outcome := .fail s!"expected file not found: {expectRel}" }
          | some expectTxt =>
            match got with
            | .error err =>
              return { outcome := .fail s!"failed with \"{err.code}\" (expected a document)",
                       droppedLines := dropped }
            | .ok gotJson =>
              match parseJson expectTxt with
              | .error _ => return { outcome := .fail "expected file is not valid JSON" }
              | .ok expJson =>
                if expandedEqual gotJson expJson then
                  return { outcome := .pass, droppedLines := dropped }
                else
                  let g := truncate 600 (jcsDocument gotJson)
                  let x := truncate 600 (jcsDocument expJson)
                  let note := if dropped > 0 then s!" [{dropped} unparseable input line(s) dropped]" else ""
                  return { outcome := .fail s!"output differs{note}\n      expected:\n{x}\n      got:\n{g}",
                           droppedLines := dropped }

/-! ## Local overrides -/

/-- Read `tests/local-overrides/*.json` — one object per disputed
fixture, carrying `"test_id"` and `"suite"` — and return the ids whose
`suite` matches. An absent directory means no overrides. Same layer the
F* runners read, so the two trees' `local-override` columns agree. -/
def loadLocalOverrides (root : System.FilePath) (suite : String) : IO (List String) := do
  let dir := root / "tests" / "local-overrides"
  let entries ← try dir.readDir catch _ => pure #[]
  let mut ids : List String := []
  for f in entries do
    if !f.fileName.endsWith ".json" then continue
    match ← readFileOpt (dir / f.fileName) with
    | none => pure ()
    | some txt =>
      match parseJson txt with
      | .error _ => pure ()
      | .ok j =>
        if (j.getString? "suite").getD "" == suite then
          match j.getString? "test_id" with
          | some i => ids := i :: ids
          | none   => pure ()
  pure ids

/-! ## Loader -/

def defaultTestsDir : System.FilePath := "third_party/testing/json-ld/tests"
def defaultCacheDir : System.FilePath := "third_party/jsonld-context-cache"

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

/-! ## One manifest -/

structure Score where
  pass       : Nat := 0
  fail       : Nat := 0
  overrideN  : Nat := 0
  unsupN     : Nat := 0
  codeOk     : Nat := 0
  codeSeen   : Nat := 0
  total      : Nat := 0
  deriving Repr

/-- The `suite` string `tests/local-overrides/*.json` uses for each
manifest — the F* runner names (`jsonld-compact`, `jsonld-fromrdf`),
which differ from this probe's short score-line labels. -/
def overrideSuiteName : String → String
  | "expand"  => "jsonld-expand"
  | "compact" => "jsonld-compact"
  | "flatten" => "jsonld-flatten"
  | "fromRdf" => "jsonld-fromrdf"
  | "html"    => "jsonld-html"
  | s         => s

def runManifest (dir cacheDir : System.FilePath) (root : System.FilePath)
    (manifestName : String) (dflt : Algo) (suiteName : String) (fstarLine : String)
    : IO Score := do
  let manifestPath := dir / manifestName
  if !(← manifestPath.pathExists) then
    IO.eprintln s!"l4jsonld-api: manifest not found: {manifestPath}"
    IO.eprintln "run tools/ensure-test-env.sh from the repository root first"
    return {}
  let raw ← IO.FS.readFile manifestPath
  match parseJson raw with
  | .error e =>
    IO.eprintln s!"l4jsonld-api: {manifestName} is not valid JSON: {e}"
    return {}
  | .ok mroot =>
    let baseIri := (mroot.getString? "baseIri").getD "https://w3c.github.io/json-ld-api/tests/"
    let seq := (mroot.getArray? "sequence").getD []
    let entries := seq.filterMap (entryOf dflt)
    let overrides ← loadLocalOverrides root (overrideSuiteName suiteName)
    let loader ← buildLoader dir cacheDir baseIri
    IO.println s!"manifest: {manifestPath}  ({entries.length} entries of {seq.length} sequence members)"
    let mut sc : Score := { total := entries.length }
    let mut failures : List String := []
    let mut unsupported : List String := []
    let mut codeMismatches : List String := []
    for e in entries do
      let r ← runEntry loader baseIri dir e
      match r.outcome with
      | .pass => sc := { sc with pass := sc.pass + 1 }
      | .fail msg =>
        if overrides.contains e.id then
          sc := { sc with overrideN := sc.overrideN + 1 }
        else
          sc := { sc with fail := sc.fail + 1 }
          failures := s!"{e.id} [{e.algo.label}/{e.kind.label}] {e.name}: {msg}" :: failures
      | .unsupported msg =>
        sc := { sc with unsupN := sc.unsupN + 1 }
        unsupported := s!"{e.id} {e.name}: {msg}" :: unsupported
      match r.codeMatch with
      | some ok =>
        sc := { sc with codeSeen := sc.codeSeen + 1 }
        if ok then sc := { sc with codeOk := sc.codeOk + 1 }
        else codeMismatches :=
          s!"{e.id}: manifest \"{e.errorCode.getD "?"}\" vs produced \"{r.producedCode.getD "?"}\"" :: codeMismatches
      | none => pure ()
    IO.println s!"{suiteName}: {sc.pass} pass, {sc.fail} fail, {sc.overrideN} local-override, {sc.unsupN} unsupported (out of {sc.total})"
    IO.println s!"  F* (recorded 2026-08-22, same manifest): {fstarLine}"
    IO.println s!"  negative-test error codes: {sc.codeOk} of {sc.codeSeen} match the manifest's expectErrorCode"
    if !failures.isEmpty then
      IO.println "  failures:"
      for f in failures.reverse do IO.println s!"    {f}"
    if !unsupported.isEmpty then
      IO.println "  unsupported:"
      for f in unsupported.reverse do IO.println s!"    {f}"
    if !codeMismatches.isEmpty then
      IO.println "  negative tests that failed for a DIFFERENT reason than the manifest names"
      IO.println "  (still counted as passes — the F* source has no error code to compare at all):"
      for c in codeMismatches.reverse do IO.println s!"    {c}"
    IO.println ""
    pure sc

/-! ## Main -/

def main (args : List String) : IO UInt32 := do
  let dir : System.FilePath := match args with
    | d :: _ => d
    | []     => defaultTestsDir
  let cacheDir : System.FilePath := match args with
    | _ :: c :: _ => c
    | _           => defaultCacheDir
  let root : System.FilePath := "."
  let mut scores : List (String × Score) := []
  for (mf, dflt, suite, fstar) in
      [("expand-manifest.jsonld",  Algo.expand,  "expand",
        "385 pass, 0 fail, 0 skip (out of 385)"),
       ("compact-manifest.jsonld", Algo.compact, "compact",
        "245 pass, 0 fail, 1 local-override, 0 skip (out of 246)"),
       ("flatten-manifest.jsonld", Algo.flatten, "flatten",
        "58 pass, 0 fail, 0 skip (out of 58)"),
       ("fromRdf-manifest.jsonld", Algo.fromRdf, "fromRdf",
        "53 pass, 0 fail, 1 local-override (out of 54)"),
       ("html-manifest.jsonld",    Algo.expand,  "html",
        "50 pass, 0 fail, 0 skip (out of 50)")] do
    let sc ← runManifest dir cacheDir root mf dflt suite fstar
    scores := (suite, sc) :: scores
  let ordered := scores.reverse
  let tot := ordered.foldl (fun (a : Score) (s : String × Score) =>
    { pass := a.pass + s.2.pass, fail := a.fail + s.2.fail,
      overrideN := a.overrideN + s.2.overrideN, unsupN := a.unsupN + s.2.unsupN,
      codeOk := a.codeOk + s.2.codeOk, codeSeen := a.codeSeen + s.2.codeSeen,
      total := a.total + s.2.total }) {}
  IO.println "=== score lines (Lean port, measured now) ==="
  for (suite, s) in ordered do
    IO.println s!"{suite}: {s.pass} pass, {s.fail} fail, {s.overrideN} local-override, {s.unsupN} unsupported (out of {s.total})"
  IO.println s!"TOTAL: {tot.pass} pass, {tot.fail} fail, {tot.overrideN} local-override, {tot.unsupN} unsupported (out of {tot.total})"
  IO.println s!"negative-test error codes, all manifests: {tot.codeOk} of {tot.codeSeen} match expectErrorCode"
  return 0

end JsonLdApiProbe

def main (args : List String) : IO UInt32 := JsonLdApiProbe.main args
