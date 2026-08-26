/-
Wasm.Cli — `l4factoidal`, a real command-line interface to the Lean 4
engine, so a person or a script can use it without knowing the
dispatch ABI (`Wasm/Dispatch.lean`).

This module is thin argument parsing and JSON-envelope decoding ONLY.
Every verb below calls one of the `Wasm/Ops/*.lean` functions the wasm
build and `l4wasm-cli` also call — the same `parseToDatasetJson`,
`queryDataset`, `owlClosure`, `clParse`, … — and prints the field a
person wants from the envelope those functions already return. No RDF,
SPARQL, OWL or CL semantics live here.

  l4factoidal parse data.ttl --out nquads
  l4factoidal query data.ttl --query-string 'SELECT * WHERE { ?s ?p ?o }'
  l4factoidal help          -- full verb list

`l4wasm-cli` (`Wasm/Main.lean`) stays as it is — the ABI smoke driver
`Wasm/native-smoke.sh` pins — and is unaffected by this module.
-/
import Wasm.Abi
import Wasm.Dispatch

namespace L4Wasm.Cli

open L4Factoidal.RDF
open L4Factoidal.Syntax
open L4Factoidal.JSON
open L4Wasm.Ops

/-! ## Argument scanning

A minimal flag scanner shared by every verb: `--flag value` pairs
(`valueFlags`), bare boolean flags (`boolFlags`), everything else
positional, in the order given. No logic beyond bucketing strings. -/

structure Scanned where
  positional : List String := []
  values     : List (String × String) := []
  bools      : List String := []

/-- Bucket `args` into positionals / `--flag value` pairs / bare
boolean flags. An unrecognised `--…` token, or a value flag with
nothing after it, is a usage error. Structurally recursive on the
remaining argument list. -/
def scanArgs (valueFlags boolFlags : List String) :
    List String → Except String Scanned
  | [] => .ok {}
  | a :: rest =>
      if boolFlags.contains a then
        (scanArgs valueFlags boolFlags rest).map fun s =>
          { s with bools := a :: s.bools }
      else if valueFlags.contains a then
        match rest with
        | [] => .error s!"{a}: missing value"
        | v :: rest' =>
            (scanArgs valueFlags boolFlags rest').map fun s =>
              { s with values := (a, v) :: s.values }
      else if a.take 2 == "--" then
        .error s!"unknown flag '{a}'"
      else
        (scanArgs valueFlags boolFlags rest).map fun s =>
          { s with positional := a :: s.positional }

def Scanned.value? (s : Scanned) (flag : String) : Option String :=
  (s.values.find? (fun kv => kv.1 == flag)).map Prod.snd

def Scanned.hasBool (s : Scanned) (flag : String) : Bool :=
  s.bools.contains flag

/-! ## Input reading

Every read goes through here so a missing file or an unreadable stdin
reports as ONE clean stderr line and exit 1, never a raw Lean
exception trace. -/

/-- Read `pathOpt` — a file, or `none` / `some "-"` for stdin. -/
def readInput (pathOpt : Option String) : IO (Except String String) := do
  match pathOpt with
  | none | some "-" =>
      try
        let t ← (← IO.getStdin).readToEnd
        pure (.ok t)
      catch e =>
        pure (.error s!"stdin: {e}")
  | some path =>
      try
        let t ← IO.FS.readFile path
        pure (.ok t)
      catch e =>
        pure (.error s!"{path}: {e}")

/-- Read `pathOpt` under `formatTag`/`baseIri` via the SAME
`parseTextToDataset` the dispatch ops use, and re-serialise to
canonical N-Quads — the input path every RDF-consuming verb below
shares (`query`, `update`, `canonicalize`, `closure`, `owl-consistent`,
`owl-entails`), because every stateless op past `parse`
itself takes N-Quads text (`Wasm/Ops/*.lean` module headers). -/
def readAsNQuads (pathOpt : Option String) (formatTag baseIri : String) :
    IO (Except String String) := do
  match ← readInput pathOpt with
  | .error e => pure (.error e)
  | .ok text =>
      match Ops.parseTextToDataset text formatTag baseIri with
      | .error e => pure (.error e)
      | .ok ds => pure (.ok (Dataset.toCanonicalNQuads ds))

/-- Resolve a `--foo FILE` / `--foo-string TEXT` pair (exactly one of
the two) into the text it names — shared by `query` and `update`.
The `Except UInt32` error already carries the exit code
the caller should return (2 for a usage mistake). -/
def resolveTextArg (verb fileFlag strFlag what : String) (s : Scanned) :
    IO (Except UInt32 String) := do
  match s.value? fileFlag, s.value? strFlag with
  | some _, some _ =>
      IO.eprintln s!"l4factoidal {verb}: pass only one of {fileFlag} / {strFlag}"
      pure (.error 2)
  | some f, none =>
      match ← readInput (some f) with
      | .error e => IO.eprintln e; pure (.error 1)
      | .ok t => pure (.ok t)
  | none, some txt => pure (.ok txt)
  | none, none =>
      IO.eprintln s!"l4factoidal {verb}: need {fileFlag} FILE or {strFlag} {what}"
      pure (.error 2)

/-! ## JSON envelope decoding

Every op answers `{"ok":true,…}` or `{"ok":false,"error":"…"}`
(`Wasm/Ops/Support.lean`). Decode once, print the error and hand back
`none` on failure, so every verb below shares one error path. -/

/-- Decode an op's JSON envelope. `none` means the error is already
printed to stderr; the caller returns exit 1. -/
def parseEnvelope (raw : String) : IO (Option Json) := do
  match parseJson raw with
  | .error e =>
      IO.eprintln s!"internal: op result was not JSON ({toString e})"
      pure none
  | .ok j =>
      if j.getBool? "ok" == some true then
        pure (some j)
      else
        IO.eprintln ((j.getString? "error").getD "unknown error")
        pure none

/-- A JSON NUMBER field (RFC 8259 §6 lexeme, kept verbatim by
`L4Factoidal.JSON` — see `JSON/Value.lean`'s module header), e.g.
`parseToDatasetJson`'s `"count"`. `Json.getString?` does not see this
field: it matches `.string` only, never `.number`. -/
def numberField? (j : Json) (key : String) : Option String :=
  match j.field? key with
  | some (.number s) => some s
  | _ => none

/-- `{"fuel":"<n>"}` or `""` — the `optsJson` argument `owlIsConsistent`
/ `owlEntails` take (`Wasm/Ops/Reason.lean`'s `owlRefuteFuelOfOpts`). -/
def optsJsonOfFuel : Option String → String
  | none => ""
  | some fuel => (Json.object [("fuel", Json.string fuel)]).toString

/-- Print a three-valued verdict field (`consistent` / `entailed`):
`true`/`false`/`unknown` to stdout, the `reason` (present on
`false`/`null`) to stderr. Exit 0 for `true`, 1 for `false` or
`unknown` — a verdict this CLI cannot tell apart from a plain failure
by exit code alone, so a script that must distinguish "refuted" from
"budget-out, raise --fuel" reads stdout, not just `$?`. -/
def printVerdict (j : Json) (key : String) : IO UInt32 := do
  let printReason : IO Unit :=
    match j.getString? "reason" with
    | some r => IO.eprintln r
    | none => pure ()
  match j.field? key with
  | some (.bool true) => IO.println "true"; pure 0
  | some (.bool false) => IO.println "false"; printReason; pure 1
  | some .null => IO.println "unknown"; printReason; pure 1
  | _ =>
      IO.eprintln s!"internal: '{key}' verdict missing or malformed"
      pure 1

/-! ## SELECT results: SPARQL Results JSON, or `--table` -/

def bindingValue? (row : Json) (v : String) : Option String :=
  (row.field? v).bind (fun t => t.getString? "value")

/-- Tab-separated: a header row of variable names, then one row per
binding (unbound = empty cell). Not a replacement for the JSON form —
a quick-look shortcut for a terminal or a shell pipeline. -/
def printSelectTable (srj : Json) : IO Unit := do
  let vars := ((srj.field? "head").bind (fun h => h.getStringArray? "vars")).getD []
  IO.println (String.intercalate "\t" vars)
  let rows := ((srj.field? "results").bind (fun r => r.getArray? "bindings")).getD []
  for row in rows do
    IO.println (String.intercalate "\t" (vars.map fun v => (bindingValue? row v).getD ""))

/-- Print the `queryDataset` envelope family
(select/ask/construct — DESCRIBE is already an error envelope, handled
by `parseEnvelope`). -/
def printQueryResult (j : Json) (table : Bool) : IO UInt32 := do
  match j.getString? "kind" with
  | some "ask" =>
      match j.getBool? "boolean" with
      | some true => IO.println "true"; pure 0
      | some false => IO.println "false"; pure 1
      | none => IO.eprintln "internal: ask result missing boolean"; pure 1
  | some "construct" =>
      IO.println ((j.getString? "nquads").getD "")
      pure 0
  | some "select" =>
      match j.field? "srj" with
      | none => IO.eprintln "internal: select result missing srj"; pure 1
      | some srj =>
          if table then printSelectTable srj else IO.println srj.toStringPretty
          pure 0
  | _ =>
      IO.eprintln "internal: unrecognised query result kind"
      pure 1

/-! ## Verbs -/

def versionCmd : IO UInt32 := do
  IO.println L4Wasm.version
  IO.println s!"dispatch ABI: {L4Wasm.dispatchAbiVersion}"
  pure 0

def opsCmd : IO UInt32 := do
  let raw ← L4Wasm.callIO "ops" "[]"
  match parseJson raw with
  | .ok j => IO.println j.toStringPretty
  | .error _ => IO.println raw
  pure 0

def parseCmd (args : List String) : IO UInt32 := do
  match scanArgs ["--format", "--base", "--out"] [] args with
  | .error e => IO.eprintln s!"l4factoidal parse: {e}"; pure 2
  | .ok s =>
    let format := (s.value? "--format").getD "turtle"
    let base := (s.value? "--base").getD ""
    match ← readInput s.positional[0]? with
    | .error e => IO.eprintln e; pure 1
    | .ok text =>
      match ← parseEnvelope (Ops.parseToDatasetJson text format base) with
      | none => pure 1
      | some j =>
        match s.value? "--out" with
        | none => IO.println ((numberField? j "count").getD "0"); pure 0
        | some "nquads" =>
            IO.println ((j.getString? "nquads").getD "")
            pure 0
        | some "turtle" =>
            let nq := (j.getString? "nquads").getD ""
            match ← parseEnvelope (Ops.serializeTurtle nq) with
            | none => pure 1
            | some jt => IO.println ((jt.getString? "turtle").getD ""); pure 0
        | some other =>
            IO.eprintln s!"l4factoidal parse: unknown --out '{other}' (nquads | turtle)"
            pure 2

def queryCmd (args : List String) : IO UInt32 := do
  match scanArgs ["--format", "--base", "--query", "--query-string"] ["--table"] args with
  | .error e => IO.eprintln s!"l4factoidal query: {e}"; pure 2
  | .ok s =>
    match ← resolveTextArg "query" "--query" "--query-string" "SPARQL" s with
    | .error code => pure code
    | .ok sparql =>
      let format := (s.value? "--format").getD "turtle"
      let base := (s.value? "--base").getD ""
      match ← readAsNQuads s.positional[0]? format base with
      | .error e => IO.eprintln e; pure 1
      | .ok nq =>
        match ← parseEnvelope (Ops.queryDataset nq sparql) with
        | none => pure 1
        | some j => printQueryResult j (s.hasBool "--table")

def updateCmd (args : List String) : IO UInt32 := do
  match scanArgs ["--format", "--base", "--update", "--update-string"] [] args with
  | .error e => IO.eprintln s!"l4factoidal update: {e}"; pure 2
  | .ok s =>
    match ← resolveTextArg "update" "--update" "--update-string" "SPARQL-UPDATE" s with
    | .error code => pure code
    | .ok upd =>
      let format := (s.value? "--format").getD "turtle"
      let base := (s.value? "--base").getD ""
      match ← readAsNQuads s.positional[0]? format base with
      | .error e => IO.eprintln e; pure 1
      | .ok nq =>
        match ← parseEnvelope (Ops.updateDataset nq upd) with
        | none => pure 1
        | some j => IO.println ((j.getString? "nquads").getD ""); pure 0

def canonicalizeCmd (args : List String) : IO UInt32 := do
  match scanArgs ["--format", "--base"] [] args with
  | .error e => IO.eprintln s!"l4factoidal canonicalize: {e}"; pure 2
  | .ok s =>
    let format := (s.value? "--format").getD "nquads"
    let base := (s.value? "--base").getD ""
    match ← readAsNQuads s.positional[0]? format base with
    | .error e => IO.eprintln e; pure 1
    | .ok nq =>
      match ← parseEnvelope (Ops.canonicalizeToNQuads nq) with
      | none => pure 1
      | some j => IO.println ((j.getString? "nquads").getD ""); pure 0

def closureCmd (args : List String) : IO UInt32 := do
  match scanArgs ["--format", "--base", "--regime"] [] args with
  | .error e => IO.eprintln s!"l4factoidal closure: {e}"; pure 2
  | .ok s =>
    match s.value? "--regime" with
    | none =>
        IO.eprintln "l4factoidal closure: need --regime rdfs|rho-df|rdfs-plus|owl-rl"
        pure 2
    | some regime =>
      if !(["rdfs", "owl-rl", "rho-df", "rdfs-plus"].contains regime) then
        IO.eprintln s!"l4factoidal closure: unknown --regime '{regime}' (rdfs | rho-df | rdfs-plus | owl-rl)"
        pure 2
      else
        let format := (s.value? "--format").getD "turtle"
        let base := (s.value? "--base").getD ""
        match ← readAsNQuads s.positional[0]? format base with
        | .error e => IO.eprintln e; pure 1
        | .ok nq =>
          let raw :=
            match regime with
            | "rdfs"      => Ops.owlClosure nq "RDFS"
            | "owl-rl"    => Ops.owlClosure nq "OWL-RL"
            | "rho-df"    => Ops.rhoDfClosure nq
            | _           => Ops.rdfsPlusClosure nq
          match ← parseEnvelope raw with
          | none => pure 1
          | some j =>
              let out := (j.getString? "nquads") <|> (j.getString? "ntriples")
              IO.println (out.getD "")
              pure 0

def owlConsistentCmd (args : List String) : IO UInt32 := do
  match scanArgs ["--format", "--base", "--fuel"] [] args with
  | .error e => IO.eprintln s!"l4factoidal owl-consistent: {e}"; pure 2
  | .ok s =>
    let format := (s.value? "--format").getD "turtle"
    let base := (s.value? "--base").getD ""
    let opts := optsJsonOfFuel (s.value? "--fuel")
    match ← readAsNQuads s.positional[0]? format base with
    | .error e => IO.eprintln e; pure 1
    | .ok nq =>
      match ← parseEnvelope (Ops.owlIsConsistent nq opts) with
      | none => pure 1
      | some j => printVerdict j "consistent"

def owlEntailsCmd (args : List String) : IO UInt32 := do
  match scanArgs ["--format", "--base", "--fuel"] [] args with
  | .error e => IO.eprintln s!"l4factoidal owl-entails: {e}"; pure 2
  | .ok s =>
    match s.positional[0]?, s.positional[1]? with
    | some premiseFile, some conclFile =>
        let format := (s.value? "--format").getD "turtle"
        let base := (s.value? "--base").getD ""
        let opts := optsJsonOfFuel (s.value? "--fuel")
        match ← readAsNQuads (some premiseFile) format base with
        | .error e => IO.eprintln e; pure 1
        | .ok premiseNq =>
          match ← readAsNQuads (some conclFile) format base with
          | .error e => IO.eprintln e; pure 1
          | .ok conclNq =>
            match ← parseEnvelope (Ops.owlEntails premiseNq conclNq opts) with
            | none => pure 1
            | some j => printVerdict j "entailed"
    | _, _ =>
        IO.eprintln "l4factoidal owl-entails: need PREMISE_FILE CONCLUSION_FILE"
        pure 2

/-! ## `cl` — Common Logic / IKL -/

def clParseCmd (args : List String) : IO UInt32 := do
  match scanArgs [] [] args with
  | .error e => IO.eprintln s!"l4factoidal cl parse: {e}"; pure 2
  | .ok s =>
    match ← readInput s.positional[0]? with
    | .error e => IO.eprintln e; pure 1
    | .ok text =>
      match ← parseEnvelope (Ops.clParse text) with
      | none => pure 1
      | some j => IO.println j.toStringPretty; pure 0

/-- The three text-shaped CL ops share `cl parse`'s shape: read one
CLIF text, print one envelope. `label` is only for the error line. -/
def clTextCmd (label : String) (op : String → String) (args : List String) :
    IO UInt32 := do
  match scanArgs [] [] args with
  | .error e => IO.eprintln s!"l4factoidal cl {label}: {e}"; pure 2
  | .ok s =>
    match ← readInput s.positional[0]? with
    | .error e => IO.eprintln e; pure 1
    | .ok text =>
      match ← parseEnvelope (op text) with
      | none => pure 1
      | some j => IO.println j.toStringPretty; pure 0

/-- `cl finite-sat INTERP.json [FILE]` — the one CL op taking two
arguments. The interpretation is a FILE rather than a flag value: it is
a JSON document (see `Wasm/Ops/CL.lean`'s wire-format note), and a
shell quoting it inline is how a domain label acquires a stray quote. -/
def clFiniteSatCmd (args : List String) : IO UInt32 := do
  match scanArgs [] [] args with
  | .error e => IO.eprintln s!"l4factoidal cl finite-sat: {e}"; pure 2
  | .ok s =>
    match s.positional[0]? with
    | none =>
        IO.eprintln "l4factoidal cl finite-sat: need INTERP.json [FILE]"
        pure 2
    | some interpFile =>
      match ← readInput (some interpFile) with
      | .error e => IO.eprintln e; pure 1
      | .ok interpJson =>
        match ← readInput s.positional[1]? with
        | .error e => IO.eprintln e; pure 1
        | .ok text =>
          match ← parseEnvelope (Ops.clFiniteSat interpJson text) with
          | none => pure 1
          | some j => IO.println j.toStringPretty; pure 0

def clCmd (sub : String) (args : List String) : IO UInt32 :=
  match sub with
  | "parse"      => clParseCmd args
  | "serialize"  => clTextCmd "serialize" Ops.clSerialize args
  | "alpha-norm" => clTextCmd "alpha-norm" Ops.clAlphaNorm args
  | "normalize"  => clTextCmd "normalize" Ops.clNormalize args
  | "finite-sat" => clFiniteSatCmd args
  | other => do
      IO.eprintln s!"l4factoidal cl: unknown subcommand '{other}' \
(parse | serialize | alpha-norm | normalize | finite-sat)"
      pure 2

/-! ## Help + dispatch -/

def usageLines : List String :=
  [ "l4factoidal — Lean 4 RDF/SPARQL/OWL/CL engine, command line"
  , ""
  , "Usage: l4factoidal VERB [options] [FILE...]"
  , ""
  , "Verbs:"
  , "  parse [FILE] [--format FMT] [--base IRI] [--out nquads|turtle]"
  , "      Parse RDF and print the quad count, or (with --out) N-Quads"
  , "      or Turtle. FILE omitted or \"-\" reads stdin. FMT: turtle |"
  , "      ntriples | nquads | trig | rdfxml (default turtle)."
  , "  query [FILE] (--query FILE.rq | --query-string SPARQL)"
  , "        [--format FMT] [--table]"
  , "      Run a SPARQL query. SELECT prints SPARQL Results JSON (or a"
  , "      tab-separated table with --table); ASK prints true/false,"
  , "      exit 0 for true and 1 for false; CONSTRUCT prints N-Quads."
  , "  update [FILE] (--update FILE.ru | --update-string SPARQL-UPDATE)"
  , "        [--format FMT]"
  , "      Apply a SPARQL Update and print the resulting N-Quads."
  , "  canonicalize [FILE] [--format FMT]"
  , "      RDFC-1.0 canonical N-Quads (default input format: nquads)."
  , "  closure [FILE] --regime rdfs|rho-df|rdfs-plus|owl-rl [--format FMT]"
  , "      Print the entailment closure (N-Quads, or N-Triples for"
  , "      rho-df / rdfs-plus)."
  , "  owl-consistent [FILE] [--format FMT] [--fuel N]"
  , "      Three-valued OWL DL consistency check: prints true, false,"
  , "      or unknown (budget-out; raise --fuel). Exit 0 for true,"
  , "      1 for false or unknown — read stdout to tell those apart."
  , "  owl-entails PREMISE_FILE CONCLUSION_FILE [--format FMT] [--fuel N]"
  , "      Three-valued OWL DL entailment check, same convention."
  , "  cl parse [FILE]"
  , "      Parse a Common Logic / IKL text; print sentence count,"
  , "      whether it is pure CL, and the canonical re-serialisation."
  , "  cl serialize [FILE]"
  , "      Re-serialise a CLIF text in canonical spacing. Reports"
  , "      roundTripProved:false — clif_roundTrip is an open lemma."
  , "  cl alpha-norm [FILE]"
  , "      Canonical representative of each sentence's"
  , "      alpha-equivalence class (bound names become v1, v2, …), so"
  , "      alpha-variants serialise byte-identically."
  , "  cl normalize [FILE]"
  , "      Hayes's reduction of IKL to Common Logic: a head text and a"
  , "      shared tail. Preserves SATISFIABILITY, not equivalence."
  , "      Reports noIntrusion — the proof hypothesis, decided; when it"
  , "      is false the output is outside what is proved."
  , "  cl finite-sat INTERP.json [FILE]"
  , "      Decide satisfaction of a CLIF text against the finite"
  , "      interpretation in INTERP.json. Refuses a text that"
  , "      quantifies a sequence marker, naming the condition."
  , "  version"
  , "      Print the engine version and the dispatch ABI version."
  , "  ops"
  , "      List every dispatch ABI operation (the l4wasm-cli / wasm"
  , "      surface this CLI is built on)."
  , ""
  , "Exit codes: 0 success/true, 1 failure/false/error, 2 usage error."
  ]

def usageText : String := String.intercalate "\n" usageLines

def main (args : List String) : IO UInt32 := do
  match args with
  | [] =>
      IO.eprintln "l4factoidal: missing verb (try 'l4factoidal help')"
      pure 2
  | "help" :: _ | "--help" :: _ | "-h" :: _ =>
      IO.println usageText
      pure 0
  | "version" :: _ => versionCmd
  | "ops" :: _ => opsCmd
  | "parse" :: rest => parseCmd rest
  | "query" :: rest => queryCmd rest
  | "update" :: rest => updateCmd rest
  | "canonicalize" :: rest => canonicalizeCmd rest
  | "closure" :: rest => closureCmd rest
  | "owl-consistent" :: rest => owlConsistentCmd rest
  | "owl-entails" :: rest => owlEntailsCmd rest
  | "cl" :: sub :: rest => clCmd sub rest
  | "cl" :: [] =>
      IO.eprintln "l4factoidal cl: need a subcommand \
(parse | serialize | alpha-norm | normalize | finite-sat)"
      pure 2
  | cmd :: _ =>
      IO.eprintln s!"l4factoidal: unknown verb '{cmd}' (try 'l4factoidal help')"
      pure 2

end L4Wasm.Cli

/-- Lake's executable entry point: `lean_exe l4factoidal` needs a
top-level `main`, matching `Harness/Main.lean`'s convention for a
namespaced implementation. -/
def main (args : List String) : IO UInt32 := L4Wasm.Cli.main args
