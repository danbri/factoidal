/-
Harness.Common — shared, PURE plumbing for the Lean W3C harness.

Everything here is a total function on strings and counters, so every
piece is checkable with `#guard` (see `Harness/HarnessTests.lean`).
The I/O lives in `Harness/Main.lean`; the RDF logic lives in the
library. This module holds three things:

  * the outcome type a single test run produces
    (`pass | fail | skip | unsupported`),
  * the score counters and the SCORE-LINE GRAMMAR — the same grammar
    `bin/w3c-runner/w3c_runner.ml` prints, with a labelled numerator
    for every bucket AND a denominator (anti-pattern #25), plus the
    `HARNESS-DIAG` line so a silently-empty run can never read as
    green,
  * the file-IRI → local-path arithmetic, ported from the F* runner's
    `iri_to_local_path` / `relpath_under` / `make_turtle_base_tc`.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/

namespace Harness

/-! ## Outcomes -/

/-- What one test case produced.

Mirrors the F* runner's `Pass | Fail of string | Skip of string`,
plus the fourth bucket this design doc requires
(`docs/designissues/2026-08-22-lean4-w3c-harness.md`): `unsupported`
names a test type the Lean tree cannot attempt yet. An unsupported
test is COUNTED and NAMED — never silently passed, never dropped from
the denominator. -/
inductive Outcome where
  | pass
  | fail (reason : String)
  | skip (reason : String)
  | unsupported (feature : String)
  deriving DecidableEq, Repr

/-- The per-test line the runner prints. -/
def Outcome.line (name : String) : Outcome → String
  | .pass            => s!"PASS {name}"
  | .fail r          => s!"FAIL {name}: {r}"
  | .skip r          => s!"SKIP {name}: {r}"
  | .unsupported f   => s!"UNSUPPORTED {name}: {f}"

/-- True for the one outcome that must make the process exit non-zero. -/
def Outcome.isFail : Outcome → Bool
  | .fail _ => true
  | _       => false

/-! ## Scores -/

/-- The four buckets. `total` is their sum, so the denominator is
always the number of manifest entries actually walked. -/
structure Score where
  pass        : Nat := 0
  fail        : Nat := 0
  skip        : Nat := 0
  unsupported : Nat := 0
  deriving DecidableEq, Repr

def Score.total (s : Score) : Nat := s.pass + s.fail + s.skip + s.unsupported

def Score.add (a b : Score) : Score :=
  { pass := a.pass + b.pass, fail := a.fail + b.fail,
    skip := a.skip + b.skip, unsupported := a.unsupported + b.unsupported }

def Score.bump (s : Score) : Outcome → Score
  | .pass          => { s with pass        := s.pass + 1 }
  | .fail _        => { s with fail        := s.fail + 1 }
  | .skip _        => { s with skip        := s.skip + 1 }
  | .unsupported _ => { s with unsupported := s.unsupported + 1 }

/-- THE score line. Same grammar as `w3c_runner`'s summary rows:
every numerator labelled, the denominator always present. -/
def Score.line (suite : String) (s : Score) : String :=
  s!"{suite}: {s.pass} pass, {s.fail} fail, {s.skip} skip, " ++
  s!"{s.unsupported} unsupported (out of {s.total})"

/-! ## Harness diagnostics

The F* runner's `HARNESS-DIAG` discipline: counters that make an empty
or aborted run visibly empty. A suite whose manifest is missing scores
`0 pass, 0 fail … (out of 0)`, which on its own reads as "nothing
wrong"; the diagnostic line is what says otherwise. -/
structure Diag where
  /-- Manifest file absent or unparseable. -/
  noManifest     : Nat := 0
  /-- Manifest parsed but yielded no entries. -/
  zeroTests      : Nat := 0
  /-- A comparison gave up: `IsoOutcome.budgetExceeded` or
  `CmpOutcome.budgetExceeded`. Counted here AND scored as `fail`,
  never as `pass`. -/
  budgetExceeded : Nat := 0
  /-- MEASUREMENT CHECK for the SPARQL evaluation tests: solution rows
  (expected + actual) and ASK booleans actually compared. A SPARQL
  suite at 100% with this at 0 compared nothing. -/
  rowsCompared   : Nat := 0
  /-- Same check for CONSTRUCT: triples (expected + actual) compared. -/
  triplesCompared : Nat := 0
  /-- Graph Store tests whose pre-state the harness MANUFACTURED from
  the entry name ("existing graph", "already in store") because the
  store did not already hold it — the F* runner's `hd_gsp_seed`
  (issue #316). A seed can turn a would-be FAIL into a PASS, so the
  count is printed. -/
  gspSeeded : Nat := 0
  deriving DecidableEq, Repr

def Diag.add (a b : Diag) : Diag :=
  { noManifest := a.noManifest + b.noManifest,
    zeroTests := a.zeroTests + b.zeroTests,
    budgetExceeded := a.budgetExceeded + b.budgetExceeded,
    rowsCompared := a.rowsCompared + b.rowsCompared,
    triplesCompared := a.triplesCompared + b.triplesCompared,
    gspSeeded := a.gspSeeded + b.gspSeeded }

def Diag.line (label : String) (d : Diag) : String :=
  s!"HARNESS-DIAG {label}: no_manifest={d.noManifest} " ++
  s!"zero_tests={d.zeroTests} budget_exceeded={d.budgetExceeded} " ++
  s!"rows_compared={d.rowsCompared} triples_compared={d.triplesCompared} " ++
  s!"gsp_seeded={d.gspSeeded}"

/-! ## String / path arithmetic

Ported from `bin/w3c-runner/w3c_runner.ml`. Kept pure so the
`#guard`s can pin the exact behaviour the F* runner has. -/

/-- Text after the LAST occurrence of `sep` in `s`; `s` itself when
`sep` does not occur. `"a/b/c" `lastAfter` "/" = "c"`. -/
def lastAfter (s sep : String) : String :=
  match (s.splitOn sep).getLast? with
  | some x => if (s.splitOn sep).length ≤ 1 then s else x
  | none   => s

/-- The local name of an IRI: the part after the last `#`, or the whole
IRI when there is none. This is EXACTLY the F* runner's namespace
strip (`String.rindex_opt s '#'`) — deliberately not "after the last
`/`", because manifest test types are all hash IRIs and a slash-strip
would mangle types that have none. -/
def localName (iri : String) : String :=
  let parts := iri.splitOn "#"
  if parts.length ≤ 1 then iri
  else match parts.getLast? with
       | some x => x
       | none   => iri

/-- Everything before the last `/`; `"."` when there is none. The
`Filename.dirname` the F* runner applies to a manifest path. -/
def dirname (p : String) : String :=
  let parts := p.splitOn "/"
  if parts.length ≤ 1 then "."
  else
    let d := String.intercalate "/" (parts.dropLast)
    if d.isEmpty then "/" else d

/-- Everything after the last `/`. -/
def basename (p : String) : String := lastAfter p "/"

/-- Strip a `file://` scheme prefix, leaving the path. -/
def stripFileScheme (s : String) : String :=
  if s.startsWith "file://" then String.ofList (s.toList.drop "file://".length) else s

/-- Port of `iri_to_local_path`. The manifest is parsed with base
`file://<absolute manifest path>`, so a relative entry `<x.ttl>`
arrives here already resolved to `file:///…/x.ttl` and the scheme
strip alone yields the path. An absolute IRI in some other scheme
falls back to `<manifestDir>/<basename>`; a bare relative string
(which a lenient parse can leave behind) to `<manifestDir>/<s>`. -/
def iriToLocalPath (manifestDir iri : String) : String :=
  if iri.startsWith "file://" then stripFileScheme iri
  else if iri.toList.contains ':' then manifestDir ++ "/" ++ basename iri
  else manifestDir ++ "/" ++ iri

/-- Port of `relpath_under`: the path of `filePath` relative to
`manifestDir` when it sits underneath it, else its basename. Suites
that nest fixtures in subdirectories (rdf-xml, parts of rdf-trig) need
the sub-path in the base IRI, not just the file name. -/
def relpathUnder (manifestDir filePath : String) : String :=
  let mdSlash := if manifestDir.endsWith "/" then manifestDir else manifestDir ++ "/"
  if filePath.startsWith mdSlash then String.ofList (filePath.toList.drop mdSlash.length)
  else basename filePath

/-- Port of `make_turtle_base_tc`: the retrieval IRI a fixture is
parsed against. With an `mf:assumedTestBase` in the manifest (every
rdf11 syntax suite has one) it is that base plus the manifest-relative
path; without one, the `file://` URI of the fixture. -/
def fixtureBase (assumedBase : Option String) (manifestDir filePath : String) : String :=
  match assumedBase with
  | some b => b ++ relpathUnder manifestDir filePath
  | none   => "file://" ++ filePath

/-- The suite name a score line carries: the manifest's parent
directory, which is how the F* runner's dashboard names these suites
(`rdf-turtle`, `rdf-trig`, …). Two directory names name nothing on
their own and take the grandparent as well:

  * `tests` — the rdf-canon manifest sits in a directory literally
    called that, so the label falls back to `rdf-canon`;
  * `syntax` / `eval` / `c14n` — every rdf12 leaf manifest sits under
    one of these, so the label is `<format>/<leaf>`
    (`rdf-turtle/syntax`, `rdf-n-quads/c14n`), exactly the names
    `bin/w3c-runner/w3c_runner.ml`'s `--rdf12` mode prints. -/
def suiteLabel (manifestPath : String) : String :=
  let d := basename (dirname manifestPath)
  if d == "tests" || d == "." || d.isEmpty then
    let up := basename (dirname (dirname manifestPath))
    if up.isEmpty || up == "." then d else up
  else if d == "syntax" || d == "eval" || d == "c14n" then
    let up := basename (dirname (dirname manifestPath))
    if up.isEmpty || up == "." then d else up ++ "/" ++ d
  else d

/-- Drop trailing CR/LF so a missing or extra final newline is not a
difference. The only normalisation the byte comparisons apply. -/
def trimTrailingNewlines (s : String) : String :=
  String.ofList (s.toList.reverse.dropWhile (fun c => c == '\n' || c == '\r')).reverse

/-! ## IO helpers -/

/-- Read a file, `none` when it is absent or undecodable. -/
def readOpt (p : System.FilePath) : IO (Option String) := do
  try
    let s ← IO.FS.readFile p
    return some s
  catch _ =>
    return none

end Harness
