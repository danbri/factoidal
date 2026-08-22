/-
Harness.Manifest — read a W3C `manifest.ttl` with the Lean Turtle
parser and turn it into the `TestCase` records the runner dispatches
on.

Iron rule #6: the manifest is the REAL file off disk, parsed by the
engine under test. That is the point of this rung — the suites'
manifests are Turtle, so a Turtle parser is what makes them readable,
and the harness proves it by depending on nothing else.

The model of a test entry is the F* runner's
(`bin/w3c-runner/w3c_runner.ml`, `extract_test_cases` ~line 380 and
`read_manifest` ~line 602), reproduced clause for clause:

  * the manifest is parsed with base `file://<absolute manifest path>`,
    so relative entry references resolve to `file://` URIs that
    `iriToLocalPath` turns straight back into paths;
  * `mf:entries` heads an RDF COLLECTION — an `rdf:first`/`rdf:rest`
    chain ending in `rdf:nil` — walked in list order, so the printed
    per-test lines come out in the manifest's own order;
  * the test type is the local name of the FIRST `rdf:type`
    (namespace stripped at the last `#`);
  * `mf:action` is either a file IRI (every rdf11 syntax suite and the
    rdf-canon suite) or a blank node carrying `qt:query` / `qt:data` /
    `qt:graphData` (the SPARQL-shaped suites). Both shapes are
    recorded; which one a runner uses is its business;
  * `rdft:approval` is RECORDED, not filtered on. The F* runner runs
    Approved, Proposed and Rejected entries alike — it never consults
    approval — and its denominators (rdf-turtle 313, rdf-trig 356 …)
    are the full typed-entry counts. Matching those denominators means
    matching that treatment;
  * an entry whose type the runner cannot execute STILL produces a
    `TestCase`. It is scored `unsupported` and stays in the
    denominator; dropping it here would silently shrink the total.

No `sorry`, no `axiom`, no `native_decide`, no `partial`: the
collection walk is fuel-bounded by the triple count, which bounds any
`rdf:rest` chain the graph can contain.
-/
import L4Factoidal.Syntax.Turtle
import Harness.Common

open L4Factoidal.RDF
open L4Factoidal.Syntax

namespace Harness

/-! ## Vocabulary IRIs -/

def mfNs   : String := "http://www.w3.org/2001/sw/DataAccess/tests/test-manifest#"
def qtNs   : String := "http://www.w3.org/2001/sw/DataAccess/tests/test-query#"
def rdfNs  : String := "http://www.w3.org/1999/02/22-rdf-syntax-ns#"
def rdftNs : String := "http://www.w3.org/ns/rdftest#"
def rdfcNs : String := "https://w3c.github.io/rdf-canon/tests/vocab#"

def rdfType  : String := rdfNs ++ "type"
def rdfFirst : String := rdfNs ++ "first"
def rdfRest  : String := rdfNs ++ "rest"
def rdfNil   : String := rdfNs ++ "nil"

/-! ## Graph lookup helpers

`Graph` is `List Triple`, so these are the same linear scans the F*
runner does — specification shape, not an index (the spec/pragmatics
split: no engine machinery in the Lean tree). -/

/-- A comparable key for a term: an IRI's text, a blank node's label,
a literal's lexical form. Port of the F* runner's `term_to_str`. -/
def termKey : Term → String
  | .iri i          => i.val
  | .bnode b        => b
  | .literal l      => l.val.lexicalForm
  | .tripleTerm _ _ _ => ""

def subjKey : Subject → String
  | .iri i   => i.val
  | .bnode b => b

/-- The subject position corresponding to a term, when the term can
occupy one (IRIs and blank nodes can; literals cannot). -/
def subjectOfTerm : Term → Option Subject
  | .iri i   => some (.iri i)
  | .bnode b => some (.bnode b)
  | _        => none

/-- Objects of `(s, p, ?)` in list order. -/
def findObjects (g : Graph) (s : Subject) (p : String) : List Term :=
  g.filterMap (fun t => if t.s == s && t.p.val == p then some t.o else none)

def findObject? (g : Graph) (s : Subject) (p : String) : Option Term :=
  (findObjects g s p).head?

/-- Walk an RDF collection (`rdf:first`/`rdf:rest`, terminated by
`rdf:nil`) rooted at `node`, returning its members in list order.

`fuel` bounds the walk; callers pass the graph's triple count, and no
chain can be longer than that because each link consumes an
`rdf:rest` triple. This is what keeps the function total — no
`partial`, no well-founded-recursion obligation. -/
def collectList (g : Graph) : Nat → Term → List Term
  | 0, _ => []
  | fuel + 1, node =>
    let sOpt : Option Subject :=
      match node with
      | .iri i   => if i.val == rdfNil then none else some (.iri i)
      | .bnode b => some (.bnode b)
      | _        => none
    match sOpt with
    | none   => []
    | some s =>
      let heads := match (findObjects g s rdfFirst).head? with
                   | some h => [h]
                   | none   => []
      match (findObjects g s rdfRest).head? with
      | some r => heads ++ collectList g fuel r
      | none   => heads

/-! ## The test case record -/

/-- One manifest entry, in the shape the F* runner models it.

`action` is the resolved local path when `mf:action` is a file IRI —
which is every entry in the rdf11 syntax suites and the rdf-canon
suite. `queryFile` / `dataFiles` / `graphData` carry the
SPARQL-shaped bnode action instead; they are STORED now and consumed
when the SPARQL rungs land (there is no Lean SPARQL string parser
yet). -/
structure TestCase where
  /-- `mf:name`, falling back to the entry node's own identifier. -/
  name       : String
  /-- The entry node's IRI text or blank-node label. -/
  entryId    : String
  /-- Local name of the first `rdf:type`, e.g. `TestTurtleEval`.
  `"Unknown"` when the entry carries no type. -/
  testType   : String
  /-- `mf:action` as a local path, when it is a plain file IRI. -/
  action     : Option String
  /-- `qt:query` as a local path (bnode-shaped action). -/
  queryFile  : Option String
  /-- `qt:data` as local paths (bnode-shaped action). -/
  dataFiles  : List String
  /-- `qt:graphData`: (graph IRI, local path) pairs. -/
  graphData  : List (String × String)
  /-- `mf:result` as a local path. -/
  resultFile : Option String
  /-- Local name of `rdft:approval` (`Approved` / `Proposed` /
  `Rejected` / …), `""` when the entry omits it. Recorded, never
  filtered on — see the module header. -/
  approval   : String
  /-- `rdfc:hashAlgorithm`, e.g. `"SHA384"` (rdf-canon only). -/
  hashAlgorithm : Option String
  deriving Repr

/-- One entry → one `TestCase`. Total: never returns `none`, because
an entry the runner cannot execute must still occupy a slot in the
denominator. -/
def extractTestCase (manifestDir : String) (g : Graph) (entry : Term) : TestCase :=
  let entryId := termKey entry
  match subjectOfTerm entry with
  | none => { name := entryId, entryId, testType := "Unknown", action := none,
              queryFile := none, dataFiles := [], graphData := [],
              resultFile := none, approval := "", hashAlgorithm := none }
  | some subj =>
    let testType :=
      match findObject? g subj rdfType with
      | some t => localName (termKey t)
      | none   => "Unknown"
    let name :=
      match findObject? g subj (mfNs ++ "name") with
      | some t => termKey t
      | none   => entryId
    let approval :=
      match findObject? g subj (rdftNs ++ "approval") with
      | some t => localName (termKey t)
      | none   => ""
    let hashAlgorithm := (findObject? g subj (rdfcNs ++ "hashAlgorithm")).map termKey
    let resultFile :=
      (findObject? g subj (mfNs ++ "result")).map (fun t => iriToLocalPath manifestDir (termKey t))
    -- `mf:action`: a file IRI, or a bnode carrying qt: predicates.
    let actionTerm := findObject? g subj (mfNs ++ "action")
    let (action, queryFile, dataFiles, graphData) :=
      match actionTerm with
      | some (.iri i) =>
          (some (iriToLocalPath manifestDir i.val), none, ([] : List String),
           ([] : List (String × String)))
      | some other =>
          match subjectOfTerm other with
          | none => (none, none, [], [])
          | some aSubj =>
            let q := (findObject? g aSubj (qtNs ++ "query")).map
                       (fun t => iriToLocalPath manifestDir (termKey t))
            let d := (findObjects g aSubj (qtNs ++ "data")).map
                       (fun t => iriToLocalPath manifestDir (termKey t))
            let gd := (findObjects g aSubj (qtNs ++ "graphData")).map (fun t =>
                        let iri := termKey t
                        (iri, iriToLocalPath manifestDir iri))
            (none, q, d, gd)
      | none => (none, none, [], [])
    { name, entryId, testType, action, queryFile, dataFiles, graphData,
      resultFile, approval, hashAlgorithm }

/-- `mf:assumedTestBase` — the base IRI the suite documents for its own
fixtures. Read out of the manifest rather than hardcoded, because the
rdf11 corpus MOVED: the suites once documented
`http://www.w3.org/2013/TurtleTests/` and now declare
`https://w3c.github.io/rdf-tests/rdf/rdf11/rdf-turtle/`, with fixtures
regenerated against the new one. The F* runner reads it the same way
(`extract_assumed_test_base`), so both trees resolve relative IRIs
identically. -/
def assumedTestBase (g : Graph) : Option String :=
  match g.find? (fun t => t.p.val == mfNs ++ "assumedTestBase") with
  | some t => match t.o with
              | .iri i => some i.val
              | _      => none
  | none   => none

/-- All entries of a parsed manifest graph, in `mf:entries` order. -/
def extractTestCases (manifestDir : String) (g : Graph) : List TestCase :=
  let fuel := g.length + 1
  let heads := g.filterMap (fun t =>
    if t.p.val == mfNs ++ "entries" then some t.o else none)
  let nodes := match heads.head? with
               | some h => collectList g fuel h
               | none   => []
  nodes.map (extractTestCase manifestDir g)

/-- The whole job as one pure function: manifest text + its path →
(entries, assumed base). Separated from I/O so `#guard` can pin it on
an inline manifest. -/
def parseManifestText (manifestPath text : String) :
    Except String (List TestCase × Option String) :=
  let base := "file://" ++ manifestPath
  match parseTurtle text (some base) with
  | .error e => .error s!"manifest parse error at offset {e.pos}: {e.msg}"
  | .ok g    => .ok (extractTestCases (dirname manifestPath) g, assumedTestBase g)

/-- Load a manifest off disk. `none` when the file is absent
(the caller counts that as `no_manifest`). -/
def loadManifest (path : System.FilePath) :
    IO (Option (Except String (List TestCase × Option String))) := do
  match ← readOpt path with
  | none      => return none
  | some text =>
      let abs ← IO.FS.realPath path
      return some (parseManifestText abs.toString text)

end Harness
