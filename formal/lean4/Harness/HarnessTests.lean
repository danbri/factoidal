/-
Harness.HarnessTests — build-time `#guard`s on the harness's pure
parts.

The harness's I/O cannot be a `#guard`, but everything it depends on
can be, and is: the manifest walk (entry ORDER, type extraction,
approval, action/result path resolution, the bnode-shaped SPARQL
action, an unknown type surviving as an entry), the path arithmetic
ported from the F* runner, and the score-line formatter whose exact
wording the dashboard and every status report depend on.

The manifest fixture below is INLINE and deliberately small — it is a
unit test of the parsing code, not a conformance claim. The
conformance numbers come only from `lake exe l4w3c` over the real
W3C manifests (iron rule #6).

A wrong answer here is a BUILD ERROR: `#guard` evaluates during
elaboration.
-/
import Harness.Run

open Harness

namespace Harness.Tests

/-! ## Path arithmetic (ports of the F* runner's helpers) -/

#guard localName "http://www.w3.org/ns/rdftest#TestTurtleEval" == "TestTurtleEval"
#guard localName "https://w3c.github.io/rdf-canon/tests/vocab#RDFC10EvalTest" == "RDFC10EvalTest"
-- No '#': the whole IRI is the local name (the F* runner's fallback).
#guard localName "http://example/NoHash" == "http://example/NoHash"

#guard dirname "/a/b/manifest.ttl" == "/a/b"
#guard dirname "manifest.ttl" == "."
#guard basename "/a/b/manifest.ttl" == "manifest.ttl"

#guard stripFileScheme "file:///a/b/x.ttl" == "/a/b/x.ttl"
#guard stripFileScheme "/a/b/x.ttl" == "/a/b/x.ttl"

-- A manifest parsed with base `file:///a/b/manifest.ttl` resolves
-- `<x.ttl>` to `file:///a/b/x.ttl`; the scheme strip gives the path.
#guard iriToLocalPath "/a/b" "file:///a/b/x.ttl" == "/a/b/x.ttl"
-- Some other absolute IRI: fall back to manifestDir + basename.
#guard iriToLocalPath "/a/b" "http://example/x.ttl" == "/a/b/x.ttl"
-- A bare relative reference: manifestDir + the reference.
#guard iriToLocalPath "/a/b" "sub/x.ttl" == "/a/b/sub/x.ttl"

-- `relpath_under`: sub-paths are preserved (rdf-xml nests fixtures in
-- subdirectories and needs the sub-path in the base IRI).
#guard relpathUnder "/a/b" "/a/b/x.ttl" == "x.ttl"
#guard relpathUnder "/a/b" "/a/b/sub/x.ttl" == "sub/x.ttl"
#guard relpathUnder "/a/b" "/elsewhere/x.ttl" == "x.ttl"

#guard fixtureBase (some "https://w3c.github.io/rdf-tests/rdf/rdf11/rdf-turtle/")
         "/a/b" "/a/b/IRI_subject.ttl"
       == "https://w3c.github.io/rdf-tests/rdf/rdf11/rdf-turtle/IRI_subject.ttl"
#guard fixtureBase none "/a/b" "/a/b/x.ttl" == "file:///a/b/x.ttl"

#guard trimTrailingNewlines "a\nb\n\n" == "a\nb"
#guard trimTrailingNewlines "a\nb" == "a\nb"

/-! ## The score-line grammar

Anti-pattern #25: every numerator labelled, the denominator always
present. This is the exact string the dashboard and every status
report quote, so it is pinned here. -/

#guard Score.line "rdf-turtle" { pass := 313, fail := 0, skip := 0, unsupported := 0 }
       == "rdf-turtle: 313 pass, 0 fail, 0 skip, 0 unsupported (out of 313)"
#guard Score.line "mixed" { pass := 1, fail := 2, skip := 3, unsupported := 4 }
       == "mixed: 1 pass, 2 fail, 3 skip, 4 unsupported (out of 10)"
-- An empty run still prints its (zero) denominator rather than nothing.
#guard Score.line "empty" {} == "empty: 0 pass, 0 fail, 0 skip, 0 unsupported (out of 0)"
#guard ({ pass := 2, fail := 1, skip := 0, unsupported := 3 } : Score).total == 6
#guard (Score.bump { pass := 1 } (.fail "x")) == { pass := 1, fail := 1 }
#guard (Score.bump {} (.unsupported "TestXMLEval")) == { unsupported := 1 }
#guard (Score.add { pass := 1, fail := 1 } { pass := 2, skip := 5 })
       == { pass := 3, fail := 1, skip := 5 }

#guard Diag.line "rdf-turtle" { noManifest := 0, zeroTests := 0, budgetExceeded := 0 }
       == "HARNESS-DIAG rdf-turtle: no_manifest=0 zero_tests=0 budget_exceeded=0 rows_compared=0 triples_compared=0 gsp_seeded=0"
-- The measurement counters are printed so a SPARQL suite that compared
-- nothing cannot read as green.
#guard Diag.line "bind" { rowsCompared := 42, triplesCompared := 7 }
       == "HARNESS-DIAG bind: no_manifest=0 zero_tests=0 budget_exceeded=0 rows_compared=42 triples_compared=7 gsp_seeded=0"
#guard (Diag.add { rowsCompared := 1, budgetExceeded := 1 } { rowsCompared := 2, triplesCompared := 3 })
       == { budgetExceeded := 1, rowsCompared := 3, triplesCompared := 3 }

#guard Outcome.line "t1" .pass == "PASS t1"
#guard Outcome.line "t1" (.fail "boom") == "FAIL t1: boom"
#guard Outcome.line "t1" (.skip "no file") == "SKIP t1: no file"
#guard Outcome.line "t1" (.unsupported "TestXMLEval") == "UNSUPPORTED t1: TestXMLEval"
#guard (Outcome.fail "x").isFail
#guard !(Outcome.unsupported "x").isFail

#guard suiteLabel "/w3c/rdf/rdf11/rdf-turtle/manifest.ttl" == "rdf-turtle"
-- The rdf-canon manifest lives in a directory literally called
-- `tests`, which names nothing; use the grandparent instead.
#guard suiteLabel "/third_party/testing/rdf-canon/tests/manifest.ttl" == "rdf-canon"

/-! ## Manifest parsing

A miniature manifest in the exact shape the real ones use: an
`mf:entries` RDF collection, entries typed in the `rdft:` namespace,
`mf:action` as both a plain file IRI and a `qt:`-bearing blank node,
`rdft:approval` in all three states, and one entry with a type the
runner cannot execute. -/

def miniManifest : String :=
"@prefix rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#> .
@prefix mf: <http://www.w3.org/2001/sw/DataAccess/tests/test-manifest#> .
@prefix qt: <http://www.w3.org/2001/sw/DataAccess/tests/test-query#> .
@prefix rdft: <http://www.w3.org/ns/rdftest#> .

<> rdf:type mf:Manifest ;
   mf:assumedTestBase <https://example.org/base/> ;
   mf:entries ( <#alpha> <#beta> <#gamma> <#delta> ) .

<#alpha> rdf:type rdft:TestTurtleEval ;
   mf:name \"alpha\" ;
   rdft:approval rdft:Approved ;
   mf:action <alpha.ttl> ;
   mf:result <alpha.nt> .

<#beta> rdf:type rdft:TestTurtleNegativeSyntax ;
   mf:name \"beta\" ;
   rdft:approval rdft:Proposed ;
   mf:action <sub/beta-bad-01.ttl> .

<#gamma> rdf:type mf:QueryEvaluationTest ;
   mf:name \"gamma\" ;
   rdft:approval rdft:Rejected ;
   mf:action [ qt:query <gamma.rq> ; qt:data <gamma.ttl> ] ;
   mf:result <gamma.srx> .

<#delta> rdf:type rdft:TestXMLEval ;
   mf:name \"delta\" ;
   mf:action <delta.rdf> ;
   mf:result <delta.nt> .
"

/-- Parsed against a manifest at `/m/manifest.ttl`, so relative
references resolve to `file:///m/…`. -/
def miniCases : List TestCase × Option String :=
  match parseManifestText "/m/manifest.ttl" miniManifest with
  | .ok r    => r
  | .error _ => ([], none)

def miniNames : List String := miniCases.1.map (·.name)
def miniTypes : List String := miniCases.1.map (·.testType)

-- The collection walk keeps the manifest's own ORDER, and no entry is
-- dropped — including the one whose type this tree cannot execute.
#guard miniNames == ["alpha", "beta", "gamma", "delta"]
#guard miniTypes == ["TestTurtleEval", "TestTurtleNegativeSyntax",
                     "QueryEvaluationTest", "TestXMLEval"]
#guard miniCases.1.length == 4

-- `mf:assumedTestBase` is read out of the manifest, not hardcoded.
#guard miniCases.2 == some "https://example.org/base/"

-- Approval is RECORDED in all three states and never filtered on:
-- a Rejected entry is still an entry.
#guard miniCases.1.map (·.approval) == ["Approved", "Proposed", "Rejected", ""]

/-- Look one entry up by name. -/
def caseNamed (n : String) : Option TestCase := miniCases.1.find? (fun tc => tc.name == n)

-- A file-IRI `mf:action` resolves relative to the manifest directory,
-- and so does `mf:result`.
#guard (caseNamed "alpha").bind (·.action) == some "/m/alpha.ttl"
#guard (caseNamed "alpha").bind (·.resultFile) == some "/m/alpha.nt"
-- Sub-directory references keep their sub-path.
#guard (caseNamed "beta").bind (·.action) == some "/m/sub/beta-bad-01.ttl"
-- and the base IRI a fixture parses against combines the two.
#guard fixtureBase miniCases.2 "/m" "/m/sub/beta-bad-01.ttl"
       == "https://example.org/base/sub/beta-bad-01.ttl"

-- A `qt:`-bearing blank-node action: no plain `action` file, but the
-- query and data files ARE captured for the SPARQL rungs to consume.
#guard (caseNamed "gamma").bind (·.action) == none
#guard (caseNamed "gamma").bind (·.queryFile) == some "/m/gamma.rq"
#guard (caseNamed "gamma").map (·.dataFiles) == some ["/m/gamma.ttl"]
#guard (caseNamed "gamma").bind (·.resultFile) == some "/m/gamma.srx"

-- An entry with no `rdft:approval` triple records the empty string
-- rather than vanishing.
#guard (caseNamed "delta").map (·.approval) == some ""

/-! ## Lenient manifest recovery (issue 602)

The rdf12 rdf-semantics manifest's shape: one entry uses an undeclared
`test:` prefix. The strict parse refuses the whole file; the lenient
parse recovers it with EXACTLY ONE warning, and the recovered entry
keeps its `rdft:approval`-free record (the `test:approval` statement
lands in the recovery namespace, which nothing reads). -/

def undeclaredPrefixManifest : String :=
"@prefix rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#> .
@prefix mf: <http://www.w3.org/2001/sw/DataAccess/tests/test-manifest#> .

<> rdf:type mf:Manifest ;
   mf:entries ( <#t1> ) .

<#t1> rdf:type mf:PositiveEntailmentTest ;
   mf:name \"t1\" ;
   mf:action <t1.ttl> ;
   mf:result false ;
   test:approval test:NotClassified .
"

#guard (match parseManifestText "/m/manifest.ttl" undeclaredPrefixManifest with
        | .error _ => true
        | .ok _    => false)
#guard (match parseManifestTextLenient "/m/manifest.ttl" undeclaredPrefixManifest with
        | (.ok (tcs, _), ws) =>
            tcs.length == 1 && ws.length == 1 &&
            (tcs.head?.map (·.name) == some "t1") &&
            (tcs.head?.map (·.resultFalse) == some true) &&
            (tcs.head?.map (·.approval) == some "")
        | _ => false)

/-! ## The sparql11 manifest shapes

An umbrella manifest (`mf:include`, no entries), an entailment-regime
action (`sd:entailmentRegime` as one IRI and as a collection) and a
SERVICE action (`qt:serviceData`). -/

def umbrellaManifest : String :=
"@prefix mf: <http://www.w3.org/2001/sw/DataAccess/tests/test-manifest#> .
<> a mf:Manifest ;
   mf:include ( <aggregates/manifest.ttl> <bind/manifest.ttl> ) ."

#guard parseManifestIncludes "/s/manifest-all.ttl" umbrellaManifest
       == ["/s/aggregates/manifest.ttl", "/s/bind/manifest.ttl"]
-- …and it has no entries of its own.
#guard (match parseManifestText "/s/manifest-all.ttl" umbrellaManifest with
        | .ok (tests, _) => tests.length
        | .error _       => 99) == 0

def sparqlManifest : String :=
"@prefix rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#> .
@prefix mf: <http://www.w3.org/2001/sw/DataAccess/tests/test-manifest#> .
@prefix qt: <http://www.w3.org/2001/sw/DataAccess/tests/test-query#> .
@prefix sd: <http://www.w3.org/ns/sparql-service-description#> .
@prefix ent: <http://www.w3.org/ns/entailment/> .

<> rdf:type mf:Manifest ;
   mf:entries ( <#one> <#two> <#svc> ) .

<#one> rdf:type mf:QueryEvaluationTest ;
   mf:name \"one\" ;
   mf:action [ qt:query <one.rq> ; qt:data <one.ttl> ;
               sd:entailmentRegime ( ent:RDFS ent:D ) ] ;
   mf:result <one.srx> .

<#two> rdf:type mf:QueryEvaluationTest ;
   mf:name \"two\" ;
   mf:action [ qt:query <two.rq> ; qt:data <two.ttl> ;
               qt:graphData <g1.ttl> ;
               sd:entailmentRegime ent:OWL-Direct ] ;
   mf:result <two.srx> .

<#svc> rdf:type mf:QueryEvaluationTest ;
   mf:name \"svc\" ;
   mf:action [ qt:query <svc.rq> ;
               qt:serviceData [ qt:endpoint <http://example.org/sparql> ;
                                qt:data <svc-endpoint.ttl> ] ] ;
   mf:result <svc.srx> ."

def sparqlCases : List TestCase :=
  match parseManifestText "/s/manifest.ttl" sparqlManifest with
  | .ok (tests, _) => tests
  | .error _       => []

def sparqlCase (n : String) : Option TestCase := sparqlCases.find? (fun tc => tc.name == n)

#guard sparqlCases.length == 3
#guard (sparqlCase "one").map (·.entailmentRegimes) == some ["RDFS", "D"]
#guard (sparqlCase "two").map (·.entailmentRegimes) == some ["OWL-Direct"]
#guard (sparqlCase "two").map (·.graphData) == some [("file:///s/g1.ttl", "/s/g1.ttl")]
#guard (sparqlCase "svc").map (·.entailmentRegimes) == some []
#guard (sparqlCase "svc").map (·.serviceData)
       == some [("http://example.org/sparql", "/s/svc-endpoint.ttl")]
#guard (sparqlCase "svc").map (·.dataFiles) == some []

/-! ## Result comparison (`Harness/Compare.lean`)

The rules of `run_query_eval_test`, pinned on tiny inputs. -/

section compare
open L4Factoidal.RDF
open L4Factoidal.SPARQL

def exA : Term := .iri ⟨"http://example.org/a", rfl⟩
def exB : Term := .iri ⟨"http://example.org/b", rfl⟩
def lit1 : Term := .literal (Literal.string "1")
def litInt1 : Term :=
  .literal ⟨{ lexicalForm := "1", datatype := xsdInteger, langTag := none, direction := none }, rfl⟩
def bn (l : String) : Term := .bnode l

-- Plain rows: a multiset, order-insensitive.
#guard compareSelectRows false false [[("x", exA)], [("x", exB)]] [[("x", exB)], [("x", exA)]] == .equal
-- A missing row, an extra row, a different value: not equal.
#guard compareSelectRows false false [[("x", exA)]] [[("x", exA)], [("x", exB)]] == .notEqual
#guard compareSelectRows false false [[("x", exA)], [("x", exB)]] [[("x", exA)]] == .notEqual
#guard compareSelectRows false false [[("x", exA)]] [[("x", exB)]] == .notEqual
-- Domains must agree: an unbound variable is not a wildcard.
#guard compareSelectRows false false [[("x", exA)]] [[("x", exA), ("y", exB)]] == .notEqual
-- Strict term equality: "1" (xsd:string) is not "1"^^xsd:integer.
#guard compareSelectRows false false [[("x", lit1)]] [[("x", litInt1)]] == .notEqual
-- …but the CSV-lenient comparison accepts it (CSV lost the datatype).
#guard compareSelectRows false true [[("x", lit1)]] [[("x", litInt1)]] == .equal

-- Blank nodes: ONE bijection across all rows. `_:a` in two expected
-- rows must map to the SAME actual label.
#guard compareSelectRows false false [[("x", bn "a")], [("x", bn "a")]]
                                     [[("x", bn "p")], [("x", bn "p")]] == .equal
#guard compareSelectRows false false [[("x", bn "a")], [("x", bn "a")]]
                                     [[("x", bn "p")], [("x", bn "q")]] == .notEqual
-- …and two distinct expected labels may not share one actual label.
#guard compareSelectRows false false [[("x", bn "a")], [("x", bn "b")]]
                                     [[("x", bn "p")], [("x", bn "p")]] == .notEqual
-- Unordered: rows may be permuted while the bijection holds.
#guard compareSelectRows false false [[("x", bn "a"), ("y", exA)], [("x", bn "b"), ("y", exB)]]
                                     [[("x", bn "q"), ("y", exB)], [("x", bn "p"), ("y", exA)]] == .equal
-- ORDER BY pins the bijection to row position: the same rows
-- permuted are now a mismatch.
#guard compareSelectRows true false [[("x", bn "a"), ("y", exA)], [("x", bn "b"), ("y", exB)]]
                                    [[("x", bn "q"), ("y", exB)], [("x", bn "p"), ("y", exA)]] == .notEqual
#guard compareSelectRows true false [[("x", bn "a"), ("y", exA)], [("x", bn "b"), ("y", exB)]]
                                    [[("x", bn "p"), ("y", exA)], [("x", bn "q"), ("y", exB)]] == .equal
-- CSV: blank nodes collapse, no bijection is demanded.
#guard compareSelectRows false true [[("x", bn "a")], [("x", bn "a")]]
                                    [[("x", bn "p")], [("x", bn "q")]] == .equal
-- An exhausted search is reported, never passed.
#guard (matchBack termMatchStrict 1 1 [] [[("x", bn "a")]] [[("x", bn "p")]]).1
       matches .exceeded

/-- An `rs:ResultSet` in the DAWG vocabulary, with `rs:index`. -/
def rsTurtle : String :=
"@prefix rs: <http://www.w3.org/2001/sw/DataAccess/tests/result-set#> .
[] a rs:ResultSet ;
   rs:resultVariable \"x\" ;
   rs:solution [ rs:index 2 ; rs:binding [ rs:variable \"x\" ; rs:value <http://example.org/b> ] ] ;
   rs:solution [ rs:index 1 ; rs:binding [ rs:variable \"x\" ; rs:value <http://example.org/a> ] ] ."

def rsDecoded : Option (List VarName × List Binding) :=
  match L4Factoidal.Syntax.parseTurtle rsTurtle (some "file:///r/x.ttl") with
  | .ok g    => decodeRsResultSet g
  | .error _ => none

#guard rsDecoded.map Prod.fst == some ["x"]
-- Rows come back in `rs:index` order.
#guard rsDecoded.map Prod.snd == some [[("x", exA)], [("x", exB)]]
#guard (match L4Factoidal.Syntax.parseTurtle rsTurtle (some "file:///r/x.ttl") with
        | .ok g => isRsResultSet g | .error _ => false)
-- A plain graph is not a result set.
#guard (match L4Factoidal.Syntax.parseTurtle "<http://example.org/a> <http://example.org/p> 1 ." none with
        | .ok g => isRsResultSet g | .error _ => true) == false

end compare

/-! ## rdf-canon helpers -/

#guard quotedTokens "{\"e0\": \"c14n0\", \"e1\": \"c14n1\"}" == ["e0", "c14n0", "e1", "c14n1"]
#guard pairUp ["e0", "c14n0", "e1", "c14n1"] == [("e0", "c14n0"), ("e1", "c14n1")]

-- SHA-384 is selected only by the literal the manifest uses.
#guard hashAlgOf { name := "x", entryId := "x", testType := "RDFC10EvalTest",
                   action := none, queryFile := none, dataFiles := [], graphData := [],
                   resultFile := none, approval := "", hashAlgorithm := some "SHA384" }
       == .sha384
#guard hashAlgOf { name := "x", entryId := "x", testType := "RDFC10EvalTest",
                   action := none, queryFile := none, dataFiles := [], graphData := [],
                   resultFile := none, approval := "", hashAlgorithm := none }
       == .sha256

/-! ## A give-up is not a pass

The rule this harness must never break: an isomorphism search that
runs out of budget is a FAILURE with its own name, and it raises the
`HARNESS-DIAG` counter. -/

#guard (isoResult "x" .equal).outcome == .pass
#guard (isoResult "x" .notEqual).outcome == .fail "x"
#guard (isoResult "x" .budgetExceeded).outcome == .fail "isomorphism budget exceeded (x)"
#guard (isoResult "x" .budgetExceeded).budgetExceeded
#guard !(isoResult "x" .notEqual).budgetExceeded

/-! ## The sparql11 UPDATE manifest shape

`ut:request` / `ut:data` / `ut:graphData` on the action, and the
expected Graph Store as `ut:data` / `ut:graphData` under `mf:result`
— a `ut:graphData` node carries `ut:graph` (file) + `rdfs:label`
(graph IRI). An `mf:result []` (update-silent) is an expected EMPTY
store: no result file, no data. -/

def updateManifest : String :=
"@prefix rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#> .
@prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .
@prefix mf: <http://www.w3.org/2001/sw/DataAccess/tests/test-manifest#> .
@prefix ut: <http://www.w3.org/2009/sparql/tests/test-update#> .

<> rdf:type mf:Manifest ;
   mf:entries ( <#u1> <#u2> <#u3> ) .

<#u1> rdf:type mf:UpdateEvaluationTest ;
   mf:name \"u1\" ;
   mf:action [ ut:request <u1.ru> ;
               ut:data <in.ttl> ;
               ut:graphData [ ut:graph <in-g1.ttl> ; rdfs:label \"http://example.org/g1\" ] ] ;
   mf:result [ ut:result ut:success ;
               ut:data <out.ttl> ;
               ut:graphData [ ut:graph <out-g1.ttl> ; rdfs:label \"http://example.org/g1\" ] ] .

<#u2> rdf:type mf:UpdateEvaluationTest ;
   mf:name \"u2\" ;
   mf:action [ ut:request <u2.ru> ] ;
   mf:result [] .

<#u3> rdf:type mf:PositiveUpdateSyntaxTest11 ;
   mf:name \"u3\" ;
   mf:action <u3.ru> .
"

def updateCases : List TestCase :=
  match parseManifestText "/u/manifest.ttl" updateManifest with
  | .ok r    => r.1
  | .error _ => []

def updateCase (n : String) : Option TestCase := updateCases.find? (fun tc => tc.name == n)

#guard updateCases.map (·.testType)
       == ["UpdateEvaluationTest", "UpdateEvaluationTest", "PositiveUpdateSyntaxTest11"]
#guard (updateCase "u1").bind (·.queryFile) == some "/u/u1.ru"
#guard (updateCase "u1").map (·.dataFiles) == some ["/u/in.ttl"]
#guard (updateCase "u1").map (·.graphData) == some [("http://example.org/g1", "/u/in-g1.ttl")]
-- The result is a blank node, so there is NO result file …
#guard (updateCase "u1").bind (·.resultFile) == none
-- … and the expected store is captured from it.
#guard (updateCase "u1").map (·.updateResultData) == some ["/u/out.ttl"]
#guard (updateCase "u1").map (·.updateResultGraphData)
       == some [("http://example.org/g1", "/u/out-g1.ttl")]
-- `mf:result []`: an expected empty store.
#guard (updateCase "u2").bind (·.resultFile) == none
#guard (updateCase "u2").map (·.updateResultData) == some []
#guard (updateCase "u2").map (·.updateResultGraphData) == some []
-- A syntax test's action is the request file itself.
#guard (updateCase "u3").bind (·.action) == some "/u/u3.ru"

/-! ## Regime names -/

#guard pickRegime ["RDFS"] == some .rdfs

/-! ## Axiom audit

Printed into every build log. The acceptable base is exactly Lean's
own foundations — `propext`, `Classical.choice`, `Quot.sound` — and
these definitions should reach even fewer. No `sorry`, no user
`axiom`, no `Lean.ofReduceBool` (which is what `native_decide` would
smuggle in). -/

#print axioms parseManifestText
#print axioms parseManifestTextLenient
#print axioms extractTestCases
#print axioms collectList
#print axioms Score.line
#print axioms iriToLocalPath
#print axioms fixtureBase

end Harness.Tests
