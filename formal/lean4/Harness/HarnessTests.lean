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
       == "HARNESS-DIAG rdf-turtle: no_manifest=0 zero_tests=0 budget_exceeded=0"

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

end Harness.Tests
