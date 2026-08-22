/-
Harness.OwlProbe — what the Lean OWL 2 RL/RDF closure can and cannot
run against the real W3C OWL 2 test corpus, MEASURED rather than
asserted.

## The finding, up front

**Zero of the 91 OWL 2 RL test cases in `profile-RL.rdf` — and zero of
the 931 across the six catalogs this probe reads — are runnable by the
Lean tree today, and the reason is a missing PARSER, not a missing
rule.** The corpus is RDF/XML from top to bottom: the manifests
are RDF/XML documents, and each test case carries its premise and
conclusion ontologies as ESCAPED RDF/XML inside
`test:rdfXmlPremiseOntology` / `test:rdfXmlConclusionOntology` string
literals. The only other serialisation the manifest offers is OWL
Functional Syntax (`test:fsPremiseOntology`). There is no Turtle, no
N-Triples, no JSON-LD anywhere in the file.

The Lean tree has a Turtle parser, a TriG parser, N-Triples, N-Quads
and a generic XML 1.0 parser. It has NO RDF/XML-to-triples mapping
(that work is in flight on another branch) and no OWL functional-syntax
parser. An XML parse of an RDF/XML document yields elements, not
triples; the RDF/XML mapping rules (RDF 1.1 XML Syntax §7) are exactly
what is absent. So the closure and the clash detector have nothing to
be fed.

## What this probe therefore measures

The census the claim above rests on, computed by READING THE FILE with
the Lean XML parser rather than by assertion:

  * how many `test:TestCase` elements each catalog holds;
  * how many carry an RDF/XML premise, an RDF/XML conclusion, or an OWL
    functional-syntax premise;
  * how many carry a serialisation the Lean tree can currently read
    (that is the runnable count, and it is the number to watch when the
    RDF/XML branch lands);
  * whether the Lean XML parser accepts the catalog at all — the
    catalogs open with a DOCTYPE internal subset declaring four general
    entities (`&rdf;`, `&rdfs;`, `&owl;`, `&test;`), so this doubles as
    a real-corpus exercise of the parser's entity handling. Measured
    2026-08-22: all six catalogs parse.

A test case can be multi-typed (the same `test:TestCase` is often a
ProfileIdentificationTest, a PositiveEntailmentTest and a
ConsistencyTest at once) and the catalogs overlap, so the per-catalog
counts are not disjoint and must not be summed as if they were. The
one number to read is the runnable count against its own catalog's
denominator.

Counts are printed with denominators and failures are named, per the
project's score-reporting rule (anti-pattern #25).

## The comparison numbers

The F* `bin/owl-runner/owl_runner.ml` reads the same catalogs and, per
`docs/test-results/latest.json` (suite ids as written there):

    owl_rl_positive_entailment   30 pass, 0 fail (out of 30)
                                 catalog third_party/testing/owl/profile-RL.rdf
    owl2_profile_ql              87 pass, 0 fail (out of 87)
    owl2_profile_el             119 pass, 1 fail (out of 120)
    owl2_dl_inconsistency       126 pass, 1 fail (out of 127)
    owl_syntax_dl_species       319 pass, 2 fail, 2 skip (out of 323)

Note the F* RL figure is 30 out of 30, not 91: the F* runner selects
the RL-entailment subset of the catalog it can drive. This probe's
denominator is the catalog's whole `test:TestCase` count, so the two
numbers are not the same denominator and must not be compared as if
they were.

NOT part of the verified library: this file does file I/O and prints
scores.
-/

import L4Factoidal.XML.Parser
import L4Factoidal.XML.Document
import L4Factoidal.OWL.RLTheorems

open L4Factoidal.XML
open L4Factoidal.OWL.RL

namespace OwlProbe

/-- Local name of a possibly-prefixed element name (`test:TestCase` →
`TestCase`). The catalogs bind `test:` to one namespace throughout, so
the local name identifies the element without a namespace pass. -/
def localName (s : String) : String :=
  match s.splitOn ":" with
  | [_, l] => l
  | _      => s

/-- Every element of the tree, in document order. -/
partial def elementsOfAux : Node → List (String × List Attribute × List Node)
  | .element tag attrs kids =>
      (tag, attrs, kids) :: (kids.flatMap elementsOfAux)
  | _ => []

/-- Direct element children of a node list, by local name. -/
def childLocalNames (kids : List Node) : List String :=
  kids.filterMap (fun n => match n with
    | .element tag _ _ => some (localName tag)
    | _                => none)

/-- What one test case offers, as a serialisation census. -/
structure CaseInfo where
  /-- `test:identifier` text, or the empty string. -/
  id        : String
  rdfXmlPremise : Bool
  rdfXmlConcl   : Bool
  fsPremise     : Bool
  /-- A serialisation the Lean tree can parse into triples today. -/
  leanReadable : Bool
deriving Repr, Inhabited

/-- Concatenated text content of a node's direct text children. -/
def directText (kids : List Node) : String :=
  String.join (kids.filterMap (fun n => match n with
    | .text t  => some t
    | .cdata t => some t
    | _        => none))

def readCase (attrs : List Attribute) (kids : List Node) : CaseInfo :=
  let _ := attrs
  let names := childLocalNames kids
  let idText :=
    match kids.find? (fun n => match n with
      | .element tag _ _ => localName tag == "identifier"
      | _                => false) with
    | some (.element _ _ k) => directText k
    | _                     => ""
  { id            := idText
    rdfXmlPremise := names.contains "rdfXmlPremiseOntology"
    rdfXmlConcl   := names.contains "rdfXmlConclusionOntology"
    fsPremise     := names.contains "fsPremiseOntology"
    -- The Lean tree parses Turtle / TriG / N-Triples / N-Quads. The
    -- catalogs carry none of those; this stays `false` until the
    -- RDF/XML mapping lands, at which point the condition becomes
    -- `rdfXmlPremise`.
    leanReadable  := names.contains "turtlePremiseOntology" ||
                     names.contains "ntriplesPremiseOntology" }

/-- Census one catalog file. Returns `none` if the Lean XML parser
could not read it — which is itself a measurement, so the caller
reports it rather than hiding it. -/
def censusOne (path : System.FilePath) : IO (Option (List CaseInfo)) := do
  let src ← IO.FS.readFile path
  match parseXML src with
  | .error e =>
      IO.println s!"  XML PARSE FAILED for {path}: {repr e}"
      return none
  | .ok doc =>
      let els := elementsOfAux doc.root
      let cases := els.filterMap (fun (tag, attrs, kids) =>
        if localName tag == "TestCase" then some (readCase attrs kids) else none)
      return some cases

def countTrue (f : CaseInfo → Bool) (cs : List CaseInfo) : Nat :=
  (cs.filter f).length

/-- A self-check that the closure engine this probe would drive is
actually wired up and computing: run it over a two-triple graph and
confirm cax-sco fires and an unrelated triple does not appear. Not a
conformance measurement — it is the "the engine is loaded" line, so a
0-runnable report cannot be confused with a 0-working engine. -/
def engineSelfCheck : (Bool × Bool) :=
  let a : L4Factoidal.RDF.WfIri := ⟨"http://ex/A", by decide⟩
  let b : L4Factoidal.RDF.WfIri := ⟨"http://ex/B", by decide⟩
  let c : L4Factoidal.RDF.WfIri := ⟨"http://ex/C", by decide⟩
  let x : L4Factoidal.RDF.WfIri := ⟨"http://ex/x", by decide⟩
  let g : L4Factoidal.RDF.Graph :=
    [⟨.iri a, rdfsSubClassOf, .iri b⟩, ⟨.iri x, rdfType, .iri a⟩]
  let cl := closure g 3
  (memB cl ⟨.iri x, rdfType, .iri b⟩, memB cl ⟨.iri x, rdfType, .iri c⟩)

def catalogs : List String :=
  ["profile-RL.rdf", "profile-EL.rdf", "profile-QL.rdf",
   "type-positive-entailment.rdf", "type-inconsistency.rdf",
   "type-consistency.rdf"]

def main (args : List String) : IO UInt32 := do
  let dir : System.FilePath :=
    match args with
    | d :: _ => d
    | []     => "../../third_party/testing/owl"
  IO.println "Lean OWL 2 RL/RDF probe — corpus census"
  IO.println s!"corpus dir: {dir}"
  let (scoOk, unrelatedAbsent) := engineSelfCheck
  IO.println s!"engine self-check: cax-sco fires = {scoOk}, \
unrelated triple absent = {!unrelatedAbsent}"
  let mut totalCases := 0
  let mut totalRunnable := 0
  let mut parseFailures : List String := []
  for name in catalogs do
    let p := dir / name
    if !(← p.pathExists) then
      IO.println s!"  MISSING {name}"
      parseFailures := name :: parseFailures
    else
      match ← censusOne p with
      | none => parseFailures := name :: parseFailures
      | some cs =>
        let n := cs.length
        let rx := countTrue (fun c => c.rdfXmlPremise) cs
        let rc := countTrue (fun c => c.rdfXmlConcl) cs
        let fs := countTrue (fun c => c.fsPremise) cs
        let run := countTrue (fun c => c.leanReadable) cs
        totalCases := totalCases + n
        totalRunnable := totalRunnable + run
        IO.println s!"{name}: {n} test cases"
        IO.println s!"    RDF/XML premise: {rx} of {n}"
        IO.println s!"    RDF/XML conclusion: {rc} of {n}"
        IO.println s!"    OWL functional-syntax premise: {fs} of {n}"
        IO.println s!"    readable by the Lean parsers today: {run} of {n}"
  IO.println ""
  IO.println s!"RUNNABLE BY THE LEAN CLOSURE: {totalRunnable} of {totalCases}"
  IO.println "unsupported: every remaining case, for one reason —"
  IO.println "  no RDF/XML-to-triples mapping in the Lean tree"
  IO.println "  (the generic XML 1.0 parser is landed; the RDF/XML"
  IO.println "   syntax mapping of RDF 1.1 XML Syntax section 7 is not)."
  IO.println "F* owl_runner comparison (docs/test-results/latest.json):"
  IO.println "  owl_rl_positive_entailment 30 pass, 0 fail (out of 30)"
  IO.println "  owl2_profile_ql 87 pass, 0 fail (out of 87)"
  IO.println "  owl2_profile_el 119 pass, 1 fail (out of 120)"
  IO.println "  owl2_dl_inconsistency 126 pass, 1 fail (out of 127)"
  IO.println "  (different denominators: the F* runner selects the"
  IO.println "   subset it drives; this census counts every TestCase.)"
  for f in parseFailures.reverse do
    IO.println s!"  catalog not read: {f}"
  return (if parseFailures.isEmpty && scoOk then 0 else 1)

end OwlProbe

def main (args : List String) : IO UInt32 := OwlProbe.main args
