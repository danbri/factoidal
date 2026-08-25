/-
Harness/GrddlRun — a GRDDL conformance runner over the vendored W3C
GRDDL test suite.

It parses `third_party/testing/grddl/grddl-tests-normative.rdf` with
this project's own RDF/XML parser, walks each test's input document
with `GRDDL.Discovery`, runs the discovered stylesheets through the
Lean XSLT engine, reads each result back as RDF/XML, and compares the
merged graph with the expected one BY ISOMORPHISM — blank-node labels
are not part of what a GRDDL result means.

## No network, and that is visible in the score

The suite's documents live under two URL trees which
`third_party/testing/grddl/docroot/` mirrors. `iriToLocal` maps an
absolute suite IRI to a file there. Anything not mirrored is
UNAVAILABLE, and a test that needs it is counted apart with the IRI
named — never as a pass, and never as a failure of the engine.

## Five outcomes

  * **pass** — the merged graph is isomorphic to the expected one;
  * **fail** — it is not. This is the number that means something is
    broken;
  * **no-transformation** — the source names no transformation this
    stage can follow and is not itself RDF/XML, so there is nothing
    to glean. Reported with the case name, because the reason is
    usually a second document that is not mirrored;
  * **unavailable** — a document the test needs is not in the
    vendored docroot;
  * **refused** — a stylesheet the engine declined to run, or output
    that is not well-formed RDF/XML.

Usage: `lake exe l4grddl [tests-dir]`
-/
import L4Factoidal.GRDDL.Discovery
import L4Factoidal.Syntax.NTriples

open L4Factoidal.RDF
open L4Factoidal.XML
open L4Factoidal.GRDDL
open L4Factoidal.Syntax

/-! ## Mapping a suite IRI to a vendored file -/

def tdPrefix : String := "http://www.w3.org/2001/sw/grddl-wg/td/"
def gPrefixHttp : String := "http://www.w3.org/2003/g/"
def gPrefixHttps : String := "https://www.w3.org/2003/g/"

def stripFragment (iri : String) : String :=
  match iri.toList.findIdx? (· == '#') with
  | some i => String.ofList (iri.toList.take i)
  | none   => iri

/-- The two host trees the suite references, and nothing else. An IRI
    outside them has no local file, which the caller reports as
    UNAVAILABLE with the IRI named. -/
def iriToLocal (docroot : String) (iri0 : String) : Option String :=
  let iri := stripFragment iri0
  let after (p : String) : String := String.ofList (iri.toList.drop p.length)
  if iri.startsWith tdPrefix then some (docroot ++ "/td/" ++ after tdPrefix)
  else if iri.startsWith gPrefixHttp then some (docroot ++ "/g/" ++ after gPrefixHttp)
  else if iri.startsWith gPrefixHttps then some (docroot ++ "/g/" ++ after gPrefixHttps)
  else none

def readIri (docroot iri : String) : IO (Option String) := do
  match iriToLocal docroot iri with
  | none      => return none
  | some path =>
      if ← System.FilePath.pathExists path then
        return some (← IO.FS.readFile path)
      else return none

/-! ## The manifest -/

def tsNS : String := "http://www.w3.org/2000/10/rdf-tests/rdfcore/testSchema#"
def rdfTypeIri : String := "http://www.w3.org/1999/02/22-rdf-syntax-ns#type"

structure GTest where
  subject : String
  input   : Option String := none
  output  : Option String := none
  types   : List String := []
deriving Repr, Inhabited

def subjIri : Subject → Option String
  | .iri i   => some i.val
  | .bnode _ => none

def objIri : Term → Option String
  | .iri i => some i.val
  | _      => none

/-- Every `rdfcore:Test` in the manifest, with its input and output
    documents. -/
def testsOf (g : Graph) : List GTest :=
  let subjects := (g.filterMap (fun t =>
    if t.p.val == rdfTypeIri then subjIri t.s else none)).eraseDups
  subjects.filterMap (fun s =>
    let mine := g.filter (fun t => subjIri t.s == some s)
    let get (p : String) : Option String :=
      (mine.find? (fun t => t.p.val == tsNS ++ p)).bind (fun t => objIri t.o)
    let types := mine.filterMap (fun t =>
      if t.p.val == rdfTypeIri then objIri t.o else none)
    if types.contains (tsNS ++ "Test") then
      some { subject := s, input := get "inputDocument",
             output := get "outputDocument", types := types }
    else none)

/-! ## Outcomes -/

/-- Replace every `https://` with `http://`, and every blank-node
    label with one placeholder, in an N-Triples serialisation.

    This is a DIAGNOSIS, never a verdict. Several of the vendored
    inputs were re-fetched from a W3C server that had upgraded its
    own links to `https`, while the expected-output files beside them
    still say `http` — so a transform can be exactly right and still
    produce a different IRI. Saying so on the FAIL line is what tells
    a reader the residue is corpus drift rather than an engine
    defect; the case still counts as a failure, because the two
    graphs really are different graphs. -/
def schemeBlind (s : String) : String :=
  let noScheme := String.intercalate "http://" (s.splitOn "https://")
  let lines := (noScheme.splitOn "\n").map (fun l =>
    -- Collapse every `_:label` to `_:b`.
    match l.splitOn "_:" with
    | []           => l
    | head :: segs =>
        head ++ String.intercalate "" (segs.map (fun seg =>
          "_:b" ++ String.ofList (seg.toList.dropWhile (fun c =>
            c.isAlphanum || c == '-' || c == '_')))))
  String.intercalate "\n" ((lines.filter (· != "")).toArray.qsort (· < ·) |>.toList)

inductive Verdict where
  | pass
  | fail (why : String)
  | noTransformation
  | unavailable (iri : String)
  | refused (why : String)
deriving Repr, Inhabited

structure Tally where
  pass    : Nat := 0
  fail    : Nat := 0
  /-- How many of the failures differ only by the http/https scheme.
      A SUB-COUNT of `fail`, never a separate bucket: the graphs
      really are different graphs. -/
  drift   : Nat := 0
  noTx    : Nat := 0
  unavail : Nat := 0
  refused : Nat := 0
deriving Inhabited

/-- Fetch and parse a second document — a namespace document (§3) or a
    profile document (§5). The FETCH is the runner's job; every
    discovery decision over the parsed tree belongs to
    `GRDDL.Discovery`. -/
def secondDoc (docroot iri : String) : IO (Option Node) := do
  match ← readIri docroot iri with
  | none     => return none
  | some src => return (match parseXML src with
      | .ok d    => some d.root
      | .error _ => none)

/-- Load a stylesheet's `xsl:import` / `xsl:include` targets, and
    theirs, to a bounded depth. Returns the pairs keyed by the href AS
    WRITTEN — that is what the reader looks up — and the hrefs that
    are not in the vendored docroot. -/
partial def loadImports (docroot : String) (styleIri : String) (root : Node)
    (fuel : Nat) : IO (List (String × Node) × List String) := do
  if fuel == 0 then return ([], [])
  let mut acc : List (String × Node) := []
  let mut miss : List String := []
  for (_, href) in L4Factoidal.XSLT.importHrefs root do
    let target := resolveIri styleIri href
    match ← readIri docroot target with
    | none => miss := miss ++ [target]
    | some src => match parseXML src with
      | .error _ => miss := miss ++ [target]
      | .ok d =>
          acc := acc ++ [(href, d.root)]
          let (deeper, m2) ← loadImports docroot target d.root (fuel - 1)
          acc := acc ++ deeper
          miss := miss ++ m2
  return (acc, miss)

def runTest (docroot : String) (t : GTest) : IO Verdict := do
  match t.input, t.output with
  | none, _ | _, none => return .fail "the manifest entry names no input or output document"
  | some inIri, some outIri =>
    match ← readIri docroot inIri with
    | none => return .unavailable inIri
    | some inputText =>
      match parseXML inputText with
      | .error e => return .refused s!"the input document is not well-formed XML: {e.message}"
      | .ok source =>
        let base := inIri
        let root := source.root
        -- §2 + §4, from the document itself.
        let sameDoc := sameDocumentTransformations base root
        -- §5: dereference each custom head @profile document.
        let mut profileTx : List String := []
        for p in customProfileUris base root do
          match ← secondDoc docroot p with
          | some tree => profileTx := profileTx ++ profileDocTransformations p tree
          | none      => pure ()
        -- §3: dereference the root element's namespace document.
        let mut nsTx : List String := []
        match rootNamespaceUri root with
        | some nsu =>
            match ← secondDoc docroot nsu with
            | some tree => nsTx := namespaceDocTransformations nsu tree
            | none      => pure ()
        | none => pure ()
        let xforms := (sameDoc ++ profileTx ++ nsTx).eraseDups
        let isRdfXml := isRdfXmlRoot root
        if xforms.isEmpty && !isRdfXml then
          return .noTransformation
        else
          let mut styles : List (Document × List (String × Node)) := []
          let mut missing : List String := []
          for x in xforms do
            match ← readIri docroot x with
            | none => missing := missing ++ [x]
            | some src => match parseXML src with
              | .ok d    =>
                  -- `xsl:import` / `xsl:include` targets, loaded
                  -- transitively. `importHrefs` says WHICH hrefs the
                  -- stylesheet wants; fetching them is the runner's
                  -- job and the meaning of the merge is not.
                  let (imps, miss) ← loadImports docroot x d.root 4
                  missing := missing ++ miss
                  styles := styles ++ [(d, imps)]
              | .error _ => missing := missing ++ [x]
          if !missing.isEmpty then
            return .unavailable (String.intercalate ", " missing)
          else
            match ← readIri docroot outIri with
            | none => return .unavailable outIri
            | some expectedText =>
              -- The GRDDL result describes the SOURCE document (a
              -- transform's `rdf:about=""` denotes it), so the
              -- expected graph is parsed against the source's
              -- EFFECTIVE base — the one a root `xml:base` or an
              -- XHTML `<base href>` may have moved — and never
              -- against the output file's own URL.
              match L4Factoidal.Syntax.RdfXml.parseRdfXml expectedText
                      (some (docBase base root)) with
              | .error e => return .refused s!"the expected output is not RDF/XML: {e.msg}"
              | .ok expected =>
                match grddlResult base source inputText styles with
                | .error why => return .refused why
                | .ok result =>
                    if Graph.isomorphic? result expected then return .pass
                    else
                      -- A count alone does not say what differs.
                      -- `GRDDL_DEBUG=<case>` prints both graphs, so a
                      -- one-versus-one mismatch (a base-URI question)
                      -- is told apart from a missing rule.
                      let want := (← IO.getEnv "GRDDL_DEBUG").getD ""
                      if want != "" && inIri.endsWith want then
                        IO.println "--- produced ---"
                        IO.println ((Graph.toNTriples result).toOption.getD "(unserialisable)")
                        IO.println "--- expected ---"
                        IO.println ((Graph.toNTriples expected).toOption.getD "(unserialisable)")
                      let rt := (Graph.toNTriples result).toOption.getD ""
                      let et := (Graph.toNTriples expected).toOption.getD ""
                      let drift := rt != "" && schemeBlind rt == schemeBlind et
                      return Verdict.fail
                        (s!"produced {result.length} triple(s), expected {expected.length}"
                         ++ (if drift then
                               " — the two differ ONLY by the http/https scheme, which is"
                               ++ " vendoring drift in the corpus, not a transform defect"
                             else ""))

def main (args : List String) : IO UInt32 := do
  let dir := args.head? |>.getD "third_party/testing/grddl"
  let manifestPath := dir ++ "/grddl-tests-normative.rdf"
  let docroot := dir ++ "/docroot"
  if !(← System.FilePath.pathExists manifestPath) then
    IO.println s!"grddl runner: manifest not found: {manifestPath}"
    IO.println "run tools/ensure-test-env.sh from the repository root first"
    return 1
  let mtext ← IO.FS.readFile manifestPath
  match L4Factoidal.Syntax.RdfXml.parseRdfXml mtext
          (some "http://www.w3.org/2001/sw/grddl-wg/td/grddl-tests-normative.rdf") with
  | .error e =>
      IO.println s!"grddl runner: the manifest did not parse as RDF/XML: {e.msg}"
      return 1
  | .ok mg =>
    let tests := testsOf mg
    let mut t : Tally := {}
    for gt in tests do
      let name := stripFragment gt.subject ++ "#" ++
        (String.ofList (gt.subject.toList.drop (stripFragment gt.subject).length)).drop 1
      let short := match (gt.subject.splitOn "#").getLast? with
        | some s => s
        | none   => gt.subject
      let _ := name
      match ← runTest docroot gt with
      | .pass => t := { t with pass := t.pass + 1 }
      | .fail why =>
          t := { t with fail := t.fail + 1,
                        drift := t.drift + (if (why.splitOn "http/https").length > 1
                                            then 1 else 0) }
          IO.println s!"FAIL {short}: {why}"
      | .noTransformation =>
          t := { t with noTx := t.noTx + 1 }
          IO.println s!"NO-TRANSFORMATION {short}"
      | .unavailable iri =>
          t := { t with unavail := t.unavail + 1 }
          IO.println s!"UNAVAILABLE {short}: not in the vendored docroot: {iri}"
      | .refused why =>
          t := { t with refused := t.refused + 1 }
          IO.println s!"REFUSED {short}: {why}"
    let decided := t.pass + t.fail
    IO.println ""
    IO.println s!"grddl DECIDED: {t.pass} pass, {t.fail} fail (out of {decided} decided)"
    IO.println s!"  of those failures, {t.drift} differ ONLY by the http/https scheme"
    IO.println "  (vendoring drift: several inputs were re-fetched from a W3C server"
    IO.println "   that had upgraded its own links, while the expected files beside"
    IO.println "   them still say http. Counted as failures, because the graphs"
    IO.println "   really are different graphs.)"
    IO.println s!"NO TRANSFORMATION FOUND: {t.noTx} cases name no transformation this stage can follow"
    IO.println s!"UNAVAILABLE: {t.unavail} cases need a document the vendored docroot does not carry"
    IO.println s!"REFUSED: {t.refused} cases the engine declined"
    IO.println s!"  (out of {tests.length} tests in the manifest)"
    IO.println ""
    IO.println "Comparison is by graph ISOMORPHISM: blank-node labels are not"
    IO.println "part of what a GRDDL result means. A case whose documents are"
    IO.println "not mirrored locally is counted apart with the IRI named — this"
    IO.println "runner makes no network request."
    return (if t.fail > 0 then 1 else 0)
