/-
Harness/XmlConfRun — the W3C XML Conformance Test Suite, run end to
end against the Lean XML parser.

`XML/ConfProbe.lean` reads a list of paths from standard input and
prints a verdict per file. That is a probe: it has no expected answer
to compare against, so it cannot say whether a verdict is RIGHT. This
runner reads the suite's OWN sub-manifests — the `<TEST>` elements with
their `TYPE` and `URI` — and scores each verdict against what the
suite says it should be.

The sub-manifests are XML, and they are parsed by the same verified
parser the tests exercise. That is deliberate: a separate manifest
reader would be a second implementation of the syntax under test.

## The parser's PROFILE decides what can be scored

`Parser.lean` implements XML 1.0, NON-VALIDATING, NON-NAMESPACE, and
reads UTF-8 only. A test outside that profile is not a failure; it is
not a test of this parser. Each is counted in its own bucket and
named:

  * `not-wf`  — the document must be REJECTED. Scored.
  * `valid` / `invalid` — both must be ACCEPTED by a NON-VALIDATING
    parser: `invalid` means "violates the DTD", which a non-validating
    parser is not asked to notice. Scored.
  * `error`   — the specification leaves the behaviour optional, so a
    verdict either way is conformant. NOT scored, and reported.
  * `VERSION="1.1"` — XML 1.1 is a different language. Out of profile.
  * non-UTF-8 bytes — the parser does not transcode. Out of profile.

Reporting these as failures would understate the parser; folding them
into passes would overstate it. Both numbers are printed.

Usage: `lake exe l4xmlconf [xmlconf-dir]`
-/
import L4Factoidal.XML.Parser

open L4Factoidal.XML

/-- Every `<TEST>` element anywhere in a manifest tree. -/
partial def testElements : Node → List Node
  | n@(.element tag _ cs) =>
      (if tag == "TEST" then [n] else []) ++ cs.flatMap testElements
  | _ => []

def attr? (name : String) : Node → Option String
  | .element _ attrs _ => (attrs.find? (fun a => a.name == name)).map (·.value)
  | _ => none

/-- The directory part of a path, with its trailing slash. -/
def dirOf (p : String) : String :=
  match (p.splitOn "/").reverse with
  | _ :: rest => if rest.isEmpty then "" else String.intercalate "/" rest.reverse ++ "/"
  | []        => ""

structure Counts where
  scored      : Nat := 0
  pass        : Nat := 0
  fail        : Nat := 0
  optional    : Nat := 0   -- TYPE="error": behaviour is optional
  xml11       : Nat := 0   -- a different language
  notUtf8     : Nat := 0   -- the parser does not transcode
  otherEdition : Nat := 0  -- EDITION says the case is not about 1.0 5e
  namespaces  : Nat := 0   -- a Namespaces-in-XML case, not an XML 1.0 one
  fileMissing : Nat := 0
deriving Repr, Inhabited

def Counts.add (a b : Counts) : Counts :=
  { scored := a.scored + b.scored, pass := a.pass + b.pass, fail := a.fail + b.fail,
    optional := a.optional + b.optional, xml11 := a.xml11 + b.xml11,
    notUtf8 := a.notUtf8 + b.notUtf8, otherEdition := a.otherEdition + b.otherEdition,
    namespaces := a.namespaces + b.namespaces,
    fileMissing := a.fileMissing + b.fileMissing }

/-- The sub-manifests, relative to the suite root. Listed rather than
    discovered so the denominator is stable and a missing file is
    visible as a missing file. -/
def subManifests : List String :=
  [ "sun/sun-valid.xml", "sun/sun-invalid.xml", "sun/sun-not-wf.xml",
    "sun/sun-error.xml", "xmltest/xmltest.xml", "japanese/japanese.xml",
    "oasis/oasis.xml", "ibm/ibm_oasis_invalid.xml", "ibm/ibm_oasis_not-wf.xml",
    "ibm/ibm_oasis_valid.xml", "eduni/errata-2e/errata2e.xml",
    "eduni/errata-3e/errata3e.xml", "eduni/errata-4e/errata4e.xml",
    "eduni/namespaces/1.0/rmt-ns10.xml", "eduni/namespaces/1.1/rmt-ns11.xml",
    "eduni/namespaces/errata-1e/errata1e.xml", "eduni/xml-1.1/xml11.xml",
    "eduni/misc/ht-bh.xml" ]

/-- Is this sub-manifest the NAMESPACES suite? Those cases test
    Namespaces in XML, not XML 1.0: `rmt-ns10-004` is
    `<a:foo xmlns:a="…"/>` with an undeclared prefix, which is
    namespace-ill-formed and XML-well-formed. This parser is
    NON-NAMESPACE by design and its header says so, so it accepts them
    correctly and the runner scored 23 of them as failures.

    They are not passes either — the parser is not being asked the
    question — so they go in a bucket of their own, the same treatment
    XML 1.1 and non-UTF-8 already get. Scoring a non-namespace parser
    against a namespace suite measures a layer that is deliberately
    somewhere else (`XML/Namespaces.lean`). -/
def isNamespaceSuite (rel : String) : Bool :=
  rel.startsWith "eduni/namespaces/"

def runManifest (root : String) (rel : String) (verbose : Bool) : IO Counts := do
  let path := root ++ "/" ++ rel
  if !(← System.FilePath.pathExists path) then
    IO.println s!"sub-manifest not found: {rel}"
    return { fileMissing := 1 }
  let src ← IO.FS.readFile path
  -- Some sub-manifests are ENTITY BODIES, not documents: `sun-not-wf.xml`
  -- is a run of sibling `<TEST>` elements with no single root, because
  -- `xmlconf.xml` includes it as an external entity. Rejecting it is
  -- the RIGHT verdict on it as a document, so the runner supplies the
  -- element the entity is included into rather than loosening the
  -- parser. Without this, three manifests and 159 tests vanished from
  -- the denominator with only a one-line notice.
  let wrapped :=
    let body := match src.splitOn "?>" with
      | _ :: rest => if src.startsWith "<?xml" then String.intercalate "?>" rest else src
      | []        => src
    "<TESTCASES>" ++ body ++ "</TESTCASES>"
  let parsed := match parseXML src with
    | .ok d    => some d
    | .error _ => match parseXML wrapped with
      | .ok d    => some d
      | .error _ => none
  match parsed with
  | none =>
      IO.println s!"sub-manifest did not parse: {rel}"
      return { fileMissing := 1 }
  | some doc =>
      let base := root ++ "/" ++ dirOf rel
      let mut c : Counts := {}
      for t in testElements doc.root do
        let ty := (attr? "TYPE" t).getD ""
        let uri := (attr? "URI" t).getD ""
        let ver := (attr? "VERSION" t).getD "1.0"
        let id := (attr? "ID" t).getD "?"
        -- The suite marks which EDITIONS of XML 1.0 a case is about.
        -- The Fifth Edition REPLACED Appendix B's enumerated
        -- BaseChar / CombiningChar / Digit / Extender classes with
        -- the ranges this parser uses, so a case marked
        -- `EDITION="1 2 3 4"` asks a question the Fifth Edition does
        -- not ask — 297 of them, all `not-wf`, all scored as failures
        -- because the runner ignored the attribute. They are NOT
        -- passes either: the parser is not being asked, so the honest
        -- place for them is a bucket of their own.
        let edition := attr? "EDITION" t
        let appliesHere := match edition with
          | none    => true
          | some es => (es.splitOn " ").contains "5"
        if uri == "" then pure ()
        else if isNamespaceSuite rel then c := Counts.add c { namespaces := 1 }
        else if !appliesHere then c := Counts.add c { otherEdition := 1 }
        else if ver == "1.1" then c := Counts.add c { xml11 := 1 }
        else if ty == "error" then c := Counts.add c { optional := 1 }
        else
          let fp := base ++ uri
          if !(← System.FilePath.pathExists fp) then
            c := Counts.add c { fileMissing := 1 }
          else
            let bytes ← IO.FS.readBinFile fp
            match String.fromUTF8? bytes with
            | none => c := Counts.add c { notUtf8 := 1 }
            | some text =>
                -- An EXTERNAL entity's text, read from disk relative
                -- to the document that names it. The parser takes the
                -- resolver as a PARAMETER and stays a total function;
                -- the I/O is here, where it belongs.
                --
                -- Every file the document could name is read up
                -- front, because the resolver is pure. That is
                -- affordable: a conformance case names at most a
                -- handful of small files, all in its own directory.
                let docDir := base ++ dirOf uri
                let mut fetched : List (String × String) := []
                -- An entity file this parser cannot DECODE puts the
                -- case out of profile, the same way a non-UTF-8
                -- DOCUMENT already is. `valid/ext-sa/007`, `008` and
                -- `014` hold their entities in UTF-16; the parser is
                -- UTF-8 only and says so, so the reference comes back
                -- undeclared and the document is rejected — a
                -- transcoding gap scored as a parser failure.
                --
                -- Only files the document NAMES count. A stray
                -- undecodable file in the directory says nothing
                -- about this case.
                let mut entityNotUtf8 := false
                if ← System.FilePath.isDir docDir then
                  for entry in (← System.FilePath.readDir docDir) do
                    let ep := entry.path.toString
                    if !(← System.FilePath.isDir ep) then
                      let b ← IO.FS.readBinFile ep
                      match String.fromUTF8? b with
                      | none   =>
                          if (text.splitOn entry.fileName).length > 1 then
                            entityNotUtf8 := true
                      | some t => fetched := fetched ++ [(entry.fileName, t)]
                let resolve : String → Option String := fun sysId =>
                  let name := ((sysId.splitOn "/").getLast?).getD sysId
                  (fetched.find? (fun (n, _) => n == name)).map (·.2)
                if entityNotUtf8 then
                  c := Counts.add c { notUtf8 := 1 }
                else
                let accepted := match parseXMLWith resolve text with
                  | .ok _    => true
                  | .error _ => false
                -- A NON-VALIDATING parser accepts `valid` AND
                -- `invalid`: the second violates the DTD, which this
                -- parser is not asked to check.
                let want := ty != "not-wf"
                if accepted == want then
                  c := Counts.add c { scored := 1, pass := 1 }
                else
                  c := Counts.add c { scored := 1, fail := 1 }
                  if verbose then
                    IO.println s!"FAIL {id} ({ty}): {uri} was {if accepted then "accepted" else "rejected"}"
      return c

def main (args : List String) : IO UInt32 := do
  let verbose := args.contains "--verbose"
  let dir := (args.filter (fun a => !a.startsWith "--")).head?
    |>.getD "third_party/testing/xml/xmlconf"
  if !(← System.FilePath.isDir dir) then
    IO.println s!"xmlconf runner: corpus not found: {dir}"
    IO.println "run tools/ensure-test-env.sh from the repository root first"
    return 1
  let mut total : Counts := {}
  for m in subManifests do
    let c ← runManifest dir m verbose
    total := Counts.add total c
  IO.println ""
  IO.println s!"xml conformance SCORED: {total.pass} pass, {total.fail} fail (out of {total.scored} in profile)"
  IO.println s!"OUT OF PROFILE, reported not scored: {total.optional} optional-behaviour (TYPE=error),"
  IO.println s!"  {total.xml11} XML 1.1, {total.notUtf8} not UTF-8 (this parser does not transcode),"
  IO.println s!"  {total.otherEdition} for editions 1-4 only (this parser follows the Fifth Edition),"
  IO.println s!"  {total.namespaces} Namespaces-in-XML cases (this parser is non-namespace)"
  if total.fileMissing > 0 then
    IO.println s!"  {total.fileMissing} referenced files not on disk"
  IO.println ""
  IO.println "The parser's profile is XML 1.0, NON-VALIDATING, NON-NAMESPACE,"
  IO.println "UTF-8 only. A `valid` and an `invalid` case must BOTH be accepted:"
  IO.println "`invalid` means it violates the DTD, which a non-validating parser"
  IO.println "is not asked to notice. Counting those as failures would understate"
  IO.println "the parser; counting the out-of-profile cases as passes would"
  IO.println "overstate it."
  return 0
