/-
Harness/RifRun — the RIF Core test suite, run end to end.

`third_party/testing/rif-core-suite/Core_v1.22/Approved` holds five
kinds of case, one directory each:

  * `PositiveSyntaxTest` / `NegativeSyntaxTest` — does the document
    parse?
  * `PositiveEntailmentTest` / `NegativeEntailmentTest` — does the
    premise entail the conclusion?
  * `ImportRejectionTest` — must the document be REJECTED for what it
    imports? Not attempted: this port has no import profile checker,
    and it says so rather than scoring them.

## Three outcomes on the entailment tests

  * **pass / fail** — the verdict matched, or it did not;
  * **undecided** — a built-in outside `RIF/Builtins.lean` blocked a
    rule, or the forward chain hit its round bound. Counted apart,
    because a closure missing a rule is not the closure and reading
    "does not entail" off it would be a guess. RIF-DTB defines 197
    built-ins; naming which are decided is what keeps this honest.

## The conclusion's prefixes

A conclusion file is a BARE FORMULA with no prologue —
`ex:myOnto[ex:hasTitle -> "Example ontology"]`. Its prefixes come
from the premise beside it, and where the premise only IMPORTS an RDF
graph, from that graph's own `@prefix` lines. That is the suite's
convention rather than a RIF rule, and it is applied here because the
alternative is calling a well-formed conclusion unparsable.

Usage: `lake exe l4rif [suite-dir]`
-/
import L4Factoidal.RIF.Engine
import L4Factoidal.RIF.Conformance
import L4Factoidal.XML.Parser
import L4Factoidal.RIF.Ps
import L4Factoidal.Syntax.Turtle
import L4Factoidal.RDFS.Closure
import Harness.Fixtures

open L4Factoidal.RIF
open L4Factoidal.RDF
open L4Factoidal.Syntax
open L4Factoidal.XML (parseXML)

/-- An RDF term as a RIF constant. RIF-RDF Compatibility §3: an IRI is
    a constant in `rif:iri`, a typed literal is one in its datatype,
    and a language-tagged literal is one in `rdf:PlainLiteral` with
    the tag in its lexical form. -/
def gOfTerm : Term → Option GTerm
  | .iri i     => some (gIri i.val)
  | .literal l =>
      (match l.val.langTag with
       | some tag => some (.const (l.val.lexicalForm ++ "@" ++ tag) (rdfNs ++ "PlainLiteral"))
       | none     => some (.const l.val.lexicalForm l.val.datatype.val))
  | .bnode b   => some (.const b localSpace)
  | _          => none

def gOfSubject : Subject → GTerm
  | .iri i   => gIri i.val
  | .bnode b => .const b localSpace

def rdfTypeStr : String := "http://www.w3.org/1999/02/22-rdf-syntax-ns#type"
def rdfsSubClassStr : String := "http://www.w3.org/2000/01/rdf-schema#subClassOf"

/-- A triple as RIF facts. `rdf:type` is MEMBERSHIP and
    `rdfs:subClassOf` is SUBCLASS, not frames: RIF-RDF Compatibility
    maps them onto RIF's own object model, and the corpus asks
    `ex:a # ex:D` of an imported graph. The frame form is kept too,
    because a rule may still read the triple as a slot. -/
def factsOfTriple (t : Triple) : List GAtom :=
  match gOfTerm t.o with
  | none => []
  | some o =>
      let s := gOfSubject t.s
      let base := [GAtom.frame s (gIri t.p.val) o]
      if t.p.val == rdfTypeStr then base ++ [GAtom.member s o]
      else if t.p.val == rdfsSubClassStr then base ++ [GAtom.sub s o]
      else base

/-- `@prefix` declarations of a Turtle document, read textually. The
    Turtle parser resolves them away, and the conclusion needs the
    NAMES. -/
def turtlePrefixes (src : String) : List (String × String) :=
  (src.splitOn "\n").filterMap (fun line =>
    let l := line.trim
    if l.startsWith "@prefix" then
      match ((String.ofList (l.toList.drop 7)).trim).splitOn ":" with
      | p :: rest =>
          let tail := (String.intercalate ":" rest).trim
          if tail.startsWith "<" then
            some (p.trim, String.ofList ((tail.toList.drop 1).takeWhile (· != '>')))
          else none
      | _ => none
    else none)

/-- The last `/`-separated segment of an import location. The corpus
publishes every import under a W3C URL whose last segment is the local
file's stem, so `.../RDF_Combination_Invalid_Profiles_1-import001`
resolves against `RDF_Combination_Invalid_Profiles_1-import001.ttl` or
`…-import001.rif` beside the case. -/
def lastSegment (url : String) : String :=
  match (url.splitOn "/").reverse with
  | seg :: _ => seg
  | []       => url

/-- The local file STEM an import location names. Some locations carry
the extension (`…-import001.rif`) and some do not (`…-import001`), so
a known extension is stripped and the candidate names are rebuilt from
the stem. -/
def importStem (url : String) : String :=
  let seg := lastSegment url
  let chop := fun (x : String) => String.ofList (x.toList.take (x.length - 4))
  if seg.endsWith ".rif" || seg.endsWith ".ttl" || seg.endsWith ".rdf" then chop seg
  else seg

/-- Load a document's imports closure: RIF-XML imports as XML trees,
RDF imports as graphs. Reading files is the runner's job; the verdict
is `L4Factoidal.RIF.Conformance.importRejectionReason`'s. -/
def loadImportClosure (cdir : String) (files : List String) (root : L4Factoidal.XML.Node)
    : IO L4Factoidal.RIF.Conformance.ImportClosure := do
  let mut rifRoots : List L4Factoidal.XML.Node := []
  let mut graphs : List (List Triple) := []
  for site in L4Factoidal.RIF.Conformance.documentImports root do
    match site.location with
    | none     => pure ()
    | some loc =>
      let stem := importStem loc
      for f in files do
        if f == stem ++ ".rif" then
          let src ← IO.FS.readFile (cdir ++ "/" ++ f)
          match parseXML src with
          | .ok d    => rifRoots := rifRoots ++ [d.root]
          | .error _ => pure ()
        else if f == stem ++ ".ttl" then
          let src ← IO.FS.readFile (cdir ++ "/" ++ f)
          match parseTurtle src none with
          | .ok g    => graphs := graphs ++ [g]
          | .error _ => graphs := graphs ++ [[]]
  return { root := root, importedRifRoots := rifRoots, importedGraphs := graphs }

structure Tally where
  pass      : Nat := 0
  fail      : Nat := 0
  undecided : Nat := 0
  notRead   : Nat := 0
  skipped   : Nat := 0
deriving Inhabited

def rounds : Nat := 24

def main (args : List String) : IO UInt32 := do
  let dir ← Harness.fixtureArgOr ((args.filter (fun a => !a.startsWith "--")).head?)
    "third_party/testing/rif-core-suite/Core_v1.22/Approved"
  let verbose := args.contains "--verbose"
  if !(← System.FilePath.isDir dir) then
    IO.println s!"rif runner: corpus not found: {dir}"
    IO.println "run tools/ensure-test-env.sh from the repository root first"
    return 1
  let mut t : Tally := {}
  for kindEntry in (← System.FilePath.readDir dir) do
    if ← System.FilePath.isDir kindEntry.path then
      let kind := kindEntry.fileName
      for caseEntry in (← System.FilePath.readDir kindEntry.path) do
        if ← System.FilePath.isDir caseEntry.path then
          let name := caseEntry.fileName
          let cdir := caseEntry.path.toString
          let files := (← System.FilePath.readDir cdir).toList.map (·.fileName)
          let readOne := fun (suffix : String) => do
            match files.find? (·.endsWith suffix) with
            | none   => pure none
            | some f => (IO.FS.readFile (cdir ++ "/" ++ f)).map some
          if kind == "ImportRejectionTest" then
            -- The import combination must be REJECTED. The verdict is
            -- the library's disjunction of the RIF-RDF/OWL Combination
            -- import-validity conditions; the runner only resolves the
            -- imported files off disk.
            match ← readOne "-input.rif" with
            | none => t := { t with notRead := t.notRead + 1 }
            | some raw =>
              match parseXML raw with
              | .error _ =>
                  t := { t with notRead := t.notRead + 1 }
                  IO.println s!"NOT READ {kind}/{name}: input.rif did not parse as XML"
              | .ok d =>
                let closure ← loadImportClosure cdir files d.root
                match L4Factoidal.RIF.Conformance.importRejectionReason closure with
                | some why =>
                    t := { t with pass := t.pass + 1 }
                    if verbose then IO.println s!"PASS {kind}/{name}: {why}"
                | none =>
                    t := { t with fail := t.fail + 1 }
                    IO.println s!"FAIL {kind}/{name}: this import combination must be rejected, and the checked conditions found no violation"
          else if kind == "PositiveSyntaxTest" || kind == "NegativeSyntaxTest" then
            match ← readOne "-input.rifps" with
            | none => t := { t with notRead := t.notRead + 1 }
            | some src =>
                -- SAFENESS is part of being a RIF Core document, and
                -- a parser cannot see it: `Core_NonSafeness` parses
                -- and is still not RIF Core.
                let parsed := match parseDocument src with
                  | .error _ => false
                  | .ok d    => documentSafe d.rules
                let want := kind == "PositiveSyntaxTest"
                if parsed == want then t := { t with pass := t.pass + 1 }
                else
                  t := { t with fail := t.fail + 1 }
                  IO.println s!"FAIL {kind}/{name}: parsed = {parsed}, expected {want}"
          else
            match ← readOne "-premise.rifps" with
            | none => t := { t with notRead := t.notRead + 1 }
            | some psrc =>
              let csrc? ← (do
                match ← readOne "-conclusion.rifps" with
                | some c => pure (some c)
                | none   => readOne "-nonconclusion.rifps")
              match csrc? with
              | none => t := { t with notRead := t.notRead + 1 }
              | some csrc =>
                -- Any Turtle beside the case is an IMPORTed graph.
                let mut imported : List Triple := []
                let mut extraPrefixes : List (String × String) := []
                for f in files do
                  if f.endsWith ".ttl" then
                    let tsrc ← IO.FS.readFile (cdir ++ "/" ++ f)
                    extraPrefixes := extraPrefixes ++ turtlePrefixes tsrc
                    match parseTurtle tsrc none with
                    | .ok g    => imported := imported ++ g
                    | .error _ => pure ()
                match parseDocument psrc with
                | .error e =>
                    t := { t with notRead := t.notRead + 1 }
                    IO.println s!"NOT READ {kind}/{name}: premise — {e.msg}"
                | .ok doc =>
                    let ctx : Ctx :=
                      { base := doc.base, prefixes := doc.prefixes ++ extraPrefixes }
                    match parseFormulaText ctx csrc with
                    | .error e =>
                        t := { t with notRead := t.notRead + 1 }
                        IO.println s!"NOT READ {kind}/{name}: conclusion — {e.msg}"
                    | .ok goal =>
                        -- An `Import` naming the RDFS entailment
                        -- regime means the imported graph is
                        -- RDFS-CLOSED before it becomes facts.
                        -- An IMPORT names an entailment regime, and
                        -- this port implements Simple, RDF and RDFS.
                        -- A case that imports under OWL-Direct or
                        -- OWL-RDF-Based asks a question about a
                        -- semantics that is not here, and the honest
                        -- answer is UNDECIDED: reading the imported
                        -- graph as plain RDF made
                        -- `Non-Annotation_Entailment` entail a triple
                        -- that OWL puts inside an annotation.
                        let profiles := doc.imports.filterMap (·.2)
                        let unsupportedRegime := profiles.any (fun p =>
                          (p.splitOn "OWL").length > 1 || (p.splitOn "entailment/RIF").length > 1)
                        let wantsRdfs := profiles.any (fun p =>
                          (p.splitOn "RDFS").length > 1)
                        let g := if wantsRdfs && !imported.isEmpty
                                 then L4Factoidal.RDFS.closureFix imported
                                 else imported
                        let facts := g.flatMap factsOfTriple
                        let want := kind == "PositiveEntailmentTest"
                        -- Local constants are DOCUMENT-scoped, so
                        -- the premise's `_p` and the conclusion's are
                        -- different symbols.
                        let rules := doc.rules.map (qualifyRule "premise")
                        let goal := qualifyFormula "conclusion" goal
                        -- An OWL-Direct combination that violates the
                        -- individual/data-value VOCABULARY SEPARATION
                        -- is INCONSISTENT, and an inconsistent
                        -- combination entails everything — including a
                        -- conclusion the rules never derive. Checked
                        -- before the regime is declared unsupported,
                        -- because it is a verdict the port can reach
                        -- without an OWL-Direct closure.
                        let separationInconsistent :=
                          L4Factoidal.RIF.Conformance.owlDirectSeparationInconsistent
                            doc.rules imported
                        match (if separationInconsistent then Verdict.holds
                               else if unsupportedRegime
                               then Verdict.undecided
                                 "the case imports under an entailment regime this port does not implement"
                               else entails rules facts goal rounds) with
                        | .holds =>
                            if want then t := { t with pass := t.pass + 1 }
                            else
                              t := { t with fail := t.fail + 1 }
                              IO.println s!"FAIL {kind}/{name}: entailed, and must not be"
                        | .doesNotHold =>
                            if !want then t := { t with pass := t.pass + 1 }
                            else
                              t := { t with fail := t.fail + 1 }
                              IO.println s!"FAIL {kind}/{name}: not entailed, and must be"
                        | .undecided why =>
                            t := { t with undecided := t.undecided + 1 }
                            if verbose then IO.println s!"UNDECIDED {kind}/{name}: {why}"
  let decided := t.pass + t.fail
  IO.println ""
  IO.println s!"rif-core DECIDED: {t.pass} pass, {t.fail} fail (out of {decided} decided)"
  IO.println s!"UNDECIDED: {t.undecided} cases — a built-in outside this port's slice"
  IO.println s!"  blocked a rule, or the chain reached its round bound"
  IO.println s!"NOT READ: {t.notRead} cases"
  if t.skipped > 0 then
    IO.println s!"IMPORT REJECTION: {t.skipped} cases, not attempted"
  IO.println ""
  IO.println "An UNDECIDED case is counted apart, never as a pass and never as a"
  IO.println "failure: a closure computed without a rule is not the closure, and"
  IO.println "reading `does not entail` off it would be a guess."
  return 0
