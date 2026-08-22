/-
Harness.OwlProbe — run the Lean OWL 2 RL/RDF closure against the real
W3C OWL 2 test corpus, and MEASURE it. Census first, then scores.

## What changed on 2026-08-22

The first version of this probe was a census only: it found that the
corpus is RDF/XML from top to bottom (catalogs AND the premise /
conclusion ontologies, which sit as escaped RDF/XML inside
`test:rdfXmlPremiseOntology` / `test:rdfXmlConclusionOntology` string
literals) and that the Lean tree had no RDF/XML-to-triples mapping. That
statement is now FALSE: `L4Factoidal/Syntax/RdfXml.lean` implements
RDF 1.1 XML Syntax §7 (`RdfXml.parseRdfXml : String → Option String →
Except ParseError Graph`). This file therefore feeds every case whose
ontologies are in RDF/XML to `OWL.RL.closure` / `OWL.RL.detectClash`
and judges it. The census is kept (it is what the runnable count is
measured against).

## The unit of scoring, and why it matches the F* runner

`bin/owl-runner/owl_runner.ml` does NOT score a `test:TestCase` once.
It runs every case once PER TEST TYPE it is typed with
(PositiveEntailmentTest, NegativeEntailmentTest, ConsistencyTest,
InconsistencyTest — a case is often typed with two or three of these)
and prints one score line per type. `ProfileIdentificationTest` is only
TALLIED by the F* runner: no profile checker is run, the RL / EL / QL
profile catalogs are simply fed to the same four judges. The F* figures
in `docs/test-results/latest.json` are the SUMS of those per-type runs
on a catalog (profile-QL: 20 PE + 3 NE + 58 Cons + 6 Inc = 87).

This probe scores the same unit — a (case, test type) pair — so its
denominators are comparable with the F* lines; it prints the per-type
lines as well as the per-catalog sum. Cases in the catalog that carry
none of the four types (ProfileIdentificationTest-only cases, and the
syntax-only `rdfXmlInputOntology` cases) contribute NO unit, exactly as
in the F* runner, and are counted in the diagnostics line instead.

## The four judgements (reproduced from the F* runner, not invented)

Premise base IRI = the case IRI (`rdf:about` of the TestCase), as the
F* runner does (`let base = info.iri`).

* PositiveEntailmentTest — every conclusion triple must appear in the
  RL closure of the premise. The match is the F* runner's RELAXED rule
  (`triple_matches`): a blank node in the conclusion matches ANY term
  at that position (the existential reading the corpus uses for
  `<owl:Ontology/>`), the predicate must be equal, a non-blank subject
  / object must be term-equal (`Term.eqb`: strict on IRIs, XMLLiteral
  c14n on literals). `RDF/Isomorphism.lean` is NOT used here on
  purpose: entailment of a conclusion is subgraph containment modulo
  blank nodes, not graph equality, and the F* runner's rule is the one
  its scores were produced with. Two F* refinements are NOT ported and
  are named as gaps when they bite: datatype VALUE equality on literals
  (`XSD_Facets.term_provably_equal`, so `"1"^^xsd:int` vs
  `"1"^^xsd:integer` differ here) and the PE-via-refutation fallback
  through the DL tableau. DIRECT-only cases (test:semantics DIRECT
  without RDF-BASED) drop conclusion triples whose predicate the
  conclusion graph itself declares an `owl:AnnotationProperty` /
  `owl:OntologyProperty` (port of `OWL_DirectMapping_Filter`).
* NegativeEntailmentTest — PASS iff at least one triple of the
  `rdfXmlNonConclusionOntology` is MISSING from the closure. An absence
  verdict on a closure that hit the budget is a FAIL here (F* #326:
  "unsupported / cap-escape"), never a PASS.
* ConsistencyTest — PASS iff `detectClash` is false on the closure;
  same budget rule as above.
* InconsistencyTest — PASS iff `detectClash` is true on the closure. A
  clash found on a truncated closure is still a real clash
  (`RLTheorems.detectClash_sound`), so it passes; no clash on a
  truncated closure is a FAIL. A case whose test:semantics is RDF-BASED
  only (no DIRECT) is a SKIP, as in the F* runner (Direct Semantics is
  what both engines implement).
* owl:imports — the catalog links each importing case to wrapper nodes
  (`test:importedOntology` → an `owl:Thing` carrying
  `test:importedOntologyIRI` + `test:rdfXmlInputOntology`). Port of
  `load_imports_into_premise`: an import is merged only once the
  premise graph so far asserts `_ owl:imports <that IRI>`, iterated to
  a fixpoint, candidates restricted to the case's own links.

Functional-syntax-only cases (`test:fsPremiseOntology` with
`test:normativeSyntax FUNCTIONAL`, no RDF/XML premise) are
`unsupported functional-syntax`: named, in the denominator. The F*
runner has a narrow Functional Syntax parser; this tree has none.

An RDF/XML premise or conclusion that does not parse is a FAIL with the
parser's message — that is a finding about the parser, not a skip.

## Budget

The closure is the library's `OWL.RL.step`, iterated here round by
round in `IO` (same stopping rule as `OWL.RL.closure`: stop when the
length does not change) so that a wall-clock deadline can be checked
BETWEEN rounds. The F* runner uses fuel 100 and a per-test SIGALRM cap;
this probe uses fuel 100 and `--cap-ms` (default 30000) per closure.
Every cap hit is counted in the diagnostics line and scores as a FAIL
for any absence-shaped verdict.

## Output grammar

    <catalog> <TestType>: N pass, N fail, N skip, N unsupported (out of N)
    <catalog>: N pass, N fail, N skip, N unsupported (out of N)
    HARNESS-DIAG-OWL <catalog>: cases=N units=N triples_parsed=N
        closure_rounds=N clashes=N cap_hits=N parse_failures=N wall_ms=N
    TOTAL: ...

FAIL lines carry a cause tag (`parser:`, `closure-gap:`, `clash:`,
`cap:`, `harness:`) and are grouped by tag at the end of each catalog.

NOT part of the verified library: this file does file I/O, reads the
clock, and prints scores.
-/

import L4Factoidal.XML.Parser
import L4Factoidal.XML.Document
import L4Factoidal.OWL.RLClosure
import L4Factoidal.Syntax.RdfXml
import Harness.Common

open L4Factoidal.XML
open L4Factoidal.RDF
open L4Factoidal.OWL.RL

namespace OwlProbe

/-! ## Catalog reading -/

/-- Local name of a possibly-prefixed element name (`test:TestCase` →
`TestCase`). The catalogs bind `test:` to one namespace throughout, so
the local name identifies the element without a namespace pass. -/
def localName (s : String) : String :=
  match s.splitOn ":" with
  | [_, l] => l
  | _      => s

/-- The fragment of a `test:` / `rdf:` resource IRI
(`…testOntology#PositiveEntailmentTest` → `PositiveEntailmentTest`). -/
def fragmentOf (iri : String) : String := Harness.lastAfter iri "#"

/-- Every element of the tree, in document order. -/
partial def elementsOfAux : Node → List (String × List Attribute × List Node)
  | .element tag attrs kids =>
      (tag, attrs, kids) :: (kids.flatMap elementsOfAux)
  | _ => []

/-- Concatenated text content of a node's direct text children. -/
def directText (kids : List Node) : String :=
  String.join (kids.filterMap (fun n => match n with
    | .text t  => some t
    | .cdata t => some t
    | _        => none))

def attrValue (attrs : List Attribute) (name : String) : Option String :=
  (attrs.find? (fun a => a.name == name)).map (·.value)

/-- One `test:TestCase`, as read from the catalog. -/
structure Case where
  iri           : String := ""
  id            : String := ""
  /-- Fragments of the `rdf:type` resources. -/
  types         : List String := []
  /-- Fragments of `test:semantics` (DIRECT / RDF-BASED). -/
  semantics     : List String := []
  /-- Fragments of `test:normativeSyntax`. -/
  normSyntax    : List String := []
  premise       : Option String := none
  conclusion    : Option String := none
  nonConclusion : Option String := none
  fsPremise     : Bool := false
  /-- `test:importedOntology` wrapper-node IRIs. -/
  imports       : List String := []
deriving Inhabited

/-- An import wrapper node: the ontology IRI the premise's `owl:imports`
names, and its RDF/XML text. -/
structure ImportDoc where
  wrapper : String
  ontIri  : String
  text    : Option String
deriving Inhabited

def readCase (attrs : List Attribute) (kids : List Node) : Case := Id.run do
  let mut c : Case := { iri := (attrValue attrs "rdf:about").getD "" }
  for n in kids do
    match n with
    | .element tag a k =>
      let res := (attrValue a "rdf:resource").getD ""
      match localName tag with
      | "type"                        => c := { c with types := c.types ++ [fragmentOf res] }
      | "identifier"                  => c := { c with id := directText k }
      | "semantics"                   => c := { c with semantics := c.semantics ++ [fragmentOf res] }
      | "normativeSyntax"             => c := { c with normSyntax := c.normSyntax ++ [fragmentOf res] }
      | "rdfXmlPremiseOntology"       => c := { c with premise := some (directText k) }
      | "rdfXmlConclusionOntology"    => c := { c with conclusion := some (directText k) }
      | "rdfXmlNonConclusionOntology" => c := { c with nonConclusion := some (directText k) }
      | "fsPremiseOntology"           => c := { c with fsPremise := true }
      | "importedOntology"            => c := { c with imports := c.imports ++ [res] }
      | _ => pure ()
    | _ => pure ()
  return c

def readImportDoc (attrs : List Attribute) (kids : List Node) : Option ImportDoc := Id.run do
  let some w := attrValue attrs "rdf:about" | return none
  let mut ont : Option String := none
  let mut text : Option String := none
  for n in kids do
    match n with
    | .element tag a k =>
      match localName tag with
      | "importedOntologyIRI"  => ont := attrValue a "rdf:resource"
      | "rdfXmlInputOntology"  => text := some (directText k)
      | _ => pure ()
    | _ => pure ()
  match ont with
  | some o => return some { wrapper := w, ontIri := o, text := text }
  | none   => return none

/-- One catalog: its cases and its import wrapper nodes. -/
structure Catalog where
  cases   : List Case
  imports : List ImportDoc

/-- Read one catalog file. Returns `none` if the Lean XML parser could
not read it — which is itself a measurement, so the caller reports it
rather than hiding it. -/
def readCatalog (path : System.FilePath) : IO (Option Catalog) := do
  let src ← IO.FS.readFile path
  match parseXML src with
  | .error e =>
      IO.println s!"  XML PARSE FAILED for {path}: {repr e}"
      return none
  | .ok doc =>
      let els := elementsOfAux doc.root
      let cases := els.filterMap (fun (tag, attrs, kids) =>
        if localName tag == "TestCase" then some (readCase attrs kids) else none)
      let imports := els.filterMap (fun (tag, attrs, kids) =>
        if localName tag == "TestCase" then none else readImportDoc attrs kids)
      return some { cases := cases, imports := imports }

/-! ## Vocabulary the harness needs beyond `OWL/Vocabulary.lean` -/

def owlImports : WfIri := ⟨"http://www.w3.org/2002/07/owl#imports", by decide⟩
def owlAnnotationProperty : WfIri :=
  ⟨"http://www.w3.org/2002/07/owl#AnnotationProperty", by decide⟩
def owlOntologyProperty : WfIri :=
  ⟨"http://www.w3.org/2002/07/owl#OntologyProperty", by decide⟩

/-! ## Display -/

def showSubject : Subject → String
  | .iri i   => s!"<{i.val}>"
  | .bnode b => s!"_:{b}"

def showTerm : Term → String
  | .iri i      => s!"<{i.val}>"
  | .bnode b    => s!"_:{b}"
  | .literal l  =>
      match l.val.langTag with
      | some lt => s!"\"{l.val.lexicalForm}\"@{lt}"
      | none    => s!"\"{l.val.lexicalForm}\"^^<{l.val.datatype.val}>"
  | .tripleTerm s p o => s!"<<( {showSubject s} <{p.val}> {showTerm o} )>>"

def showTriple (t : Triple) : String :=
  s!"{showSubject t.s} <{t.p.val}> {showTerm t.o}"

/-! ## Conclusion matching — the F* runner's relaxed rule -/

/-- Port of `subject_matches`: a blank-node pattern matches anything. -/
def subjMatches (pat s : Subject) : Bool :=
  match pat with
  | .bnode _ => true
  | _        => pat == s

/-- Port of `object_matches`, minus datatype value equality (named in
the header as a gap): a blank-node pattern matches anything, otherwise
engine term equality. -/
def objMatches (pat o : Term) : Bool :=
  match pat with
  | .bnode _ => true
  | _        => pat.eqb o

/-- Port of `triple_matches`. -/
def tripleMatches (pat t : Triple) : Bool :=
  subjMatches pat.s t.s && pat.p == t.p && objMatches pat.o t.o

/-- Port of `conclusion_triple_in_closure`. -/
def inClosure (cl : Graph) (pat : Triple) : Bool := cl.any (tripleMatches pat)

/-- Port of `OWL_DirectMapping_Filter.exclude_annotation_triples`: drop
the triples whose predicate the graph itself types as an annotation or
ontology property. -/
def excludeAnnotationTriples (g : Graph) : Graph :=
  let isAnn (p : WfIri) : Bool :=
    g.any (fun t => t.s == Subject.iri p && t.p == rdfType &&
      (t.o == Term.iri owlAnnotationProperty || t.o == Term.iri owlOntologyProperty))
  g.filter (fun t => !isAnn t.p)

/-! ## Parsing + imports -/

def parseDoc (what : String) (base : String) (text : String) : Except String Graph :=
  match L4Factoidal.Syntax.RdfXml.parseRdfXml text (some base) with
  | .ok g    => .ok g
  | .error e => .error s!"parser: {what}: {e.msg} (at {e.pos})"

/-- Port of `load_imports_into_premise`: merge an import only once the
graph so far asserts `owl:imports` for it; iterate to a fixpoint. The
fuel is the number of candidate imports, which bounds the rounds. -/
def loadImports (lookup : List ImportDoc) (allowed : List String)
    (g : Graph) (seen : List String) : Nat → Except String Graph
  | 0       => .ok g
  | n + 1 =>
    let targets := g.filterMap (fun t =>
      if t.p == owlImports then
        match t.o with
        | .iri i => if allowed.contains i.val && !seen.contains i.val then some i.val else none
        | _ => none
      else none)
    let targets := targets.eraseDups
    match targets with
    | [] => .ok g
    | _ =>
      let seen' := seen ++ targets
      let merged : Except String Graph := targets.foldlM (fun acc i =>
        match lookup.find? (fun d => d.ontIri == i) with
        | some { text := some txt, .. } =>
            match parseDoc s!"import {i}" i txt with
            | .ok gi   => .ok (acc ++ gi)
            | .error e => .error e
        | _ => .ok acc) g
      match merged with
      | .ok g' => loadImports lookup allowed g' seen' n
      | .error e => .error e

/-! ## The closure, round by round, under a clock -/

structure ClosureResult where
  graph  : Graph
  rounds : Nat
  capped : Bool

/-- `OWL.RL.closure` with the same stopping rule, one `step` per loop
iteration so the wall clock can be read between rounds. Fuel exhausted
without saturation counts as a cap hit too. -/
def closureIO (g : Graph) (fuel : Nat) (deadlineMs : Nat) : IO ClosureResult := do
  let mut cur := g
  let mut rounds := 0
  for _ in [0:fuel] do
    let g' := step cur
    rounds := rounds + 1
    if g'.length = cur.length then
      return { graph := cur, rounds := rounds, capped := false }
    cur := g'
    if (← IO.monoMsNow) > deadlineMs then
      return { graph := cur, rounds := rounds, capped := true }
  return { graph := cur, rounds := rounds, capped := true }

/-! ## Judging -/

def closureFuel : Nat := 100

/-- Per-catalog measurement counters. -/
structure Measure where
  triplesParsed  : Nat := 0
  closureRounds  : Nat := 0
  clashes        : Nat := 0
  capHits        : Nat := 0
  parseFailures  : Nat := 0
deriving Repr

def Measure.add (a b : Measure) : Measure :=
  { triplesParsed := a.triplesParsed + b.triplesParsed,
    closureRounds := a.closureRounds + b.closureRounds,
    clashes := a.clashes + b.clashes, capHits := a.capHits + b.capHits,
    parseFailures := a.parseFailures + b.parseFailures }

def isFunctionalOnly (c : Case) : Bool :=
  c.premise.isNone && c.fsPremise && c.normSyntax.contains "FUNCTIONAL"

def isDirectOnly (c : Case) : Bool :=
  c.semantics.contains "DIRECT" && !c.semantics.contains "RDF-BASED"

def isRdfBasedOnly (c : Case) : Bool :=
  c.semantics.contains "RDF-BASED" && !c.semantics.contains "DIRECT"

/-- Parse the premise, merge imports, run the closure. Shared by the
four judges. Returns the closure result or a fail outcome, plus the
measurement delta. -/
def premiseClosure (cat : Catalog) (c : Case) (capMs : Nat)
    : IO (Except Harness.Outcome ClosureResult × Measure) := do
  match c.premise with
  | none => return (.error (.fail "harness: no RDF/XML premise"), {})
  | some ptxt =>
    match parseDoc "premise" c.iri ptxt with
    | .error e => return (.error (.fail e), { parseFailures := 1 })
    | .ok gp0 =>
      let allowed := c.imports.filterMap (fun w =>
        (cat.imports.find? (fun d => d.wrapper == w)).map (·.ontIri))
      match loadImports cat.imports allowed gp0 [] (allowed.length + 1) with
      | .error e => return (.error (.fail e), { parseFailures := 1 })
      | .ok gp =>
        let t0 ← IO.monoMsNow
        let r ← closureIO gp closureFuel (t0 + capMs)
        let m : Measure := { triplesParsed := gp.length, closureRounds := r.rounds,
                             capHits := if r.capped then 1 else 0 }
        return (.ok r, m)

def judgePositive (cat : Catalog) (c : Case) (capMs : Nat) : IO (Harness.Outcome × Measure) := do
  if isFunctionalOnly c then return (.unsupported "functional-syntax", {})
  match c.conclusion with
  | none => return (.fail "harness: no RDF/XML conclusion", {})
  | some ctxt =>
    match parseDoc "conclusion" c.iri ctxt with
    | .error e => return (.fail e, { parseFailures := 1 })
    | .ok gc0 =>
      if gc0.isEmpty then return (.fail "parser: conclusion parsed to zero triples", { parseFailures := 1 })
      let (res, m) ← premiseClosure cat c capMs
      match res with
      | .error o => return (o, m)
      | .ok r =>
        let gc := if isDirectOnly c then excludeAnnotationTriples gc0 else gc0
        let m := { m with triplesParsed := m.triplesParsed + gc0.length }
        match gc.find? (fun t => !inClosure r.graph t) with
        | none => return (.pass, m)
        | some t =>
          if r.capped then
            return (.fail s!"cap: closure budget hit after {r.rounds} rounds ({r.graph.length} triples); missing {showTriple t}", m)
          else
            return (.fail s!"closure-gap: missing {showTriple t} (closure {r.graph.length} triples, {r.rounds} rounds)", m)

def judgeNegative (cat : Catalog) (c : Case) (capMs : Nat) : IO (Harness.Outcome × Measure) := do
  if isFunctionalOnly c then return (.unsupported "functional-syntax", {})
  match c.nonConclusion with
  | none => return (.fail "harness: no RDF/XML non-conclusion", {})
  | some ctxt =>
    match parseDoc "non-conclusion" c.iri ctxt with
    | .error e => return (.fail e, { parseFailures := 1 })
    | .ok gc =>
      if gc.isEmpty then return (.fail "parser: non-conclusion parsed to zero triples", { parseFailures := 1 })
      let (res, m) ← premiseClosure cat c capMs
      match res with
      | .error o => return (o, m)
      | .ok r =>
        let m := { m with triplesParsed := m.triplesParsed + gc.length }
        if gc.any (fun t => !inClosure r.graph t) then
          if r.capped then
            return (.fail s!"cap: absence verdict on a closure that hit the budget after {r.rounds} rounds", m)
          else return (.pass, m)
        else
          return (.fail s!"closure-gap: every non-conclusion triple was derived (unexpected entailment)", m)

def judgeConsistency (cat : Catalog) (c : Case) (capMs : Nat) : IO (Harness.Outcome × Measure) := do
  if isFunctionalOnly c then return (.unsupported "functional-syntax", {})
  let (res, m) ← premiseClosure cat c capMs
  match res with
  | .error o => return (o, m)
  | .ok r =>
    let clash := detectClash r.graph
    let m := { m with clashes := m.clashes + (if clash then 1 else 0) }
    if clash then return (.fail s!"clash: detectClash fired on a premise asserted consistent ({r.graph.length} triples)", m)
    else if r.capped then
      return (.fail s!"cap: absence verdict on a closure that hit the budget after {r.rounds} rounds", m)
    else return (.pass, m)

def judgeInconsistency (cat : Catalog) (c : Case) (capMs : Nat) : IO (Harness.Outcome × Measure) := do
  if isFunctionalOnly c then return (.unsupported "functional-syntax", {})
  if isRdfBasedOnly c then return (.skip "semantics-rdf-based-only", {})
  let (res, m) ← premiseClosure cat c capMs
  match res with
  | .error o => return (o, m)
  | .ok r =>
    let clash := detectClash r.graph
    let m := { m with clashes := m.clashes + (if clash then 1 else 0) }
    if clash then return (.pass, m)
    else if r.capped then
      return (.fail s!"cap: no clash on a closure that hit the budget after {r.rounds} rounds", m)
    else return (.fail s!"closure-gap: no clash row fired on a premise asserted inconsistent ({r.graph.length} triples, {r.rounds} rounds)", m)

def testTypes : List String :=
  ["PositiveEntailmentTest", "NegativeEntailmentTest", "ConsistencyTest", "InconsistencyTest"]

def judge (cat : Catalog) (c : Case) (capMs : Nat) : String → IO (Harness.Outcome × Measure)
  | "PositiveEntailmentTest" => judgePositive cat c capMs
  | "NegativeEntailmentTest" => judgeNegative cat c capMs
  | "ConsistencyTest"        => judgeConsistency cat c capMs
  | "InconsistencyTest"      => judgeInconsistency cat c capMs
  | ty                       => pure (.unsupported s!"test type {ty}", {})

/-- The cause tag of a FAIL reason: the text before the first `:`. -/
def causeOf (reason : String) : String :=
  match reason.splitOn ":" with
  | c :: _ :: _ => c
  | _           => "other"

/-! ## Per-catalog run -/

structure CatalogResult where
  score    : Harness.Score := {}
  perType  : List (String × Harness.Score) := []
  measure  : Measure := {}
  fails    : List (String × String × String) := []  -- (cause, id, reason)
  units    : Nat := 0
  wallMs   : Nat := 0

def bumpType (l : List (String × Harness.Score)) (ty : String) (o : Harness.Outcome)
    : List (String × Harness.Score) :=
  match l.find? (fun p => p.1 == ty) with
  | some _ => l.map (fun p => if p.1 == ty then (p.1, p.2.bump o) else p)
  | none   => l ++ [(ty, Harness.Score.bump {} o)]

def runCatalog (name : String) (cat : Catalog) (capMs : Nat) (verbose : Bool)
    : IO CatalogResult := do
  let t0 ← IO.monoMsNow
  let mut r : CatalogResult := {}
  for c in cat.cases do
    for ty in testTypes do
      if c.types.contains ty then
        let (o, m) ← judge cat c capMs ty
        let label := s!"{c.id} [{ty}]"
        match o with
        | .pass => if verbose then IO.println (o.line label)
        | .fail reason =>
            IO.println (o.line label)
            r := { r with fails := r.fails ++ [(causeOf reason, c.id, reason)] }
        | _ => IO.println (o.line label)
        r := { r with score := r.score.bump o, perType := bumpType r.perType ty o,
                      measure := r.measure.add m, units := r.units + 1 }
  let t1 ← IO.monoMsNow
  r := { r with wallMs := t1 - t0 }
  -- Score lines.
  for ty in testTypes do
    match r.perType.find? (fun p => p.1 == ty) with
    | some (_, s) => IO.println (Harness.Score.line s!"{name} {ty}" s)
    | none => pure ()
  IO.println (Harness.Score.line name r.score)
  IO.println s!"HARNESS-DIAG-OWL {name}: cases={cat.cases.length} units={r.units} \
triples_parsed={r.measure.triplesParsed} closure_rounds={r.measure.closureRounds} \
clashes={r.measure.clashes} cap_hits={r.measure.capHits} \
parse_failures={r.measure.parseFailures} wall_ms={r.wallMs}"
  -- FAILs grouped by cause.
  let causes := (r.fails.map (·.1)).eraseDups
  for cause in causes do
    let these := r.fails.filter (fun f => f.1 == cause)
    IO.println s!"  FAIL-GROUP {name} {cause}: {these.length} — {String.intercalate ", " (these.map (·.2.1))}"
  return r

/-! ## Census (kept from the first version) -/

def countTrue (f : Case → Bool) (cs : List Case) : Nat := (cs.filter f).length

def printCensus (name : String) (cs : List Case) : IO Unit := do
  let n := cs.length
  IO.println s!"{name}: {n} test cases"
  IO.println s!"    RDF/XML premise: {countTrue (·.premise.isSome) cs} of {n}"
  IO.println s!"    RDF/XML conclusion: {countTrue (·.conclusion.isSome) cs} of {n}"
  IO.println s!"    RDF/XML non-conclusion: {countTrue (·.nonConclusion.isSome) cs} of {n}"
  IO.println s!"    OWL functional-syntax premise: {countTrue (·.fsPremise) cs} of {n}"
  IO.println s!"    functional-syntax only (unsupported): {countTrue isFunctionalOnly cs} of {n}"
  for ty in testTypes ++ ["ProfileIdentificationTest"] do
    IO.println s!"    {ty}: {countTrue (·.types.contains ty) cs} of {n}"

/-- A self-check that the closure engine this probe drives is actually
wired up and computing: run it over a two-triple graph and confirm
cax-sco fires and an unrelated triple does not appear. Not a
conformance measurement — it is the "the engine is loaded" line. -/
def engineSelfCheck : (Bool × Bool) :=
  let a : WfIri := ⟨"http://ex/A", by decide⟩
  let b : WfIri := ⟨"http://ex/B", by decide⟩
  let c : WfIri := ⟨"http://ex/C", by decide⟩
  let x : WfIri := ⟨"http://ex/x", by decide⟩
  let g : Graph :=
    [⟨.iri a, rdfsSubClassOf, .iri b⟩, ⟨.iri x, rdfType, .iri a⟩]
  let cl := closure g 3
  (memB cl ⟨.iri x, rdfType, .iri b⟩, memB cl ⟨.iri x, rdfType, .iri c⟩)

def catalogs : List String :=
  ["profile-RL.rdf", "profile-EL.rdf", "profile-QL.rdf",
   "type-positive-entailment.rdf", "type-inconsistency.rdf",
   "type-consistency.rdf"]

/-! ## Main -/

structure Opts where
  dir     : String := "../../third_party/testing/owl"
  only    : List String := []
  capMs   : Nat := 30000
  verbose : Bool := false

def parseArgs : List String → Opts → Opts
  | [], o => o
  | "--cap-ms" :: n :: rest, o => parseArgs rest { o with capMs := n.toNat!.max 1 }
  | "-v" :: rest, o => parseArgs rest { o with verbose := true }
  | "--dir" :: d :: rest, o => parseArgs rest { o with dir := d }
  | a :: rest, o =>
      if a.endsWith ".rdf" then parseArgs rest { o with only := o.only ++ [a] }
      else parseArgs rest { o with dir := a }

def main (args : List String) : IO UInt32 := do
  let o := parseArgs args {}
  let dir : System.FilePath := o.dir
  IO.println "Lean OWL 2 RL/RDF probe — corpus census + closure run"
  IO.println s!"corpus dir: {dir}  closure fuel: {closureFuel}  per-closure cap: {o.capMs} ms"
  let (scoOk, unrelatedAbsent) := engineSelfCheck
  IO.println s!"engine self-check: cax-sco fires = {scoOk}, \
unrelated triple absent = {!unrelatedAbsent}"
  let names := if o.only.isEmpty then catalogs else o.only
  let mut total : Harness.Score := {}
  let mut totalM : Measure := {}
  let mut totalCases := 0
  let mut notRead : List String := []
  for name in names do
    let p := dir / name
    if !(← p.pathExists) then
      IO.println s!"  MISSING {name}"
      notRead := notRead ++ [name]
    else
      match ← readCatalog p with
      | none => notRead := notRead ++ [name]
      | some cat =>
        printCensus name cat.cases
        let r ← runCatalog name cat o.capMs o.verbose
        total := total.add r.score
        totalM := totalM.add r.measure
        totalCases := totalCases + cat.cases.length
        IO.println ""
  IO.println (Harness.Score.line "TOTAL" total)
  IO.println s!"HARNESS-DIAG-OWL TOTAL: cases={totalCases} units={total.total} \
triples_parsed={totalM.triplesParsed} closure_rounds={totalM.closureRounds} \
clashes={totalM.clashes} cap_hits={totalM.capHits} parse_failures={totalM.parseFailures}"
  IO.println "F* owl_runner comparison (docs/test-results/latest.json, RL regime"
  IO.println "  unless stated). Each F* number is the SUM of that catalog's"
  IO.println "  per-test-type runs (PE + NE + Consistency + Inconsistency), the"
  IO.println "  same unit this probe scores; functional-syntax skips are outside"
  IO.println "  the F* denominator but INSIDE this probe's (as unsupported):"
  IO.println "  owl_rl_positive_entailment 30 pass, 0 fail (out of 30)"
  IO.println "     = profile-RL.rdf, PositiveEntailmentTest line only"
  IO.println "  owl2_profile_ql 87 pass, 0 fail (out of 87)     = profile-QL.rdf, four types"
  IO.println "  owl2_profile_el 119 pass, 1 fail (out of 120)   = profile-EL.rdf, four types"
  IO.println "  owl2_dl_inconsistency 126 pass, 1 fail (out of 127)"
  IO.println "     = type-inconsistency.rdf, DL regime (RL closure + tableau refuter)"
  IO.println "  (type-positive-entailment.rdf and type-consistency.rdf have no"
  IO.println "   published F* line in latest.json.)"
  for f in notRead do
    IO.println s!"  catalog not read: {f}"
  return (if notRead.isEmpty && scoOk && total.fail == 0 then 0 else 1)

end OwlProbe

def main (args : List String) : IO UInt32 := OwlProbe.main args
