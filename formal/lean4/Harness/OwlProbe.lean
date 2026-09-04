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
  its scores were produced with. One F* refinement is NOT ported and
  is named as a gap when it bites: datatype VALUE equality on literals
  (`XSD_Facets.term_provably_equal`, so `"1"^^xsd:int` vs
  `"1"^^xsd:integer` differ here). The PE-via-refutation fallback
  through the DL tableau IS ported (2026-09-04): under `--dl` a
  conclusion the containment check misses is then tried against the
  conformance relation itself, `Ont(d1) union not-Ont(d2)`
  unsatisfiable, through `OWL.Refute.negationGoals` and
  `tableauConsistent` — see `refuteEntails` below and
  `docs/designissues/2026-09-04-owl-b1-class-expression-structure.md`.
  DIRECT-only cases (test:semantics DIRECT
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

## Budget and engine

The closure is the library's INDEXED engine `OWL.RL.stepI`
(`RLClosureIndexed.lean`), iterated here round by round in `IO` (same
stopping rule as `OWL.RL.closure`: stop when the size does not change)
so that a wall-clock deadline can be checked inside a round. The
indexed engine computes the same list as the specification-level
`OWL.RL.closure` at every fuel (`RLClosureIndexed.indexedClosure_eq`,
a proved list equality), so the scores below are scores of the
specification engine; the index only changes the wall clock. The F*
runner uses fuel 100 and a per-test SIGALRM cap; this probe uses fuel
100 and `--cap-ms` (default 30000) per closure. Every cap hit is
counted in the diagnostics line and scores as a FAIL for any
absence-shaped verdict.

`--profile --case <id>` runs the LIST engine row by row with timing
(the measurement that motivated the index), then the indexed round on
the same input, and checks the two rounds produced the same list.

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
import L4Factoidal.OWL.RLClosureIndexed
import L4Factoidal.OWL.Materialise
import L4Factoidal.OWL.Refute
import L4Factoidal.OWL.NegationGoals
import L4Factoidal.OWL.FunctionalSyntax
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
  /-- The FUNCTIONAL-SYNTAX premise / conclusion text, when the case
      carries one. Recording only the Boolean made every such case
      `unsupported` even where the subset parser can read it. -/
  fsPremiseText : Option String := none
  fsConclusionText : Option String := none
  fsNonConclusionText : Option String := none
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
      | "fsPremiseOntology"           =>
          c := { c with fsPremise := true, fsPremiseText := some (directText k) }
      | "fsConclusionOntology"        =>
          c := { c with fsConclusionText := some (directText k) }
      | "fsNonConclusionOntology"     =>
          c := { c with fsNonConclusionText := some (directText k) }
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
fuel is the number of candidate imports, which bounds the rounds.

Blank-node scoping: every document is parsed on its own, so the
parser's generated labels (`b0`, `b1`, …) collide across documents.
The merge is therefore an RDF MERGE (RDF 1.1 Semantics §4.1), not a
union: each imported graph's labels get a per-import ordinal prefix
(`Graph.prefixBnodes`), the F* runner's 2026-07-10 fix
(`owl_runner.ml` "Bnode renaming"). Before this, the wine+food pair
of WebOnt-miscellaneous-001/002/011 carried chimera restrictions (one
label holding wine's `owl:onProperty` and food's `owl:hasValue`), and
the OWL RL closure of that garbage grew past 68 000 triples and
clashed on a premise the corpus asserts consistent (measured
2026-08-22 with the indexed engine; the list engine never got past
round 1 so the defect was invisible). -/
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
            | .ok gi   =>
                -- ordinal = position of this import among all seen so far
                let ord := (seen'.findIdx? (· == i)).getD 0
                .ok (acc ++ gi.prefixBnodes s!"imp{ord}_")
            | .error e => .error e
        | _ => .ok acc) g
      match merged with
      | .ok g' => loadImports lookup allowed g' seen' n
      | .error e => .error e

/-! ## The closure, round by round, under a clock -/

structure ClosureResult where
  graph  : Graph
  index  : Index
  rounds : Nat
  capped : Bool

/-- One round, `OWL.RL.stepI i`, computed per driving triple so the
clock can be read INSIDE a round (a cap that only fires between rounds
is not a cap). When the deadline has not passed the result is exactly
`i.insertAll (stepConclusionsS (Store.ofIndex i))`, i.e. `stepI i`;
`none` means the deadline passed mid-round. -/
def stepIO (i : Index) (deadlineMs : Nat) : IO (Option Index) := do
  let s := Store.ofIndex i
  let mut acc : Array Triple := #[]
  let mut n := 0
  for d in s.graph do
    acc := acc ++ (conclusionsFromS s d).toArray
    n := n + 1
    if n % 32 == 0 then
      if (← IO.monoMsNow) > deadlineMs then return none
  return some (i.insertAll (axiomTriples ++ acc.toList))

/-- `OWL.RL.closureI` with the same stopping rule (stop when the size
did not change), one `stepIO` per loop iteration. Fuel exhausted
without saturation counts as a cap hit too. -/
def closureIO (g : Graph) (fuel : Nat) (deadlineMs : Nat) : IO ClosureResult := do
  let mut cur := Index.ofGraph g
  let mut rounds := 0
  for _ in [0:fuel] do
    match ← stepIO cur deadlineMs with
    | none =>
      return { graph := cur.toGraph, index := cur, rounds := rounds, capped := true }
    | some i' =>
      rounds := rounds + 1
      if i'.all.size = cur.all.size then
        return { graph := cur.toGraph, index := cur, rounds := rounds, capped := false }
      cur := i'
  return { graph := cur.toGraph, index := cur, rounds := rounds, capped := true }

/-! ## Judging -/

def closureFuel : Nat := 100

/-- The refuter's DEFAULT budget per premise, overridable with
`--refute-budget N`. The budget is THREADED through the branch
search, so it bounds the whole search rather than each branch, and
the cost is close to linear in it. Running out answers `none` — not
refuted — so the cap withholds a verdict rather than inventing one.

📊 Measured on `type-inconsistency.rdf`, 2026-08-23, out of 127
decided:

| Budget | Score | Wall |
| --- | --- | --- |
| 16 | 88 pass, 39 fail | 1.9 s |
| 24 | 90 pass, 37 fail | 2.2 s |
| 40 | 90 pass, 37 fail | 2.8 s |
| 64 | 92 pass, 35 fail | 3.5 s |
| 200 | 92 pass, 35 fail | 6.6 s |
| 400 | 92 pass, 35 fail | 9.6 s |

64 is the default: it is where the curve flattens, and four seconds
on the catalog the refuter exists for is not a cost worth trading a
case against. Above it nothing more closes — the remaining 35 need
rules, not budget. -/
def defaultRefuteBudget : Nat := 64

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

/-- A functional-syntax document the subset parser CAN read, as
    triples. `none` when the case has none or when the parser declines
    — the two are the same to the caller, which then reports the case
    as `unsupported functional-syntax` rather than as an empty
    ontology. -/
def fsGraph (txt? : Option String) : Option Graph :=
  txt?.bind L4Factoidal.OWL.FS.parseFunctionalSyntax

/-- Is the case functional-syntax-only AND outside the subset the
    parser reads? Only then is it `unsupported`. -/
def isFunctionalUnread (c : Case) : Bool :=
  isFunctionalOnly c && (fsGraph c.fsPremiseText).isNone

/-- Parse the premise and merge its imports: the graph the closure
runs on. -/
def premiseGraph (cat : Catalog) (c : Case) : Except Harness.Outcome Graph :=
  match c.premise with
  | none =>
      -- No RDF/XML premise: fall back to the functional-syntax one,
      -- which the OWL 2 Mapping to RDF Graphs tables turn into the
      -- same triples an RDF/XML premise would have carried.
      (match fsGraph c.fsPremiseText with
       | some g => .ok g
       | none   => .error (.fail "harness: no RDF/XML premise"))
  | some ptxt =>
    match parseDoc "premise" c.iri ptxt with
    | .error e => .error (.fail e)
    | .ok gp0 =>
      let allowed := c.imports.filterMap (fun w =>
        (cat.imports.find? (fun d => d.wrapper == w)).map (·.ontIri))
      match loadImports cat.imports allowed gp0 [] (allowed.length + 1) with
      | .error e => .error (.fail e)
      | .ok gp => .ok gp

/-- Parse the premise, merge imports, run the closure. Shared by the
four judges. Returns the closure result or a fail outcome, plus the
measurement delta. -/
def premiseClosure (cat : Catalog) (c : Case) (capMs : Nat) (dl : Bool)
    : IO (Except Harness.Outcome ClosureResult × Measure) := do
  match premiseGraph cat c with
  | .error o => return (.error o, { parseFailures := 1 })
  | .ok gp =>
    let t0 ← IO.monoMsNow
    let r ← closureIO gp closureFuel (t0 + capMs)
    if !dl then
      let m : Measure := { triplesParsed := gp.length, closureRounds := r.rounds,
                           capHits := if r.capped then 1 else 0 }
      return (.ok r, m)
    else
      -- `--dl`: one class-expression materialisation pass over the
      -- closed graph, then the closure again so the new `rdf:type`
      -- triples propagate through `rdfs:subClassOf`. The pass writes
      -- only memberships `L4Factoidal.OWL.Mat.cePositiveSound`
      -- admits, so every triple it adds is entailed. ONE pass, not a
      -- fixpoint: iterating materialisation against the closure is a
      -- separate decision with its own cost, and a bounded pass
      -- cannot be mistaken for a complete DL procedure.
      let (gm, budgetHit) := L4Factoidal.OWL.Mat.materialiseWithBudget r.graph
                               L4Factoidal.OWL.Mat.defaultBudget
      if budgetHit || gm.length == r.graph.length then
        -- A budget hit is a CAP HIT: the memberships this premise
        -- would have gained were not computed, so an absence verdict
        -- on it is not evidence of anything.
        let m : Measure := { triplesParsed := gp.length, closureRounds := r.rounds,
                             capHits := if r.capped || budgetHit then 1 else 0 }
        return (.ok r, m)
      else
        let t1 ← IO.monoMsNow
        let r2 ← closureIO gm closureFuel (t1 + capMs)
        let m : Measure := { triplesParsed := gp.length,
                             closureRounds := r.rounds + r2.rounds,
                             capHits := (if r.capped then 1 else 0) +
                                        (if r2.capped then 1 else 0) }
        return (.ok r2, m)

/-! ## Profiling — where does a round spend its time?

`--profile --case <id> [--rounds N]` runs the LIST engine round by
round on the named cases and prints, per round, the wall time and the
emitted (pre-dedup) triple count of every row function, then the time
the exact dedup (`addAll`) takes. This is the measurement the
`measuring-inference` skill asks for BEFORE any engine change: which
phase the time is in, per rule family, on the real corpus cases. -/

/-- Every row function of `RLClosure.conclusionsList`, named, in that
list's order. -/
def namedRows : List (String × (Graph → Triple → List Triple)) :=
  [ ("eq-ref-s", eqRefSFor), ("eq-ref-p", eqRefPFor), ("eq-ref-o", eqRefOFor),
    ("eq-sym", eqSymFor), ("eq-trans", eqTransFor),
    ("eq-rep-s", eqRepSFor), ("eq-rep-p", eqRepPFor), ("eq-rep-o", eqRepOFor),
    ("prp-dom", prpDomFor), ("prp-rng", prpRngFor), ("prp-fp", prpFpFor),
    ("prp-ifp", prpIfpFor), ("prp-symp", prpSympFor), ("prp-trp", prpTrpFor),
    ("prp-spo1", prpSpo1For), ("prp-spo2", prpSpo2For),
    ("prp-eqp1", prpEqp1For), ("prp-eqp2", prpEqp2For),
    ("prp-inv1", prpInv1For), ("prp-inv2", prpInv2For), ("prp-key", prpKeyFor),
    ("cls-int1", clsInt1For), ("cls-int2", clsInt2For), ("cls-uni", clsUniFor),
    ("cls-svf1", clsSvf1For), ("cls-svf2", clsSvf2For), ("cls-avf", clsAvfFor),
    ("cls-hv1", clsHv1For), ("cls-hv2", clsHv2For), ("cls-maxc2", clsMaxc2For),
    ("cls-oo", clsOoFor),
    ("cax-sco", caxScoFor), ("cax-eqc1", caxEqc1For), ("cax-eqc2", caxEqc2For),
    ("scm-cls", scmClsFor), ("scm-sco", scmScoFor), ("scm-eqc1", scmEqc1For),
    ("scm-eqc2", scmEqc2For), ("scm-spo", scmSpoFor), ("scm-eqp1", scmEqp1For),
    ("scm-eqp2", scmEqp2For), ("scm-dom1", scmDom1For), ("scm-dom2", scmDom2For),
    ("scm-rng1", scmRng1For), ("scm-rng2", scmRng2For),
    ("scm-int", scmIntFor), ("scm-uni", scmUniFor) ]

/-- Predicate histogram of a graph: the shape the joins run over. -/
def predicateHistogram (g : Graph) : List (String × Nat) := Id.run do
  let mut acc : List (String × Nat) := []
  for t in g do
    let k := t.p.val
    match acc.find? (fun p => p.1 == k) with
    | some _ => acc := acc.map (fun p => if p.1 == k then (p.1, p.2 + 1) else p)
    | none   => acc := acc ++ [(k, 1)]
  return acc.mergeSort (fun a b => a.2 ≥ b.2)

/-- Print and flush, so a run killed by an outer timeout keeps the
lines it already measured. -/
def say (line : String) : IO Unit := do
  IO.println line
  (← IO.getStdout).flush

def profileCase (name : String) (cat : Catalog) (c : Case) (rounds : Nat) : IO Unit := do
  say s!"PROFILE {name} {c.id}"
  match premiseGraph cat c with
  | .error o => IO.println (o.line c.id)
  | .ok gp =>
    IO.println s!"  premise triples={gp.length}"
    for (p, n) in (predicateHistogram gp).take 12 do
      IO.println s!"    {n}  {p}"
    -- The results are written to an `IO.Ref` between the two clock
    -- reads: a pure `let` whose value is only used later is moved past
    -- the second `IO.monoMsNow` by the compiler (measured 2026-08-22:
    -- every row read 0 ms while the round read seconds). The ref write
    -- is an IO action that consumes the value, so it is forced there.
    let outRef ← IO.mkRef (#[] : Array Triple)
    let gRef ← IO.mkRef (#[] : Array Triple)
    let idxRef ← IO.mkRef Index.empty
    let mut g := gp
    for r in [0:rounds] do
      say s!"  round {r + 1}: input triples={g.length}"
      let tr0 ← IO.monoMsNow
      let mut all : Array Triple := #[]
      for (nm, f) in namedRows do
        let t0 ← IO.monoMsNow
        outRef.set (g.flatMap (f g)).toArray
        let t1 ← IO.monoMsNow
        let out ← outRef.get
        if t1 - t0 > 0 || out.size > 0 then
          say s!"      {nm}: emitted={out.size} ms={t1 - t0}"
        all := all ++ out
      let t2 ← IO.monoMsNow
      gRef.set (addAll g (axiomTriples ++ all.toList)).toArray
      let t3 ← IO.monoMsNow
      let g' := (← gRef.get).toList
      say s!"    list rows total: emitted={all.size} ms={t2 - tr0}"
      say s!"    list dedup addAll: new={g'.length - g.length} ms={t3 - t2}"
      -- The indexed engine on the same input: build, one round, and the
      -- identity check against the list round (RLClosureIndexed's
      -- Index.Wf.step, evaluated on corpus data). The per-row loop above
      -- groups conclusions BY ROW, so `g'` holds the same SET as
      -- `step g` in a different insertion order; the set check is what
      -- applies to it. The LIST check is against `step g` itself, which
      -- costs another list round, so it runs only on inputs small enough
      -- for that to be affordable.
      let t4 ← IO.monoMsNow
      idxRef.set (Index.ofGraph g)
      let t5 ← IO.monoMsNow
      let idx ← idxRef.get
      idxRef.set (stepI idx)
      let t6 ← IO.monoMsNow
      let idx' ← idxRef.get
      let sameSet := idx'.all.size == g'.length && g'.all (fun t => idx'.memB t)
      let sameList := if g.length ≤ 1500 then toString (decide (idx'.toGraph = step g))
                      else "not checked (input > 1500 triples)"
      say s!"    indexed build: ms={t5 - t4}  indexed round: new={idx'.all.size - idx.all.size} \
ms={t6 - t5}  same set as the list round: {sameSet}  same list as step g: {sameList}"
      if g'.length = g.length then
        say s!"    saturated after {r + 1} rounds"
        break
      g := g'

/-! ## Positive entailment by refutation (`--dl` only)

The W3C definition of a positive entailment test is model-theoretic
over ONTOLOGIES: "a premise ontology document d1 and a conclusion
ontology document d2 where Ont(d1) entails Ont(d2) with respect to the
specified semantics" (OWL 2 Conformance, test types). Under the Direct
Semantics `Ont(d1) ⊨ Ont(d2)` iff `Ont(d1) ∪ ¬Ont(d2)` is
unsatisfiable, and an unsatisfiability verdict is what the tableau
refuter already returns for the InconsistencyTest line. Triple
containment in the RL closure is a SOUND BUT INCOMPLETE approximation
of that relation: it cannot see a conclusion whose class expression is
structure inside an axiom rather than a triple the closure must hold
(sub-bucket B1 of `docs/designissues/2026-09-03-owl-failure-split.md`).

So the refutation check runs as a FALLBACK after containment fails,
never instead of it, and only under `--dl`. It is strictly additive:
no case that passes on containment can fail because of it.

Decision and the specification citations:
`docs/designissues/2026-09-04-owl-b1-class-expression-structure.md`. -/

/-- Every document is parsed on its own, so a conclusion blank node
`_:b0` and a closure blank node `_:b0` are unrelated but EQUAL as
labels. Combining them without renaming would conflate two distinct
resources and could yield a clash for the wrong reason — a false pass.
The conclusion's blank nodes are moved under a reserved prefix that no
parser produces and that `NegationGoals`'s own `__factoidal_pe_*`
labels do not collide with. -/
def peConclusionBNodePrefix : String := "__factoidal_pe_concl_"

def renameSubjectBNode (s : Subject) : Subject :=
  match s with
  | .bnode b => .bnode (peConclusionBNodePrefix ++ b)
  | other    => other

def renameTermBNode : Term → Term
  | .bnode b            => .bnode (peConclusionBNodePrefix ++ b)
  | .tripleTerm s p o   => .tripleTerm (renameSubjectBNode s) p (renameTermBNode o)
  | other               => other

def renameConclusionBNodes (g : Graph) : Graph :=
  g.map (fun t => { t with s := renameSubjectBNode t.s, o := renameTermBNode t.o })

/-- `some true` when the premise closure REFUTES the negation of every
content assertion of the conclusion — the entailment is proven. `some
false` when a goal produced a countermodel. `none` when the conclusion
has no supported negation, or a goal's budget ran out: indeterminate,
and the caller keeps its containment verdict.

The goals are ANDed because a conclusion graph is the conjunction of
its content assertions, and each is negated SEPARATELY
(`NegationGoals`'s soundness contract: assuming an unproven conjunct
while proving another is the unsound direction). -/
def refuteEntails (closure : Graph) (gc : Graph) (rb : Nat) : Option Bool :=
  match L4Factoidal.OWL.Refute.negationGoals (renameConclusionBNodes gc) with
  | none       => none
  | some goals =>
    let step (acc : Option Bool) (goal : Graph) : Option Bool :=
      match acc with
      | some true =>
        match L4Factoidal.OWL.Refute.tableauConsistent (closure ++ goal) rb with
        | some false => some true      -- this conjunct is entailed
        | some true  => some false     -- countermodel: not entailed
        | none       => none           -- budget out: indeterminate
      | other => other
    goals.foldl step (some true)

def judgePositive (cat : Catalog) (c : Case) (capMs : Nat) (dl : Bool) (rb : Nat)
    : IO (Harness.Outcome × Measure) := do
  if isFunctionalUnread c then return (.unsupported "functional-syntax", {})
  match (match c.conclusion with
         | some ctxt => parseDoc "conclusion" c.iri ctxt
         | none => match fsGraph c.fsConclusionText with
             | some g => .ok g
             | none   => .error "harness: no RDF/XML conclusion") with
    | .error e => return (.fail e, { parseFailures := 1 })
    | .ok gc0 =>
      if gc0.isEmpty then return (.fail "parser: conclusion parsed to zero triples", { parseFailures := 1 })
      let (res, m) ← premiseClosure cat c capMs dl
      match res with
      | .error o => return (o, m)
      | .ok r =>
        let gc := if isDirectOnly c then excludeAnnotationTriples gc0 else gc0
        let m := { m with triplesParsed := m.triplesParsed + gc0.length }
        match gc.find? (fun t => !inClosure r.graph t) with
        | none => return (.pass, m)
        | some t =>
          -- The containment check did not find it. Under `--dl` the
          -- conformance relation itself is tried: entailment by
          -- refutation. Only `some true` overrides; anything else
          -- leaves the containment verdict in place.
          if dl && refuteEntails r.graph gc rb == some true then
            -- Evidence line, one per fallback pass. `premise_alone` is
            -- falsification test 2 of the decision document: a premise
            -- closure that is ITSELF refuted entails everything, so a
            -- pass on such a case proves nothing about the conclusion.
            -- `premise_alone=false` is the reading that keeps the pass
            -- meaningful.
            let alone := L4Factoidal.OWL.Refute.refute r.graph rb == some false
            IO.println s!"PE-BY-REFUTATION {c.id}: premise_alone_refuted={alone} \
(closure {r.graph.length} triples)"
            return (.pass, { m with clashes := m.clashes + 1 })
          else if r.capped then
            return (.fail s!"cap: closure budget hit after {r.rounds} rounds ({r.graph.length} triples); missing {showTriple t}", m)
          else
            return (.fail s!"closure-gap: missing {showTriple t} (closure {r.graph.length} triples, {r.rounds} rounds)", m)

def judgeNegative (cat : Catalog) (c : Case) (capMs : Nat) (dl : Bool)
    : IO (Harness.Outcome × Measure) := do
  if isFunctionalUnread c then return (.unsupported "functional-syntax", {})
  match (match c.nonConclusion with
         | some ctxt => parseDoc "non-conclusion" c.iri ctxt
         | none => match fsGraph c.fsNonConclusionText with
             | some g => .ok g
             | none   => .error "harness: no RDF/XML non-conclusion") with
    | .error e => return (.fail e, { parseFailures := 1 })
    | .ok gc =>
      if gc.isEmpty then return (.fail "parser: non-conclusion parsed to zero triples", { parseFailures := 1 })
      let (res, m) ← premiseClosure cat c capMs dl
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

def judgeConsistency (cat : Catalog) (c : Case) (capMs : Nat) (dl : Bool) (rb : Nat)
    : IO (Harness.Outcome × Measure) := do
  if isFunctionalUnread c then return (.unsupported "functional-syntax", {})
  let (res, m) ← premiseClosure cat c capMs dl
  match res with
  | .error o => return (o, m)
  | .ok r =>
    let clash := detectClashI r.index
    -- Under `--dl` the refuter is consulted too. A refutation of a
    -- premise the catalog asserts CONSISTENT is a defect in the
    -- refuter, and it has to be visible as a failure — a refuter
    -- scored only on the cases it is meant to close cannot be caught
    -- fabricating a contradiction.
    let refuted := dl && L4Factoidal.OWL.Refute.refute r.graph rb == some false
    let m := { m with clashes := m.clashes + (if clash then 1 else 0) }
    if clash then return (.fail s!"clash: detectClash fired on a premise asserted consistent ({r.graph.length} triples)", m)
    else if refuted then
      return (.fail s!"clash: the tableau refuted a premise asserted consistent ({r.graph.length} triples)", m)
    else if r.capped then
      return (.fail s!"cap: absence verdict on a closure that hit the budget after {r.rounds} rounds", m)
    else return (.pass, m)

def judgeInconsistency (cat : Catalog) (c : Case) (capMs : Nat) (dl : Bool) (rb : Nat)
    : IO (Harness.Outcome × Measure) := do
  if isFunctionalUnread c then return (.unsupported "functional-syntax", {})
  if isRdfBasedOnly c then return (.skip "semantics-rdf-based-only", {})
  let (res, m) ← premiseClosure cat c capMs dl
  match res with
  | .error o => return (o, m)
  | .ok r =>
    let clash := detectClashI r.index
    let refuted := dl && L4Factoidal.OWL.Refute.refute r.graph rb == some false
    let m := { m with clashes := m.clashes + (if clash || refuted then 1 else 0) }
    if clash || refuted then return (.pass, m)
    else if r.capped then
      return (.fail s!"cap: no clash on a closure that hit the budget after {r.rounds} rounds", m)
    else return (.fail s!"closure-gap: no clash row fired on a premise asserted inconsistent ({r.graph.length} triples, {r.rounds} rounds)", m)

def testTypes : List String :=
  ["PositiveEntailmentTest", "NegativeEntailmentTest", "ConsistencyTest", "InconsistencyTest"]

def judge (cat : Catalog) (c : Case) (capMs : Nat) (dl : Bool) (rb : Nat)
    : String → IO (Harness.Outcome × Measure)
  | "PositiveEntailmentTest" => judgePositive cat c capMs dl rb
  | "NegativeEntailmentTest" => judgeNegative cat c capMs dl
  | "ConsistencyTest"        => judgeConsistency cat c capMs dl rb
  | "InconsistencyTest"      => judgeInconsistency cat c capMs dl rb
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

def runCatalog (name : String) (cat : Catalog) (capMs : Nat) (dl : Bool) (rb : Nat)
    (verbose : Bool)
    : IO CatalogResult := do
  let t0 ← IO.monoMsNow
  let mut r : CatalogResult := {}
  for c in cat.cases do
    for ty in testTypes do
      if c.types.contains ty then
        let (o, m) ← judge cat c capMs dl rb ty
        let label := s!"{c.id} [{ty}]"
        -- A cap hit is named even when the unit still scored (a
        -- conclusion found before the budget, a clash on a truncated
        -- closure): the diagnostics count alone does not say WHICH case.
        if m.capHits > 0 then
          IO.println s!"CAP {label}: budget hit after {m.closureRounds} rounds \
(premise {m.triplesParsed} triples)"
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
  /-- `--profile`: per-row timing of the list engine on `--case` ids. -/
  profile : Bool := false
  cases   : List String := []
  rounds  : Nat := 3
  /-- `--indexed-only`: profile rounds of the indexed engine alone
  (no list-engine rows), for inputs the list engine cannot finish. -/
  indexedOnly : Bool := false
  /-- `--dl`: run one class-expression materialisation pass
  (`L4Factoidal.OWL.Mat.materialise`) between two closures, instead
  of the RL closure alone. Kept a FLAG rather than made the default
  so both numbers can be measured from the same binary and the
  difference attributed to the pass. -/
  dl : Bool := false
  /-- `--refute-budget N`: the refuter's per-premise budget. -/
  refuteBudget : Nat := defaultRefuteBudget

def parseArgs : List String → Opts → Opts
  | [], o => o
  | "--cap-ms" :: n :: rest, o => parseArgs rest { o with capMs := n.toNat!.max 1 }
  | "-v" :: rest, o => parseArgs rest { o with verbose := true }
  | "--dir" :: d :: rest, o => parseArgs rest { o with dir := d }
  | "--profile" :: rest, o => parseArgs rest { o with profile := true }
  | "--case" :: c :: rest, o => parseArgs rest { o with cases := o.cases ++ [c] }
  | "--rounds" :: n :: rest, o => parseArgs rest { o with rounds := n.toNat!.max 1 }
  | "--indexed-only" :: rest, o => parseArgs rest { o with indexedOnly := true }
  | "--dl" :: rest, o => parseArgs rest { o with dl := true }
  | "--refute-budget" :: n :: rest, o =>
      parseArgs rest { o with refuteBudget := n.toNat!.max 1 }
  | a :: rest, o =>
      if a.endsWith ".rdf" then parseArgs rest { o with only := o.only ++ [a] }
      else parseArgs rest { o with dir := a }

/-- The store-parameterised rows of `RLClosureIndexed.conclusionsListS`,
named, in that list's order. -/
def namedRowsS : List (String × (Store → Triple → List Triple)) :=
  [ ("eq-ref-s", eqRefSForS), ("eq-ref-p", eqRefPForS), ("eq-ref-o", eqRefOForS),
    ("eq-sym", eqSymForS), ("eq-trans", eqTransForS),
    ("eq-rep-s", eqRepSForS), ("eq-rep-p", eqRepPForS), ("eq-rep-o", eqRepOForS),
    ("prp-dom", prpDomForS), ("prp-rng", prpRngForS), ("prp-fp", prpFpForS),
    ("prp-ifp", prpIfpForS), ("prp-symp", prpSympForS), ("prp-trp", prpTrpForS),
    ("prp-spo1", prpSpo1ForS), ("prp-spo2", prpSpo2ForS),
    ("prp-eqp1", prpEqp1ForS), ("prp-eqp2", prpEqp2ForS),
    ("prp-inv1", prpInv1ForS), ("prp-inv2", prpInv2ForS), ("prp-key", prpKeyForS),
    ("cls-int1", clsInt1ForS), ("cls-int2", clsInt2ForS), ("cls-uni", clsUniForS),
    ("cls-svf1", clsSvf1ForS), ("cls-svf2", clsSvf2ForS), ("cls-avf", clsAvfForS),
    ("cls-hv1", clsHv1ForS), ("cls-hv2", clsHv2ForS), ("cls-maxc2", clsMaxc2ForS),
    ("cls-oo", clsOoForS),
    ("cax-sco", caxScoForS), ("cax-eqc1", caxEqc1ForS), ("cax-eqc2", caxEqc2ForS),
    ("scm-cls", scmClsForS), ("scm-sco", scmScoForS), ("scm-eqc1", scmEqc1ForS),
    ("scm-eqc2", scmEqc2ForS), ("scm-spo", scmSpoForS), ("scm-eqp1", scmEqp1ForS),
    ("scm-eqp2", scmEqp2ForS), ("scm-dom1", scmDom1ForS), ("scm-dom2", scmDom2ForS),
    ("scm-rng1", scmRng1ForS), ("scm-rng2", scmRng2ForS),
    ("scm-int", scmIntForS), ("scm-uni", scmUniForS) ]

/-- `--profile --indexed-only`: rounds of the indexed engine alone,
timed, with the size after each round, the per-row emitted counts and
times over the round's input, and the `owl:sameAs` / `rdf:type`
population of the store after the round. -/
def profileIndexed (name : String) (cat : Catalog) (c : Case) (rounds : Nat) : IO Unit := do
  say s!"PROFILE-INDEXED {name} {c.id}"
  match premiseGraph cat c with
  | .error o => say (o.line c.id)
  | .ok gp =>
    say s!"  premise triples={gp.length}"
    let idxRef ← IO.mkRef Index.empty
    let t0 ← IO.monoMsNow
    idxRef.set (Index.ofGraph gp)
    let t1 ← IO.monoMsNow
    say s!"  index build: ms={t1 - t0}"
    let mut idx ← idxRef.get
    let mut total := t1 - t0
    let outRef ← IO.mkRef (#[] : Array Triple)
    for r in [0:rounds] do
      let st := Store.ofIndex idx
      for (nm, f) in namedRowsS do
        let ra ← IO.monoMsNow
        outRef.set (st.graph.flatMap (f st)).toArray
        let rb ← IO.monoMsNow
        let out ← outRef.get
        if rb - ra > 0 || out.size > 0 then
          say s!"      {nm}: emitted={out.size} ms={rb - ra}"
      let ta ← IO.monoMsNow
      idxRef.set (stepI idx)
      let tb ← IO.monoMsNow
      let idx' ← idxRef.get
      total := total + (tb - ta)
      say s!"  round {r + 1}: input={idx.all.size} new={idx'.all.size - idx.all.size} ms={tb - ta} \
cumulative_ms={total} sameAs={(idx'.withPred owlSameAs).length} rdfType={(idx'.withPred rdfType).length}"
      if idx'.all.size = idx.all.size then
        say s!"  saturated after {r + 1} rounds, {idx'.all.size} triples, cumulative_ms={total}"
        break
      idx := idx'

/-- `--profile` entry: only the named cases, only the timing. -/
def profileMain (o : Opts) : IO UInt32 := do
  let dir : System.FilePath := o.dir
  let names := if o.only.isEmpty then catalogs else o.only
  for name in names do
    let p := dir / name
    if !(← p.pathExists) then
      IO.println s!"  MISSING {name}"
    else
      match ← readCatalog p with
      | none => pure ()
      | some cat =>
        for c in cat.cases do
          if o.cases.contains c.id then
            if o.indexedOnly then profileIndexed name cat c o.rounds
            else profileCase name cat c o.rounds
  return 0

def main (args : List String) : IO UInt32 := do
  let o := parseArgs args {}
  let dir : System.FilePath := o.dir
  IO.println "Lean OWL 2 RL/RDF probe — corpus census + closure run"
  IO.println s!"corpus dir: {dir}  closure fuel: {closureFuel}  per-closure cap: {o.capMs} ms"
  IO.println (if o.dl then
    s!"regime: RL closure + class-expression materialisation + tableau refuter \
(--dl), refuter budget {o.refuteBudget}"
  else "regime: RL closure only")
  let (scoOk, unrelatedAbsent) := engineSelfCheck
  IO.println s!"engine self-check: cax-sco fires = {scoOk}, \
unrelated triple absent = {!unrelatedAbsent}"
  if o.profile then return (← profileMain o)
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
        let r ← runCatalog name cat o.capMs o.dl o.refuteBudget o.verbose
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
