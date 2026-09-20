/-
L4Factoidal.Syntax.TurtleProvenance — where each emitted triple came from.

The Turtle reference parser (`Syntax.Turtle`) turns a document into a
`Graph`, a set of triples, and in doing so forgets which statement each
triple was read from and where in the document that statement sat. This
module keeps that information without touching the parser:

* `parseStatementsFoldProv` is `parseStatementsFold` with one more
  argument to the step: the `StatementSpan` of the statement just read
  (its 0-based ordinal and its character span). Forgetting the span
  gives back `parseStatementsFold` exactly (`parseStatementsFoldProv_forget`).
* `parseTurtleProv` returns every triple paired with a
  `TripleProvenance` (span plus the triple's ordinal within its
  statement), in document order. Projecting the triples out gives back
  `parseTurtle` exactly (`parseTurtleProv_triples`), so the annotated
  parse is the reference parse plus data, never a second parser.
* `reifyProvenance` materialises the annotations as RDF 1.2 reifiers,
  `_:r rdf:reifies <<( s p o )>>` plus one triple per provenance field,
  so downstream tools that speak RDF can attach parsing or validation
  facts to a triple by its reifier. The reifier labels contain `/`,
  which no Turtle blank node label can (`BLANK_NODE_LABEL` draws on
  `PN_CHARS`, which has no `/`), and the parser's own generated labels
  are `anon` followed by underscores (`freshBnodePrefixOfLongest`), so
  the three label populations are disjoint by construction.

Positions are character offsets into the decoded document, the same
`pos` the parser reports in a `ParseError`. `endPos` is the offset just
after the statement's terminating `.`; for a statement that ends at a
TriG `}` it is the offset of that brace.

Design record: `docs/designissues/2026-09-20-triple-provenance.md`.
-/

import L4Factoidal.Syntax.Turtle
import L4Factoidal.Syntax.TurtleTheorems

namespace L4Factoidal.Syntax

open L4Factoidal.RDF

/-! ## Provenance records -/

/-- The source span of one completed Turtle statement. -/
structure StatementSpan where
  /-- 0-based ordinal of the statement among the document's statements,
  directives included (a `@prefix` line is a statement that yields no
  triples). -/
  index    : Nat
  /-- Character offset of the statement's first character, after leading
  whitespace and comments. -/
  startPos : Nat
  /-- Character offset just past the statement (see the module header). -/
  endPos   : Nat
  deriving DecidableEq, Repr

/-- Where one emitted triple came from. -/
structure TripleProvenance where
  span    : StatementSpan
  /-- 0-based position of the triple among the triples the statement
  emitted, in emission order: a `predicateObjectList`, a collection or an
  RDF 1.2 annotation block yields several triples from one statement. -/
  ordinal : Nat
  deriving DecidableEq, Repr

/-! ## The annotated fold -/

/-- `parseStatementsFold` with the statement's span handed to the step.
`idx` is the ordinal of the next statement. Same grammar, state, fuel and
error behaviour as `parseStatementsFold`; only the step's signature differs. -/
def parseStatementsFoldProv (step : α → StatementSpan → List Triple → α) :
    Nat → Nat → TurtleState → Nat → List Char → α → Except ParseError (α × TurtleState)
  | 0,        _,   st, _,   _,  acc => .ok (acc, st)
  | fuel + 1, idx, st, pos, cs, acc =>
      let (p1, r1) := tws pos cs
      match r1 with
      | [] => .ok (acc, st)
      | _ =>
          match readStatement fuel st p1 r1 with
          | .error e => .error e
          | .ok (ts, st', p2, r2) =>
              let nextAcc := step acc ⟨idx, p1, p2⟩ ts
              if p2 ≤ p1 then .ok (nextAcc, st')
              else parseStatementsFoldProv step fuel (idx + 1) st' p2 r2 nextAcc

/-- Document-level form of `parseStatementsFoldProv`; mirrors `parseTurtleFold`. -/
def parseTurtleFoldProv (step : α → StatementSpan → List Triple → α) (init : α) (text : String)
    (base : Option String := none) (mode : Mode := .rdf11) : Except ParseError α :=
  let cs := text.toList
  match parseStatementsFoldProv step (cs.length + 2) 0 (TurtleState.initChars cs base mode) 0 cs init with
  | .error e => .error e
  | .ok (acc, _) => .ok acc

/-- A step that ignores the span is the plain fold. -/
theorem parseStatementsFoldProv_forget (step : α → List Triple → α) :
    ∀ (fuel idx : Nat) (st : TurtleState) (pos : Nat) (cs : List Char) (acc : α),
      parseStatementsFoldProv (fun a _ ts => step a ts) fuel idx st pos cs acc
        = parseStatementsFold step fuel st pos cs acc := by
  intro fuel
  induction fuel with
  | zero => intro idx st pos cs acc; rfl
  | succ fuel ih =>
      intro idx st pos cs acc
      simp only [parseStatementsFoldProv, parseStatementsFold]
      cases hr : (tws pos cs).2 with
      | nil => rfl
      | cons c rest =>
          cases hs : readStatement fuel st (tws pos cs).1 (c :: rest) with
          | error e => rfl
          | ok v =>
              obtain ⟨ts, st', p2, r2⟩ := v
              by_cases hp : p2 ≤ (tws pos cs).1
              · simp [hp]
              · simp only [hp, if_false]
                exact ih (idx + 1) st' p2 r2 (step acc ts)

theorem parseTurtleFoldProv_forget (step : α → List Triple → α) (init : α) (text : String)
    (base : Option String) (mode : Mode) :
    parseTurtleFoldProv (fun a _ ts => step a ts) init text base mode
      = parseTurtleFold step init text base mode := by
  simp only [parseTurtleFoldProv, parseTurtleFold]
  rw [parseStatementsFoldProv_forget]
  cases parseStatementsFold step (text.toList.length + 2)
      (TurtleState.initChars text.toList base mode) 0 text.toList init <;> rfl

/-! ## Annotated parsing -/

/-- Number the triples of one statement from `n`. -/
def annotate (span : StatementSpan) : Nat → List Triple → List (Triple × TripleProvenance)
  | _, []      => []
  | n, t :: ts => (t, ⟨span, n⟩) :: annotate span (n + 1) ts

theorem annotate_map_fst (span : StatementSpan) :
    ∀ (n : Nat) (ts : List Triple), (annotate span n ts).map Prod.fst = ts := by
  intro n ts
  induction ts generalizing n with
  | nil => rfl
  | cons t ts ih => simp [annotate, ih]

/-- The reversing step for annotated triples, the analogue of `prependReverse`. -/
def prependReverseProv (accRev : List (Triple × TripleProvenance)) (span : StatementSpan)
    (ts : List Triple) : List (Triple × TripleProvenance) :=
  (annotate span 0 ts).reverse ++ accRev

/-- Parse a Turtle document into its triples paired with their provenance,
in document order. Fails exactly when `parseTurtle` fails, with the same
error. -/
def parseTurtleProv (text : String) (base : Option String := none) (mode : Mode := .rdf11) :
    Except ParseError (List (Triple × TripleProvenance)) :=
  (parseTurtleFoldProv prependReverseProv [] text base mode).map List.reverse

/-- Projecting the provenance away from the annotated fold is the packer's
plain fold: the invariant that carries `parseTurtleProv_triples`. -/
theorem parseStatementsFoldProv_map_fst :
    ∀ (fuel idx : Nat) (st : TurtleState) (pos : Nat) (cs : List Char)
      (acc : List (Triple × TripleProvenance)),
      (parseStatementsFoldProv prependReverseProv fuel idx st pos cs acc).map
          (fun r => (r.1.map Prod.fst, r.2))
        = parseStatementsFold prependReverse fuel st pos cs (acc.map Prod.fst) := by
  intro fuel
  induction fuel with
  | zero => intro idx st pos cs acc; rfl
  | succ fuel ih =>
      intro idx st pos cs acc
      simp only [parseStatementsFoldProv, parseStatementsFold]
      cases hr : (tws pos cs).2 with
      | nil => simp [Except.map]
      | cons c rest =>
          cases hs : readStatement fuel st (tws pos cs).1 (c :: rest) with
          | error e => simp [Except.map]
          | ok v =>
              obtain ⟨ts, st', p2, r2⟩ := v
              by_cases hp : p2 ≤ (tws pos cs).1
              · simp [hp, Except.map, prependReverseProv, prependReverse, annotate_map_fst]
              · simp only [hp, if_false]
                rw [ih]
                simp [prependReverseProv, prependReverse, annotate_map_fst]

/-- The annotated parse is the reference parse plus data. -/
theorem parseTurtleProv_triples (text : String) (base : Option String) (mode : Mode) :
    (parseTurtleProv text base mode).map (List.map Prod.fst) = parseTurtle text base mode := by
  rw [parseTurtle_eq_fold]
  simp only [parseTurtleProv, parseTurtleFoldProv, parseTurtleFold]
  have h := parseStatementsFoldProv_map_fst (text.toList.length + 2) 0
    (TurtleState.initChars text.toList base mode) 0 text.toList []
  simp only [List.map_nil] at h
  cases hp : parseStatementsFoldProv prependReverseProv (text.toList.length + 2) 0
      (TurtleState.initChars text.toList base mode) 0 text.toList [] with
  | error e =>
      rw [hp] at h
      cases hq : parseStatementsFold prependReverse (text.toList.length + 2)
          (TurtleState.initChars text.toList base mode) 0 text.toList [] with
      | error e' => rw [hq] at h; simp [Except.map] at h; subst h; rfl
      | ok v => rw [hq] at h; simp [Except.map] at h
  | ok v =>
      rw [hp] at h
      cases hq : parseStatementsFold prependReverse (text.toList.length + 2)
          (TurtleState.initChars text.toList base mode) 0 text.toList [] with
      | error e' => rw [hq] at h; simp [Except.map] at h
      | ok w =>
          rw [hq] at h
          simp only [Except.map, Except.ok.injEq] at h
          simp [Except.map, ← h, List.map_reverse]

/-! ## Materialisation as RDF 1.2 reifiers -/

/-- Vocabulary for the provenance fields. The namespace is a placeholder
until the project settles one; every use goes through these constants. -/
def provNs : String := "https://factoidal.example/ns/provenance#"
def provSource    : WfIri := ⟨provNs ++ "source", rfl⟩
def provStatement : WfIri := ⟨provNs ++ "statement", rfl⟩
def provOrdinal   : WfIri := ⟨provNs ++ "ordinal", rfl⟩
def provStart     : WfIri := ⟨provNs ++ "start", rfl⟩
def provEnd       : WfIri := ⟨provNs ++ "end", rfl⟩

/-- An `xsd:integer` literal. -/
def Literal.natural (n : Nat) : WfLiteral :=
  ⟨{ lexicalForm := toString n, datatype := xsdInteger, langTag := none, direction := none }, rfl⟩

/-- The default reifier label for a provenance record: `prov/<statement>/<ordinal>`.
Contains `/`, so it is disjoint from every document label and every
parser-generated label (module header). -/
def defaultReifierLabel (p : TripleProvenance) : BNodeId :=
  s!"prov/{p.span.index}/{p.ordinal}"

/-- The six triples that describe one annotated triple: the reifier's
`rdf:reifies` link to the triple term, then source, statement, ordinal,
start and end. -/
def reifyOne (source : String) (label : TripleProvenance → BNodeId)
    (tp : Triple × TripleProvenance) : List Triple :=
  let (t, p) := tp
  let r : Subject := .bnode (label p)
  [ ⟨r, rdfReifies,    .tripleTerm t.s t.p t.o⟩,
    ⟨r, provSource,    .literal (Literal.string source)⟩,
    ⟨r, provStatement, .literal (Literal.natural p.span.index)⟩,
    ⟨r, provOrdinal,   .literal (Literal.natural p.ordinal)⟩,
    ⟨r, provStart,     .literal (Literal.natural p.span.startPos)⟩,
    ⟨r, provEnd,       .literal (Literal.natural p.span.endPos)⟩ ]

/-- Materialise provenance as a graph of RDF 1.2 reifiers. `source` names
the document (an IRI or any label the caller chooses). The result does
not repeat the annotated triples themselves; append it to the parsed graph
when both are wanted. -/
def reifyProvenance (source : String) (annotated : List (Triple × TripleProvenance))
    (label : TripleProvenance → BNodeId := defaultReifierLabel) : Graph :=
  annotated.flatMap (reifyOne source label)

theorem reifyOne_length (source : String) (label : TripleProvenance → BNodeId)
    (tp : Triple × TripleProvenance) : (reifyOne source label tp).length = 6 := by
  obtain ⟨t, p⟩ := tp; rfl

theorem reifyProvenance_length (source : String) (annotated : List (Triple × TripleProvenance))
    (label : TripleProvenance → BNodeId) :
    (reifyProvenance source annotated label).length = 6 * annotated.length := by
  induction annotated with
  | nil => rfl
  | cons tp rest ih =>
      simp [reifyProvenance, List.flatMap_cons, reifyOne_length] at *
      omega

/-! ## Axiom audit -/

#print axioms parseStatementsFoldProv_forget
#print axioms parseTurtleFoldProv_forget
#print axioms parseStatementsFoldProv_map_fst
#print axioms parseTurtleProv_triples
#print axioms reifyProvenance_length

end L4Factoidal.Syntax
