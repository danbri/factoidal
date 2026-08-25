/-
L4Factoidal.RIF.Translation — RIF Core to SPARQL algebra.

Port of `formal/fstar/RIF.Core.Translation.fst` (593 lines).

The RIF/RDF/OWL combination spec (W3C, §5) fixes the desugaring:

    o[p -> v]     ⇒  (o, p, v)
    o # c         ⇒  (o, rdf:type, c)
    sub ## sup    ⇒  (sub, rdfs:subClassOf, sup)

so a RIF condition becomes a basic graph pattern and a rule head becomes
a CONSTRUCT template. That is what this module computes.

## Why the Lean tree gains a SECOND route to the same answers

The F\* tree answers RIF by translating to SPARQL and running the SPARQL
engine. The Lean tree already answers it by direct forward chaining
(`RIF.Engine`). Porting the translation therefore does not replace
anything — it gives the tree an INDEPENDENT second route, and the
build-time checks at the bottom use that: they run the same program
through both and compare the answers. Two implementations that agree is
evidence neither has; agreement between them is worth having.

## Partiality is surfaced, never silent

A literal cannot be the subject of a triple pattern. For the RDF-shaped
atoms (frame, member, sub) a literal in subject position is genuinely
ill-typed and stays a hard `none`. For the positional atom's own
internal encoding it is not — see below.

## The positional-atom encoding, and what it is for

A binary positional atom `p(s, o)` maps straight to `(s, p, o)`. Arity 0
and 1 have no subject-object pair to draw on and arity ≥ 3 has no triple
at all, so those are encoded:

    p()            ⇒  (urn:rif-nullary:subject, p, "true"^^xsd:boolean)
    p(a)           ⇒  (urn:rif-nullary:subject, p, a)
    p(a₁ … aₙ)     ⇒  (anchor, p, "true"^^xsd:boolean)
                      (anchor, urn:rif-uniterm:argᵢ, aᵢ)   for each i

This is INTERNAL bookkeeping. It is never handed to an external RDF
semantics check; it exists so that the assertion side and the query side
agree, and both sides use these same functions.

The arity-1 argument goes in OBJECT position, not subject. That matters
in a rule body: `ex:a(?x)` must bind `?x` to the real value, and object
position has no literal restriction, so a literal argument needs no
encoding at all.

The anchors are deterministic FUNCTIONS OF THE VALUE, which is what
makes the encoding correct rather than merely convenient: the same fact
always reaches the same anchor, and distinct facts reach distinct ones.
A literal lexical form containing the joiner could in principle collide
two argument lists; a collision only ever MERGES two facts' anchors, and
the F\* source accepts the same bound for the same reason.
-/
import L4Factoidal.RIF.Syntax
import L4Factoidal.RIF.Engine
import L4Factoidal.SPARQL.Algebra
import L4Factoidal.RDFS.Vocabulary

namespace L4Factoidal.RIF

open L4Factoidal.RDF
open L4Factoidal.SPARQL

/-! ## Constants -/

def uniterCommaMarkerLex : String := "true"

/-- The `"true"^^xsd:boolean` object an arity-0 or arity-≥3 encoding
carries. -/
def unitermTrueMarker : Term :=
  .literal ⟨{ lexicalForm := "true", datatype := xsdBoolean,
              langTag := none, direction := none }, rfl⟩

def unitermNullarySubject : WfIri := ⟨"urn:rif-nullary:subject", by decide⟩

/-- `urn:rif-uniterm:arg<i>`. The digits of a `Nat` always make this a
valid URN, so the fallback is unreachable; it keeps the function total
without a per-`i` proof. -/
def unitermArgPred (i : Nat) : WfIri :=
  let s := "urn:rif-uniterm:arg" ++ toString i
  if h : isIri s then ⟨s, h⟩ else unitermNullarySubject

def unitermSubjectAnchorVar (v : String) : String := "$$uniterm-subj$" ++ v

/-- The anchor variable for one atom OCCURRENCE, indexed by its position
in the body, so two distinct occurrences never share an anchor. -/
def unitermAnchorVar (idx : Nat) : String := "$$uniterm-anchor$" ++ toString idx

/-! ## Terms

The Lean RIF syntax writes a constant as a lexical form plus a SYMBOL
SPACE; `rif:iri` is the IRI space and anything else is a datatype. -/

/-- The RDF term a ground constant denotes. -/
def termOfConst (lex space : String) : Term :=
  if space == iriSpace then
    if h : isIri lex then .iri ⟨lex, h⟩
    else .literal (Literal.string lex)
  else if h : isIri space then
    let l : Literal := { lexicalForm := lex, datatype := ⟨space, h⟩,
                         langTag := none, direction := none }
    if hw : literalWf l then .literal ⟨l, hw⟩ else .literal (Literal.string lex)
  else .literal (Literal.string lex)

/-- A term in PREDICATE or OBJECT position. Lists and function
applications have no pattern form. -/
def patternTermOfTm : Tm → Option PatternTerm
  | .var v => some (.var v)
  | .const lex space =>
      match termOfConst lex space with
      | .iri i => some (.iri i)
      | .literal l => some (.literal l)
      | _ => none
  | _ => none

/-- A term in SUBJECT position, strictly: a literal is ill-typed. Used
by the three RDF-shaped atoms. -/
def patternSubjectOfTm : Tm → Option PatternSubject
  | .var v => some (.var v)
  | .const lex space =>
      match termOfConst lex space with
      | .iri i => some (.iri i)
      | _ => none
  | _ => none

/-- A literal's deterministic blank-node label, keyed on its datatype,
language tag and lexical form — so equal values reach the same label on
both the assertion side and the query side. -/
def literalSubjectBnodeLabel (l : Literal) : BNodeId :=
  "rif-litsubj:" ++ l.datatype.val ++ ":" ++ (l.langTag.getD "") ++ ":" ++ l.lexicalForm

/-- A term in the positional atom's own SUBJECT slot. Unlike the strict
version, a literal is allowed here and maps to its deterministic blank
node — this slot is internal bookkeeping, not an RDF subject. -/
def unitermSubjectOfTm : Tm → Option PatternSubject
  | .var v => some (.var v)
  | .const lex space =>
      match termOfConst lex space with
      | .iri i => some (.iri i)
      | .literal l => some (.bnode (literalSubjectBnodeLabel l.val))
      | _ => none
  | _ => none

/-! ## Anchors for an arity-≥3 fact -/

def termAnchorFragment : Term → String
  | .iri i => "i:" ++ i.val
  | .bnode b => "b:" ++ b
  | .literal l => "l:" ++ l.val.datatype.val ++ ":" ++ (l.val.langTag.getD "")
                    ++ ":" ++ l.val.lexicalForm
  | .tripleTerm _ p o => "t:" ++ p.val ++ ":" ++ termAnchorFragment o

def naryFactAnchorLabel (p : WfIri) (args : List Term) : BNodeId :=
  "rif-uniterm-fact:" ++ p.val ++ "|" ++
  String.intercalate "|" (args.map termAnchorFragment)

/-! ## Atoms

Each RDF-shaped atom is exactly one triple pattern. A positional atom of
arity 2 is one as well; the other arities go through the encoding. -/

/-- The predicate IRI of a positional atom, when it has one. A
`rif:local`-scoped constant cannot be an RDF predicate. -/
def posPredIri (fn space : String) : Option WfIri :=
  if space == iriSpace then (if h : isIri fn then some ⟨fn, h⟩ else none) else none

def translateAtom : Atom → Option TriplePattern
  | .frame o p v => do
      let s ← patternSubjectOfTm o
      let pp ← patternTermOfTm p
      let vv ← patternTermOfTm v
      some { s := s, p := pp, o := vv }
  | .member o c => do
      let s ← patternSubjectOfTm o
      let cc ← patternTermOfTm c
      some { s := s, p := .iri RDFS.rdfType, o := cc }
  | .sub c d => do
      let s ← patternSubjectOfTm c
      let dd ← patternTermOfTm d
      some { s := s, p := .iri RDFS.rdfsSubClassOf, o := dd }
  | .pos fn space args => do
      let pi ← posPredIri fn space
      match args with
      | [] => some { s := .iri unitermNullarySubject, p := .iri pi,
                     o := .literal ⟨{ lexicalForm := "true", datatype := xsdBoolean,
                                      langTag := none, direction := none }, rfl⟩ }
      -- The single argument goes in OBJECT position, using the SAME
      -- fixed subject arity 0 uses. In a rule body the variable must
      -- bind to the genuine value, and object position has no literal
      -- restriction.
      | [a] => do
          let ao ← patternTermOfTm a
          some { s := .iri unitermNullarySubject, p := .iri pi, o := ao }
      | [a, b] => do
          let s ← unitermSubjectOfTm a
          let bo ← patternTermOfTm b
          some { s := s, p := .iri pi, o := bo }
      -- arity ≥ 3 has no single triple: `translateAtomBgp` reifies it.
      | _ => none
  -- `equal` and an external predicate are conditions, not graph
  -- patterns; they are what `splitFormula` separates out.
  | .equal _ _ => none
  | .externalPred _ _ => none

/-! ## Atoms as basic graph patterns

Two atoms need more than one pattern: an arity-2 positional atom whose
FIRST argument is a variable, and any atom of arity ≥ 3. -/

/-- One `(?anchor, urn:rif-uniterm:argᵢ, aᵢ)` pattern per argument. -/
def naryArgPatterns (anchor : String) : List Tm → Nat → Option Bgp
  | [], _ => some []
  | a :: rest, i => do
      let ao ← patternTermOfTm a
      let more ← naryArgPatterns anchor rest (i + 1)
      some ({ s := .var anchor, p := .iri (unitermArgPred i), o := ao } :: more)

def translateAtomBgp (idx : Nat) (a : Atom) : Option Bgp :=
  match a with
  -- A VARIABLE first argument of an arity-2 positional atom joins
  -- through the argument-value satellite, so the variable binds the
  -- genuine value rather than the bookkeeping subject encoding.
  | .pos fn space [.var v, o] => do
      let pi ← posPredIri fn space
      let oo ← patternTermOfTm o
      let anchor := unitermSubjectAnchorVar v
      some [ { s := .var anchor, p := .iri pi, o := oo },
             { s := .var anchor, p := .iri (unitermArgPred 1), o := .var v } ]
  | .pos fn space args =>
      if args.length ≥ 3 then do
        let pi ← posPredIri fn space
        let anchor := unitermAnchorVar idx
        let sats ← naryArgPatterns anchor args 1
        some ({ s := .var anchor, p := .iri pi,
                o := .literal ⟨{ lexicalForm := "true", datatype := xsdBoolean,
                                 langTag := none, direction := none }, rfl⟩ } :: sats)
      else (translateAtom a).map (fun tp => [tp])
  | _ => (translateAtom a).map (fun tp => [tp])

def translateAtomsBgpIdx : List Atom → Nat → Option Bgp
  | [], _ => some []
  | a :: rest, idx => do
      let tps ← translateAtomBgp idx a
      let more ← translateAtomsBgpIdx rest (idx + 1)
      some (tps ++ more)

def translateAtomsBgp (atoms : List Atom) : Option Bgp := translateAtomsBgpIdx atoms 0

/-! ## Conditions

A conjunction flattens into one basic graph pattern. A failure in any
conjunct rejects the whole condition rather than dropping it — a body
that silently loses a conjunct matches too much. -/

def collectAtoms : Formula → Option (List Atom)
  | .atom a => some [a]
  | .and fs => fs.foldr (fun f acc => do
      let xs ← collectAtoms f
      let rest ← acc
      some (xs ++ rest)) (some [])
  -- Disjunction has no basic-graph-pattern form, and an existential's
  -- variables are already the pattern's own free variables in SPARQL,
  -- so it would need a scope this translation does not model.
  | .or _ => none
  | .exists _ _ => none

def translateBody (f : Formula) : Option Bgp := do
  let atoms ← collectAtoms f
  translateAtomsBgp atoms

/-! ## Ground triples and graphs

A combination test whose CONCLUSION is an RDF graph holds when each of
its triples holds, blank nodes read existentially. The embedding of a
ground triple as a pattern is one to one. -/

def tripleToPattern (t : Triple) : TriplePattern :=
  { s := match t.s with
         | .iri i => .iri i
         | .bnode b => .bnode b
  , p := .iri t.p
  , o := match t.o with
         | .iri i => .iri i
         | .bnode b => .bnode b
         | .literal l => .literal l
         -- RIF Core facts carry no triple terms; a marked sentinel
         -- keeps the conversion total rather than partial for a case
         -- that cannot arise.
         | .tripleTerm _ _ _ => .bnode "rif_triple_term_unsupported" }

def graphToBgp (g : Graph) : Bgp := g.map tripleToPattern

/-! ## Rules and programs -/

def translateHead (a : Atom) : Option (List TriplePattern) :=
  (translateAtom a).map (fun tp => [tp])

/-- A rule becomes a CONSTRUCT template paired with a body pattern: the
body supplies bindings, the head instantiates the inferred triple. A
FACT — a rule with no body — pairs with the empty pattern. -/
def translateRule (r : Rule) : Option (List TriplePattern × Bgp) := do
  let hd ← translateHead r.head
  match r.body with
  | none => some (hd, [])
  | some b => do
      let bgp ← translateBody b
      some (hd, bgp)

/-- Every rule that translates. A failure in one rule does not cascade;
`translateProgramDiag` reports which ones failed. -/
def translateProgram (rs : List Rule) : List (List TriplePattern × Bgp) :=
  rs.filterMap translateRule

/-- The successful pairs, and the zero-based indices of the rules that
failed — so a caller can say WHICH rule is malformed instead of
silently dropping it. -/
def translateProgramDiag (rs : List Rule) :
    List (List TriplePattern × Bgp) × List Nat :=
  let step := rs.zipIdx.foldl (fun (acc : List (List TriplePattern × Bgp) × List Nat) (ri) =>
    match translateRule ri.1 with
    | some pr => (acc.1 ++ [pr], acc.2)
    | none => (acc.1, acc.2 ++ [ri.2])) ([], [])
  step

/-! ## Build-time checks -/

section Checks

private def ex (s : String) : String := "http://e.org/" ++ s
private def iriW (s : String) : WfIri :=
  if h : isIri s then ⟨s, h⟩ else ⟨"http://e.org/", by decide⟩

private def cIri (s : String) : Tm := .const (ex s) iriSpace
private def cInt (n : String) : Tm := .const n (xsdNs ++ "integer")

/-! ### The three RDF-shaped atoms desugar as the combination spec says -/

#guard match translateAtom (.frame (cIri "a") (cIri "p") (cIri "b")) with
       | some tp => (match tp.p with | .iri _ => true | _ => false)
       | none => false
#guard match translateAtom (.member (cIri "a") (cIri "C")) with
       | some tp => tp.p == .iri RDFS.rdfType
       | none => false
#guard match translateAtom (.sub (cIri "C") (cIri "D")) with
       | some tp => tp.p == .iri RDFS.rdfsSubClassOf
       | none => false

/-! ### A literal SUBJECT is rejected in the RDF-shaped atoms

This is the partiality the module exists to surface, and it must stay
hard: a silently dropped atom would make a body match too much. -/

#guard (translateAtom (.frame (cInt "1") (cIri "p") (cIri "b"))).isNone
#guard (translateAtom (.member (cInt "1") (cIri "C"))).isNone
#guard (translateAtom (.sub (cInt "1") (cIri "D"))).isNone

/-! ### The positional encoding, arity by arity -/

#guard match translateAtom (.pos (ex "p") iriSpace []) with
       | some tp => tp.s == .iri unitermNullarySubject && tp.o == .literal
           ⟨{ lexicalForm := "true", datatype := xsdBoolean,
              langTag := none, direction := none }, rfl⟩
       | none => false

/-! Arity 1 puts the argument in OBJECT position, which is what lets a
variable bind the genuine value — including a LITERAL argument, with no
encoding at all. -/

#guard match translateAtom (.pos (ex "gold") iriSpace [cInt "3"]) with
       | some tp => tp.s == .iri unitermNullarySubject &&
                    (match tp.o with | .literal _ => true | _ => false)
       | none => false
#guard match translateAtom (.pos (ex "a") iriSpace [.var "x"]) with
       | some tp => tp.o == .var "x"
       | none => false

/-! Arity 2 is the direct triple, and a LITERAL first argument takes the
deterministic blank node rather than being rejected — this slot is
bookkeeping, not an RDF subject. -/

#guard match translateAtom (.pos (ex "factorial") iriSpace [cInt "6", cInt "720"]) with
       | some tp => (match tp.s with | .bnode _ => true | _ => false)
       | none => false

/-! The blank node is a function of the VALUE, so equal values reach the
same label and different ones do not. That is what makes the assertion
side and the query side agree. -/

#guard unitermSubjectOfTm (cInt "6") == unitermSubjectOfTm (cInt "6")
#guard unitermSubjectOfTm (cInt "6") != unitermSubjectOfTm (cInt "7")
#guard unitermSubjectOfTm (.const "6" (xsdNs ++ "integer"))
         != unitermSubjectOfTm (.const "6" (xsdNs ++ "string"))

/-! Arity 3 has no single triple, and `translateAtom` says so rather
than inventing one. -/

#guard (translateAtom (.pos (ex "delivered") iriSpace
          [cIri "item", cIri "date", cIri "store"])).isNone

/-! ### Arity ≥ 3 reifies through an anchor -/

private def deliveredBgp : Option Bgp :=
  translateAtomBgp 0 (.pos (ex "delivered") iriSpace
    [.var "item", .var "date", .var "store"])

#guard match deliveredBgp with
       | some bgp => bgp.length == 4        -- the marker plus one per argument
       | none => false
#guard match deliveredBgp with
       | some bgp => bgp.all (fun tp => tp.s == .var (unitermAnchorVar 0))
       | none => false

/-! Two distinct occurrences get distinct anchor variables — without
that, two atoms in one body would be forced to describe the same fact. -/

#guard unitermAnchorVar 0 != unitermAnchorVar 1

/-! ### A variable first argument joins through the satellite

`p(?v, X)` becomes two patterns, so `?v` binds the genuine value rather
than the bookkeeping subject. -/

#guard match translateAtomBgp 0 (.pos (ex "factorial") iriSpace [.var "n", .var "f"]) with
       | some bgp => bgp.length == 2 &&
                     bgp.any (fun tp => tp.p == .iri (unitermArgPred 1) && tp.o == .var "n")
       | none => false

/-! ### A conjunction flattens, and a failure rejects the whole body -/

#guard match translateBody (.and [.atom (.member (cIri "a") (cIri "C")),
                                  .atom (.sub (cIri "C") (cIri "D"))]) with
       | some bgp => bgp.length == 2
       | none => false
#guard (translateBody (.and [.atom (.member (cIri "a") (cIri "C")),
                             .atom (.member (cInt "1") (cIri "D"))])).isNone

/-! ### Rules and programs

A FACT — no body — pairs its head template with the EMPTY pattern, which
is the pattern that matches once with no bindings. -/

private def factRule : Rule := { head := .member (cIri "a") (cIri "C") }
private def badRule : Rule := { head := .member (cInt "1") (cIri "C") }
private def realRule : Rule :=
  { vars := ["x"], head := .member (.var "x") (cIri "D"),
    body := some (.atom (.member (.var "x") (cIri "C"))) }

#guard match translateRule factRule with
       | some (hd, bgp) => hd.length == 1 && bgp.isEmpty
       | none => false
#guard match translateRule realRule with
       | some (hd, bgp) => hd.length == 1 && bgp.length == 1
       | none => false
#guard (translateRule badRule).isNone

/-! A failing rule does not cascade, and the diagnostic says WHICH one
failed rather than leaving a caller to count. -/

#guard (translateProgram [factRule, badRule, realRule]).length == 2
#guard (translateProgramDiag [factRule, badRule, realRule]).2 == [1]
#guard (translateProgramDiag [factRule, realRule]).2 == []

/-! ### A ground graph embeds one to one -/

#guard (graphToBgp [⟨.iri (iriW (ex "s")), iriW (ex "p"), .iri (iriW (ex "o"))⟩]).length == 1

/-! ### The two routes agree

The Lean tree answers RIF by forward chaining (`RIF.Engine`). This
module gives it a second, independent route. Here the translation's
BODY pattern is evaluated against the facts the engine derives, and the
head instantiated from those bindings — and the result is compared with
what the engine itself concludes.

A shared bug would defeat this, so it is evidence rather than proof.
What it does catch is a translation that quietly loses a conjunct or
mis-places an argument, which is the failure mode the encoding above
invites. -/

private def gIriT (s : String) : GTerm := .const (ex s) iriSpace

private def engineFacts : Facts :=
  [ .member (gIriT "a") (gIriT "C"), .member (gIriT "b") (gIriT "C") ]

private def engineRules : List Rule := [realRule]

/-- What the engine concludes: every `?x rdf:type D` it derives. -/
private def engineDerived : List GTerm :=
  ((closure engineRules engineFacts 8).1.filterMap (fun a =>
    match a with
    | .member o c => if c == gIriT "D" then some o else none
    | _ => none))

/-- What the TRANSLATION licenses: the body pattern evaluated against
the same facts as a graph, projected on the rule's variable. -/
private def factsAsGraph : Graph :=
  engineFacts.filterMap (fun a =>
    match a with
    | .member (.const ol osp) (.const cl csp) =>
        match termOfConst ol osp, termOfConst cl csp with
        | .iri oi, ci => some ⟨.iri oi, RDFS.rdfType, ci⟩
        | _, _ => none
    | _ => none)

private def translationDerived : List Term :=
  match translateRule realRule with
  | none => []
  | some (_, bgp) =>
      (evalBgp bgp factsAsGraph).filterMap (fun b => Binding.lookup "x" b)

#guard engineDerived.length == 2
#guard translationDerived.length == 2
#guard translationDerived.all (fun t =>
  engineDerived.any (fun g =>
    match g with
    | .const l sp => termOfConst l sp == t
    | _ => false))

end Checks

end L4Factoidal.RIF
