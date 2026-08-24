/-
L4Factoidal.OWL.QueryRewriteExpand — layer 5 of the port of
`OWL.QueryRewrite`: the recursive class-expression expander.

`expandCeSubject b subj op fuel` answers "what pattern does
`subj rdf:type op` become, when `op` is a class expression?" It is the
counterpart of the F\* source's `expand_ce_subject`.

## What is covered, and the one deliberate boundary

Three arms are here — intersection, union, and existential restriction
(`owl:someValuesFrom`) — plus the leaf case. The universal restriction,
the three cardinality arms and `owl:complementOf` are NOT, and fall
through to the leaf.

That fall-through is the F\* source's own discipline, stated at its
fuel-exhaustion case:

> at worst this is the pre-rewrite behaviour (a bnode as the object of
> rdf:type that won't bind in the data). Sound — never *adds*
> solutions.

`expandCeSubject_unhandled_is_leaf` below proves the Lean fall-through
has exactly that shape, so an unported arm degrades to the identity
rather than to something wrong.

## Why the cardinality arms are held back deliberately

CLAUDE.md records the shipping cardinality rewrite as sound-but-narrow
at <https://github.com/danbri/factoidal/issues/236>: the N=1 qualified
`CE_MaxCardinality` rewrite emits an anchor triple that MULTIPLIES rows
per P-edge and drops vacuous-truth individuals.

Porting it faithfully means reproducing that narrowness; fixing it in
Lean means the two trees stop computing the same thing, which is the
one property the differential method rests on. That is a design
decision for the owner, not a transcription choice, so this layer stops
at the boundary and says so.

## The fresh variable

The existential arm needs a variable for the anonymous filler
individual. Its name is derived from the restriction's marker key, as
in the F\* source, so two restrictions in one BGP get two distinct
variables. The `_sv_` prefix is what
`SPARQL/RewriteVarStrip.lean` later strips from the FINAL projection —
the two modules share that convention and neither works without it.

No `sorry`, no user `axiom`, no `native_decide`.
-/
import L4Factoidal.OWL.QueryRewriteRestriction
import L4Factoidal.SPARQL.RewriteVarStrip

namespace L4Factoidal.OWL.QueryRewriteCore

open L4Factoidal.RDF
open L4Factoidal.RDFS
open L4Factoidal.SPARQL
open L4Factoidal.OWL.RL (owlIntersectionOf owlUnionOf owlSomeValuesFrom owlOnProperty)

/-! ## Leaf and conjunction -/

/-- The unexpanded form: `subj rdf:type leaf`. -/
def singleTypeBgp (subj : PatternSubject) (leaf : PatternTerm) : Bgp :=
  [{ s := subj, p := .iri rdfType, o := leaf }]

/-- Conjoin patterns into a left-deep join. Zero conjuncts is the empty
pattern; one is itself — neither needs a join node. -/
def joinPatterns : List QueryPattern → QueryPattern
  | [] => .empty
  | [g] => g
  | g :: tl => tl.foldl QueryPattern.join g

/-! ## Which class expression is this term? -/

/-- The marker key and combinator for a term, covering the flat
markers of layer 3 and the restrictions of layer 4. -/
def ceCombinatorForTerm (b : Bgp) (pt : PatternTerm) :
    Option (String × Option CeCombinator × Option Restriction) :=
  match markerKey pt with
  | none => none
  | some k =>
      match (findFlatMarkers b).find? (fun e => e.1 == k) with
      | some (_, c) => some (k, some c, none)
      | none =>
          if isSvfSubject b k then some (k, none, some .someValuesFrom)
          else if isAvfSubject b k then some (k, none, some .allValuesFrom)
          else match cardSubjectCombinator b k with
               | some r => some (k, none, some r)
               | none =>
                   if isComplementOfSubject b k then some (k, none, some .complementOf)
                   else none

/-! ## The fresh variable for an existential filler -/

/-- Derived from the restriction's marker key, so two restrictions in
one BGP never collide. The `_sv_` prefix is the one
`SPARQL.isRewriteInternalVar` recognises. -/
def svVarName (k : String) : VarName := "_sv_" ++ k

/-! ## The expander -/

def expandCeSubject (b : Bgp) (subj : PatternSubject) : PatternTerm → Nat → QueryPattern
  | op, 0 => .bgp (singleTypeBgp subj op)
  | op, n + 1 =>
      match ceCombinatorForTerm b op with
      | none => .bgp (singleTypeBgp subj op)
      | some (k, some .intersect, _) =>
          match extractFlatIntersection b k with
          | none => .bgp (singleTypeBgp subj op)
          | some operands =>
              joinPatterns (operands.map (fun o => expandCeSubject b subj o n))
      | some (k, some .union, _) =>
          match extractFlatUnion b k with
          | none => .bgp (singleTypeBgp subj op)
          | some operands =>
              match operands.map (fun o => expandCeSubject b subj o n) with
              | [] => .bgp (singleTypeBgp subj op)
              | [g] => g
              | g :: tl => wrapDistinctOverPattern (unionLadder g tl)
      | some (k, none, some .someValuesFrom) =>
          -- `_:r owl:onProperty :p ; owl:someValuesFrom F` becomes
          -- `subj :p ?_sv_k` conjoined with F expanded at `?_sv_k`.
          match bgpFindFirstObj b k owlOnProperty,
                bgpFindFirstObj b k owlSomeValuesFrom with
          | some prop, some filler =>
              let v := svVarName k
              joinPatterns
                [ .bgp [{ s := subj, p := prop, o := .var v }],
                  expandCeSubject b (.var v) filler n ]
          | _, _ => .bgp (singleTypeBgp subj op)
      -- allValuesFrom, the three cardinality arms and complementOf are
      -- not ported; see the module header. The leaf is the F* source's
      -- own sound fall-back.
      | some (_, _, _) => .bgp (singleTypeBgp subj op)

/-! ## What the boundary guarantees -/

/-- Out of fuel is the identity rewrite. -/
theorem expandCeSubject_zero (b : Bgp) (subj : PatternSubject) (op : PatternTerm) :
    expandCeSubject b subj op 0 = .bgp (singleTypeBgp subj op) := rfl

/-- A term that is no class expression at all is left alone. -/
theorem expandCeSubject_leaf (b : Bgp) (subj : PatternSubject) (op : PatternTerm)
    (n : Nat) (h : ceCombinatorForTerm b op = none) :
    expandCeSubject b subj op (n + 1) = .bgp (singleTypeBgp subj op) := by
  simp only [expandCeSubject, h]

/-- **The unported arms degrade to the identity, not to something
wrong.** An `allValuesFrom`, cardinality or complement marker produces
the pre-rewrite triple, which is the F\* source's own stated
fall-back: it never adds a solution. -/
theorem expandCeSubject_unhandled_is_leaf (b : Bgp) (subj : PatternSubject)
    (op : PatternTerm) (n : Nat) (k : String) (r : Restriction)
    (hr : r ≠ .someValuesFrom)
    (h : ceCombinatorForTerm b op = some (k, none, some r)) :
    expandCeSubject b subj op (n + 1) = .bgp (singleTypeBgp subj op) := by
  simp only [expandCeSubject, h]
  cases r <;> simp_all

/-! ## Build-time checks -/

private def cA : WfIri := ⟨"http://example.org/A", by decide⟩
private def cB : WfIri := ⟨"http://example.org/B", by decide⟩
private def cP : WfIri := ⟨"http://example.org/p", by decide⟩

/-! An intersection of two named classes at `?x`: two conjuncts. -/
private def interB : Bgp :=
  [ { s := .bnode "c",  p := .iri owlIntersectionOf, o := .bnode "l1" },
    { s := .bnode "l1", p := .iri rdfFirst, o := .iri cA },
    { s := .bnode "l1", p := .iri rdfRest,  o := .bnode "l2" },
    { s := .bnode "l2", p := .iri rdfFirst, o := .iri cB },
    { s := .bnode "l2", p := .iri rdfRest,  o := .iri rdfNil } ]

#guard (match expandCeSubject interB (.var "x") (.bnode "c") 5 with
        | .join (.bgp l) (.bgp r) => l.length == 1 && r.length == 1
        | _ => false)

/-! A union of two named classes: a DISTINCT-wrapped ladder. -/
private def unionB : Bgp :=
  [ { s := .bnode "c",  p := .iri owlUnionOf, o := .bnode "l1" },
    { s := .bnode "l1", p := .iri rdfFirst, o := .iri cA },
    { s := .bnode "l1", p := .iri rdfRest,  o := .bnode "l2" },
    { s := .bnode "l2", p := .iri rdfFirst, o := .iri cB },
    { s := .bnode "l2", p := .iri rdfRest,  o := .iri rdfNil } ]

#guard (match expandCeSubject unionB (.var "x") (.bnode "c") 5 with
        | .subSelect _ => true
        | _ => false)

/-! An existential restriction with a named filler: the property triple
joined to the filler's leaf, and the fresh variable is `_sv_r`. -/
private def svfB : Bgp :=
  [ { s := .bnode "r", p := .iri owlOnProperty, o := .iri cP },
    { s := .bnode "r", p := .iri owlSomeValuesFrom, o := .iri cA } ]

#guard (match expandCeSubject svfB (.var "x") (.bnode "r") 5 with
        | .join (.bgp l) (.bgp r) => l.length == 1 && r.length == 1
        | _ => false)
#guard svVarName "r" == "_sv_r"
#guard L4Factoidal.SPARQL.isRewriteInternalVar (svVarName "r") == true

/-! A named class is a leaf. -/
#guard (match expandCeSubject interB (.var "x") (.iri cA) 5 with
        | .bgp out => out.length == 1
        | _ => false)

/-! An allValuesFrom marker degrades to the leaf — the unported arm. -/
private def avfB : Bgp :=
  [ { s := .bnode "r", p := .iri owlOnProperty, o := .iri cP },
    { s := .bnode "r", p := .iri L4Factoidal.OWL.RL.owlAllValuesFrom, o := .iri cA } ]
#guard (match expandCeSubject avfB (.var "x") (.bnode "r") 5 with
        | .bgp out => out == singleTypeBgp (.var "x") (.bnode "r")
        | _ => false)

/-! Zero fuel is the identity. -/
#guard (match expandCeSubject interB (.var "x") (.bnode "c") 0 with
        | .bgp out => out == singleTypeBgp (.var "x") (.bnode "c")
        | _ => false)

/-! ## Axiom audit -/

#print axioms expandCeSubject_leaf
#print axioms expandCeSubject_unhandled_is_leaf
end L4Factoidal.OWL.QueryRewriteCore
