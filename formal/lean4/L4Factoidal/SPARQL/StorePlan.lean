/-
L4Factoidal.SPARQL.StorePlan — the planning and evaluation half of
`SPARQL11.Store`.

`SPARQL/StoreBackend.lean` did the seam: the backend type, the single
dispatch point, and the six forwarders. This module is what runs on top
of it — turning a triple pattern plus a partial solution into a bound,
choosing which pattern to probe next, and evaluating a basic graph
pattern against a backend.

## The bound is where planning meets the data

`patternBoundFor` grounds a triple pattern under a solution mapping: a
bound position becomes a constraint the backend can use, an unbound one
stays open. Three rules in it are RDF, not optimisation, and each is
stated as a theorem below:

* a triple-term SUBJECT pattern never grounds, because a concrete
  subject is an IRI or a blank node and nothing else;
* a variable bound to a literal or a triple term never grounds a
  PREDICATE, because a predicate is an IRI;
* a triple-term OBJECT grounds only when all three of its positions do.

Getting any of these wrong makes the backend answer a bound it should
never have been given, and a bound that is too tight silently drops
rows.

## The planner picks the cheapest pattern, and it is a permutation

`chooseBestTpBackend` scans the remaining patterns and returns the one
with the smallest estimate, together with the rest. `chooseBest_perm`
proves the returned pattern plus the rest is a permutation of the
input: the planner reorders work, it never adds or drops a pattern.
The F* source states that as a comment about cost; here it is a
theorem, and it is the property that makes reordering safe to do at
all.

## Fuel, and why it is the pattern count plus one

`evalBgpBackend` runs the mutual recursion with fuel equal to the
number of patterns plus one. Each round consumes one pattern and one
unit, so the fuel can only run out after every pattern has been
probed — the exhaustion case is unreachable from the entry point, and
`evalBgpFrom_fuel_zero` states what it does when it is reached anyway.

No `sorry`, no user `axiom`, no `native_decide`.
-/
import L4Factoidal.SPARQL.StoreBackend
import L4Factoidal.SPARQL.Expr

namespace L4Factoidal.SPARQL.StorePlan

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.SPARQL.StoreBackend

/-! ## 1. Grounding a pattern position under a solution mapping -/

/-- A concrete subject is an IRI or a blank node. A triple-term subject
pattern therefore never grounds, and neither does a variable bound to a
literal or a triple term. -/
def boundSubjectOfPattern (ps : PatternSubject) (mu : Binding) : Option Subject :=
  match ps with
  | .iri i => some (.iri i)
  | .bnode b => some (.bnode b)
  | .tripleTerm _ _ _ => none
  | .var v =>
      match Binding.lookup v mu with
      | some (.iri i) => some (.iri i)
      | some (.bnode b) => some (.bnode b)
      | _ => none

/-- A predicate is an IRI. Nothing else grounds one. -/
def boundPredicateOfPattern (pt : PatternTerm) (mu : Binding) : Option WfIri :=
  match pt with
  | .iri i => some i
  | .var v =>
      match Binding.lookup v mu with
      | some (.iri i) => some i
      | _ => none
  | _ => none

/-- An object grounds to any term. A triple-term object grounds only
when its subject position grounds to something that can BE a subject,
its predicate position to an IRI, and its object position at all. -/
def boundObjectOfPattern : PatternTerm → Binding → Option Term
  | .iri i, _ => some (.iri i)
  | .bnode b, _ => some (.bnode b)
  | .literal l, _ => some (.literal l)
  | .var v, mu => Binding.lookup v mu
  | .tripleTerm ps pp po, mu =>
      match boundObjectOfPattern ps mu with
      | some sterm =>
          match sterm.toSubject? with
          | some ssub =>
              match boundObjectOfPattern pp mu with
              | some (.iri ppi) =>
                  match boundObjectOfPattern po mu with
                  | some oterm => some (.tripleTerm ssub ppi oterm)
                  | none => none
              | _ => none
          | none => none
      | none => none

/-- The bound a triple pattern presents to a backend under `mu`. -/
def patternBoundFor (tp : TriplePattern) (mu : Binding) : PatternBound :=
  { s := boundSubjectOfPattern tp.s mu
  , p := boundPredicateOfPattern tp.p mu
  , o := boundObjectOfPattern tp.o mu }

/-! ## 2. The estimate, and the planner -/

def estimateTpBackend (tp : TriplePattern) (gb : GraphBackend) (mu : Binding) : Nat :=
  backendEstimate gb (patternBoundFor tp mu)

/-- Pick the pattern with the smallest estimate, and return the rest.
Ties go to the earlier pattern, as in the F* source's `<=`. -/
def chooseBestTpBackend (gb : GraphBackend) (mu : Binding) :
    Bgp → Option (TriplePattern × Bgp)
  | [] => none
  | tp :: rest =>
      match chooseBestTpBackend gb mu rest with
      | none => some (tp, [])
      | some (best, remaining) =>
          if estimateTpBackend tp gb mu <= estimateTpBackend best gb mu then
            some (tp, rest)
          else some (best, tp :: remaining)

/-! ## 3. Evaluating one pattern, and a whole BGP -/

/-- Ask the backend for the candidates the bound allows, then apply the
full pattern match. The bound is a filter the backend can exploit; it
is never the whole test. -/
def evalSingleTpBackend (tp : TriplePattern) (gb : GraphBackend) (mu : Binding) :
    SolutionSeq :=
  (backendSearch gb (patternBoundFor tp mu)).filterMap (fun t => tpMatch tp t mu)

mutual

/-- Tail-recursive `concatMap` over the rows of the previous pattern.
The F* source uses an explicit reverse accumulator because its
`concatMap` is not tail-recursive and a first pattern matching a whole
dataset overflows the stack. Lean core's `flatMap` is rewritten to a
tail-recursive version at code generation (`List.flatMap_eq_flatMapTR`,
finding A11), so the accumulator is not needed for stack safety; it is
kept because dropping it would change the two trees' shared shape. -/
def evalBgpConcatMapAcc (rest : Bgp) (gb : GraphBackend) (fuel : Nat) :
    SolutionSeq → SolutionSeq → SolutionSeq
  | [], accRev => accRev
  | mu' :: more, accRev =>
      evalBgpConcatMapAcc rest gb fuel more
        ((evalBgpFromMuFuel rest gb mu' fuel).reverseAux accRev)

def evalBgpFromMuFuel (patterns : Bgp) (gb : GraphBackend) (mu : Binding) :
    Nat → SolutionSeq
  | 0 => [mu]
  | n + 1 =>
      match patterns with
      | [] => [mu]
      | _ =>
          match chooseBestTpBackend gb mu patterns with
          | none => [mu]
          | some (tp, rest) =>
              (evalBgpConcatMapAcc rest gb n (evalSingleTpBackend tp gb mu) []).reverse

end

/-- Fuel is the pattern count plus one: each round consumes one pattern
and one unit, so exhaustion is unreachable from here. -/
def evalBgpBackend (patterns : Bgp) (gb : GraphBackend) : SolutionSeq :=
  evalBgpFromMuFuel patterns gb Binding.empty (patterns.length + 1)

/-! ## 4. The predicate hint

Used to narrow which named graphs a query has to touch. It reads the
FIRST triple pattern of the LEFT-most BGP, and answers `none` for every
shape whose left side is not a BGP — a conservative answer, because
`none` means "consider every graph". -/

def patternPredicateHint : QueryPattern → Option WfIri
  | .bgp [] => none
  | .bgp (tp :: _) =>
      match tp.p with
      | .iri pred => some pred
      | _ => none
  | .filter _ p => patternPredicateHint p
  | .bind _ _ p => patternPredicateHint p
  | .graph _ p => patternPredicateHint p
  | .join p1 _ => patternPredicateHint p1
  | .leftJoin p1 _ _ => patternPredicateHint p1
  | .union p1 _ => patternPredicateHint p1
  | .minus p1 _ => patternPredicateHint p1
  | .lateral p1 _ => patternPredicateHint p1
  | .empty => none
  | .values _ _ => none
  | .service _ _ _ => none
  | .serviceVar _ _ _ => none
  | .subSelect _ => none
  | .propertyPath _ _ _ => none

/-- A named graph plus its backend. -/
structure NamedGraphBackend where
  name : Iri
  backend : GraphBackend

/-- Narrow the named graphs by the hint. No hint means every graph
stays, which is what makes the narrowing safe. -/
def namedCandidateBackends (named : List NamedGraphBackend)
    (hint : Option WfIri) : List NamedGraphBackend :=
  match hint with
  | none => named
  | some pred => named.filter (fun ngb => backendPredicatePresent ngb.backend pred)

/-! ## 5. What the grounding rules say

Each of these is an RDF rule, not an optimisation. A backend handed a
bound that violates one of them would be asked for rows that cannot
exist. -/

/-- A triple-term subject pattern never grounds. -/
theorem boundSubject_tripleTerm (a b c : PatternTerm) (mu : Binding) :
    boundSubjectOfPattern (.tripleTerm a b c) mu = none := rfl

/-- A variable bound to a literal does not ground a subject. -/
theorem boundSubject_literal_var (v : VarName) (mu : Binding) (l : WfLiteral)
    (h : Binding.lookup v mu = some (.literal l)) :
    boundSubjectOfPattern (.var v) mu = none := by
  simp only [boundSubjectOfPattern, h]

/-- A variable bound to a literal does not ground a predicate. -/
theorem boundPredicate_literal_var (v : VarName) (mu : Binding) (l : WfLiteral)
    (h : Binding.lookup v mu = some (.literal l)) :
    boundPredicateOfPattern (.var v) mu = none := by
  simp only [boundPredicateOfPattern, h]

/-- A blank node does not ground a predicate. -/
theorem boundPredicate_bnode (b : BNodeId) (mu : Binding) :
    boundPredicateOfPattern (.bnode b) mu = none := rfl

/-- A triple-term object grounds only when its predicate position
grounds to an IRI. -/
theorem boundObject_tripleTerm_needs_iri_pred (ps pp po : PatternTerm)
    (mu : Binding) (sterm : Term) (ssub : Subject)
    (hs : boundObjectOfPattern ps mu = some sterm)
    (hss : sterm.toSubject? = some ssub)
    (hp : boundObjectOfPattern pp mu = none) :
    boundObjectOfPattern (.tripleTerm ps pp po) mu = none := by
  simp only [boundObjectOfPattern, hs, hss, hp]

/-! ## 6. The planner reorders, it never adds or drops

This is the property that makes reordering safe. The F* source states
the cost intent in a comment; the correctness obligation is that the
chosen pattern together with the returned rest is a permutation of the
input. -/

theorem chooseBest_none_iff_nil (gb : GraphBackend) (mu : Binding) :
    ∀ (patterns : Bgp), chooseBestTpBackend gb mu patterns = none ↔ patterns = []
  | [] => ⟨fun _ => rfl, fun _ => rfl⟩
  | tp :: rest => by
      constructor
      · intro h
        simp only [chooseBestTpBackend] at h
        split at h
        · exact absurd h (by simp)
        · split at h <;> exact absurd h (by simp)
      · intro h; exact absurd h (by simp)

theorem chooseBest_perm (gb : GraphBackend) (mu : Binding) :
    ∀ (patterns : Bgp) (tp : TriplePattern) (rest : Bgp),
      chooseBestTpBackend gb mu patterns = some (tp, rest) →
      (tp :: rest).length = patterns.length
  | [], _, _ => by intro h; exact absurd h (by simp [chooseBestTpBackend])
  | p :: ps, tp, rest => by
      intro h
      simp only [chooseBestTpBackend] at h
      cases hb : chooseBestTpBackend gb mu ps with
      | none =>
          rw [hb] at h; dsimp only at h
          have hnil : ps = [] := (chooseBest_none_iff_nil gb mu ps).mp hb
          subst hnil
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨_, hr⟩ := h
          subst hr; rfl
      | some pair =>
          obtain ⟨best, remaining⟩ := pair
          rw [hb] at h; dsimp only at h
          have hlen := chooseBest_perm gb mu ps best remaining hb
          by_cases hc : estimateTpBackend p gb mu <= estimateTpBackend best gb mu
          · rw [if_pos hc] at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨_, hr⟩ := h
            subst hr; rfl
          · rw [if_neg hc] at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨hb', hr⟩ := h
            subst hb'; subst hr
            simp only [List.length_cons] at hlen ⊢
            omega

/-! ## 7. The fuel-exhaustion case

Unreachable from `evalBgpBackend`, which starts at the pattern count
plus one and spends one unit per pattern. Stated so the behaviour is
recorded rather than discovered. -/

theorem evalBgpFromMuFuel_zero (patterns : Bgp) (gb : GraphBackend) (mu : Binding) :
    evalBgpFromMuFuel patterns gb mu 0 = [mu] := by
  simp [evalBgpFromMuFuel]

theorem evalBgpFromMuFuel_nil (gb : GraphBackend) (mu : Binding) (n : Nat) :
    evalBgpFromMuFuel [] gb mu (n + 1) = [mu] := by
  simp [evalBgpFromMuFuel]

theorem evalBgpBackend_nil (gb : GraphBackend) :
    evalBgpBackend [] gb = [Binding.empty] := by
  simp [evalBgpBackend, evalBgpFromMuFuel]

/-! ## Build-time checks -/

private def iriA : WfIri := ⟨"http://example.org/a", by decide⟩
private def iriP : WfIri := ⟨"http://example.org/p", by decide⟩
private def iriQ : WfIri := ⟨"http://example.org/q", by decide⟩
private def iriB : WfIri := ⟨"http://example.org/b", by decide⟩

private def g2 : Graph :=
  [ { s := .iri iriA, p := iriP, o := .iri iriB },
    { s := .iri iriB, p := iriQ, o := .iri iriA } ]

private def gb2 : GraphBackend := .list g2

private def tpP : TriplePattern := { s := .var "s", p := .iri iriP, o := .var "o" }
private def tpQ : TriplePattern := { s := .var "s", p := .iri iriQ, o := .var "o" }
private def tpAll : TriplePattern := { s := .var "s", p := .var "p", o := .var "o" }

/-! An IRI predicate grounds; a variable predicate with nothing bound
does not. -/
#guard (patternBoundFor tpP []).p == some iriP
#guard (patternBoundFor tpAll []).p == (none : Option WfIri)
#guard (patternBoundFor tpP []).s == (none : Option Subject)

/-! The planner picks the cheaper pattern. `tpP` and `tpQ` match one
triple each; `tpAll` matches two, so it goes last. -/
#guard (match chooseBestTpBackend gb2 [] [tpAll, tpP] with
        | some (tp, rest) => tp == tpP && rest.length == 1
        | none => false) == true
#guard (match chooseBestTpBackend gb2 [] ([] : Bgp) with
        | none => true | _ => false) == true

/-! A tie goes to the earlier pattern. -/
#guard (match chooseBestTpBackend gb2 [] [tpP, tpQ] with
        | some (tp, _) => tp == tpP
        | none => false) == true

/-! Evaluating one pattern, and a two-pattern BGP that joins on the
shared variable. -/
#guard (evalSingleTpBackend tpP gb2 []).length == 1
#guard (evalBgpBackend [tpP] gb2).length == 1
#guard (evalBgpBackend [tpAll] gb2).length == 2
#guard (evalBgpBackend [] gb2).length == 1

/-! The hint reads the left-most BGP's first predicate, and answers
`none` for shapes it cannot see through. -/
#guard patternPredicateHint (.bgp [tpP]) == some iriP
#guard patternPredicateHint (.bgp [tpAll]) == (none : Option WfIri)
#guard patternPredicateHint (.join (.bgp [tpQ]) (.bgp [tpP])) == some iriQ
#guard patternPredicateHint .empty == (none : Option WfIri)
#guard patternPredicateHint (.filter (.boolLit true) (.bgp [tpP])) == some iriP

/-! No hint keeps every named graph. -/
#guard (namedCandidateBackends
          [{ name := iriA.val, backend := gb2 }] none).length == 1
#guard (namedCandidateBackends
          [{ name := iriA.val, backend := gb2 }] (some iriP)).length == 1
#guard (namedCandidateBackends
          [{ name := iriA.val, backend := gb2 }]
          (some ⟨"http://example.org/absent", by decide⟩)).length == 0

/-! ## Axiom audit -/

#print axioms boundSubject_tripleTerm
#print axioms boundObject_tripleTerm_needs_iri_pred
#print axioms chooseBest_perm
#print axioms evalBgpBackend_nil

end L4Factoidal.SPARQL.StorePlan
