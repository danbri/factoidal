/-
L4Factoidal.RIF.Core — RIF Core syntax and forward-chaining
evaluation, ported from `formal/fstar/RIF.Core.Syntax.fst` and
`RIF.Core.Eval.fst`.

Spec: RIF Core (https://www.w3.org/TR/rif-core/) plus RIF-RDF
Compatibility (https://www.w3.org/TR/rif-rdf-owl/) for the triple
form that lets a RIF ruleset entail RDF triples — which is what the
SPARQL RIF entailment regime consumes.

The evaluator is a plain semi-naive forward chain: apply every rule to
the current facts, keep what is new, repeat to a fixed point under a
round bound. Bounded rather than unbounded because RIF Core with
external builtins can generate ground terms indefinitely; the bound is
explicit and reported, never silent.
-/
import L4Factoidal.RDF.Core

namespace L4Factoidal.RIF

open L4Factoidal.RDF

structure Var where
  name : String
deriving Repr, DecidableEq, Inhabited

/-- A RIF term: a variable, an RDF constant, or an external
    (built-in) function application. -/
inductive Tm where
  | var      (v : Var)
  | const    (t : Term)
  | external (fn : String) (args : List Tm)
deriving Repr

/-- A RIF atom. `triple` is the RDF-compatibility form; the frame,
    member and sub forms are RIF's own object model. -/
inductive Atom where
  | triple  (s p o : Tm)
  | frame   (s p o : Tm)
  | member  (i c : Tm)
  | sub     (a b : Tm)
  | uniterm (fn : Tm) (args : List Tm)
deriving Repr

inductive Body where
  | atom     (a : Atom)
  | and      (bs : List Body)
  | external (fn : String) (args : List Tm)
  | equal    (a b : Tm)
deriving Repr

structure Rule where
  name : Option String := none
  head : Atom
  body : Body
deriving Repr

structure Program where
  rules : List Rule := []
deriving Repr

/-! ## Substitutions -/

/-- A binding of variables to ground RDF terms. -/
abbrev Subst := List (String × Term)

def Subst.lookup (s : Subst) (v : String) : Option Term :=
  (s.find? (fun (k, _) => k == v)).map (·.2)

/-- Extend a substitution, failing when the variable is already bound
    to a DIFFERENT term. This is what makes a repeated variable across
    a rule body act as a join rather than as two independent
    matches. -/
def Subst.extend (s : Subst) (v : String) (t : Term) : Option Subst :=
  match s.lookup v with
  | some u => if u.eqb t then some s else none
  | none   => some ((v, t) :: s)

/-- Ground a term under a substitution. An external call is NOT
    evaluated here — builtins are a separate concern, and an
    unevaluated external grounds to nothing rather than to a
    placeholder. -/
def groundTm (s : Subst) : Tm → Option Term
  | .var v      => s.lookup v.name
  | .const t    => some t
  | .external _ _ => none

/-- Match one term pattern against a ground term. -/
def matchTm (s : Subst) (pat : Tm) (t : Term) : Option Subst :=
  match pat with
  | .var v      => s.extend v.name t
  | .const c    => if c.eqb t then some s else none
  | .external _ _ => none

/-! ## Matching atoms against a graph -/

private def subjTerm (t : Triple) : Term := t.s.toTerm

/-- All substitutions extending `s` that make the atom true in the
    graph. Only the `triple` and `frame` forms consult RDF facts —
    frames share the triple encoding under RIF-RDF compatibility. -/
def matchAtom (facts : List Triple) (s : Subst) : Atom → List Subst
  | .triple sp pp op | .frame sp pp op =>
      facts.filterMap (fun f =>
        match matchTm s sp (subjTerm f) with
        | none => none
        | some s1 =>
            match matchTm s1 pp (.iri f.p) with
            | none => none
            | some s2 => matchTm s2 op f.o)
  | _ => []      -- member/sub/uniterm need the RIF object model

/-- All substitutions satisfying a body. `equal` compares ground
    terms; an `external` in the body contributes nothing here (see the
    module header on builtins). -/
partial def matchBody (facts : List Triple) (s : Subst) : Body → List Subst
  | .atom a  => matchAtom facts s a
  | .and bs  => bs.foldl (fun acc b => acc.flatMap (fun s' => matchBody facts s' b)) [s]
  | .equal a b =>
      match groundTm s a, groundTm s b with
      | some x, some y => if x.eqb y then [s] else []
      | _, _ => []
  | .external _ _ => []

/-- Instantiate a head atom, producing a triple when every position
    grounds to a term and the predicate is an IRI. -/
def instantiateHead (s : Subst) : Atom → Option Triple
  | .triple sp pp op | .frame sp pp op =>
      match groundTm s sp, groundTm s pp, groundTm s op with
      | some st, some (.iri p), some ot =>
          match st with
          | .iri i   => some ⟨.iri i, p, ot⟩
          | .bnode b => some ⟨.bnode b, p, ot⟩
          | _        => none      -- a literal subject is not a triple
      | _, _, _ => none
  | _ => none

/-- One round: every rule applied to the current facts. -/
def step (p : Program) (facts : List Triple) : List Triple :=
  p.rules.flatMap (fun r =>
    (matchBody facts [] r.body).filterMap (fun s => instantiateHead s r.head))

private def containsTriple (facts : List Triple) (t : Triple) : Bool :=
  facts.any (fun f => f.eqb t)

/-- Forward chain to a fixed point, bounded by `rounds`.

    Returns the facts AND whether the bound was reached. The flag is
    not decoration: a caller that reports entailment from a truncated
    closure is reporting a guess, so the bound is visible rather than
    silently absorbed. -/
def closure (p : Program) (facts : List Triple) (rounds : Nat)
    : List Triple × Bool :=
  match rounds with
  | 0     => (facts, true)
  | n + 1 =>
      let derived := (step p facts).filter (fun t => !(containsTriple facts t))
      if derived.isEmpty then (facts, false)
      else closure p (facts ++ derived) n

/-- Does the program entail the triple from these facts? -/
def entails (p : Program) (facts : List Triple) (goal : Triple) (rounds : Nat) : Bool :=
  containsTriple (closure p facts rounds).1 goal

end L4Factoidal.RIF
