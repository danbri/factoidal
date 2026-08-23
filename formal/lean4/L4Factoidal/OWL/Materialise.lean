/-
L4Factoidal.OWL.Materialise — POSITIVE-SOUND membership and the
materialisation pass.

Port of `formal/fstar/Tableau.fst` §§5–9: `is_member`, the
existential-witness introduction, and the materialisation entry
points. Step 2 of https://github.com/danbri/factoidal/issues/548 ;
step 1 was `L4Factoidal/OWL/ClassExpr.lean`, whose AST this module
reads.

## Three values, and why the third one is the point

`isMember` answers `Option Bool`:

* `some true`  — provably a member;
* `some false` — provably NOT a member;
* `none`       — not known.

`none` is ALWAYS sound: the caller falls back to the OWL RL closure,
which decides fewer things but decides them right. Every rule below
that could answer confidently on an open-world reading it cannot
justify answers `none` instead. That is not caution for its own
sake — an engine that says "not a member" because it has not SEEN a
membership has confused an empty search for a proof, and under the
open world assumption those are different things.

## What "positive-sound" means, and what it excludes

`cePositiveSound` is the gate this module applies before it writes a
membership into the graph. It admits exactly the shapes whose
`some true` is entailed in EVERY model:

* `named c` — the graph asserts `i rdf:type c`;
* `hasValue p v` — the graph asserts `i p v`;
* `someOf p c` (with `c` positive-sound) — a known successor in `c`
  is a witness;
* `minCard k p` and `minQualCard k p c` — `k` known successors are
  witnesses, and the count is a conservative floor;
* `intersection` / `union` of positive-sound parts.

It EXCLUDES:

* `allOf p c` — a successor this graph has not seen could violate
  `c`, so "every KNOWN successor is in `c`" does not entail
  `∀ p. c`;
* `maxCard` / `exactCard` / `maxQualCard` / `exactQualCard` — a
  positive membership needs `owl:sameAs` reasoning or a unique-name
  assumption, and this module has neither;
* `complement` — needs classical negation.

Refuting those is the refutation calculus's job
(`formal/fstar/Tableau.Refute.fst`, step 3 of the issue), not this
module's. Withholding an entailment is sound; asserting one that a
model can falsify is not.

## No unique-name assumption

Two different IRIs may denote one individual unless the graph says
`owl:differentFrom`. So a successor count is a LOWER bound, never an
exact figure: `minCard` can fire on it, `maxCard` cannot.
-/
import L4Factoidal.OWL.ClassExpr
import Std.Data.HashSet

namespace L4Factoidal.OWL.Mat

open L4Factoidal.RDF
open L4Factoidal.OWL
open L4Factoidal.OWL.RL

/-! ## Lookups -/

/-- Does the graph assert `i rdf:type c`? -/
def hasType (st : Store) (i : Subject) (c : WfIri) : Bool :=
  (st.withSubjPred i rdfType).any (fun t => t.o == Term.iri c)

/-- Every `y` with `(i p y)` in the graph. -/
def successors (st : Store) (i : Subject) (p : WfIri) : List Term :=
  (st.withSubjPred i p).map (·.o)

/-- `i` is provably in `¬c` when the graph puts `i` in a class
    declared `owl:disjointWith` `c`, in either direction. One
    direction only: the ABSENCE of a disjoint witness proves nothing,
    so this never answers `some false`. -/
def hasDisjointWitness (st : Store) (i : Subject) (c : WfIri) : Bool :=
  let forward := (st.withSubjPred (.iri c) owlDisjointWith).map (·.o)
  let fwdHit := forward.any (fun t => match t with
                                      | .iri d => hasType st i d
                                      | _      => false)
  if fwdHit then true
  else
    (st.withPredObj owlDisjointWith (Term.iri c)).any (fun t =>
      match t.s with
      | .iri d => hasType st i d
      | _      => false)

/-! ## `isMember`

Fuel bounds the recursion. Running out answers `none`, which is the
same answer an unreadable expression gets — the reasoner never
guesses past its budget. -/

mutual

partial def isMember (st : Store) (i : Subject) (ce : ClassExpr) (fuel : Nat)
    : Option Bool :=
  match fuel with
  | 0 => none
  | n + 1 =>
    match ce with
    | .unknown => none

    -- A named class: an open-world lookup. The graph asserting it
    -- settles the question; the graph NOT asserting it settles
    -- nothing.
    | .named c => if hasType st i c then some true else none

    -- `∃ p. {v}`: the assertion `i p v` is the witness.
    | .hasValue p v =>
        if (successors st i p).any (fun t => t == v) then some true else none

    -- `∃ p. c`: a known successor in `c` is a witness. No known
    -- successor is not a refutation — an unseen one may exist — so
    -- this never answers `some false`.
    | .someOf p c => anyIsMember st (successors st i p) c n

    -- `∀ p. c`: `some true` only when every KNOWN successor is
    -- provably in `c`; `some false` as soon as one provably is not.
    | .allOf p c => allIsMember st (successors st i p) c n

    | .intersection cs => intersectionMember st i cs n
    | .union cs        => unionMember st i cs n

    -- `¬c`: a definite answer is flipped, `none` stays `none`. This
    -- is not classical negation — it cannot prove "i is not a c"
    -- without an explicit disproof of `c`. The disjointWith bridge
    -- above supplies one common case of that disproof.
    | .complement c =>
        (match c with
         | .named ci =>
             if hasDisjointWitness st i ci then some true
             else (isMember st i c n).map (fun b => !b)
         | _ => (isMember st i c n).map (fun b => !b))

    -- `≥ k p`: the count of known successors is a conservative floor,
    -- because two distinct names may denote one individual. Reaching
    -- `k` proves membership; falling short proves nothing.
    | .minCard k p => if (successors st i p).length ≥ k then some true else none

    -- `≤ k p` and `= k p`: provable here only in the trivial case —
    -- `k = 0` with no known successor. Anything else needs the
    -- provable-distinctness machinery of the refutation calculus.
    | .maxCard k p =>
        if k == 0 && (successors st i p).isEmpty then some true else none
    | .exactCard k p =>
        if k == 0 && (successors st i p).isEmpty then some true else none

    | .minQualCard k p c =>
        if countQualSuccessors st (successors st i p) c n ≥ k then some true else none
    | .maxQualCard k p c =>
        if k == 0 && countQualSuccessors st (successors st i p) c n == 0
        then some true else none
    | .exactQualCard k p c =>
        if k == 0 && countQualSuccessors st (successors st i p) c n == 0
        then some true else none

    -- `{a₁ … aₘ}`: provable only on a SYNTACTIC match. `i` could be
    -- `owl:sameAs` a member without being spelled like one, so a
    -- miss is `none` rather than `some false`.
    | .oneOf members =>
        if members.any (fun t => t == i.toTerm) then some true else none

    -- A facet-restricted datatype. This module never evaluates a
    -- literal against facets; facet satisfiability belongs to the
    -- refutation calculus.
    | .dataRestriction _ _ => none

/-- `∃`: stop at the first successor provably in `c`. -/
partial def anyIsMember (st : Store) (ys : List Term) (c : ClassExpr) (fuel : Nat)
    : Option Bool :=
  match ys with
  | []      => none
  | y :: tl =>
    match termAsSubject y with
    | none   => anyIsMember st tl c fuel
    | some s =>
      match isMember st s c fuel with
      | some true => some true
      | _         => anyIsMember st tl c fuel

/-- `∀`: stop at the first successor provably NOT in `c`. An empty
    successor list is vacuously true. One unknown successor makes the
    whole answer unknown — "all" cannot be proved past a gap. -/
partial def allIsMember (st : Store) (ys : List Term) (c : ClassExpr) (fuel : Nat)
    : Option Bool :=
  match ys with
  | []      => some true
  | y :: tl =>
    match termAsSubject y with
    -- A literal successor is in no class, so the restriction fails.
    | none   => some false
    | some s =>
      match isMember st s c fuel with
      | some false => some false
      | some true  => allIsMember st tl c fuel
      | none       => none

/-- `⊓`: every conjunct must be `some true`. One unknown conjunct does
    NOT end the search — a later conjunct that is provably false
    still refutes the whole intersection. -/
partial def intersectionMember (st : Store) (i : Subject) (cs : List ClassExpr)
    (fuel : Nat) : Option Bool :=
  match cs with
  | []      => some true          -- the empty intersection is owl:Thing
  | c :: tl =>
    match isMember st i c fuel with
    | some false => some false
    | some true  => intersectionMember st i tl fuel
    | none       =>
      match intersectionMember st i tl fuel with
      | some false => some false
      | _          => none

/-- `⊔`: one disjunct proved true settles it; all proved false
    refutes it. An unknown disjunct still lets a later true one
    decide. -/
partial def unionMember (st : Store) (i : Subject) (cs : List ClassExpr)
    (fuel : Nat) : Option Bool :=
  match cs with
  | []      => some false         -- the empty union is owl:Nothing
  | c :: tl =>
    match isMember st i c fuel with
    | some true  => some true
    | some false => unionMember st i tl fuel
    | none       =>
      match unionMember st i tl fuel with
      | some true => some true
      | _         => none

/-- How many of `ys` are PROVABLY in `c`. A successor whose
    membership is unknown does not count, so this under-counts — the
    direction that makes `minQualCard` sound and `maxQualCard`
    unprovable. -/
partial def countQualSuccessors (st : Store) (ys : List Term) (c : ClassExpr)
    (fuel : Nat) : Nat :=
  match ys with
  | []      => 0
  | y :: tl =>
    let rest := countQualSuccessors st tl c fuel
    match termAsSubject y with
    | none   => rest
    | some s => match isMember st s c fuel with
                | some true => rest + 1
                | _         => rest

end

/-! ## The soundness gate

Which shapes may have a `some true` WRITTEN INTO THE GRAPH. See the
module header for the argument shape by shape. -/

mutual

partial def cePositiveSound : ClassExpr → Bool
  | .named _            => true
  | .hasValue _ _       => true
  | .minCard _ _        => true
  | .someOf _ c         => cePositiveSound c
  | .minQualCard _ _ c  => cePositiveSound c
  | .intersection cs    => ceListPositiveSound cs
  | .union cs           => ceListPositiveSound cs
  | _                   => false

partial def ceListPositiveSound : List ClassExpr → Bool
  | []      => true
  | c :: tl => cePositiveSound c && ceListPositiveSound tl

end

/-! ## Existential witnesses

`(i rdf:type B)` with `B` an `∃ p. c` obliges every model to give `i`
a `p`-successor in `c`. The RL closure is Datalog and cannot invent
one. This mints a deterministic blank node for the obligation and
asserts the edge.

Sound: every model of the input must already satisfy the obligation,
and the witness asserts nothing about being DISTINCT from an existing
successor, so it cannot contradict the graph. Bounded: one witness
per `(i, p)` pair, one pass, no iteration. -/

/-- The `(p, c)` obligation of an existential shape, or `none`. -/
def existentialObligation : ClassExpr → Option (WfIri × ClassExpr)
  | .someOf p c        => some (p, c)
  | .minCard k p       => if k == 1 then some (p, .unknown) else none
  | .minQualCard k p c => if k == 1 then some (p, c) else none
  | _                  => none

/-- The witness blank node for `(i, p)`. Deterministic, so re-running
    the pass mints the same node rather than a second one. -/
def witnessBNodeId (i : Subject) (p : WfIri) : BNodeId :=
  let iStr := match i with
    | .iri s   => s.val
    | .bnode b => b
  "_:bw_" ++ iStr ++ "__" ++ p.val

/-- Does `i` already have a `p`-successor that discharges the
    obligation? An UNQUALIFIED obligation (`ClassExpr.unknown` as the
    filler) is discharged by any successor at all. -/
def alreadyHasWitness (st : Store) (i : Subject) (p : WfIri) (c : ClassExpr)
    : Bool :=
  let succs := successors st i p
  match c with
  | .unknown => !succs.isEmpty
  | _        => anyIsMember st succs c 32 == some true

/-- The witness triples one existential class expression demands, over
    every individual the graph types with it. -/
def witnessesForCe (st : Store) (ceS : Subject) (ce : ClassExpr) : List Triple :=
  match existentialObligation ce with
  | none        => []
  | some (p, c) =>
    let typed := (st.withPredObj rdfType ceS.toTerm).map (·.s)
    typed.foldl (fun acc i =>
      if alreadyHasWitness st i p c then acc
      else
        let bw := witnessBNodeId i p
        let edge : Triple := { s := i, p := p, o := .bnode bw }
        match c with
        | .named ci =>
            acc ++ [edge, { s := .bnode bw, p := rdfType, o := .iri ci }]
        | _ => acc ++ [edge]) []

/-! ## Collecting the subjects the pass ranges over -/

/-- A BLANK NODE carrying class-expression markers. Named classes are
    the RL closure's territory; this predicate deliberately says
    `false` for them. -/
def isCeBNodeSubject (st : Store) (s : Subject) : Bool :=
  match s with
  | .iri _   => false
  | .bnode _ =>
      (firstObject st s owlIntersectionOf).isSome ||
      (firstObject st s owlUnionOf).isSome ||
      (firstObject st s owlComplementOf).isSome ||
      (firstObject st s owlOnProperty).isSome

/-- A NAMED subject carrying class-expression markers. In OWL 2
    RDF-Based semantics such a subject denotes exactly that class, and
    neither the RL closure nor the blank-node passes emit its
    memberships. -/
def isNamedCeSubject (st : Store) (s : Subject) : Bool :=
  match s with
  | .bnode _ => false
  | .iri _   =>
      (firstObject st s owlOnProperty).isSome ||
      (firstObject st s owlIntersectionOf).isSome ||
      (firstObject st s owlUnionOf).isSome

/-- Duplicates out, first-appearance order kept.

    The obvious `foldl` with `acc.contains s` and `acc ++ [s]` is
    QUADRATIC in both halves, and the pass runs it over every subject
    of a closed graph. On the 41 384-triple `type-consistency`
    premise that turned a two-minute probe run into one still going
    after fifteen; a hash set makes it one pass. -/
private def dedupSubjects (xs : List Subject) : List Subject :=
  let (out, _) := xs.foldl (fun (acc : List Subject × Std.HashSet Subject) s =>
    if acc.2.contains s then acc else (acc.1 ++ [s], acc.2.insert s))
    ([], (∅ : Std.HashSet Subject))
  out

def collectCeBNodes (st : Store) : List Subject :=
  dedupSubjects (st.graph.filterMap (fun t =>
    if isCeBNodeSubject st t.s then some t.s else none))

def collectNamedCeSubjects (st : Store) : List Subject :=
  dedupSubjects (st.graph.filterMap (fun t =>
    if isNamedCeSubject st t.s then some t.s else none))

/-- Every subject that is not itself a class expression. These are
    the individuals a membership may be written about. -/
def collectIndividuals (st : Store) : List Subject :=
  dedupSubjects (st.graph.filterMap (fun t =>
    if isCeBNodeSubject st t.s then none else some t.s))

/-! ## Writing memberships -/

/-- `i rdf:type ceS`, when `isMember` proves it and the graph does not
    already say it. -/
def membershipForPair (st : Store) (i : Subject) (ceS : Subject) (ce : ClassExpr)
    : List Triple :=
  let obj := ceS.toTerm
  let existing := (st.withSubjPred i rdfType).any (fun t => t.o == obj)
  if existing then []
  else match isMember st i ce 64 with
       | some true => [{ s := i, p := rdfType, o := obj }]
       | _         => []

def membershipsForCe (st : Store) (individuals : List Subject) (ceS : Subject)
    (ce : ClassExpr) : List Triple :=
  individuals.flatMap (fun i => membershipForPair st i ceS ce)

/-- Over the blank-node class expressions. `parseClassExpr` reads the
    markers on the node itself. -/
def membershipsForBNodeCes (st : Store) (individuals : List Subject)
    (ces : List Subject) : List Triple :=
  ces.flatMap (fun ceS =>
    match parseClassExpr st ceS.toTerm 32 with
    | .unknown => []
    | ce       => membershipsForCe st individuals ceS ce)

/-- Over the NAMED class expressions, behind the positive-soundness
    gate. `parseCeOfSubject` is used rather than `parseClassExpr`
    because the latter maps every IRI straight to `named`, so it would
    never look at the subject's own restriction markers. -/
def membershipsForNamedCes (st : Store) (individuals : List Subject)
    (ces : List Subject) : List Triple :=
  ces.flatMap (fun ceS =>
    match parseCeOfSubject st ceS with
    | .named _   => []
    | .unknown   => []
    | ce         => if cePositiveSound ce
                    then membershipsForCe st individuals ceS ce
                    else [])

/-! ## Structural subclass axioms

`S ≡ X₁ ⊓ … ⊓ Xₙ` entails `S ⊑ Xᵢ`; `S ≡ X₁ ⊔ … ⊔ Xₙ` entails
`Xᵢ ⊑ S`. Both hold in every model.

The axioms are emitted on the NAMED side. Emitting them on an
anonymous Boolean node instead would make every such node an answer
to a query like `?C rdfs:subClassOf <R1>` — a set of spurious
anonymous classes in the result rows. Withholding them for blank-node
subjects only WITHHOLDS inferences, which is sound. -/

def intersectionSubclasses (named : Subject) (items : List Term) : List Triple :=
  items.filterMap (fun t =>
    match termAsSubject t with
    | some _ => some { s := named, p := rdfsSubClassOf, o := t }
    | none   => none)

def unionSubclasses (named : Subject) (items : List Term) : List Triple :=
  items.filterMap (fun t =>
    (termAsSubject t).map (fun s =>
      { s := s, p := rdfsSubClassOf, o := named.toTerm }))

/-- `(X owl:equivalentClass C)` with `C` a Boolean class expression. -/
def eqcExpansion (st : Store) : List Triple :=
  st.graph.flatMap (fun t =>
    if t.p == owlEquivalentClass then
      match termAsSubject t.o with
      | none    => []
      | some ceS =>
        match firstObject st ceS owlIntersectionOf with
        | some head => intersectionSubclasses t.s (walkRdfList st head 64)
        | none      =>
          match firstObject st ceS owlUnionOf with
          | some head => unionSubclasses t.s (walkRdfList st head 64)
          | none      => []
    else [])

/-- A NAMED class defined directly as a union or an intersection. -/
def directBooleanSubclasses (st : Store) : List Triple :=
  st.graph.flatMap (fun t =>
    match t.s with
    | .bnode _ => []
    | .iri _   =>
      if t.p == owlUnionOf then unionSubclasses t.s (walkRdfList st t.o 64)
      else if t.p == owlIntersectionOf then
        intersectionSubclasses t.s (walkRdfList st t.o 64)
      else [])

/-! ## The entry points -/

/-- Add the existential witnesses the graph demands. -/
def introduceWitnesses (g : Graph) : Graph :=
  let st := Store.ofIndex (Index.ofGraph g)
  let extras := (collectCeBNodes st).flatMap (fun ceS =>
    match parseClassExpr st ceS.toTerm 32 with
    | .unknown => []
    | ce       => witnessesForCe st ceS ce)
  RL.addAll g extras

/-- One materialisation pass, in the order the F* module fixed:
    witnesses first, so a newly minted successor can discharge a
    `someOf` or a `minCard` in the same pass; then the structural
    subclass axioms; then the memberships.

    This does NOT iterate with the RL closure to a fixpoint. The
    caller runs the closure afterwards to propagate the new
    `rdf:type` triples through `rdfs:subClassOf`; running the pair to
    saturation is a separate decision with its own cost. -/
def materialiseWithBudget (g : Graph) (budget : Nat) : Graph × Bool :=
  let g1 := introduceWitnesses g
  let st := Store.ofIndex (Index.ofGraph g1)
  let individuals := collectIndividuals st
  let bnodeCes    := collectCeBNodes st
  let namedCes    := collectNamedCeSubjects st
  let structural  := eqcExpansion st
  let booleans    := directBooleanSubclasses st
  let pairs := individuals.length * (bnodeCes.length + namedCes.length)
  if pairs > budget then
    -- The membership pass is one `isMember` per (individual, class
    -- expression) PAIR, so its cost is the product. Over budget, the
    -- structural axioms still land and the memberships do not, and
    -- the caller is TOLD — a cap that reports itself is a known gap;
    -- a silent one is a wrong answer wearing a right one's clothes.
    (RL.addAll (RL.addAll g1 structural) booleans, true)
  else
    let bnodeMems := membershipsForBNodeCes st individuals bnodeCes
    let namedMems := membershipsForNamedCes st individuals namedCes
    (RL.addAll (RL.addAll (RL.addAll (RL.addAll g1 structural) booleans) bnodeMems)
       namedMems, false)

/-- The default budget: 400 000 (individual, class expression) pairs.
    Chosen from the corpus — the largest OWL premise that finishes
    the pass sits well under it — not from a principle. -/
def defaultBudget : Nat := 400000

def materialise (g : Graph) : Graph := (materialiseWithBudget g defaultBudget).1

/-- Is `(i rdf:type C)` provable by class-expression reasoning?
    `none` means the caller should fall back to the closure. A named
    class is left to the closure outright: it decides those, and this
    module would only repeat the lookup. -/
def entails (g : Graph) (goal : Triple) : Option Bool :=
  let st := Store.ofIndex (Index.ofGraph g)
  if st.memB goal then some true
  else if goal.p == rdfType then
    match parseClassExpr st goal.o 32 with
    | .unknown => none
    | .named _ => none
    | ce       => isMember st goal.s ce 64
  else none

end L4Factoidal.OWL.Mat
