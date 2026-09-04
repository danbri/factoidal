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
* `maxCard` / `exactCard` / `maxQualCard` / `exactQualCard` — in
  general a positive membership needs `owl:sameAs` reasoning or a
  unique-name assumption, and this module has neither. ⚠️ ONE
  EXCEPTION is proved and does not need either: if `i` is in
  `∀ p. {a₁ … a_m}` then every `p`-filler of `i` is one of `m` named
  individuals, so `i` has at most `m` DISTINCT `p`-fillers whatever
  the graph asserts. `fillerBoundAtMost` reads that bound and
  `isMember` uses it for `maxCard` and `maxQualCard`. The gate still
  refuses the SHAPE, because a shape cannot say whether a bound
  exists; the answer is available to a direct caller.
  ⚠️ Note also that the `k = 0` answers here are NOT entailments —
  they read an empty search as a proof, which the open world
  assumption does not allow. The gate is what keeps them out of the
  graph. See the checks in `MaterialiseTests`;
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

/-- One class expression PROVABLY entails another, by the rules this
module can justify from the graph: syntactic equality; named
subsumption asserted (or closure-derived) as `rdfs:subClassOf`; and a
named class inside the complement of a class it is declared
`owl:disjointWith`. `false` is "not proved here", never "false". -/
partial def ceEntailsCe (st : Store) (c1 c2 : ClassExpr) : Bool :=
  if ClassExpr.beq c1 c2 then true
  else match c1, c2 with
  | .named a, .named b =>
      (st.withSubjPred (.iri a) rdfsSubClassOf).any (fun t => t.o == Term.iri b)
  | .named a, .complement (.named w) =>
      (st.withSubjPred (.iri a) owlDisjointWith).any
        (fun t => t.o == Term.iri w) ||
      (st.withSubjPred (.iri w) owlDisjointWith).any
        (fun t => t.o == Term.iri a)
  | _, _ => false

/-- The class expressions PROVABLY above a named class `c`: the
objects of its `rdfs:subClassOf` and `owl:equivalentClass` triples
(and the subjects of reverse `owl:equivalentClass` triples), read
back through `parseClassExpr`, followed recursively through further
NAMED classes. Sound because `i ∈ C` with `C ⊑ D` or `C ≡ D` gives
`i ∈ D`. Fuel bounds the recursion. -/
partial def namedSuperCEs (st : Store) (c : WfIri) (fuel : Nat)
    : List ClassExpr :=
  match fuel with
  | 0 => []
  | n + 1 =>
    let ups : List Term :=
      (st.withSubjPred (.iri c) rdfsSubClassOf).map (·.o) ++
      (st.withSubjPred (.iri c) owlEquivalentClass).map (·.o) ++
      (st.withPredObj owlEquivalentClass (Term.iri c)).map (·.s.toTerm)
    ups.flatMap (fun u =>
      let ce := parseClassExpr st u n
      ce :: (match ce with
             | .named c2 => if c2 == c then [] else namedSuperCEs st c2 n
             | _ => []))

/-- The class expressions of `i`'s asserted (or closure-derived)
types, read back through `parseClassExpr` — each named type expanded
through `rdfs:subClassOf` / `owl:equivalentClass` to the class
expressions provably above it. -/
def typeCEsOf (st : Store) (i : Subject) (fuel : Nat) : List ClassExpr :=
  (st.withSubjPred i rdfType).flatMap (fun t =>
    let ce := parseClassExpr st t.o fuel
    ce :: (match ce with
           | .named c => namedSuperCEs st c (min fuel 8)
           | _ => []))


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
    | .someOf p c =>
        match anyIsMember st (successors st i p) c n with
        | some true => some true
        | r =>
            -- A type of `i` that is itself `∃ p. c'` with `c' ⊑ c`
            -- proves membership with no witness edge: the existential
            -- is inherited through the filler subsumption.
            if (typeCEsOf st i n).any (fun tce =>
                 match tce with
                 | .someOf q c' => q == p && ceEntailsCe st c' c
                 | .hasValue q _ =>
                     -- the filler's class is unknown, so this is sound
                     -- only against the top class
                     q == p && (match c with
                                | .named cn => cn == owlThing
                                | _ => false)
                 | _ => false)
            then some true else r

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
    | .minCard k p =>
        if (successors st i p).length ≥ k then some true
        -- `∃ p. c` and `∋ p. v` each entail at least one `p`-filler.
        else if k ≤ 1 && (typeCEsOf st i n).any (fun tce =>
               match tce with
               | .someOf q _ => q == p
               | .hasValue q _ => q == p
               | _ => false)
        then some true else none

    -- `≤ k p` and `= k p`. Two ways to prove one, and no others:
    -- `k = 0` with no known successor, or a FILLER BOUND — `i` is in
    -- some `∀ p. {a₁ … a_m}` with `m ≤ k`, so it cannot have more
    -- than `k` distinct `p`-fillers whatever else the graph says.
    -- Anything else needs the provable-distinctness machinery of the
    -- refutation calculus.
    | .maxCard k p =>
        if k == 0 && (successors st i p).isEmpty then some true
        else if fillerBoundAtMost st i p k n then some true else none
    | .exactCard k p =>
        if k == 0 && (successors st i p).isEmpty then some true else none

    | .minQualCard k p c =>
        if countQualSuccessors st (successors st i p) c n ≥ k then some true else none
    -- A filler bound carries to the qualified form: at most `k`
    -- `p`-fillers in total is at most `k` of them in `c`, for any `c`.
    | .maxQualCard k p c =>
        if k == 0 && countQualSuccessors st (successors st i p) c n == 0
        then some true
        else if fillerBoundAtMost st i p k n then some true else none
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

/-- Is there a proof that `i` has AT MOST `k` distinct `p`-fillers?

    One sound source, and the only one this module reads: `i` is in a
    universal restriction `∀ p. {a₁ … a_m}` with `m ≤ k`. Every
    `p`-filler of `i` is then one of the `m` listed individuals, and a
    set of `m` things cannot hold more than `m` distinct things. The
    conclusion needs no distinctness reasoning and holds however many
    `p`-edges the graph asserts — including none.

    `false` means "not proved here", never "false". -/
partial def fillerBoundAtMost (st : Store) (i : Subject) (p : WfIri) (k : Nat)
    (fuel : Nat) : Bool :=
  (successors st i rdfType).any (fun t =>
    match parseClassExpr st t fuel with
    | .allOf q (.oneOf members) => q == p && members.length ≤ k
    | _ => false)

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

/-- The printed name of a subject, for use inside a minted blank-node
    identifier. -/
def subjectKey : Subject -> String
  | .iri s   => s.val
  | .bnode b => b

/-- The witness blank node for the obligation `ceS` puts on `(i, p)`.

    The identifier carries `ceS`, the class expression that RAISED the
    obligation, and not only the pair `(i, p)`. Two different
    existence obligations on ONE property must not be discharged by
    one filler: `p1 ⊑ ∃r.A` and `p2 ⊑ ∃r.B` oblige an `r`-successor in
    `A` and an `r`-successor in `B`, and nothing obliges those two
    successors to be the same individual unless `r` is functional.
    `Refute.lean` states the same rule for the tableau beside
    `existsUnsatisfiableWitness`; this pass writes into the graph, so
    it must obey it too. Keying on `(i, p)` alone made ONE node carry
    every filler class of every `r`-obligation, which is the ⊓ of
    them, and on `WebOnt-description-logic-018` / `-020` / `-021` —
    all three asserted CONSISTENT — that intersection met a
    `owl:complementOf` pair and cls-com reported a clash that the
    premise does not have (OWL 2 Direct Semantics §2.2, the
    interpretation of `ObjectSomeValuesFrom`).

    Deterministic, so re-running the pass mints the same node rather
    than a second one. -/
def witnessBNodeId (i : Subject) (p : WfIri) (ceS : Subject) : BNodeId :=
  "_:bw_" ++ subjectKey i ++ "__" ++ p.val ++ "__" ++ subjectKey ceS

/-- Does `i` already have a `p`-successor that discharges the
    obligation? An UNQUALIFIED obligation (`ClassExpr.unknown` as the
    filler) is discharged by any successor at all. -/
def alreadyHasWitness (st : Store) (i : Subject) (p : WfIri) (c : ClassExpr)
    : Bool :=
  let succs := successors st i p
  match c with
  | .unknown => !succs.isEmpty
  | _        => anyIsMember st succs c 32 == some true

/-- The at-most bound this class expression puts on `p`, if any. -/
def maxBoundOn (p : WfIri) : ClassExpr → Option Nat
  | .maxCard k q        => if q == p then some k else none
  | .exactCard k q      => if q == p then some k else none
  | .maxQualCard k q _  => if q == p then some k else none
  | .exactQualCard k q _ => if q == p then some k else none
  | _                   => none

/-- Would minting a `p`-witness for `i` push it past an at-most bound
    `i` already carries?

    A witness is a MODEL-CONSTRUCTION device: it may coincide with an
    existing successor, so it must never be counted against a
    cardinality bound. The tableau states that rule for itself, but
    this pass writes its witness INTO THE GRAPH, and the RL clash
    detector downstream counts blank nodes like any other name. On
    `WebOnt-description-logic-018` / `-020` / `-021` — three premises
    the catalog asserts CONSISTENT — that counted witness fired the
    clash detector against a bound the individual's REAL successors
    do not exceed.

    Withholding the witness where a bound could be breached fixes it
    without hiding the witness from the pass that needs it. Stripping
    every witness edge from the output was tried instead and measured
    WORSE: it cost ten `type-inconsistency` passes and five across
    the profile catalogs to save these three, because the closure's
    clash detection does real work on the witnesses it can count
    soundly.

    `mintedHere` is the number of `p`-witnesses THIS pass has already
    minted for `i` and which are therefore not yet in `st`. One
    witness per obligation means several obligations on one property
    mint several successors, and the bound must count them all; a
    check that reads only `st` would let three obligations each pass
    a max-1 bound. -/
def witnessBreachesBound (st : Store) (i : Subject) (p : WfIri)
    (mintedHere : Nat) : Bool :=
  let have' := (successors st i p).length + mintedHere
  let functional :=
    (st.withSubjPred (.iri p) rdfType).any (fun t => t.o == Term.iri owlFunctionalProperty)
  let bounds := (st.withSubjPred i rdfType).filterMap (fun t =>
    maxBoundOn p (parseClassExpr st t.o 32))
  (functional && have' ≥ 1) || bounds.any (fun k => have' ≥ k)

/-- How many `(i, p)`-witnesses this pass has minted already. -/
def mintedCount (minted : List (Subject × WfIri)) (i : Subject) (p : WfIri)
    : Nat :=
  (minted.filter (fun q => q.1 == i && q.2 == p)).length

/-- The witness triples one existential class expression demands, over
    every individual the graph types with it. `minted` carries the
    `(individual, property)` pairs this pass has already witnessed, so
    a later obligation on the same property counts them against the
    at-most bounds. -/
def witnessesForCe (st : Store) (minted : List (Subject × WfIri))
    (ceS : Subject) (ce : ClassExpr) : List Triple × List (Subject × WfIri) :=
  match existentialObligation ce with
  | none        => ([], minted)
  | some (p, c) =>
    let typed := (st.withPredObj rdfType ceS.toTerm).map (·.s)
    typed.foldl (fun (acc : List Triple × List (Subject × WfIri)) i =>
      let (ts, m) := acc
      if alreadyHasWitness st i p c
         || witnessBreachesBound st i p (mintedCount m i p) then acc
      else
        let bw := witnessBNodeId i p ceS
        let edge : Triple := { s := i, p := p, o := .bnode bw }
        let ts' := match c with
          | .named ci => ts ++ [edge, { s := .bnode bw, p := rdfType, o := .iri ci }]
          | _         => ts ++ [edge]
        (ts', (i, p) :: m)) ([], minted)

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

/-- The individuals that could possibly satisfy `ce`, from the index
    rather than by trying them all.

    Every shape the positive-soundness gate admits, except an empty
    `minCard`, REQUIRES an edge or an assertion — `∃p.C` and
    `≥ k p` (k ≥ 1) need a `p`-edge, `hasValue p v` needs the edge
    `(· p v)` itself. An individual without one cannot be a member,
    so `isMember` would answer `none` for it after doing the lookup
    anyway.

    This is a pure speed restriction: it removes calls whose answer
    is already known, never a call that could have said `some true`.
    Trying every individual against every class expression is the
    product that made the pass the slowest thing in the probe. -/
partial def candidatesFor (st : Store) (ce : ClassExpr) (individuals : List Subject)
    : List Subject :=
  let withEdge (p : WfIri) : List Subject :=
    ((st.withPred p).map (·.s)).eraseDups.filter (individuals.contains ·)
  match ce with
  | .hasValue p v   => ((st.withPredObj p v).map (·.s)).eraseDups.filter
                         (individuals.contains ·)
  | .someOf p _     => withEdge p
  | .minCard k p    => if k == 0 then individuals else withEdge p
  | .minQualCard k p _ => if k == 0 then individuals else withEdge p
  -- Every conjunct must hold, so the smallest conjunct's candidate
  -- set already bounds the intersection.
  | .intersection cs =>
      cs.foldl (fun acc c =>
        let here := candidatesFor st c individuals
        if here.length < acc.length then here else acc) individuals
  -- One disjunct is enough, so the candidates are the union.
  | .union cs => (cs.flatMap (fun c => candidatesFor st c individuals)).eraseDups
  | _ => individuals

/-- Over the blank-node class expressions. `parseClassExpr` reads the
    markers on the node itself.

    The positive-soundness gate applies HERE TOO, not only to the
    named pass. `∀p.C` is `some true` for an individual with no known
    `p`-successor — vacuously — but that membership is not ENTAILED:
    an unseen successor could violate the filler. Writing it puts a
    triple into the graph that the closure then propagates through
    `rdfs:subClassOf`, so one unentailed membership becomes a set of
    unentailed conclusions. The F* module gates only its named pass;
    gating both is the stricter reading, and it is the one that keeps
    `materialise`'s output entailed by its input. -/
def membershipsForBNodeCes (st : Store) (individuals : List Subject)
    (ces : List Subject) : List Triple :=
  ces.flatMap (fun ceS =>
    match parseClassExpr st ceS.toTerm 32 with
    | .unknown => []
    | ce       => if cePositiveSound ce
                  then membershipsForCe st (candidatesFor st ce individuals) ceS ce
                  else [])

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
                    then membershipsForCe st (candidatesFor st ce individuals) ceS ce
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
  let extras := ((collectCeBNodes st).foldl
    (fun (acc : List Triple × List (Subject × WfIri)) ceS =>
      let (ts, m) := acc
      match parseClassExpr st ceS.toTerm 32 with
      | .unknown => acc
      | ce       =>
        let (ts', m') := witnessesForCe st m ceS ce
        (ts ++ ts', m')) ([], [])).1
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
