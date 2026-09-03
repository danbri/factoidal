/-
L4Factoidal.ShEx.Shapes — shape satisfaction over a neighbourhood,
ported from `formal/fstar/ShEx.Validation.fst`.

Spec: ShEx 2.1 Semantics `satisfies(n, Shape, G)` — matching a node's
neighbourhood against a triple expression, then the CLOSED and EXTRA
clauses.

THE DISTINCTION THIS MODULE EXISTS TO KEEP STRAIGHT, and which the F*
module records as an actual bug caught during its own measurement
run: `extra` and `closed` are two DIFFERENT clauses.

* `extra p` tolerates leftover triples on predicate `p` — ones not
  taken by a TripleConstraint's [min,max] set, or whose valueExpr
  failed — REGARDLESS of `closed`.
* `closed` bounds only triples whose predicate the expression does
  NOT mention at all. It NEVER relaxes a mentioned predicate's own
  cardinality.

Conflating them ("not closed" also granting a mentioned predicate's
leftover tolerance) is the bug. The two are computed separately below
and never share a branch.

SCOPE: no recursion through shape references — `arcSatisfiesValueExpr`
fails an unresolved reference and `satisfiesShape` resolves no
inclusion, because neither is decidable without the schema.
`L4Factoidal.ShEx.Satisfies` supplies both and reuses the matcher
below unchanged.
-/
import L4Factoidal.ShEx.Validation

namespace L4Factoidal.ShEx

open L4Factoidal.RDF

/-- An arc in the node's neighbourhood: the predicate and the term at
    the far end. Forward arcs come from triples with the node as
    subject, inverse arcs from triples with it as object. -/
structure Arc where
  predicate : String
  value     : Term
  inverse   : Bool := false
deriving Repr

mutual

/-- The predicates a triple expression MENTIONS — the set `closed`
    measures against. -/
def mentionedPredicates : TripleExpr → List String
  | .ref _              => []
  | .tripleConstraint (.mk _ _ p _ _ _ _ _) => [p]
  | .eachOf (.mk _ ges _ _ _ _) | .oneOf (.mk _ ges _ _ _ _) =>
      mentionedPredicatesList ges

/-- `flatMap` written out: the higher-order form hides the decrease. -/
def mentionedPredicatesList : List TripleExpr → List String
  | []     => []
  | e :: r => mentionedPredicates e ++ mentionedPredicatesList r

end

/-- Does an arc match a triple constraint's predicate and direction? -/
def arcMatchesPredicate (tc : TripleConstraint) (a : Arc) : Bool :=
  a.predicate == tc.predicate && a.inverse == tc.inverse

/-! Does an arc's value satisfy the constraint's valueExpr?

Only the non-recursive shape-expression forms are decided here;
a reference or a nested `shape` is NOT resolved (see the module
header), and such an arc is treated as NOT matching so it becomes
leftover rather than being silently accepted. -/

mutual

/-- Decide a shape expression against a term. -/
def arcSatisfiesShapeExpr : ShapeExpr → Term → Bool
  | .nodeConstraint nc, t => satisfiesNodeConstraint nc t
  | .shapeAnd es, t       => arcSatisfiesAll es t
  | .shapeOr es, t        => arcSatisfiesAny es t
  | .shapeNot e, t        => !(arcSatisfiesShapeExpr e t)
  | .ref _, _ | .shape _, _ | .external, _ => false

/-- `List.all` written out. -/
def arcSatisfiesAll : List ShapeExpr → Term → Bool
  | [], _     => true
  | e :: r, t => arcSatisfiesShapeExpr e t && arcSatisfiesAll r t

/-- `List.any` written out. -/
def arcSatisfiesAny : List ShapeExpr → Term → Bool
  | [], _     => false
  | e :: r, t => arcSatisfiesShapeExpr e t || arcSatisfiesAny r t

end

def arcSatisfiesValueExpr : Option ShapeExpr → Term → Bool
  | none, _    => true
  | some se, t => arcSatisfiesShapeExpr se t

/-! ## Matching a triple expression is a PARTITION, not a filter

ShEx 2.1 §5.6: a triple expression matches a SET of triples, and the
sub-expressions of an `EachOf` match DISJOINT subsets of it. The
implementation this replaced matched every sub-expression against the
whole neighbourhood and concatenated what each one took, which is the
SHACL reading — a property shape FILTERS the neighbourhood and its
siblings see the same triples again. `<S> { :a .*; (:a .+ | :a .); :a . }`
has three constraints on `:a`; under the filter reading each sees every
`:a` arc and none removes what it took, so no partition is ever
attempted, and the shape is reported unsatisfied for graphs that
satisfy it.

The search below is over SETS of arcs. An arc is named by its position
in the neighbourhood, a STATE is the set of positions still available,
and a triple expression maps a state to the states that can follow it.
A shape is satisfied when SOME resulting state passes the EXTRA and
CLOSED clauses. Duplicate states are removed after every step, which
bounds the search by the number of SUBSETS of the neighbourhood rather
than by the number of ways of reaching them.

## Interpretation choices recorded here (2026-08-26)

ShEx 2.1 states satisfaction EXISTENTIALLY — there exists a matching
of the neighbourhood — and says nothing about how to find one. Three
readings follow from that and are taken here:

1. **The search is exhaustive.** `OneOf` backtracks into its later
   branches, and a `TripleConstraint` may take ANY subset of the arcs
   it could take, not the greedy maximum. A greedy matcher answers
   "does not conform" for schemas that do conform.
2. **A group's own cardinality is a repeat of the whole group.**
   `Group.min` / `Group.max` were parsed into the AST and then never
   read, so `( <p1> . | <p2> . ){2}` was matched as if the `{2}` were
   absent. `repeatMatch` below applies it.
3. **A repetition that consumes nothing does not extend the search.**
   With an unbounded upper bound the repeat count is capped at the
   number of available arcs, because a repetition consuming no arc
   leaves the state it started from, which is already in the result.

4. **CLOSED and EXTRA are clauses about `arcsOut`.** ShEx 2.1 §5.5
   bounds `closed` by the triples whose SUBJECT is the focus node; an
   arc reached through `arcsIn` is neither closed out nor in need of
   an `extra` licence, and a leftover inverse arc is tolerated
   unconditionally. `F*`'s `ShEx.Validation.fst:1438` writes the same
   rule as `inv || List.Tot.mem pred extra`. Treating an inverse arc
   as a mentioned-predicate leftover failed every reflexive graph in
   the corpus: `<S1> { <p1> @<S2> }` against `<n1> <p1> <n1>` puts the
   SAME triple in the neighbourhood twice, once forward and once
   inverse, and the inverse copy was scored as an unconsumed `<p1>`.
5. **A constraint's direction is part of the predicate key.** A
   forward constraint on `<p1>` does not mention the inverse `<p1>`
   arc, so `mentionedPairsWith` keys on `(inverse, predicate)`.

An inclusion (`&<label>`) is resolved by the `lookupTe` parameter; a
CYCLIC inclusion would not terminate, and ShEx 2.1 §5.6 forbids one.
-/

/-- Every order-preserving sublist of `xs`. -/
def sublistsOf : List Nat → List (List Nat)
  | []     => [[]]
  | x :: r => let rs := sublistsOf r
              rs.map (fun s => x :: s) ++ rs

/-- States are sets of positions, always written in increasing order,
    so list equality is set equality. -/
def dedupStates (ss : List (List Nat)) : List (List Nat) := ss.eraseDups

/-- The repeat bounds a group carries. ShExJ omits `min` and `max`
    when they are 1; `max = -1` is UNBOUNDED. -/
def groupBounds (g : Group) : Nat × Option Nat :=
  let lo := match g.min with | some m => m.toNat | none => 1
  let hi := match g.max with
    | some m => if m < 0 then none else some m.toNat
    | none   => some 1
  (lo, hi)

/-- The bounds a triple constraint carries. -/
def tcBounds (tc : TripleConstraint) : Nat × Option Nat :=
  (tc.min.toNat, if tc.unbounded then none else some tc.max.toNat)

/-- Repeat a one-shot matcher between `lo` and `hi` times, collecting
    every state a permitted number of repetitions can leave. -/
def repeatMatch (f : List Nat → List (List Nat)) (lo : Nat) (hi : Option Nat)
    (avail : List Nat) : List (List Nat) :=
  let cap := match hi with
    | some h => h
    | none   => Nat.max lo avail.length
  let step := fun (sa : List (List Nat) × List (List Nat)) (k : Nat) =>
    let next := dedupStates (sa.1.flatMap f)
    (next, if k + 1 ≥ lo then dedupStates (sa.2 ++ next) else sa.2)
  ((List.range cap).foldl step ([avail], if lo == 0 then [avail] else [])).2

/-- The states a triple expression can leave behind.

    `valueOk` decides a value expression and `lookupTe` resolves an
    inclusion; neither is decidable without the schema, so both are
    supplied by the caller. -/
partial def matchStates (valueOk : Option ShapeExpr → Term → Bool)
    (lookupTe : String → Option TripleExpr) (arr : Array Arc)
    (te : TripleExpr) (avail : List Nat) : List (List Nat) :=
  match te with
  | .ref id =>
      match lookupTe id with
      | some te' => matchStates valueOk lookupTe arr te' avail
      | none     => []
  | .tripleConstraint tc =>
      if anySemActFails tc.semActs then [] else
      let cands := avail.filter (fun i =>
        match arr[i]? with
        | some a => arcMatchesPredicate tc a && valueOk tc.valueExpr a.value
        | none   => false)
      let (lo, hi) := tcBounds tc
      dedupStates (((sublistsOf cands).filter (fun s =>
          lo ≤ s.length && hi.all (fun h => s.length ≤ h))).map (fun s =>
            avail.filter (fun i => !(s.contains i))))
  | .eachOf g =>
      let (lo, hi) := groupBounds g
      repeatMatch (fun av =>
        g.expressions.foldl (fun states e =>
          dedupStates (states.flatMap (matchStates valueOk lookupTe arr e))) [av]) lo hi avail
  | .oneOf g =>
      let (lo, hi) := groupBounds g
      repeatMatch (fun av =>
        dedupStates (g.expressions.flatMap (fun e =>
          matchStates valueOk lookupTe arr e av))) lo hi avail

/-- Every triple constraint a triple expression contains, FOLLOWING
    inclusions. -/
partial def tripleConstraintsWith (lookupTe : String → Option TripleExpr)
    : TripleExpr → List TripleConstraint
  | .ref id => (match lookupTe id with
                | some te => tripleConstraintsWith lookupTe te
                | none    => [])
  | .tripleConstraint tc => [tc]
  | .eachOf g | .oneOf g => g.expressions.flatMap (tripleConstraintsWith lookupTe)

/-- The (inverse, predicate) pairs a triple expression mentions,
    FOLLOWING inclusions.

    The DIRECTION belongs in the key. A forward constraint on `<p1>`
    cannot match an INVERSE arc on `<p1>`, so an expression that
    mentions only the forward one does not mention the inverse one. -/
def mentionedPairsWith (lookupTe : String → Option TripleExpr)
    (te : TripleExpr) : List (Bool × String) :=
  (tripleConstraintsWith lookupTe te).map (fun tc => (tc.inverse, tc.predicate))

/-- §satisfies(n, Shape, G), with the value check and the inclusion
    lookup supplied.

    Computed in three separate steps, deliberately not fused:
    1. the CLOSED clause — arcs whose predicate the expression never
       mentions are forbidden when `closed`;
    2. match the expression, obtaining the states it can leave;
    3. the EXTRA clause — a LEFTOVER arc on a mentioned predicate
       fails unless that predicate is `extra`.

    Step 3 never relaxes step 1's unmentioned-predicate rule, and step
    1 never grants step 3's leftover tolerance. Conflating them ("not
    closed" also granting a mentioned predicate's leftover tolerance)
    is the bug the F* module records from its own measurement run.

    INTERPRETATION RECORDED (2026-08-26): `extra` never launders a
    cardinality OVER-RUN. A leftover arc on an `extra` predicate is
    tolerated when it FAILS every triple constraint on its own
    (inverse, predicate) pair, and also when the match consumed no arc
    on that pair at all. It is NOT tolerated when it satisfies a
    constraint AND the match already took another arc on the same
    pair — that is an over-count wearing `extra` as a disguise.

    The two cases this separates, both settled against the F* engine
    (`bin/linux-x86_64/factoidal shex`, which scores 1182 pass, 0 fail
    on this corpus):

    * `EXTRA <p1> { <p1> . }` against two `<p1>` arcs is FALSE. The
      constraint takes one, the second satisfies the same constraint,
      and an arc was consumed on that pair.
    * `EXTRA <q> { <p> . | <q> . }` against one `<p>` and one `<q>`
      arc is TRUE. With the `<p>` branch chosen, nothing was consumed
      on `<q>`, so the `<q>` arc is a genuine extra and not an
      over-run of a constraint that ran.

    The F* module reaches the same place from the other side, by
    asking whether a sibling constraint on the same pair could have
    claimed the arc instead (`ambiguous_pairs_of`,
    `ShEx.Validation.fst:925`); with the exhaustive search here that
    sibling simply takes it, so no arc it could have taken is ever
    leftover. -/
def satisfiesShapeGen (valueOk : Option ShapeExpr → Term → Bool)
    (lookupTe : String → Option TripleExpr) (sh : Shape) (arcs : List Arc) : Bool :=
  if anySemActFails sh.semActs then false else
  match sh.expression with
  | none => !sh.closed || arcs.isEmpty
  | some te =>
      let mentioned := mentionedPairsWith lookupTe te
      let constraints := tripleConstraintsWith lookupTe te
      -- Would some constraint of this expression accept this arc?
      let claimable := fun (a : Arc) => constraints.any (fun tc =>
        arcMatchesPredicate tc a && valueOk tc.valueExpr a.value)
      -- CLOSED and EXTRA are clauses about arcsOut. An INVERSE arc is
      -- neither closed out nor in need of an `extra` licence.
      let unmentioned := arcs.filter (fun a =>
        !a.inverse && !(mentioned.contains (false, a.predicate))
          && !(sh.extra.contains a.predicate))
      if sh.closed && !unmentioned.isEmpty then false
      else
        let arr := arcs.toArray
        let states := matchStates valueOk lookupTe arr te (List.range arcs.length)
        states.any (fun rest =>
          let leftover := rest.filterMap (fun i => arr[i]?)
          let consumed := (List.range arcs.length).filter (fun i => !(rest.contains i))
            |>.filterMap (fun i => arr[i]?)
          leftover.all (fun a =>
            a.inverse
            || !(mentioned.contains (false, a.predicate))
            || (sh.extra.contains a.predicate
                && (!(claimable a)
                    || !(consumed.any (fun c =>
                           c.predicate == a.predicate && c.inverse == a.inverse))))))

/-- §satisfies(n, Shape, G) with no schema: an unresolved value
    expression fails, and an inclusion resolves to nothing. -/
def satisfiesShape (sh : Shape) (arcs : List Arc) : Bool :=
  satisfiesShapeGen arcSatisfiesValueExpr (fun _ => none) sh arcs

/-- Build a node's neighbourhood from a graph. -/
def neighbourhood (triples : List Triple) (node : Term) : List Arc :=
  let fwd := triples.filterMap (fun t =>
    if t.s.toTerm.eqb node then some ⟨t.p.val, t.o, false⟩ else none)
  let inv := triples.filterMap (fun t =>
    if t.o.eqb node then some ⟨t.p.val, t.s.toTerm, true⟩ else none)
  fwd ++ inv

end L4Factoidal.ShEx
