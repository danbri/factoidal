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

SCOPE: no backtracking for ambiguous `OneOf` siblings sharing a
predicate, and no recursion through shape references (which needs
negation stratification). Both are stated here rather than implied;
`oneOf` takes the first satisfied branch.
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

/-- The predicates a triple expression MENTIONS — the set `closed`
    measures against. -/
partial def mentionedPredicates : TripleExpr → List String
  | .ref _              => []
  | .tripleConstraint tc => [tc.predicate]
  | .eachOf g | .oneOf g => g.expressions.flatMap mentionedPredicates

/-- Does an arc match a triple constraint's predicate and direction? -/
def arcMatchesPredicate (tc : TripleConstraint) (a : Arc) : Bool :=
  a.predicate == tc.predicate && a.inverse == tc.inverse

/-- Does an arc's value satisfy the constraint's valueExpr?

    Only the non-recursive shape-expression forms are decided here;
    a reference or a nested `shape` is NOT resolved (see the module
    header), and such an arc is treated as NOT matching so it becomes
    leftover rather than being silently accepted. -/
partial def arcSatisfiesValueExpr : Option ShapeExpr → Term → Bool
  | none, _ => true
  | some se, t =>
      match se with
      | .nodeConstraint nc => satisfiesNodeConstraint nc t
      | .shapeAnd es       => es.all (fun e => arcSatisfiesValueExpr (some e) t)
      | .shapeOr es        => es.any (fun e => arcSatisfiesValueExpr (some e) t)
      | .shapeNot e        => !(arcSatisfiesValueExpr (some e) t)
      | .ref _ | .shape _ | .external => false

/-- Split arcs into those a constraint takes and the rest. -/
def partitionForConstraint (tc : TripleConstraint) (arcs : List Arc)
    : List Arc × List Arc :=
  arcs.partition (fun a =>
    arcMatchesPredicate tc a && arcSatisfiesValueExpr tc.valueExpr a.value)

/-- Match one triple expression against a neighbourhood, returning the
    arcs it CONSUMED when it is satisfied. `none` means unsatisfied. -/
partial def matchTripleExpr (te : TripleExpr) (arcs : List Arc) : Option (List Arc) :=
  match te with
  | .ref _ => none          -- unresolved reference: see module header
  | .tripleConstraint tc =>
      let (taken, _) := partitionForConstraint tc arcs
      if tc.satisfiesCard taken.length then some taken else none
  | .eachOf g =>
      -- Every sub-expression must match; each consumes its own arcs.
      g.expressions.foldl (fun acc e =>
        match acc with
        | none => none
        | some consumed =>
            match matchTripleExpr e arcs with
            | none    => none
            | some cs => some (consumed ++ cs)) (some [])
  | .oneOf g =>
      -- First satisfied branch wins; no backtracking (module header).
      g.expressions.findSome? (fun e => matchTripleExpr e arcs)

/-- Is this arc left over after matching — i.e. not consumed? -/
def isLeftover (consumed : List Arc) (a : Arc) : Bool :=
  !(consumed.any (fun c =>
      c.predicate == a.predicate && c.value.eqb a.value && c.inverse == a.inverse))

/-- §satisfies(n, Shape, G).

    Computed in three separate steps, deliberately not fused:
    1. match the expression, obtaining the consumed arcs;
    2. the EXTRA clause — leftover arcs on an `extra` predicate are
       tolerated;
    3. the CLOSED clause — arcs whose predicate the expression never
       mentions are forbidden when `closed`.

    Step 2 never relaxes step 3's mentioned-predicate cardinality, and
    step 3 never grants step 2's leftover tolerance. -/
def satisfiesShape (sh : Shape) (arcs : List Arc) : Bool :=
  let mentioned := match sh.expression with
    | some te => mentionedPredicates te
    | none    => []
  match sh.expression with
  | none =>
      -- No expression: only the CLOSED clause can fail, and with no
      -- mentioned predicates every arc is unmentioned.
      !sh.closed || arcs.isEmpty
  | some te =>
      match matchTripleExpr te arcs with
      | none => false
      | some consumed =>
          let leftover := arcs.filter (isLeftover consumed)
          -- EXTRA: leftover on an extra predicate is fine, regardless
          -- of `closed`.
          let leftoverMentioned := leftover.filter (fun a =>
            mentioned.contains a.predicate && !(sh.extra.contains a.predicate))
          -- CLOSED: arcs on predicates the expression never mentions.
          let unmentioned := arcs.filter (fun a =>
            !(mentioned.contains a.predicate) && !(sh.extra.contains a.predicate))
          leftoverMentioned.isEmpty && (!sh.closed || unmentioned.isEmpty)

/-- Build a node's neighbourhood from a graph. -/
def neighbourhood (triples : List Triple) (node : Term) : List Arc :=
  let fwd := triples.filterMap (fun t =>
    if t.s.toTerm.eqb node then some ⟨t.p.val, t.o, false⟩ else none)
  let inv := triples.filterMap (fun t =>
    if t.o.eqb node then some ⟨t.p.val, t.s.toTerm, true⟩ else none)
  fwd ++ inv

end L4Factoidal.ShEx
