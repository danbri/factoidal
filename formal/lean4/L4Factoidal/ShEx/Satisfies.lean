/-
L4Factoidal.ShEx.Satisfies — `satisfies(n, se, G)` with the schema in
scope, so shape REFERENCES resolve.

`Shapes.lean` decides a shape against a neighbourhood and stops at a
reference: `arcSatisfiesValueExpr` returns `false` for `.ref` and
`.shape`, and `matchTripleExpr` returns `none` for a `TripleExpr.ref`.
Its module header says so. That is the right boundary for a module
that does not have the schema — but the ShEx test suite is largely
made of references, so nothing above it can be scored without this
layer.

The generalisation is one parameter: the value check. Everything else
is the same algorithm, and `Shapes.lean`'s own functions stay exactly
as they are — the EXTRA/CLOSED distinction its header exists to keep
straight is not re-derived here, it is reused.

## Recursion is bounded, and running out is a REFUSAL

A ShEx schema may be recursive (`<S> { <p> @<S> }`), and a recursive
schema against a cyclic graph can walk forever. `fuel` bounds the
depth; exhausting it answers `false`. That is a REFUSAL, not a
verdict, and the runner counts it separately — a schema this layer
declined to decide must not be reported as a validation failure.
-/
import L4Factoidal.ShEx.Shapes

namespace L4Factoidal.ShEx

open L4Factoidal.RDF

/-- A partition parameterised by the value check. -/
def partitionWith (valueOk : Option ShapeExpr → Term → Bool)
    (tc : TripleConstraint) (arcs : List Arc) : List Arc × List Arc :=
  arcs.partition (fun a => arcMatchesPredicate tc a && valueOk tc.valueExpr a.value)

/-- `matchTripleExpr` with the value check supplied. -/
partial def matchTripleExprWith (valueOk : Option ShapeExpr → Term → Bool)
    (te : TripleExpr) (arcs : List Arc) : Option (List Arc) :=
  match te with
  | .ref _ => none
  | .tripleConstraint tc =>
      let (taken, _) := partitionWith valueOk tc arcs
      if tc.satisfiesCard taken.length then some taken else none
  | .eachOf g =>
      g.expressions.foldl (fun acc e =>
        match acc with
        | none => none
        | some consumed =>
            match matchTripleExprWith valueOk e arcs with
            | none    => none
            | some cs => some (consumed ++ cs)) (some [])
  | .oneOf g =>
      g.expressions.findSome? (fun e => matchTripleExprWith valueOk e arcs)

/-- `satisfiesShape` with the value check supplied. The three steps —
    match, EXTRA, CLOSED — are `Shapes.lean`'s, unchanged. -/
def satisfiesShapeWith (valueOk : Option ShapeExpr → Term → Bool)
    (sh : Shape) (arcs : List Arc) : Bool :=
  let mentioned := match sh.expression with
    | some te => mentionedPredicates te
    | none    => []
  match sh.expression with
  | none => !sh.closed || arcs.isEmpty
  | some te =>
      match matchTripleExprWith valueOk te arcs with
      | none => false
      | some consumed =>
          let leftover := arcs.filter (isLeftover consumed)
          let leftoverMentioned := leftover.filter (fun a =>
            mentioned.contains a.predicate && !(sh.extra.contains a.predicate))
          let unmentioned := arcs.filter (fun a =>
            !(mentioned.contains a.predicate) && !(sh.extra.contains a.predicate))
          leftoverMentioned.isEmpty && (!sh.closed || unmentioned.isEmpty)

/-- `satisfies(n, se, G)`. `fuel` bounds reference recursion; running
    out answers `false`, which the caller must read as "declined",
    not as "failed". -/
partial def satisfiesIn (sch : Schema) (g : List Triple)
    : Nat → ShapeExpr → Term → Bool
  | 0,        _,  _ => false
  | fuel + 1, se, n =>
      let valueOk : Option ShapeExpr → Term → Bool := fun ve t =>
        match ve with
        | none    => true
        | some e' => satisfiesIn sch g fuel e' t
      match se with
      | .ref id =>
          (match sch.lookup id with
           | some d => satisfiesIn sch g fuel d.expr n
           | none   => false)
      | .shapeAnd es       => es.all (fun e => satisfiesIn sch g fuel e n)
      | .shapeOr es        => es.any (fun e => satisfiesIn sch g fuel e n)
      | .shapeNot e        => !(satisfiesIn sch g fuel e n)
      | .nodeConstraint nc => satisfiesNodeConstraint nc n
      | .shape sh          => satisfiesShapeWith valueOk sh (neighbourhood g n)
      | .external          => false

/-- How deep a reference chain this layer follows.

    SMALL on purpose. `fuel` is not a step count: every level re-checks
    each arc's value expression, and `eachOf` re-matches each
    sub-expression against the whole neighbourhood, so the work grows
    like a branching factor to the fuel. A first attempt at 24 did not
    finish the 1182-entry suite in ten minutes. The corpus's recursive
    schemas nest a handful of levels, and a chain deeper than this is
    reported as declined rather than waited on. -/
def refDepth : Nat := 6

/-- Validate a focus node against a labelled shape of a schema. -/
def validateNode (sch : Schema) (g : List Triple) (label : String) (n : Term) : Bool :=
  match sch.lookup label with
  | some d => satisfiesIn sch g refDepth d.expr n
  | none   => false

/-- Validate a focus node against the schema's START shape.

    A manifest entry with no `shape` names the start shape, which is a
    shape EXPRESSION and not a label: `Schema.lookup ""` cannot find
    it and answered `false` for every such entry. -/
def validateStart (sch : Schema) (g : List Triple) (n : Term) : Bool :=
  match sch.start with
  | some se => satisfiesIn sch g refDepth se n
  | none    => false

end L4Factoidal.ShEx
