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

The generalisation is two parameters: the value check, and the lookup
that resolves a triple-expression inclusion (`&<label>`). Everything
else is the same algorithm — `Shapes.satisfiesShapeGen` is called with
both supplied, so the partition search and the EXTRA/CLOSED
distinction its header exists to keep straight are reused, not
re-derived.

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

/-! ## Resolving a triple-expression INCLUSION

`&<label>` names a triple expression declared elsewhere in the schema,
by an `id` on a `TripleConstraint`, an `EachOf` or a `OneOf`.
`Shapes.matchStates` takes the lookup as a parameter because the
schema is not in scope there; here it is, so the search below walks
every shape declaration for the label. `TripleExpr.ref` used to answer
`none` from the matcher, which reads as UNSATISFIED — an inclusion was
scored as a failed shape.
-/

mutual

/-- The triple expression with this `id` inside a shape expression. -/
partial def findTeInShapeExpr (id : String) : ShapeExpr → Option TripleExpr
  | .shape sh    => sh.expression.bind (findTeInTripleExpr id)
  | .shapeAnd es => es.findSome? (findTeInShapeExpr id)
  | .shapeOr es  => es.findSome? (findTeInShapeExpr id)
  | .shapeNot e  => findTeInShapeExpr id e
  | _            => none

/-- The triple expression with this `id` inside a triple expression. -/
partial def findTeInTripleExpr (id : String) : TripleExpr → Option TripleExpr
  | te@(.tripleConstraint tc) =>
      if tc.id == some id then some te
      else tc.valueExpr.bind (findTeInShapeExpr id)
  | te@(.eachOf g) =>
      if g.id == some id then some te
      else g.expressions.findSome? (findTeInTripleExpr id)
  | te@(.oneOf g) =>
      if g.id == some id then some te
      else g.expressions.findSome? (findTeInTripleExpr id)
  | .ref _ => none

end

/-- Resolve a triple-expression label declared anywhere in the schema. -/
def Schema.tripleExpr (sch : Schema) (id : String) : Option TripleExpr :=
  sch.shapes.findSome? (fun d => findTeInShapeExpr id d.expr)

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
      | .shape sh          =>
          satisfiesShapeGen valueOk sch.tripleExpr sh (neighbourhood g n)
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
