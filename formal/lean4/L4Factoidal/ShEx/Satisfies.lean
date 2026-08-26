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

## Recursion terminates on the (label, node) pair, not on fuel

A ShEx schema may be recursive (`<S> { <p> @<S> }`), and a recursive
schema against a cyclic graph can walk forever.

This module used to bound the walk with a fuel counter, `refDepth = 6`,
and answer `false` when it ran out. Its header called that a REFUSAL
and said "the runner counts it separately". **The runner did no such
thing**: `validateNode` returned a `Bool`, `Harness/ShExRun.lean`
compared it against the expected verdict, and there was no declined
column anywhere. Sixteen entries of the validation suite were scored
as validation failures for running out of fuel — including
`<S1> { <p1> BNODE @<S1> OR MINLENGTH 20 @<S1> }` against a reflexive
triple, the three-cycle `S1 → S2 → S3 → S1`, and `1list0PlusDot`
walking a three-element RDF list, which needs depth 8. A cap that
answers a question it did not decide is a wrong answer, and a comment
claiming someone else counts it is worse than no comment.

The bound is now the (shape label, focus node) pair. `satisfiesIn`
carries the pairs already being decided further up the stack; entering
`@<S>` for a node already on the stack ASSUMES the shape holds of it
and returns `true`. Every `.ref` step either returns at once or adds a
new pair, and the pairs come from the schema's labels crossed with the
graph's terms, so the walk terminates with no cap to exhaust. Nothing
is refused, and no declined column is needed.

**The assumption is the GREATEST fixpoint reading**, and it is sound
only for a schema whose recursion does not pass through `ShapeNot`
(negation stratification, ShEx 2.1 §5.9). This module does not check
that condition. A schema that violates it gets the greatest-fixpoint
answer, which may differ from the least-fixpoint one; the corpus
contains no such schema.
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

/-- `satisfies(n, se, G)`.

    `visited` carries the (shape label, node) pairs already being
    decided further up the stack. Re-entering one ASSUMES it holds —
    see the module header for why, and for the stratification
    condition that makes the assumption sound. -/
partial def satisfiesIn (sch : Schema) (g : List Triple)
    (visited : List (String × Term)) (se : ShapeExpr) (n : Term) : Bool :=
  let valueOk : Option ShapeExpr → Term → Bool := fun ve t =>
    match ve with
    | none    => true
    | some e' => satisfiesIn sch g visited e' t
  match se with
  | .ref id =>
      if visited.contains (id, n) then true
      else
        (match sch.lookup id with
         | some d => satisfiesIn sch g ((id, n) :: visited) d.expr n
         | none   => false)
  | .shapeAnd es       => es.all (fun e => satisfiesIn sch g visited e n)
  | .shapeOr es        => es.any (fun e => satisfiesIn sch g visited e n)
  | .shapeNot e        => !(satisfiesIn sch g visited e n)
  | .nodeConstraint nc => satisfiesNodeConstraint nc n
  | .shape sh          =>
      satisfiesShapeGen valueOk sch.tripleExpr sh (neighbourhood g n)
  | .external          => false

/-- Validate a focus node against a labelled shape of a schema. -/
def validateNode (sch : Schema) (g : List Triple) (label : String) (n : Term) : Bool :=
  match sch.lookup label with
  | some d => satisfiesIn sch g [(label, n)] d.expr n
  | none   => false

/-- Validate a focus node against the schema's START shape.

    A manifest entry with no `shape` names the start shape, which is a
    shape EXPRESSION and not a label: `Schema.lookup ""` cannot find
    it and answered `false` for every such entry. -/
def validateStart (sch : Schema) (g : List Triple) (n : Term) : Bool :=
  match sch.start with
  | some se => satisfiesIn sch g [] se n
  | none    => false

end L4Factoidal.ShEx
