/-
L4Factoidal.ShEx.SchemaEq — structural equality on a ShEx schema.

Port of `formal/fstar/ShEx.SchemaEq.fst`'s role: the equality the
DIFFERENTIAL check needs, comparing a schema read from ShExC against
the same schema read from its ShExJ twin.

## Structural, and deliberately not semantic

Two different schemas can accept the same graphs; this says nothing
about that. It answers one question — did the two front doors build
the SAME TREE — which is exactly what a differential test between two
readers of one schema should ask. Calling it semantic equality would
promise something no test here checks.

## Order matters where the specification says it does

A `shapes` list is compared by MEMBERSHIP keyed on the declaration
label, because ShExJ writes its shapes in whatever order the
serialiser chose and ShExC in source order. Everything INSIDE a shape
— the members of an `EachOf`, the alternatives of a `OneOf`, the
values of a value set — is compared IN ORDER, because the
specification gives those an order and a reader that reshuffled them
would be wrong.
-/
import L4Factoidal.ShEx.Schema

namespace L4Factoidal.ShEx

mutual

def shapeExprEq : ShapeExpr → ShapeExpr → Bool
  | .ref a,            .ref b            => a == b
  | .external,         .external         => true
  | .nodeConstraint a, .nodeConstraint b => a == b
  | .shapeAnd a,       .shapeAnd b       => shapeExprListEq a b
  | .shapeOr a,        .shapeOr b        => shapeExprListEq a b
  | .shapeNot a,       .shapeNot b       => shapeExprEq a b
  | .shape a,          .shape b          => shapeEq a b
  | _,                 _                 => false

def shapeExprListEq : List ShapeExpr → List ShapeExpr → Bool
  | [],      []      => true
  | x :: xs, y :: ys => shapeExprEq x y && shapeExprListEq xs ys
  | _,       _       => false

def shapeEq : Shape → Shape → Bool
  | .mk c1 e1 x1 _ _ r1, .mk c2 e2 x2 _ _ r2 =>
      c1 == c2 && e1 == e2 && r1 == r2 && tripleExprOptEq x1 x2

def tripleExprOptEq : Option TripleExpr → Option TripleExpr → Bool
  | none,   none   => true
  | some a, some b => tripleExprEq a b
  | _,      _      => false

def tripleExprEq : TripleExpr → TripleExpr → Bool
  | .ref a,              .ref b              => a == b
  | .tripleConstraint a, .tripleConstraint b => tripleConstraintEq a b
  | .eachOf a,           .eachOf b           => groupEq a b
  | .oneOf a,            .oneOf b            => groupEq a b
  | _,                   _                   => false

def groupEq : Group → Group → Bool
  | .mk i1 es1 mn1 mx1 _ _, .mk i2 es2 mn2 mx2 _ _ =>
      i1 == i2 && mn1 == mn2 && mx1 == mx2 && tripleExprListEq es1 es2

def tripleExprListEq : List TripleExpr → List TripleExpr → Bool
  | [],      []      => true
  | x :: xs, y :: ys => tripleExprEq x y && tripleExprListEq xs ys
  | _,       _       => false

def tripleConstraintEq : TripleConstraint → TripleConstraint → Bool
  | .mk i1 inv1 p1 v1 mn1 mx1 _ _, .mk i2 inv2 p2 v2 mn2 mx2 _ _ =>
      i1 == i2 && inv1 == inv2 && p1 == p2 && mn1 == mn2 && mx1 == mx2 &&
      (match v1, v2 with
       | none,   none   => true
       | some a, some b => shapeExprEq a b
       | _,      _      => false)

end

def shapeDeclEq (a b : ShapeDecl) : Bool :=
  a.id == b.id && a.isAbstract == b.isAbstract && shapeExprEq a.expr b.expr

/-- Two schemas are structurally equal when their `start` matches,
    their imports match, and every declaration in each is matched by
    one with the SAME LABEL in the other. -/
def schemaEq (a b : Schema) : Bool :=
  (match a.start, b.start with
   | none,   none   => true
   | some x, some y => shapeExprEq x y
   | _,      _      => false) &&
  a.imports == b.imports &&
  a.shapes.length == b.shapes.length &&
  a.shapes.all (fun d =>
    match b.shapes.find? (fun e => e.id == d.id) with
    | some e => shapeDeclEq d e
    | none   => false)

/-- The label of the first declaration that differs, for a report that
    names what is wrong instead of only that something is. -/
def firstDiff (a b : Schema) : Option String :=
  match (a.shapes.find? (fun d =>
    match b.shapes.find? (fun e => e.id == d.id) with
    | some e => !(shapeDeclEq d e)
    | none   => true)) with
  | some d => some d.id
  | none   =>
      if a.shapes.length != b.shapes.length then some "<different shape counts>"
      else if !(a.imports == b.imports) then some "<different imports>"
      else if !(match a.start, b.start with
                | none,   none   => true
                | some x, some y => shapeExprEq x y
                | _,      _      => false)
      then some "<different start>"
      else none

end L4Factoidal.ShEx
