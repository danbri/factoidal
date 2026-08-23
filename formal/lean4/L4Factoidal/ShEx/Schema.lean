/-
L4Factoidal.ShEx.Schema — the ShEx 2.1 schema AST, ported from
`formal/fstar/ShEx.Schema.fst`.

Spec: ShEx 2.1 Semantics (http://shex.io/shex-semantics/) and the
ShExJ JSON serialization the test suite ships schemas in.

Numeric facets (`mininclusive` and friends) keep their VERBATIM JSON
lexeme as a `String` rather than being parsed to a number, matching
the F* module. Parsing them early would fix a precision decision
before the datatype that governs it is known, and ShEx compares them
against the node's own lexical value.
-/

namespace L4Factoidal.ShEx

inductive NodeKind where
  | iri | bnode | nonLiteral | literal
deriving Repr, DecidableEq, Inhabited

/-- A stem value: a plain string, or the ShExJ `{"type":"Wildcard"}`
    marker — legal only inside a `*StemRange`'s stem slot, since a
    plain `Stem`'s stem is always a bare string. -/
inductive Stem where
  | plain (s : String)
  | wildcard
deriving Repr, DecidableEq, Inhabited

/-- An exact ObjectValue: a bare IRI, or a literal with optional
    language tag and datatype. -/
inductive ObjectValue where
  | iri     (v : String)
  | literal (value : String) (language : Option String) (datatype : Option String)
deriving Repr, DecidableEq, Inhabited

structure SemAct where
  name : String
  code : Option String := none
deriving Repr, DecidableEq, Inhabited

structure Annotation where
  predicate : String
  object    : ObjectValue
deriving Repr, DecidableEq, Inhabited

/-- Which family a stem range restricts. -/
inductive VsvKind where
  | iri | literal | language
deriving Repr, DecidableEq, Inhabited

/-- What a stem range EXCLUDES. ShExJ writes three shapes here and the
    difference matters: a bare string, whose meaning depends on the
    range's KIND; an explicit stem object (`IriStem`, `LiteralStem`,
    `LanguageStem`); and a language tag.

    The port had this as `List ObjectValue`, and `objectValueOf` reads
    a bare string as an IRI. So `{"type": "LiteralStemRange", "stem":
    "v", "exclusions": ["v1", "v2", "v3"]}` excluded three IRIs, none
    of which a literal can be — the exclusions did nothing and every
    excluded node was admitted. Twenty-five entries of the validation
    suite, all of them negative tests, which is where a rule that
    admits too much shows up.
-/
inductive Exclusion where
  /-- An exact value. -/
  | value (ov : ObjectValue)
  /-- A language TAG, for a `LanguageStemRange`. -/
  | lang  (tag : String)
  /-- A nested STEM: the exclusion is itself a prefix. -/
  | stem  (prefix' : String)
deriving Repr, DecidableEq, Inhabited

/-- A member of a `values` set. -/
inductive ValueSetValue where
  | object    (v : ObjectValue)
  | stem      (kind : VsvKind) (s : Stem)
  | stemRange (kind : VsvKind) (s : Stem) (exclusions : List Exclusion)
  | language  (tag : String)
deriving Repr, DecidableEq, Inhabited

/-- §5.4 node constraint. Numeric facets are verbatim lexemes — see
    the module header. -/
structure NodeConstraint where
  nodeKind        : Option NodeKind := none
  datatype        : Option String := none
  values          : List ValueSetValue := []
  length          : Option Int := none
  minLength       : Option Int := none
  maxLength       : Option Int := none
  pattern         : Option String := none
  flags           : Option String := none
  minInclusive    : Option String := none
  maxInclusive    : Option String := none
  minExclusive    : Option String := none
  maxExclusive    : Option String := none
  totalDigits     : Option Int := none
  fractionDigits  : Option Int := none
deriving Repr, DecidableEq, Inhabited

mutual

/-- §5.3 shape expression. -/
inductive ShapeExpr where
  | ref            (id : String)
  | shapeAnd       (es : List ShapeExpr)
  | shapeOr        (es : List ShapeExpr)
  | shapeNot       (e : ShapeExpr)
  | nodeConstraint (nc : NodeConstraint)
  | shape          (sh : Shape)
  | external
deriving Repr, Inhabited

/-- §5.5 shape. `extendsRefs` is kept as raw refs (`extends` is a Lean
    keyword), as in the F* module. -/
inductive Shape where
  | mk (closed : Bool) (extra : List String) (expression : Option TripleExpr)
       (semActs : List SemAct) (annotations : List Annotation)
       (extendsRefs : List String)
deriving Repr, Inhabited

/-- §5.6 triple expression. -/
inductive TripleExpr where
  | ref              (id : String)
  | tripleConstraint (tc : TripleConstraint)
  | eachOf           (g : Group)
  | oneOf            (g : Group)
deriving Repr, Inhabited

/-- An EachOf/OneOf group. `min`/`max` are `none` for a plain group
    and `some` when the GROUP itself carries a repeat cardinality. -/
inductive Group where
  | mk (id : Option String) (expressions : List TripleExpr)
       (min : Option Int) (max : Option Int)
       (semActs : List SemAct) (annotations : List Annotation)
deriving Repr, Inhabited

/-- §5.7 triple constraint. `max = -1` means UNBOUNDED, matching the
    F* encoding; absent min/max default to 1. -/
inductive TripleConstraint where
  | mk (id : Option String) (inverse : Bool) (predicate : String)
       (valueExpr : Option ShapeExpr) (min : Int) (max : Int)
       (semActs : List SemAct) (annotations : List Annotation)
deriving Repr, Inhabited

end

/-- Field accessors for the mutually recursive records, which must be
    inductives (Lean structures cannot participate in a `mutual`
    block with inductives). -/
def Shape.closed : Shape → Bool | .mk c _ _ _ _ _ => c
def Shape.extra : Shape → List String | .mk _ e _ _ _ _ => e
def Shape.expression : Shape → Option TripleExpr | .mk _ _ x _ _ _ => x
def Shape.extendsRefs : Shape → List String | .mk _ _ _ _ _ x => x

def Group.id : Group → Option String | .mk i _ _ _ _ _ => i
def Group.expressions : Group → List TripleExpr | .mk _ e _ _ _ _ => e
def Group.min : Group → Option Int | .mk _ _ m _ _ _ => m
def Group.max : Group → Option Int | .mk _ _ _ m _ _ => m

def TripleConstraint.id : TripleConstraint → Option String | .mk i _ _ _ _ _ _ _ => i
def TripleConstraint.inverse : TripleConstraint → Bool | .mk _ i _ _ _ _ _ _ => i
def TripleConstraint.predicate : TripleConstraint → String | .mk _ _ p _ _ _ _ _ => p
def TripleConstraint.valueExpr : TripleConstraint → Option ShapeExpr
  | .mk _ _ _ v _ _ _ _ => v
def TripleConstraint.min : TripleConstraint → Int | .mk _ _ _ _ m _ _ _ => m
def TripleConstraint.max : TripleConstraint → Int | .mk _ _ _ _ _ m _ _ => m

/-- `max = -1` is the unbounded marker. -/
def TripleConstraint.unbounded (tc : TripleConstraint) : Bool := tc.max == -1

/-- Is a count within the constraint's cardinality? -/
def TripleConstraint.satisfiesCard (tc : TripleConstraint) (n : Nat) : Bool :=
  (n : Int) ≥ tc.min && (tc.unbounded || (n : Int) ≤ tc.max)

structure ShapeDecl where
  id         : String
  isAbstract : Bool := false
  expr       : ShapeExpr
deriving Repr, Inhabited

structure Schema where
  start     : Option ShapeExpr := none
  startActs : List SemAct := []
  shapes    : List ShapeDecl := []
  imports   : List String := []
deriving Repr, Inhabited

/-- Resolve a shape label to its declaration. -/
def Schema.lookup (s : Schema) (label : String) : Option ShapeDecl :=
  s.shapes.find? (fun d => d.id == label)

end L4Factoidal.ShEx
