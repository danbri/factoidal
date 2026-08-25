/-
L4Factoidal.SHACL.NodeExpr — SHACL 1.2 node expressions.

Port of `formal/fstar/SHACL.NodeExpr.fst` (713 lines). SHACL-AF §5, the
`shnex:` vocabulary. A node expression is an RDF subgraph that, given a
focus node and a variable scope, EVALUATES to a list of terms. The W3C
shacl12 `node-expr` suite drives these directly.

The evaluator reads the expression node straight off the graph — no
separate parse step: it looks at which `shnex:` predicate the node
carries and dispatches. Fuel bounds the recursion, because expression
graphs may be cyclic.

## One function where F\* has five

The F\* evaluator is a mutual block of five functions with a
lexicographic measure `%[fuel; tag; length]`: the list walks recurse at
the SAME fuel while `eval_ne` recurses at `fuel - 1`.

Here the four helpers are not recursive at all. `eval_ne_list` is
`es.flatMap (evalNe … fuel')`, `eval_ne_flatmap` is a `flatMap` with a
different focus, `eval_ne_keyed` is a `map`, and `eval_ne_argvals` is a
`flatMap … |>.take 1` — each calls `evalNe` only at the already
decremented `fuel'`. So the whole thing is one function whose measure
is `fuel`, and `eval_ne_intersect` becomes a plain list fold over
already-computed results. Same semantics, one termination argument
instead of a three-component one.

## Adapted to the Lean SHACL API, which differs from the F\* one

`node_conforms` in F\* calls `collect_shape_violations` against a
materialised `shacl_class_closure`. The Lean validator has no violation
collector exposed and no closure materialiser: it has `validate` over a
`ShapesGraph`, and `isShaclInstance`, which already walks
`rdfs:subClassOf`. So:

* `nodeConforms` re-targets the named shape at the single value node,
  clears every other shape's targets, and asks `validate` whether the
  result conforms. That is the same judgment by a different route.
* `instancesOf` filters the graph's subjects by `isShaclInstance`,
  which gives the `rdfs:subClassOf` closure without materialising
  triples.

## ⚠️ Phase coverage, in the F\* module's own words

Its header says "Phase 1 covers the generator + simple-aggregate forms;
the per-element-focus forms (orderBy / filterShape / flatMap /
intersection / min / max / sum / the match\* / find\* / remove family)
land in a follow-up" — but the F\* code as it stands implements all of
them, so the comment is stale there. Every form the F\* code handles is
handled here.
-/
import L4Factoidal.SHACL.Validation
import L4Factoidal.SPARQL.Expr

namespace L4Factoidal.SHACL

open L4Factoidal.RDF
open L4Factoidal.SPARQL

/-! ## The `shnex` vocabulary -/

def shnexNs : String := "http://www.w3.org/ns/shacl-node-expr#"

private def shnex (local_ : String) : WfIri :=
  ⟨shnexNs ++ local_, by simp [isIri, String.isEmpty, shnexNs]⟩

def shnexFocusNode    : WfIri := shnex "focusNode"
def shnexPathValues   : WfIri := shnex "pathValues"
def shnexNodes        : WfIri := shnex "nodes"
def shnexConcat       : WfIri := shnex "concat"
def shnexCount        : WfIri := shnex "count"
def shnexDistinct     : WfIri := shnex "distinct"
def shnexExists       : WfIri := shnex "exists"
def shnexIf           : WfIri := shnex "if"
def shnexThen         : WfIri := shnex "then"
def shnexElse         : WfIri := shnex "else"
def shnexSum          : WfIri := shnex "sum"
def shnexMin          : WfIri := shnex "min"
def shnexMax          : WfIri := shnex "max"
def shnexIntersection : WfIri := shnex "intersection"
def shnexInstancesOf  : WfIri := shnex "instancesOf"
def shnexVar          : WfIri := shnex "var"
def shnexFlatMap      : WfIri := shnex "flatMap"
def shnexRemove       : WfIri := shnex "remove"
def shnexOrderBy      : WfIri := shnex "orderBy"
def shnexDesc         : WfIri := shnex "desc"
def shnexFilterShape  : WfIri := shnex "filterShape"
def shnexMatchAll     : WfIri := shnex "matchAll"
def shnexFindFirst    : WfIri := shnex "findFirst"
def shnexNodesMatching : WfIri := shnex "nodesMatching"
def shnexLimit        : WfIri := shnex "limit"
def shnexOffset       : WfIri := shnex "offset"

/-! ## Small helpers -/

def mkIntLit (n : Int) : Term := .literal (mkTypedLiteral (toString n) xsdInteger)

def mkBoolLit (b : Bool) : Term :=
  .literal (mkTypedLiteral (if b then "true" else "false") xsdBoolean)

/-- A leading boolean literal decides; otherwise a non-empty list is
    truthy. -/
def neEbv (l : List Term) : Bool :=
  match l with
  | .literal lit :: _ =>
      if lit.val.datatype == xsdBoolean then lit.val.lexicalForm == "true" else true
  | [] => false
  | _  => true

/-- Every subject of `g` that is an instance of `c`, subclasses
    included. `isShaclInstance` walks `rdfs:subClassOf`, so no closure
    is materialised. -/
def instancesOf (g : Graph) (c : WfIri) : List Term :=
  dedupTerms (((distinctSubjects g).map Subject.toTerm).filter
    (fun t => isShaclInstance g t c))

/-- Does `v` conform to the shape `shapeTerm` names? An unresolvable
    reference conforms vacuously, as in F\*. -/
def nodeConforms (g : Graph) (shapeTerm : Term) (v : Term) : Bool :=
  match termToShapeRef shapeTerm with
  | none => true
  | some r =>
      let sg := decodeShapesGraph g
      match lookupShape r sg.shapes with
      | none => true
      | some _ =>
          let shapes := sg.shapes.map (fun s =>
            if s.id == r then { s with targets := [Target.node v] }
            else { s with targets := ([] : List Target) })
          (validate g { sg with shapes := shapes }).conforms

/-! ## Numeric aggregates

`sum` is decimal-aware: each value parses to `(scaledInt, scale)` with
`value = scaledInt / 10 ^ scale`, and summing rescales to the common
maximum scale. An all-integer sum keeps scale 0. `min` and `max` are
integer-only, as in F\*: a decimal member makes them bow out rather
than compute a wrong result. -/

def parseIntTerm (t : Term) : Option Int :=
  match t with
  | .literal l => if l.val.datatype == xsdInteger then parseIntString l.val.lexicalForm else none
  | _ => none

def intsOf : List Term → Option (List Int)
  | [] => some []
  | h :: r => match parseIntTerm h, intsOf r with
              | some n, some ns => some (n :: ns)
              | _, _ => none

def pow10 : Nat → Int
  | 0 => 1
  | n + 1 => 10 * pow10 n

def splitDot : List Char → List Char → List Char × Option (List Char)
  | [], acc => (acc.reverse, none)
  | '.' :: rest, acc => (acc.reverse, some rest)
  | c :: rest, acc => splitDot rest (c :: acc)

def parseDecLexical (s : String) : Option (Int × Nat) :=
  match splitDot s.toList [] with
  | (_, none) => (parseIntString s).map (fun n => (n, 0))
  | (before, some after) =>
      (parseIntString (String.ofList (before ++ after))).map (fun n => (n, after.length))

def parseNumTerm (t : Term) : Option (Int × Nat) :=
  match t with
  | .literal l =>
      if l.val.datatype == xsdInteger || l.val.datatype == xsdDecimal
      then parseDecLexical l.val.lexicalForm else none
  | _ => none

def numsOf : List Term → Option (List (Int × Nat))
  | [] => some []
  | h :: r => match parseNumTerm h, numsOf r with
              | some p, some ps => some (p :: ps)
              | _, _ => none

def maxScale : List (Int × Nat) → Nat → Nat
  | [], acc => acc
  | (_, sc) :: r, acc => maxScale r (if sc > acc then sc else acc)

def sumScaled : List (Int × Nat) → Nat → Int
  | [], _ => 0
  | (n, sc) :: r, ms => n * pow10 (if ms ≥ sc then ms - sc else 0) + sumScaled r ms

def repeat0 : Nat → List Char
  | 0 => []
  | n + 1 => '0' :: repeat0 n

/-- Render `scaledVal / 10 ^ scale` as an `xsd:decimal`, or an
    `xsd:integer` when the scale is zero. -/
def mkDecimalLit (scaledVal : Int) (scale : Nat) : Term :=
  if scale == 0 then mkIntLit scaledVal
  else
    let neg := scaledVal < 0
    let a := if neg then -scaledVal else scaledVal
    let digits := (toString a).toList
    let padded := (if digits.length ≥ scale + 1 then [] else repeat0 (scale + 1 - digits.length))
                  ++ digits
    let k := if padded.length ≥ scale then padded.length - scale else 0
    let body := String.ofList (padded.take k ++ ['.'] ++ padded.drop k)
    .literal (mkTypedLiteral (if neg then "-" ++ body else body) xsdDecimal)

def sumExpr (vals : List Term) : List Term :=
  match numsOf vals with
  | some ps => let ms := maxScale ps 0; [mkDecimalLit (sumScaled ps ms) ms]
  | none => []

def maxInt : List Int → Int → Int
  | [], acc => acc
  | h :: r, acc => maxInt r (if h > acc then h else acc)

def minInt : List Int → Int → Int
  | [], acc => acc
  | h :: r, acc => minInt r (if h < acc then h else acc)

def maxExpr (vals : List Term) : List Term :=
  match intsOf vals with
  | some (h :: t) => [mkIntLit (maxInt t h)]
  | _ => []

def minExpr (vals : List Term) : List Term :=
  match intsOf vals with
  | some (h :: t) => [mkIntLit (minInt t h)]
  | _ => []

/-! `shnex:remove` and `shnex:intersection` compare TERMS, not values:
`"01"^^xsd:integer` is a different term from `"1"^^xsd:integer` even
though the two are value-equal. `Shapes.termMem` is that comparison and
is reused here rather than restated. -/

def termRender : Term → String
  | .iri i => i.val
  | .literal l => l.val.lexicalForm
  | .bnode b => b
  | .tripleTerm _ _ _ => ""

/-- Numeric when both sides are integer literals; otherwise a lexical
    comparison of the rendered term, which orders ISO dates and plain
    strings correctly and puts the empty-string "no value" sentinel
    first. -/
def termCmpLe (a b : Term) : Bool :=
  match parseIntTerm a, parseIntTerm b with
  | some x, some y => x ≤ y
  | _, _ => match compare (termRender a) (termRender b) with
            | .gt => false
            | _   => true

/-- Insertion sort by the pair's key, stable on equal keys. -/
def insertByKeyTerm (x : Term × Term) : List (Term × Term) → List (Term × Term)
  | [] => [x]
  | y :: ys => if termCmpLe x.2 y.2 && !(termCmpLe y.2 x.2) then x :: y :: ys
               else y :: insertByKeyTerm x ys

def sortByKeyTerm : List (Term × Term) → List (Term × Term)
  | [] => []
  | x :: xs => insertByKeyTerm x (sortByKeyTerm xs)

/-! ## SHACL-SPARQL node expressions

A `[ sparql:<fn> ( arg1 arg2 … ) ]` expression applies the SPARQL
built-in to its evaluated arguments. Each argument value is wrapped as
a constant `Expr`, dispatched to the matching constructor, evaluated
with an empty binding, and converted back to a term. -/

def sparqlNs : String := "http://www.w3.org/ns/sparql#"

def sparqlLocalName (p : WfIri) : Option String :=
  if p.val.startsWith sparqlNs && p.val.length > sparqlNs.length
  then some (String.ofList (p.val.toList.drop sparqlNs.length))
  else none

def sparqlCallOf (g : Graph) (es : Subject) : Option (String × Term) :=
  match (g.filter (fun tr => tr.s == es && (sparqlLocalName tr.p).isSome)) with
  | tr :: _ => (sparqlLocalName tr.p).map (fun ln => (ln, tr.o))
  | [] => none

/-- A triple-term subject is an IRI or a blank node, never a nested
    triple term, so this needs no recursion. -/
def subjToExpr : Subject → Expr
  | .iri i => .iri i
  | .bnode _ => .lit (mkTypedLiteral "" xsdString)

/-- Wrap a computed value as a constant expression, promoting numeric
    and boolean literals so the arithmetic builtins see numbers rather
    than opaque literals. -/
def termToExpr : Term → Expr
  | .iri i => .iri i
  | .literal l =>
      if l.val.datatype == xsdInteger then
        match parseIntString l.val.lexicalForm with
        | some n => .numericLit n
        | none => .lit l
      else if l.val.datatype == xsdDecimal then .decimalLit l.val.lexicalForm
      else if l.val.datatype == xsdDouble then .doubleLit l.val.lexicalForm
      else if l.val.datatype == xsdBoolean then .boolLit (l.val.lexicalForm == "true")
      else .lit l
  | .tripleTerm s p o => .tripleTerm (subjToExpr s) (.iri p) (termToExpr o)
  | .bnode _ => .lit (mkTypedLiteral "" xsdString)

/-- `none` for a name or arity this does not bridge. -/
def sparqlFnExpr (ln : String) (args : List Expr) : Option Expr :=
  match ln, args with
  | "abs", [a] => some (.abs a)
  | "ceil", [a] => some (.ceil a)
  | "floor", [a] => some (.floor a)
  | "round", [a] => some (.round a)
  | "str", [a] => some (.str a)
  | "strlen", [a] => some (.strLen a)
  | "ucase", [a] => some (.uCase a)
  | "lcase", [a] => some (.lCase a)
  | "lang", [a] => some (.lang a)
  | "langdir", [a] => some (.langDir a)
  | "hasLang", [a] => some (.hasLang a)
  | "hasLang", [a, _] => some (.hasLang a)
  | "hasLangdir", [a] => some (.hasLangDir a)
  | "hasLangdir", [a, _] => some (.hasLangDir a)
  | "datatype", [a] => some (.datatype a)
  | "iri", [a] => some (.iriFn a)
  | "uri", [a] => some (.iriFn a)
  | "encode-for-uri", [a] => some (.encodeForUri a)
  | "encode", [a] => some (.encodeForUri a)
  | "isIRI", [a] => some (.isIri a)
  | "isURI", [a] => some (.isIri a)
  | "isBlank", [a] => some (.isBlank a)
  | "isLiteral", [a] => some (.isLiteral a)
  | "isNumeric", [a] => some (.isNumeric a)
  | "isTriple", [a] => some (.isTriple a)
  | "triple", [a, b, c] => some (.tripleTerm a b c)
  | "subject", [a] => some (.ttSubject a)
  | "predicate", [a] => some (.ttPredicate a)
  | "object", [a] => some (.ttObject a)
  | "contains", [a, b] => some (.contains a b)
  | "strstarts", [a, b] => some (.strStarts a b)
  | "strends", [a, b] => some (.strEnds a b)
  | "strbefore", [a, b] => some (.strBefore a b)
  | "strafter", [a, b] => some (.strAfter a b)
  | "strdt", [a, b] => some (.strDt a b)
  | "strlang", [a, b] => some (.strLang a b)
  | "strlangdir", [a, b, c] => some (.strLangDir a b c)
  | "concat", _ => some (.concat args)
  | "coalesce", _ => some (.coalesce args)
  | "sameTerm", [a, b] => some (.sameTerm a b)
  | "if", [a, b, c] => some (.cond a b c)
  | "substr", [a, b] => some (.substr a b none)
  | "substr", [a, b, c] => some (.substr a b (some c))
  | "replace", [a, b, c] => some (.replace a b c none)
  | "replace", [a, b, c, d] => some (.replace a b c (some d))
  | "regex", [a, b] => some (.regex a b none)
  | "regex", [a, b, c] => some (.regex a b (some c))
  | "year", [a] => some (.year a)
  | "month", [a] => some (.month a)
  | "day", [a] => some (.day a)
  | "hours", [a] => some (.hours a)
  | "minutes", [a] => some (.minutes a)
  | "seconds", [a] => some (.seconds a)
  | "timezone", [a] => some (.timezone a)
  | "tz", [a] => some (.tz a)
  | "md5", [a] => some (.md5 a)
  | "sha1", [a] => some (.sha1 a)
  | "sha256", [a] => some (.sha256 a)
  | "sha384", [a] => some (.sha384 a)
  | "sha512", [a] => some (.sha512 a)
  | "logical-not", [a] => some (.not a)
  | "unary-minus", [a] => some (.unaryMinus a)
  | "unary-plus", [a] => some (.unaryPlus a)
  | "logical-and", [a, b] => some (.and a b)
  | "logical-or", [a, b] => some (.or a b)
  | "divide", [a, b] => some (.arith .div a b)
  | "multiply", [a, b] => some (.arith .mul a b)
  | "plus", [a, b] => some (.arith .add a b)
  | "subtract", [a, b] => some (.arith .sub a b)
  | "equals", [a, b] => some (.compare .eq a b)
  | "sameValue", [a, b] => some (.compare .eq a b)
  | "not-equals", [a, b] => some (.compare .ne a b)
  | "greater-than", [a, b] => some (.compare .gt a b)
  | "greater-than-or-equal", [a, b] => some (.compare .ge a b)
  | "less-than", [a, b] => some (.compare .lt a b)
  | "less-than-or-equal", [a, b] => some (.compare .le a b)
  | _, _ => none

/-- The canonical `xsd:decimal` lexical form carries a decimal point;
    `ABS`/`CEIL`/`FLOOR`/`ROUND` of a decimal yield a decimal, and the
    evaluator emits `"4"` where the canonical form is `"4.0"`. -/
def canonDecimal (t : Term) : Term :=
  match t with
  | .literal l =>
      if l.val.datatype == xsdDecimal && !(l.val.lexicalForm.toList.contains '.')
      then .literal (mkTypedLiteral (l.val.lexicalForm ++ ".0") xsdDecimal)
      else t
  | _ => t

def neUuidIri : WfIri :=
  ⟨"urn:uuid:00000000-0000-0000-0000-000000000000", by simp [isIri, String.isEmpty]⟩

def afterChar (c : Char) : List Char → List Char
  | [] => []
  | x :: r => if x == c then r else afterChar c r

def takeWhileLc (p : Char → Bool) : List Char → List Char
  | [] => []
  | c :: r => if p c then c :: takeWhileLc p r else []

/-- The seconds field of `…THH:MM:SS[.fff][tz]`, keeping its two-digit
    form: the shnex-sparql fixture expects the lexical `"00"`, not the
    canonical decimal `"0"`. -/
def extractSecondsField (s : String) : String :=
  match takeWhileLc Char.isDigit (afterChar ':' (afterChar ':' (afterChar 'T' s.toList))) with
  | [] => "0"
  | secs => String.ofList secs

/-- RFC 4647 basic-range match: `*` matches any non-empty tag;
    otherwise the tag equals the range or extends it at a `-`
    boundary. -/
def langMatchesNe (tag range : String) : Bool :=
  if range == "*" then tag.length > 0
  else tag == range || tag.startsWith (range ++ "-")

/-- Evaluate a bridged builtin. A few are handled here rather than
    through the expression AST, because the AST cannot represent their
    argument or result (a blank node, a computed UUID) or because they
    inspect the raw arguments (`BOUND`). -/
def sparqlApply (ln : String) (argvals : List Term) : List Term :=
  match ln, argvals with
  | "isBlank", [t] => [mkBoolLit (match t with | .bnode _ => true | _ => false)]
  | "bnode", _ => [.bnode "ne_bnode0"]
  | "uuid", _ => [.iri neUuidIri]
  | "struuid", _ =>
      [.literal (mkTypedLiteral "00000000-0000-0000-0000-000000000000" xsdString)]
  | "langMatches", [a, b] => [mkBoolLit (langMatchesNe (termRender a) (termRender b))]
  | "seconds", [.literal l] =>
      [.literal (mkTypedLiteral (extractSecondsField l.val.lexicalForm) xsdDecimal)]
  -- BOUND: the argument contributed a value exactly when `argvals` is
  -- non-empty, since an argument evaluating to `[]` is dropped.
  | "bound", _ => [mkBoolLit !argvals.isEmpty]
  | _, _ =>
      match sparqlFnExpr ln (argvals.map termToExpr) with
      | some e =>
          match (Expr.eval Binding.empty e).toTerm? with
          | some t => [canonDecimal t]
          | none => []
      | none => []

/-! ## The evaluator -/

def firstInt (l : List Term) : Option Nat :=
  match l with
  | .literal lit :: _ => (parseIntString lit.val.lexicalForm).map Int.toNat
  | _ => none

/-- Terms present in every member list. -/
def intersectAll : List (List Term) → List Term
  | [] => []
  | [m] => m
  | m :: rest => let tl := intersectAll rest; m.filter (fun x => termMem x tl)

def evalNe (g : Graph) (focus : Option Term) (scope : List (String × Term))
    (expr : Term) (fuel : Nat) : List Term :=
  match fuel with
  | 0 => []
  | f + 1 =>
    match expr.toSubject? with
    | none => [expr]                                  -- a literal is a constant
    | some es =>
      let startNodes : List Term :=
        match objectsOf g es shnexFocusNode with
        | fe :: _ => evalNe g focus scope fe f
        | [] => match focus with | some x => [x] | none => []
      let base : List Term :=
        match objectsOf g es shnexVar with
        | .literal l :: _ =>
            if l.val.lexicalForm == "focusNode" then
              match focus with | some x => [x] | none => []
            else
              match scope.find? (fun p => p.1 == l.val.lexicalForm) with
              | some (_, t) => [t]
              | none => []
        | _ =>
        match objectsOf g es shnexPathValues with
        | p :: _ => startNodes.flatMap (fun st => evalPath g st (decodePath g p f))
        | [] =>
        match objectsOf g es shnexNodes with
        | l :: _ => evalNe g focus scope l f
        | [] =>
        match objectsOf g es shnexConcat with
        | l :: _ => (rdfListTerms g l f).flatMap (fun e => evalNe g focus scope e f)
        | [] =>
        match objectsOf g es shnexDistinct with
        | e :: _ => dedupTerms (evalNe g focus scope e f)
        | [] =>
        match objectsOf g es shnexCount with
        | e :: _ => [mkIntLit (evalNe g focus scope e f).length]
        | [] =>
        match objectsOf g es shnexExists with
        | e :: _ => [mkBoolLit !(evalNe g focus scope e f).isEmpty]
        | [] =>
        match objectsOf g es shnexIf with
        | c :: _ =>
            if neEbv (evalNe g focus scope c f) then
              match objectsOf g es shnexThen with
              | t :: _ => evalNe g focus scope t f
              | [] => []
            else
              match objectsOf g es shnexElse with
              | e :: _ => evalNe g focus scope e f
              | [] => []
        | [] =>
        match objectsOf g es shnexSum with
        | e :: _ => sumExpr (evalNe g focus scope e f)
        | [] =>
        match objectsOf g es shnexMin with
        | e :: _ => minExpr (evalNe g focus scope e f)
        | [] =>
        match objectsOf g es shnexMax with
        | e :: _ => maxExpr (evalNe g focus scope e f)
        | [] =>
        match objectsOf g es shnexIntersection with
        | l :: _ =>
            dedupTerms (intersectAll ((rdfListTerms g l f).map (fun m => evalNe g focus scope m f)))
        | [] =>
        match objectsOf g es shnexNodesMatching with
        | s :: _ =>
            dedupTerms (((distinctSubjects g).map Subject.toTerm).filter
              (fun v => nodeConforms g s v))
        | [] =>
        match sparqlCallOf g es with
        | some (ln, arglist) =>
            sparqlApply ln ((rdfListTerms g arglist f).flatMap
              (fun a => (evalNe g focus scope a f).take 1))
        | none =>
        match objectsOf g es shnexInstancesOf with
        | .iri c :: _ => instancesOf g c
        | _ =>
            -- No shnex predicate. A blank node may still be a bare
            -- rdf:List expression, or an empty `[]`. An IRI or literal
            -- is a constant.
            match objectsOf g es rdfFirst with
            | _ :: _ => (rdfListTerms g expr f).flatMap (fun e => evalNe g focus scope e f)
            | [] => match expr with | .bnode _ => [] | _ => [expr]
      let afterFlatMap :=
        match objectsOf g es shnexFlatMap with
        | m :: _ => base.flatMap (fun el => evalNe g (some el) scope m f)
        | [] => base
      let afterRemove :=
        match objectsOf g es shnexRemove with
        | r :: _ =>
            let rm := evalNe g focus scope r f
            afterFlatMap.filter (fun x => !termMem x rm)
        | [] => afterFlatMap
      let afterOrderBy :=
        match objectsOf g es shnexOrderBy with
        | k :: _ =>
            let desc := (firstBool (objectsOf g es shnexDesc)).getD false
            let keyed := afterRemove.map (fun el =>
              (el, match evalNe g (some el) scope k f with
                   | kk :: _ => kk
                   | [] => .literal (mkTypedLiteral "" xsdString)))
            let ordered := (sortByKeyTerm keyed).map (·.1)
            if desc then ordered.reverse else ordered
        | [] => afterRemove
      let afterFilter :=
        match objectsOf g es shnexFilterShape with
        | s :: _ => afterOrderBy.filter (fun v => nodeConforms g s v)
        | [] => afterOrderBy
      let afterMatchAll :=
        match objectsOf g es shnexMatchAll with
        | s :: _ => [mkBoolLit (afterFilter.all (fun v => nodeConforms g s v))]
        | [] => afterFilter
      let afterFindFirst :=
        match objectsOf g es shnexFindFirst with
        | s :: _ => match afterMatchAll.find? (fun v => nodeConforms g s v) with
                    | some v => [v]
                    | none => []
        | [] => afterMatchAll
      let afterOffset :=
        match firstInt (objectsOf g es shnexOffset) with
        | some n => afterFindFirst.drop n
        | none => afterFindFirst
      match firstInt (objectsOf g es shnexLimit) with
      | some n => afterOffset.take n
      | none => afterOffset
termination_by fuel

/-- The runner's entry point. -/
def evalNodeExprTop (g : Graph) (focus : Option Term)
    (scope : List (String × Term)) (expr : Term) : List Term :=
  evalNe g focus scope expr (g.length + 100)

end L4Factoidal.SHACL
